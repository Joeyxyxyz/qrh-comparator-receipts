#!/usr/bin/env python3
"""Static look at the proof's source files. Read-only; compiles nothing.

Starting from one entry module, follow `import` lines through the project's own .lean files and
report: how many project files the proof depends on, their total size, a digest of exactly those
files, which outside libraries they import, and whether any of them contains a construct that
deserves a second look (sorry, axiom, native_decide, set_option, unsafe code, metaprogramming).

This is a cross-check for the human reader, NOT the verdict. The verdict comes from Comparator,
which checks the compiled proof term itself: its axioms, and every step, in the Lean kernel.

usage: closure_scan.py LEAN_ROOT ENTRY_MODULE [--json OUT.json] [--list OUT.txt]
"""
import hashlib
import json
import re
import sys
from pathlib import Path

HEADER_WORDS = {"module", "prelude"}
IMPORT_MODIFIERS = {"public", "private", "meta", "all"}

# Words that, outside comments and strings, mark something worth a second look: missing proofs,
# extra axioms, trust in compiled code, and every way a Lean file can define its own syntax,
# tactics or commands or run a program while it is being compiled.
FLAG_WORDS = [
    "sorry", "admit", "sorryAx",
    "axiom",
    "native_decide", "native", "ofReduceBool", "reduceBool", "trustCompiler",
    "implemented_by", "extern", "unsafe", "unsafeCast", "partial",
    "set_option",
    "elab", "elab_rules", "macro", "macro_rules", "syntax", "declare_syntax_cat",
    "run_cmd", "run_elab", "run_meta", "run_tac", "by_elab", "simproc", "dsimproc",
    "initialize", "builtin_initialize",
    "addDecl", "addDeclWithoutChecking", "skipKernelTC",
    "infix", "infixl", "infixr", "prefix", "postfix",
]
# Flagged wherever they occur, also as part of a longer name.
FLAG_SUBSTRINGS = ["IO.", "Lean.Elab", "Lean.Meta", "Lean.Parser", "ofReduceBool", "@[tactic", "@[command_elab",
                   "@[term_elab", "@[macro", "@[builtin_", "@[export", "open Lean"]
# Any command that starts with # (#eval, #check, #guard, ...) at the start of a line.
HASH_COMMAND_RE = re.compile(r"^\s*#[A-Za-z_]")
IMPORT_LINE_RE = re.compile(r"^\s*(?:(?:public|private|meta)\s+)*import\s")
# Notations are counted, not flagged: a notation is an abbreviation by pattern and cannot run code.
NOTATION_RE = re.compile(r"^\s*((?:local|scoped)\s+)?notation\b")


def strip_comments_and_strings(text: str) -> str:
    """Blank out comments (line, nested block, doc) and string literals, keeping line structure."""
    out = []
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j < 0 else j
            out.append(" ")
        elif text.startswith("/-", i):
            out.append(" ")
            depth, i = 1, i + 2
            while i < n and depth:
                if text.startswith("/-", i):
                    depth, i = depth + 1, i + 2
                elif text.startswith("-/", i):
                    depth, i = depth - 1, i + 2
                else:
                    if text[i] == "\n":
                        out.append("\n")
                    i += 1
        elif c == '"':
            i += 1
            while i < n and text[i] != '"':
                if text[i] == "\\":
                    i += 1
                if i < n and text[i] == "\n":
                    out.append("\n")
                i += 1
            i += 1
            out.append('""')
        else:
            out.append(c)
            i += 1
    return "".join(out)


def header_imports(text: str, path: Path):
    """Modules imported by the header block (the imports before the first other command)."""
    code = strip_comments_and_strings(text)
    words = code.split()
    imports = []
    i = 0
    while i < len(words):
        w = words[i]
        if w in HEADER_WORDS:
            i += 1
            continue
        j = i
        while j < len(words) and words[j] in IMPORT_MODIFIERS:
            j += 1
        if j < len(words) and words[j] == "import":
            j += 1
            if j < len(words) and words[j] == "all":
                j += 1
            if j >= len(words):
                raise SystemExit(f"{path}: 'import' with no module name")
            name = words[j]
            if "«" in name or not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.!?]*", name):
                raise SystemExit(f"{path}: cannot parse import name {name!r}; inspect by hand")
            imports.append(name)
            i = j + 1
            continue
        break
    # Lean accepts imports only in the header. If the word turns up later as a command, this
    # parser has misread the file and its closure cannot be trusted.
    rest = " ".join(words[i:])
    if re.search(r"(?:^|\s)import\s+[A-Z]", rest):
        raise SystemExit(f"{path}: an import appears after the header; inspect by hand")
    return imports


def main():
    args = sys.argv[1:]
    if len(args) < 2:
        raise SystemExit(__doc__)
    root = Path(args[0]).resolve()
    entry = args[1]
    json_out = list_out = None
    rest = args[2:]
    while rest:
        if rest[0] == "--json":
            json_out, rest = rest[1], rest[2:]
        elif rest[0] == "--list":
            list_out, rest = rest[1], rest[2:]
        else:
            raise SystemExit(f"unknown argument {rest[0]}")

    def local_path(module: str) -> Path:
        return root.joinpath(*module.split(".")).with_suffix(".lean")

    if not local_path(entry).is_file():
        raise SystemExit(f"entry module {entry} not found under {root}")

    seen, order, stack = set(), [], [entry]
    external = {}
    texts = {}
    while stack:
        mod = stack.pop()
        if mod in seen:
            continue
        seen.add(mod)
        path = local_path(mod)
        data = path.read_bytes()
        text = data.decode("utf-8")
        texts[mod] = (data, text)
        order.append(mod)
        for imp in header_imports(text, path):
            if local_path(imp).is_file():
                if imp not in seen:
                    stack.append(imp)
            else:
                external.setdefault(imp, 0)
                external[imp] += 1

    modules = sorted(order)
    total_lines = 0
    total_bytes = 0
    digest = hashlib.sha256()
    flags = {}
    notations = {}
    word_re = re.compile(r"(?<![A-Za-z0-9_'.])(" + "|".join(re.escape(w) for w in FLAG_WORDS) + r")(?![A-Za-z0-9_'])")
    for mod in modules:
        data, text = texts[mod]
        total_bytes += len(data)
        total_lines += text.count("\n") + (0 if text.endswith("\n") or not text else 1)
        digest.update(mod.encode() + b"\0" + hashlib.sha256(data).hexdigest().encode() + b"\n")
        code = strip_comments_and_strings(text)
        for lineno, line in enumerate(code.split("\n"), 1):
            if IMPORT_LINE_RE.match(line):
                continue  # imports are reported separately, under external_libraries
            hits = set(word_re.findall(line))
            for sub in FLAG_SUBSTRINGS:
                if sub in line:
                    hits.add(sub)
            if HASH_COMMAND_RE.match(line):
                hits.add("#command")
            for h in hits:
                flags.setdefault(h, []).append(f"{mod}:{lineno}")
            m = NOTATION_RE.match(line)
            if m:
                kind = (m.group(1) or "global ").strip() + " notation"
                notations[kind] = notations.get(kind, 0) + 1

    by_library = {}
    for imp in external:
        by_library.setdefault(imp.split(".")[0], set()).add(imp)

    result = {
        "entry": entry,
        "project_modules": len(modules),
        "project_lines": total_lines,
        "project_bytes": total_bytes,
        "closure_digest": digest.hexdigest(),
        "module_prefixes": sorted({".".join(m.split(".")[:3]) for m in modules}),
        "external_libraries": {k: sorted(v) for k, v in sorted(by_library.items())},
        "notations": dict(sorted(notations.items())),
        "flag_counts": {k: len(v) for k, v in sorted(flags.items())},
        "flag_locations": {k: v[:20] for k, v in sorted(flags.items())},
    }
    if list_out:
        Path(list_out).write_text("\n".join(modules) + "\n")
    text = json.dumps(result, indent=2, sort_keys=True)
    if json_out:
        Path(json_out).write_text(text + "\n")
    print(text)


if __name__ == "__main__":
    main()
