#!/usr/bin/env python3
"""Final round: relabel the <title> tooltips of the two relabeled figures so that they use the
wording of the visible labels. Only the text inside <title> elements changes; the script checks
that everything outside <title> elements is byte-identical before and after."""
import re, sys, pathlib
def strip_titles(s): return re.sub(r"<title>[^<]*</title>", "<title/>", s)
def cascade(t):
    n = [0]
    def a(m):
        n[0] += 1
        return f"<title>x = {m.group(1)}: {m.group(2)} spacings below x, fraction of the total spacing length {m.group(3)}</title>"
    t = re.sub(r"<title>D = ([0-9.]+): ([0-9]+) spacings below, h/sum = ([0-9.]+)</title>", a, t)
    def b(m):
        n[0] += 1
        return (f"<title>x = {m.group(1)}: {m.group(2)} of {m.group(3)} spacings below x, their total length {m.group(4)}, "
                f"fraction of the total spacing length {m.group(5)} (GUE exact {m.group(6)}, Poisson {m.group(7)})</title>")
    t = re.sub(r"<title>D = ([0-9.]+): n_below = ([0-9]+) of ([0-9]+), h_D = ([0-9.]+), h_D/sum s = ([0-9.]+) \(GUE exact ([0-9.]+), Poisson ([0-9.]+)\)</title>", b, t)
    return t, n[0]
CUBE = [
 ("<title>reservoir: Delta &lt;= max|delta| &lt; 3/8 (O(T^(1-c)) zeros, proved); empty for the 400 zeros here</title>",
  "<title>Delta &lt;= max|delta| &lt; 3/8: O(T^(1-c)) zeros up to height T (Carlson 1920); empty for the 400 zeros here</title>"),
 ("<title>band: 0 &lt; max|delta| &lt; Delta = 1/8 (illustrative); empty under the gap hypothesis (open)</title>",
  "<title>band: 0 &lt; max|delta| &lt; Delta = 1/8 (illustrative); empty iff the gap hypothesis holds (unproved)</title>"),
 ("<title>7/8 face: max(|delta1|,|delta2|) &gt;= 3/8</title>",
  "<title>max(|delta1|,|delta2|) &gt; 3/8: no zeros (OpenAI's 7/8 theorem)</title>"),
]
for d in sys.argv[1:]:
    d = pathlib.Path(d)
    f = d / "cascade-relabeled.svg"; s = f.read_text(encoding="utf-8"); t, n = cascade(s)
    assert n == 21, n
    assert strip_titles(s) == strip_titles(t)
    assert not re.search(r"<title>[^<]*(h_D|n_below|D = )[^<]*</title>", t)
    f.write_text(t, encoding="utf-8"); print(f, "tooltips relabeled:", n)
    f = d / "cube-relabeled.svg"; s = f.read_text(encoding="utf-8"); t = s
    for old, new in CUBE:
        assert t.count(old) == 1, old
        t = t.replace(old, new)
    assert strip_titles(s) == strip_titles(t)
    assert not re.search(r"<title>[^<]*(reservoir|face|\(open\)|, proved\))[^<]*</title>", t)
    f.write_text(t, encoding="utf-8"); print(f, "tooltips relabeled:", len(CUBE))
