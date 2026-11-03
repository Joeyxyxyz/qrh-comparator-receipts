#!/usr/bin/env bash
# Phase 4. Fetch OpenAI's repository at the pinned commit and check that it is byte-for-byte the
# tree that was audited when this kit was written. Compiles nothing.
#
# Takes a few minutes. Run it detached:   scripts/detach.sh fetch 04_fetch.sh
. "$(dirname "${BASH_SOURCE[0]}")/lib.sh"
require_not_root
require_phase 3
need_cmd git
need_cmd python3
begin_phase 4

log "== fetch the artifact under test =="

if [ ! -d "$OAI_DIR/.git" ]; then
  git init --quiet "$OAI_DIR"
  git -C "$OAI_DIR" remote add origin "$OAI_REPO"
fi
[ "$(git -C "$OAI_DIR" remote get-url origin)" = "$OAI_REPO" ] || die "unexpected origin in $OAI_DIR"

if [ "$(git -C "$OAI_DIR" rev-parse -q --verify HEAD 2>/dev/null || true)" != "$OAI_COMMIT" ]; then
  log "fetching $OAI_REPO at $OAI_COMMIT (about 0.8 GB to download, 2.2 GB checked out)"
  git -C "$OAI_DIR" fetch --quiet --depth 1 origin "$OAI_COMMIT"
  git -C "$OAI_DIR" -c advice.detachedHead=false checkout --quiet --detach FETCH_HEAD
else
  ok "checkout already present"
fi

verify_oai_tree

fact oai_commit "$OAI_COMMIT"
fact oai_commit_date "$(git -C "$OAI_DIR" log -1 --format=%cI)"
fact oai_commit_subject "$(git -C "$OAI_DIR" log -1 --format=%s)"
fact oai_tree_dirichletl "$OAI_TREE_DIRICHLETL"

# The proof's own files: same count, same size, same bytes as audited, and nothing flagged.
closure_check "$OAI_LEAN" "$OAI_SOLUTION_MODULE" "$CLOSURE_MODULES" "$CLOSURE_LINES" "$CLOSURE_DIGEST" \
  "proof source closure" "$RECEIPT/closure"
fact closure_modules "$CLOSURE_MODULES"
fact closure_lines "$CLOSURE_LINES"
fact closure_digest "$CLOSURE_DIGEST"

# Has OpenAI published anything newer? Informational: this run certifies the pinned commit only.
remote_head="$({ git -C "$OAI_DIR" ls-remote origin HEAD 2>/dev/null || true; } | awk '{print $1}')"
if [ -z "$remote_head" ]; then
  warn "could not read the repository's current head"
  fact oai_remote_head "unknown"
elif [ "$remote_head" = "$OAI_COMMIT" ]; then
  ok "the pinned commit is still the head of OpenAI's repository"
  fact oai_remote_head "$remote_head (same as pinned)"
else
  warn "OpenAI's repository has moved on to $remote_head. This run checks the pinned commit $OAI_COMMIT only; say so in the report"
  fact oai_remote_head "$remote_head (NEWER than pinned)"
fi

mark_phase 4
log "fetch complete: the tree matches the audit"
