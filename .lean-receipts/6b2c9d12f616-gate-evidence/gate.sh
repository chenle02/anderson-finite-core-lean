#!/usr/bin/env bash
# Lower-tier gate. Lives in (and writes to) its evidence directory, .lean-receipts/<commit12>-gate-evidence/;
# every path it runs with or records is relative to the repository root, so the committed evidence
# carries no machine-specific path.
set -u
cd "$(git -C "$(dirname "$0")" rev-parse --show-toplevel)"
E="$(realpath --relative-to=. "$(dirname "$0")")"
R="$E/gate-report.txt"; : > "$R"
say(){ echo "$*" | tee -a "$R"; }
say "anderson-finite-core-lean lower-tier gate report"
say "commit: $(git rev-parse HEAD)"; say "tree: $(git rev-parse HEAD^{tree})"; say "dirty-tracked: $(git status --porcelain --untracked-files=no | wc -l)"
say "evidence dir: $E"
say "lean-toolchain: $(cat lean-toolchain)"
say "mathlib_rev: $(python3 -c "import json;print([p['rev'] for p in json.load(open('lake-manifest.json'))['packages'] if p['name']=='mathlib'][0])")"
say "systemd invocation: ${INVOCATION_ID:-none}"; say "date: $(date -u +%FT%TZ)"
say "--- source sha256 (tracked .lean, json, toml, manifest)"; git ls-files '*.lean' '*.json' '*.toml' lean-toolchain | xargs sha256sum | tee -a "$R" >/dev/null
say "--- sorry/admit scan of solution modules (AndersonAudit/)"; n=$(grep -n -E '\bsorry\b|\badmit\b' AndersonAudit/*.lean AndersonAudit.lean | grep -v -E '^\S+:[0-9]+:\s*--' | wc -l); say "sorry_admit_hits: $n"
say "--- lake build"; lake build AndersonAudit ComparatorChallenges > "$E/gate-build.log" 2>&1; b=$?; say "build rc=$b errors=$(grep -c 'error:' "$E/gate-build.log") solution-warnings=$(grep -c '^warning: AndersonAudit' "$E/gate-build.log")"
say "--- axioms"; lake env lean AndersonAudit/Axioms.lean 2>&1 | grep -v 'local changes' > "$E/gate-axioms.txt"; say "axiom lines: $(grep -c 'depends on axioms' "$E/gate-axioms.txt")"; say "sorryAx hits: $(grep -c sorryAx "$E/gate-axioms.txt")"
say "--- leanchecker"; lake env leanchecker AndersonAudit.FiniteCore > "$E/gate-leanchecker.log" 2>&1; lc=$?; say "leanchecker rc=$lc"
say "--- log hashes"; sha256sum "$E/gate-build.log" "$E/gate-axioms.txt" "$E/gate-leanchecker.log" | tee -a "$R" >/dev/null
ok=0; [ "$b" = 0 ] && [ "$lc" = 0 ] && [ "$n" = 0 ] && ! grep -q sorryAx "$E/gate-axioms.txt" || ok=1
say "VERDICT: $([ $ok = 0 ] && echo PASS || echo FAIL)"; echo "EXIT=$ok" > "$E/gate.done"
