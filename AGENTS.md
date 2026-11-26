# Project Instructions & Durable Memory (`lifo-backpressure-lean`)

## Standing Operational Rules
1. **Proof Atlas Skill Lessons Journal (`proof-atlas-lessons.md`):**
   - Continuously record any issues, friction, bugs, edge cases, or improvement ideas encountered in the `../proof-atlas/` (`build-proof-atlas`) skill into `proof-atlas-lessons.md` as we go along.
   - Include concrete symptoms, script/line references where applicable, workarounds used, and suggested fixes.
2. **40% Context Handoff Rule:**
   - Whenever context usage approaches ~40%, stop cleanly, save durable progress in the repo (`project.json` checkpoints, `proof-atlas-lessons.md`, and `HANDOFF.md`), rebuild & publish the latest GitHub Pages for the Proof Atlas so progress is immediately visible online, and emit a succinct copy-paste prompt so a fresh session can resume seamlessly.
3. **Atomic Git Commits per Logical Milestone:**
   - Make small, atomic Git commits at each logical unit of effort (e.g., after closing/auditing each theorem, after landing a verified `Routine/` foundation library, after adding witnesses/distillation) rather than accumulating multi-theorem changes uncommitted.
4. **Formalization Scope & Policy:**
   - **Scope / Profile:** Paper-wide (`mode: "paper"`), `thorough` profile across all 4 theorems of `arXiv:1008.4895v2` (including proving Theorems 2 and 3 from the companion papers in `references/`).
   - **Statement Policy:** Formalize the clean, mathematically true statement (e.g., adding the missing $\tilde{\lambda}_j > 0$ guard, ergodicity/a.s.-constant time average hypothesis, and exact buffer-window width under Eq. (3) for Theorem 4), and explicitly document every added hypothesis or constant adjustment in `comparisons.json` and propose synchronized entries in `manuscript-edits.json` to build revision suggestions for the paper.
   - **Hosting & CI:** Public GitHub repo `electronjoe/lifo-backpressure-lean` with GitHub Pages and GitHub Actions independent Lean verification (`paranoid` tier: offline `unshare -rn`, hash-locked `Challenge.lean`/`Solution.lean`, and `leanchecker --fresh`).
   - **Lean Package:** `lean/` (`LifoBackpressure`), pinned to `leanprover/lean4:v4.33.1` with matching Mathlib, structured with `Prelude.lean`, `Statements/`, `Routine/`, `Proofs/`, `Examples/`, and `Assembly.lean`.
