# lifo-backpressure-lean

[![Verify Lean claims](https://github.com/electronjoe/lifo-backpressure-lean/actions/workflows/verify-lean.yml/badge.svg)](https://github.com/electronjoe/lifo-backpressure-lean/actions/workflows/verify-lean.yml)
[![Publish Proof Atlas](https://github.com/electronjoe/lifo-backpressure-lean/actions/workflows/pages.yml/badge.svg)](https://github.com/electronjoe/lifo-backpressure-lean/actions/workflows/pages.yml)
[![License: MIT](https://img.shields.io/badge/License-MIT-blue.svg)](LICENSE)

Complete, axiom-clean **Lean 4** formalization and interactive **[Proof Atlas](https://electronjoe.github.io/lifo-backpressure-lean/)** of:

> Longbo Huang, Scott Moeller, Michael J. Neely, and Bhaskar Krishnamachari, *"LIFO-Backpressure Achieves Near-Optimal Utility-Delay Tradeoff,"* IEEE/ACM Transactions on Networking 21(3): 831–844 (2012); arXiv preprint [`arXiv:1008.4895v2`](https://arxiv.org/abs/1008.4895v2).

* **Interactive Proof Atlas (4-View Reader, Dependency Graph & Dashboard):** <https://electronjoe.github.io/lifo-backpressure-lean/>
* **Full Machine-Generated Verification Manifest:** [`dist/VERIFICATION.md`](dist/VERIFICATION.md)
* **Blind Statement Comparisons & Manuscript Revision Suggestions:** [`comparisons.json`](comparisons.json) · [`manuscript-edits.json`](manuscript-edits.json)

---

## Verification Manifest Summary

| Metric | Value |
| :--- | :--- |
| **Pinned Toolchain & Mathlib** | `leanprover/lean4:v4.33.1` · Mathlib [`0df444a360ea`](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474) · **0 third-party packages** |
| **Headline Claims Proved** | **4 / 4 unconditionally closed** (including companion-paper Theorems 2 & 3 proved from first principles) |
| **Transitive Axiom Profile** | Strictly `{propext, Classical.choice, Quot.sound}` — **0 `sorry`, 0 custom `axiom`, 0 `native_decide`, 0 warnings** |
| **Non-Vacuity Witnesses** | **4 / 4 compilable witnesses** (`lean/Examples/`), including the guarded `0 < λ̃_j` clause of Theorem 4 |
| **Owned Lean 4 Scale** | **4,754 non-empty LoC** (5,043 raw lines across 24 `.lean` files; 3,905 checked LoC in Theorem 4 closure) |
| **CI Verification Tier** | **Paranoid (`lean_ci_level: "paranoid"`)** — offline `unshare -rn`, hash-locked `Challenge.lean`/`Solution.lean` kernel comparison, and fresh-environment `leanchecker --fresh` replay |
| **Human Author Sign-Off** | Pending co-author review (`0 / 4` signed off in Proof Atlas; Theorem 4 edits queued in `manuscript-edits.json`) |

### Theorem-by-Theorem Status

| Paper Result | Source Proof | Assembly Declaration | Checked LoC | Witness | Statement Correspondence |
| :--- | :--- | :--- | :---: | :--- | :--- |
| **Theorem 1** (`theorem:little1`, Modified Little's Theorem for LIFO) | `paper/qla-lifo-tech2-v5.tex` (Appendix A) | `Assembly.theorem_little1` | 289 | `Examples.theorem1_witness` | **Match** (slotted discrete time) |
| **Theorem 2** (`theorem:qla-markovian`, `[O(1/V), O(V)]` Markov Tradeoff) | `references/1008.0200v1/` (`[17]`) | `Assembly.theorem_qla_markovian` | 1,982 | `Examples.theorem2_witness` | **Match** (stronger non-causal `optCost`; Poisson proof `basis: "lean"`) |
| **Theorem 3** (`thm:prob_multi_con`, Exponential Attraction) | `references/0904.3795v1/` (`[9]`) | `Assembly.thm_prob_multi_con` | 2,866 | `Examples.theorem3_witness` | **Match** (adds explicit `V ≥ 1`, nonempty `X^(s)`) |
| **Theorem 4** (`thm:qlalifo_delay`, Rate & `O([log V]^2)` Delay) | `paper/qla-lifo-tech2-v5.tex` (Sec. VI-C) | `Assembly.thm_qlalifo_delay` | 3,905 | `Examples.theorem4_witness` | **Sound repair (`difference`)** — 5 documented manuscript findings below |

### Documented Manuscript Findings (Theorem 4 & Minor Clarifications)

All core asymptotic conclusions of `arXiv:1008.4895v2` ($[O(1/V), O(V)]$ tradeoff, $1 - O(1/V^{\log V})$ traffic fraction, and $O([\log V]^2)$ LIFO delay) are **fully verified**. Formalization surfaced five concrete precision issues in Theorem 4, recorded with exact source lines in [`comparisons.json`](comparisons.json) and proposed fixes in [`manuscript-edits.json`](manuscript-edits.json):

1. **Buffer-window width under Eq. (3):** Because Eq. (3) executes service $\mu_j(t) \le \delta_{\max}$ *before* adding arrivals $A_j(t) \le \delta_{\max}$, packets arriving when $q_j(t) \in [Q_{j,\mathrm{Low}}, Q_{j,\mathrm{High}}]$ can land down to $\max(Q_{j,\mathrm{Low}} - \delta_{\max}, 0)$, widening the integer buffer band to $2D + 2K[\log V]^2 + 2\delta_{\max} + 1$ (same $O([\log V]^2/\tilde{\lambda}_j)$ scaling and leading constant $2K/\tilde{\lambda}_j$, coarser by an additive $\delta_{\max}+1$ vs. the printed $+\delta_{\max}$).
2. **Missing $\tilde{\lambda}_j > 0$ guard in Part (b):** Small $V \ge 1$ allows $\tilde{\lambda}_j = 0$, causing division by zero in $W_{\mathrm{bound}}$ (note: an earlier commented draft at L678 of `qla-lifo-tech2-v5.tex` included this guard).
3. **Almost-sure constancy (ergodicity) for DCT:** L593 assumes only that time averages *exist* a.s., whereas the Dominated Convergence step (L641–L648) requires a.s.-constant deterministic limits $\lambda_j, \tilde{\lambda}_j$.
4. **Explicit discrete unit-packet LIFO buffer coupling:** Section III defines real-valued $(A_j, \mu_j, q_j) \in \mathbb{R}_+$, while Theorem 4 applies Theorem 1 to discrete unit packets in integer buffer slots (`LifoQueueRealization`).
5. **Typographical fixes:** Reversed interval endpoints $\mathcal{B}_j \triangleq [Q_{j,\mathrm{High}}, Q_{j,\mathrm{Low}}]$ at L605/L664 (and duplicate `= \defequiv` at L664); explicit $V \ge 1$ in Theorem 3; discrete sum vs. continuous integral in Appendix A.

---

## Reproducing the Lean 4 Verification Locally

Requires [Elan](https://github.com/leanprover/elan) (automatically installs `leanprover/lean4:v4.33.1`) and Python 3.11+:

```bash
# 1. Fetch prebuilt Mathlib .olean cache and build all default targets (0 warnings)
cd lean
lake exe cache get
lake build

# 2. Verify hash-locked Challenge.lean / Solution.lean harness and replay in fresh kernel
cd ..
python3 tools/proof-atlas/scripts/atlas.py challenge . --check
(cd lean && lake --no-cache build Challenge Solution && lake env leanchecker --fresh Solution)

# 3. Rebuild the Proof Atlas explorer, dashboard, and verification manifest
python3 tools/proof-atlas/scripts/atlas.py build .
python3 tools/proof-atlas/scripts/atlas.py manifest .
python3 tools/proof-atlas/scripts/atlas.py review-work . --check
```

---

## Repository Architecture

```text
lifo-backpressure-lean/
  lean/
    lean-toolchain                  # Pinned leanprover/lean4:v4.33.1
    lakefile.toml / lake-manifest.json
    Prelude.lean                    # Narrow targeted Mathlib imports (pure external)
    Statements/                     # Gate-1 SHA-256 frozen specifications (576 raw LoC; no proof imports)
      SystemModel.lean              # NetworkModel, MarkovProcess, Policy, Backpressure, Dual
      Little.lean                   # Theorem 1 statement & BufferSystem
      MarkovTradeoff.lean           # Theorem 2 statement
      ExponentialAttraction.lean    # Theorem 3 statement
      LifoDelay.lean                # Theorem 4 statement & LifoQueueRealization
    Routine/                        # Statement- & proof-isolated shared theory (972 raw LoC)
      MarkovMixing.lean             # Schur, primitivity, Doeblin L¹ mixing, Poisson potential, T_ν
      BackpressureDrift.lean        # Quadratic/distance drift, Padé exp bound, Cesàro stability
    Proofs/                         # Separable per-claim proofs (2,914 raw LoC)
    Examples/                       # Compilable non-vacuity witnesses for Theorems 1–4 (525 raw LoC)
    Assembly.lean                   # Mechanically generated topological proof composition
    Challenge.lean / Solution.lean  # Mechanically generated hash-locked paranoid CI harness
  paper/                            # Bound arXiv:1008.4895v2 LaTeX source & PDF
  references/                       # Companion arXiv LaTeX sources ([17] 1008.0200v1, [9] 0904.3795v1)
  lamport/                          # Distilled human-readable Lamport structured proofs
  evidence/                         # Machine-checked SHA-256 & #print axioms audit receipts
  project.json / reader.json / comparisons.json / manuscript-edits.json
  dist/                             # Built Proof Atlas static site & VERIFICATION.md
  .github/workflows/                # Paranoid Lean CI (verify-lean.yml) & GitHub Pages (pages.yml)
  proof-atlas-lessons.md            # Running lessons journal for the Proof Atlas skill
```

---

## AI-Use & Provenance Disclosure

This Lean 4 formalization, non-vacuity witness suite, Lamport proof distillations, and Proof Atlas metadata were developed under human direction (Scott Moeller) using AI coding and theorem-proving assistance (Google Antigravity CLI with Gemini 4 models) following the [`build-proof-atlas`](tools/proof-atlas/) `thorough` protocol:

* **Trust boundary:** Every proof term is checked mechanically by Lean 4's kernel (`v4.33.1`) and replayed in a fresh kernel environment via `leanchecker --fresh` inside an offline (`unshare -rn`) GitHub Actions workflow against hash-locked `Statements/`, `Challenge.lean`, and `Solution.lean`.
* **Human accountability:** Statement-to-manuscript alignment (`comparisons.json`) and proposed manuscript revisions (`manuscript-edits.json`) are explicitly surfaced for co-author inspection; human sign-off status is tracked transparently on the Proof Atlas dashboard.

---

## License & Citation

* **License:** Lean 4 formalization, Proof Atlas records, and documentation are released under the [MIT License](LICENSE). Bundled arXiv preprints in `paper/` and `references/` remain subject to their original arXiv licenses.
* **Citation:** See [`CITATION.cff`](CITATION.cff) for machine-readable citation metadata for both this formalization repository and the original IEEE/ACM Transactions on Networking paper.
