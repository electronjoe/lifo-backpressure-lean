# lifo-backpressure-lean

Lean validation of Huang, Longbo, Scott Moeller, Michael J. Neely, and Bhaskar Krishnamachari, *"LIFO-backpressure achieves near-optimal utility-delay tradeoff,"* IEEE/ACM Transactions on Networking 21.3 (2012): 831–844 (arXiv preprint `arXiv:1008.4895v2`).

## Source Material & Layout

Prefer reading the author-submitted `.tex` files for exact notation, equations, and proofs; use the PDF for inspecting figures (e.g., Fig. 14 in Appendix A).

* `paper/` — Main paper (`arXiv:1008.4895v2`):
  * `paper/qla-lifo-tech2-v5.tex` & `paper/qla-lifo-tech2-v5.bbl` — Author LaTeX source and bibliography.
  * `paper/1008.4895v2.pdf` — Compiled arXiv PDF (includes figures).
* `references/` — Companion arXiv LaTeX sources supplying the two externally cited theorems:
  * `references/1008.0200v1/pure-qla-markovian-v9.tex` (`.bbl`) — Huang & Neely, *"Max-Weight Achieves the Exact $[O(1/V), O(V)]$ Utility-Delay Tradeoff Under Markov Dynamics"* (`arXiv:1008.0200v1`, cited as `[17]`).
  * `references/0904.3795v1/delay_reduction_tr_v8_Markovian.tex` (`.bbl`) — Huang & Neely, *"Delay Reduction via Lagrange Multipliers in Stochastic Network Optimization"* (`arXiv:0904.3795v1` / IEEE TAC 2011, cited as `[9]`).

## Theorem & Proof Map

| Paper Result | Statement | Proof Location | Key Dependencies |
| --- | --- | --- | --- |
| **System Model & Dual Problem** | `paper/qla-lifo-tech2-v5.tex` (Sections II–V, L239–L471) | — | Finite-state irreducible aperiodic Markov chain $S(t)$, compact $\mathcal{X}^{(s_i)}$, $\eta$-slackness |
| **Theorem 1** (Modified Little's Theorem for LIFO) | `paper/qla-lifo-tech2-v5.tex` (`\label{theorem:little1}`, L524–L534) | Appendix A (L1019–L1104) & Fig. 14 | Sample-path argument (pure real analysis / finite sums) |
| **Theorem 2** (`[O(1/V), O(V)]` under Markovian $S(t)$) | `paper/qla-lifo-tech2-v5.tex` (`\label{theorem:qla-markovian}`, L540–L549) | `references/1008.0200v1/pure-qla-markovian-v9.tex` (`\label{thm:generalq}`, L452–L730; primal-dual equality `\label{thm:primaldualequal}`, Appendix A L731–L935) | Variable multi-slot Lyapunov drift, Carathéodory's theorem, convex duality/subgradients, finite Markov chain return-time identities |
| **Theorem 3** (Exponential Attraction) | `paper/qla-lifo-tech2-v5.tex` (`\label{thm:prob_multi_con}`, L553–L570) | `references/0904.3795v1/delay_reduction_tr_v8_Markovian.tex` (`\label{theorem:prob_multicon_polyhedral}` & `\label{thm:prob_multi_con}`, L354–L562; Appendices A & B, L1120–L1333) | Projection non-expansiveness, Markov convergent interval $T_\nu$, elementary $e^y$ Taylor bound |
| **Theorem 4** (LIFO-Backpressure rate & $O([\log V]^2)$ delay) | `paper/qla-lifo-tech2-v5.tex` (`\label{thm:qlalifo_delay}`, L610–L629) | Section VI-C (L635–L666) | Theorems 1, 2, 3, and Dominated Convergence Theorem |

### Notes for Formalization
* Watch for minor typos in the original `.tex`, e.g. $\mathcal{B}_j \triangleq [Q_{j,\mathrm{High}}, Q_{j,\mathrm{Low}}]$ at L605 and L664 has the interval endpoints written reversed (it means $[Q_{j,\mathrm{Low}}, Q_{j,\mathrm{High}}]$, as used at L652 and L656).
* No additional custom papers beyond `references/` are required for end-to-end validation; all remaining prerequisites are standard textbook mathematics (convex analysis, finite-state Markov chains, Dominated Convergence).

