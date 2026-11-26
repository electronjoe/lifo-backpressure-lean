# Lamport Proof — Theorem 4 (LIFO-Backpressure Throughput & $O([\log V]^2)$ Delay)

*Provenance: Follows Section VI-C of `arXiv:1008.4895v2` (L635–666), with explicit rigor for the Fatou never-departing bound, a.s.-constant DCT, $\tilde{\lambda}_j > 0$ guard, and Eq. (3) window width $2D + 2K(\log V)^2 + 2\delta_{\max} + 1$.*

**Theorem 4.** Under $V \ge 1$, unique $\boldsymbol{\gamma}_V^*$, $\eta$-slackness, polyhedral growth (15), and a.s.-constant $\lambda_j > 0, \tilde{\lambda}_j$: (a) the in-window eventually-departing rate equals $\tilde{\lambda}_j$ a.s. with $\lambda_j \ge \tilde{\lambda}_j \ge [\lambda_j - \delta_{\max} c^* / V^{\log V}]^+$; (b) whenever $\tilde{\lambda}_j > 0$, their $\limsup$ average delay is at most $(2D + 2K(\log V)^2 + 2\delta_{\max} + 1)/\tilde{\lambda}_j$ a.s.

1. **Zero rate of never-departing packets (Theorem 2 + Fatou)**
   - 1.1. **Finite expected average backlog**: By Theorem 2, Backpressure is stable so queue $j$ has finite expected time-average backlog: $\limsup_{t\to\infty} \frac{1}{t}\sum_{\tau<t} \mathbb{E}[q_j(\tau)] < \infty$.
     - *Uses:* Theorem 2 (`Assembly.theorem_qla_markovian`)
     - *Lean:* `Proofs.LifoDelay.never_depart_rate_zero`
   - 1.2. **Fatou bounds the monotone never-departing count $N_\infty(\tau)$**: The count $N_\infty(\tau, \omega)$ of packets arriving before $\tau$ that never depart is monotone nondecreasing and bounded by $q_j(\tau, \omega)$. Fatou's lemma yields $\mathbb{E}[\sup_\tau N_\infty(\tau)] < \infty$, hence $\sup_\tau N_\infty(\tau) < \infty$ a.s.
     - *Uses:* `⟨1⟩1.⟨2⟩1`, `LifoQueueRealization.never_depart_le_queue`
     - *Lean:* `Proofs.LifoDelay.ae_eventually_bounded_never_depart`
   - 1.3. **In-window eventually-departing rate equals $\tilde{\lambda}_j$ a.s.**: Subtracting a bounded count divided by $t$ vanishes as $t \to \infty$, so the a.s. arrival rate of in-window *eventually-departing* packets equals $\tilde{\lambda}_j$.
     - *Uses:* `⟨1⟩1.⟨2⟩2`
     - *Lean:* `Proofs.LifoDelay.window_departing_rate_eq`

2. **Throughput-fraction bound — Part (a) (Theorem 3 + DCT)**
   - 2.1. **Dominated Convergence on out-of-window arrivals**: Set $\tilde{\lambda}_j^c := \lambda_j - \tilde{\lambda}_j$ and $1_j(\tau) := \mathbf{1}_{q_j(\tau) \notin \mathcal{B}_j}$. Because $\frac{1}{t}\sum_{\tau<t} A_j(\tau)1_j(\tau) \to \tilde{\lambda}_j^c$ a.s. (deterministic limit!) and is bounded by $\delta_{\max}$, Dominated Convergence gives $\tilde{\lambda}_j^c = \lim_{t\to\infty} \frac{1}{t}\sum_{\tau<t} \mathbb{E}[A_j(\tau)1_j(\tau)]$.
     - *Uses:* a.s.-constant ergodicity hypothesis
     - *Lean:* `Proofs.LifoDelay.out_of_window_rate_le`
   - 2.2. **Apply Theorem 3 at $m := (\log V)^2$**: Since $q_j(\tau) \notin [Q_{j,\mathrm{Low}}, Q_{j,\mathrm{High}}]$ implies $|q_j(\tau) - \gamma_{Vj}^*| > D + K(\log V)^2$, Theorem 3 at $m = (\log V)^2 \ge 0$ yields $\tilde{\lambda}_j^c \le \delta_{\max}\,\mathcal{P}^{(r)}(D, K(\log V)^2) \le \delta_{\max} c^* e^{-(\log V)^2} = \delta_{\max} c^* / V^{\log V}$.
     - *Uses:* `⟨1⟩2.⟨2⟩1`, Theorem 3 (`Assembly.thm_prob_multi_con`)
     - *Lean:* `Proofs.LifoDelay.theorem4_part_a`

3. **$O([\log V]^2)$ delay bound — Part (b) (Theorem 1)**
   - 3.1. **Exact enlarged buffer slot set $\tilde{\mathcal{B}}_j$ under Eq. (3)**: Assume $\tilde{\lambda}_j > 0$. Because Eq. (3) applies service $\mu_j \le \delta_{\max}$ *before* arrivals $A_j \le \delta_{\max}$, packets arriving while $q_j(t) \in [Q_{j,\mathrm{Low}}, Q_{j,\mathrm{High}}]$ land in integer slots inside $\tilde{\mathcal{B}}_j = [\max(Q_{j,\mathrm{Low}}-\delta_{\max},0), Q_{j,\mathrm{High}}+\delta_{\max})$, whose cardinality is at most $2D + 2K(\log V)^2 + 2\delta_{\max} + 1$.
     - *Uses:* `LifoQueueRealization.slot_bounds`, `0 < lamTilde` guard
     - *Lean:* `Proofs.LifoDelay.tight_slot_card_le`
   - 3.2. **Invoke Modified Little's Theorem (Q.E.D.)**: Restricting to in-window eventually-departing packets gives a `BufferSystem` over $\tilde{\mathcal{B}}_j$ with a.s. arrival rate $\tilde{\lambda}_j > 0$ (hence $D(t) \ge N(t) - |\tilde{\mathcal{B}}_j| \to \infty$). Theorem 1 directly yields $\limsup_{t\to\infty} \mathrm{avgDelay}(t) \le (2D + 2K(\log V)^2 + 2\delta_{\max} + 1) / \tilde{\lambda}_j$ a.s. $\blacksquare$
     - *Uses:* `⟨1⟩1.⟨2⟩3`, `⟨1⟩3.⟨2⟩1`, Theorem 1 (`Assembly.theorem_little1`)
     - *Lean:* `Assembly.thm_qlalifo_delay`
