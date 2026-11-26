# Lamport Proof — Theorem 2 ($[O(1/V), O(V)]$ Utility-Delay Tradeoff Under Markov Dynamics)

*Provenance: Lean-only proof route (`basis: "lean"`). The manuscript cites `arXiv:1008.0200v1` (variable multi-slot return-time drift + Carathéodory strong duality). Our Lean formalization proves the exact same Theorem 2 directly via finite-Markov Doeblin mixing, Poisson's equation, and elementary weak duality—avoiding renewal stopping times.*

**Theorem 2.** Under finite-state irreducible aperiodic $S(t)$ and $\eta$-slackness, there exist $V$-independent $C_{\mathrm{cost}}, C_{q0}, C_{q1} \ge 0$ such that for all $V \ge 1$, Backpressure is stable and achieves $f^*_{av} \le f^{BP}_{av} \le f^*_{av} + C_{\mathrm{cost}}/V$ and $\overline{q}^{BP} \le C_{q0} + C_{q1} V$.

1. **Geometric mixing & Poisson's equation for finite Markov chain $S(t)$**
   - 1.1. **Primitivity from irreducibility + aperiodicity**: By Schur's additive submonoid theorem on finite `State`, irreducibility and aperiodicity imply $P$ is primitive: $\exists m > 0,\, \forall s, s',\, P^m(s, s') > 0$.
     - *Uses:* `Routine.MarkovMixing.exists_matPow_pos`
     - *Lean:* `Routine.MarkovMixing.exists_matPow_pos`
   - 1.2. **Doeblin $L^1$ geometric mixing**: Doeblin contraction gives $C_{\mathrm{mix}}, \rho \in (0, 1)$ (depending only on $P$) with $\sum_{s'} |P^n(s,s') - \pi_{s'}| \le C_{\mathrm{mix}} \rho^n$, so $C' := \sum_{n=0}^\infty \sup_s \sum_{s'} |P^n(s,s') - \pi_{s'}| < \infty$.
     - *Uses:* `⟨1⟩1.⟨2⟩1`
     - *Lean:* `Routine.MarkovMixing.exists_geometric_mixing`
   - 1.3. **Lipschitz Poisson potential $h(V, \gamma, s)$**: Define $h(V,\gamma,s) := \sum_{n=0}^\infty \sum_{s'} (P^n(s,s') - \pi_{s'}) g_{s'}(V,\gamma)$. It solves $g_s - g = h(s) - (Ph)(s)$, is $(C'B)$-Lipschitz in $\gamma$ ($B = \sqrt{r}\delta_{\max}$), and satisfies $|h(V,\gamma,s)| \le C'(V\delta_{\max} + B\|\gamma\|)$.
     - *Uses:* `⟨1⟩1.⟨2⟩2`
     - *Lean:* `Routine.MarkovMixing.poisson_equation`

2. **Elementary weak duality ($g(V, \gamma) \le V f^*_{av}$ for all $\gamma \succeq 0$)**
   - 2.1. **Per-slot dual lower bound for any policy $\Pi$**: For any measurable stable policy $\Pi$ and $\gamma \succeq 0$, $g_{S(\tau)}(V,\gamma) \le V f^\Pi(\tau) + \sum_j \gamma_j (A_j^\Pi(\tau) - \mu_j^\Pi(\tau))$, and Eq. (3) gives $A_j^\Pi - \mu_j^\Pi \le q_j^\Pi(\tau+1) - q_j^\Pi(\tau)$.
     - *Uses:* Eq. (3) dynamics, `dualState` def
     - *Lean:* `Proofs.MarkovTradeoff.dual_le_V_mul_avgCost`
   - 2.2. **Cesàro subsequence eliminates boundary queue term**: Summing over $\tau < t$ and taking expectations gives $\frac{1}{t}\sum_{\tau<t}\mathbb{E}[g_{S(\tau)}] \le V \cdot \frac{1}{t}\sum_{\tau<t}\mathbb{E}[f^\Pi] + \frac{1}{t}\sum_j \gamma_j \mathbb{E}[q_j^\Pi(t)]$. Stability forces $\liminf_{t\to\infty} \mathbb{E}[q_j^\Pi(t)]/t = 0$, yielding $g(V,\gamma) \le V f^*_{av}$.
     - *Uses:* `⟨1⟩2.⟨2⟩1`, `Routine.BackpressureDrift.exists_small_ratio_of_avg_limsup_lt_top`
     - *Lean:* `Proofs.MarkovTradeoff.dual_le_V_mul_optCost`

3. **One-slot Lyapunov drift + Poisson telescoping**
   - 3.1. **Quadratic drift under Backpressure**: For $L(t) = \frac{1}{2}\sum_j q_j(t)^2$, Eq. (3) and Eq. (6) optimality yield $L(t+1) - L(t) + V f^{BP}(t) \le B^2 + g_{S(t)}(V, q(t))$.
     - *Uses:* `Routine.BackpressureDrift.sum_quad_drift`, `FollowsBackpressure`
     - *Lean:* `Proofs.MarkovTradeoff.bp_one_slot_drift`
   - 3.2. **Telescope perturbed Lyapunov function $L(t) + h(q(t), S(t))$**: Substituting Poisson's equation and using $|h(q(t+1), S(t+1)) - h(q(t), S(t+1))| \le C'B^2$ gives $\mathbb{E}[L(t+1)+h_{t+1}] - \mathbb{E}[L(t)+h_t] + V\mathbb{E}[f^{BP}(t)] \le (1+C')B^2 + \mathbb{E}[g(V, q(t))]$. Completing the square bounds $L(T) + h_T$ uniformly below.
     - *Uses:* `⟨1⟩1.⟨2⟩3`, `⟨1⟩3.⟨2⟩1`
     - *Lean:* `Proofs.MarkovTradeoff.perturbed_lyapunov_telescope`

4. **Conclude $[O(1/V), O(V)]$ bounds (Q.E.D.)**
   - 4.1. **$O(V)$ backlog & stability from $\eta$-slackness**: Using $g(V, q) \le V\delta_{\max} - \eta\sum_j q_j$ yields $\overline{q}^{BP} \le ((1+C')B^2 + V\delta_{\max})/\eta = O(V)$ and stability.
     - *Uses:* `⟨1⟩3.⟨2⟩2`, `HasSlackness`
     - *Lean:* `Proofs.MarkovTradeoff.theorem2`
   - 4.2. **$O(1/V)$ cost optimality from weak duality (Q.E.D.)**: Using $g(V, q) \le V f^*_{av}$ (`⟨1⟩2.⟨2⟩2`) yields $f^{BP}_{av} \le f^*_{av} + (1+C')B^2/V$, while stability gives $f^*_{av} \le f^{BP}_{av}$. $\blacksquare$
     - *Uses:* `⟨1⟩2.⟨2⟩2`, `⟨1⟩3.⟨2⟩2`, `⟨1⟩4.⟨2⟩1`
     - *Lean:* `Assembly.theorem_qla_markovian`
