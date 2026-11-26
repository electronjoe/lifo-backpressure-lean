# Lamport Proof — Theorem 3 (Exponential Attraction of Queue Backlogs)

*Provenance: Follows Theorem 1 & Appendices A–B of companion paper `arXiv:0904.3795v1` (`delay_reduction_tr_v8_Markovian.tex`, L354–531 & L1120–1333).*

**Theorem 3.** Under $V \ge 1$, unique $\boldsymbol{\gamma}_V^*$, $\eta$-slackness, and $g(\boldsymbol{\gamma}_V^*) \ge g(\boldsymbol{\gamma}) + L\|\boldsymbol{\gamma}_V^* - \boldsymbol{\gamma}\|$ ($L > 0$ independent of $V$), there exist $V$-independent $D, K, c^* > 0$ such that $\mathcal{P}^{(r)}(D, Km) \le c^* e^{-m}$ for all $m \ge 0$.

1. **One-slot squared-distance inequality (Companion App. A, Lemma 2)**
   - 1.1. **Non-expansiveness of $[\cdot]^+$ projection onto $\mathbb{R}_+^r$**: With $B = \sqrt{r}\delta_{\max}$, non-expansiveness of projection onto $\mathbb{R}_+^r$ yields $\|q(t+1) - \gamma_V^*\|^2 \le \|q(t) - \gamma_V^*\|^2 + 2B^2 - 2(\gamma_V^* - q(t))^\top (A(t) - \mu(t))$.
     - *Uses:* `Routine.BackpressureDrift.sum_dist_sq_drift`
     - *Lean:* `Routine.BackpressureDrift.sum_dist_sq_drift`
   - 1.2. **Backpressure produces a subgradient of $g_{S(t)}$**: By Eq. (6) optimality, $A(t) - \mu(t)$ is a subgradient of $g_{S(t)}(V, \cdot)$ at $q(t)$, so $(\gamma_V^* - q(t))^\top (A(t) - \mu(t)) \ge g_{S(t)}(\gamma_V^*) - g_{S(t)}(q(t))$.
     - *Uses:* `FollowsBackpressure`
     - *Lean:* `Proofs.ExponentialAttraction.bp_subgradient_bound`

2. **$T_\nu$-slot expected quadratic drift (Companion App. A, Lemma 1)**
   - 2.1. **$V$-independent convergent mixing interval $T_\nu$**: Choose $\nu = L/(2B) > 0$. By geometric mixing of $S(t)$, there exists a $V$-independent horizon $T_\nu \ge 1$ such that $\sum_s |\pi_s - \frac{1}{T_\nu}\sum_{\tau=0}^{T_\nu-1} P^\tau(s_0, s)| \le \nu$ for every $s_0$.
     - *Uses:* `Routine.MarkovMixing.exists_convergent_interval`
     - *Lean:* `Routine.MarkovMixing.exists_convergent_interval`
   - 2.2. **Multi-slot conditional quadratic drift**: Summing Step `⟨1⟩1` over $\tau = 0, \dots, T_\nu - 1$, using $B$-Lipschitzness of $g_s$ and $\|q(t+\tau) - q(t)\| \le \tau B$, gives $\mathbb{E}[\|q(t+T_\nu)-\gamma_V^*\|^2 \mid \mathcal{H}(t)] \le \|q(t)-\gamma_V^*\|^2 + (T_\nu^2+T_\nu)B^2 - 2T_\nu(g(\gamma_V^*)-g(q(t))) + 2T_\nu \nu B \|\gamma_V^*-q(t)\|$.
     - *Uses:* `⟨1⟩1.⟨2⟩1`, `⟨1⟩1.⟨2⟩2`, `⟨1⟩2.⟨2⟩1`
     - *Lean:* `Proofs.ExponentialAttraction.multi_slot_dist_sq_drift`

3. **Linear negative drift outside radius $D$**
   - 3.1. **Polyhedral growth + Jensen yield strict contraction**: Set $\eta_d := T_\nu L / 4 > 0$ and $D := \max\!\left(\frac{(T_\nu^2+T_\nu)B^2 - \eta_d^2}{2T_\nu(L - \eta_d/T_\nu - B\nu)}, \eta_d\right)$ (all $V$-independent). Applying $g(\gamma_V^*) - g(q(t)) \ge L\|\gamma_V^* - q(t)\|$ and Jensen's inequality shows that whenever $Y(t) := \|q(t) - \gamma_V^*\| \ge D$, $\mathbb{E}[Y(t+T_\nu) \mid \mathcal{H}(t)] \le Y(t) - \eta_d$.
     - *Uses:* `⟨1⟩2.⟨2⟩2`, `DualPolyhedral`
     - *Lean:* `Proofs.ExponentialAttraction.linear_negative_drift`

4. **Exponential Lyapunov drift & Markov's inequality (Q.E.D.)**
   - 4.1. **Padé exponential bound on $\tilde{Y}(t) = \max(Y(t) - D, 0)$**: With $w := \eta_d / (T_\nu^2 B^2 + T_\nu B \eta_d / 3)$, since $|\tilde{Y}(t+T_\nu)-\tilde{Y}(t)| \le T_\nu B$ and $w T_\nu B < 3$, the Padé bound $e^y \le 1 + y + \frac{y^2}{2(1 - y/3)}$ yields $\mathbb{E}[e^{w\tilde{Y}(t+T_\nu)} - e^{w\tilde{Y}(t)}] \le e^{2wT_\nu B} - \frac{w\eta_d}{2}\mathbb{E}[e^{w\tilde{Y}(t)}]$.
     - *Uses:* `⟨1⟩3.⟨2⟩1`, `Routine.BackpressureDrift.exp_le_quad_div`
     - *Lean:* `Proofs.ExponentialAttraction.exp_lyapunov_drift`
   - 4.2. **Telescope & apply Markov's inequality (Q.E.D.)**: Telescoping along residue classes $t_0 + j T_\nu$ bounds $\limsup \frac{1}{t}\sum_{\tau<t}\mathbb{E}[e^{w\tilde{Y}(\tau)}] \le \frac{2}{w\eta_d} e^{2wT_\nu B} =: c^*$. Setting $K := 1/w$, Markov's inequality yields $\mathcal{P}^{(r)}(D, Km) \le c^* e^{-wKm} = c^* e^{-m}$. $\blacksquare$
     - *Uses:* `⟨1⟩4.⟨2⟩1`
     - *Lean:* `Assembly.thm_prob_multi_con`
