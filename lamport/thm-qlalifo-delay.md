# Lamport Proof — Theorem 4 (LIFO-Backpressure Throughput & `O([log V]^2)` Delay)

*Provenance: Follows Section VI-C of `arXiv:1008.4895v2` (lines 635–666) with explicit rigor for the Fatou never-departing step, a.s.-constant Dominated Convergence, `λ̃_j > 0` guard, and Eq. (3) buffer window width `2D + 2K[log V]^2 + 2 δ_max + 1`.*

**Theorem 4.** Under `V ≥ 1`, unique `γ*_V`, `η`-slackness, and polyhedral dual growth (15), let `D, K, c* > 0` be the `V`-independent constants from Theorem 3 and `B_j = [Q_{j,Low}, Q_{j,High}]`. For any queue `j` with a.s.-constant arrival rate `λ_j > 0` and in-window arrival rate `λ̃_j`:
- (a) The rate of packets arriving when `q_j(t) ∈ B_j` that eventually depart equals `λ̃_j` a.s. and satisfies `λ_j ≥ λ̃_j ≥ max(λ_j - δ_max c* / V^{log V}, 0)`.
- (b) Whenever `λ̃_j > 0`, their `limsup` average delay is at most `(2D + 2K [log V]^2 + 2 δ_max + 1) / λ̃_j` a.s.

1. **Zero rate of never-departing packets (via Theorem 2 + Fatou).**
   - 1.1. By Theorem 2, queue `j` has finite expected time-average backlog: `limsup_{t→∞} (1/t) ∑_{τ<t} E[q_j(τ)] < ∞`.
   - 1.2. Let `N_∞(τ, ω)` be the count of packets arriving before `τ` that never depart. It is monotone nondecreasing in `τ` with `N_∞(τ, ω) ≤ q_j(τ, ω)`.
   - 1.3. By monotone convergence / Fatou's lemma, `E[sup_τ N_∞(τ)] < ∞`, so `sup_τ N_∞(τ, ω) < ∞` almost surely: only finitely many packets ever fail to depart.
   - 1.4. Subtracting a bounded count divided by `t` does not change the time-average limit, so the a.s. arrival rate of in-window *eventually-departing* packets equals `λ̃_j`.

2. **Throughput-fraction bound (Part (a), via Theorem 3 + Dominated Convergence).**
   - 2.1. Define `λ̃_j^c := λ_j - λ̃_j`. Clearly `0 ≤ λ̃_j ≤ λ_j` since `0 ≤ A_j(τ) · 1_{q_j(τ) ∈ B_j} ≤ A_j(τ)`.
   - 2.2. With `1_j(τ) = 1_{q_j(τ) ∉ B_j}`, `(1/t) ∑_{τ<t} A_j(τ) 1_j(τ) → λ̃_j^c` almost surely and is uniformly bounded by `δ_max`.
   - 2.3. By the Lebesgue Dominated Convergence Theorem, `λ̃_j^c = lim_{t→∞} (1/t) ∑_{τ<t} E[A_j(τ) 1_j(τ)]`.
   - 2.4. Since `0 ≤ A_j(τ) ≤ δ_max` and `q_j(τ) ≥ 0`, `q_j(τ) ∉ [Q_{j,Low}, Q_{j,High}]` implies `|q_j(τ) - γ*_{Vj}| > D + K [log V]^2`.
   - 2.5. Applying Theorem 3 with `m := [log V]^2 ≥ 0` (since `V ≥ 1`) gives
     `λ̃_j^c ≤ δ_max · P^(r)(D, K [log V]^2) ≤ δ_max c* e^{-[log V]^2} = δ_max c* / V^{log V}`,
     proving `λ̃_j ≥ max(λ_j - δ_max c* / V^{log V}, 0)`.

3. **Delay bound (Part (b), via Theorem 1).**
   - 3.1. Assume `λ̃_j > 0`. Under Eq. (3) (`q_j(t+1) = max(q_j(t) - μ_j(t), 0) + A_j(t)` with `μ_j, A_j ≤ δ_max`), every packet arriving while `q_j(t) ∈ [Q_{j,Low}, Q_{j,High}]` occupies an integer buffer slot in `B̃_j := [⌊max(Q_{j,Low} - δ_max, 0)⌋, ⌈Q_{j,High} + δ_max⌉)`.
   - 3.2. The cardinality of `B̃_j` satisfies `|B̃_j| ≤ (Q_{j,High} + δ_max) - max(Q_{j,Low} - δ_max, 0) + 1 ≤ 2D + 2K [log V]^2 + 2 δ_max + 1`.
   - 3.3. Restricting to in-window eventually-departing packets yields a `BufferSystem` over `B̃_j` whose arrival rate is `λ̃_j > 0` a.s. (Step 1.4), hence `D(t) ≥ N(t) - |B̃_j| → ∞` a.s.
   - 3.4. Applying Theorem 1 directly gives `limsup_{t→∞} (1/D(t)) ∑_{i=1}^{D(t)} W_i ≤ |B̃_j| / λ̃_j ≤ (2D + 2K [log V]^2 + 2 δ_max + 1) / λ̃_j` a.s. ∎
