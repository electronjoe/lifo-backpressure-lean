# Lamport Proof — Theorem 3 (Exponential Attraction of Queue Backlogs)

*Provenance: Follows Theorem 1 & Appendices A–B of companion paper `arXiv:0904.3795v1` (`delay_reduction_tr_v8_Markovian.tex`, lines 354–531 and 1120–1333).*

**Theorem 3.** Under unique `γ*_V`, `η`-slackness, and `g(γ*_V) ≥ g(γ) + L ‖γ*_V - γ‖` (`L > 0` independent of `V`), there exist `V`-independent constants `D, K, c* > 0` such that under Backpressure, `P^(r)(D, K m) ≤ c* e^{-m}` for all `m ≥ 0`.

1. **One-slot distance inequality (Appendix A, Lemma 2).**
   - 1.1. By non-expansiveness of projection `[·]^+` onto `ℝ^r_+` and `q(t), μ(t), A(t) ⪰ 0`,
     `‖q(t+1) - γ*_V‖^2 ≤ ‖q(t) - γ*_V‖^2 + 2 B^2 - 2 (γ*_V - q(t))^T (A(t) - μ(t))`,
     where `B = √r δ_max`.
   - 1.2. By Backpressure optimality (Eq. 6), `A(t) - μ(t)` is a subgradient of `g_{S(t)}(V, ·)` at `q(t)`, so `(γ*_V - q(t))^T (A(t) - μ(t)) ≥ g_{S(t)}(γ*_V) - g_{S(t)}(q(t))`.

2. **`T_ν`-slot expected quadratic drift (Appendix A, Lemma 1).**
   - 2.1. Choose `ν = L / (2 B) > 0` (independent of `V`). By geometric mixing of the finite irreducible aperiodic Markov chain `S(t)`, there exists a `V`-independent convergent interval `T_ν ≥ 1` such that `∑_s |π_s - (1/T_ν) ∑_{τ=0}^{T_ν-1} P^τ(s_0, s)| ≤ ν` for every `s_0`.
   - 2.2. Summing Step 1 over `τ = 0, …, T_ν - 1`, using `B`-Lipschitzness of `g_s` and `‖q(t+τ) - q(t)‖ ≤ τ B`, and taking conditional expectation over the Markov history `H(t)` gives
     `E[‖q(t + T_ν) - γ*_V‖^2 | H(t)] ≤ ‖q(t) - γ*_V‖^2 + (T_ν^2 + T_ν) B^2 - 2 T_ν (g(γ*_V) - g(q(t))) + 2 T_ν ν B ‖γ*_V - q(t)‖`.

3. **Linear negative drift outside radius `D` (Theorem 1(a)).**
   - 3.1. Set `η_d := T_ν (L - B ν) / 2 = T_ν L / 4 > 0` and `D := max(((T_ν^2 + T_ν) B^2 - η_d^2) / (2 T_ν (L - η_d/T_ν - B ν)), η_d)` (all independent of `V`).
   - 3.2. Applying the polyhedral bound `g(γ*_V) - g(q(t)) ≥ L ‖γ*_V - q(t)‖` and Jensen's inequality shows that whenever `Y(t) := ‖q(t) - γ*_V‖ ≥ D`, `E[Y(t + T_ν) | H(t)] ≤ Y(t) - η_d`.

4. **Exponential Lyapunov drift & Markov's inequality (Theorem 1(b) & Appendix B).**
   - 4.1. Let `Ỹ(t) := max(Y(t) - D, 0)` and `w := η_d / (T_ν^2 B^2 + T_ν B η_d / 3)`. Since `|Ỹ(t+T_ν) - Ỹ(t)| ≤ T_ν B` and `w T_ν B < 3`, the Taylor bound `e^y ≤ 1 + y + y^2 / (2 (1 - y/3))` yields `E[e^{w Ỹ(t+T_ν)} - e^{w Ỹ(t)}] ≤ e^{2 w T_ν B} - (w η_d / 2) E[e^{w Ỹ(t)}]`.
   - 4.2. Telescoping over arithmetic progressions `t_0 + j T_ν` (`t_0 = 0, …, T_ν - 1`), summing, dividing by `N T_ν`, and taking `limsup` gives `limsup (1/t) ∑_{τ<t} E[e^{w Ỹ(τ)}] ≤ (2 / (w η_d)) e^{2 w T_ν B} =: c*`.
   - 4.3. Set `K := 1 / w`. Since `∃ j, |q_j(τ) - γ*_{Vj}| > D + K m` implies `Ỹ(τ) > K m`, Markov's inequality gives `P^(r)(D, K m) ≤ c* e^{-w K m} = c* e^{-m}`. ∎
