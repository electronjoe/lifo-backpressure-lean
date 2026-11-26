# Lamport Proof — Theorem 2 (`[O(1/V), O(V)]` Utility-Delay Tradeoff Under Markov Dynamics)

*Provenance: Lean proof route (`basis: "lean"`). The manuscript cites `arXiv:1008.0200v1` (variable multi-slot return-time drift + Carathéodory strong duality). Our Lean proof proves the exact same Theorem 2 via finite-Markov-chain geometric mixing (Poisson's equation) and direct elementary weak duality, avoiding renewal stopping times and unproved convergence-of-averages assumptions.*

**Theorem 2.** Under a finite-state irreducible aperiodic Markov chain `S(t)` and `η`-slackness, there exist `V`-independent constants `C_cost, C_q0, C_q1 ≥ 0` such that for all `V ≥ 1`, Backpressure (FIFO or LIFO) is stable and satisfies `f^*_av ≤ f^{BP}_av ≤ f^*_av + C_cost / V` and `q̄^{BP} ≤ C_q0 + C_q1 V`.

1. **Geometric mixing & Poisson's equation for finite irreducible aperiodic Markov chains.**
   - 1.1. By irreducibility and aperiodicity of `P` on finite `State`, `P` is primitive (`∃ m > 0, ∀ s s', P^m(s, s') > 0`).
   - 1.2. Doeblin contraction gives `C_mix, ρ ∈ (0, 1)` (depending only on `P`) with `∑_{s'} |P^n(s, s') - π_{s'}| ≤ C_mix ρ^n` for all `n, s`, so `C' := ∑_{n=0}^∞ sup_s ∑_{s'} |P^n(s, s') - π_{s'}| < ∞`.
   - 1.3. Define the Poisson potential `h(V, γ, s) := ∑_{n=0}^∞ ∑_{s'} (P^n(s, s') - π_{s'}) g_{s'}(V, γ)`. It satisfies `g_s(V, γ) - g(V, γ) = h(V, γ, s) - ∑_{s'} P(s, s') h(V, γ, s')` and is `(C' B)`-Lipschitz in `γ` (`B = √r δ_max`), with `|h(V, γ, s)| ≤ C' (V δ_max + B ‖γ‖)`.

2. **Direct weak duality (`g(V, γ) ≤ V f^*_av` for all `γ ⪰ 0`).**
   - 2.1. For any feasible stable policy `Π` and any `γ ⪰ 0`, `g_{S(τ)}(V, γ) ≤ V f^Π(τ) + ∑_j γ_j (A_j^Π(τ) - μ_j^Π(τ))`.
   - 2.2. From Eq. (3), `A_j^Π(τ) - μ_j^Π(τ) ≤ q_j^Π(τ+1) - q_j^Π(τ)`. Summing over `τ < t` and taking expectations gives `(1/t) ∑_{τ<t} E[g_{S(τ)}(V, γ)] ≤ V · (1/t) ∑_{τ<t} E[f^Π(τ)] + (1/t) ∑_j γ_j E[q_j^Π(t)]`.
   - 2.3. Stability (`limsup (1/t) ∑_{τ<t} ∑_j E[q_j^Π(τ)] < ∞`) forces `liminf_{t→∞} (1/t) ∑_j E[q_j^Π(t)] = 0`. Taking `liminf` along a subsequence yields `g(V, γ) ≤ V f^Π_av`, hence `g(V, γ) ≤ V f^*_av`.

3. **One-slot Lyapunov drift + Poisson telescoping.**
   - 3.1. For `L(t) = (1/2) ∑_j q_j(t)^2`, Eq. (3) and Backpressure optimality (Eq. 6) give `L(t+1) - L(t) + V f^{BP}(t) ≤ B^2 + g_{S(t)}(V, q(t))`.
   - 3.2. Substituting Poisson's equation and taking expectations using the Markov property yields
     `E[L(t+1) + h(q(t+1), S(t+1))] - E[L(t) + h(q(t), S(t))] + V E[f^{BP}(t)] ≤ (1 + C') B^2 + E[g(V, q(t))]`,
     since `|h(q(t+1), S(t+1)) - h(q(t), S(t+1))| ≤ C' B ‖q(t+1) - q(t)‖ ≤ C' B^2`.
   - 3.3. Summing over `t = 0, …, T - 1` and using `L(T) + h(q(T), S(T)) ≥ -(C' B)^2/2 - C' V δ_max` (completing the square) bounds both `V ∑_{t<T} E[f^{BP}(t)]` and `η ∑_{t<T} ∑_j E[q_j(t)]`.

4. **Conclude `[O(1/V), O(V)]`.**
   - 4.1. Using `g(V, q(t)) ≤ V δ_max - η ∑_j q_j(t)` (from `η`-slackness) gives `q̄^{BP} ≤ ((1 + C') B^2 + V δ_max) / η = O(V)` and stability.
   - 4.2. Using `g(V, q(t)) ≤ V f^*_av` (Step 2) gives `f^{BP}_av ≤ f^*_av + (1 + C') B^2 / V = f^*_av + O(1/V)`, while stability implies `f^*_av ≤ f^{BP}_av`. ∎
