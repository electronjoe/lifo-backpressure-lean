# Lamport Proof — Theorem 1 (Modified Little's Theorem for LIFO Systems)

*Provenance: Follows Appendix A of `arXiv:1008.4895v2` (lines 1019–1080), adapted to discrete slotted time `t ∈ ℕ`.*

**Theorem 1.** Let `B` be a finite set of single-occupancy LIFO buffer locations. Suppose with probability 1 that `liminf_{t→∞} N(t)/t ≥ λ_min > 0` and `lim_{t→∞} D(t) = ∞`. Then with probability 1,
`limsup_{t→∞} (1 / D(t)) ∑_{i=1}^{D(t)} W_i ≤ |B| / λ_min`.

1. **Restrict to an almost-sure sample path.**
   Fix a sample path `ω` on which `liminf_{t→∞} N(t)/t ≥ λ_min` and `D(t) → ∞`. (This event has probability 1 by assumption.)

2. **Total delay bound (`∑_{i=1}^{D(t)} W_i ≤ |B| t`).**
   - 2.1. For each buffer location `b ∈ B`, any two distinct jobs assigned to `b` occupy disjoint time intervals `[a_k, d_k)`.
   - 2.2. Every job departing by time `t` (`d_k ≤ t`) has `[a_k, d_k) ⊆ {0, …, t - 1}`, so summing interval lengths over jobs departing from `b` up to time `t` yields `∑_{k : slot(k)=b, d_k ≤ t} W_k ≤ t`. (Discrete analogue of Eq. (23) and Fig. 14.)
   - 2.3. Summing over all `b ∈ B` gives `∑_{k : d_k ≤ t} W_k ≤ |B| · t` for every `t ∈ ℕ`. (Note: in discrete time this holds for all `b ∈ B` directly, avoiding the paper's split into `B̃` and the finite remainder `J`.)

3. **Departure lower bound (`D(t) ≥ N(t) - |B|`).**
   - 3.1. Any job arriving before time `t` (`a_k < t`) that has not yet departed by time `t` (`d_k > t`) occupies its buffer slot `slot(k) ∈ B` at time `t`.
   - 3.2. By single occupancy, at most one undeparted job can occupy each `b ∈ B` at time `t`, so at most `|B|` arriving jobs have `d_k > t`.
   - 3.3. Therefore `N(t) ≤ D(t) + |B|`, i.e., `D(t) ≥ N(t) - |B|`.

4. **Asymptotic `limsup` bound.**
   - 4.1. For any `ε ∈ (0, λ_min)`, since `liminf N(t)/t ≥ λ_min` and `|B|/t → 0`, eventually `N(t)/t - |B|/t ≥ λ_min - ε > 0`, hence `D(t) ≥ (λ_min - ε) t > 0`.
   - 4.2. Combining Steps 2.3 and 3.3 gives `(1 / D(t)) ∑_{k : d_k ≤ t} W_k ≤ |B| t / D(t) ≤ |B| / (λ_min - ε)` eventually.
   - 4.3. Letting `ε → 0⁺` yields `limsup_{t→∞} (1 / D(t)) ∑_{i=1}^{D(t)} W_i ≤ |B| / λ_min`. ∎
