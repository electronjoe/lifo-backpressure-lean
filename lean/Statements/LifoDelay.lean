import Statements.Little
import Statements.MarkovTradeoff
import Statements.ExponentialAttraction

/-!
# Statements for Theorem 4 (`thm:qlalifo_delay`): LIFO-Backpressure Throughput and `O([log V]^2)` Delay

Formalizes the clean, mathematically sound version of Theorem 4 of `arXiv:1008.4895v2`
(Section VI-C, lines 587-666). Differences against the manuscript prose (reversed `[Q_High, Q_Low]`
typo, missing `λ̃_j > 0` guard in Part (b), a.s.-constant time averages for Dominated Convergence,
discrete unit-packet LIFO buffer coupling, and exact `+ 2 δ_max + 1` window width under Eq. (3))
are explicitly recorded in `comparisons.json` and `manuscript-edits.json`.
-/

namespace LifoBackpressure.Statements

open Filter MeasureTheory Classical

/-- Upper window endpoint `Q_{j,High} = γ*_{Vj} + D + K [log(V)]^2` (Section VI-C, L601). -/
noncomputable def qHigh (γstar_j D K V : ℝ) : ℝ :=
  γstar_j + D + K * (Real.log V) ^ 2

/-- Lower window endpoint `Q_{j,Low} = max(γ*_{Vj} - D - K [log(V)]^2, 0)` (Section VI-C, L602). -/
noncomputable def qLow (γstar_j D K V : ℝ) : ℝ :=
  max (γstar_j - D - K * (Real.log V) ^ 2) 0

/-- Corrected backlog window `B_j = [Q_{j,Low}, Q_{j,High}]` (manuscript L605 writes endpoints reversed). -/
def backlogWindow (γstar_j D K V : ℝ) : Set ℝ :=
  Set.Icc (qLow γstar_j D K V) (qHigh γstar_j D K V)

/-- A discrete unit-packet LIFO buffer realization for queue `j` of a Backpressure policy `Π`,
coupling individual packet arrival/departure/buffer-slot trajectories to `Π.queue τ ω j` and
`M.arrival (proc.S τ ω) (Π.act τ ω) j` under the queueing dynamics Eq. (3). -/
structure LifoQueueRealization {M : NetworkModel} {Ω : Type} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {proc : M.MarkovProcess Ω μ}
    (pol : M.Policy proc) (j : Fin M.r) (ι : Type) where
  /-- Discrete arrival slot of packet `k` on sample path `ω`. -/
  arrival : Ω → ι → ℕ
  /-- Departure slot of packet `k` on sample path `ω`, or `⊤` if it never departs. -/
  depart : Ω → ι → WithTop ℕ
  /-- Fixed nonnegative integer LIFO buffer slot occupied by packet `k` on sample path `ω`. -/
  slot : Ω → ι → ℕ
  /-- No packet departs before it arrives. -/
  arrival_le_depart : ∀ ω k, (arrival ω k : WithTop ℕ) ≤ depart ω k
  /-- Only finitely many packets arrive before any finite horizon `t`. -/
  finite_arrivals : ∀ ω (t : ℕ), Set.Finite {k : ι | arrival ω k < t}
  /-- Each LIFO buffer slot holds at most one packet at any time slot `τ`. -/
  disjoint_slots :
    ∀ ω k₁ k₂, k₁ ≠ k₂ → slot ω k₁ = slot ω k₂ →
      ∀ τ : ℕ, ¬ ((arrival ω k₁ ≤ τ ∧ (τ : WithTop ℕ) < depart ω k₁) ∧
                   (arrival ω k₂ ≤ τ ∧ (τ : WithTop ℕ) < depart ω k₂))
  /-- Packet arrivals in slot `τ` match `A_j(τ, ω)`. -/
  arrivals_at_eq :
    ∀ ω (τ : ℕ),
      (((finite_arrivals ω (τ + 1)).subset (fun k (hk : arrival ω k = τ) => hk ▸ Nat.lt_succ_self τ)).toFinset.card : ℝ) =
        M.arrival (proc.S τ ω) (pol.act τ ω) j
  /-- Under Eq. (3), packets arriving at slot `τ` are placed on top of the post-service queue
  `max(q_j(τ) - μ_j(τ), 0)` and strictly below `q_j(τ) + δ_max`. -/
  slot_bounds :
    ∀ ω k,
      let τ := arrival ω k
      max (pol.queue τ ω j - M.δmax) 0 ≤ (slot ω k : ℝ) ∧
      (slot ω k : ℝ) < pol.queue τ ω j + M.δmax
  /-- Packets that arrived before time `τ` and never depart remain counted in the backlog `q_j(τ)`. -/
  never_depart_le_queue :
    ∀ ω (τ : ℕ),
      (((finite_arrivals ω τ).subset (fun k (hk : arrival ω k < τ ∧ depart ω k = ⊤) => hk.1)).toFinset.card : ℝ) ≤
        pol.queue τ ω j
  /-- Measurability of the count of never-departing packets arriving before time `τ`. -/
  measurable_never_depart :
    ∀ (τ : ℕ),
      Measurable (fun ω =>
        (((finite_arrivals ω τ).subset (fun k (hk : arrival ω k < τ ∧ depart ω k = ⊤) => hk.1)).toFinset.card : ℝ))

namespace LifoQueueRealization

variable {M : NetworkModel} {Ω : Type} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {proc : M.MarkovProcess Ω μ}
    {pol : M.Policy proc} {j : Fin M.r} {ι : Type}

/-- Set of packets on sample path `ω` that arrive while `q_j(t) ∈ B_j` and eventually depart. -/
def windowDepartingSet (L : LifoQueueRealization pol j ι) (γstar_j D K V : ℝ) (ω : Ω) : Set ι :=
  {k | pol.queue (L.arrival ω k) ω j ∈ backlogWindow γstar_j D K V ∧ L.depart ω k ≠ ⊤}

/-- Number of packets in `windowDepartingSet` that arrive before time `t`. -/
noncomputable def windowDepartingArrivals (L : LifoQueueRealization pol j ι)
    (γstar_j D K V : ℝ) (ω : Ω) (t : ℕ) : ℕ :=
  ((L.finite_arrivals ω t).subset
    (fun k (hk : L.arrival ω k < t ∧ k ∈ L.windowDepartingSet γstar_j D K V ω) => hk.1)).toFinset.card

/-- Set of integer buffer slots reachable by packets arriving while `q_j(t) ∈ B_j` under Eq. (3). -/
noncomputable def enlargedBufferSlots (γstar_j D K V δmax : ℝ) : Finset ℕ :=
  Finset.Ico (Nat.floor (max (qLow γstar_j D K V - δmax) 0))
    (Nat.ceil (qHigh γstar_j D K V + δmax))

/-- The `BufferSystem` obtained by restricting `L` to `windowDepartingSet`, whose slots all lie in
`enlargedBufferSlots`. -/
noncomputable def windowBufferSystem (L : LifoQueueRealization pol j ι)
    (γstar_j D K V : ℝ) (ω : Ω) :
    BufferSystem {b : ℕ // b ∈ enlargedBufferSlots γstar_j D K V M.δmax}
      {k : ι // k ∈ L.windowDepartingSet γstar_j D K V ω} where
  arrival k := L.arrival ω k.1
  depart k := L.depart ω k.1
  slot k := ⟨L.slot ω k.1, by
    rcases k.2 with ⟨hwin, _⟩
    have hsb := L.slot_bounds ω k.1
    rw [enlargedBufferSlots, Finset.mem_Ico]
    constructor
    · apply Nat.floor_le_of_le
      calc max (qLow γstar_j D K V - M.δmax) 0
          ≤ max (pol.queue (L.arrival ω k.1) ω j - M.δmax) 0 :=
            max_le_max_right 0 (sub_le_sub_right hwin.1 M.δmax)
        _ ≤ (L.slot ω k.1 : ℝ) := hsb.1
    · rw [Nat.lt_ceil]
      linarith [hsb.2, hwin.2]⟩
  arrival_le_depart k := L.arrival_le_depart ω k.1
  finite_arrivals t :=
    (L.finite_arrivals ω t).preimage (fun _ _ _ _ h => Subtype.ext h)
  disjoint_slots k₁ k₂ hne hsl τ :=
    L.disjoint_slots ω k₁.1 k₂.1 (fun h => hne (Subtype.ext h)) (congrArg Subtype.val hsl) τ

end LifoQueueRealization

/-- Paper Theorem 4 (`thm:qlalifo_delay`, clean mathematically sound formulation):
Under `V ≥ 1`, unique dual optimum `γ*_V`, `η`-slackness, and `V`-independent polyhedral dual
growth with constant `L > 0`, there exist `V`-independent constants `D, K, c* > 0` (from Theorem 3)
such that for any queue `j` with a.s.-constant time-average arrival rate `λ_j > 0` and
a.s.-constant in-window arrival rate `λ̃_j`:
  (a) `λ̃_j` equals the a.s. arrival rate of packets arriving when `q_j(t) ∈ B_j` that eventually
      depart, and satisfies `λ_j ≥ λ̃_j ≥ max(λ_j - δ_max c* / V^{log V}, 0)`.
  (b) Whenever `λ̃_j > 0`, with probability 1 the `limsup` average delay of these packets is at
      most `(2D + 2K [log V]^2 + 2 δ_max + 1) / λ̃_j`. -/
def Theorem4Statement : Prop :=
  ∀ (M : NetworkModel) (η L : ℝ),
    M.HasSlackness η →
    0 < L →
    ∃ (D K cstar : ℝ), 0 < D ∧ 0 < K ∧ 0 < cstar ∧
      ∀ (V : ℝ), 1 ≤ V →
        ∀ (γstar : Fin M.r → ℝ),
          M.IsUniqueDualOpt V γstar →
          M.DualPolyhedral V γstar L →
          ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
            (proc : M.MarkovProcess Ω μ) (pol : M.Policy proc),
            pol.FollowsBackpressure V →
            ∀ (j : Fin M.r) (ι : Type) (Q : LifoQueueRealization pol j ι)
              (lamJ lamTilde : ℝ),
              0 < lamJ →
              (∀ᵐ ω ∂μ, Filter.Tendsto
                (fun t : ℕ => ((1 : ℝ) / (t : ℝ)) *
                  ∑ τ ∈ Finset.range t, M.arrival (proc.S τ ω) (pol.act τ ω) j)
                Filter.atTop (nhds lamJ)) →
              (∀ᵐ ω ∂μ, Filter.Tendsto
                (fun t : ℕ => ((1 : ℝ) / (t : ℝ)) *
                  ∑ τ ∈ Finset.range t,
                    if pol.queue τ ω j ∈ backlogWindow (γstar j) D K V
                    then M.arrival (proc.S τ ω) (pol.act τ ω) j else 0)
                Filter.atTop (nhds lamTilde)) →
              -- Part (a): rate of in-window eventually-departing packets
              (∀ᵐ ω ∂μ, Filter.Tendsto
                (fun t : ℕ =>
                  ((Q.windowDepartingArrivals (γstar j) D K V ω t : ℝ) / (t : ℝ)))
                Filter.atTop (nhds lamTilde)) ∧
              max (lamJ - M.δmax * cstar / (V ^ Real.log V)) 0 ≤ lamTilde ∧
              lamTilde ≤ lamJ ∧
              -- Part (b): O([log V]^2) average delay bound whenever lamTilde > 0
              (0 < lamTilde →
                ∀ᵐ ω ∂μ,
                  Filter.limsup
                    (fun t : ℕ =>
                      ((Q.windowBufferSystem (γstar j) D K V ω).avgDelay t : EReal))
                    Filter.atTop ≤
                    (((2 * D + 2 * K * (Real.log V) ^ 2 + 2 * M.δmax + 1) / lamTilde : ℝ) : EReal))

end LifoBackpressure.Statements
