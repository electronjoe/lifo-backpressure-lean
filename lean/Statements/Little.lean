import Prelude

/-!
# Statements for Theorem 1 (`theorem:little1`): Modified Little's Theorem for LIFO Systems

Formalizes the sample-path and almost-sure discrete-time LIFO buffer-slot model and
Theorem 1 of Huang, Moeller, Neely, and Krishnamachari (`arXiv:1008.4895v2`, Section VI-B,
lines 517-531; proof in Appendix A, lines 1019-1080).
-/

namespace LifoBackpressure.Statements

open Filter MeasureTheory

/-- A discrete-time sample path of jobs entering a finite set `B` of single-occupancy
buffer locations where each job stays in its assigned buffer slot from arrival until
departure (as under the LIFO discipline). -/
structure BufferSystem (B : Type*) [Fintype B] (ι : Type*) where
  /-- Discrete arrival time slot of job `k`. -/
  arrival : ι → ℕ
  /-- Departure time slot of job `k`, or `⊤` if the job never departs. -/
  depart : ι → WithTop ℕ
  /-- Fixed buffer location in `B` occupied by job `k`. -/
  slot : ι → B
  /-- No job departs before it arrives. -/
  arrival_le_depart : ∀ k, (arrival k : WithTop ℕ) ≤ depart k
  /-- Only finitely many jobs arrive before any finite horizon `t`. -/
  finite_arrivals : ∀ t : ℕ, Set.Finite {k : ι | arrival k < t}
  /-- Each buffer location holds at most one job at any time slot `τ`. -/
  disjoint_slots :
    ∀ k₁ k₂, k₁ ≠ k₂ → slot k₁ = slot k₂ →
      ∀ τ : ℕ, ¬ ((arrival k₁ ≤ τ ∧ (τ : WithTop ℕ) < depart k₁) ∧
                   (arrival k₂ ≤ τ ∧ (τ : WithTop ℕ) < depart k₂))

namespace BufferSystem

variable {B : Type*} [Fintype B] {ι : Type*}

/-- Jobs that arrive strictly before time `t`. -/
def arrivalsSet (sys : BufferSystem B ι) (t : ℕ) : Set ι :=
  {k | sys.arrival k < t}

/-- Jobs that depart up to (and including) time `t`. -/
def departuresSet (sys : BufferSystem B ι) (t : ℕ) : Set ι :=
  {k | sys.depart k ≤ (t : WithTop ℕ)}

/-- Only finitely many jobs depart by time `t`, since every departing job arrived by time `t`. -/
lemma finite_departures (sys : BufferSystem B ι) (t : ℕ) :
    Set.Finite (sys.departuresSet t) := by
  apply (sys.finite_arrivals (t + 1)).subset
  intro k hk
  have hle : (sys.arrival k : WithTop ℕ) ≤ (t : WithTop ℕ) :=
    le_trans (sys.arrival_le_depart k) hk
  have hleNat : sys.arrival k ≤ t := by exact_mod_cast hle
  exact Nat.lt_succ_of_le hleNat

/-- Number `N(t)` of arrivals into `B` up to time `t`. -/
noncomputable def arrivalsCount (sys : BufferSystem B ι) (t : ℕ) : ℕ :=
  (sys.finite_arrivals t).toFinset.card

/-- Number `D(t)` of departures from `B` up to time `t`. -/
noncomputable def departuresCount (sys : BufferSystem B ι) (t : ℕ) : ℕ :=
  (sys.finite_departures t).toFinset.card

/-- Delay `W_k` of job `k` (equals `d - arrival k` when `depart k = d`, and `0` if `depart k = ⊤`). -/
def jobDelay (sys : BufferSystem B ι) (k : ι) : ℕ :=
  match sys.depart k with
  | some d => d - sys.arrival k
  | none => 0

/-- Total delay `∑_{i=1}^{D(t)} W_i` of all jobs that depart from `B` by time `t`. -/
noncomputable def totalDelay (sys : BufferSystem B ι) (t : ℕ) : ℕ :=
  ∑ k ∈ (sys.finite_departures t).toFinset, sys.jobDelay k

/-- Empirical average delay `(1 / D(t)) ∑_{i=1}^{D(t)} W_i` of jobs departing by time `t`. -/
noncomputable def avgDelay (sys : BufferSystem B ι) (t : ℕ) : ℝ :=
  (sys.totalDelay t : ℝ) / (sys.departuresCount t : ℝ)

/-- Restrict a buffer system to any subset `S` of jobs (e.g., packets arriving while queue
backlog lies in a target window `B_j`). -/
def restrict (sys : BufferSystem B ι) (S : Set ι) : BufferSystem B {k : ι // k ∈ S} where
  arrival k := sys.arrival k.1
  depart k := sys.depart k.1
  slot k := sys.slot k.1
  arrival_le_depart k := sys.arrival_le_depart k.1
  finite_arrivals t :=
    (sys.finite_arrivals t).preimage (fun _ _ _ _ h => Subtype.ext h)
  disjoint_slots k₁ k₂ hne hsl τ :=
    sys.disjoint_slots k₁.1 k₂.1 (fun h => hne (Subtype.ext h)) hsl τ

end BufferSystem

/-- Paper Theorem 1 (`theorem:little1`): Modified Little's Theorem for LIFO systems.
If with probability 1 the `liminf` arrival rate into a finite buffer set `B` is at least
`λ_min > 0` and infinitely many jobs depart (`D(t) → ∞`), then with probability 1 the
`limsup` average delay of departing jobs is at most `|B| / λ_min`. -/
def Theorem1Statement : Prop :=
  ∀ (B : Type) [Fintype B] (ι : Type) (Ω : Type) [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (sys : Ω → BufferSystem B ι) (lamMin : ℝ),
    0 < lamMin →
    (∀ᵐ ω ∂μ, (lamMin : EReal) ≤
      Filter.liminf (fun t : ℕ => (((sys ω).arrivalsCount t : ℝ) / (t : ℝ) : EReal)) Filter.atTop) →
    (∀ᵐ ω ∂μ, Filter.Tendsto (fun t : ℕ => (sys ω).departuresCount t) Filter.atTop Filter.atTop) →
    (∀ᵐ ω ∂μ,
      Filter.limsup (fun t : ℕ => ((sys ω).avgDelay t : EReal)) Filter.atTop ≤
        (((Fintype.card B : ℝ) / lamMin : ℝ) : EReal))

end LifoBackpressure.Statements
