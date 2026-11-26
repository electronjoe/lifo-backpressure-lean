import Statements.Little

/-!
# Non-Degenerate Witness for Theorem 1 (`theorem:little1`)

Instantiates the Section VI-A two-slot LIFO example (`arXiv:1008.4895v2`, lines 494–512)
on a two-point `(1/2, 1/2)` probability space `Ω = Bool`:
- Packet `0` arrives at `t = 0` into buffer slot `0 : Fin 2` and never departs (`depart = ⊤`).
- Packet `k + 1` arrives at `t = k` into buffer slot `1 : Fin 2` and departs at `t = k + 1`.
Here `N(t) = t + 1` for `t ≥ 1`, `D(t) = t`, `λ_min = 1 > 0`, and `|B| = 2`.
-/

namespace LifoBackpressure.Examples

open Filter MeasureTheory
open LifoBackpressure.Statements

/-- Section VI-A deterministic two-slot LIFO buffer system with one permanently trapped packet
in slot `0` and unit-delay packets `k + 1` in slot `1`. -/
def sectionVIA_system : BufferSystem (Fin 2) ℕ where
  arrival
    | 0 => 0
    | k + 1 => k
  depart
    | 0 => ⊤
    | k + 1 => ((k + 1 : ℕ) : WithTop ℕ)
  slot
    | 0 => ⟨0, by decide⟩
    | _ + 1 => ⟨1, by decide⟩
  arrival_le_depart
    | 0 => le_top
    | k + 1 => by
      change (k : WithTop ℕ) ≤ ((k + 1 : ℕ) : WithTop ℕ)
      exact_mod_cast Nat.le_succ k
  finite_arrivals t := by
    apply (Set.finite_Iio (t + 1)).subset
    intro k hk
    cases k with
    | zero => exact Nat.zero_lt_succ t
    | succ n =>
      change n < t at hk
      exact Nat.succ_lt_succ hk
  disjoint_slots k₁ k₂ hne hsl τ hocc := by
    cases k₁ with
    | zero =>
      cases k₂ with
      | zero => exact hne rfl
      | succ n₂ =>
        change (⟨0, by decide⟩ : Fin 2) = ⟨1, by decide⟩ at hsl
        exact absurd (congrArg Fin.val hsl) (by decide)
    | succ n₁ =>
      cases k₂ with
      | zero =>
        change (⟨1, by decide⟩ : Fin 2) = ⟨0, by decide⟩ at hsl
        exact absurd (congrArg Fin.val hsl) (by decide)
      | succ n₂ =>
        rcases hocc with ⟨⟨ha₁, hd₁⟩, ⟨ha₂, hd₂⟩⟩
        change n₁ ≤ τ at ha₁
        change n₂ ≤ τ at ha₂
        change (τ : WithTop ℕ) < ((n₁ + 1 : ℕ) : WithTop ℕ) at hd₁
        change (τ : WithTop ℕ) < ((n₂ + 1 : ℕ) : WithTop ℕ) at hd₂
        have hd₁' : τ < n₁ + 1 := by exact_mod_cast hd₁
        have hd₂' : τ < n₂ + 1 := by exact_mod_cast hd₂
        have h1 : τ = n₁ := le_antisymm (Nat.lt_succ_iff.mp hd₁') ha₁
        have h2 : τ = n₂ := le_antisymm (Nat.lt_succ_iff.mp hd₂') ha₂
        exact hne (congrArg Nat.succ (h1.symm.trans h2))

private lemma sectionVIA_arrivalsCount (t : ℕ) (ht : 0 < t) :
    sectionVIA_system.arrivalsCount t = t + 1 := by
  unfold BufferSystem.arrivalsCount
  have hset : (sectionVIA_system.finite_arrivals t).toFinset = Finset.range (t + 1) := by
    ext k
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Finset.mem_range]
    cases k with
    | zero =>
      constructor
      · intro _; exact Nat.zero_lt_succ t
      · intro _; exact ht
    | succ n =>
      change n < t ↔ n + 1 < t + 1
      exact Nat.succ_lt_succ_iff.symm
  rw [hset, Finset.card_range]

private lemma sectionVIA_departuresCount (t : ℕ) :
    sectionVIA_system.departuresCount t = t := by
  unfold BufferSystem.departuresCount
  have hset : (sectionVIA_system.finite_departures t).toFinset =
      (Finset.range t).map ⟨Nat.succ, Nat.succ_injective⟩ := by
    ext k
    simp only [Set.Finite.mem_toFinset, BufferSystem.departuresSet, Set.mem_ofPred_eq,
      Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
    cases k with
    | zero =>
      simp [sectionVIA_system]
    | succ n =>
      change ((n + 1 : ℕ) : WithTop ℕ) ≤ (t : WithTop ℕ) ↔ ∃ a < t, a + 1 = n + 1
      constructor
      · intro h
        have h' : n + 1 ≤ t := by exact_mod_cast h
        exact ⟨n, h', rfl⟩
      · rintro ⟨a, ha, hEq⟩
        have ha' : n = a := (Nat.succ.inj hEq).symm
        subst ha'
        exact_mod_cast Nat.succ_le_of_lt ha
  rw [hset, Finset.card_map, Finset.card_range]

/-- Uniform `(1/2, 1/2)` probability measure on `Bool` (with discrete σ-algebra `⊤`). -/
noncomputable def fairCoinMeasure : @Measure Bool ⊤ :=
  letI : MeasurableSpace Bool := ⊤
  (1 / 2 : ENNReal) • Measure.dirac true + (1 / 2 : ENNReal) • Measure.dirac false

lemma fairCoinMeasure_isProb : @IsProbabilityMeasure Bool ⊤ fairCoinMeasure := by
  let _ : MeasurableSpace Bool := ⊤
  refine ⟨?_⟩
  change ((1 / 2 : ENNReal) • Measure.dirac true + (1 / 2 : ENNReal) • Measure.dirac false) Set.univ = 1
  simp [ENNReal.inv_two_add_inv_two]

/-- Non-degenerate witness showing that all hypotheses of `Theorem1Statement` are jointly
satisfiable (Section VI-A example on a `(1/2, 1/2)` probability space). -/
theorem theorem1_witness :
    ∃ (B : Type) (_ : Fintype B) (ι : Type) (Ω : Type) (_ : MeasurableSpace Ω)
      (μ : Measure Ω) (sys : Ω → BufferSystem B ι) (lamMin : ℝ),
      IsProbabilityMeasure μ ∧
      0 < lamMin ∧
      (∀ᵐ ω ∂μ, (lamMin : EReal) ≤
        Filter.liminf (fun t : ℕ => (((sys ω).arrivalsCount t : ℝ) / (t : ℝ) : EReal)) Filter.atTop) ∧
      (∀ᵐ ω ∂μ, Filter.Tendsto (fun t : ℕ => (sys ω).departuresCount t) Filter.atTop Filter.atTop) := by
  refine ⟨Fin 2, inferInstance, ℕ, Bool, ⊤, fairCoinMeasure, fun _ => sectionVIA_system, 1,
    fairCoinMeasure_isProb, zero_lt_one, ?_, ?_⟩
  · refine Filter.Eventually.of_forall (fun _ => ?_)
    refine Filter.le_liminf_of_le (by isBoundedDefault) ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with t ht
    have ht_pos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one ht)
    have harr : sectionVIA_system.arrivalsCount t = t + 1 :=
      sectionVIA_arrivalsCount t (lt_of_lt_of_le Nat.zero_lt_one ht)
    rw [harr]
    apply EReal.coe_le_coe_iff.mpr
    rw [← div_eq_mul_inv, le_div_iff₀ ht_pos]
    push_cast
    linarith
  · refine Filter.Eventually.of_forall (fun _ => ?_)
    have hfun : (fun t : ℕ => sectionVIA_system.departuresCount t) = id := by
      funext t
      exact sectionVIA_departuresCount t
    rw [hfun]
    exact tendsto_id

end LifoBackpressure.Examples
