import Statements.MarkovTradeoff
import Statements.ExponentialAttraction
import Statements.LifoDelay
import Examples.LittleWitness

/-!
# Non-Degenerate Witnesses for Theorems 2, 3, and 4

Instantiates a concrete single-queue, two-action `NetworkModel` (`twoActionModel`) on the
two-point `(1/2, 1/2)` probability space `(Bool, fairCoinMeasure)` with:
- Feasible compact action set `Action () = Bool`:
  - `false`: `cost = 0`, `arrival = 1`, `service = 0` (`A - μ = +1`)
  - `true`:  `cost = 1`, `arrival = 1`, `service = 2` (`A - μ = -1`)
- Uniform bound `δmax = 2 > 0`.
- `η`-slackness with `η = 1 > 0` (achieved by always selecting `true`).
- Exact dual function `g(V, γ) = min (γ 0) (V - γ 0) = V / 2 - |γ 0 - V / 2|`, giving a
  unique dual optimum `γ*_V = fun _ => V / 2` and exact polyhedral linear growth with `L = 1 > 0`
  uniformly for all `V ≥ 1`.
- At `V = 2` (`γ* = 1`), Backpressure selects `false` at `t = 0` (`q(0) = 0`) and `true` for all
  `t ≥ 1` (`q(t) = 1`), coupled with a unit-packet `LifoQueueRealization` having `λ_j = λ̃_j = 1 > 0`.

This single concrete instance witnesses joint satisfiability of all hypotheses of
`Theorem2Statement`, `Theorem3Statement`, and `Theorem4Statement` (including the guarded
Part (b) clause `0 < λ̃_j`).
-/

namespace LifoBackpressure.Examples

open Filter MeasureTheory Classical
open LifoBackpressure.Statements

/-- Concrete single-queue, two-action `NetworkModel` with `δmax = 2`, `η = 1`,
unique dual optimum `γ*_V = V / 2`, and exact polyhedral growth `L = 1`. -/
abbrev twoActionModel : NetworkModel where
  State := Unit
  r := 1
  hr := Nat.zero_lt_one
  P _ _ := 1
  P_nonneg _ _ := zero_le_one
  P_sum_one _ := by simp
  P_irreducible _ _ := ⟨1, Nat.zero_lt_one, by simp [Statements.matPow]⟩
  P_aperiodic s d hd := Nat.eq_one_of_dvd_one (hd 1 Nat.zero_lt_one (by simp [Statements.matPow]))
  π _ := 1
  π_pos _ := zero_lt_one
  π_sum_one := by simp
  π_stationary _ := by simp
  Action _ := Bool
  cost _ b := if b then 1 else 0
  arrival _ _ _ := 1
  service _ b _ := if b then 2 else 0
  cost_cont _ := continuous_of_discreteTopology
  arrival_cont _ _ := continuous_of_discreteTopology
  service_cont _ _ := continuous_of_discreteTopology
  δmax := 2
  hδmax := by norm_num
  cost_nonneg _ b := by cases b <;> norm_num
  cost_le _ b := by cases b <;> norm_num
  arrival_nonneg _ _ _ := by norm_num
  arrival_le _ _ _ := by norm_num
  service_nonneg _ b _ := by cases b <;> norm_num
  service_le _ b _ := by cases b <;> norm_num

lemma twoActionModel_slackness : twoActionModel.HasSlackness 1 := by
  refine ⟨zero_lt_one, 1, fun _ _ => true, fun _ _ => 1, ?_, ?_, ?_⟩
  · intro _ _; exact zero_le_one
  · intro _; simp
  · intro j
    simp [twoActionModel]
    norm_num

lemma twoActionModel_dualState (V : ℝ) (s : Unit) (γ : Fin 1 → ℝ) :
    twoActionModel.dualState V s γ = min (γ 0) (V - γ 0) := by
  unfold NetworkModel.dualState
  have hval : ∀ x : Bool,
      V * twoActionModel.cost s x +
        ∑ j : Fin 1, γ j * (twoActionModel.arrival s x j - twoActionModel.service s x j) =
      if x then V - γ 0 else γ 0 := by
    intro x
    cases x
    · simp
    · simp; ring
  simp_rw [hval]
  have hbdd : BddBelow (Set.range (fun x : Bool => if x then V - γ 0 else γ 0)) := by
    refine ⟨min (γ 0) (V - γ 0), ?_⟩
    rintro _ ⟨x, rfl⟩
    cases x
    · simp
    · simp
  refine le_antisymm ?_ ?_
  · apply le_min
    · simpa using ciInf_le hbdd false
    · simpa using ciInf_le hbdd true
  · refine le_ciInf (fun x => ?_)
    cases x
    · simp
    · simp

lemma twoActionModel_dual (V : ℝ) (γ : Fin 1 → ℝ) :
    twoActionModel.dual V γ = min (γ 0) (V - γ 0) := by
  unfold NetworkModel.dual
  simp [twoActionModel_dualState]

lemma twoActionModel_uniqueDualOpt (V : ℝ) (hV : 1 ≤ V) :
    twoActionModel.IsUniqueDualOpt V (fun _ => V / 2) := by
  have hmin_eq : min (V / 2) (V - V / 2) = V / 2 := by
    have : V - V / 2 = V / 2 := by ring
    rw [this, min_self]
  have hopt : twoActionModel.IsDualOpt V (fun _ => V / 2) := by
    refine ⟨fun _ => by linarith, fun γ _ => ?_⟩
    rw [twoActionModel_dual, twoActionModel_dual, hmin_eq]
    rcases le_or_gt (γ 0) (V / 2) with h | h
    · exact le_trans (min_le_left _ _) h
    · exact le_trans (min_le_right _ _) (by linarith)
  refine ⟨hopt, fun γ hγ => ?_⟩
  have hge := hγ.2 (fun _ => V / 2) (fun _ => by linarith)
  rw [twoActionModel_dual, twoActionModel_dual, hmin_eq] at hge
  have h1 : V / 2 ≤ γ 0 := le_trans hge (min_le_left _ _)
  have h2 : V / 2 ≤ V - γ 0 := le_trans hge (min_le_right _ _)
  funext j
  fin_cases j
  change γ 0 = V / 2
  linarith

lemma twoActionModel_polyhedral (V : ℝ) :
    twoActionModel.DualPolyhedral V (fun _ => V / 2) 1 := by
  refine ⟨zero_lt_one, fun γ _ => ?_⟩
  have hmin_eq : min (V / 2) (V - V / 2) = V / 2 := by
    have : V - V / 2 = V / 2 := by ring
    rw [this, min_self]
  rw [twoActionModel_dual, twoActionModel_dual, hmin_eq]
  have heuc : NetworkModel.eucDist (fun _ : Fin 1 => V / 2) γ = |V / 2 - γ 0| := by
    unfold NetworkModel.eucDist
    simp [Real.sqrt_sq_eq_abs]
  rw [heuc, one_mul]
  rcases le_or_gt (γ 0) (V / 2) with h | h
  · rw [min_eq_left (by linarith), abs_of_nonneg (by linarith)]
    linarith
  · rw [min_eq_right (by linarith), abs_of_neg (by linarith)]
    linarith

/-- Discrete `⊤` measurable space instance on `Bool` for the `(1/2, 1/2)` witness space. -/
private local instance : MeasurableSpace Bool := ⊤
private local instance : IsProbabilityMeasure fairCoinMeasure := fairCoinMeasure_isProb

/-- Markov process for `twoActionModel` on the two-point `(1/2, 1/2)` space `(Bool, fairCoinMeasure)`. -/
noncomputable def witnessProc : twoActionModel.MarkovProcess Bool fairCoinMeasure where
  S _ _ := ()
  measurable_S _ _ := trivial
  markov t h s' := by
    have h1 : {ω : Bool | (∀ i : Fin (t + 1), () = h i) ∧ () = s'} = Set.univ := by
      ext ω; simp
    have h2 : {ω : Bool | ∀ i : Fin (t + 1), () = h i} = Set.univ := by
      ext ω; simp
    rw [h1, h2]
    simp

/-- Backpressure decision rule for `twoActionModel` at `V = 2`: serve (`true`) iff `q 0 ≥ 1`. -/
noncomputable def witnessChoice (_ : Unit) (q : Fin 1 → ℝ) : Bool :=
  decide (1 ≤ q 0)

lemma witnessChoice_bp : twoActionModel.IsBackpressureRule 2 witnessChoice := by
  intro s q x
  by_cases h : 1 ≤ q 0
  · have hch : witnessChoice s q = true := by simp [witnessChoice, h]
    rw [hch]
    cases x
    · simp; linarith
    · simp
  · have hch : witnessChoice s q = false := by simp [witnessChoice, h]
    rw [hch]
    cases x
    · simp
    · simp; linarith

/-- Concrete Backpressure policy at `V = 2`: `false` at `t = 0`, `true` for all `t ≥ 1`. -/
noncomputable def witnessPolicy : twoActionModel.Policy witnessProc where
  act t _ := decide (1 ≤ t)
  measurable_cost _ := measurable_const
  measurable_arrival _ _ := measurable_const
  measurable_service _ _ := measurable_const

lemma witnessPolicy_queue (t : ℕ) (ω : Bool) :
    witnessPolicy.queue t ω 0 = if t = 0 then 0 else 1 := by
  induction t with
  | zero => rfl
  | succ k ih =>
    change max (witnessPolicy.queue k ω 0 -
        twoActionModel.service () (decide (1 ≤ k)) 0) 0 +
      twoActionModel.arrival () (decide (1 ≤ k)) 0 = 1
    rw [ih]
    cases k with
    | zero =>
      simp only [↓reduceIte, show decide (1 ≤ 0) = false by decide]
      norm_num
    | succ m =>
      have h1 : 1 ≤ m + 1 := Nat.succ_le_succ (Nat.zero_le m)
      simp only [Nat.succ_ne_zero, ↓reduceIte, h1, decide_true]
      norm_num

lemma witnessPolicy_followsBP : witnessPolicy.FollowsBackpressure 2 := by
  refine ⟨witnessChoice, witnessChoice_bp, fun t ω => ?_⟩
  change decide (1 ≤ t) = decide (1 ≤ witnessPolicy.queue t ω 0)
  rw [witnessPolicy_queue t ω]
  cases t with
  | zero => simp
  | succ m => simp

/-- Unit-packet LIFO buffer realization for `witnessPolicy`: packet `k` arrives at slot `k`,
occupies buffer slot `0`, and departs at slot `k + 1`. -/
noncomputable def witnessLifo : LifoQueueRealization witnessPolicy (0 : Fin 1) ℕ where
  arrival _ k := k
  depart _ k := ((k + 1 : ℕ) : WithTop ℕ)
  slot _ _ := 0
  arrival_le_depart _ k := by
    exact_mod_cast Nat.le_succ k
  finite_arrivals _ t := Set.finite_Iio t
  disjoint_slots _ k₁ k₂ hne _ τ hocc := by
    rcases hocc with ⟨⟨ha₁, hd₁⟩, ⟨ha₂, hd₂⟩⟩
    have hd₁' : τ < k₁ + 1 := by exact_mod_cast hd₁
    have hd₂' : τ < k₂ + 1 := by exact_mod_cast hd₂
    have h1 : τ = k₁ := le_antisymm (Nat.lt_succ_iff.mp hd₁') ha₁
    have h2 : τ = k₂ := le_antisymm (Nat.lt_succ_iff.mp hd₂') ha₂
    exact hne (h1.symm.trans h2)
  arrivals_at_eq _ τ := by
    have hset : ((Set.finite_Iio (τ + 1)).subset (t := {k : ℕ | k = τ})
        (fun k (hk : k = τ) => hk ▸ Nat.lt_succ_self τ)).toFinset = {τ} := by
      ext k
      simp
    change (((Set.finite_Iio (τ + 1)).subset (t := {k : ℕ | k = τ})
        (fun k (hk : k = τ) => hk ▸ Nat.lt_succ_self τ)).toFinset.card : ℝ) = 1
    rw [hset]
    simp
  slot_bounds ω k := by
    dsimp only
    rw [witnessPolicy_queue k ω]
    cases k with
    | zero =>
      simp only [↓reduceIte, Nat.cast_zero]
      constructor <;> norm_num
    | succ m =>
      simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.cast_zero]
      constructor <;> norm_num
  never_depart_le_queue ω τ := by
    have hset : ((Set.finite_Iio τ).subset
        (t := {k : ℕ | k < τ ∧ ((k + 1 : ℕ) : WithTop ℕ) = ⊤})
        (fun _ hk => hk.1)).toFinset = ∅ := by
      ext k
      simp
    change (((Set.finite_Iio τ).subset
        (t := {k : ℕ | k < τ ∧ ((k + 1 : ℕ) : WithTop ℕ) = ⊤})
        (fun _ hk => hk.1)).toFinset.card : ℝ) ≤
      witnessPolicy.queue τ ω 0
    rw [hset, Finset.card_empty, Nat.cast_zero, witnessPolicy_queue τ ω]
    split_ifs <;> norm_num
  measurable_never_depart τ := by
    have hconst : (fun _ : Bool =>
        (((Set.finite_Iio τ).subset
          (t := {k : ℕ | k < τ ∧ ((k + 1 : ℕ) : WithTop ℕ) = ⊤})
          (fun _ hk => hk.1)).toFinset.card : ℝ)) =
        fun _ => 0 := by
      funext _
      have hset : ((Set.finite_Iio τ).subset
          (t := {k : ℕ | k < τ ∧ ((k + 1 : ℕ) : WithTop ℕ) = ⊤})
          (fun _ hk => hk.1)).toFinset = ∅ := by
        ext k
        simp
      rw [hset]
      simp
    change Measurable (fun _ : Bool =>
        (((Set.finite_Iio τ).subset
          (t := {k : ℕ | k < τ ∧ ((k + 1 : ℕ) : WithTop ℕ) = ⊤})
          (fun _ hk => hk.1)).toFinset.card : ℝ))
    rw [hconst]
    exact measurable_const

/-! ### Non-degenerate witness theorems matching `HYPOTHESES_QUERY` -/

/-- Non-degenerate witness showing all hypotheses of `Theorem2Statement` are jointly satisfiable. -/
theorem theorem2_witness :
    ∃ (M : NetworkModel) (η V : ℝ) (Ω : Type) (_ : MeasurableSpace Ω)
      (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (proc : M.MarkovProcess Ω μ) (pol : M.Policy proc),
      M.HasSlackness η ∧ 1 ≤ V ∧ pol.FollowsBackpressure V :=
  ⟨twoActionModel, 1, 2, Bool, ⊤, fairCoinMeasure, fairCoinMeasure_isProb,
    witnessProc, witnessPolicy, twoActionModel_slackness, by norm_num, witnessPolicy_followsBP⟩

/-- Non-degenerate witness showing all hypotheses of `Theorem3Statement` are jointly satisfiable. -/
theorem theorem3_witness :
    ∃ (M : NetworkModel) (η L V : ℝ) (γstar : Fin M.r → ℝ) (Ω : Type) (_ : MeasurableSpace Ω)
      (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (proc : M.MarkovProcess Ω μ) (pol : M.Policy proc) (m : ℝ),
      M.HasSlackness η ∧
      0 < L ∧
      1 ≤ V ∧
      M.IsUniqueDualOpt V γstar ∧
      M.DualPolyhedral V γstar L ∧
      pol.FollowsBackpressure V ∧
      0 ≤ m :=
  ⟨twoActionModel, 1, 1, 2, fun _ => 1, Bool, ⊤, fairCoinMeasure, fairCoinMeasure_isProb,
    witnessProc, witnessPolicy, 1,
    twoActionModel_slackness,
    zero_lt_one,
    by norm_num,
    by simpa [show (2 : ℝ) / 2 = 1 by norm_num] using twoActionModel_uniqueDualOpt 2 (by norm_num),
    by simpa [show (2 : ℝ) / 2 = 1 by norm_num] using twoActionModel_polyhedral 2,
    witnessPolicy_followsBP,
    zero_le_one⟩

/-- Non-degenerate witness showing all hypotheses of `Theorem4Statement` (including the guarded
Part (b) clause `0 < lamTilde`) are jointly satisfiable. -/
theorem theorem4_witness :
    ∃ (M : NetworkModel) (η L D K V : ℝ) (γstar : Fin M.r → ℝ) (Ω : Type) (_ : MeasurableSpace Ω)
      (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (proc : M.MarkovProcess Ω μ) (pol : M.Policy proc)
      (j : Fin M.r) (ι : Type) (_Q : LifoQueueRealization pol j ι) (lamJ lamTilde : ℝ),
      M.HasSlackness η ∧
      0 < L ∧
      1 ≤ V ∧
      M.IsUniqueDualOpt V γstar ∧
      M.DualPolyhedral V γstar L ∧
      pol.FollowsBackpressure V ∧
      0 < lamJ ∧
      (∀ᵐ ω ∂μ, Filter.Tendsto
        (fun t : ℕ => ((1 : ℝ) / (t : ℝ)) *
          ∑ τ ∈ Finset.range t, M.arrival (proc.S τ ω) (pol.act τ ω) j)
        Filter.atTop (nhds lamJ)) ∧
      (∀ᵐ ω ∂μ, Filter.Tendsto
        (fun t : ℕ => ((1 : ℝ) / (t : ℝ)) *
          ∑ τ ∈ Finset.range t,
            if pol.queue τ ω j ∈ backlogWindow (γstar j) D K V
            then M.arrival (proc.S τ ω) (pol.act τ ω) j else 0)
        Filter.atTop (nhds lamTilde)) ∧
      0 < lamTilde := by
  have hones : Filter.Tendsto (fun t : ℕ => ((1 : ℝ) / (t : ℝ)) * ∑ _τ ∈ Finset.range t, (1 : ℝ))
      Filter.atTop (nhds (1 : ℝ)) := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Filter.eventually_ge_atTop 1] with t ht
    have ht_pos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one ht)
    simp [ht_pos.ne']
  have hmem : ∀ (τ : ℕ) (ω : Bool),
      witnessPolicy.queue τ ω 0 ∈ backlogWindow (1 : ℝ) 1 1 2 := by
    intro τ ω
    rw [witnessPolicy_queue τ ω]
    unfold backlogWindow qLow qHigh
    have hlog_sq : 0 ≤ (Real.log 2) ^ 2 := sq_nonneg _
    have hlow : max ((1 : ℝ) - 1 - 1 * (Real.log 2) ^ 2) 0 = 0 := max_eq_right (by linarith)
    rw [hlow]
    split_ifs
    · exact ⟨le_rfl, by linarith⟩
    · exact ⟨zero_le_one, by linarith⟩
  refine ⟨twoActionModel, 1, 1, 1, 1, 2, fun _ => 1, Bool, ⊤, fairCoinMeasure, fairCoinMeasure_isProb,
    witnessProc, witnessPolicy, (0 : Fin 1), ℕ, witnessLifo, 1, 1,
    twoActionModel_slackness,
    zero_lt_one,
    by norm_num,
    by simpa [show (2 : ℝ) / 2 = 1 by norm_num] using twoActionModel_uniqueDualOpt 2 (by norm_num),
    by simpa [show (2 : ℝ) / 2 = 1 by norm_num] using twoActionModel_polyhedral 2,
    witnessPolicy_followsBP,
    zero_lt_one,
    Filter.Eventually.of_forall (fun _ => hones),
    Filter.Eventually.of_forall (fun ω => ?_),
    zero_lt_one⟩
  have hfun : (fun t : ℕ => ((1 : ℝ) / (t : ℝ)) *
        ∑ τ ∈ Finset.range t,
          if witnessPolicy.queue τ ω 0 ∈ backlogWindow (1 : ℝ) 1 1 2
          then twoActionModel.arrival (witnessProc.S τ ω) (witnessPolicy.act τ ω) 0 else 0) =
      fun t : ℕ => ((1 : ℝ) / (t : ℝ)) * ∑ _τ ∈ Finset.range t, (1 : ℝ) := by
    funext t
    congr 1
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    rw [if_pos (hmem τ ω)]
  rwa [hfun]

end LifoBackpressure.Examples
