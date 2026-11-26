import Statements.MarkovTradeoff
import Routine.MarkovMixing
import Routine.BackpressureDrift

/-!
# Proof of Theorem 2 (`theorem:qla-markovian`): `[O(1/V), O(V)]` Utility-Delay Tradeoff

Proves `LifoBackpressure.Statements.Theorem2Statement` via finite-state Markov chain geometric
mixing (`Routine.MarkovMixing`), Poisson's equation telescoping, and elementary weak duality
(`basis: "lean"`, matching `lamport/theorem-qla-markovian.md`).
-/

namespace LifoBackpressure.Proofs

open Filter MeasureTheory Classical
open LifoBackpressure.Statements
open LifoBackpressure.Routine

/-! ### Bridge between `Statements.matPow` and `Routine.matPow` -/

lemma statements_matPow_eq_routine {S : Type*} [Fintype S] [DecidableEq S]
    (P : S → S → ℝ) :
    ∀ n s s', Statements.matPow P n s s' = Routine.matPow P n s s'
  | 0, _, _ => rfl
  | n + 1, s, s' => by
    simp only [Statements.matPow, Routine.matPow, statements_matPow_eq_routine P n]

/-! ### Finite-cylinder Markov expectations and tower property -/

/-- Cylinder event `{ω | ∀ i : Fin (t + 1), proc.S i ω = h i}`. -/
def markovCyl {M : NetworkModel} {Ω : Type} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (proc : M.MarkovProcess Ω μ) (t : ℕ) (h : Fin (t + 1) → M.State) : Set Ω :=
  {ω | ∀ i : Fin (t + 1), proc.S i ω = h i}

lemma measurableSet_markovCyl {M : NetworkModel} {Ω : Type} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (proc : M.MarkovProcess Ω μ) (t : ℕ) (h : Fin (t + 1) → M.State) :
    MeasurableSet (markovCyl proc t h) := by
  have heq : markovCyl proc t h = ⋂ i : Fin (t + 1), {ω | proc.S i ω = h i} := by
    ext ω; simp [markovCyl]
  rw [heq]
  exact MeasurableSet.iInter (fun i => proc.measurable_S i (h i))

/-- Integral of any function of the finite Markov history `(S(0), ..., S(t))` is a finite sum
over cylinder events. -/
lemma integral_history_eq_sum {M : NetworkModel} {Ω : Type} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (proc : M.MarkovProcess Ω μ) (t : ℕ) (F : (Fin (t + 1) → M.State) → ℝ) :
    Integrable (fun ω => F (fun i => proc.S i ω)) μ ∧
    ∫ ω, F (fun i => proc.S i ω) ∂μ =
      ∑ h : Fin (t + 1) → M.State, (μ (markovCyl proc t h)).toReal * F h := by
  have hdecomp : (fun ω => F (fun i => proc.S i ω)) =
      fun ω => ∑ h : Fin (t + 1) → M.State, (markovCyl proc t h).indicator (fun _ => F h) ω := by
    funext ω
    symm
    rw [Fintype.sum_eq_single (fun i : Fin (t + 1) => proc.S i ω)]
    · rw [Set.indicator_of_mem]; intro i; rfl
    · intro h hne
      rw [Set.indicator_of_notMem]
      intro hmem
      exact hne (funext (fun i => (hmem i).symm))
  have hint_term : ∀ h ∈ (Finset.univ : Finset (Fin (t + 1) → M.State)),
      Integrable ((markovCyl proc t h).indicator (fun _ => F h)) μ := fun h _ =>
    (integrable_const (F h)).indicator (measurableSet_markovCyl proc t h)
  rw [hdecomp]
  constructor
  · exact integrable_finsetSum _ hint_term
  · rw [integral_finsetSum _ hint_term]
    refine Finset.sum_congr rfl (fun h _ => ?_)
    rw [integral_indicator_const (F h) (measurableSet_markovCyl proc t h), smul_eq_mul, measureReal_def]

/-- One-step Markov tower property for any function of `(S(0), ..., S(t))` and `S(t + 1)`. -/
lemma integral_history_next_eq {M : NetworkModel} {Ω : Type} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (proc : M.MarkovProcess Ω μ) (t : ℕ)
    (G : (Fin (t + 1) → M.State) → M.State → ℝ) :
    ∫ ω, G (fun i => proc.S i ω) (proc.S (t + 1) ω) ∂μ =
      ∫ ω, (∑ s' : M.State, M.P (proc.S t ω) s' * G (fun i => proc.S i ω) s') ∂μ := by
  -- Express LHS via cylinders of length `t + 2`
  let F2 : (Fin (t + 2) → M.State) → ℝ := fun h2 =>
    G (fun i => h2 i.castSucc) (h2 (Fin.last (t + 1)))
  have hLHS : ∫ ω, G (fun i => proc.S i ω) (proc.S (t + 1) ω) ∂μ =
      ∑ h2 : Fin (t + 2) → M.State, (μ (markovCyl proc (t + 1) h2)).toReal * F2 h2 :=
    (integral_history_eq_sum proc (t + 1) F2).2
  have hRHS : ∫ ω, (∑ s' : M.State, M.P (proc.S t ω) s' * G (fun i => proc.S i ω) s') ∂μ =
      ∑ h : Fin (t + 1) → M.State, (μ (markovCyl proc t h)).toReal *
        (∑ s' : M.State, M.P (h (Fin.last t)) s' * G h s') :=
    (integral_history_eq_sum proc t
      (fun h => ∑ s' : M.State, M.P (h (Fin.last t)) s' * G h s')).2
  rw [hLHS, hRHS]
  -- Bijection `(Fin (t + 2) → State) ≃ (Fin (t + 1) → State) × State`
  let e : ((Fin (t + 1) → M.State) × M.State) ≃ (Fin (t + 2) → M.State) :=
    { toFun := fun p => Fin.snoc p.1 p.2
      invFun := fun h2 => (fun i => h2 i.castSucc, h2 (Fin.last (t + 1)))
      left_inv := fun ⟨h, s'⟩ => by
        ext i
        · simp [Fin.snoc_castSucc]
        · simp [Fin.snoc_last]
      right_inv := fun h2 => by
        ext i
        refine Fin.lastCases ?_ ?_ i
        · simp [Fin.snoc_last]
        · intro j; simp [Fin.snoc_castSucc] }
  rw [← Equiv.sum_comp e, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun s' _ => ?_)
  have hcyl : markovCyl proc (t + 1) (e (h, s')) =
      {ω | (∀ i : Fin (t + 1), proc.S i ω = h i) ∧ proc.S (t + 1) ω = s'} := by
    ext ω
    simp only [markovCyl, e, Equiv.coe_fn_mk, Set.mem_ofPred_eq]
    constructor
    · intro hAll
      refine ⟨fun i => ?_, ?_⟩
      · simpa [Fin.snoc_castSucc] using hAll i.castSucc
      · simpa [Fin.snoc_last] using hAll (Fin.last (t + 1))
    · rintro ⟨hPrev, hLast⟩ i
      refine Fin.lastCases ?_ ?_ i
      · simpa [Fin.snoc_last] using hLast
      · intro j; simpa [Fin.snoc_castSucc] using hPrev j
  have hmeas : μ (markovCyl proc (t + 1) (e (h, s'))) =
      μ (markovCyl proc t h) * ENNReal.ofReal (M.P (h (Fin.last t)) s') := by
    rw [hcyl]
    exact proc.markov t h s'
  have hF2 : F2 (e (h, s')) = G h s' := by
    simp [F2, e, Fin.snoc_castSucc, Fin.snoc_last]
  rw [hmeas, hF2, ENNReal.toReal_mul, ENNReal.toReal_ofReal (M.P_nonneg _ _)]
  ring

/-- Marginal state distribution evolution: `P(S(τ) = s') = ∑_{s₀} P(S(0) = s₀) * P^τ(s₀, s')`. -/
lemma marginal_prob_eq {M : NetworkModel} {Ω : Type} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (proc : M.MarkovProcess Ω μ) :
    ∀ (τ : ℕ) (s' : M.State),
      (μ {ω | proc.S τ ω = s'}).toReal =
        ∑ s₀ : M.State, (μ {ω | proc.S 0 ω = s₀}).toReal * Routine.matPow M.P τ s₀ s'
  | 0, s' => by
    simp [Routine.matPow]
  | τ + 1, s' => by
    -- Express `P(S(τ + 1) = s')` as the integral of `1_{S(τ + 1) = s'}` and apply Markov tower property
    have h1 : (μ {ω | proc.S (τ + 1) ω = s'}).toReal =
        ∫ ω, (if proc.S (τ + 1) ω = s' then (1 : ℝ) else 0) ∂μ := by
      have hind : (fun ω => if proc.S (τ + 1) ω = s' then (1 : ℝ) else 0) =
          {ω | proc.S (τ + 1) ω = s'}.indicator (fun _ => (1 : ℝ)) := by
        funext ω; simp [Set.indicator]
      rw [hind, integral_indicator_const 1 (proc.measurable_S (τ + 1) s'), smul_eq_mul, mul_one,
        measureReal_def]
    have h2 : ∫ ω, (if proc.S (τ + 1) ω = s' then (1 : ℝ) else 0) ∂μ =
        ∫ ω, M.P (proc.S τ ω) s' ∂μ := by
      have htw := integral_history_next_eq proc τ (fun _ u => if u = s' then (1 : ℝ) else 0)
      simpa using htw
    have h3 : ∫ ω, M.P (proc.S τ ω) s' ∂μ =
        ∑ u : M.State, (μ {ω | proc.S τ ω = u}).toReal * M.P u s' := by
      have hdec : (fun ω => M.P (proc.S τ ω) s') =
          fun ω => ∑ u : M.State, {ω | proc.S τ ω = u}.indicator (fun _ => M.P u s') ω := by
        funext ω
        symm
        rw [Finset.sum_eq_single (proc.S τ ω)]
        · rw [Set.indicator_of_mem]; rfl
        · intro u _ hne; rw [Set.indicator_of_notMem]; exact fun h => hne h.symm
        · intro hnot; exact absurd (Finset.mem_univ _) hnot
      rw [hdec, integral_finsetSum _ (fun u _ => (integrable_const _).indicator (proc.measurable_S τ u))]
      refine Finset.sum_congr rfl (fun u _ => ?_)
      rw [integral_indicator_const _ (proc.measurable_S τ u), smul_eq_mul, measureReal_def]
    rw [h1, h2, h3]
    simp_rw [marginal_prob_eq proc τ, Routine.matPow, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun s₀ _ => Finset.sum_congr rfl (fun u _ => by ring))

/-- Expectation of `φ (proc.S τ ω)` converges to `∑ s, M.π s * φ s` at geometric rate. -/
lemma abs_integral_state_sub_stationary_le {M : NetworkModel} {Ω : Type} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (proc : M.MarkovProcess Ω μ) {C ρ : ℝ}
    (hmix : ∀ n s, ∑ s', |Routine.matPow M.P n s s' - M.π s'| ≤ C * ρ ^ n)
    (φ : M.State → ℝ) {K : ℝ} (hK : ∀ s, |φ s| ≤ K) (τ : ℕ) :
    |(∫ ω, φ (proc.S τ ω) ∂μ) - ∑ s', M.π s' * φ s'| ≤ C * ρ ^ τ * K := by
  have hK0 : 0 ≤ K := by
    obtain ⟨s₀⟩ := M.stateNonempty
    exact le_trans (abs_nonneg _) (hK s₀)
  have hint_eq : ∫ ω, φ (proc.S τ ω) ∂μ = ∑ s', (μ {ω | proc.S τ ω = s'}).toReal * φ s' := by
    have hdec : (fun ω => φ (proc.S τ ω)) =
        fun ω => ∑ s' : M.State, {ω | proc.S τ ω = s'}.indicator (fun _ => φ s') ω := by
      funext ω
      symm
      rw [Finset.sum_eq_single (proc.S τ ω)]
      · rw [Set.indicator_of_mem]; rfl
      · intro s' _ hne; rw [Set.indicator_of_notMem]; exact fun h => hne h.symm
      · intro hnot; exact absurd (Finset.mem_univ _) hnot
    rw [hdec, integral_finsetSum _ (fun s' _ => (integrable_const _).indicator (proc.measurable_S τ s'))]
    refine Finset.sum_congr rfl (fun s' _ => ?_)
    rw [integral_indicator_const _ (proc.measurable_S τ s'), smul_eq_mul, measureReal_def]
  have hprob0_sum : ∑ s₀ : M.State, (μ {ω | proc.S 0 ω = s₀}).toReal = 1 := by
    have h1 := integral_const (1 : ℝ) (μ := μ)
    have hdec : (fun _ : Ω => (1 : ℝ)) =
        fun ω => ∑ s₀ : M.State, {ω | proc.S 0 ω = s₀}.indicator (fun _ => (1 : ℝ)) ω := by
      funext ω
      symm
      rw [Finset.sum_eq_single (proc.S 0 ω)]
      · rw [Set.indicator_of_mem]; rfl
      · intro s₀ _ hne; rw [Set.indicator_of_notMem]; exact fun h => hne h.symm
      · intro hnot; exact absurd (Finset.mem_univ _) hnot
    have hint1 : ∫ _ : Ω, (1 : ℝ) ∂μ = 1 := by
      simp [integral_const, measureReal_def, measure_univ]
    rw [← hint1, hdec, integral_finsetSum _ (fun s₀ _ => (integrable_const _).indicator (proc.measurable_S 0 s₀))]
    refine Finset.sum_congr rfl (fun s₀ _ => ?_)
    rw [integral_indicator_const _ (proc.measurable_S 0 s₀), smul_eq_mul, mul_one, measureReal_def]
  rw [hint_eq]
  simp_rw [marginal_prob_eq proc τ]
  have hdiff : (∑ s', (∑ s₀, (μ {ω | proc.S 0 ω = s₀}).toReal * Routine.matPow M.P τ s₀ s') * φ s') -
      ∑ s', M.π s' * φ s' =
      ∑ s₀, (μ {ω | proc.S 0 ω = s₀}).toReal * ∑ s', (Routine.matPow M.P τ s₀ s' - M.π s') * φ s' := by
    have hstat : ∑ s', M.π s' * φ s' =
        ∑ s₀, (μ {ω | proc.S 0 ω = s₀}).toReal * ∑ s', M.π s' * φ s' := by
      rw [← Finset.sum_mul, hprob0_sum, one_mul]
    rw [hstat]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun s₀ _ => ?_)
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun s' _ => by ring)
  rw [hdiff]
  calc |∑ s₀, (μ {ω | proc.S 0 ω = s₀}).toReal * ∑ s', (Routine.matPow M.P τ s₀ s' - M.π s') * φ s'|
      ≤ ∑ s₀, |(μ {ω | proc.S 0 ω = s₀}).toReal * ∑ s', (Routine.matPow M.P τ s₀ s' - M.π s') * φ s'| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ s₀, (μ {ω | proc.S 0 ω = s₀}).toReal * |∑ s', (Routine.matPow M.P τ s₀ s' - M.π s') * φ s'| := by
        refine Finset.sum_congr rfl (fun s₀ _ => ?_)
        rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
    _ ≤ ∑ s₀, (μ {ω | proc.S 0 ω = s₀}).toReal * (C * ρ ^ τ * K) := by
        refine Finset.sum_le_sum (fun s₀ _ => mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg)
        calc |∑ s', (Routine.matPow M.P τ s₀ s' - M.π s') * φ s'|
            ≤ ∑ s', |Routine.matPow M.P τ s₀ s' - M.π s'| * |φ s'| := by
                refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
                exact Finset.sum_le_sum (fun s' _ => by rw [abs_mul])
          _ ≤ ∑ s', |Routine.matPow M.P τ s₀ s' - M.π s'| * K :=
                Finset.sum_le_sum (fun s' _ => mul_le_mul_of_nonneg_left (hK s') (abs_nonneg _))
          _ = (∑ s', |Routine.matPow M.P τ s₀ s' - M.π s'|) * K := (Finset.sum_mul _ _ _).symm
          _ ≤ (C * ρ ^ τ) * K := mul_le_mul_of_nonneg_right (hmix τ s₀) hK0
    _ = C * ρ ^ τ * K := by rw [← Finset.sum_mul, hprob0_sum, one_mul]

/-! ### Properties of `M.dualState`, `M.dual`, and Backpressure policies -/

/-- `B = √r * δ_max` bound on `‖A - μ‖₂`. -/
noncomputable def driftBound (M : NetworkModel) : ℝ :=
  Real.sqrt (M.r : ℝ) * M.δmax

lemma driftBound_sq (M : NetworkModel) :
    (driftBound M) ^ 2 = (M.r : ℝ) * M.δmax ^ 2 := by
  unfold driftBound
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg M.r)]

lemma driftBound_pos (M : NetworkModel) : 0 < driftBound M :=
  mul_pos (Real.sqrt_pos.mpr (Nat.cast_pos.mpr M.hr)) M.hδmax

lemma abs_sum_mul_arr_sub_serv_le (M : NetworkModel) (s : M.State) (x : M.Action s)
    (v : Fin M.r → ℝ) :
    |∑ j : Fin M.r, v j * (M.arrival s x j - M.service s x j)| ≤
      driftBound M * Real.sqrt (∑ j : Fin M.r, (v j) ^ 2) := by
  have hcs := abs_sum_mul_le_sqrt_mul_sqrt v (fun j => M.arrival s x j - M.service s x j)
  have hdiff_sq : ∑ j : Fin M.r, (M.arrival s x j - M.service s x j) ^ 2 ≤ (M.r : ℝ) * M.δmax ^ 2 := by
    calc ∑ j : Fin M.r, (M.arrival s x j - M.service s x j) ^ 2
        ≤ ∑ _j : Fin M.r, M.δmax ^ 2 := by
            refine Finset.sum_le_sum (fun j _ => ?_)
            have h1 := M.arrival_nonneg s x j
            have h2 := M.arrival_le s x j
            have h3 := M.service_nonneg s x j
            have h4 := M.service_le s x j
            nlinarith
      _ = (M.r : ℝ) * M.δmax ^ 2 := by simp
  have hsqrt : Real.sqrt (∑ j : Fin M.r, (M.arrival s x j - M.service s x j) ^ 2) ≤ driftBound M := by
    calc Real.sqrt (∑ j : Fin M.r, (M.arrival s x j - M.service s x j) ^ 2)
        ≤ Real.sqrt ((M.r : ℝ) * M.δmax ^ 2) := Real.sqrt_le_sqrt hdiff_sq
      _ = Real.sqrt (M.r : ℝ) * Real.sqrt (M.δmax ^ 2) := Real.sqrt_mul (Nat.cast_nonneg _) _
      _ = driftBound M := by rw [Real.sqrt_sq (le_of_lt M.hδmax)]; rfl
  calc |∑ j : Fin M.r, v j * (M.arrival s x j - M.service s x j)|
      ≤ Real.sqrt (∑ j : Fin M.r, (v j) ^ 2) *
          Real.sqrt (∑ j : Fin M.r, (M.arrival s x j - M.service s x j) ^ 2) := hcs
    _ ≤ Real.sqrt (∑ j : Fin M.r, (v j) ^ 2) * driftBound M :=
          mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg _)
    _ = driftBound M * Real.sqrt (∑ j : Fin M.r, (v j) ^ 2) := mul_comm _ _

lemma bddBelow_dualState (M : NetworkModel) (V : ℝ) (s : M.State) (γ : Fin M.r → ℝ) :
    BddBelow (Set.range (fun x : M.Action s =>
      V * M.cost s x + ∑ j : Fin M.r, γ j * (M.arrival s x j - M.service s x j))) := by
  refine ⟨-(|V| * M.δmax + driftBound M * Real.sqrt (∑ j, (γ j) ^ 2)), ?_⟩
  rintro _ ⟨x, rfl⟩
  have h1 : |V * M.cost s x| ≤ |V| * M.δmax := by
    rw [abs_mul, abs_of_nonneg (M.cost_nonneg s x)]
    exact mul_le_mul_of_nonneg_left (M.cost_le s x) (abs_nonneg V)
  have h2 := abs_sum_mul_arr_sub_serv_le M s x γ
  have h3 := neg_abs_le (V * M.cost s x)
  have h4 := neg_abs_le (∑ j : Fin M.r, γ j * (M.arrival s x j - M.service s x j))
  linarith

lemma dualState_le (M : NetworkModel) (V : ℝ) (s : M.State) (γ : Fin M.r → ℝ) (x : M.Action s) :
    M.dualState V s γ ≤
      V * M.cost s x + ∑ j : Fin M.r, γ j * (M.arrival s x j - M.service s x j) :=
  ciInf_le (bddBelow_dualState M V s γ) x

lemma dualState_eq_of_bp (M : NetworkModel) {V : ℝ} {choice : (s : M.State) → (Fin M.r → ℝ) → M.Action s}
    (hbp : M.IsBackpressureRule V choice) (s : M.State) (q : Fin M.r → ℝ) :
    M.dualState V s q =
      V * M.cost s (choice s q) +
        ∑ j : Fin M.r, q j * (M.arrival s (choice s q) j - M.service s (choice s q) j) := by
  refine le_antisymm (dualState_le M V s q (choice s q)) ?_
  refine le_ciInf (fun x => ?_)
  have h := hbp s q x
  have hneg : ∀ y : M.Action s,
      -(V * M.cost s y + ∑ j : Fin M.r, q j * (M.arrival s y j - M.service s y j)) =
      -V * M.cost s y + ∑ j : Fin M.r, q j * (M.service s y j - M.arrival s y j) := by
    intro y
    rw [neg_add, ← Finset.sum_neg_distrib]
    congr 1
    · ring
    · refine Finset.sum_congr rfl (fun j _ => by ring)
  linarith [hneg x, hneg (choice s q)]

lemma abs_dualState_le (M : NetworkModel) {V : ℝ} (hV : 0 ≤ V) (s : M.State) (γ : Fin M.r → ℝ) :
    |M.dualState V s γ| ≤ V * M.δmax + driftBound M * Real.sqrt (∑ j : Fin M.r, (γ j) ^ 2) := by
  rw [abs_le]
  constructor
  · refine le_ciInf (fun x => ?_)
    have h1 : 0 ≤ V * M.cost s x := mul_nonneg hV (M.cost_nonneg s x)
    have h2 := abs_sum_mul_arr_sub_serv_le M s x γ
    have h3 := neg_abs_le (∑ j : Fin M.r, γ j * (M.arrival s x j - M.service s x j))
    linarith [mul_nonneg hV (le_of_lt M.hδmax)]
  · obtain ⟨x₀⟩ := M.actionNonempty s
    have h1 := dualState_le M V s γ x₀
    have h2 : V * M.cost s x₀ ≤ V * M.δmax := mul_le_mul_of_nonneg_left (M.cost_le s x₀) hV
    have h3 := le_trans (le_abs_self _) (abs_sum_mul_arr_sub_serv_le M s x₀ γ)
    linarith

lemma abs_dualState_sub_le (M : NetworkModel) (V : ℝ) (s : M.State) (γ₁ γ₂ : Fin M.r → ℝ) :
    |M.dualState V s γ₁ - M.dualState V s γ₂| ≤
      driftBound M * Real.sqrt (∑ j : Fin M.r, (γ₁ j - γ₂ j) ^ 2) := by
  have h1 : ∀ a b : Fin M.r → ℝ,
      M.dualState V s a - M.dualState V s b ≤
        driftBound M * Real.sqrt (∑ j : Fin M.r, (a j - b j) ^ 2) := by
    intro a b
    have hle : M.dualState V s a - driftBound M * Real.sqrt (∑ j : Fin M.r, (a j - b j) ^ 2) ≤
        M.dualState V s b := by
      refine le_ciInf (fun x => ?_)
      have hx := dualState_le M V s a x
      have hdiff : (V * M.cost s x + ∑ j, a j * (M.arrival s x j - M.service s x j)) -
          (V * M.cost s x + ∑ j, b j * (M.arrival s x j - M.service s x j)) =
          ∑ j, (a j - b j) * (M.arrival s x j - M.service s x j) := by
        have : ∀ j, a j * (M.arrival s x j - M.service s x j) -
            b j * (M.arrival s x j - M.service s x j) =
            (a j - b j) * (M.arrival s x j - M.service s x j) := fun j => by ring
        rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun j _ => this j)
      have habs := le_trans (le_abs_self _) (abs_sum_mul_arr_sub_serv_le M s x (fun j => a j - b j))
      linarith
    linarith
  rw [abs_le]
  refine ⟨?_, h1 γ₁ γ₂⟩
  have h2 := h1 γ₂ γ₁
  have hsym : ∑ j : Fin M.r, (γ₂ j - γ₁ j) ^ 2 = ∑ j : Fin M.r, (γ₁ j - γ₂ j) ^ 2 :=
    Finset.sum_congr rfl (fun j _ => by ring)
  rw [hsym] at h2
  linarith

/-- Under `η`-slackness, `g(V, q) ≤ V * δ_max - η * ∑_j q_j` for all `q ⪰ 0`. -/
lemma dual_le_of_slackness {M : NetworkModel} {η : ℝ} (hslack : M.HasSlackness η)
    {V : ℝ} (hV : 0 ≤ V) {q : Fin M.r → ℝ} (hq : ∀ j, 0 ≤ q j) :
    M.dual V q ≤ V * M.δmax - η * ∑ j : Fin M.r, q j := by
  rcases hslack with ⟨_, m, x, θ, hθ_nonneg, hθ_sum, hdrift⟩
  have hstate : ∀ s : M.State, M.dualState V s q ≤
      V * M.δmax + ∑ j : Fin M.r, q j *
        (∑ k : Fin m, θ s k * (M.arrival s (x s k) j - M.service s (x s k) j)) := by
    intro s
    have hterm : ∀ k : Fin m, θ s k * M.dualState V s q ≤
        θ s k * (V * M.δmax + ∑ j, q j * (M.arrival s (x s k) j - M.service s (x s k) j)) := by
      intro k
      refine mul_le_mul_of_nonneg_left ?_ (hθ_nonneg s k)
      have hd := dualState_le M V s q (x s k)
      have hc : V * M.cost s (x s k) ≤ V * M.δmax := mul_le_mul_of_nonneg_left (M.cost_le s (x s k)) hV
      linarith
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun k _ => hterm k)
    rw [← Finset.sum_mul, hθ_sum s, one_mul] at hsum
    simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hθ_sum s, one_mul] at hsum
    have hswap : ∑ k : Fin m, θ s k * ∑ j : Fin M.r, q j * (M.arrival s (x s k) j - M.service s (x s k) j) =
        ∑ j : Fin M.r, q j * ∑ k : Fin m, θ s k * (M.arrival s (x s k) j - M.service s (x s k) j) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => by ring))
    linarith [hsum, hswap]
  unfold NetworkModel.dual
  have hpi := Finset.sum_le_sum (s := Finset.univ) (fun s _ =>
    mul_le_mul_of_nonneg_left (hstate s) (le_of_lt (M.π_pos s)))
  simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, M.π_sum_one, one_mul] at hpi
  have hswap2 : ∑ s : M.State, M.π s * ∑ j : Fin M.r, q j *
      (∑ k : Fin m, θ s k * (M.arrival s (x s k) j - M.service s (x s k) j)) =
      ∑ j : Fin M.r, q j *
        (∑ s : M.State, M.π s * ∑ k : Fin m, θ s k * (M.arrival s (x s k) j - M.service s (x s k) j)) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    exact Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun k _ => by ring))
  have hneg : ∑ j : Fin M.r, q j *
      (∑ s : M.State, M.π s * ∑ k : Fin m, θ s k * (M.arrival s (x s k) j - M.service s (x s k) j)) ≤
      ∑ j : Fin M.r, q j * (-η) :=
    Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hdrift j) (hq j))
  have hrhs : ∑ j : Fin M.r, q j * (-η) = -η * ∑ j : Fin M.r, q j := by
    rw [← Finset.sum_mul]; ring
  linarith

/-! ### Queue regularity for any policy, and finite-history representation for Backpressure -/

private lemma pol_queue_nonneg {M : NetworkModel} {Ω : Type} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {proc : M.MarkovProcess Ω μ}
    (pol : M.Policy proc) : ∀ (τ : ℕ) (ω : Ω) (j : Fin M.r), 0 ≤ pol.queue τ ω j
  | 0, _, _ => le_rfl
  | _ + 1, _, _ => add_nonneg (le_max_right _ _) (M.arrival_nonneg _ _ _)

private lemma pol_queue_le_mul {M : NetworkModel} {Ω : Type} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {proc : M.MarkovProcess Ω μ}
    (pol : M.Policy proc) : ∀ (τ : ℕ) (ω : Ω) (j : Fin M.r), pol.queue τ ω j ≤ (τ : ℝ) * M.δmax
  | 0, _, _ => by simp [NetworkModel.Policy.queue]
  | t + 1, ω, j => by
    change max (pol.queue t ω j - M.service (proc.S t ω) (pol.act t ω) j) 0 +
      M.arrival (proc.S t ω) (pol.act t ω) j ≤ ((t + 1 : ℕ) : ℝ) * M.δmax
    have hq := pol_queue_nonneg pol t ω j
    have hle := pol_queue_le_mul pol t ω j
    have hs := M.service_nonneg (proc.S t ω) (pol.act t ω) j
    have ha := M.arrival_le (proc.S t ω) (pol.act t ω) j
    have hmax : max (pol.queue t ω j - M.service (proc.S t ω) (pol.act t ω) j) 0 ≤ pol.queue t ω j :=
      max_le (by linarith) hq
    push_cast
    linarith

private lemma pol_measurable_queue {M : NetworkModel} {Ω : Type} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {proc : M.MarkovProcess Ω μ}
    (pol : M.Policy proc) : ∀ (τ : ℕ) (j : Fin M.r), Measurable (fun ω => pol.queue τ ω j)
  | 0, _ => measurable_const
  | t + 1, j =>
    (((pol_measurable_queue pol t j).sub (pol.measurable_service t j)).max measurable_const).add
      (pol.measurable_arrival t j)

private lemma pol_integrable_queue {M : NetworkModel} {Ω : Type} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {proc : M.MarkovProcess Ω μ}
    (pol : M.Policy proc) (τ : ℕ) (j : Fin M.r) :
    Integrable (fun ω => pol.queue τ ω j) μ := by
  refine Integrable.of_bound (pol_measurable_queue pol τ j).aestronglyMeasurable ((τ : ℝ) * M.δmax) ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (pol_queue_nonneg pol τ ω j)]
  exact pol_queue_le_mul pol τ ω j

private lemma pol_integrable_cost {M : NetworkModel} {Ω : Type} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {proc : M.MarkovProcess Ω μ}
    (pol : M.Policy proc) (τ : ℕ) :
    Integrable (fun ω => M.cost (proc.S τ ω) (pol.act τ ω)) μ := by
  refine Integrable.of_bound (pol.measurable_cost τ).aestronglyMeasurable M.δmax ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (M.cost_nonneg _ _)]
  exact M.cost_le _ _

/-- Deterministic queue vector as a function of the finite Markov history `h : Fin t → M.State`. -/
def bpQueueHist (M : NetworkModel) (choice : (s : M.State) → (Fin M.r → ℝ) → M.Action s) :
    (t : ℕ) → (Fin t → M.State) → (Fin M.r → ℝ)
  | 0, _ => fun _ => 0
  | t + 1, h =>
    let q := bpQueueHist M choice t (fun i => h i.castSucc)
    let s := h (Fin.last t)
    let x := choice s q
    NetworkModel.queueNext q (M.service s x) (M.arrival s x)

lemma bp_queue_eq_hist {M : NetworkModel} {Ω : Type} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {proc : M.MarkovProcess Ω μ}
    {pol : M.Policy proc} {choice : (s : M.State) → (Fin M.r → ℝ) → M.Action s}
    (hact : ∀ t ω, pol.act t ω = choice (proc.S t ω) (pol.queue t ω)) :
    ∀ (t : ℕ) (ω : Ω), pol.queue t ω = bpQueueHist M choice t (fun i => proc.S i ω)
  | 0, _ => rfl
  | t + 1, ω => by
    simp only [NetworkModel.Policy.queue, bpQueueHist, hact t ω, bp_queue_eq_hist hact t ω]
    rfl

/-! ### Step 2: Elementary Weak Duality (`dual V γ / V ≤ optCost`) -/

/-- Direct weak duality: for every stable policy `pol_any` and every `γ ⪰ 0`,
`g(V, γ) / V ≤ f_av^{pol_any}`. -/
lemma dual_div_V_le_avgCost {M : NetworkModel} {Ω : Type} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (proc : M.MarkovProcess Ω μ) {C ρ : ℝ}
    (hC : 0 < C) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hmix : ∀ n s, ∑ s', |Routine.matPow M.P n s s' - M.π s'| ≤ C * ρ ^ n)
    {V : ℝ} (hV : 1 ≤ V) (pol_any : M.Policy proc) (hstab : pol_any.IsStable)
    (γ : Fin M.r → ℝ) (hγ : ∀ j, 0 ≤ γ j) :
    ((M.dual V γ / V : ℝ) : EReal) ≤ pol_any.avgCost := by
  have hV_pos : 0 < V := lt_of_lt_of_le zero_lt_one hV
  -- Bound on `|dualState V s γ|`
  let Mφ : ℝ := V * M.δmax + driftBound M * Real.sqrt (∑ j : Fin M.r, (γ j) ^ 2)
  have hMφ : ∀ s : M.State, |M.dualState V s γ| ≤ Mφ := fun s =>
    abs_dualState_le M (le_of_lt hV_pos) s γ
  -- One-slot expectation inequality for every `τ`
  have hslot : ∀ τ : ℕ,
      ∫ ω, M.dualState V (proc.S τ ω) γ ∂μ ≤
        V * (∫ ω, M.cost (proc.S τ ω) (pol_any.act τ ω) ∂μ) +
        (∑ j : Fin M.r, γ j * ∫ ω, pol_any.queue (τ + 1) ω j ∂μ) -
        (∑ j : Fin M.r, γ j * ∫ ω, pol_any.queue τ ω j ∂μ) := by
    intro τ
    have hpt : ∀ ω : Ω, M.dualState V (proc.S τ ω) γ ≤
        V * M.cost (proc.S τ ω) (pol_any.act τ ω) +
        ∑ j : Fin M.r, γ j * (pol_any.queue (τ + 1) ω j - pol_any.queue τ ω j) := by
      intro ω
      have h1 := dualState_le M V (proc.S τ ω) γ (pol_any.act τ ω)
      have h2 : ∑ j : Fin M.r, γ j * (M.arrival (proc.S τ ω) (pol_any.act τ ω) j -
          M.service (proc.S τ ω) (pol_any.act τ ω) j) ≤
          ∑ j : Fin M.r, γ j * (pol_any.queue (τ + 1) ω j - pol_any.queue τ ω j) := by
        refine Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left ?_ (hγ j))
        exact sub_le_max_sub_add _ _ _
      linarith
    have hint_lhs : Integrable (fun ω => M.dualState V (proc.S τ ω) γ) μ := by
      have hdec := (integral_history_eq_sum proc τ (fun h => M.dualState V (h (Fin.last τ)) γ)).1
      simpa using hdec
    have hint_term : ∀ j ∈ (Finset.univ : Finset (Fin M.r)),
        Integrable (fun ω => γ j * (pol_any.queue (τ + 1) ω j - pol_any.queue τ ω j)) μ :=
      fun j _ => ((pol_integrable_queue pol_any (τ + 1) j).sub (pol_integrable_queue pol_any τ j)).const_mul _
    have hint_rhs : Integrable (fun ω =>
        V * M.cost (proc.S τ ω) (pol_any.act τ ω) +
        ∑ j : Fin M.r, γ j * (pol_any.queue (τ + 1) ω j - pol_any.queue τ ω j)) μ :=
      ((pol_integrable_cost pol_any τ).const_mul V).add (integrable_finsetSum _ hint_term)
    have hint_le := integral_mono hint_lhs hint_rhs hpt
    rw [integral_add ((pol_integrable_cost pol_any τ).const_mul V) (integrable_finsetSum _ hint_term),
      integral_const_mul, integral_finsetSum _ hint_term] at hint_le
    have hsum_eq : ∑ j : Fin M.r, ∫ ω, γ j * (pol_any.queue (τ + 1) ω j - pol_any.queue τ ω j) ∂μ =
        (∑ j : Fin M.r, γ j * ∫ ω, pol_any.queue (τ + 1) ω j ∂μ) -
        (∑ j : Fin M.r, γ j * ∫ ω, pol_any.queue τ ω j ∂μ) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [integral_const_mul, integral_sub (pol_integrable_queue pol_any (τ + 1) j)
        (pol_integrable_queue pol_any τ j)]
      ring
    linarith [hint_le, hsum_eq]
  -- Telescope from `0` to `t - 1`
  have htele : ∀ t : ℕ,
      ∑ τ ∈ Finset.range t, ∫ ω, M.dualState V (proc.S τ ω) γ ∂μ ≤
        V * (∑ τ ∈ Finset.range t, ∫ ω, M.cost (proc.S τ ω) (pol_any.act τ ω) ∂μ) +
        (∑ j : Fin M.r, γ j) * (∑ j : Fin M.r, ∫ ω, pol_any.queue t ω j ∂μ) := by
    intro t
    have hsum := Finset.sum_le_sum (s := Finset.range t) (fun τ _ => hslot τ)
    let Q : ℕ → ℝ := fun τ => ∑ j : Fin M.r, γ j * ∫ ω, pol_any.queue τ ω j ∂μ
    have hQ0 : Q 0 = 0 := by simp [Q, NetworkModel.Policy.queue]
    have hsum_rhs : ∑ τ ∈ Finset.range t,
        (V * (∫ ω, M.cost (proc.S τ ω) (pol_any.act τ ω) ∂μ) + Q (τ + 1) - Q τ) =
        V * (∑ τ ∈ Finset.range t, ∫ ω, M.cost (proc.S τ ω) (pol_any.act τ ω) ∂μ) + Q t := by
      have h1 : ∀ τ, V * (∫ ω, M.cost (proc.S τ ω) (pol_any.act τ ω) ∂μ) + Q (τ + 1) - Q τ =
          V * (∫ ω, M.cost (proc.S τ ω) (pol_any.act τ ω) ∂μ) + (Q (τ + 1) - Q τ) := fun _ => by ring
      simp_rw [h1, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_range_sub Q t, hQ0, sub_zero]
    have hQt_le : Q t ≤ (∑ j : Fin M.r, γ j) * (∑ j : Fin M.r, ∫ ω, pol_any.queue t ω j ∂μ) := by
      dsimp [Q]
      have hq_int_nonneg : ∀ j, 0 ≤ ∫ ω, pol_any.queue t ω j ∂μ := fun j =>
        integral_nonneg (fun ω => pol_queue_nonneg pol_any t ω j)
      calc ∑ j : Fin M.r, γ j * ∫ ω, pol_any.queue t ω j ∂μ
          ≤ ∑ j : Fin M.r, γ j * (∑ j' : Fin M.r, ∫ ω, pol_any.queue t ω j' ∂μ) :=
            Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left
              (Finset.single_le_sum (fun j' _ => hq_int_nonneg j') (Finset.mem_univ j)) (hγ j))
        _ = (∑ j : Fin M.r, γ j) * (∑ j' : Fin M.r, ∫ ω, pol_any.queue t ω j' ∂μ) :=
            (Finset.sum_mul _ _ _).symm
    linarith [hsum, hsum_rhs, hQt_le]
  -- Conclude `dual V γ / V ≤ pol_any.avgCost` by contradiction
  by_contra hnot
  have hlt : pol_any.avgCost < ((M.dual V γ / V : ℝ) : EReal) := lt_of_not_ge hnot
  obtain ⟨y, hy1, hy2⟩ := EReal.exists_between_coe_real hlt
  have hy_lt : y < M.dual V γ / V := EReal.coe_lt_coe_iff.mp hy2
  set ε : ℝ := (M.dual V γ / V - y) / 3
  have hε_pos : 0 < ε := by dsimp [ε]; linarith
  -- Event 1: eventually `(1/t) * ∑ E[cost] < y`
  have hev_cost : ∀ᶠ t : ℕ in Filter.atTop,
      ((1 : ℝ) / (t : ℝ)) * ∑ τ ∈ Finset.range t, ∫ ω, M.cost (proc.S τ ω) (pol_any.act τ ω) ∂μ < y := by
    have h := Filter.eventually_lt_of_limsup_lt hy1
    filter_upwards [h] with t ht
    exact EReal.coe_lt_coe_iff.mp ht
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp hev_cost
  -- Event 2: for `t ≥ N₂`, `(1/t) * ∑ E[dualState] ≥ dual V γ - V * ε`
  have h1ρ : 0 < 1 - ρ := sub_pos.mpr hρ1
  have hMφ0 : 0 ≤ Mφ := by
    obtain ⟨s₀⟩ := M.stateNonempty
    exact le_trans (abs_nonneg _) (hMφ s₀)
  let Bmix : ℝ := C * Mφ / (1 - ρ)
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt (Bmix / (V * ε))
  -- Event 3: stability gives `t ≥ max N₁ (max N₂ 1)` with small `a(t) / t`
  let a : ℕ → ℝ := fun t => ∑ j : Fin M.r, ∫ ω, pol_any.queue t ω j ∂μ
  have ha_nonneg : ∀ t, 0 ≤ a t := fun t =>
    Finset.sum_nonneg (fun j _ => integral_nonneg (fun ω => pol_queue_nonneg pol_any t ω j))
  let γsum : ℝ := ∑ j : Fin M.r, γ j
  have hγsum_nonneg : 0 ≤ γsum := Finset.sum_nonneg (fun j _ => hγ j)
  let ε' : ℝ := ε / (γsum / V + 1)
  have hε'_pos : 0 < ε' := div_pos hε_pos (by positivity)
  obtain ⟨t, ht_ge, ht_pos, ha_small⟩ :=
    exists_small_ratio_of_avg_limsup_lt_top ha_nonneg hstab hε'_pos (max N₁ (max N₂ 1))
  have ht_real_pos : (0 : ℝ) < (t : ℝ) := Nat.cast_pos.mpr ht_pos
  have ht_N1 : N₁ ≤ t := le_trans (le_max_left _ _) ht_ge
  have ht_N2 : N₂ ≤ t := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) ht_ge)
  have hcost_lt : ((1 : ℝ) / (t : ℝ)) *
      ∑ τ ∈ Finset.range t, ∫ ω, M.cost (proc.S τ ω) (pol_any.act τ ω) ∂μ < y := hN₁ t ht_N1
  -- Mixing bound on `∑ τ < t, E[dualState]`
  have hmix_sum : |(∑ τ ∈ Finset.range t, ∫ ω, M.dualState V (proc.S τ ω) γ ∂μ) - (t : ℝ) * M.dual V γ| ≤ Bmix := by
    have heq : (∑ τ ∈ Finset.range t, ∫ ω, M.dualState V (proc.S τ ω) γ ∂μ) - (t : ℝ) * M.dual V γ =
        ∑ τ ∈ Finset.range t, ((∫ ω, M.dualState V (proc.S τ ω) γ ∂μ) - M.dual V γ) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [heq]
    calc |∑ τ ∈ Finset.range t, ((∫ ω, M.dualState V (proc.S τ ω) γ ∂μ) - M.dual V γ)|
        ≤ ∑ τ ∈ Finset.range t, |(∫ ω, M.dualState V (proc.S τ ω) γ ∂μ) - M.dual V γ| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ τ ∈ Finset.range t, C * ρ ^ τ * Mφ :=
          Finset.sum_le_sum (fun τ _ =>
            abs_integral_state_sub_stationary_le proc hmix (fun s => M.dualState V s γ) hMφ τ)
      _ = (C * Mφ) * ∑ τ ∈ Finset.range t, ρ ^ τ := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun τ _ => by ring)
      _ ≤ (C * Mφ) * (1 - ρ)⁻¹ := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (le_of_lt hC) hMφ0)
          rw [← tsum_geometric_of_lt_one hρ0 hρ1]
          exact (summable_geometric_of_lt_one hρ0 hρ1).sum_le_tsum (Finset.range t)
            (fun n _ => pow_nonneg hρ0 n)
      _ = Bmix := by dsimp [Bmix]; ring
  have hBmix_lt : Bmix / (t : ℝ) < V * ε := by
    have h1 : Bmix / (V * ε) < (t : ℝ) := lt_of_lt_of_le hN₂ (by exact_mod_cast ht_N2)
    have h2 : Bmix < (V * ε) * (t : ℝ) := by linarith [(div_lt_iff₀ (mul_pos hV_pos hε_pos)).mp h1]
    exact (div_lt_iff₀ ht_real_pos).mpr h2
  have hdual_ge : M.dual V γ - V * ε <
      ((1 : ℝ) / (t : ℝ)) * ∑ τ ∈ Finset.range t, ∫ ω, M.dualState V (proc.S τ ω) γ ∂μ := by
    have h1 := (abs_le.mp hmix_sum).1
    have h2 : (t : ℝ) * M.dual V γ - Bmix ≤
        ∑ τ ∈ Finset.range t, ∫ ω, M.dualState V (proc.S τ ω) γ ∂μ := by linarith
    have h3 : M.dual V γ - Bmix / (t : ℝ) ≤
        ((1 : ℝ) / (t : ℝ)) * ∑ τ ∈ Finset.range t, ∫ ω, M.dualState V (proc.S τ ω) γ ∂μ := by
      have hdiv := div_le_div_of_nonneg_right h2 (le_of_lt ht_real_pos)
      rw [sub_div, mul_div_cancel_left₀ _ ht_real_pos.ne'] at hdiv
      simpa [one_div, inv_mul_eq_div] using hdiv
    linarith
  have htele_t := htele t
  have hdiv_t : ((1 : ℝ) / (t : ℝ)) * ∑ τ ∈ Finset.range t, ∫ ω, M.dualState V (proc.S τ ω) γ ∂μ ≤
      V * (((1 : ℝ) / (t : ℝ)) * ∑ τ ∈ Finset.range t, ∫ ω, M.cost (proc.S τ ω) (pol_any.act τ ω) ∂μ) +
      γsum * (a t / (t : ℝ)) := by
    have h := mul_le_mul_of_nonneg_left htele_t (by positivity : 0 ≤ (1 : ℝ) / (t : ℝ))
    have hrhs : (1 : ℝ) / (t : ℝ) *
        (V * (∑ τ ∈ Finset.range t, ∫ ω, M.cost (proc.S τ ω) (pol_any.act τ ω) ∂μ) + γsum * a t) =
        V * (((1 : ℝ) / (t : ℝ)) * ∑ τ ∈ Finset.range t, ∫ ω, M.cost (proc.S τ ω) (pol_any.act τ ω) ∂μ) +
        γsum * (a t / (t : ℝ)) := by ring
    linarith
  have hγ_term : (γsum / V) * (a t / (t : ℝ)) < ε := by
    have h1 : (γsum / V) * (a t / (t : ℝ)) ≤ (γsum / V + 1) * (a t / (t : ℝ)) :=
      mul_le_mul_of_nonneg_right (by linarith) (div_nonneg (ha_nonneg t) (le_of_lt ht_real_pos))
    have h2 : (γsum / V + 1) * (a t / (t : ℝ)) < (γsum / V + 1) * ε' :=
      mul_lt_mul_of_pos_left ha_small (by positivity)
    have h3 : (γsum / V + 1) * ε' = ε := by
      dsimp [ε']
      exact mul_div_cancel₀ ε (by positivity)
    linarith
  have hfinal_mul : M.dual V γ - V * ε < V * y + V * ε := by
    have hVcost : V * (((1 : ℝ) / (t : ℝ)) *
        ∑ τ ∈ Finset.range t, ∫ ω, M.cost (proc.S τ ω) (pol_any.act τ ω) ∂μ) < V * y :=
      mul_lt_mul_of_pos_left hcost_lt hV_pos
    have hVγ : γsum * (a t / (t : ℝ)) < V * ε := by
      have := mul_lt_mul_of_pos_left hγ_term hV_pos
      have heq : V * (γsum / V * (a t / (t : ℝ))) = γsum * (a t / (t : ℝ)) := by
        field_simp [hV_pos.ne']
      linarith
    linarith
  have hfinal : M.dual V γ / V - ε < y + ε := by
    have := (div_lt_div_iff_of_pos_right hV_pos).mpr hfinal_mul
    rw [sub_div, add_div, mul_div_cancel_left₀ _ hV_pos.ne', mul_div_cancel_left₀ _ hV_pos.ne'] at this
    exact this
  dsimp [ε] at hfinal
  linarith

/-! ### Step 3 & 4: Main Theorem 2 Proof via Quadratic Lyapunov + Poisson Telescoping -/

/-- Proof of Theorem 2 (`theorem:qla-markovian`): `[O(1/V), O(V)]` utility-delay tradeoff
under finite-state irreducible aperiodic Markovian network dynamics. -/
theorem theorem2 : Theorem2Statement := by
  intro M η hslack
  have hη_pos : 0 < η := hslack.1
  -- Extract `V`-independent geometric mixing parameters `(C_mix, ρ)` depending only on `M`
  have hirr : ∀ s s', ∃ n : ℕ, 0 < n ∧ 0 < Routine.matPow M.P n s s' := by
    intro s s'
    obtain ⟨n, hn, hpos⟩ := M.P_irreducible s s'
    exact ⟨n, hn, by rwa [← statements_matPow_eq_routine]⟩
  have haper : ∀ s : M.State, ∀ d : ℕ,
      (∀ n : ℕ, 0 < n → 0 < Routine.matPow M.P n s s → d ∣ n) → d = 1 := by
    intro s d hd
    exact M.P_aperiodic s d (fun n hn hpos => hd n hn (by rwa [← statements_matPow_eq_routine]))
  obtain ⟨C_mix, ρ, hC_mix, hρ0, hρ1, hmix⟩ :=
    exists_geometric_mixing M.P_nonneg M.P_sum_one hirr haper
      (fun s => le_of_lt (M.π_pos s)) M.π_sum_one M.π_stationary
  let C' : ℝ := C_mix / (1 - ρ)
  have hC'_pos : 0 < C' := div_pos hC_mix (sub_pos.mpr hρ1)
  let B : ℝ := driftBound M
  have hB_pos : 0 < B := driftBound_pos M
  have hB_sq : B ^ 2 = (M.r : ℝ) * M.δmax ^ 2 := driftBound_sq M
  -- Define `V`-independent constants `C_cost`, `C_q0`, `C_q1`
  let C_cost : ℝ := (1 + C') * B ^ 2
  let C_q0 : ℝ := (1 + C') * B ^ 2 / η
  let C_q1 : ℝ := M.δmax / η
  refine ⟨C_cost, C_q0, C_q1,
    mul_nonneg (by linarith) (sq_nonneg _),
    div_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) (le_of_lt hη_pos),
    div_nonneg (le_of_lt M.hδmax) (le_of_lt hη_pos), ?_⟩
  intro V hV Ω _ μ _ proc pol hbp
  have hV_pos : 0 < V := lt_of_lt_of_le zero_lt_one hV
  rcases hbp with ⟨choice, hchoice_bp, hchoice_act⟩
  -- Define quadratic Lyapunov function `L(q)` and Poisson potential `hPot(q, s)`
  let L_fn : (Fin M.r → ℝ) → ℝ := fun q => (1 / 2 : ℝ) * ∑ j : Fin M.r, (q j) ^ 2
  let hPot : (Fin M.r → ℝ) → M.State → ℝ := fun q s =>
    poissonPotential M.P M.π (fun s' => M.dualState V s' q) s
  -- Bounds on `hPot`
  have hhPot_abs : ∀ q s, |hPot q s| ≤ C' * (V * M.δmax + B * Real.sqrt (∑ j : Fin M.r, (q j) ^ 2)) :=
    fun q s => abs_poissonPotential_le (le_of_lt hρ0) hρ1 hmix _
      (fun s' => abs_dualState_le M (le_of_lt hV_pos) s' q) s
  have hhPot_lip : ∀ q₁ q₂ s,
      |hPot q₁ s - hPot q₂ s| ≤ C' * (B * Real.sqrt (∑ j : Fin M.r, (q₁ j - q₂ j) ^ 2)) :=
    fun q₁ q₂ s => abs_poissonPotential_sub_le (le_of_lt hρ0) hρ1 hmix _ _
      (fun s' => abs_dualState_sub_le M V s' q₁ q₂) s
  -- Lower bound on `L(q) + hPot(q, s)` by completing the square
  have hLh_lower : ∀ q s, -(1 / 2 : ℝ) * (C' * B) ^ 2 - C' * V * M.δmax ≤ L_fn q + hPot q s := by
    intro q s
    let z : ℝ := Real.sqrt (∑ j : Fin M.r, (q j) ^ 2)
    have hz_sq : z ^ 2 = ∑ j : Fin M.r, (q j) ^ 2 :=
      Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    have habs := hhPot_abs q s
    have hlower : -(C' * (V * M.δmax + B * z)) ≤ hPot q s := (abs_le.mp habs).1
    have hsq_nonneg : 0 ≤ (1 / 2 : ℝ) * (z - C' * B) ^ 2 := by positivity
    dsimp [L_fn]
    rw [← hz_sq]
    nlinarith
  -- One-slot expected Lyapunov + Poisson drift inequality
  have hstep_exp : ∀ t : ℕ,
      (∫ ω, (L_fn (pol.queue (t + 1) ω) + hPot (pol.queue (t + 1) ω) (proc.S (t + 1) ω)) ∂μ) -
      (∫ ω, (L_fn (pol.queue t ω) + hPot (pol.queue t ω) (proc.S t ω)) ∂μ) +
      V * (∫ ω, M.cost (proc.S t ω) (pol.act t ω) ∂μ) ≤
      (1 + C') * B ^ 2 + ∫ ω, M.dual V (pol.queue t ω) ∂μ := by
    intro t
    -- Express every quantity at step `t` as a function of finite Markov history
    have hq_hist : ∀ ω, pol.queue t ω = bpQueueHist M choice t (fun i => proc.S i ω) :=
      bp_queue_eq_hist hchoice_act t
    have hq1_hist : ∀ ω, pol.queue (t + 1) ω = bpQueueHist M choice (t + 1) (fun i => proc.S i ω) :=
      bp_queue_eq_hist hchoice_act (t + 1)
    -- Pointwise one-slot quadratic drift + Poisson equation
    have hpt : ∀ ω : Ω,
        (L_fn (pol.queue (t + 1) ω) + hPot (pol.queue (t + 1) ω) (proc.S (t + 1) ω)) -
        (L_fn (pol.queue t ω) + hPot (pol.queue t ω) (proc.S t ω)) +
        V * M.cost (proc.S t ω) (pol.act t ω) ≤
        (1 + C') * B ^ 2 + M.dual V (pol.queue t ω) +
        (hPot (pol.queue t ω) (proc.S (t + 1) ω) -
          ∑ u : M.State, M.P (proc.S t ω) u * hPot (pol.queue t ω) u) := by
      intro ω
      have hquad := sum_quad_drift
        (pol_queue_nonneg pol t ω)
        (fun j => M.service_nonneg (proc.S t ω) (pol.act t ω) j)
        (fun j => M.arrival_nonneg (proc.S t ω) (pol.act t ω) j)
        (fun j => M.service_le (proc.S t ω) (pol.act t ω) j)
        (fun j => M.arrival_le (proc.S t ω) (pol.act t ω) j)
      have hbp_eq : M.dualState V (proc.S t ω) (pol.queue t ω) =
          V * M.cost (proc.S t ω) (pol.act t ω) +
          ∑ j : Fin M.r, pol.queue t ω j *
            (M.arrival (proc.S t ω) (pol.act t ω) j - M.service (proc.S t ω) (pol.act t ω) j) := by
        rw [hchoice_act t ω]
        exact dualState_eq_of_bp M hchoice_bp (proc.S t ω) (pol.queue t ω)
      have hpois := poisson_equation M.P_sum_one (le_of_lt hρ0) hρ1 hmix
        (fun s' => M.dualState V s' (pol.queue t ω)) (proc.S t ω)
      have hstep_norm : Real.sqrt (∑ j : Fin M.r, (pol.queue (t + 1) ω j - pol.queue t ω j) ^ 2) ≤ B :=
        sqrt_sum_sq_step_le
          (pol_queue_nonneg pol t ω)
          (fun j => M.service_nonneg (proc.S t ω) (pol.act t ω) j)
          (fun j => M.arrival_nonneg (proc.S t ω) (pol.act t ω) j)
          (fun j => M.service_le (proc.S t ω) (pol.act t ω) j)
          (fun j => M.arrival_le (proc.S t ω) (pol.act t ω) j)
          (le_of_lt M.hδmax)
      have hlip_step : hPot (pol.queue (t + 1) ω) (proc.S (t + 1) ω) -
          hPot (pol.queue t ω) (proc.S (t + 1) ω) ≤ C' * B ^ 2 := by
        have h1 := le_trans (le_abs_self _) (hhPot_lip (pol.queue (t + 1) ω) (pol.queue t ω) (proc.S (t + 1) ω))
        have h2 : C' * (B * Real.sqrt (∑ j, (pol.queue (t + 1) ω j - pol.queue t ω j) ^ 2)) ≤ C' * B ^ 2 := by
          have : B * Real.sqrt (∑ j, (pol.queue (t + 1) ω j - pol.queue t ω j) ^ 2) ≤ B * B :=
            mul_le_mul_of_nonneg_left hstep_norm (le_of_lt hB_pos)
          rw [sq]
          exact mul_le_mul_of_nonneg_left this (le_of_lt hC'_pos)
        exact le_trans h1 h2
      change (L_fn (pol.queue (t + 1) ω) - L_fn (pol.queue t ω)) ≤
        (M.r : ℝ) * M.δmax ^ 2 + ∑ j, pol.queue t ω j *
          (M.arrival (proc.S t ω) (pol.act t ω) j - M.service (proc.S t ω) (pol.act t ω) j) at hquad
      change hPot (pol.queue t ω) (proc.S t ω) -
        ∑ u, M.P (proc.S t ω) u * hPot (pol.queue t ω) u =
        M.dualState V (proc.S t ω) (pol.queue t ω) - M.dual V (pol.queue t ω) at hpois
      linarith [hB_sq]
    -- Integrability of every finite-history function
    have hint_Lh1 : Integrable (fun ω =>
        L_fn (pol.queue (t + 1) ω) + hPot (pol.queue (t + 1) ω) (proc.S (t + 1) ω)) μ := by
      have h := (integral_history_eq_sum proc (t + 1) (fun h2 =>
        L_fn (bpQueueHist M choice (t + 1) (fun i => h2 i.castSucc)) +
        hPot (bpQueueHist M choice (t + 1) (fun i => h2 i.castSucc)) (h2 (Fin.last (t + 1))))).1
      simpa [hq1_hist] using h
    have hint_Lh0 : Integrable (fun ω =>
        L_fn (pol.queue t ω) + hPot (pol.queue t ω) (proc.S t ω)) μ := by
      have h := (integral_history_eq_sum proc t (fun h1 =>
        L_fn (bpQueueHist M choice t (fun i => h1 i.castSucc)) +
        hPot (bpQueueHist M choice t (fun i => h1 i.castSucc)) (h1 (Fin.last t)))).1
      simpa [hq_hist] using h
    have hint_cost : Integrable (fun ω => V * M.cost (proc.S t ω) (pol.act t ω)) μ :=
      (pol_integrable_cost pol t).const_mul V
    have hint_dual : Integrable (fun ω => M.dual V (pol.queue t ω)) μ := by
      have h := (integral_history_eq_sum proc t (fun h1 =>
        M.dual V (bpQueueHist M choice t (fun i => h1 i.castSucc)))).1
      simpa [hq_hist] using h
    have hint_mart1 : Integrable (fun ω => hPot (pol.queue t ω) (proc.S (t + 1) ω)) μ := by
      have h := (integral_history_eq_sum proc (t + 1) (fun h2 =>
        hPot (bpQueueHist M choice t (fun i => h2 i.castSucc.castSucc)) (h2 (Fin.last (t + 1))))).1
      simpa [hq_hist] using h
    have hint_mart2 : Integrable (fun ω => ∑ u : M.State, M.P (proc.S t ω) u * hPot (pol.queue t ω) u) μ := by
      have h := (integral_history_eq_sum proc t (fun h1 =>
        ∑ u : M.State, M.P (h1 (Fin.last t)) u *
          hPot (bpQueueHist M choice t (fun i => h1 i.castSucc)) u)).1
      simpa [hq_hist] using h
    -- The martingale difference has zero expectation by the Markov tower property!
    have hmart_zero : ∫ ω, (hPot (pol.queue t ω) (proc.S (t + 1) ω) -
        ∑ u : M.State, M.P (proc.S t ω) u * hPot (pol.queue t ω) u) ∂μ = 0 := by
      rw [integral_sub hint_mart1 hint_mart2]
      have htw := integral_history_next_eq proc t
        (fun h1 u => hPot (bpQueueHist M choice t (fun i => h1 i.castSucc)) u)
      have htw' : ∫ ω, hPot (pol.queue t ω) (proc.S (t + 1) ω) ∂μ =
          ∫ ω, (∑ u : M.State, M.P (proc.S t ω) u * hPot (pol.queue t ω) u) ∂μ := by
        simpa [hq_hist] using htw
      linarith
    have hint_sub : Integrable (fun ω =>
        (L_fn (pol.queue (t + 1) ω) + hPot (pol.queue (t + 1) ω) (proc.S (t + 1) ω)) -
        (L_fn (pol.queue t ω) + hPot (pol.queue t ω) (proc.S t ω))) μ := hint_Lh1.sub hint_Lh0
    have hint_rhs1 : Integrable (fun ω => (1 + C') * B ^ 2 + M.dual V (pol.queue t ω)) μ :=
      (integrable_const ((1 + C') * B ^ 2)).add hint_dual
    have hint_mart : Integrable (fun ω => hPot (pol.queue t ω) (proc.S (t + 1) ω) -
        ∑ u : M.State, M.P (proc.S t ω) u * hPot (pol.queue t ω) u) μ := hint_mart1.sub hint_mart2
    have hmono := integral_mono (hint_sub.add hint_cost) (hint_rhs1.add hint_mart) hpt
    dsimp only [Pi.add_apply] at hmono
    rw [integral_add hint_sub hint_cost, integral_sub hint_Lh1 hint_Lh0,
      integral_const_mul, integral_add hint_rhs1 hint_mart,
      integral_add (integrable_const _) hint_dual, hmart_zero, add_zero,
      integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] at hmono
    exact hmono
  -- Telescope from `0` to `T - 1`
  let K_V : ℝ := (1 / 2 : ℝ) * (C' * B) ^ 2 + 2 * C' * V * M.δmax
  have hK_V_nonneg : 0 ≤ K_V :=
    add_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hC'_pos)) (le_of_lt hV_pos))
        (le_of_lt M.hδmax))
  have htele_bp : ∀ T : ℕ,
      V * (∑ t ∈ Finset.range T, ∫ ω, M.cost (proc.S t ω) (pol.act t ω) ∂μ) ≤
        K_V + (T : ℝ) * ((1 + C') * B ^ 2) + ∑ t ∈ Finset.range T, ∫ ω, M.dual V (pol.queue t ω) ∂μ := by
    intro T
    let Φ : ℕ → ℝ := fun t => ∫ ω, (L_fn (pol.queue t ω) + hPot (pol.queue t ω) (proc.S t ω)) ∂μ
    have hsum := Finset.sum_le_sum (s := Finset.range T) (fun t _ => hstep_exp t)
    have hLHS : ∑ t ∈ Finset.range T,
        (Φ (t + 1) - Φ t + V * ∫ ω, M.cost (proc.S t ω) (pol.act t ω) ∂μ) =
        Φ T - Φ 0 + V * ∑ t ∈ Finset.range T, ∫ ω, M.cost (proc.S t ω) (pol.act t ω) ∂μ := by
      rw [Finset.sum_add_distrib, Finset.sum_range_sub Φ T, ← Finset.mul_sum]
    have hRHS : ∑ t ∈ Finset.range T, ((1 + C') * B ^ 2 + ∫ ω, M.dual V (pol.queue t ω) ∂μ) =
        (T : ℝ) * ((1 + C') * B ^ 2) + ∑ t ∈ Finset.range T, ∫ ω, M.dual V (pol.queue t ω) ∂μ := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hΦT_ge : -(1 / 2 : ℝ) * (C' * B) ^ 2 - C' * V * M.δmax ≤ Φ T := by
      have hintT : Integrable (fun ω => L_fn (pol.queue T ω) + hPot (pol.queue T ω) (proc.S T ω)) μ := by
        have h := (integral_history_eq_sum proc T (fun h1 =>
          L_fn (bpQueueHist M choice T (fun i => h1 i.castSucc)) +
          hPot (bpQueueHist M choice T (fun i => h1 i.castSucc)) (h1 (Fin.last T)))).1
        simpa [bp_queue_eq_hist hchoice_act T] using h
      have hle := integral_mono (integrable_const _) hintT (fun ω => hLh_lower (pol.queue T ω) (proc.S T ω))
      simpa [Φ, integral_const, measureReal_def, measure_univ] using hle
    have hΦ0_le : Φ 0 ≤ C' * V * M.δmax := by
      have hint0 : Integrable (fun ω => L_fn (pol.queue 0 ω) + hPot (pol.queue 0 ω) (proc.S 0 ω)) μ := by
        have h := (integral_history_eq_sum proc 0 (fun h1 =>
          L_fn (fun _ => 0) + hPot (fun _ => 0) (h1 (Fin.last 0)))).1
        simpa [NetworkModel.Policy.queue] using h
      have hpt0 : ∀ ω, L_fn (pol.queue 0 ω) + hPot (pol.queue 0 ω) (proc.S 0 ω) ≤ C' * V * M.δmax := by
        intro ω
        have hL0 : L_fn (pol.queue 0 ω) = 0 := by simp [L_fn, NetworkModel.Policy.queue]
        have hh0 := le_trans (le_abs_self _) (hhPot_abs (pol.queue 0 ω) (proc.S 0 ω))
        have hq0 : Real.sqrt (∑ j : Fin M.r, (pol.queue 0 ω j) ^ 2) = 0 := by
          simp [NetworkModel.Policy.queue]
        rw [hq0, mul_zero, add_zero] at hh0
        linarith
      have hle := integral_mono hint0 (integrable_const _) hpt0
      simpa [Φ, integral_const, measureReal_def, measure_univ] using hle
    dsimp [K_V]
    linarith [hsum, hLHS, hRHS, hΦT_ge, hΦ0_le]
  -- Conclusion 4 & 1: `O(V)` average backlog bound and queue stability
  have hbacklog : pol.avgBacklog ≤ ((C_q0 + C_q1 * V : ℝ) : EReal) := by
    have hT_bound : ∀ T : ℕ, 0 < T →
        ((1 : ℝ) / (T : ℝ)) * ∑ t ∈ Finset.range T, ∑ j : Fin M.r, ∫ ω, pol.queue t ω j ∂μ ≤
          C_q0 + C_q1 * V + K_V / (η * (T : ℝ)) := by
      intro T hT
      have hT_pos : (0 : ℝ) < (T : ℝ) := Nat.cast_pos.mpr hT
      have hcost_nonneg : 0 ≤ V * ∑ t ∈ Finset.range T, ∫ ω, M.cost (proc.S t ω) (pol.act t ω) ∂μ :=
        mul_nonneg (le_of_lt hV_pos) (Finset.sum_nonneg (fun t _ =>
          integral_nonneg (fun ω => M.cost_nonneg _ _)))
      have hdual_le : ∀ t : ℕ, ∫ ω, M.dual V (pol.queue t ω) ∂μ ≤
          V * M.δmax - η * ∑ j : Fin M.r, ∫ ω, pol.queue t ω j ∂μ := by
        intro t
        have hint_dual : Integrable (fun ω => M.dual V (pol.queue t ω)) μ := by
          have h := (integral_history_eq_sum proc t (fun h1 =>
            M.dual V (bpQueueHist M choice t (fun i => h1 i.castSucc)))).1
          simpa [bp_queue_eq_hist hchoice_act t] using h
        have hint_sum : Integrable (fun ω => ∑ j : Fin M.r, pol.queue t ω j) μ :=
          integrable_finsetSum _ (fun j _ => pol_integrable_queue pol t j)
        have hle := integral_mono hint_dual ((integrable_const (V * M.δmax)).sub (hint_sum.const_mul η))
          (fun ω => dual_le_of_slackness hslack (le_of_lt hV_pos) (pol_queue_nonneg pol t ω))
        dsimp only [Pi.sub_apply] at hle
        rw [integral_sub (integrable_const _) (hint_sum.const_mul η),
          integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul,
          integral_const_mul, integral_finsetSum _ (fun j _ => pol_integrable_queue pol t j)] at hle
        exact hle
      have hsum_dual := Finset.sum_le_sum (s := Finset.range T) (fun t _ => hdual_le t)
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum] at hsum_dual
      have hη_sum : η * ∑ t ∈ Finset.range T, ∑ j : Fin M.r, ∫ ω, pol.queue t ω j ∂μ ≤
          K_V + (T : ℝ) * ((1 + C') * B ^ 2 + V * M.δmax) := by
        linarith [htele_bp T, hcost_nonneg, hsum_dual]
      have hdiv := div_le_div_of_nonneg_right hη_sum (le_of_lt (mul_pos hη_pos hT_pos))
      have hLHS_eq : (η * ∑ t ∈ Finset.range T, ∑ j : Fin M.r, ∫ ω, pol.queue t ω j ∂μ) / (η * (T : ℝ)) =
          ((1 : ℝ) / (T : ℝ)) * ∑ t ∈ Finset.range T, ∑ j : Fin M.r, ∫ ω, pol.queue t ω j ∂μ := by
        field_simp [hη_pos.ne', hT_pos.ne']
      have hRHS_eq : (K_V + (T : ℝ) * ((1 + C') * B ^ 2 + V * M.δmax)) / (η * (T : ℝ)) =
          C_q0 + C_q1 * V + K_V / (η * (T : ℝ)) := by
        dsimp [C_q0, C_q1]
        field_simp [hη_pos.ne', hT_pos.ne']
        ring
      linarith [hdiv, hLHS_eq, hRHS_eq]
    -- Take `limsup` as `T → ∞` using `K_V / (η * T) → 0`
    have hlim_rhs : Filter.Tendsto
        (fun T : ℕ => ((C_q0 + C_q1 * V + K_V / (η * (T : ℝ)) : ℝ) : EReal))
        Filter.atTop (nhds ((C_q0 + C_q1 * V : ℝ) : EReal)) := by
      have h0 : Filter.Tendsto (fun T : ℕ => K_V / (η * (T : ℝ))) Filter.atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop
          (Filter.Tendsto.const_mul_atTop hη_pos tendsto_natCast_atTop_atTop)
      have hreal : Filter.Tendsto (fun T : ℕ => C_q0 + C_q1 * V + K_V / (η * (T : ℝ)))
          Filter.atTop (nhds (C_q0 + C_q1 * V)) := by
        simpa [add_zero] using tendsto_const_nhds.add h0
      exact (EReal.continuous_coe_iff.mpr continuous_id).continuousAt.tendsto.comp hreal
    rw [← hlim_rhs.limsup_eq]
    refine Filter.limsup_le_limsup ?_ (by isBoundedDefault) (by isBoundedDefault)
    filter_upwards [Filter.eventually_ge_atTop 1] with T hT
    exact EReal.coe_le_coe_iff.mpr (hT_bound T (lt_of_lt_of_le Nat.zero_lt_one hT))
  have hstab : pol.IsStable := lt_of_le_of_lt hbacklog (EReal.coe_lt_top _)
  -- Conclusion 2: `M.optCost proc ≤ pol.avgCost`
  have hopt_le : M.optCost proc ≤ pol.avgCost := by
    unfold NetworkModel.optCost
    exact iInf₂_le pol hstab
  -- Show `M.optCost proc` is a finite real `fstar`
  have hopt_ge_zero : (0 : EReal) ≤ M.optCost proc := by
    unfold NetworkModel.optCost
    refine le_iInf₂ (fun pol_any _ => ?_)
    have h0 : Filter.limsup (fun _ : ℕ => (0 : EReal)) Filter.atTop = 0 := by
      simp [Filter.limsup_const]
    rw [← h0]
    refine Filter.limsup_le_limsup ?_ (by isBoundedDefault) (by isBoundedDefault)
    filter_upwards with t
    apply EReal.coe_le_coe_iff.mpr
    exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun τ _ =>
      integral_nonneg (fun ω => M.cost_nonneg _ _)))
  have havgCost_le_δ : pol.avgCost ≤ (M.δmax : EReal) := by
    refine Filter.limsup_le_of_le (by isBoundedDefault) ?_
    filter_upwards with t
    apply EReal.coe_le_coe_iff.mpr
    cases t with
    | zero => simp [le_of_lt M.hδmax]
    | succ n =>
      have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
      have hsum : ∑ τ ∈ Finset.range (n + 1), ∫ ω, M.cost (proc.S τ ω) (pol.act τ ω) ∂μ ≤
          ((n + 1 : ℕ) : ℝ) * M.δmax := by
        calc _ ≤ ∑ _τ ∈ Finset.range (n + 1), M.δmax := by
              refine Finset.sum_le_sum (fun τ _ => ?_)
              have hle := integral_mono (pol_integrable_cost pol τ) (integrable_const M.δmax)
                (fun ω => M.cost_le _ _)
              simpa [integral_const, measureReal_def, measure_univ] using hle
          _ = ((n + 1 : ℕ) : ℝ) * M.δmax := by simp
      rw [one_mul, inv_mul_le_iff₀ hpos]
      linarith
  have hopt_lt_top : M.optCost proc < ⊤ :=
    lt_of_le_of_lt (le_trans hopt_le havgCost_le_δ) (EReal.coe_lt_top _)
  obtain ⟨fstar, hfstar⟩ : ∃ fstar : ℝ, M.optCost proc = (fstar : EReal) := by
    cases hval : M.optCost proc with
    | bot => exact absurd (hval ▸ hopt_ge_zero) (by simp)
    | top => exact absurd hval (ne_of_lt hopt_lt_top)
    | coe x => exact ⟨x, rfl⟩
  -- Weak duality: `∀ q ⪰ 0, M.dual V q ≤ V * fstar`
  have hweak : ∀ q : Fin M.r → ℝ, (∀ j, 0 ≤ q j) → M.dual V q ≤ V * fstar := by
    intro q hq
    have hle_opt : ((M.dual V q / V : ℝ) : EReal) ≤ M.optCost proc := by
      unfold NetworkModel.optCost
      exact le_iInf₂ (fun pol_any hst =>
        dual_div_V_le_avgCost proc hC_mix (le_of_lt hρ0) hρ1 hmix hV pol_any hst q hq)
    rw [hfstar, EReal.coe_le_coe_iff] at hle_opt
    linarith [(div_le_iff₀ hV_pos).mp hle_opt]
  -- Conclusion 3: `pol.avgCost ≤ M.optCost proc + C_cost / V`
  have hcost_opt : pol.avgCost ≤ M.optCost proc + ((C_cost / V : ℝ) : EReal) := by
    rw [hfstar, ← EReal.coe_add]
    have hT_cost : ∀ T : ℕ, 0 < T →
        ((1 : ℝ) / (T : ℝ)) * ∑ t ∈ Finset.range T, ∫ ω, M.cost (proc.S t ω) (pol.act t ω) ∂μ ≤
          fstar + C_cost / V + K_V / (V * (T : ℝ)) := by
      intro T hT
      have hT_pos : (0 : ℝ) < (T : ℝ) := Nat.cast_pos.mpr hT
      have hdual_fstar : ∀ t : ℕ, ∫ ω, M.dual V (pol.queue t ω) ∂μ ≤ V * fstar := by
        intro t
        have hint_dual : Integrable (fun ω => M.dual V (pol.queue t ω)) μ := by
          have h := (integral_history_eq_sum proc t (fun h1 =>
            M.dual V (bpQueueHist M choice t (fun i => h1 i.castSucc)))).1
          simpa [bp_queue_eq_hist hchoice_act t] using h
        have hle := integral_mono hint_dual (integrable_const (V * fstar))
          (fun ω => hweak (pol.queue t ω) (pol_queue_nonneg pol t ω))
        simpa [integral_const, measureReal_def, measure_univ] using hle
      have hsum_dual : ∑ t ∈ Finset.range T, ∫ ω, M.dual V (pol.queue t ω) ∂μ ≤ (T : ℝ) * (V * fstar) := by
        calc _ ≤ ∑ _t ∈ Finset.range T, (V * fstar) := Finset.sum_le_sum (fun t _ => hdual_fstar t)
          _ = (T : ℝ) * (V * fstar) := by simp
      have h1 : V * ∑ t ∈ Finset.range T, ∫ ω, M.cost (proc.S t ω) (pol.act t ω) ∂μ ≤
          K_V + (T : ℝ) * C_cost + (T : ℝ) * (V * fstar) := by
        dsimp [C_cost]; linarith [htele_bp T, hsum_dual]
      have hdiv := div_le_div_of_nonneg_right h1 (le_of_lt (mul_pos hV_pos hT_pos))
      have hLHS_eq : (V * ∑ t ∈ Finset.range T, ∫ ω, M.cost (proc.S t ω) (pol.act t ω) ∂μ) / (V * (T : ℝ)) =
          ((1 : ℝ) / (T : ℝ)) * ∑ t ∈ Finset.range T, ∫ ω, M.cost (proc.S t ω) (pol.act t ω) ∂μ := by
        field_simp [hV_pos.ne', hT_pos.ne']
      have hRHS_eq : (K_V + (T : ℝ) * C_cost + (T : ℝ) * (V * fstar)) / (V * (T : ℝ)) =
          fstar + C_cost / V + K_V / (V * (T : ℝ)) := by
        field_simp [hV_pos.ne', hT_pos.ne']
        ring
      linarith [hdiv, hLHS_eq, hRHS_eq]
    have hlim_rhs : Filter.Tendsto
        (fun T : ℕ => ((fstar + C_cost / V + K_V / (V * (T : ℝ)) : ℝ) : EReal))
        Filter.atTop (nhds ((fstar + C_cost / V : ℝ) : EReal)) := by
      have h0 : Filter.Tendsto (fun T : ℕ => K_V / (V * (T : ℝ))) Filter.atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop
          (Filter.Tendsto.const_mul_atTop hV_pos tendsto_natCast_atTop_atTop)
      have hreal : Filter.Tendsto (fun T : ℕ => fstar + C_cost / V + K_V / (V * (T : ℝ)))
          Filter.atTop (nhds (fstar + C_cost / V)) := by
        simpa [add_zero] using tendsto_const_nhds.add h0
      exact (EReal.continuous_coe_iff.mpr continuous_id).continuousAt.tendsto.comp hreal
    rw [← hlim_rhs.limsup_eq]
    refine Filter.limsup_le_limsup ?_ (by isBoundedDefault) (by isBoundedDefault)
    filter_upwards [Filter.eventually_ge_atTop 1] with T hT
    exact EReal.coe_le_coe_iff.mpr (hT_cost T (lt_of_lt_of_le Nat.zero_lt_one hT))
  exact ⟨hstab, hopt_le, hcost_opt, hbacklog⟩

end LifoBackpressure.Proofs
