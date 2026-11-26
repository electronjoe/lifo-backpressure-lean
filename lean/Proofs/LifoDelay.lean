import Statements.LifoDelay

/-!
# Proof of Theorem 4 (`thm:qlalifo_delay`): LIFO-Backpressure Throughput and `O([log V]^2)` Delay

Separable proof of `LifoBackpressure.Statements.Theorem4Statement` taking
`Theorem1Statement`, `Theorem2Statement`, and `Theorem3Statement` as explicit hypotheses
(composed automatically by `Assembly.lean`), following Section VI-C of `arXiv:1008.4895v2`
(lines 635–666) and `lamport/thm-qlalifo-delay.md`.
-/

namespace LifoBackpressure.Proofs

open Filter MeasureTheory Classical
open LifoBackpressure.Statements

/-! ### Queue regularity helpers -/

private lemma queue_nonneg {M : NetworkModel} {Ω : Type} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {proc : M.MarkovProcess Ω μ}
    (pol : M.Policy proc) (τ : ℕ) (ω : Ω) (j : Fin M.r) :
    0 ≤ pol.queue τ ω j := by
  induction τ with
  | zero => exact le_rfl
  | succ t _ =>
    change 0 ≤ max (pol.queue t ω j - M.service (proc.S t ω) (pol.act t ω) j) 0 +
      M.arrival (proc.S t ω) (pol.act t ω) j
    exact add_nonneg (le_max_right _ _) (M.arrival_nonneg _ _ _)

private lemma queue_le_mul_δmax {M : NetworkModel} {Ω : Type} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {proc : M.MarkovProcess Ω μ}
    (pol : M.Policy proc) (τ : ℕ) (ω : Ω) (j : Fin M.r) :
    pol.queue τ ω j ≤ (τ : ℝ) * M.δmax := by
  induction τ with
  | zero => simp [NetworkModel.Policy.queue]
  | succ t ih =>
    change max (pol.queue t ω j - M.service (proc.S t ω) (pol.act t ω) j) 0 +
      M.arrival (proc.S t ω) (pol.act t ω) j ≤ ((t + 1 : ℕ) : ℝ) * M.δmax
    have hq0 : 0 ≤ pol.queue t ω j := queue_nonneg pol t ω j
    have hserv : 0 ≤ M.service (proc.S t ω) (pol.act t ω) j := M.service_nonneg _ _ _
    have hmax : max (pol.queue t ω j - M.service (proc.S t ω) (pol.act t ω) j) 0 ≤ pol.queue t ω j :=
      max_le (by linarith) hq0
    have harr : M.arrival (proc.S t ω) (pol.act t ω) j ≤ M.δmax := M.arrival_le _ _ _
    push_cast
    linarith

private lemma measurable_queue {M : NetworkModel} {Ω : Type} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {proc : M.MarkovProcess Ω μ}
    (pol : M.Policy proc) (τ : ℕ) (j : Fin M.r) :
    Measurable (fun ω => pol.queue τ ω j) := by
  induction τ with
  | zero => exact measurable_const
  | succ t ih =>
    change Measurable (fun ω =>
      max (pol.queue t ω j - M.service (proc.S t ω) (pol.act t ω) j) 0 +
        M.arrival (proc.S t ω) (pol.act t ω) j)
    exact ((ih.sub (pol.measurable_service t j)).max measurable_const).add
      (pol.measurable_arrival t j)

private lemma integrable_queue {M : NetworkModel} {Ω : Type} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {proc : M.MarkovProcess Ω μ}
    (pol : M.Policy proc) (τ : ℕ) (j : Fin M.r) :
    Integrable (fun ω => pol.queue τ ω j) μ := by
  refine Integrable.of_bound (measurable_queue pol τ j).aestronglyMeasurable ((τ : ℝ) * M.δmax) ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (queue_nonneg pol τ ω j)]
  exact queue_le_mul_δmax pol τ ω j

/-! ### Step 1: Zero rate of never-departing packets via stability and monotone convergence -/

/-- Count of packets arriving strictly before `τ` that never depart. -/
private noncomputable def neverDepartCount {M : NetworkModel} {Ω : Type} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {proc : M.MarkovProcess Ω μ}
    {pol : M.Policy proc} {j : Fin M.r} {ι : Type}
    (Q : LifoQueueRealization pol j ι) (τ : ℕ) (ω : Ω) : ℕ :=
  ((Q.finite_arrivals ω τ).subset
    (fun k (hk : Q.arrival ω k < τ ∧ Q.depart ω k = ⊤) => hk.1)).toFinset.card

private lemma neverDepartCount_mono {M : NetworkModel} {Ω : Type} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {proc : M.MarkovProcess Ω μ}
    {pol : M.Policy proc} {j : Fin M.r} {ι : Type}
    (Q : LifoQueueRealization pol j ι) (ω : Ω) :
    Monotone (fun τ => neverDepartCount Q τ ω) := by
  intro τ₁ τ₂ hle
  unfold neverDepartCount
  apply Finset.card_le_card
  intro k hk
  rcases (Set.Finite.mem_toFinset _).mp hk with ⟨h1, h2⟩
  exact (Set.Finite.mem_toFinset _).mpr ⟨lt_of_lt_of_le h1 hle, h2⟩

/-- Lamport Step 1.3: Finite expected average backlog implies almost surely only finitely many
packets ever fail to depart. -/
private lemma ae_neverDepartCount_bdd {M : NetworkModel} {Ω : Type} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {proc : M.MarkovProcess Ω μ}
    {pol : M.Policy proc} {j : Fin M.r} {ι : Type}
    (Q : LifoQueueRealization pol j ι) (hstab : pol.IsStable) :
    ∀ᵐ ω ∂μ, ∃ B : ℝ, ∀ τ : ℕ, (neverDepartCount Q τ ω : ℝ) ≤ B := by
  unfold NetworkModel.Policy.IsStable NetworkModel.Policy.avgBacklog at hstab
  -- Extract a finite real upper bound `C` on the `limsup`
  have hlt_top : Filter.limsup
      (fun t : ℕ => (((1 : ℝ) / (t : ℝ)) *
        ∑ τ ∈ Finset.range t, ∑ j' : Fin M.r, ∫ ω, pol.queue τ ω j' ∂μ : EReal))
      Filter.atTop < ⊤ := hstab
  obtain ⟨C, hC_lt⟩ : ∃ C : ℝ, 0 ≤ C ∧ Filter.limsup
      (fun t : ℕ => (((1 : ℝ) / (t : ℝ)) *
        ∑ τ ∈ Finset.range t, ∑ j' : Fin M.r, ∫ ω, pol.queue τ ω j' ∂μ : EReal))
      Filter.atTop < (C : EReal) := by
    cases hval : Filter.limsup
        (fun t : ℕ => (((1 : ℝ) / (t : ℝ)) *
          ∑ τ ∈ Finset.range t, ∑ j' : Fin M.r, ∫ ω, pol.queue τ ω j' ∂μ : EReal))
        Filter.atTop with
    | bot => exact ⟨1, zero_le_one, EReal.bot_lt_coe 1⟩
    | top => exact absurd hval (ne_of_lt hlt_top)
    | coe x =>
      refine ⟨max x 0 + 1, by linarith [le_max_right x 0], ?_⟩
      exact EReal.coe_lt_coe_iff.mpr (by linarith [le_max_left x 0])
  have hev_avg : ∀ᶠ t : ℕ in Filter.atTop,
      ((1 : ℝ) / (t : ℝ)) *
        ∑ τ ∈ Finset.range t, ∑ j' : Fin M.r, ∫ ω, pol.queue τ ω j' ∂μ < C := by
    have h := Filter.eventually_lt_of_limsup_lt hC_lt.2
    filter_upwards [h] with t ht
    exact EReal.coe_lt_coe_iff.mp ht
  rw [Filter.eventually_atTop] at hev_avg
  obtain ⟨t₀, ht₀⟩ := hev_avg
  -- Uniform bound on `∫ ω, neverDepartCount Q M₀ ω ∂μ ≤ 2 * C` for all `M₀`
  have h_int_bdd : ∀ M₀ : ℕ, ∫ ω, (neverDepartCount Q M₀ ω : ℝ) ∂μ ≤ 2 * C := by
    intro M₀
    let t : ℕ := max (2 * M₀) (max t₀ 1)
    have ht_ge_t0 : t₀ ≤ t := le_trans (le_max_left t₀ 1) (le_max_right _ _)
    have ht_ge_1 : 1 ≤ t := le_trans (le_max_right t₀ 1) (le_max_right _ _)
    have ht_ge_2M : 2 * M₀ ≤ t := le_max_left _ _
    have ht_pos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one ht_ge_1)
    have hsum_lt : ∑ τ ∈ Finset.range t, ∑ j' : Fin M.r, ∫ ω, pol.queue τ ω j' ∂μ ≤ C * (t : ℝ) := by
      have h1 := ht₀ t ht_ge_t0
      have h2 : (1 / (t : ℝ)) *
          ∑ τ ∈ Finset.range t, ∑ j' : Fin M.r, ∫ ω, pol.queue τ ω j' ∂μ ≤ C := le_of_lt h1
      rw [one_div, inv_mul_le_iff₀ ht_pos] at h2
      linarith
    have h_int_nd : ∀ τ : ℕ, Integrable (fun ω => (neverDepartCount Q τ ω : ℝ)) μ := by
      intro τ
      refine Integrable.of_bound (Q.measurable_never_depart τ).aestronglyMeasurable ((τ : ℝ) * M.δmax) ?_
      filter_upwards with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
      exact le_trans (Q.never_depart_le_queue ω τ) (queue_le_mul_δmax pol τ ω j)
    have h_term_le : ∀ τ : ℕ, M₀ ≤ τ →
        ∫ ω, (neverDepartCount Q M₀ ω : ℝ) ∂μ ≤
          ∑ j' : Fin M.r, ∫ ω, pol.queue τ ω j' ∂μ := by
      intro τ hτ
      have h1 : ∫ ω, (neverDepartCount Q M₀ ω : ℝ) ∂μ ≤ ∫ ω, pol.queue τ ω j ∂μ := by
        refine integral_mono (h_int_nd M₀) (integrable_queue pol τ j) (fun ω => ?_)
        have hmono : (neverDepartCount Q M₀ ω : ℝ) ≤ (neverDepartCount Q τ ω : ℝ) := by
          exact_mod_cast neverDepartCount_mono Q ω hτ
        exact le_trans hmono (Q.never_depart_le_queue ω τ)
      have h2 : ∫ ω, pol.queue τ ω j ∂μ ≤ ∑ j' : Fin M.r, ∫ ω, pol.queue τ ω j' ∂μ := by
        refine Finset.single_le_sum (f := fun j' => ∫ ω, pol.queue τ ω j' ∂μ) (fun j' _ => ?_) (Finset.mem_univ j)
        exact integral_nonneg (fun ω => queue_nonneg pol τ ω j')
      exact le_trans h1 h2
    have hIco_sub : Finset.Ico M₀ t ⊆ Finset.range t := by
      intro τ hτ
      rw [Finset.mem_Ico] at hτ
      rw [Finset.mem_range]
      exact hτ.2
    have hIco_le : ∑ τ ∈ Finset.Ico M₀ t, ∑ j' : Fin M.r, ∫ ω, pol.queue τ ω j' ∂μ ≤
        ∑ τ ∈ Finset.range t, ∑ j' : Fin M.r, ∫ ω, pol.queue τ ω j' ∂μ := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hIco_sub (fun τ _ _ => ?_)
      exact Finset.sum_nonneg (fun j' _ => integral_nonneg (fun ω => queue_nonneg pol τ ω j'))
    have h_lower : ((t - M₀ : ℕ) : ℝ) * (∫ ω, (neverDepartCount Q M₀ ω : ℝ) ∂μ) ≤
        ∑ τ ∈ Finset.Ico M₀ t, ∑ j' : Fin M.r, ∫ ω, pol.queue τ ω j' ∂μ := by
      calc ((t - M₀ : ℕ) : ℝ) * (∫ ω, (neverDepartCount Q M₀ ω : ℝ) ∂μ)
          = ∑ _τ ∈ Finset.Ico M₀ t, ∫ ω, (neverDepartCount Q M₀ ω : ℝ) ∂μ := by
              simp [Nat.card_Ico]
        _ ≤ ∑ τ ∈ Finset.Ico M₀ t, ∑ j' : Fin M.r, ∫ ω, pol.queue τ ω j' ∂μ := by
              exact Finset.sum_le_sum (fun τ hτ => h_term_le τ (Finset.mem_Ico.mp hτ).1)
    have h_diff_ge : (t : ℝ) / 2 ≤ ((t - M₀ : ℕ) : ℝ) := by
      have hle : M₀ ≤ t := by omega
      rw [Nat.cast_sub hle]
      have h2M : (2 : ℝ) * (M₀ : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht_ge_2M
      linarith
    have h_int_nonneg : 0 ≤ ∫ ω, (neverDepartCount Q M₀ ω : ℝ) ∂μ :=
      integral_nonneg (fun _ => Nat.cast_nonneg _)
    have h_mul : ((t : ℝ) / 2) * (∫ ω, (neverDepartCount Q M₀ ω : ℝ) ∂μ) ≤ C * (t : ℝ) :=
      le_trans (mul_le_mul_of_nonneg_right h_diff_ge h_int_nonneg) (le_trans h_lower (le_trans hIco_le hsum_lt))
    nlinarith
  -- Convert to `lintegral` and apply Monotone Convergence (`lintegral_iSup`)
  let f : ℕ → Ω → ENNReal := fun τ ω => ENNReal.ofReal (neverDepartCount Q τ ω : ℝ)
  have hf_meas : ∀ τ, Measurable (f τ) := fun τ =>
    ENNReal.measurable_ofReal.comp (Q.measurable_never_depart τ)
  have hf_mono : Monotone f := fun τ₁ τ₂ hle ω =>
    ENNReal.ofReal_le_ofReal (by exact_mod_cast neverDepartCount_mono Q ω hle)
  have h_lintegral_le : ∀ τ, ∫⁻ ω, f τ ω ∂μ ≤ ENNReal.ofReal (2 * C) := by
    intro τ
    have h_int : Integrable (fun ω => (neverDepartCount Q τ ω : ℝ)) μ := by
      refine Integrable.of_bound (Q.measurable_never_depart τ).aestronglyMeasurable ((τ : ℝ) * M.δmax) ?_
      filter_upwards with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
      exact le_trans (Q.never_depart_le_queue ω τ) (queue_le_mul_δmax pol τ ω j)
    rw [← ofReal_integral_eq_lintegral_ofReal h_int (Filter.Eventually.of_forall (fun _ => Nat.cast_nonneg _))]
    exact ENNReal.ofReal_le_ofReal (h_int_bdd τ)
  have h_iSup_lt_top : ∫⁻ ω, (⨆ τ, f τ ω) ∂μ < ⊤ := by
    rw [lintegral_iSup hf_meas hf_mono]
    exact lt_of_le_of_lt (iSup_le h_lintegral_le) ENNReal.ofReal_lt_top
  have hae_fin : ∀ᵐ ω ∂μ, (⨆ τ, f τ ω) < ⊤ :=
    ae_lt_top (Measurable.iSup hf_meas) h_iSup_lt_top.ne
  filter_upwards [hae_fin] with ω hω
  refine ⟨(⨆ τ, f τ ω).toReal, fun τ => ?_⟩
  have hle : f τ ω ≤ ⨆ τ', f τ' ω := le_iSup (fun τ' => f τ' ω) τ
  have h1 := ENNReal.toReal_mono hω.ne hle
  simpa [f, ENNReal.toReal_ofReal (Nat.cast_nonneg _)] using h1

/-- Relate the cardinality of all in-window arrivals before time `t` to the finite sum of
`M.arrival` over in-window slots `τ < t`. -/
private lemma card_inWindow_arrivals_eq {M : NetworkModel} {Ω : Type} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {proc : M.MarkovProcess Ω μ}
    {pol : M.Policy proc} {j : Fin M.r} {ι : Type}
    (Q : LifoQueueRealization pol j ι) (γstar_j D K V : ℝ) (ω : Ω) (t : ℕ) :
    (((Q.finite_arrivals ω t).subset
      (fun k (hk : Q.arrival ω k < t ∧ pol.queue (Q.arrival ω k) ω j ∈ backlogWindow γstar_j D K V) =>
        hk.1)).toFinset.card : ℝ) =
      ∑ τ ∈ Finset.range t,
        if pol.queue τ ω j ∈ backlogWindow γstar_j D K V
        then M.arrival (proc.S τ ω) (pol.act τ ω) j else 0 := by
  let S := ((Q.finite_arrivals ω t).subset
    (fun k (hk : Q.arrival ω k < t ∧ pol.queue (Q.arrival ω k) ω j ∈ backlogWindow γstar_j D K V) =>
      hk.1)).toFinset
  have hpart : (S.card : ℝ) = ∑ τ ∈ Finset.range t, ((S.filter (fun k => Q.arrival ω k = τ)).card : ℝ) := by
    have hnat : S.card = ∑ τ ∈ Finset.range t, (S.filter (fun k => Q.arrival ω k = τ)).card := by
      have := Finset.card_eq_sum_card_fiberwise (f := Q.arrival ω) (s := S) (t := Finset.range t)
        (fun k hk => by
          rw [Finset.mem_coe, Finset.mem_range]
          exact ((Set.Finite.mem_toFinset _).mp (Finset.mem_coe.mp hk)).1)
      exact this
    exact_mod_cast hnat
  rw [hpart]
  refine Finset.sum_congr rfl (fun τ hτ => ?_)
  have hτ_lt : τ < t := Finset.mem_range.mp hτ
  by_cases hwin : pol.queue τ ω j ∈ backlogWindow γstar_j D K V
  · rw [if_pos hwin, ← Q.arrivals_at_eq ω τ]
    congr 1
    apply congrArg Finset.card
    ext k
    rw [Finset.mem_filter]
    constructor
    · rintro ⟨_, hEq⟩
      exact (Set.Finite.mem_toFinset _).mpr hEq
    · intro hk
      have hEq := (Set.Finite.mem_toFinset _).mp hk
      change Q.arrival ω k = τ at hEq
      exact ⟨(Set.Finite.mem_toFinset _).mpr ⟨hEq ▸ hτ_lt, hEq ▸ hwin⟩, hEq⟩
  · rw [if_neg hwin]
    have hemp : S.filter (fun k => Q.arrival ω k = τ) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro k hk
      rw [Finset.mem_filter] at hk
      have hkS := (Set.Finite.mem_toFinset _).mp hk.1
      exact hwin (hk.2 ▸ hkS.2)
    simp [hemp]

/-! ### Step 3 helper: Tight buffer-slot set for Theorem 1 application in Part (b) -/

private noncomputable def tightBufferSlots (γstar_j D K V δmax : ℝ) : Finset ℕ :=
  Finset.Ico (Nat.ceil (max (qLow γstar_j D K V - δmax) 0))
    (Nat.ceil (qHigh γstar_j D K V + δmax))

private lemma card_tightBufferSlots_le {γstar_j D K V δmax : ℝ}
    (hγ : 0 ≤ γstar_j) (hD : 0 < D) (hK : 0 < K) (hδ : 0 < δmax) :
    ((tightBufferSlots γstar_j D K V δmax).card : ℝ) ≤
      2 * D + 2 * K * (Real.log V) ^ 2 + 2 * δmax + 1 := by
  unfold tightBufferSlots
  rw [Nat.card_Ico]
  set a : ℝ := max (qLow γstar_j D K V - δmax) 0
  set b : ℝ := qHigh γstar_j D K V + δmax
  have hb_nonneg : 0 ≤ b := by
    dsimp [b, qHigh]
    have hsq : 0 ≤ (Real.log V) ^ 2 := sq_nonneg _
    nlinarith
  by_cases hle : Nat.ceil b ≤ Nat.ceil a
  · rw [Nat.sub_eq_zero_of_le hle, Nat.cast_zero]
    have hsq : 0 ≤ (Real.log V) ^ 2 := sq_nonneg _
    nlinarith
  · push Not at hle
    rw [Nat.cast_sub (le_of_lt hle)]
    have hceil_b : (Nat.ceil b : ℝ) < b + 1 := Nat.ceil_lt_add_one hb_nonneg
    have hceil_a : a ≤ (Nat.ceil a : ℝ) := Nat.le_ceil a
    have hb_eq : b = γstar_j + D + K * (Real.log V) ^ 2 + δmax := rfl
    have ha_ge : γstar_j - D - K * (Real.log V) ^ 2 - δmax ≤ a := by
      dsimp [a, qLow]
      exact le_trans (sub_le_sub_right (le_max_left _ _) δmax) (le_max_left _ _)
    linarith

private noncomputable def tightWindowBufferSystem {M : NetworkModel} {Ω : Type} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {proc : M.MarkovProcess Ω μ}
    {pol : M.Policy proc} {j : Fin M.r} {ι : Type}
    (Q : LifoQueueRealization pol j ι) (γstar_j D K V : ℝ) (ω : Ω) :
    BufferSystem {b : ℕ // b ∈ tightBufferSlots γstar_j D K V M.δmax}
      {k : ι // k ∈ Q.windowDepartingSet γstar_j D K V ω} where
  arrival k := Q.arrival ω k.1
  depart k := Q.depart ω k.1
  slot k := ⟨Q.slot ω k.1, by
    rcases k.2 with ⟨hwin, _⟩
    have hsb := Q.slot_bounds ω k.1
    rw [tightBufferSlots, Finset.mem_Ico]
    constructor
    · rw [Nat.ceil_le]
      calc max (qLow γstar_j D K V - M.δmax) 0
          ≤ max (pol.queue (Q.arrival ω k.1) ω j - M.δmax) 0 :=
            max_le_max_right 0 (sub_le_sub_right hwin.1 M.δmax)
        _ ≤ (Q.slot ω k.1 : ℝ) := hsb.1
    · rw [Nat.lt_ceil]
      linarith [hsb.2, hwin.2]⟩
  arrival_le_depart k := Q.arrival_le_depart ω k.1
  finite_arrivals t :=
    (Q.finite_arrivals ω t).preimage (fun _ _ _ _ h => Subtype.ext h)
  disjoint_slots k₁ k₂ hne hsl τ :=
    Q.disjoint_slots ω k₁.1 k₂.1 (fun h => hne (Subtype.ext h)) (congrArg Subtype.val hsl) τ

private lemma tightWindowBufferSystem_avgDelay_eq {M : NetworkModel} {Ω : Type} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {proc : M.MarkovProcess Ω μ}
    {pol : M.Policy proc} {j : Fin M.r} {ι : Type}
    (Q : LifoQueueRealization pol j ι) (γstar_j D K V : ℝ) (ω : Ω) (t : ℕ) :
    (tightWindowBufferSystem Q γstar_j D K V ω).avgDelay t =
      (Q.windowBufferSystem γstar_j D K V ω).avgDelay t :=
  rfl

private lemma tightWindowBufferSystem_arrivalsCount_eq {M : NetworkModel} {Ω : Type} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {proc : M.MarkovProcess Ω μ}
    {pol : M.Policy proc} {j : Fin M.r} {ι : Type}
    (Q : LifoQueueRealization pol j ι) (γstar_j D K V : ℝ) (ω : Ω) (t : ℕ) :
    (tightWindowBufferSystem Q γstar_j D K V ω).arrivalsCount t =
      Q.windowDepartingArrivals γstar_j D K V ω t := by
  unfold BufferSystem.arrivalsCount LifoQueueRealization.windowDepartingArrivals
  refine Finset.card_bij (fun k _ => k.1) ?_ ?_ ?_
  · intro k hk
    have hk' := (Set.Finite.mem_toFinset _).mp hk
    exact (Set.Finite.mem_toFinset _).mpr ⟨hk', k.2⟩
  · intro k₁ _ k₂ _ h
    exact Subtype.ext h
  · intro b hb
    rcases (Set.Finite.mem_toFinset _).mp hb with ⟨hb1, hb2⟩
    exact ⟨⟨b, hb2⟩, (Set.Finite.mem_toFinset _).mpr hb1, rfl⟩

/-! ### Main Theorem 4 proof -/

/-- Separable proof of Theorem 4 (`thm:qlalifo_delay`), taking Theorems 1, 2, and 3 as explicit
hypotheses (composed automatically by `Assembly.lean`). -/
theorem theorem4
    (h1 : Theorem1Statement)
    (h2 : Theorem2Statement)
    (h3 : Theorem3Statement) :
    Theorem4Statement := by
  intro M η L hslack hL
  obtain ⟨D, K, cstar, hD, hK, hcstar, h3_body⟩ := h3 M η L hslack hL
  refine ⟨D, K, cstar, hD, hK, hcstar, ?_⟩
  intro V hV γstar huniq hpoly Ω _ μ _ proc pol hbp j ι Q lamJ lamTilde hlamJ h_arr_t h_win_t
  -- Obtain queue stability from Theorem 2
  obtain ⟨C_cost, C_q0, C_q1, _, _, _, h2_body⟩ := h2 M η hslack
  have hstab : pol.IsStable := (h2_body V hV Ω μ proc pol hbp).1
  -- Step 1: Rate of in-window eventually-departing packets equals `lamTilde` a.s.
  have h_part_a1 : ∀ᵐ ω ∂μ, Filter.Tendsto
      (fun t : ℕ => ((Q.windowDepartingArrivals (γstar j) D K V ω t : ℝ) / (t : ℝ)))
      Filter.atTop (nhds lamTilde) := by
    filter_upwards [h_win_t, ae_neverDepartCount_bdd Q hstab] with ω hω_win ⟨B_ω, hB_ω⟩
    have h_sub_tendsto : Filter.Tendsto
        (fun t : ℕ => ((1 : ℝ) / (t : ℝ)) *
          (∑ τ ∈ Finset.range t,
            if pol.queue τ ω j ∈ backlogWindow (γstar j) D K V
            then M.arrival (proc.S τ ω) (pol.act τ ω) j else 0) - B_ω / (t : ℝ))
        Filter.atTop (nhds lamTilde) := by
      have h0 : Filter.Tendsto (fun t : ℕ => B_ω / (t : ℝ)) Filter.atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
      simpa [sub_zero] using hω_win.sub h0
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h_sub_tendsto hω_win ?_ ?_
    · filter_upwards [Filter.eventually_ge_atTop 1] with t ht
      have ht_pos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one ht)
      let W_all := ((Q.finite_arrivals ω t).subset
        (fun k (hk : Q.arrival ω k < t ∧ pol.queue (Q.arrival ω k) ω j ∈ backlogWindow (γstar j) D K V) =>
          hk.1)).toFinset
      let W_dep := ((Q.finite_arrivals ω t).subset
        (fun k (hk : Q.arrival ω k < t ∧ k ∈ Q.windowDepartingSet (γstar j) D K V ω) =>
          hk.1)).toFinset
      let N_inf := ((Q.finite_arrivals ω t).subset
        (fun k (hk : Q.arrival ω k < t ∧ Q.depart ω k = ⊤) => hk.1)).toFinset
      have hsub : W_all ⊆ W_dep ∪ N_inf := by
        intro k hk
        rcases (Set.Finite.mem_toFinset _).mp hk with ⟨hk1, hk2⟩
        rw [Finset.mem_union]
        by_cases htop : Q.depart ω k = ⊤
        · exact Or.inr ((Set.Finite.mem_toFinset _).mpr ⟨hk1, htop⟩)
        · exact Or.inl ((Set.Finite.mem_toFinset _).mpr ⟨hk1, hk2, htop⟩)
      have hcard_nat : W_all.card ≤ W_dep.card + N_inf.card :=
        le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
      have hcard_real : (W_all.card : ℝ) ≤ (Q.windowDepartingArrivals (γstar j) D K V ω t : ℝ) +
          (neverDepartCount Q t ω : ℝ) := by
        exact_mod_cast hcard_nat
      have hsum_eq : (W_all.card : ℝ) = ∑ τ ∈ Finset.range t,
          if pol.queue τ ω j ∈ backlogWindow (γstar j) D K V
          then M.arrival (proc.S τ ω) (pol.act τ ω) j else 0 :=
        card_inWindow_arrivals_eq Q (γstar j) D K V ω t
      have hB : (neverDepartCount Q t ω : ℝ) ≤ B_ω := hB_ω t
      have hnum : (W_all.card : ℝ) - B_ω ≤ (Q.windowDepartingArrivals (γstar j) D K V ω t : ℝ) := by
        linarith
      rw [← hsum_eq, one_div, inv_mul_eq_div, ← sub_div]
      exact div_le_div_of_nonneg_right hnum (le_of_lt ht_pos)
    · filter_upwards [Filter.eventually_ge_atTop 1] with t ht
      have ht_pos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one ht)
      let W_all := ((Q.finite_arrivals ω t).subset
        (fun k (hk : Q.arrival ω k < t ∧ pol.queue (Q.arrival ω k) ω j ∈ backlogWindow (γstar j) D K V) =>
          hk.1)).toFinset
      let W_dep := ((Q.finite_arrivals ω t).subset
        (fun k (hk : Q.arrival ω k < t ∧ k ∈ Q.windowDepartingSet (γstar j) D K V ω) =>
          hk.1)).toFinset
      have hsub : W_dep ⊆ W_all := by
        intro k hk
        rcases (Set.Finite.mem_toFinset _).mp hk with ⟨hk1, hk2⟩
        exact (Set.Finite.mem_toFinset _).mpr ⟨hk1, hk2.1⟩
      have hcard_real : (Q.windowDepartingArrivals (γstar j) D K V ω t : ℝ) ≤ (W_all.card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      have hsum_eq := card_inWindow_arrivals_eq Q (γstar j) D K V ω t
      rw [← hsum_eq, one_div, inv_mul_eq_div]
      exact div_le_div_of_nonneg_right hcard_real (le_of_lt ht_pos)
  -- Step 2.1: `0 ≤ lamTilde` and `lamTilde ≤ lamJ`
  have h_bounds_lam : 0 ≤ lamTilde ∧ lamTilde ≤ lamJ := by
    obtain ⟨ω, hω_arr, hω_win⟩ := (h_arr_t.and h_win_t).exists
    constructor
    · refine ge_of_tendsto hω_win ?_
      filter_upwards with t
      refine mul_nonneg (by positivity) (Finset.sum_nonneg (fun τ _ => ?_))
      split_ifs
      · exact M.arrival_nonneg _ _ _
      · exact le_rfl
    · refine le_of_tendsto_of_tendsto hω_win hω_arr ?_
      filter_upwards with t
      refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun τ _ => ?_)) (by positivity)
      split_ifs
      · exact le_rfl
      · exact M.arrival_nonneg _ _ _
  -- Step 2.2-2.5: Lower bound `lamJ - M.δmax * cstar / V ^ Real.log V ≤ lamTilde` via DCT + Theorem 3
  have h_part_a2 : max (lamJ - M.δmax * cstar / (V ^ Real.log V)) 0 ≤ lamTilde := by
    refine max_le ?_ h_bounds_lam.1
    -- Define the out-of-window average arrival process `X t ω`
    let Bwin := backlogWindow (γstar j) D K V
    let X : ℕ → Ω → ℝ := fun t ω =>
      ((1 : ℝ) / (t : ℝ)) *
        ∑ τ ∈ Finset.range t,
          if pol.queue τ ω j ∈ Bwin then 0 else M.arrival (proc.S τ ω) (pol.act τ ω) j
    have hX_meas : ∀ t, Measurable (X t) := by
      intro t
      refine Measurable.const_mul ?_ _
      refine Finset.measurable_sum _ (fun τ _ => ?_)
      have hset : MeasurableSet {ω | pol.queue τ ω j ∈ Bwin} :=
        measurableSet_Icc.preimage (measurable_queue pol τ j)
      exact Measurable.ite hset measurable_const (pol.measurable_arrival τ j)
    have hX_bdd : ∀ t ω, ‖X t ω‖ ≤ M.δmax := by
      intro t ω
      have hX_nonneg : 0 ≤ X t ω := by
        refine mul_nonneg (by positivity) (Finset.sum_nonneg (fun τ _ => ?_))
        split_ifs
        · exact le_rfl
        · exact M.arrival_nonneg _ _ _
      rw [Real.norm_eq_abs, abs_of_nonneg hX_nonneg]
      cases t with
      | zero => simp [X, le_of_lt M.hδmax]
      | succ n =>
        have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
        have hsum : (∑ τ ∈ Finset.range (n + 1),
            if pol.queue τ ω j ∈ Bwin then 0 else M.arrival (proc.S τ ω) (pol.act τ ω) j) ≤
            ((n + 1 : ℕ) : ℝ) * M.δmax := by
          calc _ ≤ ∑ _τ ∈ Finset.range (n + 1), M.δmax := by
                refine Finset.sum_le_sum (fun τ _ => ?_)
                split_ifs
                · exact le_of_lt M.hδmax
                · exact M.arrival_le _ _ _
            _ = ((n + 1 : ℕ) : ℝ) * M.δmax := by simp
        dsimp [X]
        rw [one_div, inv_mul_le_iff₀ hpos]
        linarith
    have hX_tendsto : ∀ᵐ ω ∂μ, Filter.Tendsto (fun t => X t ω) Filter.atTop (nhds (lamJ - lamTilde)) := by
      filter_upwards [h_arr_t, h_win_t] with ω hω_arr hω_win
      have hsub := hω_arr.sub hω_win
      have heq : (fun t : ℕ => X t ω) = fun t : ℕ =>
          ((1 : ℝ) / (t : ℝ)) * ∑ τ ∈ Finset.range t, M.arrival (proc.S τ ω) (pol.act τ ω) j -
          ((1 : ℝ) / (t : ℝ)) * ∑ τ ∈ Finset.range t,
            if pol.queue τ ω j ∈ Bwin then M.arrival (proc.S τ ω) (pol.act τ ω) j else 0 := by
        funext t
        dsimp [X]
        rw [← mul_sub, ← Finset.sum_sub_distrib]
        congr 1
        refine Finset.sum_congr rfl (fun τ _ => ?_)
        split_ifs <;> ring
      rw [heq]
      exact hsub
    have h_int_tendsto : Filter.Tendsto (fun t => ∫ ω, X t ω ∂μ) Filter.atTop (nhds (lamJ - lamTilde)) := by
      have hdct := MeasureTheory.tendsto_integral_of_dominated_convergence (fun _ => M.δmax)
        (fun t => (hX_meas t).aestronglyMeasurable) (integrable_const M.δmax)
        (fun t => Filter.Eventually.of_forall (hX_bdd t)) hX_tendsto
      simpa [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] using hdct
    -- Pointwise upper bound on `∫ X t` by `M.δmax * (1/t) * ∑ τ < t, P(E_τ)`
    let E : ℕ → Set Ω := fun τ =>
      {ω | ∃ j' : Fin M.r, D + K * (Real.log V) ^ 2 < |pol.queue τ ω j' - γstar j'|}
    have hE_meas : ∀ τ, MeasurableSet (E τ) := by
      intro τ
      have : E τ = ⋃ j' : Fin M.r, {ω | D + K * (Real.log V) ^ 2 < |pol.queue τ ω j' - γstar j'|} := by
        ext ω; simp [E]
      rw [this]
      refine MeasurableSet.iUnion (fun j' => ?_)
      exact measurableSet_Ioi.preimage
        (continuous_abs.measurable.comp ((measurable_queue pol τ j').sub measurable_const))
    have h_int_le : ∀ t : ℕ, ∫ ω, X t ω ∂μ ≤
        M.δmax * (((1 : ℝ) / (t : ℝ)) * ∑ τ ∈ Finset.range t, (μ (E τ)).toReal) := by
      intro t
      have hterm_int : ∀ τ ∈ Finset.range t,
          Integrable (fun ω => if pol.queue τ ω j ∈ Bwin then 0 else M.arrival (proc.S τ ω) (pol.act τ ω) j) μ := by
        intro τ _
        have hset : MeasurableSet {ω | pol.queue τ ω j ∈ Bwin} :=
          measurableSet_Icc.preimage (measurable_queue pol τ j)
        have hmeas : Measurable (fun ω =>
            if pol.queue τ ω j ∈ Bwin then 0 else M.arrival (proc.S τ ω) (pol.act τ ω) j) :=
          Measurable.ite hset measurable_const (pol.measurable_arrival τ j)
        refine Integrable.of_bound hmeas.aestronglyMeasurable M.δmax ?_
        filter_upwards with ω
        split_ifs
        · simp [le_of_lt M.hδmax]
        · rw [Real.norm_eq_abs, abs_of_nonneg (M.arrival_nonneg _ _ _)]
          exact M.arrival_le _ _ _
      have hlin : ∫ ω, X t ω ∂μ = ((1 : ℝ) / (t : ℝ)) *
          ∑ τ ∈ Finset.range t, ∫ ω,
            (if pol.queue τ ω j ∈ Bwin then 0 else M.arrival (proc.S τ ω) (pol.act τ ω) j) ∂μ := by
        dsimp [X]
        rw [integral_const_mul, integral_finsetSum _ hterm_int]
      rw [hlin]
      have hterm_le : ∀ τ ∈ Finset.range t,
          ∫ ω, (if pol.queue τ ω j ∈ Bwin then 0 else M.arrival (proc.S τ ω) (pol.act τ ω) j) ∂μ ≤
            M.δmax * (μ (E τ)).toReal := by
        intro τ hτ
        have hind_int : Integrable ((E τ).indicator (fun _ : Ω => M.δmax)) μ :=
          (integrable_const M.δmax).indicator (hE_meas τ)
        have hpt : ∀ ω, (if pol.queue τ ω j ∈ Bwin then 0 else M.arrival (proc.S τ ω) (pol.act τ ω) j) ≤
            (E τ).indicator (fun _ : Ω => M.δmax) ω := by
          intro ω
          by_cases hmem : pol.queue τ ω j ∈ Bwin
          · rw [if_pos hmem]
            exact Set.indicator_nonneg (fun _ _ => le_of_lt M.hδmax) ω
          · rw [if_neg hmem]
            have hωE : ω ∈ E τ := by
              refine ⟨j, ?_⟩
              have hq0 : 0 ≤ pol.queue τ ω j := queue_nonneg pol τ ω j
              have hKlog : 0 ≤ K * (Real.log V) ^ 2 := mul_nonneg (le_of_lt hK) (sq_nonneg _)
              simp only [Bwin, backlogWindow, Set.mem_Icc, not_and_or, not_le, qLow, qHigh] at hmem
              rcases hmem with hlow | hhigh
              · have hlt : pol.queue τ ω j < γstar j - D - K * (Real.log V) ^ 2 := by
                  rcases max_choice (γstar j - D - K * (Real.log V) ^ 2) 0 with hmax | hmax
                  · rwa [hmax] at hlow
                  · rw [hmax] at hlow; linarith
                rw [abs_of_neg (by linarith)]
                linarith
              · rw [abs_of_pos (by linarith)]
                linarith
            rw [Set.indicator_of_mem hωE]
            exact M.arrival_le _ _ _
        have hmono := integral_mono (hterm_int τ hτ) hind_int hpt
        rw [integral_indicator_const M.δmax (hE_meas τ), smul_eq_mul, mul_comm, measureReal_def] at hmono
        exact hmono
      have hsum_le : (∑ τ ∈ Finset.range t,
          ∫ ω, (if pol.queue τ ω j ∈ Bwin then 0 else M.arrival (proc.S τ ω) (pol.act τ ω) j) ∂μ) ≤
          ∑ τ ∈ Finset.range t, M.δmax * (μ (E τ)).toReal :=
        Finset.sum_le_sum hterm_le
      rw [← Finset.mul_sum] at hsum_le
      calc ((1 : ℝ) / (t : ℝ)) *
              (∑ τ ∈ Finset.range t,
                ∫ ω, (if pol.queue τ ω j ∈ Bwin then 0 else M.arrival (proc.S τ ω) (pol.act τ ω) j) ∂μ)
          ≤ ((1 : ℝ) / (t : ℝ)) * (M.δmax * ∑ τ ∈ Finset.range t, (μ (E τ)).toReal) :=
            mul_le_mul_of_nonneg_left hsum_le (by positivity)
        _ = M.δmax * (((1 : ℝ) / (t : ℝ)) * ∑ τ ∈ Finset.range t, (μ (E τ)).toReal) := by ring
    -- Apply Theorem 3 with `m = (Real.log V)^2 ≥ 0`
    have h3_app := h3_body V hV γstar huniq hpoly Ω μ proc pol hbp ((Real.log V) ^ 2) (sq_nonneg _)
    have hexp_eq : cstar * Real.exp (-((Real.log V) ^ 2)) = cstar / (V ^ Real.log V) := by
      have hV_pos : 0 < V := lt_of_lt_of_le zero_lt_one hV
      rw [Real.rpow_def_of_pos hV_pos, ← sq, Real.exp_neg, div_eq_mul_inv]
    rw [hexp_eq] at h3_app
    -- Conclude `lamJ - lamTilde ≤ M.δmax * cstar / V ^ Real.log V` by contradiction
    suffices hdiff : lamJ - lamTilde ≤ M.δmax * cstar / (V ^ Real.log V) by linarith
    by_contra hnot
    push Not at hnot
    have hlt_div : cstar / (V ^ Real.log V) < (lamJ - lamTilde) / M.δmax := by
      rw [lt_div_iff₀ M.hδmax]
      linarith [mul_div_assoc M.δmax cstar (V ^ Real.log V)]
    let y : ℝ := (cstar / (V ^ Real.log V) + (lamJ - lamTilde) / M.δmax) / 2
    have hy1 : cstar / (V ^ Real.log V) < y := by dsimp [y]; linarith
    have hy2 : y < (lamJ - lamTilde) / M.δmax := by dsimp [y]; linarith
    have hlimsup_lt : deviationProb pol γstar D (K * (Real.log V) ^ 2) < (y : EReal) :=
      lt_of_le_of_lt h3_app (EReal.coe_lt_coe_iff.mpr hy1)
    have hev_p : ∀ᶠ t : ℕ in Filter.atTop,
        ((1 : ℝ) / (t : ℝ)) * ∑ τ ∈ Finset.range t, (μ (E τ)).toReal < y := by
      have h := Filter.eventually_lt_of_limsup_lt hlimsup_lt
      filter_upwards [h] with t ht
      exact EReal.coe_lt_coe_iff.mp ht
    have hev_int : ∀ᶠ t : ℕ in Filter.atTop, ∫ ω, X t ω ∂μ ≤ M.δmax * y := by
      filter_upwards [hev_p] with t ht
      exact le_trans (h_int_le t) (mul_le_mul_of_nonneg_left (le_of_lt ht) (le_of_lt M.hδmax))
    have hlim_le : lamJ - lamTilde ≤ M.δmax * y := le_of_tendsto h_int_tendsto hev_int
    have hMy_lt : M.δmax * y < lamJ - lamTilde := by
      have := (lt_div_iff₀ M.hδmax).mp hy2
      linarith
    linarith
  -- Combine Parts (a1), (a2), (a3), and prove Part (b) via Theorem 1
  refine ⟨h_part_a1, h_part_a2, h_bounds_lam.2, ?_⟩
  intro hlamTilde_pos
  filter_upwards [h_part_a1] with ω hω_rate
  let tightSys := tightWindowBufferSystem Q (γstar j) D K V ω
  -- Instantiate `Theorem1Statement` per sample path `ω` on `Ω' = Unit`, `μ' = Measure.dirac ()`
  have h1_ω := h1 {b : ℕ // b ∈ tightBufferSlots (γstar j) D K V M.δmax}
    {k : ι // k ∈ Q.windowDepartingSet (γstar j) D K V ω}
    Unit (Measure.dirac ()) (fun _ => tightSys) lamTilde hlamTilde_pos
  have h_liminf : ∀ᵐ _ : Unit ∂(Measure.dirac ()), (lamTilde : EReal) ≤
      Filter.liminf (fun t : ℕ => ((tightSys.arrivalsCount t : ℝ) / (t : ℝ) : EReal)) Filter.atTop := by
    refine Filter.Eventually.of_forall (fun _ => ?_)
    have hrate' : Filter.Tendsto
        (fun t : ℕ => ((tightSys.arrivalsCount t : ℝ) / (t : ℝ)))
        Filter.atTop (nhds lamTilde) := by
      simpa [tightSys, tightWindowBufferSystem_arrivalsCount_eq] using hω_rate
    have hrate_ereal : Filter.Tendsto
        (fun t : ℕ => ((tightSys.arrivalsCount t : ℝ) / (t : ℝ) : EReal))
        Filter.atTop (nhds (lamTilde : EReal)) :=
      (EReal.continuous_coe_iff.mpr continuous_id).continuousAt.tendsto.comp hrate'
    rw [hrate_ereal.liminf_eq]
  have h_dep_inf : ∀ᵐ _ : Unit ∂(Measure.dirac ()),
      Filter.Tendsto (fun t : ℕ => tightSys.departuresCount t) Filter.atTop Filter.atTop := by
    refine Filter.Eventually.of_forall (fun _ => ?_)
    rw [Filter.tendsto_atTop_atTop]
    intro N
    have hev_half : ∀ᶠ t : ℕ in Filter.atTop,
        lamTilde / 2 < (tightSys.arrivalsCount t : ℝ) / (t : ℝ) := by
      have hrate' : Filter.Tendsto
          (fun t : ℕ => ((tightSys.arrivalsCount t : ℝ) / (t : ℝ)))
          Filter.atTop (nhds lamTilde) := by
        simpa [tightSys, tightWindowBufferSystem_arrivalsCount_eq] using hω_rate
      exact hrate'.eventually (Ioi_mem_nhds (half_lt_self hlamTilde_pos))
    obtain ⟨t₁_0, ht₁_0⟩ := Filter.eventually_atTop.mp hev_half
    obtain ⟨t₁_1, ht₁_1⟩ := exists_nat_gt ((N : ℝ) / (lamTilde / 2))
    let t₁ : ℕ := max (max t₁_0 t₁_1) 1
    have ht₁_pos : (0 : ℝ) < (t₁ : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _))
    have ht₁_arr : N ≤ (tightSys.finite_arrivals t₁).toFinset.card := by
      have h1' := ht₁_0 t₁ (le_trans (le_max_left _ _) (le_max_left _ _))
      have h2' : (N : ℝ) / (lamTilde / 2) < (t₁ : ℝ) :=
        lt_of_lt_of_le ht₁_1 (by exact_mod_cast (le_trans (le_max_right _ _) (le_max_left _ _)))
      have h3' : (N : ℝ) < (lamTilde / 2) * (t₁ : ℝ) := by
        have := (div_lt_iff₀ (half_pos hlamTilde_pos)).mp h2'
        linarith
      have h4' : (lamTilde / 2) * (t₁ : ℝ) < (tightSys.arrivalsCount t₁ : ℝ) :=
        (lt_div_iff₀ ht₁_pos).mp h1'
      have h5' : (N : ℝ) < ((tightSys.finite_arrivals t₁).toFinset.card : ℝ) :=
        lt_trans h3' h4'
      exact Nat.le_of_lt (by exact_mod_cast h5')
    let S := (tightSys.finite_arrivals t₁).toFinset
    let depTime : {k : ι // k ∈ Q.windowDepartingSet (γstar j) D K V ω} → ℕ :=
      fun k => match Q.depart ω k.1 with
        | some d => d
        | none => 0
    let T : ℕ := S.sup depTime
    refine ⟨T, fun t ht => ?_⟩
    have hsub : S ⊆ (tightSys.finite_departures t).toFinset := by
      intro k hk
      rw [Set.Finite.mem_toFinset]
      change Q.depart ω k.1 ≤ (t : WithTop ℕ)
      have hne : Q.depart ω k.1 ≠ ⊤ := k.2.2
      cases hd : Q.depart ω k.1 with
      | top => exact absurd hd hne
      | coe d =>
        have hleT : depTime k ≤ T := Finset.le_sup (f := depTime) hk
        have hd_eq : depTime k = d := by simp [depTime, hd]
        rw [hd_eq] at hleT
        exact WithTop.coe_le_coe.mpr (le_trans hleT ht)
    exact le_trans ht₁_arr (Finset.card_le_card hsub)
  have h1_res := h1_ω h_liminf h_dep_inf
  have h1_pt : Filter.limsup (fun t : ℕ => (tightSys.avgDelay t : EReal)) Filter.atTop ≤
      (((Fintype.card {b : ℕ // b ∈ tightBufferSlots (γstar j) D K V M.δmax} : ℝ) / lamTilde : ℝ) : EReal) := by
    have := Filter.Eventually.exists h1_res
    rcases this with ⟨_, h⟩
    exact h
  have hcard_eq : (Fintype.card {b : ℕ // b ∈ tightBufferSlots (γstar j) D K V M.δmax} : ℝ) =
      ((tightBufferSlots (γstar j) D K V M.δmax).card : ℝ) := by
    exact_mod_cast Fintype.card_coe _
  have hcard_le := card_tightBufferSlots_le (V := V) (huniq.1.1 j) hD hK M.hδmax
  have hdiv_le : ((Fintype.card {b : ℕ // b ∈ tightBufferSlots (γstar j) D K V M.δmax} : ℝ) / lamTilde) ≤
      (2 * D + 2 * K * (Real.log V) ^ 2 + 2 * M.δmax + 1) / lamTilde := by
    rw [hcard_eq]
    exact div_le_div_of_nonneg_right hcard_le (le_of_lt hlamTilde_pos)
  exact le_trans h1_pt (EReal.coe_le_coe_iff.mpr hdiv_le)

end LifoBackpressure.Proofs
