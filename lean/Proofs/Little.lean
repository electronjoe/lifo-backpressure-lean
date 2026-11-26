import Statements.Little

/-!
# Proof of Theorem 1 (`theorem:little1`): Modified Little's Theorem for LIFO Systems

Proves `LifoBackpressure.Statements.Theorem1Statement` following Appendix A of
`arXiv:1008.4895v2` (lines 1019–1080) and `lamport/theorem-little1.md`.
-/

namespace LifoBackpressure.Proofs

open Filter MeasureTheory Classical
open LifoBackpressure.Statements

/-- Occupancy interval `[arrival k, d)` of a departing job `k`, or `∅` if `k` never departs. -/
private def jobInterval {B : Type*} [Fintype B] {ι : Type*}
    (sys : BufferSystem B ι) (k : ι) : Finset ℕ :=
  match sys.depart k with
  | some d => Finset.Ico (sys.arrival k) d
  | none => ∅

private lemma card_jobInterval {B : Type*} [Fintype B] {ι : Type*}
    (sys : BufferSystem B ι) (k : ι) :
    (jobInterval sys k).card = sys.jobDelay k := by
  unfold jobInterval BufferSystem.jobDelay
  cases sys.depart k with
  | top => simp
  | coe d => simp [Nat.card_Ico]

private lemma jobInterval_subset_range {B : Type*} [Fintype B] {ι : Type*}
    (sys : BufferSystem B ι) {t : ℕ} {k : ι}
    (hk : k ∈ (sys.finite_departures t).toFinset) :
    jobInterval sys k ⊆ Finset.range t := by
  have hk' : sys.depart k ≤ (t : WithTop ℕ) := by
    simpa [BufferSystem.departuresSet] using hk
  unfold jobInterval
  cases hdep : sys.depart k with
  | top => simp
  | coe d =>
    rw [hdep] at hk'
    have hd : d ≤ t := WithTop.coe_le_coe.mp hk'
    intro τ hτ
    rw [Finset.mem_Ico] at hτ
    rw [Finset.mem_range]
    exact lt_of_lt_of_le hτ.2 hd

private lemma disjoint_jobInterval {B : Type*} [Fintype B] {ι : Type*}
    (sys : BufferSystem B ι) {k₁ k₂ : ι} (hne : k₁ ≠ k₂)
    (hsl : sys.slot k₁ = sys.slot k₂) :
    Disjoint (jobInterval sys k₁) (jobInterval sys k₂) := by
  rw [Finset.disjoint_left]
  intro τ hτ₁ hτ₂
  have h1 : sys.arrival k₁ ≤ τ ∧ (τ : WithTop ℕ) < sys.depart k₁ := by
    unfold jobInterval at hτ₁
    cases hd₁ : sys.depart k₁ with
    | top => simp [hd₁] at hτ₁
    | coe d₁ =>
      simp only [hd₁, Finset.mem_Ico] at hτ₁
      exact ⟨hτ₁.1, WithTop.coe_lt_coe.mpr hτ₁.2⟩
  have h2 : sys.arrival k₂ ≤ τ ∧ (τ : WithTop ℕ) < sys.depart k₂ := by
    unfold jobInterval at hτ₂
    cases hd₂ : sys.depart k₂ with
    | top => simp [hd₂] at hτ₂
    | coe d₂ =>
      simp only [hd₂, Finset.mem_Ico] at hτ₂
      exact ⟨hτ₂.1, WithTop.coe_lt_coe.mpr hτ₂.2⟩
  exact sys.disjoint_slots k₁ k₂ hne hsl τ ⟨h1, h2⟩

/-- Lamport Step 2: Total delay of all jobs departing from `B` by time `t` is at most `|B| * t`. -/
theorem totalDelay_le_card_mul {B : Type*} [Fintype B] {ι : Type*}
    (sys : BufferSystem B ι) (t : ℕ) :
    sys.totalDelay t ≤ Fintype.card B * t := by
  unfold BufferSystem.totalDelay
  let D : Finset ι := (sys.finite_departures t).toFinset
  have hpart :
      ∑ k ∈ D, sys.jobDelay k =
        ∑ b : B, ∑ k ∈ D.filter (fun k => sys.slot k = b), sys.jobDelay k := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := sys.slot) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)]
  rw [hpart]
  calc
    ∑ b : B, ∑ k ∈ D.filter (fun k => sys.slot k = b), sys.jobDelay k
        ≤ ∑ _b : B, t := by
          apply Finset.sum_le_sum
          intro b _
          let Sb := D.filter (fun k => sys.slot k = b)
          have hdisj : (Sb : Set ι).PairwiseDisjoint (jobInterval sys) := by
            intro k₁ hk₁ k₂ hk₂ hne
            have hb₁ : sys.slot k₁ = b := (Finset.mem_filter.mp hk₁).2
            have hb₂ : sys.slot k₂ = b := (Finset.mem_filter.mp hk₂).2
            exact disjoint_jobInterval sys hne (hb₁.trans hb₂.symm)
          have hsub : Sb.biUnion (jobInterval sys) ⊆ Finset.range t := by
            rw [Finset.biUnion_subset]
            intro k hk
            exact jobInterval_subset_range sys (Finset.mem_filter.mp hk).1
          calc
            ∑ k ∈ Sb, sys.jobDelay k
                = ∑ k ∈ Sb, (jobInterval sys k).card := by
                    refine Finset.sum_congr rfl (fun k _ => (card_jobInterval sys k).symm)
            _ = (Sb.biUnion (jobInterval sys)).card := (Finset.card_biUnion hdisj).symm
            _ ≤ (Finset.range t).card := Finset.card_le_card hsub
            _ = t := Finset.card_range t
    _ = Fintype.card B * t := by simp

/-- Lamport Step 3: At most `|B|` jobs arriving before time `t` can remain undeparted at time `t`,
so `N(t) ≤ D(t) + |B|`. -/
theorem arrivalsCount_le_departuresCount_add_card {B : Type*} [Fintype B] {ι : Type*}
    (sys : BufferSystem B ι) (t : ℕ) :
    sys.arrivalsCount t ≤ sys.departuresCount t + Fintype.card B := by
  unfold BufferSystem.arrivalsCount BufferSystem.departuresCount
  let A : Finset ι := (sys.finite_arrivals t).toFinset
  let D : Finset ι := (sys.finite_departures t).toFinset
  have hsub : A ⊆ D ∪ (A \ D) := by
    intro k hk
    by_cases h : k ∈ D
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hk, h⟩)
  have hcard : A.card ≤ D.card + (A \ D).card :=
    le_trans (Finset.card_le_card hsub) (Finset.card_union_le D (A \ D))
  have hinj : Set.InjOn sys.slot ↑(A \ D) := by
    intro k₁ hk₁ k₂ hk₂ hsl
    by_contra hne
    rcases Finset.mem_sdiff.mp (Finset.mem_coe.mp hk₁) with ⟨ha₁, hd₁⟩
    rcases Finset.mem_sdiff.mp (Finset.mem_coe.mp hk₂) with ⟨ha₂, hd₂⟩
    have ha₁' : sys.arrival k₁ ≤ t := le_of_lt (by simpa [A] using ha₁)
    have ha₂' : sys.arrival k₂ ≤ t := le_of_lt (by simpa [A] using ha₂)
    have hd₁' : (t : WithTop ℕ) < sys.depart k₁ := by
      have hnot : ¬ sys.depart k₁ ≤ (t : WithTop ℕ) := by
        simpa [D, BufferSystem.departuresSet] using hd₁
      exact lt_of_not_ge hnot
    have hd₂' : (t : WithTop ℕ) < sys.depart k₂ := by
      have hnot : ¬ sys.depart k₂ ≤ (t : WithTop ℕ) := by
        simpa [D, BufferSystem.departuresSet] using hd₂
      exact lt_of_not_ge hnot
    exact sys.disjoint_slots k₁ k₂ hne hsl t ⟨⟨ha₁', hd₁'⟩, ⟨ha₂', hd₂'⟩⟩
  have hdiff : (A \ D).card ≤ Fintype.card B := by
    have := Finset.card_le_card_of_injOn sys.slot (fun _ _ => Finset.mem_univ _) hinj
    simpa using this
  exact le_trans hcard (Nat.add_le_add_left hdiff D.card)

/-- Lamport Step 4: Deterministic sample-path `limsup` average delay bound. -/
theorem limsup_avgDelay_le_of_path {B : Type*} [Fintype B] {ι : Type*}
    (sys : BufferSystem B ι) {lamMin : ℝ} (hlam : 0 < lamMin)
    (hliminf : (lamMin : EReal) ≤
      Filter.liminf (fun t : ℕ => (((sys.arrivalsCount t : ℝ) / (t : ℝ)) : EReal)) Filter.atTop) :
    Filter.limsup (fun t : ℕ => ((sys.avgDelay t : ℝ) : EReal)) Filter.atTop ≤
      (((Fintype.card B : ℝ) / lamMin : ℝ) : EReal) := by
  let C : ℝ := (Fintype.card B : ℝ)
  have hC_nonneg : 0 ≤ C := Nat.cast_nonneg _
  have hbound : ∀ r : ℝ, 0 < r → r < lamMin →
      Filter.limsup (fun t : ℕ => ((sys.avgDelay t : ℝ) : EReal)) Filter.atTop ≤
        ((C / r : ℝ) : EReal) := by
    intro r hr_pos hr_lt
    let r' : ℝ := (r + lamMin) / 2
    have hr'_gt : r < r' := by dsimp [r']; linarith
    have hr'_lt : r' < lamMin := by dsimp [r']; linarith
    have hlt_liminf : ((r' : ℝ) : EReal) <
        Filter.liminf (fun t : ℕ => (((sys.arrivalsCount t : ℝ) / (t : ℝ)) : EReal)) Filter.atTop :=
      lt_of_lt_of_le (EReal.coe_lt_coe_iff.mpr hr'_lt) hliminf
    have hev_arr : ∀ᶠ t : ℕ in Filter.atTop,
        ((r' : ℝ) : EReal) < (((sys.arrivalsCount t : ℝ) / (t : ℝ)) : EReal) :=
      Filter.eventually_lt_of_lt_liminf hlt_liminf
    have hev_t : ∀ᶠ t : ℕ in Filter.atTop, C < (r' - r) * (t : ℝ) ∧ 0 < (t : ℝ) := by
      obtain ⟨N, hN⟩ := exists_nat_gt (C / (r' - r))
      filter_upwards [Filter.eventually_ge_atTop (max N 1)] with t ht
      have ht1 : (1 : ℕ) ≤ t := le_trans (le_max_right N 1) ht
      have ht_pos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one ht1)
      have htN : (N : ℝ) ≤ (t : ℝ) := by exact_mod_cast (le_trans (le_max_left N 1) ht)
      have hdiff_pos : 0 < r' - r := sub_pos.mpr hr'_gt
      have h1 : C / (r' - r) < (t : ℝ) := lt_of_lt_of_le hN htN
      exact ⟨by linarith [(div_lt_iff₀ hdiff_pos).mp h1], ht_pos⟩
    have hev_avg : ∀ᶠ t : ℕ in Filter.atTop,
        ((sys.avgDelay t : ℝ) : EReal) ≤ ((C / r : ℝ) : EReal) := by
      filter_upwards [hev_arr, hev_t] with t h_arr ⟨hC_lt, ht_pos⟩
      have h_arr_real : r' < (sys.arrivalsCount t : ℝ) / (t : ℝ) :=
        EReal.coe_lt_coe_iff.mp h_arr
      have h_arr_mul : r' * (t : ℝ) < (sys.arrivalsCount t : ℝ) :=
        (lt_div_iff₀ ht_pos).mp h_arr_real
      have hND : (sys.arrivalsCount t : ℝ) ≤ (sys.departuresCount t : ℝ) + C := by
        dsimp [C]
        exact_mod_cast arrivalsCount_le_departuresCount_add_card sys t
      have hD_gt : r * (t : ℝ) < (sys.departuresCount t : ℝ) := by linarith
      have hrt_pos : 0 < r * (t : ℝ) := mul_pos hr_pos ht_pos
      have hD_pos : 0 < (sys.departuresCount t : ℝ) := lt_trans hrt_pos hD_gt
      have hW_le : (sys.totalDelay t : ℝ) ≤ C * (t : ℝ) := by
        dsimp [C]
        exact_mod_cast totalDelay_le_card_mul sys t
      have havg_le : sys.avgDelay t ≤ C / r := by
        unfold BufferSystem.avgDelay
        rw [div_le_div_iff₀ hD_pos hr_pos]
        have h1 : (sys.totalDelay t : ℝ) * r ≤ C * (t : ℝ) * r :=
          mul_le_mul_of_nonneg_right hW_le (le_of_lt hr_pos)
        have h2 : C * (r * (t : ℝ)) ≤ C * (sys.departuresCount t : ℝ) :=
          mul_le_mul_of_nonneg_left (le_of_lt hD_gt) hC_nonneg
        linarith
      exact EReal.coe_le_coe_iff.mpr havg_le
    exact Filter.limsup_le_of_le (by isBoundedDefault) hev_avg
  by_contra hnot
  have hlt : ((C / lamMin : ℝ) : EReal) <
      Filter.limsup (fun t : ℕ => ((sys.avgDelay t : ℝ) : EReal)) Filter.atTop :=
    lt_of_not_ge hnot
  rcases eq_or_lt_of_le hC_nonneg with hC0 | hC_pos
  · have hb := hbound (lamMin / 2) (half_pos hlam) (half_lt_self hlam)
    rw [← hC0, zero_div] at hb hlt
    exact not_lt_of_ge hb hlt
  · obtain ⟨y, hy1, hy2⟩ := EReal.exists_between_coe_real hlt
    have hy_gt : C / lamMin < y := EReal.coe_lt_coe_iff.mp hy1
    have hy_pos : 0 < y := lt_trans (div_pos hC_pos hlam) hy_gt
    have hCy_lt : C / y < lamMin := by
      rw [div_lt_iff₀ hy_pos]
      have := (div_lt_iff₀ hlam).mp hy_gt
      linarith
    have hCy_pos : 0 < C / y := div_pos hC_pos hy_pos
    let r : ℝ := (C / y + lamMin) / 2
    have hr_pos : 0 < r := by dsimp [r]; linarith
    have hr_lt : r < lamMin := by dsimp [r]; linarith
    have hr_gt : C / y < r := by dsimp [r]; linarith
    have hCr_lt : C / r < y := by
      rw [div_lt_iff₀ hr_pos]
      have := (div_lt_iff₀ hy_pos).mp hr_gt
      linarith
    have hb := hbound r hr_pos hr_lt
    have hlt' : ((C / r : ℝ) : EReal) <
        Filter.limsup (fun t : ℕ => ((sys.avgDelay t : ℝ) : EReal)) Filter.atTop :=
      lt_trans (EReal.coe_lt_coe_iff.mpr hCr_lt) hy2
    exact not_lt_of_ge hb hlt'

/-- Proof of Theorem 1 (`theorem:little1`): Modified Little's Theorem for LIFO Systems. -/
theorem theorem1 : Theorem1Statement := by
  intro B _ ι Ω _ μ _ sys lamMin hlam hliminf hdep
  filter_upwards [hliminf, hdep] with ω hω_liminf _
  exact limsup_avgDelay_le_of_path (sys ω) hlam hω_liminf

end LifoBackpressure.Proofs
