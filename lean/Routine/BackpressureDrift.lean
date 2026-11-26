import Prelude
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Routine Queueing Drift, Exponential Bound, and Cesàro Stability Lemmas

Statement-independent algebraic and analytic lemmas shared by Theorems 2 and 3:
1. One-slot queue backlog bounds (`queueNext_sub_abs_le`, `quad_drift_one_slot`,
   `dist_sq_drift_one_slot`).
2. Padé-type exponential upper bound (`exp_le_quad_div`):
   `e^y ≤ 1 + y + y^2 / (2 * (1 - y / 3))` for all `y < 3` (Appendix B of `arXiv:0904.3795v1`).
3. Cesàro stability subsequence lemma (`exists_small_ratio_of_avg_limsup_lt_top`) for
   elementary weak duality in Theorem 2.
-/

namespace LifoBackpressure.Routine

open Filter

section QueueAlgebra

lemma sub_le_max_sub_add (q μ A : ℝ) :
    A - μ ≤ (max (q - μ) 0 + A) - q := by
  linarith [le_max_left (q - μ) 0]

lemma abs_max_sub_add_sub_le {q μ A δ : ℝ}
    (hq : 0 ≤ q) (hμ0 : 0 ≤ μ) (hA0 : 0 ≤ A) (hμδ : μ ≤ δ) (hAδ : A ≤ δ) :
    |(max (q - μ) 0 + A) - q| ≤ δ := by
  rw [abs_le]
  rcases le_or_gt μ q with h | h
  · rw [max_eq_left (sub_nonneg.mpr h)]
    constructor <;> linarith
  · rw [max_eq_right (le_of_lt (sub_neg.mpr h))]
    constructor <;> linarith

/-- Scalar one-slot quadratic Lyapunov drift inequality (Eq. 3). -/
lemma scalar_quad_drift {q μ A δ : ℝ}
    (hq : 0 ≤ q) (hμ0 : 0 ≤ μ) (hA0 : 0 ≤ A) (hμδ : μ ≤ δ) (hAδ : A ≤ δ) :
    (1 / 2 : ℝ) * (max (q - μ) 0 + A) ^ 2 - (1 / 2 : ℝ) * q ^ 2 ≤
      δ ^ 2 + q * (A - μ) := by
  rcases le_or_gt μ q with h | h
  · rw [max_eq_left (sub_nonneg.mpr h)]
    have hdiff : (A - μ) ^ 2 ≤ δ ^ 2 := by nlinarith
    nlinarith
  · rw [max_eq_right (le_of_lt (sub_neg.mpr h))]
    nlinarith

/-- Vector one-slot quadratic Lyapunov drift inequality (for Theorem 2). -/
lemma sum_quad_drift {r : ℕ} {q μ A : Fin r → ℝ} {δ : ℝ}
    (hq : ∀ j, 0 ≤ q j) (hμ0 : ∀ j, 0 ≤ μ j) (hA0 : ∀ j, 0 ≤ A j)
    (hμδ : ∀ j, μ j ≤ δ) (hAδ : ∀ j, A j ≤ δ) :
    (1 / 2 : ℝ) * ∑ j : Fin r, (max (q j - μ j) 0 + A j) ^ 2 -
      (1 / 2 : ℝ) * ∑ j : Fin r, (q j) ^ 2 ≤
      (r : ℝ) * δ ^ 2 + ∑ j : Fin r, q j * (A j - μ j) := by
  have hsum : ∑ j : Fin r,
      ((1 / 2 : ℝ) * (max (q j - μ j) 0 + A j) ^ 2 - (1 / 2 : ℝ) * (q j) ^ 2) ≤
      ∑ j : Fin r, (δ ^ 2 + q j * (A j - μ j)) :=
    Finset.sum_le_sum (fun j _ => scalar_quad_drift (hq j) (hμ0 j) (hA0 j) (hμδ j) (hAδ j))
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  exact hsum

/-- Scalar one-slot squared distance drift inequality to any `γ ≥ 0` (Appendix A Lemma 2 of `0904.3795v1`). -/
lemma scalar_dist_sq_drift {q μ A γ δ : ℝ}
    (hq : 0 ≤ q) (hμ0 : 0 ≤ μ) (hA0 : 0 ≤ A) (hγ : 0 ≤ γ) (hμδ : μ ≤ δ) (hAδ : A ≤ δ) :
    ((max (q - μ) 0 + A) - γ) ^ 2 ≤
      (q - γ) ^ 2 + 2 * δ ^ 2 - 2 * (γ - q) * (A - μ) := by
  rcases le_or_gt μ q with h | h
  · rw [max_eq_left (sub_nonneg.mpr h)]
    have hdiff : (A - μ) ^ 2 ≤ δ ^ 2 := by nlinarith
    nlinarith
  · rw [max_eq_right (le_of_lt (sub_neg.mpr h))]
    have h1 : 0 ≤ 2 * γ * (μ - q) := by nlinarith
    have h2 : 0 ≤ (q - μ) ^ 2 := sq_nonneg _
    have h3 : 0 ≤ 2 * q * A := by nlinarith
    have h4 : 0 ≤ δ ^ 2 - μ ^ 2 := by nlinarith
    have h5 : 0 ≤ δ ^ 2 - A ^ 2 := by nlinarith
    nlinarith

/-- Vector one-slot squared Euclidean distance drift inequality (for Theorem 3). -/
lemma sum_dist_sq_drift {r : ℕ} {q μ A γ : Fin r → ℝ} {δ : ℝ}
    (hq : ∀ j, 0 ≤ q j) (hμ0 : ∀ j, 0 ≤ μ j) (hA0 : ∀ j, 0 ≤ A j) (hγ : ∀ j, 0 ≤ γ j)
    (hμδ : ∀ j, μ j ≤ δ) (hAδ : ∀ j, A j ≤ δ) :
    ∑ j : Fin r, ((max (q j - μ j) 0 + A j) - γ j) ^ 2 ≤
      ∑ j : Fin r, (q j - γ j) ^ 2 + 2 * (r : ℝ) * δ ^ 2 -
      2 * ∑ j : Fin r, (γ j - q j) * (A j - μ j) := by
  have hsum : ∑ j : Fin r, ((max (q j - μ j) 0 + A j) - γ j) ^ 2 ≤
      ∑ j : Fin r, ((q j - γ j) ^ 2 + 2 * δ ^ 2 - 2 * (γ j - q j) * (A j - μ j)) :=
    Finset.sum_le_sum (fun j _ => scalar_dist_sq_drift (hq j) (hμ0 j) (hA0 j) (hγ j) (hμδ j) (hAδ j))
  calc ∑ j : Fin r, ((max (q j - μ j) 0 + A j) - γ j) ^ 2
      ≤ ∑ j : Fin r, ((q j - γ j) ^ 2 + 2 * δ ^ 2 - 2 * (γ j - q j) * (A j - μ j)) := hsum
    _ = (∑ j : Fin r, (q j - γ j) ^ 2) + (∑ _j : Fin r, 2 * δ ^ 2) -
          ∑ j : Fin r, 2 * ((γ j - q j) * (A j - μ j)) := by
          simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, mul_assoc]
    _ = ∑ j : Fin r, (q j - γ j) ^ 2 + 2 * (r : ℝ) * δ ^ 2 -
          2 * ∑ j : Fin r, (γ j - q j) * (A j - μ j) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
          ring

/-- Euclidean one-step queue increment bound: `√(∑_j (q'_j - q_j)^2) ≤ √r * δ`. -/
lemma sqrt_sum_sq_step_le {r : ℕ} {q μ A : Fin r → ℝ} {δ : ℝ}
    (hq : ∀ j, 0 ≤ q j) (hμ0 : ∀ j, 0 ≤ μ j) (hA0 : ∀ j, 0 ≤ A j)
    (hμδ : ∀ j, μ j ≤ δ) (hAδ : ∀ j, A j ≤ δ) (hδ : 0 ≤ δ) :
    Real.sqrt (∑ j : Fin r, ((max (q j - μ j) 0 + A j) - q j) ^ 2) ≤
      Real.sqrt (r : ℝ) * δ := by
  have hsum : ∑ j : Fin r, ((max (q j - μ j) 0 + A j) - q j) ^ 2 ≤ (r : ℝ) * δ ^ 2 := by
    calc ∑ j : Fin r, ((max (q j - μ j) 0 + A j) - q j) ^ 2
        ≤ ∑ _j : Fin r, δ ^ 2 := by
            refine Finset.sum_le_sum (fun j _ => ?_)
            have habs := abs_max_sub_add_sub_le (hq j) (hμ0 j) (hA0 j) (hμδ j) (hAδ j)
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) habs 2
      _ = (r : ℝ) * δ ^ 2 := by simp
  calc Real.sqrt (∑ j : Fin r, ((max (q j - μ j) 0 + A j) - q j) ^ 2)
      ≤ Real.sqrt ((r : ℝ) * δ ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt (r : ℝ) * Real.sqrt (δ ^ 2) := Real.sqrt_mul (Nat.cast_nonneg r) _
    _ = Real.sqrt (r : ℝ) * δ := by rw [Real.sqrt_sq hδ]

/-- Cauchy-Schwarz inequality on `Fin r → ℝ`:
`|∑_j a_j * b_j| ≤ √(∑_j a_j^2) * √(∑_j b_j^2)`. -/
lemma abs_sum_mul_le_sqrt_mul_sqrt {r : ℕ} (a b : Fin r → ℝ) :
    |∑ j : Fin r, a j * b j| ≤
      Real.sqrt (∑ j : Fin r, (a j) ^ 2) * Real.sqrt (∑ j : Fin r, (b j) ^ 2) := by
  have hcs : (∑ j : Fin r, a j * b j) ^ 2 ≤
      (∑ j : Fin r, (a j) ^ 2) * (∑ j : Fin r, (b j) ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b
  have h1 : Real.sqrt ((∑ j : Fin r, a j * b j) ^ 2) ≤
      Real.sqrt ((∑ j : Fin r, (a j) ^ 2) * (∑ j : Fin r, (b j) ^ 2)) :=
    Real.sqrt_le_sqrt hcs
  rw [Real.sqrt_sq_eq_abs,
    Real.sqrt_mul (Finset.sum_nonneg (fun _ _ => sq_nonneg _))] at h1
  exact h1

/-- Triangle inequality for Euclidean distance on `Fin r → ℝ`. -/
lemma euc_triangle {r : ℕ} (a b c : Fin r → ℝ) :
    Real.sqrt (∑ j : Fin r, (a j - c j) ^ 2) ≤
      Real.sqrt (∑ j : Fin r, (a j - b j) ^ 2) + Real.sqrt (∑ j : Fin r, (b j - c j) ^ 2) := by
  have hsum_eq : ∑ j : Fin r, (a j - c j) ^ 2 =
      (∑ j : Fin r, (a j - b j) ^ 2) + 2 * (∑ j : Fin r, (a j - b j) * (b j - c j)) +
      (∑ j : Fin r, (b j - c j) ^ 2) := by
    have hpt : ∀ j, (a j - c j) ^ 2 = (a j - b j) ^ 2 + 2 * ((a j - b j) * (b j - c j)) + (b j - c j) ^ 2 :=
      fun j => by ring
    simp_rw [hpt, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hcs := abs_sum_mul_le_sqrt_mul_sqrt (fun j => a j - b j) (fun j => b j - c j)
  have hle : ∑ j : Fin r, (a j - b j) * (b j - c j) ≤
      Real.sqrt (∑ j : Fin r, (a j - b j) ^ 2) * Real.sqrt (∑ j : Fin r, (b j - c j) ^ 2) :=
    le_trans (le_abs_self _) hcs
  have hsq : ∑ j : Fin r, (a j - c j) ^ 2 ≤
      (Real.sqrt (∑ j : Fin r, (a j - b j) ^ 2) + Real.sqrt (∑ j : Fin r, (b j - c j) ^ 2)) ^ 2 := by
    rw [hsum_eq, add_sq, Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _)),
      Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
    linarith
  calc Real.sqrt (∑ j : Fin r, (a j - c j) ^ 2)
      ≤ Real.sqrt ((Real.sqrt (∑ j : Fin r, (a j - b j) ^ 2) +
          Real.sqrt (∑ j : Fin r, (b j - c j) ^ 2)) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (∑ j : Fin r, (a j - b j) ^ 2) + Real.sqrt (∑ j : Fin r, (b j - c j) ^ 2) :=
        Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

end QueueAlgebra

/-! ### Exponential Padé upper bound for Appendix B of `arXiv:0904.3795v1` -/

/-- For every `y < 3`, `Real.exp y ≤ 1 + y + y^2 / (2 * (1 - y / 3))`. -/
theorem exp_le_quad_div {y : ℝ} (hy : y < 3) :
    Real.exp y ≤ 1 + y + y ^ 2 / (2 * (1 - y / 3)) := by
  let g : ℝ → ℝ := fun x => Real.exp (-x) * ((6 + 4 * x + x ^ 2) / (6 - 2 * x))
  have hderiv : ∀ x : ℝ, x < 3 →
      HasDerivAt g (2 * x ^ 3 * Real.exp (-x) / (6 - 2 * x) ^ 2) x := by
    intro x hx
    have hden : 6 - 2 * x ≠ 0 := by linarith
    have hd_exp : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-x)) x := by
      have h := (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)
      simpa [Function.comp_def] using h
    have hd_num : HasDerivAt (fun t : ℝ => 6 + 4 * t + t ^ 2) (4 + 2 * x) x :=
      (((hasDerivAt_const x (6 : ℝ)).add ((hasDerivAt_id x).const_mul 4)).add
        (hasDerivAt_pow 2 x)).congr_deriv (by ring)
    have hd_den : HasDerivAt (fun t : ℝ => 6 - 2 * t) (-2) x :=
      ((hasDerivAt_const x (6 : ℝ)).sub ((hasDerivAt_id x).const_mul 2)).congr_deriv (by ring)
    refine (hd_exp.mul (hd_num.div hd_den hden)).congr_deriv ?_
    have hden2 : (6 - 2 * x) ^ 2 ≠ 0 := pow_ne_zero 2 hden
    rw [eq_div_iff hden2]
    have hmul1 : -Real.exp (-x) * ((6 + 4 * x + x ^ 2) / (6 - 2 * x)) * (6 - 2 * x) ^ 2 =
        -Real.exp (-x) * (6 + 4 * x + x ^ 2) * (6 - 2 * x) := by
      have : (6 + 4 * x + x ^ 2) / (6 - 2 * x) * (6 - 2 * x) ^ 2 = (6 + 4 * x + x ^ 2) * (6 - 2 * x) := by
        rw [sq (6 - 2 * x), ← mul_assoc, div_mul_cancel₀ _ hden]
      linear_combination -Real.exp (-x) * this
    have hmul2 : Real.exp (-x) * (((4 + 2 * x) * (6 - 2 * x) - (6 + 4 * x + x ^ 2) * -2) / (6 - 2 * x) ^ 2) *
        (6 - 2 * x) ^ 2 =
        Real.exp (-x) * ((4 + 2 * x) * (6 - 2 * x) - (6 + 4 * x + x ^ 2) * -2) := by
      rw [mul_assoc, div_mul_cancel₀ _ hden2]
    dsimp only [Pi.div_apply]
    rw [add_mul, hmul1, hmul2]
    ring
  have hg_ge_one : 1 ≤ g y := by
    have hg0 : g 0 = 1 := by simp [g]
    rcases le_or_gt 0 y with hy0 | hy0
    · -- On `[0, y] ⊆ (-∞, 3)`, `g' ≥ 0`, so `g 0 ≤ g y`
      have hmono : MonotoneOn g (Set.Icc 0 y) := by
        refine monotoneOn_of_deriv_nonneg (convex_Icc 0 y) ?_ ?_ ?_
        · intro x hx
          exact (hderiv x (lt_of_le_of_lt hx.2 hy)).continuousAt.continuousWithinAt
        · intro x hx
          rw [interior_Icc] at hx
          exact (hderiv x (lt_of_lt_of_le hx.2 (le_of_lt hy))).differentiableAt.differentiableWithinAt
        · intro x hx
          rw [interior_Icc] at hx
          rw [(hderiv x (lt_of_lt_of_le hx.2 (le_of_lt hy))).deriv]
          have hx0 : 0 ≤ x := le_of_lt hx.1
          positivity
      rw [← hg0]
      exact hmono (Set.left_mem_Icc.mpr hy0) (Set.right_mem_Icc.mpr hy0) hy0
    · -- On `[y, 0] ⊆ (-∞, 3)`, `g' ≤ 0`, so `g 0 ≤ g y`
      have hanti : AntitoneOn g (Set.Icc y 0) := by
        refine antitoneOn_of_deriv_nonpos (convex_Icc y 0) ?_ ?_ ?_
        · intro x hx
          exact (hderiv x (lt_of_le_of_lt hx.2 (by norm_num))).continuousAt.continuousWithinAt
        · intro x hx
          rw [interior_Icc] at hx
          exact (hderiv x (lt_of_lt_of_le hx.2 (by norm_num))).differentiableAt.differentiableWithinAt
        · intro x hx
          rw [interior_Icc] at hx
          rw [(hderiv x (lt_of_lt_of_le hx.2 (by norm_num))).deriv]
          have hx3 : x ^ 3 ≤ 0 := by nlinarith [hx.2, sq_nonneg x]
          have hnum : 2 * x ^ 3 * Real.exp (-x) ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt (Real.exp_pos _))
          exact div_nonpos_of_nonpos_of_nonneg hnum (sq_nonneg _)
      rw [← hg0]
      exact hanti (Set.left_mem_Icc.mpr (le_of_lt hy0)) (Set.right_mem_Icc.mpr (le_of_lt hy0)) (le_of_lt hy0)
  have hden_pos : 0 < 6 - 2 * y := by linarith
  have hfrac_eq : (6 + 4 * y + y ^ 2) / (6 - 2 * y) = 1 + y + y ^ 2 / (2 * (1 - y / 3)) := by
    rw [show 2 * (1 - y / 3) = (6 - 2 * y) / 3 by ring, div_div_eq_mul_div,
      div_eq_iff hden_pos.ne', add_mul, add_mul, div_mul_cancel₀ _ hden_pos.ne']
    ring
  rw [← hfrac_eq]
  have hmul := mul_le_mul_of_nonneg_left hg_ge_one (le_of_lt (Real.exp_pos y))
  dsimp [g] at hmul
  rw [mul_one, ← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul] at hmul
  exact hmul

/-! ### Cesàro stability subsequence lemma (for Theorem 2 weak duality) -/

/-- If `a : ℕ → ℝ` is nonnegative and has finite `limsup` Cesàro average, then `a(t) / t` comes
arbitrarily close to `0` along arbitrarily large `t`. -/
theorem exists_small_ratio_of_avg_limsup_lt_top {a : ℕ → ℝ}
    (ha_nonneg : ∀ t, 0 ≤ a t)
    (hbdd : Filter.limsup
      (fun t : ℕ => (((1 : ℝ) / (t : ℝ)) * ∑ τ ∈ Finset.range t, a τ : EReal))
      Filter.atTop < ⊤)
    {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ t : ℕ, N ≤ t ∧ 0 < t ∧ a t / (t : ℝ) < ε := by
  by_contra hnot
  push Not at hnot
  -- Extract a finite bound `C` on the `limsup`
  obtain ⟨C, hC_lt⟩ : ∃ C : ℝ, Filter.limsup
      (fun t : ℕ => (((1 : ℝ) / (t : ℝ)) * ∑ τ ∈ Finset.range t, a τ : EReal))
      Filter.atTop < (C : EReal) := by
    cases hval : Filter.limsup
        (fun t : ℕ => (((1 : ℝ) / (t : ℝ)) * ∑ τ ∈ Finset.range t, a τ : EReal))
        Filter.atTop with
    | bot => exact ⟨1, EReal.bot_lt_coe 1⟩
    | top => exact absurd hval (ne_of_lt hbdd)
    | coe x => exact ⟨x + 1, EReal.coe_lt_coe_iff.mpr (by linarith)⟩
  have hev : ∀ᶠ t : ℕ in Filter.atTop,
      ((1 : ℝ) / (t : ℝ)) * ∑ τ ∈ Finset.range t, a τ < C := by
    have h := Filter.eventually_lt_of_limsup_lt hC_lt
    filter_upwards [h] with t ht
    exact EReal.coe_lt_coe_iff.mp ht
  obtain ⟨t₀, ht₀⟩ := Filter.eventually_atTop.mp hev
  obtain ⟨K, hK⟩ := exists_nat_gt (4 * max C 0 / ε)
  let t : ℕ := max (max t₀ (2 * max N 1 + 2)) (2 * K + 2)
  have ht_ge_t0 : t₀ ≤ t := le_trans (le_max_left _ _) (le_max_left _ _)
  have ht_lt_C : ((1 : ℝ) / (t : ℝ)) * ∑ τ ∈ Finset.range t, a τ < C := ht₀ t ht_ge_t0
  have ht_pos : 0 < t := by omega
  have ht_real_pos : (0 : ℝ) < (t : ℝ) := Nat.cast_pos.mpr ht_pos
  -- Lower bound the sum over `[t / 2, t)`
  have hhalf_ge_N : N ≤ t / 2 := by omega
  have hIco_sub : Finset.Ico (t / 2) t ⊆ Finset.range t := by
    intro τ hτ
    exact Finset.mem_range.mpr (Finset.mem_Ico.mp hτ).2
  have hsum_ge : ∑ τ ∈ Finset.range t, a τ ≥ ∑ τ ∈ Finset.Ico (t / 2) t, a τ :=
    Finset.sum_le_sum_of_subset_of_nonneg hIco_sub (fun τ _ _ => ha_nonneg τ)
  have hterm_ge : ∀ τ ∈ Finset.Ico (t / 2) t, ε * ((t / 2 : ℕ) : ℝ) ≤ a τ := by
    intro τ hτ
    have hτ_ge : t / 2 ≤ τ := (Finset.mem_Ico.mp hτ).1
    have hτ_N : N ≤ τ := le_trans hhalf_ge_N hτ_ge
    have hτ_pos : 0 < τ := by omega
    have hτ_real_pos : (0 : ℝ) < (τ : ℝ) := Nat.cast_pos.mpr hτ_pos
    have h1 : ε ≤ a τ / (τ : ℝ) := hnot τ hτ_N hτ_pos
    have h2 : ε * (τ : ℝ) ≤ a τ := (le_div_iff₀ hτ_real_pos).mp h1
    have h3 : ((t / 2 : ℕ) : ℝ) ≤ (τ : ℝ) := by exact_mod_cast hτ_ge
    exact le_trans (mul_le_mul_of_nonneg_left h3 (le_of_lt hε)) h2
  have hIco_ge : ((t - t / 2 : ℕ) : ℝ) * (ε * ((t / 2 : ℕ) : ℝ)) ≤
      ∑ τ ∈ Finset.Ico (t / 2) t, a τ := by
    calc ((t - t / 2 : ℕ) : ℝ) * (ε * ((t / 2 : ℕ) : ℝ))
        = ∑ _τ ∈ Finset.Ico (t / 2) t, (ε * ((t / 2 : ℕ) : ℝ)) := by simp [Nat.card_Ico]
      _ ≤ ∑ τ ∈ Finset.Ico (t / 2) t, a τ := Finset.sum_le_sum hterm_ge
  have h1 : (t : ℝ) / 2 ≤ ((t - t / 2 : ℕ) : ℝ) := by
    have : t ≤ 2 * (t - t / 2) := by omega
    have hcast : (t : ℝ) ≤ 2 * ((t - t / 2 : ℕ) : ℝ) := by exact_mod_cast this
    linarith
  have h2 : (K : ℝ) ≤ ((t / 2 : ℕ) : ℝ) := by
    have : K ≤ t / 2 := by omega
    exact_mod_cast this
  have hK_gt : 4 * max C 0 < ε * (K : ℝ) := by
    have := (div_lt_iff₀ hε).mp hK
    linarith
  have havg_ge : ((1 : ℝ) / (t : ℝ)) * ∑ τ ∈ Finset.range t, a τ ≥ ε * (K : ℝ) / 2 := by
    have hprod : ((t : ℝ) / 2) * (ε * (K : ℝ)) ≤ ∑ τ ∈ Finset.range t, a τ := by
      have h_inner : ε * (K : ℝ) ≤ ε * ((t / 2 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left h2 (le_of_lt hε)
      have h_mul : ((t : ℝ) / 2) * (ε * (K : ℝ)) ≤
          ((t - t / 2 : ℕ) : ℝ) * (ε * ((t / 2 : ℕ) : ℝ)) :=
        mul_le_mul h1 h_inner (by positivity) (by positivity)
      exact le_trans h_mul (le_trans hIco_ge hsum_ge)
    have := mul_le_mul_of_nonneg_left hprod (by positivity : 0 ≤ (1 : ℝ) / (t : ℝ))
    have heq : (1 : ℝ) / (t : ℝ) * ((t : ℝ) / 2 * (ε * (K : ℝ))) = ε * (K : ℝ) / 2 := by
      field_simp [ht_real_pos.ne']
    linarith
  have hC_le : C ≤ max C 0 := le_max_left C 0
  linarith [le_max_right C 0]

end LifoBackpressure.Routine
