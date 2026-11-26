import Statements.SystemModel

/-!
# Statements for Theorem 3 (`thm:prob_multi_con`): Exponential Attraction of Queue Backlogs

Formalizes Theorem 3 of `arXiv:1008.4895v2` (Section VI-C, lines 553-570; companion proof in
`references/0904.3795v1/delay_reduction_tr_v8_Markovian.tex`).
-/

namespace LifoBackpressure.Statements

open Filter MeasureTheory

/-- Time-average probability `P^(r)(D, offset)` from Eq. (14) that at least one queue `j`
deviates from `γ*_Vj` by strictly more than `D + offset`. -/
noncomputable def deviationProb {M : NetworkModel} {Ω : Type} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {proc : M.MarkovProcess Ω μ}
    (pol : M.Policy proc) (γstar : Fin M.r → ℝ) (D offset : ℝ) : EReal :=
  Filter.limsup
    (fun t : ℕ =>
      (((1 : ℝ) / (t : ℝ)) *
        ∑ τ ∈ Finset.range t,
          (μ {ω | ∃ j : Fin M.r, D + offset < |pol.queue τ ω j - γstar j|}).toReal : EReal))
    Filter.atTop

/-- Paper Theorem 3 (`thm:prob_multi_con`): Exponential attraction of the Backpressure queue
vector to the unique dual optimum `γ*_V` under `η`-slackness and the `V`-independent polyhedral
dual growth condition `g(γ*_V) ≥ g(γ) + L ‖γ*_V - γ‖`. Constants `D, K, c* > 0` are independent
of `V ≥ 1` and `m ≥ 0`. -/
def Theorem3Statement : Prop :=
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
            ∀ m : ℝ, 0 ≤ m →
              deviationProb pol γstar D (K * m) ≤ ((cstar * Real.exp (-m) : ℝ) : EReal)

end LifoBackpressure.Statements
