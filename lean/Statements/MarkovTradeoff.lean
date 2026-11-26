import Statements.SystemModel

/-!
# Statements for Theorem 2 (`theorem:qla-markovian`): `[O(1/V), O(V)]` Tradeoff Under Markov Dynamics

Formalizes Theorem 2 of `arXiv:1008.4895v2` (Section VI-C, lines 540-549; companion proof in
`references/1008.0200v1/pure-qla-markovian-v9.tex`).
-/

namespace LifoBackpressure.Statements

open Filter MeasureTheory

/-- Paper Theorem 2 (`theorem:qla-markovian`): Under a finite-state irreducible aperiodic
Markovian network state process `S(t)` and `η`-slackness, Backpressure (with either FIFO or
LIFO queueing discipline) achieves an `[O(1/V), O(V)]` utility-delay tradeoff uniformly in
`V ≥ 1`, with constants `C_cost, C_q0, C_q1` independent of `V`. -/
def Theorem2Statement : Prop :=
  ∀ (M : NetworkModel) (η : ℝ),
    M.HasSlackness η →
    ∃ (C_cost C_q0 C_q1 : ℝ), 0 ≤ C_cost ∧ 0 ≤ C_q0 ∧ 0 ≤ C_q1 ∧
      ∀ (V : ℝ), 1 ≤ V →
        ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (proc : M.MarkovProcess Ω μ) (pol : M.Policy proc),
          pol.FollowsBackpressure V →
          pol.IsStable ∧
          M.optCost proc ≤ pol.avgCost ∧
          pol.avgCost ≤ M.optCost proc + ((C_cost / V : ℝ) : EReal) ∧
          pol.avgBacklog ≤ ((C_q0 + C_q1 * V : ℝ) : EReal)

end LifoBackpressure.Statements
