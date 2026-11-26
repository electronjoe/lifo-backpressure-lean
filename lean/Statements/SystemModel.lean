import Prelude

/-!
# Shared System Model, Backpressure Algorithm, and Dual Problem

Formalizes Sections III–V of Huang, Moeller, Neely, and Krishnamachari (`arXiv:1008.4895v2`,
lines 280-467): finite-state irreducible aperiodic Markovian network state `S(t)`, compact
feasible action sets `X^(s)`, continuous uniformly bounded cost/traffic/service functions,
`η`-slackness, queueing dynamics (Eq. 3), queue stability (Eq. 4), time-average cost (Eq. 5),
Backpressure action selection (Eq. 6), and the deterministic dual function `g(γ)` (Eq. 10).
-/

namespace LifoBackpressure.Statements

open Filter MeasureTheory

/-- Matrix power `P^n` of a transition kernel `P : State → State → ℝ` on a finite state space. -/
def matPow {State : Type*} [Fintype State] [DecidableEq State]
    (P : State → State → ℝ) : ℕ → State → State → ℝ
  | 0, s, s' => if s = s' then 1 else 0
  | n + 1, s, s' => ∑ u, matPow P n s u * P u s'

/-- A finite-state Markov transition kernel is irreducible if every state can reach every
state in finitely many positive steps with positive probability. -/
def Irreducible {State : Type*} [Fintype State] [DecidableEq State]
    (P : State → State → ℝ) : Prop :=
  ∀ s s', ∃ n : ℕ, 0 < n ∧ 0 < matPow P n s s'

/-- A finite-state Markov transition kernel is aperiodic if the greatest common divisor of
the positive return times of each state is `1`. -/
def Aperiodic {State : Type*} [Fintype State] [DecidableEq State]
    (P : State → State → ℝ) : Prop :=
  ∀ s : State, ∀ d : ℕ, (∀ n : ℕ, 0 < n → 0 < matPow P n s s → d ∣ n) → d = 1

/-- Stochastic network optimization model from Section III of `arXiv:1008.4895v2`. -/
structure NetworkModel where
  /-- Finite set of network states `S = {s_1, ..., s_M}`. -/
  State : Type
  [stateFintype : Fintype State]
  [stateDecEq : DecidableEq State]
  [stateNonempty : Nonempty State]
  /-- Number of queues `r ≥ 1`. -/
  r : ℕ
  hr : 0 < r
  /-- One-step transition probabilities of the Markov chain `S(t)`. -/
  P : State → State → ℝ
  P_nonneg : ∀ s s', 0 ≤ P s s'
  P_sum_one : ∀ s, ∑ s', P s s' = 1
  P_irreducible : Irreducible P
  P_aperiodic : Aperiodic P
  /-- Steady-state distribution `π_s > 0`. -/
  π : State → ℝ
  π_pos : ∀ s, 0 < π s
  π_sum_one : ∑ s, π s = 1
  π_stationary : ∀ s', ∑ s, π s * P s s' = π s'
  /-- Feasible compact nonempty action set `X^(s)` for each network state `s`. -/
  Action : State → Type
  [actionTop : ∀ s, TopologicalSpace (Action s)]
  [actionCompact : ∀ s, CompactSpace (Action s)]
  [actionNonempty : ∀ s, Nonempty (Action s)]
  /-- Instantaneous cost `f(s, x) ∈ [0, δ_max]`. -/
  cost : (s : State) → Action s → ℝ
  /-- Traffic generated to queue `j`: `A_j(s, x) ∈ [0, δ_max]`. -/
  arrival : (s : State) → Action s → Fin r → ℝ
  /-- Service allocated to queue `j`: `μ_j(s, x) ∈ [0, δ_max]`. -/
  service : (s : State) → Action s → Fin r → ℝ
  cost_cont : ∀ s, Continuous (cost s)
  arrival_cont : ∀ s j, Continuous (fun x => arrival s x j)
  service_cont : ∀ s j, Continuous (fun x => service s x j)
  /-- Uniform upper bound `δ_max ∈ (0, ∞)`. -/
  δmax : ℝ
  hδmax : 0 < δmax
  cost_nonneg : ∀ s x, 0 ≤ cost s x
  cost_le : ∀ s x, cost s x ≤ δmax
  arrival_nonneg : ∀ s x j, 0 ≤ arrival s x j
  arrival_le : ∀ s x j, arrival s x j ≤ δmax
  service_nonneg : ∀ s x j, 0 ≤ service s x j
  service_le : ∀ s x j, service s x j ≤ δmax

attribute [instance] NetworkModel.stateFintype NetworkModel.stateDecEq NetworkModel.stateNonempty
attribute [instance] NetworkModel.actionTop NetworkModel.actionCompact NetworkModel.actionNonempty

namespace NetworkModel

/-- The `η`-slackness feasibility condition (Eq. 2): there exists a stationary randomized
policy with strict negative expected drift `-η < 0` on every queue. -/
def HasSlackness (M : NetworkModel) (η : ℝ) : Prop :=
  0 < η ∧ ∃ (m : ℕ) (x : (s : M.State) → Fin m → M.Action s) (θ : M.State → Fin m → ℝ),
    (∀ s k, 0 ≤ θ s k) ∧
    (∀ s, ∑ k, θ s k = 1) ∧
    ∀ j : Fin M.r,
      ∑ s, M.π s * ∑ k, θ s k * (M.arrival s (x s k) j - M.service s (x s k) j) ≤ -η

/-- One-step queue backlog recursion (Eq. 3): `q_j(t+1) = max(q_j(t) - μ_j(t), 0) + A_j(t)`. -/
def queueNext {r : ℕ} (q μ A : Fin r → ℝ) : Fin r → ℝ :=
  fun j => max (q j - μ j) 0 + A j

/-- Euclidean distance `‖a - b‖₂` on `Fin r → ℝ`. -/
noncomputable def eucDist {r : ℕ} (a b : Fin r → ℝ) : ℝ :=
  Real.sqrt (∑ j : Fin r, (a j - b j) ^ 2)

/-- Single-state dual function `g_s(V, γ)` from Eq. (10). -/
noncomputable def dualState (M : NetworkModel) (V : ℝ) (s : M.State) (γ : Fin M.r → ℝ) : ℝ :=
  ⨅ x : M.Action s, (V * M.cost s x + ∑ j : Fin M.r, γ j * (M.arrival s x j - M.service s x j))

/-- Full dual function `g(V, γ) = ∑_s π_s g_s(V, γ)` (Eq. 10). -/
noncomputable def dual (M : NetworkModel) (V : ℝ) (γ : Fin M.r → ℝ) : ℝ :=
  ∑ s : M.State, M.π s * M.dualState V s γ

/-- `γ*` is an optimal solution of the dual problem (Eq. 9): `γ* ⪰ 0` and `g(γ*) ≥ g(γ)` for all `γ ⪰ 0`. -/
def IsDualOpt (M : NetworkModel) (V : ℝ) (γstar : Fin M.r → ℝ) : Prop :=
  (∀ j, 0 ≤ γstar j) ∧ ∀ γ : Fin M.r → ℝ, (∀ j, 0 ≤ γ j) → M.dual V γ ≤ M.dual V γstar

/-- `γ*` is the unique optimal solution of the dual problem (Eq. 9). -/
def IsUniqueDualOpt (M : NetworkModel) (V : ℝ) (γstar : Fin M.r → ℝ) : Prop :=
  M.IsDualOpt V γstar ∧ ∀ γ : Fin M.r → ℝ, M.IsDualOpt V γ → γ = γstar

/-- Polyhedral linear-growth condition on the dual function `g` (Eq. 12 / Eq. 15). -/
def DualPolyhedral (M : NetworkModel) (V : ℝ) (γstar : Fin M.r → ℝ) (L : ℝ) : Prop :=
  0 < L ∧ ∀ γ : Fin M.r → ℝ, (∀ j, 0 ≤ γ j) →
    M.dual V γ + L * eucDist γstar γ ≤ M.dual V γstar

/-- A discrete-time Markov process `S(t)` on a probability space `(Ω, μ)` with transition kernel `M.P`. -/
structure MarkovProcess (M : NetworkModel) (Ω : Type) [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] where
  S : ℕ → Ω → M.State
  measurable_S : ∀ t s, MeasurableSet {ω | S t ω = s}
  markov : ∀ (t : ℕ) (h : Fin (t + 1) → M.State) (s' : M.State),
    μ {ω | (∀ i : Fin (t + 1), S i ω = h i) ∧ S (t + 1) ω = s'} =
    μ {ω | ∀ i : Fin (t + 1), S i ω = h i} * ENNReal.ofReal (M.P (h ⟨t, Nat.lt_succ_self t⟩) s')

/-- A feasible action-choosing policy on a realization `proc` of `S(t)`. -/
structure Policy (M : NetworkModel) {Ω : Type} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (proc : M.MarkovProcess Ω μ) where
  act : (t : ℕ) → (ω : Ω) → M.Action (proc.S t ω)
  measurable_cost : ∀ t, Measurable (fun ω => M.cost (proc.S t ω) (act t ω))
  measurable_arrival : ∀ t j, Measurable (fun ω => M.arrival (proc.S t ω) (act t ω) j)
  measurable_service : ∀ t j, Measurable (fun ω => M.service (proc.S t ω) (act t ω) j)

/-- Queue backlog process `q(t)` induced by a policy `pol`, starting from `q(0) = 0` (Eq. 3). -/
def Policy.queue {M : NetworkModel} {Ω : Type} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {proc : M.MarkovProcess Ω μ}
    (pol : M.Policy proc) : ℕ → Ω → (Fin M.r → ℝ)
  | 0, _ => fun _ => 0
  | t + 1, ω =>
    queueNext (pol.queue t ω)
      (M.service (proc.S t ω) (pol.act t ω))
      (M.arrival (proc.S t ω) (pol.act t ω))

/-- Expected time-average total queue backlog (Eq. 4), valued in `EReal`. -/
noncomputable def Policy.avgBacklog {M : NetworkModel} {Ω : Type} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {proc : M.MarkovProcess Ω μ}
    (pol : M.Policy proc) : EReal :=
  Filter.limsup
    (fun t : ℕ =>
      (((1 : ℝ) / (t : ℝ)) *
        ∑ τ ∈ Finset.range t, ∑ j : Fin M.r, ∫ ω, pol.queue τ ω j ∂μ : EReal))
    Filter.atTop

/-- A policy is stable if its expected time-average total backlog is finite (Eq. 4). -/
def Policy.IsStable {M : NetworkModel} {Ω : Type} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {proc : M.MarkovProcess Ω μ}
    (pol : M.Policy proc) : Prop :=
  pol.avgBacklog < ⊤

/-- Expected time-average cost `f_av^Π` (Eq. 5), valued in `EReal`. -/
noncomputable def Policy.avgCost {M : NetworkModel} {Ω : Type} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {proc : M.MarkovProcess Ω μ}
    (pol : M.Policy proc) : EReal :=
  Filter.limsup
    (fun t : ℕ =>
      (((1 : ℝ) / (t : ℝ)) *
        ∑ τ ∈ Finset.range t, ∫ ω, M.cost (proc.S τ ω) (pol.act τ ω) ∂μ : EReal))
    Filter.atTop

/-- Optimal time-average cost `f_av^*` over all stable feasible policies (Problem P1). -/
noncomputable def optCost (M : NetworkModel) {Ω : Type} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (proc : M.MarkovProcess Ω μ) : EReal :=
  ⨅ (pol : M.Policy proc) (_ : pol.IsStable), pol.avgCost

/-- Backpressure action selection (Eq. 6): at every slot `t`, given `S(t) = s` and `q(t)`,
the chosen action maximizes `-V f(s, x) + ∑_j q_j(t) (μ_j(s, x) - A_j(s, x))` over `X^(s)`.
A deterministic state-backlog decision rule `choice` induces a measurable Backpressure policy. -/
def IsBackpressureRule (M : NetworkModel) (V : ℝ)
    (choice : (s : M.State) → (Fin M.r → ℝ) → M.Action s) : Prop :=
  ∀ (s : M.State) (q : Fin M.r → ℝ) (x : M.Action s),
    -V * M.cost s x + ∑ j : Fin M.r, q j * (M.service s x j - M.arrival s x j) ≤
    -V * M.cost s (choice s q) +
      ∑ j : Fin M.r, q j * (M.service s (choice s q) j - M.arrival s (choice s q) j)

/-- Deterministic queue trajectory driven by a state-backlog rule `choice` along a path of states. -/
def bpQueuePath (M : NetworkModel) (choice : (s : M.State) → (Fin M.r → ℝ) → M.Action s)
    (path : ℕ → M.State) : ℕ → (Fin M.r → ℝ)
  | 0 => fun _ => 0
  | t + 1 =>
    let q := bpQueuePath M choice path t
    let s := path t
    let x := choice s q
    queueNext q (M.service s x) (M.arrival s x)

/-- Predicate stating that a feasible policy `pol` follows the Backpressure rule `choice`
(same queue trajectory under both FIFO and LIFO queueing disciplines). -/
def Policy.FollowsBackpressure {M : NetworkModel} {Ω : Type} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {proc : M.MarkovProcess Ω μ}
    (V : ℝ) (pol : M.Policy proc) : Prop :=
  ∃ choice : (s : M.State) → (Fin M.r → ℝ) → M.Action s,
    M.IsBackpressureRule V choice ∧
    ∀ t ω, pol.act t ω = choice (proc.S t ω) (pol.queue t ω)

end NetworkModel

end LifoBackpressure.Statements
