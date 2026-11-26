import Statements.ExponentialAttraction
import Proofs.MarkovTradeoff
import Routine.MarkovMixing
import Routine.BackpressureDrift

/-!
# Proof of Theorem 3 (`thm:prob_multi_con`): Exponential Attraction of Queue Backlogs

Proves `LifoBackpressure.Statements.Theorem3Statement` following Theorem 1 and Appendices A–B of
companion paper `arXiv:0904.3795v1` (`delay_reduction_tr_v8_Markovian.tex`) and
`lamport/thm-prob-multi-con.md`, reusing `Routine/MarkovMixing.lean` (`exists_geometric_mixing`,
`exists_convergent_interval`), `Routine/BackpressureDrift.lean` (`sum_dist_sq_drift`,
`sqrt_sum_sq_step_le`, `euc_triangle`, `exp_le_quad_div`), and the finite-cylinder Markov
expectation infrastructure from `Proofs/MarkovTradeoff.lean`.
-/

namespace LifoBackpressure.Proofs

open Filter MeasureTheory Classical
open LifoBackpressure.Statements
open LifoBackpressure.Routine

/-! ### Multi-step Markov path weights and conditional expectations -/

section MultiStepMarkov

/-- Non-dependent `Fin.cons` for state trajectories `(s₀, u 0, ..., u (k - 1))`. -/
def consState {S : Type*} (s₀ : S) {k : ℕ} (u : Fin k → S) : Fin (k + 1) → S :=
  Fin.cons (α := fun _ => S) s₀ u

/-- Non-dependent `Fin.snoc` for state trajectories `(v 0, ..., v (k - 1), w)`. -/
def snocState {S : Type*} {k : ℕ} (v : Fin k → S) (w : S) : Fin (k + 1) → S :=
  Fin.snoc (α := fun _ => S) v w

private lemma consState_zero {S : Type*} (s₀ : S) {k : ℕ} (u : Fin k → S) :
    consState s₀ u 0 = s₀ := rfl

private lemma consState_succ {S : Type*} (s₀ : S) {k : ℕ} (u : Fin k → S) (i : Fin k) :
    consState s₀ u i.succ = u i := rfl

private lemma snocState_castSucc {S : Type*} {k : ℕ} (v : Fin k → S) (w : S) (i : Fin k) :
    snocState v w i.castSucc = v i := by
  simp [snocState, Fin.snoc_castSucc]

private lemma snocState_last {S : Type*} {k : ℕ} (v : Fin k → S) (w : S) :
    snocState v w (Fin.last k) = w := by
  simp [snocState, Fin.snoc_last]

private lemma consState_snoc {S : Type*} (s₀ : S) {k : ℕ} (v : Fin k → S) (w : S) :
    consState s₀ (snocState v w) = snocState (consState s₀ v) w := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change s₀ = snocState (consState s₀ v) w (0 : Fin (k + 1)).castSucc
    rw [snocState_castSucc, consState_zero]
  · refine Fin.lastCases ?_ (fun l => ?_) j
    · change snocState v w (Fin.last k) = snocState (consState s₀ v) w (Fin.last (k + 1))
      rw [snocState_last, snocState_last]
    · change snocState v w l.castSucc = snocState (consState s₀ v) w (l.succ).castSucc
      rw [snocState_castSucc, snocState_castSucc, consState_succ]

/-- Final state of the `(k + 1)`-state trajectory `(s₀, u 0, ..., u (k - 1))`. -/
def lastState {S : Type*} (s₀ : S) {k : ℕ} (u : Fin k → S) : S :=
  consState s₀ u (Fin.last k)

/-- Conditional probability weight of a `k`-step future trajectory `u : Fin k → S`
starting from `s₀` under transition kernel `P`. -/
def pathWeight {S : Type*} (P : S → S → ℝ) : (k : ℕ) → S → (Fin k → S) → ℝ
  | 0, _, _ => 1
  | k + 1, s₀, u =>
      pathWeight P k s₀ (Fin.init u) * P (lastState s₀ (Fin.init u)) (u (Fin.last k))

private def snocEquiv (S : Type*) (k : ℕ) : ((Fin k → S) × S) ≃ (Fin (k + 1) → S) where
  toFun p := snocState p.1 p.2
  invFun u := (Fin.init u, u (Fin.last k))
  left_inv p := by
    rcases p with ⟨v, w⟩
    ext i
    · simp [Fin.init, snocState_castSucc]
    · simp [snocState_last]
  right_inv u := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [snocState_last]
    · simp [Fin.init, snocState_castSucc]

lemma pathWeight_snoc {S : Type*} (P : S → S → ℝ) (k : ℕ) (s₀ : S) (v : Fin k → S) (w : S) :
    pathWeight P (k + 1) s₀ (snocState v w) = pathWeight P k s₀ v * P (lastState s₀ v) w := by
  have hinit : Fin.init (snocState v w) = v := by
    ext i; simp [Fin.init, snocState_castSucc]
  simp [pathWeight, hinit, snocState_last]

lemma pathWeight_nonneg {S : Type*} {P : S → S → ℝ} (hP : ∀ s s', 0 ≤ P s s') :
    ∀ (k : ℕ) (s₀ : S) (u : Fin k → S), 0 ≤ pathWeight P k s₀ u
  | 0, _, _ => zero_le_one
  | k + 1, s₀, u => mul_nonneg (pathWeight_nonneg hP k s₀ (Fin.init u)) (hP _ _)

lemma pathWeight_sum_one {S : Type*} [Fintype S] {P : S → S → ℝ} (hsum : ∀ s, ∑ s', P s s' = 1) :
    ∀ (k : ℕ) (s₀ : S), ∑ u : Fin k → S, pathWeight P k s₀ u = 1
  | 0, _ => by simp [pathWeight]
  | k + 1, s₀ => by
    rw [← Equiv.sum_comp (snocEquiv S k), Fintype.sum_prod_type]
    simp only [snocEquiv, Equiv.coe_fn_mk, pathWeight_snoc]
    simp_rw [← Finset.mul_sum, hsum, mul_one]
    exact pathWeight_sum_one hsum k s₀

/-- Marginal distribution of the `τ`-th state `(consState s₀ u) τ` under `pathWeight P k s₀`
equals the `τ`-step transition probability `Routine.matPow P τ s₀`. -/
lemma pathWeight_marginal {S : Type*} [Fintype S] [DecidableEq S]
    {P : S → S → ℝ} (hsum : ∀ s, ∑ s', P s s' = 1) :
    ∀ (k : ℕ) (s₀ : S) (τ : Fin (k + 1)) (s' : S),
      ∑ u : Fin k → S, pathWeight P k s₀ u * (if consState s₀ u τ = s' then (1 : ℝ) else 0) =
        Routine.matPow P τ.val s₀ s'
  | 0, s₀, τ, s' => by
    have hτ : τ = 0 := Fin.eq_zero τ
    subst hτ
    simp only [pathWeight, consState_zero, Routine.matPow, one_mul]
    rw [Fintype.sum_unique]
    by_cases h : s₀ = s' <;> simp [h]
  | k + 1, s₀, τ, s' => by
    rw [← Equiv.sum_comp (snocEquiv S k), Fintype.sum_prod_type]
    simp only [snocEquiv, Equiv.coe_fn_mk, pathWeight_snoc, consState_snoc]
    refine Fin.lastCases ?_ (fun i => ?_) τ
    · -- `τ = Fin.last (k + 1)`
      simp only [snocState_last, mul_ite, mul_one, mul_zero]
      have hinner : ∀ v : Fin k → S,
          ∑ w : S, (if w = s' then pathWeight P k s₀ v * P (lastState s₀ v) w else 0) =
            pathWeight P k s₀ v * P (lastState s₀ v) s' := by
        intro v
        rw [Finset.sum_ite_eq' Finset.univ s']
        simp
      simp_rw [hinner]
      have hsplit : ∀ v : Fin k → S,
          pathWeight P k s₀ v * P (lastState s₀ v) s' =
            ∑ a : S, (pathWeight P k s₀ v * (if lastState s₀ v = a then (1 : ℝ) else 0)) * P a s' := by
        intro v
        rw [Finset.sum_eq_single (lastState s₀ v)]
        · simp
        · intro a _ hne; simp [hne.symm]
        · intro h; exact absurd (Finset.mem_univ _) h
      simp_rw [hsplit]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul]
      have hih : ∀ a : S,
          ∑ v : Fin k → S, pathWeight P k s₀ v * (if lastState s₀ v = a then (1 : ℝ) else 0) =
            Routine.matPow P k s₀ a := fun a =>
        pathWeight_marginal hsum k s₀ (Fin.last k) a
      simp_rw [hih]
      rfl
    · -- `τ = i.castSucc`
      simp only [snocState_castSucc]
      have hpull : ∀ v : Fin k → S,
          ∑ w : S, pathWeight P k s₀ v * P (lastState s₀ v) w *
              (if consState s₀ v i = s' then (1 : ℝ) else 0) =
            pathWeight P k s₀ v * (if consState s₀ v i = s' then (1 : ℝ) else 0) *
              (∑ w : S, P (lastState s₀ v) w) := by
        intro v
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun w _ => by ring)
      simp_rw [hpull, hsum, mul_one]
      exact pathWeight_marginal hsum k s₀ i s'

end MultiStepMarkov

/-- Exact multi-step Markov expectation formula over cylinder histories `H_t` and `k` future states
`(S(t+1), ..., S(t+k))`. -/
lemma integral_history_future_eq {M : NetworkModel} {Ω : Type} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (proc : M.MarkovProcess Ω μ) (t : ℕ) :
    ∀ (k : ℕ) (G : (Fin (t + 1) → M.State) → (Fin k → M.State) → ℝ),
      ∫ ω, G (fun i => proc.S i ω) (fun j => proc.S (t + 1 + j.val) ω) ∂μ =
        ∑ h : Fin (t + 1) → M.State, (μ (markovCyl proc t h)).toReal *
          ∑ u : Fin k → M.State, pathWeight M.P k (h (Fin.last t)) u * G h u
  | 0, G => by
    have hfun : (fun ω => G (fun i => proc.S i ω) (fun j : Fin 0 => proc.S (t + 1 + j.val) ω)) =
        fun ω => G (fun i => proc.S i ω) Fin.elim0 := by
      funext ω
      congr 1
      ext j
      exact Fin.elim0 j
    rw [hfun, (integral_history_eq_sum proc t (fun h => G h Fin.elim0)).2]
    refine Finset.sum_congr rfl (fun h _ => ?_)
    have hsum : ∑ u : Fin 0 → M.State, pathWeight M.P 0 (h (Fin.last t)) u * G h u = G h Fin.elim0 := by
      rw [Fintype.sum_eq_single Fin.elim0]
      · simp [pathWeight]
      · intro u hne; exact absurd (Subsingleton.elim u Fin.elim0) hne
    rw [hsum]
  | k + 1, G => by
    let Gstep : (Fin (t + k + 1) → M.State) → M.State → ℝ := fun hist w =>
      G (fun i => hist ⟨i.val, by omega⟩)
        (snocState (fun j : Fin k => hist ⟨t + 1 + j.val, by omega⟩) w)
    have hrewrite : (fun ω => G (fun i => proc.S i ω) (fun j : Fin (k + 1) => proc.S (t + 1 + j.val) ω)) =
        fun ω => Gstep (fun i : Fin (t + k + 1) => proc.S i ω) (proc.S (t + k + 1) ω) := by
      funext ω
      dsimp [Gstep]
      congr 1
      ext j
      refine Fin.lastCases ?_ (fun l => ?_) j
      · simp [snocState_last]; congr 1; omega
      · simp [snocState_castSucc]
    rw [hrewrite, integral_history_next_eq proc (t + k) Gstep]
    let G' : (Fin (t + 1) → M.State) → (Fin k → M.State) → ℝ := fun h v =>
      ∑ w : M.State, M.P (lastState (h (Fin.last t)) v) w * G h (snocState v w)
    have hrewrite2 : (fun ω => ∑ w : M.State, M.P (proc.S (t + k) ω) w *
          Gstep (fun i : Fin (t + k + 1) => proc.S i ω) w) =
        fun ω => G' (fun i => proc.S i ω) (fun j : Fin k => proc.S (t + 1 + j.val) ω) := by
      funext ω
      dsimp [G', Gstep]
      have hlast : lastState (proc.S t ω) (fun j : Fin k => proc.S (t + 1 + j.val) ω) =
          proc.S (t + k) ω := by
        cases k with
        | zero => simp [lastState, consState_zero]
        | succ m =>
          change consState (proc.S t ω) (fun j : Fin (m + 1) => proc.S (t + 1 + j.val) ω)
              (Fin.last m).succ = proc.S (t + (m + 1)) ω
          rw [consState_succ]
          congr 1
          simp [Fin.last]
          omega
      rw [hlast]
    rw [hrewrite2, integral_history_future_eq proc t k G']
    refine Finset.sum_congr rfl (fun h _ => ?_)
    congr 1
    symm
    rw [← Equiv.sum_comp (snocEquiv M.State k), Fintype.sum_prod_type]
    simp only [snocEquiv, Equiv.coe_fn_mk, pathWeight_snoc, G']
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun w _ => by ring)

/-! ### Deterministic multi-step Backpressure trajectory from `(q₀, seq)` -/

/-- One deterministic Backpressure queue update from `(q, s)`. -/
def bpStep (M : NetworkModel) (choice : (s : M.State) → (Fin M.r → ℝ) → M.Action s)
    (q : Fin M.r → ℝ) (s : M.State) : Fin M.r → ℝ :=
  let x := choice s q
  NetworkModel.queueNext q (M.service s x) (M.arrival s x)

/-- Deterministic Backpressure queue after `τ` steps along a finite state sequence `seq : Fin n → M.State`. -/
def bpRun (M : NetworkModel) (choice : (s : M.State) → (Fin M.r → ℝ) → M.Action s)
    (q₀ : Fin M.r → ℝ) {n : ℕ} (seq : Fin n → M.State) : (τ : ℕ) → τ ≤ n → (Fin M.r → ℝ)
  | 0, _ => q₀
  | τ + 1, hτ => bpStep M choice (bpRun M choice q₀ seq τ (Nat.le_of_succ_le hτ)) (seq ⟨τ, hτ⟩)

lemma bpStep_nonneg (M : NetworkModel) (choice : (s : M.State) → (Fin M.r → ℝ) → M.Action s)
    (q : Fin M.r → ℝ) (s : M.State) (j : Fin M.r) :
    0 ≤ bpStep M choice q s j :=
  add_nonneg (le_max_right _ _) (M.arrival_nonneg _ _ _)

lemma bpRun_nonneg (M : NetworkModel) (choice : (s : M.State) → (Fin M.r → ℝ) → M.Action s)
    {q₀ : Fin M.r → ℝ} (hq₀ : ∀ j, 0 ≤ q₀ j) {n : ℕ} (seq : Fin n → M.State) :
    ∀ (τ : ℕ) (hτ : τ ≤ n) (j : Fin M.r), 0 ≤ bpRun M choice q₀ seq τ hτ j
  | 0, _, j => hq₀ j
  | _ + 1, _, j => bpStep_nonneg M choice _ _ j

lemma bpRun_eq_pol_queue {M : NetworkModel} {Ω : Type} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {proc : M.MarkovProcess Ω μ}
    {pol : M.Policy proc} {choice : (s : M.State) → (Fin M.r → ℝ) → M.Action s}
    (hact : ∀ t ω, pol.act t ω = choice (proc.S t ω) (pol.queue t ω))
    (t k : ℕ) (ω : Ω) :
    ∀ (τ : ℕ) (hτ : τ ≤ k + 1),
      bpRun M choice (pol.queue t ω)
        (consState (proc.S t ω) (fun j : Fin k => proc.S (t + 1 + j.val) ω)) τ hτ =
      pol.queue (t + τ) ω
  | 0, _ => by simp [bpRun]
  | τ + 1, hτ => by
    have ih := bpRun_eq_pol_queue hact t k ω τ (Nat.le_of_succ_le hτ)
    have hstate : consState (proc.S t ω) (fun j : Fin k => proc.S (t + 1 + j.val) ω) ⟨τ, hτ⟩ =
        proc.S (t + τ) ω := by
      cases τ with
      | zero => exact consState_zero _ _
      | succ m =>
        change consState (proc.S t ω) (fun j : Fin k => proc.S (t + 1 + j.val) ω)
            (⟨m, by omega⟩ : Fin k).succ = proc.S (t + (m + 1)) ω
        rw [consState_succ]
        dsimp only
        congr 1
        omega
    change bpStep M choice _ _ = _
    rw [ih, hstate]
    have hadd : t + (τ + 1) = (t + τ) + 1 := by omega
    rw [hadd]
    simp only [NetworkModel.Policy.queue, bpStep, hact (t + τ) ω]

lemma eucDist_symm {r : ℕ} (a b : Fin r → ℝ) :
    NetworkModel.eucDist a b = NetworkModel.eucDist b a := by
  unfold NetworkModel.eucDist
  congr 1
  exact Finset.sum_congr rfl (fun j _ => by ring)

lemma eucDist_nonneg {r : ℕ} (a b : Fin r → ℝ) :
    0 ≤ NetworkModel.eucDist a b :=
  Real.sqrt_nonneg _

lemma eucDist_sq {r : ℕ} (a b : Fin r → ℝ) :
    (NetworkModel.eucDist a b) ^ 2 = ∑ j : Fin r, (a j - b j) ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

lemma bpRun_eucDist_le (M : NetworkModel) (choice : (s : M.State) → (Fin M.r → ℝ) → M.Action s)
    {q₀ : Fin M.r → ℝ} (hq₀ : ∀ j, 0 ≤ q₀ j) {n : ℕ} (seq : Fin n → M.State) :
    ∀ (τ : ℕ) (hτ : τ ≤ n),
      NetworkModel.eucDist (bpRun M choice q₀ seq τ hτ) q₀ ≤ (τ : ℝ) * driftBound M
  | 0, _ => by
    simp [bpRun, NetworkModel.eucDist]
  | τ + 1, hτ => by
    have hτ' : τ ≤ n := Nat.le_of_succ_le hτ
    have ih := bpRun_eucDist_le M choice hq₀ seq τ hτ'
    have hstep : NetworkModel.eucDist
        (bpRun M choice q₀ seq (τ + 1) hτ) (bpRun M choice q₀ seq τ hτ') ≤ driftBound M := by
      unfold NetworkModel.eucDist driftBound
      exact sqrt_sum_sq_step_le
        (bpRun_nonneg M choice hq₀ seq τ hτ')
        (fun j => M.service_nonneg _ _ j)
        (fun j => M.arrival_nonneg _ _ j)
        (fun j => M.service_le _ _ j)
        (fun j => M.arrival_le _ _ j)
        (le_of_lt M.hδmax)
    have htri : NetworkModel.eucDist (bpRun M choice q₀ seq (τ + 1) hτ) q₀ ≤
        NetworkModel.eucDist (bpRun M choice q₀ seq (τ + 1) hτ) (bpRun M choice q₀ seq τ hτ') +
        NetworkModel.eucDist (bpRun M choice q₀ seq τ hτ') q₀ :=
      euc_triangle (bpRun M choice q₀ seq (τ + 1) hτ) (bpRun M choice q₀ seq τ hτ') q₀
    push_cast
    linarith

lemma subgradient_dualState_of_bp (M : NetworkModel) {V : ℝ}
    {choice : (s : M.State) → (Fin M.r → ℝ) → M.Action s}
    (hbp : M.IsBackpressureRule V choice) (s : M.State) (q γ : Fin M.r → ℝ) :
    M.dualState V s γ - M.dualState V s q ≤
      ∑ j : Fin M.r, (γ j - q j) *
        (M.arrival s (choice s q) j - M.service s (choice s q) j) := by
  have heq := dualState_eq_of_bp M hbp s q
  have hle := dualState_le M V s γ (choice s q)
  have hsub : (V * M.cost s (choice s q) +
        ∑ j : Fin M.r, γ j * (M.arrival s (choice s q) j - M.service s (choice s q) j)) -
      (V * M.cost s (choice s q) +
        ∑ j : Fin M.r, q j * (M.arrival s (choice s q) j - M.service s (choice s q) j)) =
      ∑ j : Fin M.r, (γ j - q j) * (M.arrival s (choice s q) j - M.service s (choice s q) j) := by
    rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  linarith

/-! ### Telescoping sum helper for shift `T` -/

private lemma sum_range_shift_sub (a : ℕ → ℝ) (T : ℕ) :
    ∀ N : ℕ,
      ∑ t ∈ Finset.range N, (a (t + T) - a t) =
        (∑ t ∈ Finset.range T, a (N + t)) - (∑ t ∈ Finset.range T, a t)
  | 0 => by simp
  | N + 1 => by
    rw [Finset.sum_range_succ, sum_range_shift_sub a T N]
    have hshift : (∑ t ∈ Finset.range T, a (N + t)) + a (N + T) =
        (∑ t ∈ Finset.range T, a (N + 1 + t)) + a N := by
      have h1 : ∑ t ∈ Finset.range (T + 1), a (N + t) =
          (∑ t ∈ Finset.range T, a (N + t)) + a (N + T) := Finset.sum_range_succ _ T
      have h2 : ∑ t ∈ Finset.range (T + 1), a (N + t) =
          (∑ t ∈ Finset.range T, a (N + (t + 1))) + a (N + 0) := Finset.sum_range_succ' _ T
      have h3 : ∑ t ∈ Finset.range T, a (N + (t + 1)) = ∑ t ∈ Finset.range T, a (N + 1 + t) :=
        Finset.sum_congr rfl (fun t _ => by congr 1; omega)
      rw [h3, add_zero] at h2
      linarith
    linarith

/-! ### Pointwise `T`-step exponential Lyapunov drift (Steps 1–4 of Theorem 3) -/

private lemma pointwise_exp_drift (M : NetworkModel) {L V : ℝ} (hL_pos : 0 < L)
    {T : ℕ} (hT_pos : 0 < T)
    (hT_conv : ∀ s₀ : M.State,
      ∑ s', |M.π s' - (1 / (T : ℝ)) * ∑ τ ∈ Finset.range T, Routine.matPow M.P τ s₀ s'| ≤
        L / (2 * driftBound M))
    {γstar : Fin M.r → ℝ} (hγ_nonneg : ∀ j, 0 ≤ γstar j)
    (hpoly : M.DualPolyhedral V γstar L)
    {choice : (s : M.State) → (Fin M.r → ℝ) → M.Action s}
    (hchoice_bp : M.IsBackpressureRule V choice)
    {η_d C_quad D M_step w C_exp : ℝ}
    (hη_d_def : η_d = (T : ℝ) * L / 4)
    (hC_quad_def : C_quad = 2 * (T : ℝ) ^ 2 * (driftBound M) ^ 2)
    (hD_ge_2η : 2 * η_d ≤ D)
    (hC_quad_le : C_quad ≤ 2 * η_d * D)
    (hM_step_def : M_step = (T : ℝ) * driftBound M)
    (hw_pos : 0 < w)
    (hwM_lt3 : w * M_step < 3)
    (hw_quad_eq : (w * M_step) ^ 2 / (2 * (1 - w * M_step / 3)) = w * η_d / 2)
    (hC_exp_def : C_exp = (1 + w * η_d / 2) * Real.exp (2 * w * M_step))
    (q₀ : Fin M.r → ℝ) (hq₀ : ∀ j, 0 ≤ q₀ j) (s₀ : M.State) :
    (∑ u : Fin T → M.State, pathWeight M.P T s₀ u *
        Real.exp (w * max (NetworkModel.eucDist (bpRun M choice q₀ (consState s₀ u) T (Nat.le_succ T)) γstar - D) 0)) -
      Real.exp (w * max (NetworkModel.eucDist q₀ γstar - D) 0) ≤
      C_exp - (w * η_d / 2) * Real.exp (w * max (NetworkModel.eucDist q₀ γstar - D) 0) := by
  have hT_real_pos : (0 : ℝ) < (T : ℝ) := Nat.cast_pos.mpr hT_pos
  have hB_pos : 0 < driftBound M := driftBound_pos M
  have hB_sq : (driftBound M) ^ 2 = (M.r : ℝ) * M.δmax ^ 2 := driftBound_sq M
  have hη_d_pos : 0 < η_d := by rw [hη_d_def]; positivity
  have hM_step_pos : 0 < M_step := by rw [hM_step_def]; positivity
  have hC_exp_pos : 0 < C_exp := by rw [hC_exp_def]; positivity
  let Ytilde : (Fin M.r → ℝ) → ℝ := fun q => max (NetworkModel.eucDist q γstar - D) 0
  let qEnd : (Fin T → M.State) → (Fin M.r → ℝ) := fun u =>
    bpRun M choice q₀ (consState s₀ u) T (Nat.le_succ T)
  let Y0 : ℝ := NetworkModel.eucDist q₀ γstar
  let Yu : (Fin T → M.State) → ℝ := fun u => NetworkModel.eucDist (qEnd u) γstar
  have hY0_nonneg : 0 ≤ Y0 := eucDist_nonneg _ _
  have hYu_nonneg : ∀ u, 0 ≤ Yu u := fun _ => eucDist_nonneg _ _
  have hpw_nonneg : ∀ u, 0 ≤ pathWeight M.P T s₀ u := pathWeight_nonneg M.P_nonneg T s₀
  have hpw_sum : ∑ u : Fin T → M.State, pathWeight M.P T s₀ u = 1 :=
    pathWeight_sum_one M.P_sum_one T s₀
  -- Uniform `M_step` increment bound `|Yu u - Y0| ≤ M_step`
  have hYu_diff : ∀ u : Fin T → M.State, |Yu u - Y0| ≤ M_step := by
    intro u
    have hrun : NetworkModel.eucDist (qEnd u) q₀ ≤ M_step := by
      rw [hM_step_def]
      exact bpRun_eucDist_le M choice hq₀ (consState s₀ u) T (Nat.le_succ T)
    have htri1 : Yu u ≤ NetworkModel.eucDist (qEnd u) q₀ + Y0 :=
      euc_triangle (qEnd u) q₀ γstar
    have htri2 : Y0 ≤ NetworkModel.eucDist q₀ (qEnd u) + Yu u :=
      euc_triangle q₀ (qEnd u) γstar
    rw [eucDist_symm q₀ (qEnd u)] at htri2
    rw [abs_le]
    constructor <;> linarith
  change (∑ u : Fin T → M.State, pathWeight M.P T s₀ u * Real.exp (w * Ytilde (qEnd u))) -
      Real.exp (w * Ytilde q₀) ≤ C_exp - (w * η_d / 2) * Real.exp (w * Ytilde q₀)
  by_cases hlarge : D + M_step ≤ Y0
  · -- Case 1: `Y0 ≥ D + M_step` (quadratic drift → linear negative drift → exponential contraction)
    let Δg : M.State → ℝ := fun s' => M.dualState V s' γstar - M.dualState V s' q₀
    have hΔg_abs : ∀ s', |Δg s'| ≤ driftBound M * Y0 := fun s' => by
      have h := abs_dualState_sub_le M V s' γstar q₀
      have heq : Real.sqrt (∑ j : Fin M.r, (γstar j - q₀ j) ^ 2) = Y0 :=
        eucDist_symm γstar q₀
      rwa [heq] at h
    -- 1a. Pathwise `T`-slot squared distance bound
    have hpath_sq : ∀ u : Fin T → M.State,
        (Yu u) ^ 2 ≤ Y0 ^ 2 + C_quad - 2 * ∑ τ : Fin T, Δg (consState s₀ u τ.castSucc) := by
      intro u
      let seq : Fin (T + 1) → M.State := consState s₀ u
      have hstep_sq : ∀ τ (hτ : τ < T),
          (NetworkModel.eucDist (bpRun M choice q₀ seq (τ + 1) (by omega)) γstar) ^ 2 -
          (NetworkModel.eucDist (bpRun M choice q₀ seq τ (by omega)) γstar) ^ 2 ≤
          2 * (T : ℝ) * (driftBound M) ^ 2 - 2 * Δg (seq ⟨τ, by omega⟩) := by
        intro τ hτ
        let qτ := bpRun M choice q₀ seq τ (by omega)
        let sτ := seq ⟨τ, by omega⟩
        let xτ := choice sτ qτ
        rw [eucDist_sq, eucDist_sq]
        change (∑ j : Fin M.r, (max (qτ j - M.service sτ xτ j) 0 + M.arrival sτ xτ j - γstar j) ^ 2) -
            (∑ j : Fin M.r, (qτ j - γstar j) ^ 2) ≤
            2 * (T : ℝ) * (driftBound M) ^ 2 - 2 * (M.dualState V sτ γstar - M.dualState V sτ q₀)
        have h1 := sum_dist_sq_drift
          (bpRun_nonneg M choice hq₀ seq τ (by omega))
          (fun j => M.service_nonneg sτ xτ j)
          (fun j => M.arrival_nonneg sτ xτ j)
          hγ_nonneg
          (fun j => M.service_le sτ xτ j)
          (fun j => M.arrival_le sτ xτ j)
        have h2 := subgradient_dualState_of_bp M hchoice_bp sτ qτ γstar
        have h3 : |M.dualState V sτ qτ - M.dualState V sτ q₀| ≤ (τ : ℝ) * (driftBound M) ^ 2 := by
          have hlip := abs_dualState_sub_le M V sτ qτ q₀
          have hdist : Real.sqrt (∑ j : Fin M.r, (qτ j - q₀ j) ^ 2) ≤ (τ : ℝ) * driftBound M :=
            bpRun_eucDist_le M choice hq₀ seq τ (by omega)
          have hmul := mul_le_mul_of_nonneg_left hdist (le_of_lt hB_pos)
          have hsq : driftBound M * ((τ : ℝ) * driftBound M) = (τ : ℝ) * (driftBound M) ^ 2 := by ring
          exact le_trans hlip (hsq ▸ hmul)
        have h3_upper : M.dualState V sτ qτ - M.dualState V sτ q₀ ≤ (τ : ℝ) * (driftBound M) ^ 2 :=
          (abs_le.mp h3).2
        have hτ_le : ((τ : ℝ) + 1) ≤ (T : ℝ) := by
          have : τ + 1 ≤ T := hτ
          exact_mod_cast this
        have hconst_le : 2 * (driftBound M) ^ 2 + 2 * (τ : ℝ) * (driftBound M) ^ 2 ≤
            2 * (T : ℝ) * (driftBound M) ^ 2 := by
          nlinarith [sq_nonneg (driftBound M)]
        have hrB : 2 * (M.r : ℝ) * M.δmax ^ 2 = 2 * (driftBound M) ^ 2 := by linarith [hB_sq]
        linarith
      let fsq : ℕ → ℝ := fun τ =>
        if hτ : τ ≤ T then (NetworkModel.eucDist (bpRun M choice q₀ seq τ (by omega)) γstar) ^ 2 else 0
      have htele_sq : ∑ τ : Fin T, (fsq (τ.val + 1) - fsq τ.val) = (Yu u) ^ 2 - Y0 ^ 2 := by
        rw [Fin.sum_univ_eq_sum_range (fun τ => fsq (τ + 1) - fsq τ) T, Finset.sum_range_sub fsq T]
        simp [fsq, Yu, qEnd, Y0, seq, bpRun]
      have hsum_le : ∑ τ : Fin T, (fsq (τ.val + 1) - fsq τ.val) ≤
          ∑ τ : Fin T, (2 * (T : ℝ) * (driftBound M) ^ 2 - 2 * Δg (seq τ.castSucc)) := by
        refine Finset.sum_le_sum (fun τ _ => ?_)
        have h1 : fsq (τ.val + 1) = (NetworkModel.eucDist (bpRun M choice q₀ seq (τ.val + 1) (by omega)) γstar) ^ 2 :=
          dif_pos (by omega)
        have h2 : fsq τ.val = (NetworkModel.eucDist (bpRun M choice q₀ seq τ.val (by omega)) γstar) ^ 2 :=
          dif_pos (by omega)
        rw [h1, h2]
        exact hstep_sq τ.val τ.isLt
      rw [htele_sq, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, ← Finset.mul_sum] at hsum_le
      have hCeq : (T : ℝ) * (2 * (T : ℝ) * (driftBound M) ^ 2) = C_quad := by rw [hC_quad_def]; ring
      linarith
    -- 1b. Weighted expectation of squared distance using convergent interval `T`
    have hquad_exp : ∑ u : Fin T → M.State, pathWeight M.P T s₀ u * (Yu u) ^ 2 ≤
        Y0 ^ 2 + C_quad - 4 * η_d * Y0 := by
      have hsum1 := Finset.sum_le_sum (s := Finset.univ) (fun u _ =>
        mul_le_mul_of_nonneg_left (hpath_sq u) (hpw_nonneg u))
      simp_rw [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib,
        ← Finset.sum_mul, hpw_sum, one_mul] at hsum1
      have hdual_eval :
          ∑ u : Fin T → M.State, pathWeight M.P T s₀ u *
            (2 * ∑ τ : Fin T, Δg (consState s₀ u τ.castSucc)) =
          2 * (T : ℝ) * ∑ s' : M.State,
            ((1 / (T : ℝ)) * ∑ τ ∈ Finset.range T, Routine.matPow M.P τ s₀ s') * Δg s' := by
        have h1 : ∀ u : Fin T → M.State,
            pathWeight M.P T s₀ u * (2 * ∑ τ : Fin T, Δg (consState s₀ u τ.castSucc)) =
            2 * ∑ τ : Fin T, pathWeight M.P T s₀ u * Δg (consState s₀ u τ.castSucc) := by
          intro u
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun τ _ => by ring)
        simp_rw [h1, ← Finset.mul_sum]
        rw [mul_assoc]
        congr 1
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        have htau : ∀ τ : Fin T,
            ∑ u : Fin T → M.State, pathWeight M.P T s₀ u * Δg (consState s₀ u τ.castSucc) =
            ∑ s' : M.State, Routine.matPow M.P τ.val s₀ s' * Δg s' := by
          intro τ
          have hsplit : ∀ u : Fin T → M.State,
              pathWeight M.P T s₀ u * Δg (consState s₀ u τ.castSucc) =
              ∑ s' : M.State, (pathWeight M.P T s₀ u *
                (if consState s₀ u τ.castSucc = s' then (1 : ℝ) else 0)) * Δg s' := by
            intro u
            rw [Finset.sum_eq_single (consState s₀ u τ.castSucc)]
            · simp
            · intro s' _ hne; simp [hne.symm]
            · intro h; exact absurd (Finset.mem_univ _) h
          simp_rw [hsplit]
          rw [Finset.sum_comm]
          simp_rw [← Finset.sum_mul]
          refine Finset.sum_congr rfl (fun s' _ => ?_)
          have hmarg := pathWeight_marginal M.P_sum_one T s₀ τ.castSucc s'
          rw [hmarg]
          rfl
        rw [Finset.sum_congr rfl (fun τ _ => htau τ),
          Fin.sum_univ_eq_sum_range (fun τ => ∑ s' : M.State, Routine.matPow M.P τ s₀ s' * Δg s') T,
          Finset.sum_comm]
        refine Finset.sum_congr rfl (fun s' _ => ?_)
        rw [← Finset.sum_mul, ← Finset.mul_sum]
        field_simp [hT_real_pos.ne']
      have hdual_diff :
          (M.dual V γstar - M.dual V q₀) -
            ∑ s' : M.State, ((1 / (T : ℝ)) * ∑ τ ∈ Finset.range T, Routine.matPow M.P τ s₀ s') * Δg s' ≤
          (L / (2 * driftBound M)) * (driftBound M * Y0) := by
        have hlhs : (M.dual V γstar - M.dual V q₀) -
            ∑ s' : M.State, ((1 / (T : ℝ)) * ∑ τ ∈ Finset.range T, Routine.matPow M.P τ s₀ s') * Δg s' =
            ∑ s' : M.State, (M.π s' - (1 / (T : ℝ)) * ∑ τ ∈ Finset.range T, Routine.matPow M.P τ s₀ s') * Δg s' := by
          unfold NetworkModel.dual
          rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl (fun s' _ => by dsimp [Δg]; ring)
        rw [hlhs]
        calc _ ≤ |∑ s' : M.State,
              (M.π s' - (1 / (T : ℝ)) * ∑ τ ∈ Finset.range T, Routine.matPow M.P τ s₀ s') * Δg s'| :=
              le_abs_self _
          _ ≤ ∑ s' : M.State,
              |(M.π s' - (1 / (T : ℝ)) * ∑ τ ∈ Finset.range T, Routine.matPow M.P τ s₀ s') * Δg s'| :=
              Finset.abs_sum_le_sum_abs _ _
          _ = ∑ s' : M.State,
              |M.π s' - (1 / (T : ℝ)) * ∑ τ ∈ Finset.range T, Routine.matPow M.P τ s₀ s'| * |Δg s'| :=
              Finset.sum_congr rfl (fun s' _ => abs_mul _ _)
          _ ≤ ∑ s' : M.State,
              |M.π s' - (1 / (T : ℝ)) * ∑ τ ∈ Finset.range T, Routine.matPow M.P τ s₀ s'| * (driftBound M * Y0) :=
              Finset.sum_le_sum (fun s' _ => mul_le_mul_of_nonneg_left (hΔg_abs s') (abs_nonneg _))
          _ = (∑ s' : M.State,
              |M.π s' - (1 / (T : ℝ)) * ∑ τ ∈ Finset.range T, Routine.matPow M.P τ s₀ s'|) * (driftBound M * Y0) :=
              (Finset.sum_mul _ _ _).symm
          _ ≤ (L / (2 * driftBound M)) * (driftBound M * Y0) :=
              mul_le_mul_of_nonneg_right (hT_conv s₀) (mul_nonneg (le_of_lt hB_pos) hY0_nonneg)
      have hpoly_q0 : L * Y0 ≤ M.dual V γstar - M.dual V q₀ := by
        have hp := hpoly.2 q₀ hq₀
        rw [eucDist_symm γstar q₀] at hp
        dsimp [Y0]
        linarith
      have hνB : (L / (2 * driftBound M)) * (driftBound M * Y0) = (L / 2) * Y0 := by
        field_simp [hB_pos.ne']
      have hlower_avg : (L / 2) * Y0 ≤
          ∑ s' : M.State, ((1 / (T : ℝ)) * ∑ τ ∈ Finset.range T, Routine.matPow M.P τ s₀ s') * Δg s' := by
        linarith [hdual_diff, hpoly_q0, hνB]
      have hlower_mul : 4 * η_d * Y0 ≤
          2 * (T : ℝ) * ∑ s' : M.State,
            ((1 / (T : ℝ)) * ∑ τ ∈ Finset.range T, Routine.matPow M.P τ s₀ s') * Δg s' := by
        have hmul := mul_le_mul_of_nonneg_left hlower_avg (by positivity : 0 ≤ 2 * (T : ℝ))
        have heq : 2 * (T : ℝ) * ((L / 2) * Y0) = 4 * η_d * Y0 := by rw [hη_d_def]; ring
        linarith
      linarith [hsum1, hdual_eval, hlower_mul]
    -- 1c. Linear negative drift via Cauchy-Schwarz (Jensen for `x ↦ x^2`)
    have hY0_ge_D : D ≤ Y0 := by linarith
    have hY0_sub_nonneg : 0 ≤ Y0 - η_d := by linarith
    have hsq_le_sq : ∑ u : Fin T → M.State, pathWeight M.P T s₀ u * (Yu u) ^ 2 ≤ (Y0 - η_d) ^ 2 := by
      have hCq : C_quad ≤ 2 * η_d * Y0 :=
        le_trans hC_quad_le (mul_le_mul_of_nonneg_left hY0_ge_D (by positivity))
      nlinarith [sq_nonneg η_d]
    have hlin_drift : ∑ u : Fin T → M.State, pathWeight M.P T s₀ u * Yu u ≤ Y0 - η_d := by
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin T → M.State))
        (fun u => Real.sqrt (pathWeight M.P T s₀ u))
        (fun u => Real.sqrt (pathWeight M.P T s₀ u) * Yu u)
      have hL_eq : ∑ u : Fin T → M.State,
          Real.sqrt (pathWeight M.P T s₀ u) * (Real.sqrt (pathWeight M.P T s₀ u) * Yu u) =
          ∑ u : Fin T → M.State, pathWeight M.P T s₀ u * Yu u := by
        refine Finset.sum_congr rfl (fun u _ => ?_)
        rw [← mul_assoc, Real.mul_self_sqrt (hpw_nonneg u)]
      have hR1_eq : ∑ u : Fin T → M.State, (Real.sqrt (pathWeight M.P T s₀ u)) ^ 2 = 1 := by
        calc ∑ u : Fin T → M.State, (Real.sqrt (pathWeight M.P T s₀ u)) ^ 2
            = ∑ u : Fin T → M.State, pathWeight M.P T s₀ u :=
                Finset.sum_congr rfl (fun u _ => Real.sq_sqrt (hpw_nonneg u))
          _ = 1 := hpw_sum
      have hR2_eq : ∑ u : Fin T → M.State, (Real.sqrt (pathWeight M.P T s₀ u) * Yu u) ^ 2 =
          ∑ u : Fin T → M.State, pathWeight M.P T s₀ u * (Yu u) ^ 2 := by
        refine Finset.sum_congr rfl (fun u _ => ?_)
        rw [mul_pow, Real.sq_sqrt (hpw_nonneg u)]
      rw [hL_eq, hR1_eq, hR2_eq, one_mul] at hcs
      have hsq_final : (∑ u : Fin T → M.State, pathWeight M.P T s₀ u * Yu u) ^ 2 ≤ (Y0 - η_d) ^ 2 :=
        le_trans hcs hsq_le_sq
      have hsum_nonneg : 0 ≤ ∑ u : Fin T → M.State, pathWeight M.P T s₀ u * Yu u :=
        Finset.sum_nonneg (fun u _ => mul_nonneg (hpw_nonneg u) (hYu_nonneg u))
      have hsqrt := Real.sqrt_le_sqrt hsq_final
      rwa [Real.sqrt_sq hsum_nonneg, Real.sqrt_sq hY0_sub_nonneg] at hsqrt
    -- 1d. Exponential contraction using `Routine.exp_le_quad_div`
    have hYtilde0 : Ytilde q₀ = Y0 - D := max_eq_left (by linarith)
    have hYtilde_u : ∀ u : Fin T → M.State, Ytilde (qEnd u) = Yu u - D := by
      intro u
      have hlo : -M_step ≤ Yu u - Y0 := (abs_le.mp (hYu_diff u)).1
      exact max_eq_left (by linarith)
    have hexp_pt : ∀ u : Fin T → M.State,
        Real.exp (w * Ytilde (qEnd u)) ≤
          Real.exp (w * Ytilde q₀) * (1 + w * (Yu u - Y0) + w * η_d / 2) := by
      intro u
      let Δ : ℝ := Yu u - Y0
      have hΔ_abs : |Δ| ≤ M_step := hYu_diff u
      have hΔ_le : Δ ≤ M_step := (abs_le.mp hΔ_abs).2
      have hy_le : w * Δ ≤ w * M_step := mul_le_mul_of_nonneg_left hΔ_le (le_of_lt hw_pos)
      have hy_lt3 : w * Δ < 3 := lt_of_le_of_lt hy_le hwM_lt3
      have hpade := exp_le_quad_div hy_lt3
      have hnum_le : (w * Δ) ^ 2 ≤ (w * M_step) ^ 2 := by
        have h1 : |w * Δ| ≤ w * M_step := by
          rw [abs_mul, abs_of_pos hw_pos]
          exact mul_le_mul_of_nonneg_left hΔ_abs (le_of_lt hw_pos)
        rw [← sq_abs (w * Δ)]
        exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      have hden_pos : 0 < 2 * (1 - w * M_step / 3) := by linarith
      have hden_le : 2 * (1 - w * M_step / 3) ≤ 2 * (1 - w * Δ / 3) := by linarith
      have hfrac_le : (w * Δ) ^ 2 / (2 * (1 - w * Δ / 3)) ≤ w * η_d / 2 := by
        calc (w * Δ) ^ 2 / (2 * (1 - w * Δ / 3))
            ≤ (w * M_step) ^ 2 / (2 * (1 - w * M_step / 3)) :=
              div_le_div₀ (sq_nonneg _) hnum_le hden_pos hden_le
          _ = w * η_d / 2 := hw_quad_eq
      have h1 : Real.exp (w * Δ) ≤ 1 + w * Δ + w * η_d / 2 := le_trans hpade (by linarith)
      have hmul := mul_le_mul_of_nonneg_left h1 (le_of_lt (Real.exp_pos (w * Ytilde q₀)))
      rw [← Real.exp_add] at hmul
      have harg : w * Ytilde q₀ + w * Δ = w * Ytilde (qEnd u) := by
        rw [hYtilde0, hYtilde_u u]; dsimp [Δ]; ring
      rwa [harg] at hmul
    have hsum_exp : ∑ u : Fin T → M.State, pathWeight M.P T s₀ u * Real.exp (w * Ytilde (qEnd u)) ≤
        Real.exp (w * Ytilde q₀) * (1 - w * η_d / 2) := by
      calc ∑ u : Fin T → M.State, pathWeight M.P T s₀ u * Real.exp (w * Ytilde (qEnd u))
          ≤ ∑ u : Fin T → M.State, pathWeight M.P T s₀ u *
              (Real.exp (w * Ytilde q₀) * (1 + w * (Yu u - Y0) + w * η_d / 2)) :=
            Finset.sum_le_sum (fun u _ => mul_le_mul_of_nonneg_left (hexp_pt u) (hpw_nonneg u))
        _ = Real.exp (w * Ytilde q₀) *
              (1 + w * ((∑ u : Fin T → M.State, pathWeight M.P T s₀ u * Yu u) - Y0) + w * η_d / 2) := by
            have hre : ∀ u : Fin T → M.State,
                pathWeight M.P T s₀ u * (Real.exp (w * Ytilde q₀) * (1 + w * (Yu u - Y0) + w * η_d / 2)) =
                Real.exp (w * Ytilde q₀) *
                  (pathWeight M.P T s₀ u * (1 - w * Y0 + w * η_d / 2) +
                   w * (pathWeight M.P T s₀ u * Yu u)) := fun u => by ring
            simp_rw [hre, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_mul,
              ← Finset.mul_sum, hpw_sum, one_mul]
            ring
        _ ≤ Real.exp (w * Ytilde q₀) * (1 + w * (-η_d) + w * η_d / 2) := by
            refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (Real.exp_pos _))
            nlinarith [hlin_drift, hw_pos]
        _ = Real.exp (w * Ytilde q₀) * (1 - w * η_d / 2) := by ring
    linarith [hsum_exp, hC_exp_pos]
  · -- Case 2: `Y0 < D + M_step` (bounded `Ytilde ≤ 2 * M_step`)
    push Not at hlarge
    have hYtilde0_le : Ytilde q₀ ≤ 2 * M_step := by
      dsimp [Ytilde]
      exact max_le (by linarith) (by positivity)
    have hYtilde_u_le : ∀ u : Fin T → M.State, Ytilde (qEnd u) ≤ 2 * M_step := by
      intro u
      have hhi : Yu u - Y0 ≤ M_step := (abs_le.mp (hYu_diff u)).2
      dsimp [Ytilde]
      exact max_le (by linarith) (by positivity)
    have hexp0_le : Real.exp (w * Ytilde q₀) ≤ Real.exp (2 * w * M_step) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hw_pos]
    have hexp_u_le : ∑ u : Fin T → M.State, pathWeight M.P T s₀ u * Real.exp (w * Ytilde (qEnd u)) ≤
        Real.exp (2 * w * M_step) := by
      calc _ ≤ ∑ u : Fin T → M.State, pathWeight M.P T s₀ u * Real.exp (2 * w * M_step) := by
            refine Finset.sum_le_sum (fun u _ => mul_le_mul_of_nonneg_left ?_ (hpw_nonneg u))
            apply Real.exp_le_exp.mpr
            nlinarith [hYtilde_u_le u, hw_pos]
        _ = Real.exp (2 * w * M_step) := by rw [← Finset.sum_mul, hpw_sum, one_mul]
    have hterm_le : (w * η_d / 2) * Real.exp (w * Ytilde q₀) ≤
        (w * η_d / 2) * Real.exp (2 * w * M_step) :=
      mul_le_mul_of_nonneg_left hexp0_le (by positivity)
    have hexp0_pos : 0 ≤ Real.exp (w * Ytilde q₀) := le_of_lt (Real.exp_pos _)
    rw [hC_exp_def]
    linarith

/-! ### Main Proof of Theorem 3 (`thm:prob_multi_con`) -/

/-- Proof of Theorem 3 (`thm:prob_multi_con`): exponential attraction of Backpressure queue
backlogs to the unique dual optimum `γ*_V` with `V`-independent constants `D, K, c* > 0`. -/
theorem theorem3 : Theorem3Statement := by
  intro M η L _hslack hL_pos
  -- Step 0: Extract `V`-independent geometric mixing & convergent interval `T ≥ 1`
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
  let B : ℝ := driftBound M
  have hB_pos : 0 < B := driftBound_pos M
  let ν : ℝ := L / (2 * B)
  have hν_pos : 0 < ν := div_pos hL_pos (by positivity)
  obtain ⟨T, hT_pos, hT_conv⟩ :=
    exists_convergent_interval hC_mix (le_of_lt hρ0) hρ1 hmix hν_pos
  have hT_real_pos : (0 : ℝ) < (T : ℝ) := Nat.cast_pos.mpr hT_pos
  -- Define all `V`-independent constants: `η_d`, `C_quad`, `D`, `M_step`, `w`, `C_exp`, `K`, `cstar`
  let η_d : ℝ := (T : ℝ) * L / 4
  have hη_d_pos : 0 < η_d := by dsimp [η_d]; positivity
  let C_quad : ℝ := 2 * (T : ℝ) ^ 2 * B ^ 2
  let D : ℝ := max (C_quad / (2 * η_d)) (2 * η_d)
  have hD_pos : 0 < D := lt_of_lt_of_le (by positivity) (le_max_right _ _)
  have hD_ge_2η : 2 * η_d ≤ D := le_max_right _ _
  have hC_quad_le : C_quad ≤ 2 * η_d * D := by
    have h1 : C_quad / (2 * η_d) ≤ D := le_max_left _ _
    linarith [(div_le_iff₀ (by positivity)).mp h1]
  let M_step : ℝ := (T : ℝ) * B
  have hM_step_pos : 0 < M_step := mul_pos hT_real_pos hB_pos
  let w_den : ℝ := M_step ^ 2 + M_step * η_d / 3
  have hw_den_pos : 0 < w_den := by dsimp [w_den]; positivity
  let w : ℝ := η_d / w_den
  have hw_pos : 0 < w := div_pos hη_d_pos hw_den_pos
  have hwM_lt3 : w * M_step < 3 := by
    dsimp [w]
    rw [div_mul_eq_mul_div, div_lt_iff₀ hw_den_pos]
    have h3 : 3 * w_den = 3 * M_step ^ 2 + M_step * η_d := by dsimp [w_den]; ring
    nlinarith [sq_pos_of_pos hM_step_pos]
  have hw_quad_eq : (w * M_step) ^ 2 / (2 * (1 - w * M_step / 3)) = w * η_d / 2 := by
    have h1m : 1 - w * M_step / 3 = M_step ^ 2 / w_den := by
      dsimp [w, w_den]
      field_simp [hw_den_pos.ne']
      ring
    rw [h1m]
    have hw_mul : w * w_den = η_d := div_mul_cancel₀ η_d hw_den_pos.ne'
    have hM2_ne : M_step ^ 2 ≠ 0 := (sq_pos_of_pos hM_step_pos).ne'
    field_simp [hw_den_pos.ne', hM2_ne]
    nlinarith [hw_mul]
  let C_exp : ℝ := (1 + w * η_d / 2) * Real.exp (2 * w * M_step)
  have hC_exp_pos : 0 < C_exp := by dsimp [C_exp]; positivity
  let K : ℝ := 1 / w
  have hK_pos : 0 < K := one_div_pos.mpr hw_pos
  let cstar : ℝ := 2 * C_exp / (w * η_d)
  have hcstar_pos : 0 < cstar := by dsimp [cstar]; positivity
  refine ⟨D, K, cstar, hD_pos, hK_pos, hcstar_pos, ?_⟩
  -- Fix `V ≥ 1`, unique polyhedral dual optimum `γstar`, Markov process `proc`, Backpressure `pol`
  intro V _hV γstar huniq hpoly Ω _ μ _ proc pol hbp
  have hγ_nonneg : ∀ j, 0 ≤ γstar j := huniq.1.1
  rcases hbp with ⟨choice, hchoice_bp, hchoice_act⟩
  let Ytilde : (Fin M.r → ℝ) → ℝ := fun q => max (NetworkModel.eucDist q γstar - D) 0
  -- Step 5: Integrate the pointwise `T`-step exponential drift over `(Ω, μ)`
  let a : ℕ → ℝ := fun t => ∫ ω, Real.exp (w * Ytilde (pol.queue t ω)) ∂μ
  have ha_nonneg : ∀ t, 0 ≤ a t := fun t =>
    integral_nonneg (fun _ => le_of_lt (Real.exp_pos _))
  have ha_drift : ∀ t : ℕ, a (t + T) - a t ≤ C_exp - (w * η_d / 2) * a t := by
    intro t
    let qH : (Fin (t + 1) → M.State) → (Fin M.r → ℝ) := fun h =>
      bpQueueHist M choice t (fun i => h i.castSucc)
    have hqH_nonneg : ∀ h j, 0 ≤ qH h j := by
      intro h j
      have haux : ∀ (n : ℕ) (h' : Fin n → M.State) (j : Fin M.r),
          0 ≤ bpQueueHist M choice n h' j := by
        intro n
        induction n with
        | zero => intro _ _; exact le_rfl
        | succ k _ => intro _ _; exact add_nonneg (le_max_right _ _) (M.arrival_nonneg _ _ _)
      exact haux t _ j
    have ha_t : a t = ∑ h : Fin (t + 1) → M.State,
        (μ (markovCyl proc t h)).toReal * Real.exp (w * Ytilde (qH h)) := by
      have heq := (integral_history_eq_sum proc t (fun h => Real.exp (w * Ytilde (qH h)))).2
      have hfun : (fun ω => Real.exp (w * Ytilde (pol.queue t ω))) =
          fun ω => Real.exp (w * Ytilde (qH (fun i => proc.S i ω))) := by
        funext ω
        dsimp [qH]
        rw [bp_queue_eq_hist hchoice_act t ω]
      dsimp [a]
      rw [hfun, heq]
    have ha_tT : a (t + T) = ∑ h : Fin (t + 1) → M.State,
        (μ (markovCyl proc t h)).toReal *
          ∑ u : Fin T → M.State, pathWeight M.P T (h (Fin.last t)) u *
            Real.exp (w * Ytilde (bpRun M choice (qH h) (consState (h (Fin.last t)) u) T (Nat.le_succ T))) := by
      let G : (Fin (t + 1) → M.State) → (Fin T → M.State) → ℝ := fun h u =>
        Real.exp (w * Ytilde (bpRun M choice (qH h) (consState (h (Fin.last t)) u) T (Nat.le_succ T)))
      have hfun : (fun ω => Real.exp (w * Ytilde (pol.queue (t + T) ω))) =
          fun ω => G (fun i => proc.S i ω) (fun j => proc.S (t + 1 + j.val) ω) := by
        funext ω
        dsimp [G, qH]
        have hq0 : bpQueueHist M choice t (fun i : Fin t => proc.S i.val ω) = pol.queue t ω :=
          (bp_queue_eq_hist hchoice_act t ω).symm
        rw [hq0, bpRun_eq_pol_queue hchoice_act t T ω T (Nat.le_succ T)]
      dsimp [a]
      rw [hfun]
      exact integral_history_future_eq proc t T G
    have hcyl_sum : ∑ h : Fin (t + 1) → M.State, (μ (markovCyl proc t h)).toReal = 1 := by
      have h1 := (integral_history_eq_sum proc t (fun _ => (1 : ℝ))).2
      have h2 : ∫ _ : Ω, (1 : ℝ) ∂μ = 1 := by simp [integral_const, measureReal_def, measure_univ]
      simpa [h2] using h1.symm
    rw [ha_tT, ha_t, ← Finset.sum_sub_distrib]
    have hpt_sum : ∑ h : Fin (t + 1) → M.State,
        ((μ (markovCyl proc t h)).toReal *
          ∑ u : Fin T → M.State, pathWeight M.P T (h (Fin.last t)) u *
            Real.exp (w * Ytilde (bpRun M choice (qH h) (consState (h (Fin.last t)) u) T (Nat.le_succ T))) -
         (μ (markovCyl proc t h)).toReal * Real.exp (w * Ytilde (qH h))) ≤
        ∑ h : Fin (t + 1) → M.State,
          (μ (markovCyl proc t h)).toReal * (C_exp - (w * η_d / 2) * Real.exp (w * Ytilde (qH h))) := by
      refine Finset.sum_le_sum (fun h _ => ?_)
      rw [← mul_sub]
      exact mul_le_mul_of_nonneg_left
        (pointwise_exp_drift M hL_pos hT_pos hT_conv hγ_nonneg hpoly hchoice_bp
          rfl rfl hD_ge_2η hC_quad_le rfl hw_pos hwM_lt3 hw_quad_eq rfl
          (qH h) (hqH_nonneg h) (h (Fin.last t)))
        ENNReal.toReal_nonneg
    calc _ ≤ ∑ h : Fin (t + 1) → M.State,
            (μ (markovCyl proc t h)).toReal * (C_exp - (w * η_d / 2) * Real.exp (w * Ytilde (qH h))) := hpt_sum
      _ = (∑ h : Fin (t + 1) → M.State, (μ (markovCyl proc t h)).toReal) * C_exp -
          (w * η_d / 2) * ∑ h : Fin (t + 1) → M.State,
            (μ (markovCyl proc t h)).toReal * Real.exp (w * Ytilde (qH h)) := by
            simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, ← mul_assoc,
              mul_comm _ (w * η_d / 2), mul_assoc, ← Finset.mul_sum]
      _ = C_exp - (w * η_d / 2) * ∑ h : Fin (t + 1) → M.State,
            (μ (markovCyl proc t h)).toReal * Real.exp (w * Ytilde (qH h)) := by
            rw [hcyl_sum, one_mul]
  -- Step 6: Telescope `ha_drift` over `t = 0 .. N - 1`
  let S_init : ℝ := (2 * ∑ t ∈ Finset.range T, a t) / (w * η_d)
  have havg_a : ∀ N : ℕ, 0 < N →
      ((1 : ℝ) / (N : ℝ)) * ∑ t ∈ Finset.range N, a t ≤ cstar + S_init / (N : ℝ) := by
    intro N hN
    have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
    have hsum := Finset.sum_le_sum (s := Finset.range N) (fun t _ => ha_drift t)
    rw [sum_range_shift_sub a T N, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, ← Finset.mul_sum] at hsum
    have htail_nonneg : 0 ≤ ∑ t ∈ Finset.range T, a (N + t) :=
      Finset.sum_nonneg (fun t _ => ha_nonneg (N + t))
    have h1 : (w * η_d / 2) * ∑ t ∈ Finset.range N, a t ≤
        (N : ℝ) * C_exp + ∑ t ∈ Finset.range T, a t := by linarith
    have hdiv := div_le_div_of_nonneg_right h1 (by positivity : 0 ≤ (w * η_d / 2) * (N : ℝ))
    have hLHS : ((w * η_d / 2) * ∑ t ∈ Finset.range N, a t) / ((w * η_d / 2) * (N : ℝ)) =
        ((1 : ℝ) / (N : ℝ)) * ∑ t ∈ Finset.range N, a t := by
      have hne : w * η_d / 2 ≠ 0 := by positivity
      field_simp [hne, hN_pos.ne']
    have hRHS : ((N : ℝ) * C_exp + ∑ t ∈ Finset.range T, a t) / ((w * η_d / 2) * (N : ℝ)) =
        cstar + S_init / (N : ℝ) := by
      dsimp [cstar, S_init]
      have hne1 : w * η_d ≠ 0 := by positivity
      field_simp [hne1, hN_pos.ne']
    linarith
  -- Step 7: Markov's inequality and `limsup` for every `m ≥ 0`
  intro m _hm
  have hmarkov : ∀ τ : ℕ,
      (μ {ω | ∃ j : Fin M.r, D + K * m < |pol.queue τ ω j - γstar j|}).toReal ≤
        Real.exp (-m) * a τ := by
    intro τ
    let E : Set Ω := {ω | ∃ j : Fin M.r, D + K * m < |pol.queue τ ω j - γstar j|}
    have hE_meas : MeasurableSet E := by
      have hq_meas : ∀ j : Fin M.r, Measurable (fun ω => pol.queue τ ω j) := by
        intro j
        induction τ with
        | zero => exact measurable_const
        | succ k ih =>
          exact ((ih.sub (pol.measurable_service k j)).max measurable_const).add
            (pol.measurable_arrival k j)
      have hE_eq : E = ⋃ j : Fin M.r, {ω | D + K * m < |pol.queue τ ω j - γstar j|} := by
        ext ω; simp [E]
      rw [hE_eq]
      exact MeasurableSet.iUnion (fun j =>
        measurableSet_lt measurable_const (continuous_abs.measurable.comp ((hq_meas j).sub measurable_const)))
    have hint_E : Integrable (E.indicator (fun _ => Real.exp m)) μ :=
      (integrable_const (Real.exp m)).indicator hE_meas
    have hint_a : Integrable (fun ω => Real.exp (w * Ytilde (pol.queue τ ω))) μ := by
      have h := (integral_history_eq_sum proc τ (fun h =>
        Real.exp (w * Ytilde (bpQueueHist M choice τ (fun i => h i.castSucc))))).1
      have hfun : (fun ω => Real.exp (w * Ytilde (pol.queue τ ω))) =
          fun ω => Real.exp (w * Ytilde (bpQueueHist M choice τ (fun i => proc.S i.castSucc ω))) := by
        funext ω
        rw [bp_queue_eq_hist hchoice_act τ ω]
        simp [Fin.val_castSucc]
      rwa [hfun]
    have hpt_le : ∀ ω : Ω, E.indicator (fun _ => Real.exp m) ω ≤ Real.exp (w * Ytilde (pol.queue τ ω)) := by
      intro ω
      by_cases hω : ω ∈ E
      · rw [Set.indicator_of_mem hω]
        rcases hω with ⟨j, hj⟩
        have hcoord : |pol.queue τ ω j - γstar j| ≤ NetworkModel.eucDist (pol.queue τ ω) γstar := by
          rw [← Real.sqrt_sq_eq_abs]
          apply Real.sqrt_le_sqrt
          exact Finset.single_le_sum (f := fun j' : Fin M.r => (pol.queue τ ω j' - γstar j') ^ 2)
            (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
        have hYt : K * m ≤ Ytilde (pol.queue τ ω) :=
          le_trans (by linarith) (le_max_left _ _)
        have hwK : w * (K * m) = m := by dsimp [K]; field_simp [hw_pos.ne']
        apply Real.exp_le_exp.mpr
        rw [← hwK]
        exact mul_le_mul_of_nonneg_left hYt (le_of_lt hw_pos)
      · rw [Set.indicator_of_notMem hω]
        exact le_of_lt (Real.exp_pos _)
    have hint_le := integral_mono hint_E hint_a hpt_le
    rw [integral_indicator_const (Real.exp m) hE_meas, smul_eq_mul, measureReal_def] at hint_le
    have hmul := mul_le_mul_of_nonneg_left hint_le (le_of_lt (Real.exp_pos (-m)))
    have hcancel : Real.exp (-m) * ((μ E).toReal * Real.exp m) = (μ E).toReal := by
      rw [mul_comm (μ E).toReal, ← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
    linarith
  have havg_prob : ∀ N : ℕ, 0 < N →
      ((1 : ℝ) / (N : ℝ)) * ∑ τ ∈ Finset.range N,
          (μ {ω | ∃ j : Fin M.r, D + K * m < |pol.queue τ ω j - γstar j|}).toReal ≤
        cstar * Real.exp (-m) + (Real.exp (-m) * S_init) / (N : ℝ) := by
    intro N hN
    have hsum : ∑ τ ∈ Finset.range N,
        (μ {ω | ∃ j : Fin M.r, D + K * m < |pol.queue τ ω j - γstar j|}).toReal ≤
        Real.exp (-m) * ∑ τ ∈ Finset.range N, a τ := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun τ _ => hmarkov τ)
    have h1 : ((1 : ℝ) / (N : ℝ)) * ∑ τ ∈ Finset.range N,
        (μ {ω | ∃ j : Fin M.r, D + K * m < |pol.queue τ ω j - γstar j|}).toReal ≤
        Real.exp (-m) * (((1 : ℝ) / (N : ℝ)) * ∑ τ ∈ Finset.range N, a τ) := by
      have h := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ (1 : ℝ) / (N : ℝ))
      linarith
    have h2 := mul_le_mul_of_nonneg_left (havg_a N hN) (le_of_lt (Real.exp_pos (-m)))
    have h3 : Real.exp (-m) * (cstar + S_init / (N : ℝ)) =
        cstar * Real.exp (-m) + (Real.exp (-m) * S_init) / (N : ℝ) := by ring
    linarith
  -- Take `Filter.limsup` as `N → ∞`
  unfold deviationProb
  have hlim_rhs : Filter.Tendsto
      (fun N : ℕ => ((cstar * Real.exp (-m) + (Real.exp (-m) * S_init) / (N : ℝ) : ℝ) : EReal))
      Filter.atTop (nhds ((cstar * Real.exp (-m) : ℝ) : EReal)) := by
    have h0 : Filter.Tendsto (fun N : ℕ => (Real.exp (-m) * S_init) / (N : ℝ))
        Filter.atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have hreal : Filter.Tendsto
        (fun N : ℕ => cstar * Real.exp (-m) + (Real.exp (-m) * S_init) / (N : ℝ))
        Filter.atTop (nhds (cstar * Real.exp (-m))) := by
      simpa [add_zero] using tendsto_const_nhds.add h0
    exact (EReal.continuous_coe_iff.mpr continuous_id).continuousAt.tendsto.comp hreal
  rw [← hlim_rhs.limsup_eq]
  refine Filter.limsup_le_limsup ?_ (by isBoundedDefault) (by isBoundedDefault)
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  exact EReal.coe_le_coe_iff.mpr (havg_prob N (lt_of_lt_of_le Nat.zero_lt_one hN))

end LifoBackpressure.Proofs
