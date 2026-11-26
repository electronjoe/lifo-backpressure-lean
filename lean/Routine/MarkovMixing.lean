import Prelude

/-!
# Finite-State Markov Chain Mixing, Poisson Potential, and Convergent Intervals

Routine (statement-independent) library for finite-state irreducible aperiodic Markov chains:
1. Schur's additive submonoid theorem (`exists_all_ge_of_gcd_one`).
2. Primitivity (`exists_matPow_pos`): `∃ m > 0, ∀ s s', 0 < matPow P m s s'`.
3. Doeblin `L¹` geometric mixing (`exists_geometric_mixing`):
   `∃ C > 0, ∃ ρ ∈ (0, 1), ∀ n s, ∑ s', |matPow P n s s' - π s'| ≤ C * ρ ^ n`.
4. Poisson potential `poissonPotential P π f` satisfying Poisson's equation and uniform
   Lipschitz / amplitude bounds (used by Theorem 2).
5. Convergent interval existence `exists_convergent_interval` for any `ν > 0` (used by Theorem 3).
-/

namespace LifoBackpressure.Routine

open Classical

/-- Matrix power `P^n` of a transition kernel `P : S → S → ℝ` on a finite state space. -/
def matPow {S : Type*} [Fintype S] [DecidableEq S]
    (P : S → S → ℝ) : ℕ → S → S → ℝ
  | 0, s, s' => if s = s' then 1 else 0
  | n + 1, s, s' => ∑ u, matPow P n s u * P u s'

section BasicMatrixPowers

variable {S : Type*} [Fintype S] [DecidableEq S]

lemma matPow_nonneg {P : S → S → ℝ} (hP : ∀ s s', 0 ≤ P s s') :
    ∀ n s s', 0 ≤ matPow P n s s'
  | 0, s, s' => by
    unfold matPow
    split_ifs <;> norm_num
  | n + 1, s, s' => by
    unfold matPow
    exact Finset.sum_nonneg (fun u _ => mul_nonneg (matPow_nonneg hP n s u) (hP u s'))

lemma matPow_sum_one {P : S → S → ℝ} (hsum : ∀ s, ∑ s', P s s' = 1) :
    ∀ n s, ∑ s', matPow P n s s' = 1
  | 0, s => by simp [matPow]
  | n + 1, s => by
    simp only [matPow]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hsum, mul_one]
    exact matPow_sum_one hsum n s

lemma matPow_add (P : S → S → ℝ) (m n : ℕ) (s s' : S) :
    matPow P (m + n) s s' = ∑ u, matPow P m s u * matPow P n u s' := by
  induction n generalizing s' with
  | zero => simp [matPow]
  | succ k ih =>
    rw [← Nat.add_assoc]
    simp only [matPow, ih]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun v _ => by ring))

lemma matPow_one (P : S → S → ℝ) (s s' : S) :
    matPow P 1 s s' = P s s' := by
  simp [matPow]

lemma matPow_succ_left (P : S → S → ℝ) (n : ℕ) (s s' : S) :
    matPow P (n + 1) s s' = ∑ u, P s u * matPow P n u s' := by
  rw [Nat.add_comm, matPow_add]
  simp_rw [matPow_one]

lemma matPow_pos_add {P : S → S → ℝ} (hP : ∀ s s', 0 ≤ P s s')
    {m n : ℕ} {s u s' : S}
    (hm : 0 < matPow P m s u) (hn : 0 < matPow P n u s') :
    0 < matPow P (m + n) s s' := by
  rw [matPow_add]
  have hterm : 0 < matPow P m s u * matPow P n u s' := mul_pos hm hn
  have hle : matPow P m s u * matPow P n u s' ≤
      ∑ v, matPow P m s v * matPow P n v s' :=
    Finset.single_le_sum (f := fun v => matPow P m s v * matPow P n v s')
      (fun v _ => mul_nonneg (matPow_nonneg hP m s v) (matPow_nonneg hP n v s'))
      (Finset.mem_univ u)
  exact lt_of_lt_of_le hterm hle

lemma matPow_stationary {P : S → S → ℝ} {π : S → ℝ}
    (hstat : ∀ s', ∑ s, π s * P s s' = π s') :
    ∀ n s', ∑ s, π s * matPow P n s s' = π s'
  | 0, s' => by simp [matPow]
  | n + 1, s' => by
    simp only [matPow]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    have : ∀ u, ∑ s, π s * (matPow P n s u * P u s') = (∑ s, π s * matPow P n s u) * P u s' := by
      intro u
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun s _ => by ring)
    simp_rw [this, matPow_stationary hstat n]
    exact hstat s'

end BasicMatrixPowers

/-! ### Schur's additive submonoid theorem & primitivity -/

private lemma finset_gcd_bezout (F : Finset ℕ) :
    ∃ c : ℕ → ℤ, ∑ a ∈ F, c a * (a : ℤ) = ((F.gcd id : ℕ) : ℤ) := by
  induction F using Finset.induction_on with
  | empty =>
    exact ⟨fun _ => 0, by simp⟩
  | @insert b s hb ih =>
    obtain ⟨c, hc⟩ := ih
    let g := s.gcd id
    have hbez : (Nat.gcd b g : ℤ) = (b : ℤ) * Nat.gcdA b g + (g : ℤ) * Nat.gcdB b g :=
      Nat.gcd_eq_gcd_ab b g
    refine ⟨fun x => if x = b then Nat.gcdA b g else Nat.gcdB b g * c x, ?_⟩
    rw [Finset.sum_insert hb]
    dsimp only
    rw [if_pos rfl]
    have hsum : ∑ a ∈ s, (if a = b then Nat.gcdA b g else Nat.gcdB b g * c a) * (a : ℤ) =
        Nat.gcdB b g * ∑ a ∈ s, c a * (a : ℤ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun a ha => ?_)
      have hne : a ≠ b := fun h => hb (h ▸ ha)
      rw [if_neg hne]
      ring
    rw [hsum, hc, Finset.gcd_insert]
    change Nat.gcdA b g * (b : ℤ) + Nat.gcdB b g * (g : ℤ) = ((Nat.gcd b g : ℕ) : ℤ)
    linarith

private lemma mul_mem_of_add_closed {A : Set ℕ}
    (hadd : ∀ a ∈ A, ∀ b ∈ A, a + b ∈ A) {a : ℕ} (ha : a ∈ A) :
    ∀ k : ℕ, 0 < k → k * a ∈ A
  | 0, hk => absurd hk (lt_irrefl 0)
  | 1, _ => by simpa using ha
  | k + 2, _ => by
    have ih := mul_mem_of_add_closed hadd ha (k + 1) (Nat.succ_pos k)
    have heq : (k + 2) * a = (k + 1) * a + a := by ring
    rw [heq]
    exact hadd _ ih _ ha

private lemma sum_pos_mul_mem_of_add_closed {A : Set ℕ}
    (hadd : ∀ a ∈ A, ∀ b ∈ A, a + b ∈ A)
    (F : Finset ℕ) (hF_ne : F.Nonempty) (hF : ∀ a ∈ F, a ∈ A)
    (w : ℕ → ℕ) (hw : ∀ a ∈ F, 0 < w a) :
    (∑ a ∈ F, w a * a) ∈ A := by
  induction F using Finset.induction_on with
  | empty => exact absurd hF_ne Finset.not_nonempty_empty
  | @insert b s hb ih =>
    rw [Finset.sum_insert hb]
    have hb_mem : w b * b ∈ A :=
      mul_mem_of_add_closed hadd (hF b (Finset.mem_insert_self b s))
        (w b) (hw b (Finset.mem_insert_self b s))
    by_cases hs : s.Nonempty
    · have hs_mem := ih hs
        (fun a ha => hF a (Finset.mem_insert_of_mem ha))
        (fun a ha => hw a (Finset.mem_insert_of_mem ha))
      exact hadd _ hb_mem _ hs_mem
    · rw [Finset.not_nonempty_iff_eq_empty.mp hs]
      simpa using hb_mem

/-- Schur's theorem: an additive subsemigroup of `ℕ` with gcd `1` contains all sufficiently large `n`. -/
lemma exists_all_ge_of_gcd_one {A : Set ℕ}
    (hadd : ∀ a ∈ A, ∀ b ∈ A, a + b ∈ A)
    (hne : ∃ a ∈ A, 0 < a)
    (hgcd : ∀ d : ℕ, (∀ a ∈ A, 0 < a → d ∣ a) → d = 1) :
    ∃ N : ℕ, ∀ n ≥ N, n ∈ A := by
  -- Step 1: find a finite nonempty subset `F ⊆ A ∩ {> 0}` with `F.gcd id = 1`
  have hexF : ∃ F : Finset ℕ, F.Nonempty ∧ (∀ a ∈ F, a ∈ A ∧ 0 < a) ∧ F.gcd id = 1 := by
    suffices h : ∀ g : ℕ, 0 < g →
        (∃ F : Finset ℕ, F.Nonempty ∧ (∀ a ∈ F, a ∈ A ∧ 0 < a) ∧ F.gcd id = g) →
        ∃ F : Finset ℕ, F.Nonempty ∧ (∀ a ∈ F, a ∈ A ∧ 0 < a) ∧ F.gcd id = 1 by
      obtain ⟨a₀, ha₀, ha₀_pos⟩ := hne
      exact h a₀ ha₀_pos ⟨{a₀}, Finset.singleton_nonempty a₀,
        fun a ha => by rw [Finset.mem_singleton.mp ha]; exact ⟨ha₀, ha₀_pos⟩, by simp⟩
    intro g
    induction g using Nat.strong_induction_on with
    | h g ih =>
      intro hg_pos ⟨F, hF_ne, hF, hFg⟩
      by_cases hg1 : g = 1
      · exact ⟨F, hF_ne, hF, hg1 ▸ hFg⟩
      · have hnotdiv : ¬ ∀ a ∈ A, 0 < a → g ∣ a := fun hd => hg1 (hgcd g hd)
        push Not at hnotdiv
        obtain ⟨b, hbA, hb_pos, hndiv⟩ := hnotdiv
        let F' := insert b F
        let g' := F'.gcd id
        have hg'_eq : g' = Nat.gcd b g := by
          dsimp [g', F']
          rw [Finset.gcd_insert, hFg]
          rfl
        have hg'_pos : 0 < g' := by
          rw [hg'_eq]
          exact Nat.gcd_pos_of_pos_left g hb_pos
        have hg'_lt : g' < g := by
          rw [hg'_eq]
          have hle : Nat.gcd b g ≤ g := Nat.gcd_le_right b hg_pos
          have hne_g : Nat.gcd b g ≠ g := fun heq => hndiv (heq ▸ Nat.gcd_dvd_left b g)
          exact lt_of_le_of_ne hle hne_g
        refine ih g' hg'_lt hg'_pos ⟨F', Finset.insert_nonempty b F, ?_, rfl⟩
        intro a ha
        rcases Finset.mem_insert.mp ha with rfl | haF
        · exact ⟨hbA, hb_pos⟩
        · exact hF a haF
  obtain ⟨F, hF_ne, hF, hFg⟩ := hexF
  -- Step 2: use Bézout to obtain `q ∈ A` (`q > 0`) and `q + 1 ∈ A`
  obtain ⟨c, hc⟩ := finset_gcd_bezout F
  rw [hFg] at hc
  let p : ℕ → ℕ := fun a => (c a).toNat + 1
  let q_coeff : ℕ → ℕ := fun a => (-c a).toNat + 1
  let P : ℕ := ∑ a ∈ F, p a * a
  let Q : ℕ := ∑ a ∈ F, q_coeff a * a
  have hP_mem : P ∈ A :=
    sum_pos_mul_mem_of_add_closed hadd F hF_ne (fun a ha => (hF a ha).1) p (fun _ _ => Nat.succ_pos _)
  have hQ_mem : Q ∈ A :=
    sum_pos_mul_mem_of_add_closed hadd F hF_ne (fun a ha => (hF a ha).1) q_coeff (fun _ _ => Nat.succ_pos _)
  have hQ_pos : 0 < Q := by
    obtain ⟨a₀, ha₀⟩ := hF_ne
    have h1 : 0 < q_coeff a₀ * a₀ := mul_pos (Nat.succ_pos _) (hF a₀ ha₀).2
    have h2 : q_coeff a₀ * a₀ ≤ Q :=
      Finset.single_le_sum (f := fun a => q_coeff a * a) (fun _ _ => Nat.zero_le _) ha₀
    exact lt_of_lt_of_le h1 h2
  have hPQ : P = Q + 1 := by
    have hZ : (P : ℤ) - (Q : ℤ) = 1 := by
      dsimp [P, Q]
      push_cast
      rw [← Finset.sum_sub_distrib]
      have hterm : ∀ a ∈ F, ((p a : ℤ) * (a : ℤ) - (q_coeff a : ℤ) * (a : ℤ)) = c a * (a : ℤ) := by
        intro a _
        dsimp [p, q_coeff]
        have hdiff : ((c a).toNat : ℤ) - ((-c a).toNat : ℤ) = c a := by
          rcases le_or_gt 0 (c a) with h | h
          · rw [Int.toNat_of_nonneg h, Int.toNat_of_nonpos (by linarith)]; ring
          · rw [Int.toNat_of_nonpos (le_of_lt h), Int.toNat_of_nonneg (by linarith)]; ring
        linear_combination (a : ℤ) * hdiff
      rw [Finset.sum_congr rfl hterm]
      exact_mod_cast hc
    omega
  -- Step 3: every `n ≥ Q * Q` lies in `A`
  refine ⟨Q * Q, fun n hn => ?_⟩
  let k := n / Q
  let r := n % Q
  have hr_lt : r < Q := Nat.mod_lt n hQ_pos
  have hk_ge : Q ≤ k := by
    have : Q * Q ≤ Q * k + r := by
      simpa [k, r] using (Nat.div_add_mod n Q).symm ▸ hn
    have : Q * Q < Q * (k + 1) := by
      calc Q * Q ≤ Q * k + r := this
        _ < Q * k + Q := Nat.add_lt_add_left hr_lt _
        _ = Q * (k + 1) := by ring
    exact Nat.le_of_lt_succ (Nat.lt_of_mul_lt_mul_left this)
  have hkr_pos : 0 < k - r := Nat.sub_pos_of_lt (lt_of_lt_of_le hr_lt hk_ge)
  have hdecomp : n = (k - r) * Q + r * P := by
    have hdiv : Q * k + r = n := Nat.div_add_mod n Q
    rw [hPQ]
    have hle : r ≤ k := le_of_lt (lt_of_lt_of_le hr_lt hk_ge)
    zify [hle]
    zify at hdiv
    linarith
  rw [hdecomp]
  have h1 : (k - r) * Q ∈ A := mul_mem_of_add_closed hadd hQ_mem (k - r) hkr_pos
  rcases Nat.eq_zero_or_pos r with hr0 | hr_pos
  · rw [hr0, zero_mul, add_zero]
    rwa [hr0] at h1
  · exact hadd _ h1 _ (mul_mem_of_add_closed hadd hP_mem r hr_pos)

/-- Every finite-state irreducible aperiodic Markov chain is primitive: `∃ m > 0, ∀ s s', P^m(s, s') > 0`. -/
theorem exists_matPow_pos {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    {P : S → S → ℝ}
    (hP_nonneg : ∀ s s', 0 ≤ P s s')
    (hirr : ∀ s s', ∃ n : ℕ, 0 < n ∧ 0 < matPow P n s s')
    (haper : ∀ s : S, ∀ d : ℕ, (∀ n : ℕ, 0 < n → 0 < matPow P n s s → d ∣ n) → d = 1) :
    ∃ m : ℕ, 0 < m ∧ ∀ s s' : S, 0 < matPow P m s s' := by
  have hself : ∀ s : S, ∃ N : ℕ, ∀ n ≥ N, 0 < matPow P n s s := by
    intro s
    let A : Set ℕ := {n | 0 < n ∧ 0 < matPow P n s s}
    have hadd : ∀ a ∈ A, ∀ b ∈ A, a + b ∈ A := by
      intro a ha b hb
      exact ⟨Nat.add_pos_left ha.1 b, matPow_pos_add hP_nonneg ha.2 hb.2⟩
    have hne : ∃ a ∈ A, 0 < a := by
      obtain ⟨n, hn, hpos⟩ := hirr s s
      exact ⟨n, ⟨hn, hpos⟩, hn⟩
    have hgcd : ∀ d : ℕ, (∀ a ∈ A, 0 < a → d ∣ a) → d = 1 :=
      fun d hd => haper s d (fun n hn hpos => hd n ⟨hn, hpos⟩ hn)
    obtain ⟨N, hN⟩ := exists_all_ge_of_gcd_one hadd hne hgcd
    exact ⟨N, fun n hn => (hN n hn).2⟩
  choose N hN using hself
  choose K hK_pos hK_mat using hirr
  let Nmax : ℕ := Finset.univ.sup N
  let Kmax : ℕ := Finset.univ.sup (fun p : S × S => K p.1 p.2)
  let m : ℕ := Nmax + Kmax + 1
  refine ⟨m, Nat.succ_pos _, fun s s' => ?_⟩
  have hKm : K s s' ≤ Kmax := Finset.le_sup (f := fun p : S × S => K p.1 p.2) (Finset.mem_univ (s, s'))
  have hNm : N s ≤ Nmax := Finset.le_sup (f := N) (Finset.mem_univ s)
  have hsub_ge : N s ≤ m - K s s' := by omega
  have hsplit : m = (m - K s s') + K s s' := by omega
  rw [hsplit]
  exact matPow_pos_add hP_nonneg (hN s (m - K s s') hsub_ge) (hK_mat s s')

/-! ### Doeblin `L¹` contraction & geometric mixing -/

private lemma l1_nonexpansive {S : Type*} [Fintype S] [DecidableEq S]
    {P : S → S → ℝ} (hP_nonneg : ∀ s s', 0 ≤ P s s') (hP_sum : ∀ s, ∑ s', P s s' = 1)
    (v : S → ℝ) :
    ∑ s', |∑ s, v s * P s s'| ≤ ∑ s, |v s| := by
  calc
    ∑ s', |∑ s, v s * P s s'|
        ≤ ∑ s', ∑ s, |v s * P s s'| :=
          Finset.sum_le_sum (fun s' _ => Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ s', ∑ s, |v s| * P s s' := by
          refine Finset.sum_congr rfl (fun s' _ => Finset.sum_congr rfl (fun s _ => ?_))
          rw [abs_mul, abs_of_nonneg (hP_nonneg s s')]
    _ = ∑ s, |v s| * ∑ s', P s s' := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun s _ => (Finset.mul_sum _ _ _).symm)
    _ = ∑ s, |v s| := by simp [hP_sum]

private lemma l1_doeblin_contraction {S : Type*} [Fintype S] [DecidableEq S]
    {Q : S → S → ℝ} (hQ_sum : ∀ s, ∑ s', Q s s' = 1)
    {ε : ℝ} (hε_le : ∀ s s', ε ≤ Q s s')
    {v : S → ℝ} (hv_zero : ∑ s, v s = 0) :
    ∑ s', |∑ s, v s * Q s s'| ≤ (1 - (Fintype.card S : ℝ) * ε) * ∑ s, |v s| := by
  have hshift : ∀ s', ∑ s, v s * Q s s' = ∑ s, v s * (Q s s' - ε) := by
    intro s'
    have h1 : ∑ s, v s * (Q s s' - ε) = ∑ s, v s * Q s s' - (∑ s, v s) * ε := by
      simp_rw [mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
    rw [h1, hv_zero, zero_mul, sub_zero]
  simp_rw [hshift]
  calc
    ∑ s', |∑ s, v s * (Q s s' - ε)|
        ≤ ∑ s', ∑ s, |v s * (Q s s' - ε)| :=
          Finset.sum_le_sum (fun s' _ => Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ s', ∑ s, |v s| * (Q s s' - ε) := by
          refine Finset.sum_congr rfl (fun s' _ => Finset.sum_congr rfl (fun s _ => ?_))
          rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr (hε_le s s'))]
    _ = ∑ s, |v s| * ∑ s', (Q s s' - ε) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun s _ => (Finset.mul_sum _ _ _).symm)
    _ = ∑ s, |v s| * (1 - (Fintype.card S : ℝ) * ε) := by
          refine Finset.sum_congr rfl (fun s _ => ?_)
          rw [Finset.sum_sub_distrib, hQ_sum s, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = (1 - (Fintype.card S : ℝ) * ε) * ∑ s, |v s| := by
          rw [← Finset.sum_mul, mul_comm]

/-- Doeblin geometric mixing in total variation (`L¹`) for any finite irreducible aperiodic
Markov chain: `∃ C > 0, ∃ ρ ∈ (0, 1), ∀ n s, ∑ s', |P^n(s, s') - π(s')| ≤ C * ρ ^ n`. -/
theorem exists_geometric_mixing {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    {P : S → S → ℝ} {π : S → ℝ}
    (hP_nonneg : ∀ s s', 0 ≤ P s s')
    (hP_sum : ∀ s, ∑ s', P s s' = 1)
    (hirr : ∀ s s', ∃ n : ℕ, 0 < n ∧ 0 < matPow P n s s')
    (haper : ∀ s : S, ∀ d : ℕ, (∀ n : ℕ, 0 < n → 0 < matPow P n s s → d ∣ n) → d = 1)
    (hπ_nonneg : ∀ s, 0 ≤ π s)
    (hπ_sum : ∑ s, π s = 1)
    (hπ_stat : ∀ s', ∑ s, π s * P s s' = π s') :
    ∃ (C ρ : ℝ), 0 < C ∧ 0 < ρ ∧ ρ < 1 ∧
      ∀ (n : ℕ) (s : S), ∑ s', |matPow P n s s' - π s'| ≤ C * ρ ^ n := by
  obtain ⟨m, hm_pos, hm_mat⟩ := exists_matPow_pos hP_nonneg hirr haper
  let Q := matPow P m
  have hQ_sum : ∀ s, ∑ s', Q s s' = 1 := matPow_sum_one hP_sum m
  have huniv_ne : (Finset.univ : Finset (S × S)).Nonempty := Finset.univ_nonempty
  let ε : ℝ := Finset.univ.inf' huniv_ne (fun p : S × S => Q p.1 p.2)
  have hε_pos : 0 < ε := by
    rw [Finset.lt_inf'_iff]
    intro p _
    exact hm_mat p.1 p.2
  have hε_le : ∀ s s', ε ≤ Q s s' := fun s s' =>
    Finset.inf'_le (fun p : S × S => Q p.1 p.2) (Finset.mem_univ (s, s'))
  have hcard_pos : (0 : ℝ) < (Fintype.card S : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hγ_lt_one : 1 - (Fintype.card S : ℝ) * ε < 1 := by nlinarith
  have hγ_nonneg : 0 ≤ 1 - (Fintype.card S : ℝ) * ε := by
    obtain ⟨s₀⟩ := ‹Nonempty S›
    have hsum_le : (Fintype.card S : ℝ) * ε ≤ ∑ s', Q s₀ s' := by
      calc (Fintype.card S : ℝ) * ε = ∑ _s' : S, ε := by simp
        _ ≤ ∑ s' : S, Q s₀ s' := Finset.sum_le_sum (fun s' _ => hε_le s₀ s')
    rw [hQ_sum s₀] at hsum_le
    linarith
  let γ : ℝ := max (1 - (Fintype.card S : ℝ) * ε) (1 / 2)
  have hγ_pos : 0 < γ := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hγ_lt1 : γ < 1 := max_lt hγ_lt_one (by norm_num)
  have hγ_ge : 1 - (Fintype.card S : ℝ) * ε ≤ γ := le_max_left _ _
  -- Bound `L¹` distance at step `n`: monotone nonincreasing and contracts by `γ` every `m` steps
  have h_step : ∀ (n : ℕ) (s : S),
      ∑ s', |matPow P (n + 1) s s' - π s'| ≤ ∑ s', |matPow P n s s' - π s'| := by
    intro n s
    have hdiff : ∀ s', matPow P (n + 1) s s' - π s' =
        ∑ u, (matPow P n s u - π u) * P u s' := by
      intro s'
      calc matPow P (n + 1) s s' - π s'
          = (∑ u, matPow P n s u * P u s') - (∑ u, π u * P u s') := by rw [matPow, hπ_stat s']
        _ = ∑ u, (matPow P n s u - π u) * P u s' := by
              rw [← Finset.sum_sub_distrib]
              refine Finset.sum_congr rfl (fun u _ => by ring)
    simp_rw [hdiff]
    exact l1_nonexpansive hP_nonneg hP_sum _
  have h_mono : ∀ (a b : ℕ) (s : S), a ≤ b →
      ∑ s', |matPow P b s s' - π s'| ≤ ∑ s', |matPow P a s s' - π s'| := by
    intro a b s hab
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
    clear hab
    induction d with
    | zero => simp
    | succ k ih =>
      rw [← Nat.add_assoc]
      exact le_trans (h_step (a + k) s) ih
  have h_block : ∀ (n : ℕ) (s : S),
      ∑ s', |matPow P (n + m) s s' - π s'| ≤ γ * ∑ s', |matPow P n s s' - π s'| := by
    intro n s
    have hdiff : ∀ s', matPow P (n + m) s s' - π s' =
        ∑ u, (matPow P n s u - π u) * Q u s' := by
      intro s'
      calc matPow P (n + m) s s' - π s'
          = (∑ u, matPow P n s u * Q u s') - (∑ u, π u * Q u s') := by
              rw [matPow_add, matPow_stationary hπ_stat m s']
        _ = ∑ u, (matPow P n s u - π u) * Q u s' := by
              rw [← Finset.sum_sub_distrib]
              refine Finset.sum_congr rfl (fun u _ => by ring)
    have hzero : ∑ u, (matPow P n s u - π u) = 0 := by
      rw [Finset.sum_sub_distrib, matPow_sum_one hP_sum n s, hπ_sum, sub_self]
    simp_rw [hdiff]
    have h1 := l1_doeblin_contraction hQ_sum hε_le hzero
    exact le_trans h1 (mul_le_mul_of_nonneg_right hγ_ge (Finset.sum_nonneg (fun _ _ => abs_nonneg _)))
  have h_base : ∀ s : S, ∑ s', |matPow P 0 s s' - π s'| ≤ 2 := by
    intro s
    calc ∑ s', |matPow P 0 s s' - π s'|
        ≤ ∑ s', (|matPow P 0 s s'| + |π s'|) :=
          Finset.sum_le_sum (fun s' _ => abs_sub _ _)
      _ = (∑ s', matPow P 0 s s') + (∑ s', π s') := by
          rw [Finset.sum_add_distrib]
          congr 1
          · refine Finset.sum_congr rfl (fun s' _ => abs_of_nonneg (matPow_nonneg hP_nonneg 0 s s'))
          · refine Finset.sum_congr rfl (fun s' _ => abs_of_nonneg (hπ_nonneg s'))
      _ = 2 := by rw [matPow_sum_one hP_sum 0 s, hπ_sum]; norm_num
  have h_km : ∀ (k : ℕ) (s : S), ∑ s', |matPow P (k * m) s s' - π s'| ≤ 2 * γ ^ k := by
    intro k s
    induction k with
    | zero => simpa using h_base s
    | succ j ih =>
      have heq : (j + 1) * m = j * m + m := by ring
      rw [heq, pow_succ]
      calc ∑ s', |matPow P (j * m + m) s s' - π s'|
          ≤ γ * ∑ s', |matPow P (j * m) s s' - π s'| := h_block (j * m) s
        _ ≤ γ * (2 * γ ^ j) := mul_le_mul_of_nonneg_left ih (le_of_lt hγ_pos)
        _ = 2 * (γ ^ j * γ) := by ring
  -- Convert `γ ^ (n / m)` to `C * ρ ^ n` with `ρ := γ ^ (1 / m)` and `C := 2 / γ`
  let ρ : ℝ := γ ^ ((1 : ℝ) / (m : ℝ))
  have hm_real_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm_pos
  have hρ_pos : 0 < ρ := Real.rpow_pos_of_pos hγ_pos _
  have hρ_lt1 : ρ < 1 := Real.rpow_lt_one (le_of_lt hγ_pos) hγ_lt1 (by positivity)
  have hρ_pow_m : ρ ^ m = γ := by
    dsimp [ρ]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hγ_pos), one_div_mul_cancel hm_real_pos.ne',
      Real.rpow_one]
  refine ⟨2 / γ, ρ, div_pos two_pos hγ_pos, hρ_pos, hρ_lt1, fun n s => ?_⟩
  let k := n / m
  have hkm_le : k * m ≤ n := Nat.div_mul_le_self n m
  have hn_le : n ≤ (k + 1) * m := by
    have := Nat.lt_div_mul_add (a := n) hm_pos
    have heq : n / m * m + m = (k + 1) * m := by dsimp [k]; ring
    omega
  have h1 : ∑ s', |matPow P n s s' - π s'| ≤ 2 * γ ^ k :=
    le_trans (h_mono (k * m) n s hkm_le) (h_km k s)
  have h2 : γ ^ (k + 1) ≤ ρ ^ n := by
    calc γ ^ (k + 1) = (ρ ^ m) ^ (k + 1) := by rw [hρ_pow_m]
      _ = ρ ^ ((k + 1) * m) := by rw [← pow_mul, mul_comm]
      _ ≤ ρ ^ n := pow_le_pow_of_le_one (le_of_lt hρ_pos) (le_of_lt hρ_lt1) hn_le
  have h3 : γ ^ k ≤ (1 / γ) * ρ ^ n := by
    rw [one_div, inv_mul_eq_div, le_div_iff₀ hγ_pos]
    simpa [pow_succ] using h2
  calc ∑ s', |matPow P n s s' - π s'| ≤ 2 * γ ^ k := h1
    _ ≤ 2 * ((1 / γ) * ρ ^ n) := mul_le_mul_of_nonneg_left h3 (by norm_num)
    _ = (2 / γ) * ρ ^ n := by ring

/-! ### Poisson potential and convergent intervals -/

/-- Poisson potential `h_f(s) = ∑'_{n=0}^∞ ∑_{s'} (P^n(s, s') - π(s')) f(s')`. -/
noncomputable def poissonPotential {S : Type*} [Fintype S] [DecidableEq S]
    (P : S → S → ℝ) (π f : S → ℝ) (s : S) : ℝ :=
  ∑' n : ℕ, ∑ s', (matPow P n s s' - π s') * f s'

section PoissonAndConvergent

variable {S : Type*} [Fintype S] [DecidableEq S]

lemma summable_poisson_term {P : S → S → ℝ} {π : S → ℝ} {C ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hmix : ∀ n s, ∑ s', |matPow P n s s' - π s'| ≤ C * ρ ^ n)
    (f : S → ℝ) {M : ℝ} (hM : ∀ s', |f s'| ≤ M) (s : S) :
    Summable (fun n : ℕ => ∑ s', (matPow P n s s' - π s') * f s') := by
  have hgeom : Summable (fun n : ℕ => (C * M) * ρ ^ n) :=
    (summable_geometric_of_lt_one hρ0 hρ1).mul_left (C * M)
  refine Summable.of_norm_bounded hgeom (fun n => ?_)
  rw [Real.norm_eq_abs]
  calc
    |∑ s', (matPow P n s s' - π s') * f s'|
        ≤ ∑ s', |(matPow P n s s' - π s') * f s'| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ s', |matPow P n s s' - π s'| * |f s'| := by
          refine Finset.sum_congr rfl (fun s' _ => abs_mul _ _)
    _ ≤ ∑ s', |matPow P n s s' - π s'| * M :=
          Finset.sum_le_sum (fun s' _ => mul_le_mul_of_nonneg_left (hM s') (abs_nonneg _))
    _ = (∑ s', |matPow P n s s' - π s'|) * M := (Finset.sum_mul _ _ _).symm
    _ ≤ (C * ρ ^ n) * M :=
          mul_le_mul_of_nonneg_right (hmix n s) (le_trans (abs_nonneg _) (hM s))
    _ = (C * M) * ρ ^ n := by ring

lemma abs_poissonPotential_le {P : S → S → ℝ} {π : S → ℝ} {C ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hmix : ∀ n s, ∑ s', |matPow P n s s' - π s'| ≤ C * ρ ^ n)
    (f : S → ℝ) {M : ℝ} (hM : ∀ s', |f s'| ≤ M) (s : S) :
    |poissonPotential P π f s| ≤ (C / (1 - ρ)) * M := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM s)
  have hgeom : Summable (fun n : ℕ => (C * M) * ρ ^ n) :=
    (summable_geometric_of_lt_one hρ0 hρ1).mul_left (C * M)
  have hbound : ∀ n : ℕ, |∑ s', (matPow P n s s' - π s') * f s'| ≤ (C * M) * ρ ^ n := by
    intro n
    calc |∑ s', (matPow P n s s' - π s') * f s'|
        ≤ ∑ s', |matPow P n s s' - π s'| * |f s'| := by
            refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
            exact Finset.sum_le_sum (fun s' _ => by rw [abs_mul])
      _ ≤ ∑ s', |matPow P n s s' - π s'| * M :=
            Finset.sum_le_sum (fun s' _ => mul_le_mul_of_nonneg_left (hM s') (abs_nonneg _))
      _ = (∑ s', |matPow P n s s' - π s'|) * M := (Finset.sum_mul _ _ _).symm
      _ ≤ (C * ρ ^ n) * M := mul_le_mul_of_nonneg_right (hmix n s) hM0
      _ = (C * M) * ρ ^ n := by ring
  have hnorm_sum : Summable (fun n : ℕ => ‖∑ s', (matPow P n s s' - π s') * f s'‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => by simpa [Real.norm_eq_abs] using hbound n) hgeom
  calc |poissonPotential P π f s|
      = ‖∑' n : ℕ, ∑ s', (matPow P n s s' - π s') * f s'‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' n : ℕ, ‖∑ s', (matPow P n s s' - π s') * f s'‖ := norm_tsum_le_tsum_norm hnorm_sum
    _ ≤ ∑' n : ℕ, (C * M) * ρ ^ n :=
          hnorm_sum.tsum_le_tsum (fun n => by simpa [Real.norm_eq_abs] using hbound n) hgeom
    _ = (C * M) * (1 - ρ)⁻¹ := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one hρ0 hρ1]
    _ = (C / (1 - ρ)) * M := by ring

lemma abs_poissonPotential_sub_le {P : S → S → ℝ} {π : S → ℝ} {C ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hmix : ∀ n s, ∑ s', |matPow P n s s' - π s'| ≤ C * ρ ^ n)
    (f₁ f₂ : S → ℝ) {M : ℝ} (hM : ∀ s', |f₁ s' - f₂ s'| ≤ M) (s : S) :
    |poissonPotential P π f₁ s - poissonPotential P π f₂ s| ≤ (C / (1 - ρ)) * M := by
  have hM1 : ∃ M₁, ∀ s', |f₁ s'| ≤ M₁ :=
    ⟨Finset.univ.sup' ⟨s, Finset.mem_univ s⟩ (fun s' => |f₁ s'|),
      fun s' => Finset.le_sup' (fun s' => |f₁ s'|) (Finset.mem_univ s')⟩
  have hM2 : ∃ M₂, ∀ s', |f₂ s'| ≤ M₂ :=
    ⟨Finset.univ.sup' ⟨s, Finset.mem_univ s⟩ (fun s' => |f₂ s'|),
      fun s' => Finset.le_sup' (fun s' => |f₂ s'|) (Finset.mem_univ s')⟩
  obtain ⟨M₁, hM₁⟩ := hM1
  obtain ⟨M₂, hM₂⟩ := hM2
  have hs1 := summable_poisson_term hρ0 hρ1 hmix f₁ hM₁ s
  have hs2 := summable_poisson_term hρ0 hρ1 hmix f₂ hM₂ s
  have hsub : poissonPotential P π f₁ s - poissonPotential P π f₂ s =
      poissonPotential P π (fun s' => f₁ s' - f₂ s') s := by
    unfold poissonPotential
    rw [← hs1.tsum_sub hs2]
    congr 1
    funext n
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun s' _ => by ring)
  rw [hsub]
  exact abs_poissonPotential_le hρ0 hρ1 hmix (fun s' => f₁ s' - f₂ s') hM s

/-- Poisson's equation: `h_f(s) - ∑_u P(s, u) h_f(u) = f(s) - ∑_{s'} π(s') f(s')`. -/
lemma poisson_equation {P : S → S → ℝ} {π : S → ℝ} {C ρ : ℝ}
    (hP_sum : ∀ s, ∑ s', P s s' = 1)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hmix : ∀ n s, ∑ s', |matPow P n s s' - π s'| ≤ C * ρ ^ n)
    (f : S → ℝ) (s : S) :
    poissonPotential P π f s - ∑ u, P s u * poissonPotential P π f u =
      f s - ∑ s', π s' * f s' := by
  have hM : ∃ M, ∀ s', |f s'| ≤ M :=
    ⟨Finset.univ.sup' ⟨s, Finset.mem_univ s⟩ (fun s' => |f s'|),
      fun s' => Finset.le_sup' (fun s' => |f s'|) (Finset.mem_univ s')⟩
  obtain ⟨M, hM⟩ := hM
  have hs : ∀ u, Summable (fun n : ℕ => ∑ s', (matPow P n u s' - π s') * f s') :=
    fun u => summable_poisson_term hρ0 hρ1 hmix f hM u
  have hsplit : poissonPotential P π f s =
      (∑ s', (matPow P 0 s s' - π s') * f s') +
      ∑' n : ℕ, ∑ s', (matPow P (n + 1) s s' - π s') * f s' :=
    (hs s).tsum_eq_zero_add
  have h0 : ∑ s', (matPow P 0 s s' - π s') * f s' = f s - ∑ s', π s' * f s' := by
    simp [matPow, sub_mul, Finset.sum_sub_distrib]
  have htail : ∑ u, P s u * poissonPotential P π f u =
      ∑' n : ℕ, ∑ s', (matPow P (n + 1) s s' - π s') * f s' := by
    unfold poissonPotential
    simp_rw [← tsum_mul_left]
    rw [← Summable.tsum_finsetSum (fun u _ => (hs u).mul_left (P s u))]
    congr 1
    funext n
    have hstep : ∑ u, P s u * ∑ s', (matPow P n u s' - π s') * f s' =
        ∑ s', (∑ u, P s u * (matPow P n u s' - π s')) * f s' := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun s' _ => ?_)
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun u _ => by ring)
    rw [hstep]
    refine Finset.sum_congr rfl (fun s' _ => ?_)
    congr 1
    simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hP_sum s, one_mul, matPow_succ_left]
  rw [hsplit, h0, htail]
  ring

/-- Convergent-interval existence for Theorem 3: for every `ν > 0`, there exists `T ≥ 1`
such that the `T`-step Cesàro average of `P^τ(s₀, ·)` is within `ν` of `π` in `L¹` for all `s₀`. -/
theorem exists_convergent_interval {P : S → S → ℝ} {π : S → ℝ} {C ρ : ℝ}
    (hC : 0 < C) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hmix : ∀ n s, ∑ s', |matPow P n s s' - π s'| ≤ C * ρ ^ n)
    {ν : ℝ} (hν : 0 < ν) :
    ∃ T : ℕ, 0 < T ∧ ∀ s₀ : S,
      ∑ s', |π s' - (1 / (T : ℝ)) * ∑ τ ∈ Finset.range T, matPow P τ s₀ s'| ≤ ν := by
  have h1ρ : 0 < 1 - ρ := sub_pos.mpr hρ1
  let B : ℝ := C / (1 - ρ)
  obtain ⟨T₀, hT₀⟩ := exists_nat_gt (B / ν)
  let T : ℕ := max T₀ 1
  have hT_pos : 0 < T := lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)
  have hT_real_pos : (0 : ℝ) < (T : ℝ) := Nat.cast_pos.mpr hT_pos
  refine ⟨T, hT_pos, fun s₀ => ?_⟩
  have hrewrite : ∀ s',
      |π s' - (1 / (T : ℝ)) * ∑ τ ∈ Finset.range T, matPow P τ s₀ s'| =
      (1 / (T : ℝ)) * |∑ τ ∈ Finset.range T, (matPow P τ s₀ s' - π s')| := by
    intro s'
    have heq : π s' - (1 / (T : ℝ)) * ∑ τ ∈ Finset.range T, matPow P τ s₀ s' =
        -(1 / (T : ℝ)) * ∑ τ ∈ Finset.range T, (matPow P τ s₀ s' - π s') := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp [hT_real_pos.ne']
      ring
    rw [heq, abs_mul, abs_neg, abs_of_pos (one_div_pos.mpr hT_real_pos)]
  simp_rw [hrewrite, ← Finset.mul_sum]
  have hsum_le : ∑ s', |∑ τ ∈ Finset.range T, (matPow P τ s₀ s' - π s')| ≤ B := by
    calc ∑ s', |∑ τ ∈ Finset.range T, (matPow P τ s₀ s' - π s')|
        ≤ ∑ s', ∑ τ ∈ Finset.range T, |matPow P τ s₀ s' - π s'| :=
          Finset.sum_le_sum (fun s' _ => Finset.abs_sum_le_sum_abs _ _)
      _ = ∑ τ ∈ Finset.range T, ∑ s', |matPow P τ s₀ s' - π s'| := Finset.sum_comm
      _ ≤ ∑ τ ∈ Finset.range T, C * ρ ^ τ := Finset.sum_le_sum (fun τ _ => hmix τ s₀)
      _ = C * ∑ τ ∈ Finset.range T, ρ ^ τ := (Finset.mul_sum _ _ _).symm
      _ ≤ C * (1 - ρ)⁻¹ := by
          refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hC)
          rw [← tsum_geometric_of_lt_one hρ0 hρ1]
          exact (summable_geometric_of_lt_one hρ0 hρ1).sum_le_tsum (Finset.range T)
            (fun n _ => pow_nonneg hρ0 n)
      _ = B := by dsimp [B]; ring
  have hB_div : B / (T : ℝ) ≤ ν := by
    have h1 : B / ν < (T : ℝ) := lt_of_lt_of_le hT₀ (by exact_mod_cast le_max_left T₀ 1)
    have h2 : B < ν * (T : ℝ) := by linarith [(div_lt_iff₀ hν).mp h1]
    exact le_of_lt ((div_lt_iff₀ hT_real_pos).mpr h2)
  calc (1 / (T : ℝ)) * ∑ s', |∑ τ ∈ Finset.range T, (matPow P τ s₀ s' - π s')|
      ≤ (1 / (T : ℝ)) * B := mul_le_mul_of_nonneg_left hsum_le (by positivity)
    _ = B / (T : ℝ) := by ring
    _ ≤ ν := hB_div

end PoissonAndConvergent

end LifoBackpressure.Routine
