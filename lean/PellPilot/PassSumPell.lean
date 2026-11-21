import Mathlib

/-!
# Lean pilot: the Pell chain of the pass-sum paper, Proposition 4.4

Source: R. L. Hampton Jr., "Proof pieces for a Mellin-Barnes closed form of a pass sum",
revision r5f (30 October 2026), Section 2.2 (notation), Section 4.5 (Proposition 4.4) and
Section 4.6 (Proposition W).

What is formalized here is the integer and binomial part only. The analytic link from the
meeting residues of `H Φ u^{-s}` to the number `Q_{p+l}(-l)` (Lemma 4.2 (c) and the display
`G_l = R_l Q_{p+l}(-l) / L`) is not formalized; it stays in the paper.

* Part 1 (target T1): the chain of `y^2 - 3 b^2 = -2`, every member solves it, and every
  solution with `y, b ≥ 0` is a member, by a descent that strictly lowers `b` and ends at the
  base `(1, 1)`.
* Part 2 (target T2, first half): the paper's binomial and `Q_n(s)`, the reflection form (V),
  and Step 3 of the proof as integer identities, all symbolic.
* Part 3 (target T2, second half): Proposition 4.4 (a) to (d) as the paper states it.
* Part 4 (target T3): Proposition W (a) to (e) for the weights `(1, k, 1)`, the two swaps and
  the descent for `t^2 - k t x + x^2 = t + x`, the bridge to Part 3 at `k = 4`, the identities
  of Proposition B, and the forms at `k = 2` and `k = 3`.

Every statement is about a field `K` of characteristic zero where `Q_n` is evaluated; the
paper's `Q_n` is over `ℂ`, which is such a field. Compile with
`lake env lean PellPilot/PassSumPell.lean`; the `#print axioms` lines at the end list the
axioms each theorem rests on.
-/

namespace PellPilot

/-! ## Part 1. The chain of `y^2 - 3 b^2 = -2` -/

/-- One step up the chain: multiplication by the unit `2 + √3`, `(y, b) ↦ (2y + 3b, y + 2b)`. -/
def up (v : ℤ × ℤ) : ℤ × ℤ := (2 * v.1 + 3 * v.2, v.1 + 2 * v.2)

/-- The descent map: multiplication by `2 - √3`, `(y, b) ↦ (2y - 3b, 2b - y)`. -/
def down (v : ℤ × ℤ) : ℤ × ℤ := (2 * v.1 - 3 * v.2, 2 * v.2 - v.1)

/-- The chain `chain k = (y_k, b_k)`, from the base `(y_0, b_0) = (1, 1)` by the step `up`. -/
def chain : ℕ → ℤ × ℤ
  | 0 => (1, 1)
  | k + 1 => up (chain k)

/-- The Pell-type equation `y^2 - 3 b^2 = -2` for a pair `v = (y, b)`. -/
def IsSol (v : ℤ × ℤ) : Prop := v.1 ^ 2 - 3 * v.2 ^ 2 = -2

theorem down_up (v : ℤ × ℤ) : down (up v) = v := by
  obtain ⟨y, b⟩ := v
  simp only [up, down, Prod.mk.injEq]
  constructor <;> ring

theorem up_down (v : ℤ × ℤ) : up (down v) = v := by
  obtain ⟨y, b⟩ := v
  simp only [up, down, Prod.mk.injEq]
  constructor <;> ring

theorem up_isSol {v : ℤ × ℤ} (h : IsSol v) : IsSol (up v) := by
  obtain ⟨y, b⟩ := v
  simp only [IsSol, up] at *
  linear_combination h

theorem down_isSol {v : ℤ × ℤ} (h : IsSol v) : IsSol (down v) := by
  obtain ⟨y, b⟩ := v
  simp only [IsSol, down] at *
  linear_combination h

/-- Every member of the chain solves `y^2 - 3 b^2 = -2`. -/
theorem chain_isSol (k : ℕ) : IsSol (chain k) := by
  induction k with
  | zero => norm_num [IsSol, chain]
  | succ k ih => exact up_isSol ih

/-- Every member of the chain has positive components. -/
theorem chain_pos (k : ℕ) : 0 < (chain k).1 ∧ 0 < (chain k).2 := by
  induction k with
  | zero => norm_num [chain]
  | succ k ih =>
    simp only [chain, up]
    constructor <;> linarith [ih.1, ih.2]

/-- The chain is the sequence `y_k + b_k √3 = (1 + √3) (2 + √3)^k` in `ℤ[√3]`. -/
theorem chain_eq_sqrt3 (k : ℕ) :
    (⟨(chain k).1, (chain k).2⟩ : ℤ√3) = (1 + Zsqrtd.sqrtd) * (2 + Zsqrtd.sqrtd) ^ k := by
  induction k with
  | zero => ext <;> simp [chain]
  | succ k ih =>
    rw [pow_succ, ← mul_assoc, ← ih]
    ext <;> simp [chain, up] <;> ring

/-- The paper's norm argument: `N(1 + √3) = -2`, `N(2 + √3) = 1`, and the norm is multiplicative. -/
theorem norm_chain_sqrt3 (k : ℕ) :
    Zsqrtd.norm ((1 + Zsqrtd.sqrtd) * (2 + Zsqrtd.sqrtd) ^ k : ℤ√3) = -2 := by
  have h1 : Zsqrtd.norm (1 + Zsqrtd.sqrtd : ℤ√3) = -2 := by
    simp [Zsqrtd.norm_def]
  have h2 : Zsqrtd.norm (2 + Zsqrtd.sqrtd : ℤ√3) = 1 := by
    simp [Zsqrtd.norm_def]
  have hp : ∀ j : ℕ, Zsqrtd.norm ((2 + Zsqrtd.sqrtd : ℤ√3) ^ j) = 1 := by
    intro j
    induction j with
    | zero => simp
    | succ j ihj => rw [pow_succ, Zsqrtd.norm_mul, ihj, h2]; norm_num
  rw [Zsqrtd.norm_mul, h1, hp]; norm_num

/-- The descent map sends a solution with `y ≥ 0`, `b ≥ 2` to a solution with both components
positive and with a strictly smaller `b`. -/
theorem down_pos_lt {v : ℤ × ℤ} (h : IsSol v) (hy : 0 ≤ v.1) (hb : 2 ≤ v.2) :
    0 < (down v).1 ∧ 0 < (down v).2 ∧ (down v).2 < v.2 := by
  obtain ⟨y, b⟩ := v
  simp only [IsSol, down] at *
  refine ⟨?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · nlinarith

/-- The base: the only solution with `y ≥ 0` and `0 ≤ b ≤ 1` is `(1, 1)`. -/
theorem base_of_le_one {v : ℤ × ℤ} (h : IsSol v) (hy : 0 ≤ v.1) (hb0 : 0 ≤ v.2) (hb : v.2 ≤ 1) :
    v = (1, 1) := by
  obtain ⟨y, b⟩ := v
  simp only [IsSol] at *
  have hb' : b = 0 ∨ b = 1 := by omega
  rcases hb' with rfl | rfl
  · nlinarith
  · have hy1 : y = 1 := by nlinarith
    rw [hy1]

theorem chain_complete_aux (N : ℕ) : ∀ v : ℤ × ℤ, IsSol v → 0 ≤ v.1 → 0 ≤ v.2 →
    v.2 ≤ N → ∃ k, chain k = v := by
  induction N with
  | zero =>
    intro v h hy hb hN
    exact ⟨0, (base_of_le_one h hy hb (by omega)).symm⟩
  | succ N ih =>
    intro v h hy hb hN
    by_cases hb1 : v.2 ≤ 1
    · exact ⟨0, (base_of_le_one h hy hb hb1).symm⟩
    · obtain ⟨h1, h2, h3⟩ := down_pos_lt h hy (by omega)
      obtain ⟨k, hk⟩ := ih (down v) (down_isSol h) h1.le h2.le (by omega)
      exact ⟨k + 1, by rw [chain, hk, up_down]⟩

/-- Completeness: every solution of `y^2 - 3 b^2 = -2` with `y ≥ 0` and `b ≥ 0` is a member of
the chain. -/
theorem chain_complete {y b : ℤ} (h : y ^ 2 - 3 * b ^ 2 = -2) (hy : 0 ≤ y) (hb : 0 ≤ b) :
    ∃ k, chain k = (y, b) :=
  chain_complete_aux b.toNat (y, b) h hy hb (by simp only; omega)

/-- The descent ends at the base: `k` steps down from `chain k` reach `(1, 1)`. -/
theorem down_iterate_chain (k : ℕ) : down^[k] (chain k) = (1, 1) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, chain, down_up, ih]

/-- Every nonnegative solution reaches the base `(1, 1)` under finitely many descent steps. -/
theorem descent_reaches_base {y b : ℤ} (h : y ^ 2 - 3 * b ^ 2 = -2) (hy : 0 ≤ y) (hb : 0 ≤ b) :
    ∃ k, down^[k] (y, b) = (1, 1) := by
  obtain ⟨k, hk⟩ := chain_complete h hy hb
  exact ⟨k, by rw [← hk, down_iterate_chain]⟩

/-- Both sequences satisfy `x_{k+2} = 4 x_{k+1} - x_k`. -/
theorem chain_rec (k : ℕ) :
    (chain (k + 2)).1 = 4 * (chain (k + 1)).1 - (chain k).1 ∧
    (chain (k + 2)).2 = 4 * (chain (k + 1)).2 - (chain k).2 := by
  simp only [chain, up]
  constructor <;> ring

/-- Every `y_k` and every `b_k` is odd. -/
theorem chain_odd (k : ℕ) : (chain k).1 % 2 = 1 ∧ (chain k).2 % 2 = 1 := by
  induction k with
  | zero => norm_num [chain]
  | succ k ih =>
    simp only [chain, up]
    omega

/-- `b_k` is strictly increasing. -/
theorem chain_b_lt (k : ℕ) : (chain k).2 < (chain (k + 1)).2 := by
  simp only [chain, up]
  linarith [(chain_pos k).1, (chain_pos k).2]

theorem chain_b_ge_three {k : ℕ} (hk : 1 ≤ k) : 3 ≤ (chain k).2 := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk'
    · norm_num [chain, up]
    · have := ih hk'
      have := chain_b_lt k
      omega

/-- The first values of the chain. -/
theorem chain_values :
    chain 0 = (1, 1) ∧ chain 1 = (5, 3) ∧ chain 2 = (19, 11) ∧ chain 3 = (71, 41) ∧
    chain 4 = (265, 153) ∧ chain 5 = (989, 571) ∧ chain 6 = (3691, 2131) ∧
    chain 7 = (13775, 7953) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [chain, up]


/-! ## Part 2. The paper's binomial, `Q_n(s)`, the reflection form (V), and Step 3 -/

section Binomial

variable {K : Type*} [Field K]

/-- The paper's binomial coefficient `binom(z, j) = z (z - 1) ⋯ (z - j + 1) / j!`. -/
def gbinom (z : K) (j : ℕ) : K := (∏ i ∈ Finset.range j, (z - i)) / (j.factorial : K)

/-- The paper's `Q_n(s) = ∑_{m=0}^{min(2,n)} c_m binom(s + n - m - 1, n - m)`, weights `c`. -/
def Q (c : ℕ → K) (n : ℕ) (s : K) : K :=
  ∑ m ∈ Finset.range (min 2 n + 1), c m * gbinom (s + n - m - 1) (n - m)

/-- The weights `(1, k, 1)`; at `k = 4` they are the paper's `(1, 4, 1)`. -/
def w1k1 (k : K) : ℕ → K := fun m => if m = 1 then k else 1

theorem gbinom_eq_descPochhammer (z : K) (j : ℕ) :
    gbinom z j = (descPochhammer K j).eval z / (j.factorial : K) := by
  rw [gbinom, descPochhammer_eval_eq_prod_range]

variable [CharZero K]

/-- At a natural number `N`, the paper's binomial is the ordinary one (zero when `j > N`). -/
theorem gbinom_natCast (N j : ℕ) : gbinom (N : K) j = (N.choose j : K) := by
  rw [gbinom_eq_descPochhammer, descPochhammer_eval_eq_descFactorial,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul,
    mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j))]

/-- The reflection `binom(-z, j) = (-1)^j binom(z + j - 1, j)`. -/
theorem gbinom_neg (z : K) (j : ℕ) : gbinom (-z) j = (-1) ^ j * gbinom (z + j - 1) j := by
  rw [gbinom_eq_descPochhammer, gbinom_eq_descPochhammer, descPochhammer_eval_eq_ascPochhammer,
    show -z - (j : K) + 1 = -(z + j - 1) by ring, ascPochhammer_eval_neg_eq_descPochhammer]
  ring

end Binomial

/-- `binom(l, j)` for an integer `j`, with the paper's convention that it is `0` for `j < 0`
(and, as for every binomial coefficient, for `j > l`). -/
def bZ (l : ℕ) (j : ℤ) : ℤ := if 0 ≤ j then ((l.choose j.toNat : ℕ) : ℤ) else 0

theorem bZ_of_neg {l : ℕ} {j : ℤ} (hj : j < 0) : bZ l j = 0 := by
  simp [bZ, not_le.mpr hj]

theorem bZ_of_gt {l : ℕ} {j : ℤ} (hj : (l : ℤ) < j) : bZ l j = 0 := by
  have h0 : 0 ≤ j := by omega
  simp only [bZ, h0, ↓reduceIte]
  rw [Nat.choose_eq_zero_of_lt (by omega)]
  simp

theorem bZ_natCast (l j : ℕ) : bZ l (j : ℤ) = (l.choose j : ℤ) := by
  simp [bZ]

/-- `B_a(l) = binom(l, a) - k binom(l, a+1) + binom(l, a+2)` (weights `(1, k, 1)`). -/
def Bk (k a : ℤ) (l : ℕ) : ℤ := bZ l a - k * bZ l (a + 1) + bZ l (a + 2)

section Reflection

variable {K : Type*} [Field K] [CharZero K]

/-- Step 1 of the proof of Proposition 4.4, one term at a time: at `s = -l`, `n = p + l`,
`m ≤ n`, the paper's binomial is `(-1)^(n-m) binom(l, a + m)` with `a = -p`. -/
theorem term_eq (p : ℤ) (l n m : ℕ) (hn : (n : ℤ) = p + l) (hm : m ≤ n) :
    gbinom (-(l : K) + n - m - 1) (n - m) = (-1) ^ (n - m) * ((bZ l (-p + m) : ℤ) : K) := by
  have hnK : (n : K) = (p : K) + l := by
    have := congrArg (Int.cast : ℤ → K) hn
    push_cast at this
    exact this
  by_cases hpm : 0 ≤ p - m - 1
  · -- the top is a natural number below the bottom: both sides vanish
    obtain ⟨N, hN⟩ : ∃ N : ℕ, (N : ℤ) = p - m - 1 := ⟨(p - m - 1).toNat, Int.toNat_of_nonneg hpm⟩
    have hNK : (N : K) = (p : K) - m - 1 := by
      have := congrArg (Int.cast : ℤ → K) hN
      push_cast at this
      exact this
    have htop : (-(l : K) + n - m - 1) = (N : K) := by
      rw [hNK, hnK]; ring
    rw [htop, gbinom_natCast, Nat.choose_eq_zero_of_lt (by omega), bZ_of_neg (by omega)]
    simp
  · -- the top is a negative integer: the reflection
    obtain ⟨R, hR⟩ : ∃ R : ℕ, (R : ℤ) = -p + m := ⟨(-p + m).toNat, Int.toNat_of_nonneg (by omega)⟩
    have hRK : (R : K) = -(p : K) + m := by
      have := congrArg (Int.cast : ℤ → K) hR
      push_cast at this
      exact this
    have htop : (-(l : K) + n - m - 1) = -((R + 1 : ℕ) : K) := by
      push_cast
      rw [hRK, hnK]; ring
    have hl : R + (n - m) = l := by omega
    have htop2 : ((R + 1 : ℕ) : K) + ((n - m : ℕ) : K) - 1 = ((l : ℕ) : K) := by
      rw [← hl]; push_cast; ring
    rw [htop, gbinom_neg, htop2, gbinom_natCast, ← hR, bZ_natCast,
      Nat.choose_symm_of_eq_add (show l = (n - m) + R by omega), Int.cast_natCast]

/-- (V), for any weights `c`: `Q_{p+l}(-l) = (-1)^n (c_0 binom(l,a) - c_1 binom(l,a+1)
+ c_2 binom(l,a+2))` with `a = -p`, `n = p + l`. -/
theorem Q_reflect (c : ℕ → K) (p : ℤ) (l n : ℕ) (hn : (n : ℤ) = p + l) :
    Q c n (-(l : K)) = (-1) ^ n * (c 0 * ((bZ l (-p) : ℤ) : K) - c 1 * ((bZ l (-p + 1) : ℤ) : K)
      + c 2 * ((bZ l (-p + 2) : ℤ) : K)) := by
  have hsum : Q c n (-(l : K)) =
      ∑ m ∈ Finset.range (min 2 n + 1), c m * ((-1) ^ (n - m) * ((bZ l (-p + m) : ℤ) : K)) := by
    unfold Q
    refine Finset.sum_congr rfl (fun m hm => ?_)
    rw [term_eq p l n m hn (by rw [Finset.mem_range] at hm; omega)]
  rw [hsum]
  rcases (show n = 0 ∨ n = 1 ∨ 2 ≤ n by omega) with h0 | h1 | h2
  · subst h0
    have e1 : bZ l (-p + 1) = 0 := bZ_of_gt (by omega)
    have e2 : bZ l (-p + 2) = 0 := bZ_of_gt (by omega)
    rw [show min 2 0 + 1 = 1 by rfl, Finset.sum_range_one, e1, e2,
      show -p + ((0 : ℕ) : ℤ) = -p by simp, show 0 - 0 = 0 by rfl]
    simp
  · subst h1
    have e2 : bZ l (-p + 2) = 0 := bZ_of_gt (by omega)
    rw [show min 2 1 + 1 = 2 by rfl, Finset.sum_range_succ, Finset.sum_range_one, e2,
      show -p + ((0 : ℕ) : ℤ) = -p by simp, show -p + ((1 : ℕ) : ℤ) = -p + 1 by simp,
      show 1 - 0 = 1 by rfl, show 1 - 1 = 0 by rfl]
    simp only [Int.cast_zero, mul_zero, add_zero, pow_one, pow_zero, one_mul]
    ring
  · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 2 := ⟨n - 2, by omega⟩
    rw [show min 2 (n' + 2) + 1 = 3 by omega, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_one]
    rw [show n' + 2 - 0 = n' + 2 by omega, show n' + 2 - 1 = n' + 1 by omega,
      show n' + 2 - 2 = n' by omega, show -p + ((0 : ℕ) : ℤ) = -p by simp,
      show -p + ((1 : ℕ) : ℤ) = -p + 1 by simp, show -p + ((2 : ℕ) : ℤ) = -p + 2 by simp]
    ring

/-- The weights `(1, k, 1)`: `Q_{p+l}(-l) = (-1)^n B_a(l)`, `a = -p`. -/
theorem Q_w1k1 (k : ℤ) (p : ℤ) (l n : ℕ) (hn : (n : ℤ) = p + l) :
    Q (w1k1 (k : K)) n (-(l : K)) = (-1) ^ n * ((Bk k (-p) l : ℤ) : K) := by
  rw [Q_reflect _ p l n hn]
  have h0 : w1k1 (k : K) 0 = 1 := by simp [w1k1]
  have h1 : w1k1 (k : K) 1 = k := by simp [w1k1]
  have h2 : w1k1 (k : K) 2 = 1 := by simp [w1k1]
  rw [h0, h1, h2, Bk]
  push_cast
  ring

theorem Q_w1k1_eq_zero_iff (k : ℤ) (p : ℤ) (l n : ℕ) (hn : (n : ℤ) = p + l) :
    Q (w1k1 (k : K)) n (-(l : K)) = 0 ↔ Bk k (-p) l = 0 := by
  rw [Q_w1k1 k p l n hn, mul_eq_zero, Int.cast_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd h (pow_ne_zero _ (by norm_num))
    · exact h
  · intro h; exact Or.inr h

end Reflection

/-- Step 3 of the proof of Proposition 4.4, as an identity in the integers, for the weights
`(1, k, 1)`: with `x = l - a`, `(a+1)(a+2) B_a(l) = binom(l,a) [(a+1)(a+2) - k(a+2)x + x(x-1)]`. -/
theorem step3_identity (k : ℤ) (A l : ℕ) (hAl : A ≤ l) :
    ((A : ℤ) + 1) * ((A : ℤ) + 2) * Bk k A l =
      (l.choose A : ℤ) * (((A : ℤ) + 1) * ((A : ℤ) + 2) - k * ((A : ℤ) + 2) * ((l : ℤ) - A)
        + ((l : ℤ) - A) * ((l : ℤ) - A - 1)) := by
  have e0 : bZ l (A : ℤ) = (l.choose A : ℤ) := bZ_natCast l A
  have e1 : bZ l ((A : ℤ) + 1) = (l.choose (A + 1) : ℤ) := by
    rw [show ((A : ℤ) + 1) = ((A + 1 : ℕ) : ℤ) by push_cast; ring, bZ_natCast]
  have e2 : bZ l ((A : ℤ) + 2) = (l.choose (A + 2) : ℤ) := by
    rw [show ((A : ℤ) + 2) = ((A + 2 : ℕ) : ℤ) by push_cast; ring, bZ_natCast]
  have h1 : (l.choose (A + 1) : ℤ) * ((A : ℤ) + 1) = (l.choose A : ℤ) * ((l : ℤ) - A) := by
    have := Nat.choose_succ_right_eq l A
    have h' : ((l.choose (A + 1) * (A + 1) : ℕ) : ℤ) = ((l.choose A * (l - A) : ℕ) : ℤ) := by
      rw [this]
    push_cast [Nat.cast_sub hAl] at h'
    linarith
  have h2 : (l.choose (A + 2) : ℤ) * ((A : ℤ) + 2) =
      (l.choose (A + 1) : ℤ) * ((l : ℤ) - A - 1) := by
    rcases Nat.lt_or_ge A l with hlt | hge
    · have := Nat.choose_succ_right_eq l (A + 1)
      have h' : ((l.choose (A + 1 + 1) * (A + 1 + 1) : ℕ) : ℤ) =
          ((l.choose (A + 1) * (l - (A + 1)) : ℕ) : ℤ) := by rw [this]
      push_cast [Nat.cast_sub (show A + 1 ≤ l by omega)] at h'
      linarith
    · have hAl' : A = l := le_antisymm hAl hge
      subst hAl'
      rw [Nat.choose_eq_zero_of_lt (by omega : A < A + 2),
        Nat.choose_eq_zero_of_lt (by omega : A < A + 1)]
      simp
  rw [Bk, e0, e1, e2]
  linear_combination (((l : ℤ) - A) - 1 - k * ((A : ℤ) + 2)) * h1 + ((A : ℤ) + 1) * h2

/-- At `p = 1` (`a = -1`): `B_{-1}(l) = l - k`. -/
theorem Bk_neg_one (k : ℤ) (l : ℕ) : Bk k (-1) l = (l : ℤ) - k := by
  have e0 : bZ l (-1) = 0 := bZ_of_neg (by norm_num)
  have e1 : bZ l ((-1) + 1) = 1 := by
    rw [show ((-1 : ℤ) + 1) = ((0 : ℕ) : ℤ) by norm_num, bZ_natCast]; simp
  have e2 : bZ l ((-1) + 2) = l := by
    rw [show ((-1 : ℤ) + 2) = ((1 : ℕ) : ℤ) by norm_num, bZ_natCast]; simp
  rw [Bk, e0, e1, e2]; ring

/-- At `p = 2` (`a = -2`): `B_{-2}(l) = 1`. -/
theorem Bk_neg_two (k : ℤ) (l : ℕ) : Bk k (-2) l = 1 := by
  have e0 : bZ l (-2) = 0 := bZ_of_neg (by norm_num)
  have e1 : bZ l ((-2) + 1) = 0 := bZ_of_neg (by norm_num)
  have e2 : bZ l ((-2) + 2) = 1 := by
    rw [show ((-2 : ℤ) + 2) = ((0 : ℕ) : ℤ) by norm_num, bZ_natCast]; simp
  rw [Bk, e0, e1, e2]; ring

/-- At `a ≤ -3` (that is `p ≥ 3`): `B_a(l) = 0`. -/
theorem Bk_of_le (k a : ℤ) (l : ℕ) (ha : a ≤ -3) : Bk k a l = 0 := by
  rw [Bk, bZ_of_neg (by omega), bZ_of_neg (by omega), bZ_of_neg (by omega)]; ring

/-- Proposition W (c), in the paper's coordinates `t = 2 - p`, `x = l + p`: for `p ≤ 1` and
`l ≥ max(0, -p)`, `B_{-p}(l) = 0` exactly when `t^2 - k t x + x^2 = t + x`. -/
theorem Bk_eq_zero_iff_Ek (k p : ℤ) (l : ℕ) (hp : p ≤ 1) (hl : -p ≤ (l : ℤ)) :
    Bk k (-p) l = 0 ↔
      (2 - p) ^ 2 - k * (2 - p) * ((l : ℤ) + p) + ((l : ℤ) + p) ^ 2 = (2 - p) + ((l : ℤ) + p) := by
  rcases (show p = 1 ∨ p ≤ 0 by omega) with rfl | hp0
  · rw [Bk_neg_one]
    constructor
    · intro h
      have : (l : ℤ) = k := by linarith
      rw [this]; ring
    · intro h
      have h' : ((l : ℤ) + 1) * ((l : ℤ) - k) = 0 := by linear_combination h
      rcases mul_eq_zero.mp h' with h'' | h''
      · omega
      · exact h''
  · obtain ⟨A, hA⟩ : ∃ A : ℕ, (A : ℤ) = -p := ⟨(-p).toNat, Int.toNat_of_nonneg (by omega)⟩
    have hAl : A ≤ l := by omega
    have hid := step3_identity k A l hAl
    rw [← hA]
    have hpos : (0 : ℤ) < ((A : ℤ) + 1) * ((A : ℤ) + 2) := by positivity
    have hC : (0 : ℤ) < (l.choose A : ℤ) := by exact_mod_cast Nat.choose_pos hAl
    have hp' : p = -(A : ℤ) := by omega
    subst hp'
    constructor
    · intro h
      rw [h, mul_zero] at hid
      have := (mul_eq_zero.mp hid.symm).resolve_left hC.ne'
      linear_combination this
    · intro h
      have hb : ((A : ℤ) + 1) * ((A : ℤ) + 2) - k * ((A : ℤ) + 2) * ((l : ℤ) - A)
          + ((l : ℤ) - A) * ((l : ℤ) - A - 1) = 0 := by linear_combination h
      rw [hb, mul_zero] at hid
      exact (mul_eq_zero.mp hid).resolve_left hpos.ne'


/-! ## Part 3. Proposition 4.4 at the weights `(1, 4, 1)` -/

section Prop44

variable (K : Type*) [Field K] [CharZero K]

/-- `Q_{p+l}(-l)` at the paper's weights `(1, 4, 1)`, for integers `p` and `l`, with
`n = p + l`. In Proposition 4.4 the ranges are `l ≥ max(0, -p)`, so `n ≥ 0`. -/
def Qpl (p l : ℤ) : K := Q (w1k1 (4 : K)) (p + l).toNat (-(l : K))

theorem Qpl_eq (p l : ℤ) (hl0 : 0 ≤ l) (hpl : -p ≤ l) :
    Qpl K p l = (-1) ^ (p + l).toNat * ((Bk 4 (-p) l.toNat : ℤ) : K) := by
  have hn : (((p + l).toNat : ℕ) : ℤ) = p + ((l.toNat : ℕ) : ℤ) := by omega
  have hlK : ((l : ℤ) : K) = ((l.toNat : ℕ) : K) := by
    have h := Int.toNat_of_nonneg hl0
    exact_mod_cast h.symm
  unfold Qpl
  rw [hlK, show (4 : K) = ((4 : ℤ) : K) by norm_num]
  exact Q_w1k1 4 p l.toNat (p + l).toNat hn

theorem Qpl_eq_zero_iff (p l : ℤ) (hl0 : 0 ≤ l) (hpl : -p ≤ l) :
    Qpl K p l = 0 ↔ Bk 4 (-p) l.toNat = 0 := by
  rw [Qpl_eq K p l hl0 hpl, mul_eq_zero, Int.cast_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd h (pow_ne_zero _ (by norm_num))
    · exact h
  · intro h
    exact Or.inr h

/-- The algebraic half of the sentence before Proposition 4.4: given the formula
`G_l = R_l Q_{p+l}(-l) / L` with `R_l = (-1)^l binom(l+2, 2)` and `L ≠ 0`, `G_l = 0` exactly when
`Q_{p+l}(-l) = 0`. (That `G_l` is the coefficient of `(s+l)^{-2}` in `H Φ` is analytic and is not
formalized here.) -/
theorem G_eq_zero_iff (L q : K) (hL : L ≠ 0) (l : ℕ) :
    (-1) ^ l * ((l + 2).choose 2 : K) * q / L = 0 ↔ q = 0 := by
  have hR : (-1) ^ l * ((l + 2).choose 2 : K) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num))
      (Nat.cast_ne_zero.mpr (Nat.choose_pos (by omega)).ne')
  rw [div_eq_zero_iff, mul_eq_zero]
  constructor
  · rintro ((h | h) | h)
    · exact absurd h hR
    · exact h
    · exact absurd h hL
  · intro h
    exact Or.inl (Or.inr h)

/-- Proposition 4.4 (a): at an integer `p ≥ 3`, `Q_n(-l) = 0`. -/
theorem prop44_a (p l : ℤ) (hp : 3 ≤ p) (hl : max 0 (-p) ≤ l) : Qpl K p l = 0 := by
  have hl0 : 0 ≤ l := le_trans (le_max_left _ _) hl
  have hpl : -p ≤ l := le_trans (le_max_right _ _) hl
  rw [Qpl_eq K p l hl0 hpl, Bk_of_le 4 (-p) l.toNat (by omega)]
  simp

/-- Proposition 4.4 (b): at `p = 2`, `Q_n(-l) = (-1)^l`, which is never `0`. -/
theorem prop44_b (l : ℤ) (hl : max 0 (-2) ≤ l) :
    Qpl K 2 l = (-1) ^ l.toNat ∧ Qpl K 2 l ≠ 0 := by
  have hl0 : 0 ≤ l := le_trans (le_max_left _ _) hl
  have h : Qpl K 2 l = (-1) ^ l.toNat := by
    rw [Qpl_eq K 2 l hl0 (by omega), Bk_neg_two, show (2 + l).toNat = l.toNat + 2 by omega,
      pow_add]
    simp
  exact ⟨h, by rw [h]; exact pow_ne_zero _ (by norm_num)⟩

/-- The paper's Step 3 polynomial `P_a(x) = x^2 - (4a + 9) x + (a+1)(a+2)` is the bracket of
Proposition W (c) at `k = 4`, `t = a + 2`. -/
theorem P_eq_E4 (a x : ℤ) :
    x ^ 2 - (4 * a + 9) * x + (a + 1) * (a + 2) =
      (a + 2) ^ 2 - 4 * (a + 2) * x + x ^ 2 - ((a + 2) + x) := by
  ring

/-- Step 3, the discriminant: `(4a+9)^2 - 4(a+1)(a+2) = 12a^2 + 60a + 73 = 3(2a+5)^2 - 2`. -/
theorem discriminant_eq (a : ℤ) :
    (4 * a + 9) ^ 2 - 4 * (a + 1) * (a + 2) = 12 * a ^ 2 + 60 * a + 73 ∧
      12 * a ^ 2 + 60 * a + 73 = 3 * (2 * a + 5) ^ 2 - 2 := by
  constructor <;> ring

/-- Step 3, completing the square: `4 P_a(x) = (2x - (4a+9))^2 - (3 b^2 - 2)` with `b = 2a + 5`. -/
theorem four_P_eq (a x : ℤ) :
    4 * (x ^ 2 - (4 * a + 9) * x + (a + 1) * (a + 2)) =
      (2 * x - (4 * a + 9)) ^ 2 - (3 * (2 * a + 5) ^ 2 - 2) := by
  ring

/-- Step 3, the case `p = 1`: `B_{-1}(l) = l - 4`, zero only at `l = 4`. -/
theorem prop44_p1 (l : ℕ) : Bk 4 (-1) l = 0 ↔ l = 4 := by
  rw [Bk_neg_one]
  omega

/-- The remark after Proposition 4.4: for weights `(1, c_1, 1)` the discriminant of the Step 3
quadratic `x^2 - (c_1 (a+2) + 1) x + (a+1)(a+2)` is
`(c_1^2 - 4)(a+2)^2 + (2 c_1 + 4)(a+2) + 1`, which is `3 (2a+5)^2 - 2` at `c_1 = 4`. -/
theorem remark_discriminant (c₁ a : ℤ) :
    (c₁ * (a + 2) + 1) ^ 2 - 4 * ((a + 1) * (a + 2)) =
        (c₁ ^ 2 - 4) * (a + 2) ^ 2 + (2 * c₁ + 4) * (a + 2) + 1 ∧
      (4 ^ 2 - 4) * (a + 2) ^ 2 + (2 * 4 + 4) * (a + 2) + 1 = 3 * (2 * a + 5) ^ 2 - 2 := by
  constructor <;> ring

/-- Proposition 4.4 (c): for `p ≤ 1`, `l ≥ max(0, -p)` and `b = 5 - 2p`, `Q_n(-l) = 0` if and
only if `3 b^2 - 2 = y^2` for an integer `y ≥ 0` with `l = (3b - 6 ± y)/2`. -/
theorem prop44_c (p l : ℤ) (hp : p ≤ 1) (hl : max 0 (-p) ≤ l) :
    Qpl K p l = 0 ↔ ∃ y : ℤ, 0 ≤ y ∧ 3 * (5 - 2 * p) ^ 2 - 2 = y ^ 2 ∧
      (2 * l = 3 * (5 - 2 * p) - 6 + y ∨ 2 * l = 3 * (5 - 2 * p) - 6 - y) := by
  have hl0 : 0 ≤ l := le_trans (le_max_left _ _) hl
  have hpl : -p ≤ l := le_trans (le_max_right _ _) hl
  rw [Qpl_eq_zero_iff K p l hl0 hpl, Bk_eq_zero_iff_Ek 4 p l.toNat hp (by omega),
    Int.toNat_of_nonneg hl0]
  constructor
  · intro h
    have hsq : (2 * l - 3 * (5 - 2 * p) + 6) ^ 2 = 3 * (5 - 2 * p) ^ 2 - 2 := by
      linear_combination 4 * h
    rcases le_total 0 (2 * l - 3 * (5 - 2 * p) + 6) with hs | hs
    · exact ⟨2 * l - 3 * (5 - 2 * p) + 6, hs, hsq.symm, Or.inl (by ring)⟩
    · refine ⟨-(2 * l - 3 * (5 - 2 * p) + 6), by linarith, ?_, Or.inr (by ring)⟩
      rw [neg_sq]
      exact hsq.symm
  · rintro ⟨y, hy, hy2, h | h⟩
    · have h4 : 4 * (((2 - p) ^ 2 - 4 * (2 - p) * (l + p) + (l + p) ^ 2) - ((2 - p) + (l + p)))
          = 0 := by
        linear_combination (2 * l - 3 * (5 - 2 * p) + 6 + y) * h - hy2
      linarith
    · have h4 : 4 * (((2 - p) ^ 2 - 4 * (2 - p) * (l + p) + (l + p) ^ 2) - ((2 - p) + (l + p)))
          = 0 := by
        linear_combination (2 * l - 3 * (5 - 2 * p) + 6 - y) * h - hy2
      linarith

/-- Proposition 4.4 (c) as a set, with its exception: the vanishing `l` in range are exactly the
numbers `(3b - 6 + y)/2` and `(3b - 6 - y)/2`, the lower sign only when that number is `≥ 0`;
every such number lies in the range `l ≥ max(0, -p)`. -/
theorem prop44_c_set (p : ℤ) (hp : p ≤ 1) :
    {l : ℤ | max 0 (-p) ≤ l ∧ Qpl K p l = 0} =
      {l : ℤ | ∃ y : ℤ, 0 ≤ y ∧ 3 * (5 - 2 * p) ^ 2 - 2 = y ^ 2 ∧
        (2 * l = 3 * (5 - 2 * p) - 6 + y ∨
          (2 * l = 3 * (5 - 2 * p) - 6 - y ∧ 0 ≤ 3 * (5 - 2 * p) - 6 - y))} := by
  ext l
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hl, hQ⟩
    obtain ⟨y, hy, hy2, h⟩ := (prop44_c K p l hp hl).mp hQ
    refine ⟨y, hy, hy2, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · have hl0 : 0 ≤ l := le_trans (le_max_left _ _) hl
      exact Or.inr ⟨h, by linarith⟩
  · rintro ⟨y, hy, hy2, h⟩
    have hrange : max 0 (-p) ≤ l := by
      rcases h with h | ⟨h, h'⟩
      · apply max_le <;> linarith
      · have h5 : 0 < y + (9 - 4 * p) := by linarith
        have hy9 : y ≤ 9 - 4 * p := by
          rcases le_or_gt y (9 - 4 * p) with h9 | h9
          · exact h9
          · exfalso
            have h6 : 0 < y - (9 - 4 * p) := by linarith
            nlinarith [mul_pos h6 h5,
              mul_nonneg (show (0 : ℤ) ≤ 1 - p by linarith) (show (0 : ℤ) ≤ 1 - p by linarith)]
        apply max_le <;> linarith
    refine ⟨hrange, (prop44_c K p l hp hrange).mpr ⟨y, hy, hy2, ?_⟩⟩
    rcases h with h | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inr h

/-- `p_k = (5 - b_k)/2`. -/
def pk (k : ℕ) : ℤ := (5 - (chain k).2) / 2

/-- `λ_k = (3 b_k + y_k)/2 - 3`. -/
def lam (k : ℕ) : ℤ := (3 * (chain k).2 + (chain k).1) / 2 - 3

theorem two_pk (k : ℕ) : 2 * pk k = 5 - (chain k).2 := by
  have h := (chain_odd k).2
  unfold pk
  omega

theorem two_lam (k : ℕ) : 2 * (lam k + 3) = 3 * (chain k).2 + (chain k).1 := by
  have h := chain_odd k
  unfold lam
  omega

theorem pk_le_one {k : ℕ} (hk : 1 ≤ k) : pk k ≤ 1 := by
  have h1 := two_pk k
  have h2 := chain_b_ge_three hk
  omega

theorem lam_ge_two {k : ℕ} (hk : 1 ≤ k) : 2 ≤ lam k := by
  have h1 := two_lam k
  have h2 := chain_b_ge_three hk
  have h3 := (chain_pos k).1
  omega

/-- The step back: `3 b_k + y_k = 3 b_{k+1} - y_{k+1}`. -/
theorem step_back (k : ℕ) :
    3 * (chain k).2 + (chain k).1 = 3 * (chain (k + 1)).2 - (chain (k + 1)).1 := by
  simp only [chain, up]
  ring

/-- The two roots at `p_{k+1}` are distinct: `λ_k < λ_{k+1}` (their difference is `y_{k+1} > 0`). -/
theorem lam_lt_succ (k : ℕ) : lam k < lam (k + 1) := by
  have h1 := two_lam k
  have h2 := two_lam (k + 1)
  have h3 := step_back k
  have h4 := (chain_pos (k + 1)).1
  omega

/-- Proposition 4.4 (d), first part: the integers `p ≤ 1` at which (c) gives zeros are exactly
the `p_k`, `k ≥ 1`. -/
theorem prop44_d_p (p : ℤ) (hp : p ≤ 1) :
    (∃ l : ℤ, max 0 (-p) ≤ l ∧ Qpl K p l = 0) ↔ ∃ k : ℕ, 1 ≤ k ∧ p = pk k := by
  constructor
  · rintro ⟨l, hl, hQ⟩
    obtain ⟨y, hy, hy2, -⟩ := (prop44_c K p l hp hl).mp hQ
    obtain ⟨k, hk⟩ := chain_complete (y := y) (b := 5 - 2 * p) (by linarith) hy (by omega)
    have hb : (chain k).2 = 5 - 2 * p := by rw [hk]
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · subst h0
        simp only [chain] at hb
        omega
      · exact h0
    refine ⟨k, hk1, ?_⟩
    have := two_pk k
    omega
  · rintro ⟨k, hk, rfl⟩
    have hb := two_pk k
    have hsol := chain_isSol k
    unfold IsSol at hsol
    have hl := two_lam k
    have hmem : lam k ∈ {l : ℤ | ∃ y : ℤ, 0 ≤ y ∧ 3 * (5 - 2 * pk k) ^ 2 - 2 = y ^ 2 ∧
        (2 * l = 3 * (5 - 2 * pk k) - 6 + y ∨
          (2 * l = 3 * (5 - 2 * pk k) - 6 - y ∧ 0 ≤ 3 * (5 - 2 * pk k) - 6 - y))} := by
      refine ⟨(chain k).1, (chain_pos k).1.le, ?_, Or.inl ?_⟩
      · rw [show 5 - 2 * pk k = (chain k).2 by linarith]
        linarith
      · rw [show 5 - 2 * pk k = (chain k).2 by linarith]
        linarith
    rw [← prop44_c_set K (pk k) (pk_le_one hk)] at hmem
    exact ⟨lam k, hmem.1, hmem.2⟩

/-- Proposition 4.4 (d), second part: at `p_k` the vanishing `l` (in the range
`l ≥ max(0, -p_k)`) are `λ_k`, and `λ_{k-1}` when it is `≥ 0`. -/
theorem prop44_d_l (k : ℕ) (hk : 1 ≤ k) :
    {l : ℤ | max 0 (-pk k) ≤ l ∧ Qpl K (pk k) l = 0} =
      {l : ℤ | l = lam k ∨ (l = lam (k - 1) ∧ 0 ≤ lam (k - 1))} := by
  rw [prop44_c_set K (pk k) (pk_le_one hk)]
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  ext l
  simp only [Set.mem_ofPred_eq, Nat.add_sub_cancel]
  have hb := two_pk (k' + 1)
  have hl := two_lam (k' + 1)
  have hl' := two_lam k'
  have hback := step_back k'
  have hsol := chain_isSol (k' + 1)
  unfold IsSol at hsol
  have hpos := chain_pos (k' + 1)
  rw [show 5 - 2 * pk (k' + 1) = (chain (k' + 1)).2 by linarith]
  constructor
  · rintro ⟨y, hy, hy2, h⟩
    have hyy : y = (chain (k' + 1)).1 := by nlinarith
    subst hyy
    rcases h with h | ⟨h, h'⟩
    · left
      linarith
    · right
      constructor <;> linarith
  · rintro (h | ⟨h, h'⟩)
    · exact ⟨(chain (k' + 1)).1, hpos.1.le, by linarith, Or.inl (by linarith)⟩
    · exact ⟨(chain (k' + 1)).1, hpos.1.le, by linarith, Or.inr ⟨by linarith, by linarith⟩⟩

/-- Proposition 4.4 (d) at `k = 1`: at `p_1 = 1` the only vanishing `l` is `λ_1 = 4`. -/
theorem prop44_d_l_one : {l : ℤ | max 0 (-pk 1) ≤ l ∧ Qpl K (pk 1) l = 0} = {4} := by
  rw [prop44_d_l K 1 le_rfl]
  have h0 : lam 0 = -1 := by norm_num [lam, chain]
  have h1 : lam 1 = 4 := by norm_num [lam, chain, up]
  ext l
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Nat.sub_self, h0, h1]
  constructor
  · rintro (h | ⟨-, h⟩)
    · exact h
    · norm_num at h
  · intro h
    exact Or.inl h

/-- Proposition 4.4 (d) at `k ≥ 2`: at `p_k` the vanishing `l` are exactly `λ_{k-1}` and `λ_k`. -/
theorem prop44_d_l_ge_two (k : ℕ) (hk : 2 ≤ k) :
    {l : ℤ | max 0 (-pk k) ≤ l ∧ Qpl K (pk k) l = 0} = {lam (k - 1), lam k} := by
  rw [prop44_d_l K k (by omega)]
  have h := lam_ge_two (k := k - 1) (by omega)
  ext l
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (h1 | ⟨h1, -⟩)
    · exact Or.inr h1
    · exact Or.inl h1
  · rintro (h1 | h1)
    · exact Or.inr ⟨h1, by omega⟩
    · exact Or.inl h1

/-- Each `λ_k` with `k ≥ 1` is a vanishing `l` at both `p_k` and `p_{k+1}`. -/
theorem lam_vanishes_twice (k : ℕ) (hk : 1 ≤ k) :
    (max 0 (-pk k) ≤ lam k ∧ Qpl K (pk k) (lam k) = 0) ∧
      (max 0 (-pk (k + 1)) ≤ lam k ∧ Qpl K (pk (k + 1)) (lam k) = 0) := by
  have h1 : lam k ∈ {l : ℤ | max 0 (-pk k) ≤ l ∧ Qpl K (pk k) l = 0} := by
    rw [prop44_d_l K k hk]
    exact Or.inl rfl
  have h2 : lam k ∈ {l : ℤ | max 0 (-pk (k + 1)) ≤ l ∧ Qpl K (pk (k + 1)) l = 0} := by
    rw [prop44_d_l K (k + 1) (by omega)]
    refine Or.inr ⟨by rw [Nat.add_sub_cancel], ?_⟩
    rw [Nat.add_sub_cancel]
    have := lam_ge_two hk
    omega
  exact ⟨h1, h2⟩

/-- The recurrence `p_{k+2} = 4 p_{k+1} - p_k - 5`. -/
theorem pk_rec (k : ℕ) : pk (k + 2) = 4 * pk (k + 1) - pk k - 5 := by
  have h1 := two_pk k
  have h2 := two_pk (k + 1)
  have h3 := two_pk (k + 2)
  have hr := (chain_rec k).2
  omega

/-- The recurrence `λ_{k+2} = 4 λ_{k+1} - λ_k + 6`. -/
theorem lam_rec (k : ℕ) : lam (k + 2) = 4 * lam (k + 1) - lam k + 6 := by
  have h1 := two_lam k
  have h2 := two_lam (k + 1)
  have h3 := two_lam (k + 2)
  have hr := chain_rec k
  omega

/-- The values listed in Proposition 4.4 (d). -/
theorem pk_values :
    pk 1 = 1 ∧ pk 2 = -3 ∧ pk 3 = -18 ∧ pk 4 = -74 ∧ pk 5 = -283 ∧ pk 6 = -1063 ∧
      pk 7 = -3974 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [pk, chain, up]

theorem lam_values :
    lam 0 = -1 ∧ lam 1 = 4 ∧ lam 2 = 23 ∧ lam 3 = 94 ∧ lam 4 = 359 ∧ lam 5 = 1348 ∧
      lam 6 = 5039 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [lam, chain, up]

theorem pk_mod (k : ℕ) : pk (k + 2) % 2 = (pk k + 1) % 2 := by
  have := pk_rec k
  omega

/-- The parity of `p_k` (`k ≥ 1`) runs odd, odd, even, even, repeating. -/
theorem pk_parity (k : ℕ) (hk : 1 ≤ k) : Odd (pk k) ↔ (k % 4 = 1 ∨ k % 4 = 2) := by
  rw [Int.odd_iff]
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases (show k = 1 ∨ k = 2 ∨ 3 ≤ k by omega) with h1 | h2 | h3
    · subst h1
      norm_num [pk, chain, up]
    · subst h2
      norm_num [pk, chain, up]
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
      have h := ih j (by omega) (by omega)
      have hm := pk_mod j
      omega

/-- The examples after Proposition 4.4: the terms `u^4 ln(1/u)` at `p = 1`, and `u^4 ln(1/u)`
and `u^23 ln(1/u)` at `p = -3`, are absent. -/
theorem prop44_examples : Qpl K 1 4 = 0 ∧ Qpl K (-3) 4 = 0 ∧ Qpl K (-3) 23 = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · exact (prop44_c K 1 4 (by norm_num) (by norm_num)).mpr
      ⟨5, by norm_num, by norm_num, Or.inl (by norm_num)⟩
  · exact (prop44_c K (-3) 4 (by norm_num) (by norm_num)).mpr
      ⟨19, by norm_num, by norm_num, Or.inr (by norm_num)⟩
  · exact (prop44_c K (-3) 23 (by norm_num) (by norm_num)).mpr
      ⟨19, by norm_num, by norm_num, Or.inl (by norm_num)⟩

/-- All of Proposition 4.4 at `p ≤ 2` in one statement: for `l ≥ max(0, -p)`, `Q_{p+l}(-l) = 0`
exactly at the pairs `(p_k, λ_{k-1})` and `(p_k, λ_k)`, `k ≥ 1`. -/
theorem vanishing_pairs (p l : ℤ) (hp : p ≤ 2) (hl : max 0 (-p) ≤ l) :
    Qpl K p l = 0 ↔ ∃ k : ℕ, 1 ≤ k ∧ p = pk k ∧ (l = lam (k - 1) ∨ l = lam k) := by
  rcases (show p = 2 ∨ p ≤ 1 by omega) with h2 | h1
  · subst h2
    constructor
    · intro h
      exact absurd h (prop44_b K l hl).2
    · rintro ⟨k, hk, hpk, -⟩
      have := pk_le_one hk
      omega
  · constructor
    · intro h
      obtain ⟨k, hk, hpk⟩ := (prop44_d_p K p h1).mp ⟨l, hl, h⟩
      subst hpk
      have hmem : l ∈ {l : ℤ | max 0 (-pk k) ≤ l ∧ Qpl K (pk k) l = 0} := ⟨hl, h⟩
      rw [prop44_d_l K k hk] at hmem
      rcases hmem with h' | ⟨h', -⟩
      · exact ⟨k, hk, rfl, Or.inr h'⟩
      · exact ⟨k, hk, rfl, Or.inl h'⟩
    · rintro ⟨k, hk, hpk, hlk⟩
      subst hpk
      have hl0 : 0 ≤ l := le_trans (le_max_left _ _) hl
      have hmem : l ∈ {l : ℤ | l = lam k ∨ (l = lam (k - 1) ∧ 0 ≤ lam (k - 1))} := by
        rcases hlk with h' | h'
        · exact Or.inr ⟨h', by rw [← h']; exact hl0⟩
        · exact Or.inl h'
      rw [← prop44_d_l K k hk] at hmem
      exact hmem.2

/-- The same, as a set of pairs (the form of Proposition W (e) at `k = 4`): the zeros with `p ≤ 1`
are exactly `(p_j, λ_j)` and `(p_{j+1}, λ_j)`, `j ≥ 1`. -/
theorem vanishing_pairs_set :
    {pl : ℤ × ℤ | pl.1 ≤ 1 ∧ max 0 (-pl.1) ≤ pl.2 ∧ Qpl K pl.1 pl.2 = 0} =
      {pl | ∃ j : ℕ, 1 ≤ j ∧ (pl = (pk j, lam j) ∨ pl = (pk (j + 1), lam j))} := by
  ext ⟨p, l⟩
  simp only [Set.mem_ofPred_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨hp, hl, hQ⟩
    obtain ⟨k, hk, hpk, hlk⟩ := (vanishing_pairs K p l (by omega) hl).mp hQ
    rcases hlk with h' | h'
    · -- `l = λ_{k-1}`: then `k ≥ 2`, since `λ_0 = -1 < 0`
      have hk2 : 2 ≤ k := by
        rcases (show k = 1 ∨ 2 ≤ k by omega) with h1 | h1
        · subst h1
          have h0 : lam 0 = -1 := by norm_num [lam, chain]
          have hl0 : 0 ≤ l := le_trans (le_max_left _ _) hl
          simp only [Nat.sub_self, h0] at h'
          omega
        · exact h1
      refine ⟨k - 1, by omega, Or.inr ⟨?_, h'⟩⟩
      rw [show k - 1 + 1 = k by omega]
      exact hpk
    · exact ⟨k, hk, Or.inl ⟨hpk, h'⟩⟩
  · rintro ⟨j, hj, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · obtain ⟨⟨h1, h2⟩, -⟩ := lam_vanishes_twice K j hj
      exact ⟨pk_le_one hj, h1, h2⟩
    · obtain ⟨-, ⟨h1, h2⟩⟩ := lam_vanishes_twice K j hj
      exact ⟨pk_le_one (by omega), h1, h2⟩

end Prop44

/-! ## Part 4. Proposition W: the weights `(1, k, 1)` -/

section PropW

/-- The equation `(E_k)`: `t^2 - k t x + x^2 = t + x`. -/
def Ek (k t x : ℤ) : Prop := t ^ 2 - k * t * x + x ^ 2 = t + x

/-- The swap `S : (t, x) ↦ (x, t)`. -/
def Sw (v : ℤ × ℤ) : ℤ × ℤ := (v.2, v.1)

/-- The swap `T : (t, x) ↦ (t, k t + 1 - x)`. -/
def Tw (k : ℤ) (v : ℤ × ℤ) : ℤ × ℤ := (v.1, k * v.1 + 1 - v.2)

theorem Sw_Sw (v : ℤ × ℤ) : Sw (Sw v) = v := rfl

theorem Tw_Tw (k : ℤ) (v : ℤ × ℤ) : Tw k (Tw k v) = v := by
  obtain ⟨t, x⟩ := v
  show (t, k * t + 1 - (k * t + 1 - x)) = (t, x)
  rw [show k * t + 1 - (k * t + 1 - x) = x by ring]

/-- `S` keeps `(E_k)`. -/
theorem Ek_Sw {k : ℤ} {v : ℤ × ℤ} (h : Ek k v.1 v.2) : Ek k (Sw v).1 (Sw v).2 := by
  obtain ⟨t, x⟩ := v
  simp only [Ek, Sw] at *
  linear_combination h

/-- `T` keeps `(E_k)`: the two roots in `x` at a fixed `t` add to `k t + 1`. -/
theorem Ek_Tw {k : ℤ} {v : ℤ × ℤ} (h : Ek k v.1 v.2) : Ek k (Tw k v).1 (Tw k v).2 := by
  obtain ⟨t, x⟩ := v
  simp only [Ek, Tw] at *
  linear_combination h

/-- `z_i` at a natural index: `z_0 = z_1 = 0`, `z_{i+2} = k z_{i+1} - z_i + 1`. -/
def zN (k : ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => 0
  | i + 2 => k * zN k (i + 1) - zN k i + 1

theorem zN_rec (k : ℤ) (i : ℕ) : zN k (i + 2) = k * zN k (i + 1) - zN k i + 1 := rfl

/-- The paper's `z_i` at every integer `i`; `z_rec` below shows it satisfies
`z_{i+1} = k z_i - z_{i-1} + 1` for all integers `i`, and `z_unique` that it is the only such
sequence with `z_0 = z_1 = 0`. -/
def z (k i : ℤ) : ℤ := if 0 ≤ i then zN k i.toNat else zN k (1 - i).toNat

theorem z_natCast (k : ℤ) (i : ℕ) : z k i = zN k i := by
  simp [z]

theorem z_zero (k : ℤ) : z k 0 = 0 := by
  simp [z, zN]

theorem z_one (k : ℤ) : z k 1 = 0 := by
  simp [z, zN]

/-- `z_{1-i} = z_i`. -/
theorem z_symm (k i : ℤ) : z k (1 - i) = z k i := by
  unfold z
  split_ifs
  · rcases (show i = 0 ∨ i = 1 by omega) with h | h <;> subst h <;> simp [zN]
  · rfl
  · congr 1
    omega
  · omega

/-- The recurrence `z_{i+1} = k z_i - z_{i-1} + 1`, at every integer `i`. -/
theorem z_rec (k i : ℤ) : z k (i + 1) = k * z k i - z k (i - 1) + 1 := by
  rcases (show 1 ≤ i ∨ i ≤ 0 by omega) with h | h
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, i = (j : ℤ) + 1 := ⟨(i - 1).toNat, by omega⟩
    rw [show (j : ℤ) + 1 + 1 = ((j + 2 : ℕ) : ℤ) by push_cast; ring,
      show (j : ℤ) + 1 = ((j + 1 : ℕ) : ℤ) by push_cast; ring,
      show ((j + 1 : ℕ) : ℤ) - 1 = ((j : ℕ) : ℤ) by push_cast; ring,
      z_natCast, z_natCast, z_natCast, zN_rec]
  · obtain ⟨j, hj⟩ : ∃ j : ℕ, (j : ℤ) = -i := ⟨(-i).toNat, by omega⟩
    have a1 : z k (i + 1) = zN k j := by
      rw [← z_symm k (i + 1), show 1 - (i + 1) = (j : ℤ) by omega, z_natCast]
    have a2 : z k i = zN k (j + 1) := by
      rw [← z_symm k i, show 1 - i = ((j + 1 : ℕ) : ℤ) by push_cast; omega, z_natCast]
    have a3 : z k (i - 1) = zN k (j + 2) := by
      rw [← z_symm k (i - 1), show 1 - (i - 1) = ((j + 2 : ℕ) : ℤ) by push_cast; omega,
        z_natCast]
    rw [a1, a2, a3, zN_rec]
    ring

/-- The sequence is determined by `z_0 = z_1 = 0` and the recurrence. -/
theorem z_unique (k : ℤ) (f : ℤ → ℤ) (h0 : f 0 = 0) (h1 : f 1 = 0)
    (hrec : ∀ i : ℤ, f (i + 1) = k * f i - f (i - 1) + 1) : ∀ i : ℤ, f i = z k i := by
  have up : ∀ n : ℕ, f n = z k n ∧ f (n + 1) = z k (n + 1) := by
    intro n
    induction n with
    | zero => simp [h0, h1, z_zero, z_one]
    | succ n ih =>
      refine ⟨by exact_mod_cast ih.2, ?_⟩
      have e1 := hrec ((n : ℤ) + 1)
      have e2 := z_rec k ((n : ℤ) + 1)
      rw [show (n : ℤ) + 1 - 1 = n by ring] at e1 e2
      push_cast
      rw [e1, e2, ih.1, ih.2]
  have down : ∀ n : ℕ, f (-(n : ℤ)) = z k (-(n : ℤ)) ∧ f (-(n : ℤ) + 1) = z k (-(n : ℤ) + 1) := by
    intro n
    induction n with
    | zero => simp [h0, h1, z_zero, z_one]
    | succ n ih =>
      have e1 := hrec (-(n : ℤ))
      have e2 := z_rec k (-(n : ℤ))
      rw [ih.1, ih.2] at e1
      push_cast
      refine ⟨?_, by rw [show -((n : ℤ) + 1) + 1 = -(n : ℤ) by ring]; exact ih.1⟩
      rw [show -((n : ℤ) + 1) = -(n : ℤ) - 1 by ring]
      linarith [e1, e2]
  intro i
  rcases (show 0 ≤ i ∨ i < 0 by omega) with h | h
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = n := ⟨i.toNat, by omega⟩
    exact (up n).1
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, i = -(n : ℤ) := ⟨(-i).toNat, by omega⟩
    rw [hn]
    exact (down n).1

/-- The quantity whose vanishing is `(E_k)` at the pair `(z_i, z_{i+1})`. -/
def Fz (k i : ℤ) : ℤ :=
  z k i ^ 2 - k * z k i * z k (i + 1) + z k (i + 1) ^ 2 - z k i - z k (i + 1)

theorem Fz_succ (k i : ℤ) : Fz k (i + 1) = Fz k i := by
  unfold Fz
  have h := z_rec k (i + 1)
  rw [show i + 1 - 1 = i by ring] at h
  rw [h]
  ring

theorem Fz_eq_zero (k i : ℤ) : Fz k i = 0 := by
  induction i with
  | zero => simp [Fz, z_zero, z_one]
  | succ i ih => rw [Fz_succ, ih]
  | pred i ih => rw [← Fz_succ k (-(i : ℤ) - 1), show -(i : ℤ) - 1 + 1 = -(i : ℤ) by ring, ih]

/-- Every consecutive pair `(z_i, z_{i+1})`, `i ∈ ℤ`, solves `(E_k)`. -/
theorem Ek_z (k i : ℤ) : Ek k (z k i) (z k (i + 1)) := by
  have h := Fz_eq_zero k i
  unfold Fz at h
  unfold Ek
  linarith

/-- `T (z_i, z_{i+1}) = (z_{1-i}, z_{2-i})`. -/
theorem Tw_z (k i : ℤ) : Tw k (z k i, z k (i + 1)) = (z k (1 - i), z k (1 - i + 1)) := by
  simp only [Tw, Prod.mk.injEq]
  refine ⟨(z_symm k i).symm, ?_⟩
  have h := z_rec k i
  rw [show 1 - i + 1 = 1 - (i - 1) by ring, z_symm]
  linarith

/-- `S (z_i, z_{i+1}) = (z_{-i}, z_{1-i})`. -/
theorem Sw_z (k i : ℤ) : Sw (z k i, z k (i + 1)) = (z k (-i), z k (-i + 1)) := by
  simp only [Sw, Prod.mk.injEq]
  constructor
  · rw [show -i = 1 - (i + 1) by ring, z_symm]
  · rw [show -i + 1 = 1 - i by ring, z_symm]

/-- `T S` sends `(z_i, z_{i+1})` to `(z_{i+1}, z_{i+2})`. -/
theorem TwSw_z (k i : ℤ) : Tw k (Sw (z k i, z k (i + 1))) = (z k (i + 1), z k (i + 1 + 1)) := by
  rw [Sw_z, Tw_z, show 1 - -i = i + 1 by ring]

/-- `v` is a consecutive pair `(z_i, z_{i+1})` for some integer `i`. -/
def IsZPair (k : ℤ) (v : ℤ × ℤ) : Prop := ∃ i : ℤ, v = (z k i, z k (i + 1))

theorem IsZPair_Sw {k : ℤ} {v : ℤ × ℤ} (h : IsZPair k v) : IsZPair k (Sw v) := by
  obtain ⟨i, rfl⟩ := h
  exact ⟨-i, Sw_z k i⟩

theorem IsZPair_Tw {k : ℤ} {v : ℤ × ℤ} (h : IsZPair k v) : IsZPair k (Tw k v) := by
  obtain ⟨i, rfl⟩ := h
  exact ⟨1 - i, Tw_z k i⟩

/-- One step of the descent of Proposition W (d): `S T S` when `x ≤ t`, else `T`. -/
def descW (k : ℤ) (v : ℤ × ℤ) : ℤ × ℤ := if v.2 ≤ v.1 then Sw (Tw k (Sw v)) else Tw k v

theorem descW_cases (k : ℤ) (v : ℤ × ℤ) :
    descW k v = Sw (Tw k (Sw v)) ∨ descW k v = Tw k v := by
  unfold descW
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The descent step on a solution in nonnegative integers other than `(0, 0)` gives a solution
in nonnegative integers with a strictly smaller `t + x`. -/
theorem descW_spec {k : ℤ} {v : ℤ × ℤ} (h : Ek k v.1 v.2) (ht : 0 ≤ v.1) (hx : 0 ≤ v.2)
    (hne : v ≠ (0, 0)) :
    Ek k (descW k v).1 (descW k v).2 ∧ 0 ≤ (descW k v).1 ∧ 0 ≤ (descW k v).2 ∧
      (descW k v).1 + (descW k v).2 < v.1 + v.2 := by
  obtain ⟨t, x⟩ := v
  have hne' : ¬ (t = 0 ∧ x = 0) := by
    rintro ⟨rfl, rfl⟩
    exact hne rfl
  simp only [Ek] at h
  simp only [Ek, descW, Sw, Tw] at ht hx ⊢
  split_ifs with hxt
  · -- `x ≤ t`: the other root in `t` at this `x`, `t' = k x + 1 - t`, with `t t' = x^2 - x`
    have htpos : 0 < t := by omega
    have hprod : t * (k * x + 1 - t) = x ^ 2 - x := by linear_combination -h
    refine ⟨by linear_combination h, ?_, hx, ?_⟩
    · rcases (show x = 0 ∨ 1 ≤ x by omega) with hx0 | hx1
      · subst hx0
        have h2 : t * (k * 0 + 1 - t) = 0 := by rw [hprod]; ring
        rcases mul_eq_zero.mp h2 with h3 | h3
        · omega
        · omega
      · have hx2 : 0 ≤ x ^ 2 - x := by nlinarith
        by_contra hneg
        have hneg' : 0 < -(k * x + 1 - t) := by linarith
        nlinarith [mul_pos htpos hneg']
    · rcases (show x = 0 ∨ 1 ≤ x by omega) with hx0 | hx1
      · subst hx0
        have h2 : t * (k * 0 + 1 - t) = 0 := by rw [hprod]; ring
        rcases mul_eq_zero.mp h2 with h3 | h3
        · omega
        · omega
      · have hle : k * x + 1 - t ≤ x - 1 := by
          by_contra hgt
          have hgt' : 0 < (k * x + 1 - t) - (x - 1) := by linarith
          nlinarith [mul_pos htpos hgt', mul_nonneg (show (0 : ℤ) ≤ t - x by linarith) hx]
        linarith
  · -- `x > t`: the other root in `x` at this `t`, `x' = k t + 1 - x`, with `x x' = t^2 - t`
    have hxpos : 0 < x := by omega
    have hprod : x * (k * t + 1 - x) = t ^ 2 - t := by linear_combination -h
    refine ⟨by linear_combination h, ht, ?_, ?_⟩
    · rcases (show t = 0 ∨ 1 ≤ t by omega) with ht0 | ht1
      · subst ht0
        have h2 : x * (k * 0 + 1 - x) = 0 := by rw [hprod]; ring
        rcases mul_eq_zero.mp h2 with h3 | h3
        · omega
        · omega
      · have ht2 : 0 ≤ t ^ 2 - t := by nlinarith
        by_contra hneg
        have hneg' : 0 < -(k * t + 1 - x) := by linarith
        nlinarith [mul_pos hxpos hneg']
    · rcases (show t = 0 ∨ 1 ≤ t by omega) with ht0 | ht1
      · subst ht0
        have h2 : x * (k * 0 + 1 - x) = 0 := by rw [hprod]; ring
        rcases mul_eq_zero.mp h2 with h3 | h3
        · omega
        · omega
      · have hle : k * t + 1 - x ≤ t - 1 := by
          by_contra hgt
          have hgt' : 0 < (k * t + 1 - x) - (t - 1) := by linarith
          nlinarith [mul_pos hxpos hgt', mul_nonneg (show (0 : ℤ) ≤ x - t by linarith) ht]
        linarith

theorem IsZPair_of_descW {k : ℤ} {v : ℤ × ℤ} (h : IsZPair k (descW k v)) : IsZPair k v := by
  unfold descW at h
  split_ifs at h
  · have e : v = Sw (Tw k (Sw (Sw (Tw k (Sw v))))) := by rw [Sw_Sw, Tw_Tw, Sw_Sw]
    rw [e]
    exact IsZPair_Sw (IsZPair_Tw (IsZPair_Sw h))
  · rw [← Tw_Tw k v]
    exact IsZPair_Tw h

theorem Ek_imp_IsZPair (k : ℤ) (N : ℕ) : ∀ v : ℤ × ℤ, 0 ≤ v.1 → 0 ≤ v.2 → v.1 + v.2 ≤ N →
    Ek k v.1 v.2 → IsZPair k v := by
  induction N with
  | zero =>
    intro v ht hx hN h
    have hv : v = (0, 0) := Prod.ext (by simp; omega) (by simp; omega)
    exact ⟨0, by rw [hv, z_zero, show (0 : ℤ) + 1 = 1 by ring, z_one]⟩
  | succ N ih =>
    intro v ht hx hN h
    by_cases h00 : v = (0, 0)
    · exact ⟨0, by rw [h00, z_zero, show (0 : ℤ) + 1 = 1 by ring, z_one]⟩
    · obtain ⟨h1, h2, h3, h4⟩ := descW_spec h ht hx h00
      exact IsZPair_of_descW (ih _ h2 h3 (by push_cast at hN; omega) h1)

/-- Proposition W (d): for every integer `k`, the solutions of `(E_k)` in nonnegative integers
are exactly the nonnegative pairs among `(z_i, z_{i+1})`, `i ∈ ℤ`. -/
theorem propW_d (k t x : ℤ) (ht : 0 ≤ t) (hx : 0 ≤ x) :
    Ek k t x ↔ ∃ i : ℤ, t = z k i ∧ x = z k (i + 1) := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := Ek_imp_IsZPair k (t + x).toNat (t, x) ht hx (by simp only; omega) h
    exact ⟨i, (Prod.mk.inj hi).1, (Prod.mk.inj hi).2⟩
  · rintro ⟨i, rfl, rfl⟩
    exact Ek_z k i

/-- Proposition W (d), the descent: each solution in nonnegative integers is carried to `(0, 0)`
by finitely many steps `descW`, each a `T` or an `S T S` (`descW_cases`) that lowers `t + x`
(`descW_spec`). -/
theorem propW_d_descent (k : ℤ) (N : ℕ) : ∀ v : ℤ × ℤ, 0 ≤ v.1 → 0 ≤ v.2 → v.1 + v.2 ≤ N →
    Ek k v.1 v.2 → ∃ n : ℕ, (descW k)^[n] v = (0, 0) := by
  induction N with
  | zero =>
    intro v ht hx hN h
    exact ⟨0, Prod.ext (by simp; omega) (by simp; omega)⟩
  | succ N ih =>
    intro v ht hx hN h
    by_cases h00 : v = (0, 0)
    · exact ⟨0, h00⟩
    · obtain ⟨h1, h2, h3, h4⟩ := descW_spec h ht hx h00
      obtain ⟨n, hn⟩ := ih _ h2 h3 (by push_cast at hN; omega) h1
      exact ⟨n + 1, by rw [Function.iterate_succ_apply, hn]⟩

variable (K : Type*) [Field K] [CharZero K]

/-- `Q_{p+l}(-l)` at the weights `(1, k, 1)`. -/
def Qk (k p l : ℤ) : K := Q (w1k1 (k : K)) (p + l).toNat (-(l : K))

theorem Qk_eq (k p l : ℤ) (hl0 : 0 ≤ l) (hpl : -p ≤ l) :
    Qk K k p l = (-1) ^ (p + l).toNat * ((Bk k (-p) l.toNat : ℤ) : K) := by
  have hn : (((p + l).toNat : ℕ) : ℤ) = p + ((l.toNat : ℕ) : ℤ) := by omega
  have hlK : ((l : ℤ) : K) = ((l.toNat : ℕ) : K) := by
    have h := Int.toNat_of_nonneg hl0
    exact_mod_cast h.symm
  unfold Qk
  rw [hlK]
  exact Q_w1k1 k p l.toNat (p + l).toNat hn

omit [CharZero K] in
theorem Qpl_eq_Qk (p l : ℤ) : Qpl K p l = Qk K 4 p l := by
  unfold Qpl Qk
  norm_num

/-- Proposition W (a): at `p ≥ 3`, `Q_n(-l) = 0`. -/
theorem propW_a (k p l : ℤ) (hp : 3 ≤ p) (hl : max 0 (-p) ≤ l) : Qk K k p l = 0 := by
  have hl0 : 0 ≤ l := le_trans (le_max_left _ _) hl
  have hpl : -p ≤ l := le_trans (le_max_right _ _) hl
  rw [Qk_eq K k p l hl0 hpl, Bk_of_le k (-p) l.toNat (by omega)]
  simp

/-- Proposition W (b): at `p = 2`, `Q_n(-l) = (-1)^l ≠ 0`. -/
theorem propW_b (k l : ℤ) (hl : max 0 (-2) ≤ l) :
    Qk K k 2 l = (-1) ^ l.toNat ∧ Qk K k 2 l ≠ 0 := by
  have hl0 : 0 ≤ l := le_trans (le_max_left _ _) hl
  have h : Qk K k 2 l = (-1) ^ l.toNat := by
    rw [Qk_eq K k 2 l hl0 (by omega), Bk_neg_two, show (2 + l).toNat = l.toNat + 2 by omega,
      pow_add]
    simp
  exact ⟨h, by rw [h]; exact pow_ne_zero _ (by norm_num)⟩

/-- Proposition W (c): at `p ≤ 1`, `Q_n(-l) = 0` exactly when `(E_k)` holds at `t = 2 - p`,
`x = l + p`. -/
theorem propW_c (k p l : ℤ) (hp : p ≤ 1) (hl : max 0 (-p) ≤ l) :
    Qk K k p l = 0 ↔ Ek k (2 - p) (l + p) := by
  have hl0 : 0 ≤ l := le_trans (le_max_left _ _) hl
  have hpl : -p ≤ l := le_trans (le_max_right _ _) hl
  have key := Bk_eq_zero_iff_Ek k p l.toNat hp (by omega)
  rw [Int.toNat_of_nonneg hl0] at key
  rw [Qk_eq K k p l hl0 hpl, mul_eq_zero, Int.cast_eq_zero, Ek, ← key]
  constructor
  · rintro (h | h)
    · exact absurd h (pow_ne_zero _ (by norm_num))
    · exact h
  · intro h
    exact Or.inr h

/-- For `k ≥ 2`: `z_i ≥ 0` and `z_{i+1} - z_i ≥ i`. -/
theorem zN_grow (k : ℤ) (hk : 2 ≤ k) (i : ℕ) : 0 ≤ zN k i ∧ (i : ℤ) ≤ zN k (i + 1) - zN k i := by
  induction i with
  | zero => simp [zN]
  | succ i ih =>
    obtain ⟨h1, h2⟩ := ih
    have hz : 0 ≤ zN k (i + 1) := by linarith
    refine ⟨hz, ?_⟩
    have e : zN k (i + 1 + 1) = k * zN k (i + 1) - zN k i + 1 := zN_rec k i
    rw [e]
    push_cast
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ k - 2 by linarith) hz]

theorem zN_two (k : ℤ) : zN k 2 = 1 := by simp [zN]

theorem zN_three (k : ℤ) : zN k 3 = k + 1 := by simp [zN]

theorem zN_four (k : ℤ) : zN k 4 = k ^ 2 + k := by simp [zN]; ring

theorem zN_ge_one (k : ℤ) (hk : 2 ≤ k) {i : ℕ} (hi : 2 ≤ i) : 1 ≤ zN k i := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have := zN_grow k hk j
  have hj : (1 : ℤ) ≤ j := by exact_mod_cast (show 1 ≤ j by omega)
  linarith [this.1, this.2]

/-- The vanishing pairs at the weights `(1, k, 1)`: `p_j = 2 - z_{j+1}`. -/
def pW (k : ℤ) (j : ℕ) : ℤ := 2 - zN k (j + 1)

/-- `λ_j = z_{j+1} + z_{j+2} - 2`. -/
def lamW (k : ℤ) (j : ℕ) : ℤ := zN k (j + 1) + zN k (j + 2) - 2

/-- In range (`t ≥ 1`, `x ≥ 0`, `t + x ≥ 2`), a consecutive pair is `(z_m, z_{m+1})` or
`(z_{m+1}, z_m)` with `m ≥ 2` (this step holds for every `k`). -/
theorem zpair_in_range (k : ℤ) (i : ℤ) (h1 : 1 ≤ z k i) (h2 : 2 ≤ z k i + z k (i + 1)) :
    ∃ m : ℕ, 2 ≤ m ∧ ((z k i = zN k m ∧ z k (i + 1) = zN k (m + 1)) ∨
      (z k i = zN k (m + 1) ∧ z k (i + 1) = zN k m)) := by
  rcases (show 0 ≤ i ∨ i < 0 by omega) with hi | hi
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, i = m := ⟨i.toNat, by omega⟩
    rw [z_natCast] at h1
    have e : z k ((m : ℤ) + 1) = zN k (m + 1) := by
      rw [show (m : ℤ) + 1 = ((m + 1 : ℕ) : ℤ) by push_cast; ring, z_natCast]
    refine ⟨m, ?_, Or.inl ⟨z_natCast k m, e⟩⟩
    rcases (show m = 0 ∨ m = 1 ∨ 2 ≤ m by omega) with h | h | h
    · subst h; simp [zN] at h1
    · subst h; simp [zN] at h1
    · exact h
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = -i := ⟨(-i).toNat, by omega⟩
    have e1 : z k i = zN k (m + 1) := by
      rw [← z_symm k i, show 1 - i = ((m + 1 : ℕ) : ℤ) by push_cast; omega, z_natCast]
    have e2 : z k (i + 1) = zN k m := by
      rw [← z_symm k (i + 1), show 1 - (i + 1) = (m : ℤ) by omega, z_natCast]
    refine ⟨m, ?_, Or.inr ⟨e1, e2⟩⟩
    rw [e1, e2] at h2
    rcases (show m = 0 ∨ m = 1 ∨ 2 ≤ m by omega) with h | h | h
    · omega
    · subst h; simp [zN] at h2
    · exact h

/-- Proposition W (e), `k ≥ 2`: the pairs with `p ≤ 1` (and `l ≥ max(0, -p)`) at which
`Q_{p+l}(-l) = 0` are exactly `(p_j, λ_j)` and `(p_{j+1}, λ_j)`, `j ≥ 1`. -/
theorem propW_e (k : ℤ) (hk : 2 ≤ k) :
    {pl : ℤ × ℤ | pl.1 ≤ 1 ∧ max 0 (-pl.1) ≤ pl.2 ∧ Qk K k pl.1 pl.2 = 0} =
      {pl | ∃ j : ℕ, 1 ≤ j ∧ (pl = (pW k j, lamW k j) ∨ pl = (pW k (j + 1), lamW k j))} := by
  ext ⟨p, l⟩
  simp only [Set.mem_ofPred_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨hp, hl, hQ⟩
    have hl0 : 0 ≤ l := le_trans (le_max_left _ _) hl
    have hpl : -p ≤ l := le_trans (le_max_right _ _) hl
    rw [propW_c K k p l hp hl] at hQ
    obtain ⟨i, hi1, hi2⟩ := (propW_d k (2 - p) (l + p) (by omega) (by omega)).mp hQ
    obtain ⟨m, hm, hcase⟩ := zpair_in_range k i (by omega) (by omega)
    rcases hcase with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · refine ⟨m - 1, by omega, Or.inl ⟨?_, ?_⟩⟩
      · unfold pW; rw [show m - 1 + 1 = m by omega]; omega
      · unfold lamW; rw [show m - 1 + 1 = m by omega, show m - 1 + 2 = m + 1 by omega]; omega
    · refine ⟨m - 1, by omega, Or.inr ⟨?_, ?_⟩⟩
      · unfold pW; rw [show m - 1 + 1 + 1 = m + 1 by omega]; omega
      · unfold lamW; rw [show m - 1 + 1 = m by omega, show m - 1 + 2 = m + 1 by omega]; omega
  · rintro ⟨j, hj, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · have g1 := zN_ge_one k hk (show 2 ≤ j + 1 by omega)
      have g2 := zN_ge_one k hk (show 2 ≤ j + 2 by omega)
      have hp : pW k j ≤ 1 := by unfold pW; omega
      have hl : max 0 (-pW k j) ≤ lamW k j := by unfold pW lamW; apply max_le <;> omega
      refine ⟨hp, hl, (propW_c K k _ _ hp hl).mpr ?_⟩
      have h := Ek_z k ((j : ℤ) + 1)
      rw [show (j : ℤ) + 1 = ((j + 1 : ℕ) : ℤ) by push_cast; ring, z_natCast,
        show ((j + 1 : ℕ) : ℤ) + 1 = ((j + 2 : ℕ) : ℤ) by push_cast; ring, z_natCast] at h
      unfold pW lamW
      rw [show 2 - (2 - zN k (j + 1)) = zN k (j + 1) by ring,
        show zN k (j + 1) + zN k (j + 2) - 2 + (2 - zN k (j + 1)) = zN k (j + 2) by ring]
      exact h
    · have g1 := zN_ge_one k hk (show 2 ≤ j + 1 by omega)
      have g2 : 1 ≤ zN k (j + 2) := zN_ge_one k hk (show 2 ≤ j + 2 by omega)
      have hpW : pW k (j + 1) = 2 - zN k (j + 2) := rfl
      have hlW : lamW k j = zN k (j + 1) + zN k (j + 2) - 2 := rfl
      have hp : pW k (j + 1) ≤ 1 := by rw [hpW]; omega
      have hl : max 0 (-pW k (j + 1)) ≤ lamW k j := by
        rw [hpW, hlW]; apply max_le <;> omega
      refine ⟨hp, hl, (propW_c K k _ _ hp hl).mpr ?_⟩
      have h := Ek_z k ((j : ℤ) + 1)
      rw [show (j : ℤ) + 1 = ((j + 1 : ℕ) : ℤ) by push_cast; ring, z_natCast,
        show ((j + 1 : ℕ) : ℤ) + 1 = ((j + 2 : ℕ) : ℤ) by push_cast; ring, z_natCast] at h
      have h' := Ek_Sw (v := (zN k (j + 1), zN k (j + 2))) h
      simp only [Sw] at h'
      rw [hpW, hlW, show 2 - (2 - zN k (j + 2)) = zN k (j + 2) by ring,
        show zN k (j + 1) + zN k (j + 2) - 2 + (2 - zN k (j + 2)) = zN k (j + 1) by ring]
      exact h'

/-- `p_1 = 1`, `p_2 = 1 - k`, `λ_1 = k`, `λ_2 = (k+1)^2 - 2`. -/
theorem pW_lamW_values (k : ℤ) :
    pW k 1 = 1 ∧ pW k 2 = 1 - k ∧ lamW k 1 = k ∧ lamW k 2 = (k + 1) ^ 2 - 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [pW, zN]
  · simp [pW, zN]; ring
  · simp [lamW, zN]; ring
  · simp [lamW, zN]; ring

/-- `p_{j+2} = k p_{j+1} - p_j - (2k - 3)`. -/
theorem pW_rec (k : ℤ) (j : ℕ) : pW k (j + 2) = k * pW k (j + 1) - pW k j - (2 * k - 3) := by
  have e : zN k (j + 3) = k * zN k (j + 2) - zN k (j + 1) + 1 := zN_rec k (j + 1)
  show 2 - zN k (j + 3) = k * (2 - zN k (j + 2)) - (2 - zN k (j + 1)) - (2 * k - 3)
  rw [e]
  ring

/-- `λ_{j+2} = k λ_{j+1} - λ_j + 2(k - 1)`. -/
theorem lamW_rec (k : ℤ) (j : ℕ) :
    lamW k (j + 2) = k * lamW k (j + 1) - lamW k j + 2 * (k - 1) := by
  have e3 : zN k (j + 3) = k * zN k (j + 2) - zN k (j + 1) + 1 := zN_rec k (j + 1)
  have e4 : zN k (j + 4) = k * zN k (j + 3) - zN k (j + 2) + 1 := zN_rec k (j + 2)
  show zN k (j + 3) + zN k (j + 4) - 2 =
    k * (zN k (j + 2) + zN k (j + 3) - 2) - (zN k (j + 1) + zN k (j + 2) - 2) + 2 * (k - 1)
  rw [e4, e3]
  ring

/-- The swap `S` in the coordinates `(p, l)`: the other `p` at the same `l`, `p' = 2 - l - p`. -/
def Sp (pl : ℤ × ℤ) : ℤ × ℤ := (2 - pl.2 - pl.1, pl.2)

/-- The swap `T` in the coordinates `(p, l)`: the other `l` at the same `p`,
`l' = 2k + 1 - (k+2) p - l`. -/
def Tp (k : ℤ) (pl : ℤ × ℤ) : ℤ × ℤ := (pl.1, 2 * k + 1 - (k + 2) * pl.1 - pl.2)

/-- `Sp` and `Tp` are `S` and `T` read through `t = 2 - p`, `x = l + p`. -/
theorem Sp_Tp_coords (k p l : ℤ) :
    Sw (2 - p, l + p) = (2 - (Sp (p, l)).1, (Sp (p, l)).2 + (Sp (p, l)).1) ∧
      Tw k (2 - p, l + p) = (2 - (Tp k (p, l)).1, (Tp k (p, l)).2 + (Tp k (p, l)).1) := by
  refine ⟨Prod.ext ?_ ?_, Prod.ext ?_ ?_⟩ <;> simp only [Sw, Tw, Sp, Tp] <;> ring

theorem Sp_walk (k : ℤ) (j : ℕ) : Sp (pW k j, lamW k j) = (pW k (j + 1), lamW k j) := by
  simp only [Sp, pW, lamW, Prod.mk.injEq]
  constructor
  · rw [show j + 1 + 1 = j + 2 by rfl]; ring
  · trivial

theorem Tp_walk (k : ℤ) (j : ℕ) : Tp k (pW k (j + 1), lamW k j) = (pW k (j + 1), lamW k (j + 1)) := by
  have e : zN k (j + 3) = k * zN k (j + 2) - zN k (j + 1) + 1 := zN_rec k (j + 1)
  simp only [Tp, Prod.mk.injEq, true_and]
  show 2 * k + 1 - (k + 2) * (2 - zN k (j + 2)) - (zN k (j + 1) + zN k (j + 2) - 2) =
    zN k (j + 2) + zN k (j + 3) - 2
  rw [e]
  ring

/-- Every member is joined to `(1, k)` by `S` and `T` alternately, through members only:
`(T S)^j (1, k) = (p_{j+1}, λ_{j+1})`, and `S` sends `(p_j, λ_j)` to `(p_{j+1}, λ_j)`. -/
theorem walk_from_base (k : ℤ) (j : ℕ) :
    (fun pl => Tp k (Sp pl))^[j] (1, k) = (pW k (j + 1), lamW k (j + 1)) := by
  induction j with
  | zero =>
    obtain ⟨h1, -, h3, -⟩ := pW_lamW_values k
    simp [h1, h3]
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, Sp_walk, Tp_walk]

/-- Proposition W (e), `k = 1`: the vanishing pairs with `p ≤ 1` are `(1,1)`, `(0,1)`, `(0,2)`. -/
theorem propW_e_one :
    {pl : ℤ × ℤ | pl.1 ≤ 1 ∧ max 0 (-pl.1) ≤ pl.2 ∧ Qk K 1 pl.1 pl.2 = 0} =
      {(1, 1), (0, 1), (0, 2)} := by
  ext ⟨p, l⟩
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨hp, hl, hQ⟩
    have hl0 : 0 ≤ l := le_trans (le_max_left _ _) hl
    have hpl : -p ≤ l := le_trans (le_max_right _ _) hl
    rw [propW_c K 1 p l hp hl] at hQ
    unfold Ek at hQ
    obtain ⟨t, ht⟩ : ∃ t : ℤ, t = 2 - p := ⟨_, rfl⟩
    obtain ⟨x, hx⟩ : ∃ x : ℤ, x = l + p := ⟨_, rfl⟩
    rw [← ht, ← hx] at hQ
    have hb : t + x ≤ 4 := by
      nlinarith [sq_nonneg (t - x), sq_nonneg (t + x - 4)]
    have ht1 : 1 ≤ t := by omega
    have ht4 : t ≤ 4 := by omega
    have hx0 : 0 ≤ x := by omega
    have hx3 : x ≤ 3 := by omega
    interval_cases t <;> interval_cases x <;> norm_num at hQ <;> omega
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
      refine ⟨by norm_num, by norm_num, (propW_c K 1 _ _ (by norm_num) (by norm_num)).mpr ?_⟩ <;>
      norm_num [Ek]

/-- Proposition W (e), `k = 0`: the only vanishing pair with `p ≤ 1` is `(1, 0)`. -/
theorem propW_e_zero :
    {pl : ℤ × ℤ | pl.1 ≤ 1 ∧ max 0 (-pl.1) ≤ pl.2 ∧ Qk K 0 pl.1 pl.2 = 0} = {(1, 0)} := by
  ext ⟨p, l⟩
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨hp, hl, hQ⟩
    have hl0 : 0 ≤ l := le_trans (le_max_left _ _) hl
    have hpl : -p ≤ l := le_trans (le_max_right _ _) hl
    rw [propW_c K 0 p l hp hl] at hQ
    unfold Ek at hQ
    obtain ⟨t, ht⟩ : ∃ t : ℤ, t = 2 - p := ⟨_, rfl⟩
    obtain ⟨x, hx⟩ : ∃ x : ℤ, x = l + p := ⟨_, rfl⟩
    rw [← ht, ← hx] at hQ
    have hb : t + x ≤ 2 := by
      nlinarith [sq_nonneg (t - x), sq_nonneg (t + x - 2)]
    have ht1 : 1 ≤ t := by omega
    have ht2 : t ≤ 2 := by omega
    have hx0 : 0 ≤ x := by omega
    have hx1 : x ≤ 1 := by omega
    interval_cases t <;> interval_cases x <;> norm_num at hQ <;> omega
  · rintro ⟨rfl, rfl⟩
    exact ⟨by norm_num, by norm_num, (propW_c K 0 1 0 (by norm_num) (by norm_num)).mpr
      (by norm_num [Ek])⟩

/-- Proposition W (e), `k ≤ -1`: there are no vanishing pairs with `p ≤ 1`. -/
theorem propW_e_neg (k : ℤ) (hk : k ≤ -1) :
    {pl : ℤ × ℤ | pl.1 ≤ 1 ∧ max 0 (-pl.1) ≤ pl.2 ∧ Qk K k pl.1 pl.2 = 0} = ∅ := by
  ext ⟨p, l⟩
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro hp hl hQ
  have hl0 : 0 ≤ l := le_trans (le_max_left _ _) hl
  have hpl : -p ≤ l := le_trans (le_max_right _ _) hl
  rw [propW_c K k p l hp hl] at hQ
  unfold Ek at hQ
  have ht : 1 ≤ 2 - p := by omega
  have hx : 0 ≤ l + p := by omega
  rcases (show l + p = 0 ∨ 1 ≤ l + p by omega) with hx0 | hx1
  · rw [hx0] at hQ
    have : (2 - p) * ((2 - p) - 1) = 0 := by linear_combination hQ
    rcases mul_eq_zero.mp this with h | h <;> omega
  · nlinarith [mul_nonneg (show (0 : ℤ) ≤ 2 - p - 1 by omega) (show (0 : ℤ) ≤ 2 - p by omega),
      mul_nonneg (show (0 : ℤ) ≤ l + p - 1 by omega) hx,
      mul_nonneg (mul_nonneg (show (0 : ℤ) ≤ -k - 1 by omega) (show (0 : ℤ) ≤ 2 - p by omega)) hx,
      mul_pos (show (0 : ℤ) < 2 - p by omega) (show (0 : ℤ) < l + p by omega)]

/-! ### `k = 4`: the bridge to the Pell chain of Proposition 4.4 -/

/-- `b_j = 2 z_{j+1} + 1` at `k = 4` (Proposition B (iii), (iv): `X_i = (k-2) z_i + 1`). -/
theorem chain_b_eq_zN (j : ℕ) : (chain j).2 = 2 * zN 4 (j + 1) + 1 := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rcases (show j = 0 ∨ j = 1 ∨ 2 ≤ j by omega) with h | h | h
    · subst h; simp [chain, zN]
    · subst h; simp [chain, up, zN]
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 2 := ⟨j - 2, by omega⟩
      have h1 : (chain i).2 = 2 * zN 4 (i + 1) + 1 := ih i (by omega)
      have h2 : (chain (i + 1)).2 = 2 * zN 4 (i + 2) + 1 := ih (i + 1) (by omega)
      have hr := (chain_rec i).2
      have hz : zN 4 (i + 3) = 4 * zN 4 (i + 2) - zN 4 (i + 1) + 1 := zN_rec 4 (i + 1)
      show (chain (i + 2)).2 = 2 * zN 4 (i + 3) + 1
      rw [hr, hz, h1, h2]
      ring

/-- At `k = 4`, `p_j` of Proposition W is `p_j` of Proposition 4.4. -/
theorem pW_four (j : ℕ) : pW 4 j = pk j := by
  have h1 := two_pk j
  have h2 := chain_b_eq_zN j
  unfold pW
  omega

/-- At `k = 4`, `λ_j` of Proposition W is `λ_j` of Proposition 4.4. -/
theorem lamW_four (j : ℕ) : lamW 4 j = lam j := by
  have h1 := two_lam j
  have h2 := chain_b_eq_zN j
  have h3 : (chain (j + 1)).2 = 2 * zN 4 (j + 2) + 1 := chain_b_eq_zN (j + 1)
  have h4 : (chain (j + 1)).2 = (chain j).1 + 2 * (chain j).2 := by simp [chain, up]
  unfold lamW
  omega

/-- Proposition B (i): `(k-2)^2 (t^2 - k t x + x^2 - t - x) = U^2 - k U V + V^2 - (2 - k)` with
`U = (k-2) t + 1`, `V = (k-2) x + 1`. -/
theorem propB_i (k t x : ℤ) :
    (k - 2) ^ 2 * (t ^ 2 - k * t * x + x ^ 2 - t - x) =
      ((k - 2) * t + 1) ^ 2 - k * ((k - 2) * t + 1) * ((k - 2) * x + 1) +
        ((k - 2) * x + 1) ^ 2 - (2 - k) := by
  ring

/-- Proposition B (i), the norm: if `ω^2 = k ω - 1` and `ω' = k - ω`, then
`(U - V ω)(U - V ω') = U^2 - k U V + V^2`. -/
theorem propB_norm {R : Type*} [CommRing R] (k U V ω : R) (hω : ω ^ 2 = k * ω - 1) :
    (U - V * ω) * (U - V * (k - ω)) = U ^ 2 - k * U * V + V ^ 2 := by
  linear_combination (-V ^ 2) * hω

/-- Proposition B (iii): with `X_i = (k-2) z_i + 1`, the pair `(p_j, λ_j)` has
`(U, V) = (X_{j+1}, X_{j+2})`, the pair `(p_{j+1}, λ_j)` has `(U, V) = (X_{j+2}, X_{j+1})`,
and `X_0 = X_1 = 1`, `X_{i+2} = k X_{i+1} - X_i`. -/
theorem propB_iii (k : ℤ) (j i : ℕ) :
    ((k - 2) * (2 - pW k j) + 1 = (k - 2) * zN k (j + 1) + 1 ∧
      (k - 2) * (lamW k j + pW k j) + 1 = (k - 2) * zN k (j + 2) + 1) ∧
    ((k - 2) * (2 - pW k (j + 1)) + 1 = (k - 2) * zN k (j + 2) + 1 ∧
      (k - 2) * (lamW k j + pW k (j + 1)) + 1 = (k - 2) * zN k (j + 1) + 1) ∧
    (k - 2) * zN k 0 + 1 = 1 ∧ (k - 2) * zN k 1 + 1 = 1 ∧
    (k - 2) * zN k (i + 2) + 1 = k * ((k - 2) * zN k (i + 1) + 1) - ((k - 2) * zN k i + 1) := by
  have e : zN k (j + 1 + 1) = zN k (j + 2) := rfl
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, by simp [zN], by simp [zN], ?_⟩
  · simp only [pW]; ring
  · simp only [pW, lamW]; ring
  · simp only [pW, e]; ring
  · simp only [pW, lamW, e]; ring
  · rw [zN_rec]; ring

/-- Proposition B (ii): in `(U, V)`, `T` is `(U, V) ↦ (U, k U - V)`, and it and `S` keep the
form `U^2 - k U V + V^2`. -/
theorem propB_ii (k t x : ℤ) :
    (k - 2) * (k * t + 1 - x) + 1 = k * ((k - 2) * t + 1) - ((k - 2) * x + 1) ∧
      ∀ U V : ℤ, (V ^ 2 - k * V * U + U ^ 2 = U ^ 2 - k * U * V + V ^ 2 ∧
        U ^ 2 - k * U * (k * U - V) + (k * U - V) ^ 2 = U ^ 2 - k * U * V + V ^ 2) := by
  refine ⟨by ring, fun U V => ⟨by ring, by ring⟩⟩

/-- Proposition B (ii): `T S : (U, V) ↦ (V, k V - U)` multiplies `U - V ω` by the unit `ω`,
`(U - V ω) ω = V - (k V - U) ω`. -/
theorem propB_ii_unit {R : Type*} [CommRing R] (k U V ω : R) (hω : ω ^ 2 = k * ω - 1) :
    (U - V * ω) * ω = V - (k * V - U) * ω := by
  linear_combination (-V) * hω

/-- Proposition B (ii), on columns: `S` and `T` have determinant `-1` (reflections), and
`T S` has determinant `1` and trace `k`. -/
theorem propB_ii_matrices (k : ℤ) :
    (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ).det = -1 ∧
      (!![1, 0; k, -1] : Matrix (Fin 2) (Fin 2) ℤ).det = -1 ∧
      (!![0, 1; -1, k] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 ∧
      (!![0, 1; -1, k] : Matrix (Fin 2) (Fin 2) ℤ).trace = k := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [Matrix.det_fin_two_of]
  · simp [Matrix.det_fin_two_of]
  · simp [Matrix.det_fin_two_of]
  · simp [Matrix.trace_fin_two_of]

/-- Proposition B (iv): at `k = 4`, `U = 5 - 2p` is the `b` of Proposition 4.4, and
`U^2 - 4UV + V^2 = (V - 2U)^2 - 3U^2`; along the chain `y_j = b_{j+1} - 2 b_j` and
`y_{j+1} = 2 b_{j+1} - b_j`. -/
theorem propB_iv (p t U V : ℤ) (j : ℕ) (ht : t = 2 - p) :
    (4 - 2) * t + 1 = 5 - 2 * p ∧ U ^ 2 - 4 * U * V + V ^ 2 = (V - 2 * U) ^ 2 - 3 * U ^ 2 ∧
      (chain j).1 = (chain (j + 1)).2 - 2 * (chain j).2 ∧
      (chain (j + 1)).1 = 2 * (chain (j + 1)).2 - (chain j).2 := by
  refine ⟨by rw [ht]; ring, by ring, ?_, ?_⟩
  · simp only [chain, up]; ring
  · simp only [chain, up]; ring

/-- Proposition B (v): at `k = 1, 0, -1`, `T S` has order `6, 4, 3`. -/
theorem propB_v (v : ℤ × ℤ) :
    (fun w => Tw 1 (Sw w))^[6] v = v ∧ (fun w => Tw 0 (Sw w))^[4] v = v ∧
      (fun w => Tw (-1) (Sw w))^[3] v = v := by
  obtain ⟨t, x⟩ := v
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, Tw, Sw,
      Prod.mk.injEq] <;>
    constructor <;> ring

/-! ### `k = 2` and `k = 3` -/

/-- At `k = 2`, `z_i = i (i - 1) / 2` (triangular numbers), so `p_j = 2 - j(j+1)/2` and
`λ_j = (j+1)^2 - 2`. -/
theorem k_two (i j : ℕ) :
    2 * zN 2 i = (i : ℤ) * ((i : ℤ) - 1) ∧ 2 * pW 2 j = 4 - (j : ℤ) * ((j : ℤ) + 1) ∧
      lamW 2 j = ((j : ℤ) + 1) ^ 2 - 2 := by
  have hz : ∀ i : ℕ, 2 * zN 2 i = (i : ℤ) * ((i : ℤ) - 1) := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      rcases (show i = 0 ∨ i = 1 ∨ 2 ≤ i by omega) with h | h | h
      · subst h; simp [zN]
      · subst h; simp [zN]
      · obtain ⟨m, rfl⟩ : ∃ m, i = m + 2 := ⟨i - 2, by omega⟩
        have h1 := ih m (by omega)
        have h2 := ih (m + 1) (by omega)
        rw [zN_rec]
        push_cast at h1 h2 ⊢
        linarith
  refine ⟨hz i, ?_, ?_⟩
  · have := hz (j + 1)
    unfold pW
    push_cast at this
    linarith
  · have h1 := hz (j + 1)
    have h2 := hz (j + 2)
    unfold lamW
    push_cast at h1 h2
    linarith

/-- At `k = 2`, `z_i = i (i - 1) / 2` at every integer `i`. -/
theorem k_two_z (i : ℤ) : 2 * z 2 i = i * (i - 1) := by
  rcases (show 0 ≤ i ∨ i < 0 by omega) with h | h
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = n := ⟨i.toNat, by omega⟩
    rw [z_natCast]
    exact (k_two n 0).1
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = 1 - i := ⟨(1 - i).toNat, by omega⟩
    rw [← z_symm 2 i, ← hn, z_natCast, (k_two n 0).1, hn]
    ring

/-- The Lucas numbers, `Luc_0 = 2`, `Luc_1 = 1`, `Luc_{n+2} = Luc_n + Luc_{n+1}`. -/
def luc : ℕ → ℤ
  | 0 => 2
  | 1 => 1
  | n + 2 => luc n + luc (n + 1)

theorem luc_eq_fib (n : ℕ) : luc (n + 1) = (Nat.fib n : ℤ) + Nat.fib (n + 2) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases (show n = 0 ∨ n = 1 ∨ 2 ≤ n by omega) with h | h | h
    · subst h; simp [luc, Nat.fib_add_two]
    · subst h; simp [luc, Nat.fib_add_two]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
      have h1 := ih m (by omega)
      have h2 := ih (m + 1) (by omega)
      have e : luc (m + 2 + 1) = luc (m + 1) + luc (m + 1 + 1) := rfl
      rw [e, h1, h2]
      have f1 : Nat.fib (m + 2) = Nat.fib m + Nat.fib (m + 1) := Nat.fib_add_two
      have f2 : Nat.fib (m + 3) = Nat.fib (m + 1) + Nat.fib (m + 2) := Nat.fib_add_two
      have f3 : Nat.fib (m + 4) = Nat.fib (m + 2) + Nat.fib (m + 3) := Nat.fib_add_two
      show (Nat.fib m : ℤ) + Nat.fib (m + 2) + (Nat.fib (m + 1) + Nat.fib (m + 3)) =
        Nat.fib (m + 2) + Nat.fib (m + 4)
      push_cast [f1, f2, f3]
      ring

/-- At `k = 3`, `p_j = 3 - Fib_{2j+1}` and `λ_j = Luc_{2j+2} - 4`, `j ≥ 0`. -/
theorem k_three (j : ℕ) :
    pW 3 j = 3 - (Nat.fib (2 * j + 1) : ℤ) ∧ lamW 3 j = luc (2 * j + 2) - 4 := by
  have hz : ∀ j : ℕ, zN 3 (j + 1) = (Nat.fib (2 * j + 1) : ℤ) - 1 := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      rcases (show j = 0 ∨ j = 1 ∨ 2 ≤ j by omega) with h | h | h
      · subst h; simp [zN]
      · subst h; simp [zN, Nat.fib_add_two]
      · obtain ⟨m, rfl⟩ : ∃ m, j = m + 2 := ⟨j - 2, by omega⟩
        have h1 := ih m (by omega)
        have h2 : zN 3 (m + 2) = (Nat.fib (2 * m + 3) : ℤ) - 1 := ih (m + 1) (by omega)
        have e : zN 3 (m + 3) = 3 * zN 3 (m + 2) - zN 3 (m + 1) + 1 := zN_rec 3 (m + 1)
        have f1 : Nat.fib (2 * m + 3) = Nat.fib (2 * m + 1) + Nat.fib (2 * m + 2) :=
          Nat.fib_add_two
        have f2 : Nat.fib (2 * m + 2) = Nat.fib (2 * m) + Nat.fib (2 * m + 1) := Nat.fib_add_two
        have f3 : Nat.fib (2 * m + 4) = Nat.fib (2 * m + 2) + Nat.fib (2 * m + 3) :=
          Nat.fib_add_two
        have f4 : Nat.fib (2 * m + 5) = Nat.fib (2 * m + 3) + Nat.fib (2 * m + 4) :=
          Nat.fib_add_two
        show zN 3 (m + 3) = (Nat.fib (2 * m + 5) : ℤ) - 1
        rw [e, h1, h2]
        have g1 : (Nat.fib (2 * m + 3) : ℤ) = Nat.fib (2 * m + 1) + Nat.fib (2 * m + 2) := by
          exact_mod_cast f1
        have g2 : (Nat.fib (2 * m + 2) : ℤ) = Nat.fib (2 * m) + Nat.fib (2 * m + 1) := by
          exact_mod_cast f2
        have g3 : (Nat.fib (2 * m + 4) : ℤ) = Nat.fib (2 * m + 2) + Nat.fib (2 * m + 3) := by
          exact_mod_cast f3
        have g4 : (Nat.fib (2 * m + 5) : ℤ) = Nat.fib (2 * m + 3) + Nat.fib (2 * m + 4) := by
          exact_mod_cast f4
        linarith
  refine ⟨?_, ?_⟩
  · unfold pW
    rw [hz j]
    ring
  · unfold lamW
    have h2 : zN 3 (j + 2) = (Nat.fib (2 * j + 3) : ℤ) - 1 := hz (j + 1)
    rw [hz j, h2, show 2 * j + 2 = (2 * j + 1) + 1 by ring, luc_eq_fib]
    ring

end PropW

end PellPilot

/-! ## Axiom check, every theorem above: each line should list only `propext`, `Classical.choice`,
`Quot.sound` (or a subset). A `sorryAx` here would mean an unproved step. -/
#print axioms PellPilot.down_up
#print axioms PellPilot.up_down
#print axioms PellPilot.up_isSol
#print axioms PellPilot.down_isSol
#print axioms PellPilot.chain_isSol
#print axioms PellPilot.chain_pos
#print axioms PellPilot.chain_eq_sqrt3
#print axioms PellPilot.norm_chain_sqrt3
#print axioms PellPilot.down_pos_lt
#print axioms PellPilot.base_of_le_one
#print axioms PellPilot.chain_complete_aux
#print axioms PellPilot.chain_complete
#print axioms PellPilot.down_iterate_chain
#print axioms PellPilot.descent_reaches_base
#print axioms PellPilot.chain_rec
#print axioms PellPilot.chain_odd
#print axioms PellPilot.chain_b_lt
#print axioms PellPilot.chain_b_ge_three
#print axioms PellPilot.chain_values
#print axioms PellPilot.gbinom_eq_descPochhammer
#print axioms PellPilot.gbinom_natCast
#print axioms PellPilot.gbinom_neg
#print axioms PellPilot.bZ_of_neg
#print axioms PellPilot.bZ_of_gt
#print axioms PellPilot.bZ_natCast
#print axioms PellPilot.term_eq
#print axioms PellPilot.Q_reflect
#print axioms PellPilot.Q_w1k1
#print axioms PellPilot.Q_w1k1_eq_zero_iff
#print axioms PellPilot.step3_identity
#print axioms PellPilot.Bk_neg_one
#print axioms PellPilot.Bk_neg_two
#print axioms PellPilot.Bk_of_le
#print axioms PellPilot.Bk_eq_zero_iff_Ek
#print axioms PellPilot.Qpl_eq
#print axioms PellPilot.Qpl_eq_zero_iff
#print axioms PellPilot.G_eq_zero_iff
#print axioms PellPilot.prop44_a
#print axioms PellPilot.prop44_b
#print axioms PellPilot.P_eq_E4
#print axioms PellPilot.discriminant_eq
#print axioms PellPilot.four_P_eq
#print axioms PellPilot.prop44_p1
#print axioms PellPilot.remark_discriminant
#print axioms PellPilot.prop44_c
#print axioms PellPilot.prop44_c_set
#print axioms PellPilot.two_pk
#print axioms PellPilot.two_lam
#print axioms PellPilot.pk_le_one
#print axioms PellPilot.lam_ge_two
#print axioms PellPilot.step_back
#print axioms PellPilot.lam_lt_succ
#print axioms PellPilot.prop44_d_p
#print axioms PellPilot.prop44_d_l
#print axioms PellPilot.prop44_d_l_one
#print axioms PellPilot.prop44_d_l_ge_two
#print axioms PellPilot.lam_vanishes_twice
#print axioms PellPilot.pk_rec
#print axioms PellPilot.lam_rec
#print axioms PellPilot.pk_values
#print axioms PellPilot.lam_values
#print axioms PellPilot.pk_mod
#print axioms PellPilot.pk_parity
#print axioms PellPilot.prop44_examples
#print axioms PellPilot.vanishing_pairs
#print axioms PellPilot.vanishing_pairs_set
#print axioms PellPilot.Sw_Sw
#print axioms PellPilot.Tw_Tw
#print axioms PellPilot.Ek_Sw
#print axioms PellPilot.Ek_Tw
#print axioms PellPilot.zN_rec
#print axioms PellPilot.z_natCast
#print axioms PellPilot.z_zero
#print axioms PellPilot.z_one
#print axioms PellPilot.z_symm
#print axioms PellPilot.z_rec
#print axioms PellPilot.z_unique
#print axioms PellPilot.Fz_succ
#print axioms PellPilot.Fz_eq_zero
#print axioms PellPilot.Ek_z
#print axioms PellPilot.Tw_z
#print axioms PellPilot.Sw_z
#print axioms PellPilot.TwSw_z
#print axioms PellPilot.IsZPair_Sw
#print axioms PellPilot.IsZPair_Tw
#print axioms PellPilot.descW_cases
#print axioms PellPilot.descW_spec
#print axioms PellPilot.IsZPair_of_descW
#print axioms PellPilot.Ek_imp_IsZPair
#print axioms PellPilot.propW_d
#print axioms PellPilot.propW_d_descent
#print axioms PellPilot.Qk_eq
#print axioms PellPilot.Qpl_eq_Qk
#print axioms PellPilot.propW_a
#print axioms PellPilot.propW_b
#print axioms PellPilot.propW_c
#print axioms PellPilot.zN_grow
#print axioms PellPilot.zN_two
#print axioms PellPilot.zN_three
#print axioms PellPilot.zN_four
#print axioms PellPilot.zN_ge_one
#print axioms PellPilot.zpair_in_range
#print axioms PellPilot.propW_e
#print axioms PellPilot.pW_lamW_values
#print axioms PellPilot.pW_rec
#print axioms PellPilot.lamW_rec
#print axioms PellPilot.Sp_Tp_coords
#print axioms PellPilot.Sp_walk
#print axioms PellPilot.Tp_walk
#print axioms PellPilot.walk_from_base
#print axioms PellPilot.propW_e_one
#print axioms PellPilot.propW_e_zero
#print axioms PellPilot.propW_e_neg
#print axioms PellPilot.chain_b_eq_zN
#print axioms PellPilot.pW_four
#print axioms PellPilot.lamW_four
#print axioms PellPilot.propB_i
#print axioms PellPilot.propB_norm
#print axioms PellPilot.propB_iii
#print axioms PellPilot.propB_ii
#print axioms PellPilot.propB_ii_unit
#print axioms PellPilot.propB_ii_matrices
#print axioms PellPilot.propB_iv
#print axioms PellPilot.propB_v
#print axioms PellPilot.k_two
#print axioms PellPilot.k_two_z
#print axioms PellPilot.luc_eq_fib
#print axioms PellPilot.k_three
