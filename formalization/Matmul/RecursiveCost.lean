import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Log

/-!
# Integer cost bounds for rectangular block recursion

A fixed base algorithm supplies a fixed number `ρ` of recursive products and a
fixed integer linear-combination cost `K` per block entry. If the three block
entry counts grow by at most `d`, the deterministic work envelope satisfies
`C(t+1) = ρ C(t) + K d^t`.

The lemmas here solve that recurrence, including the critical case `d = ρ`.
They do not postulate a matrix-multiplication exponent or a fast algorithm.
-/

namespace Matmul.RecursiveCost

/-- Deterministic work envelope with `ρ` recursive calls per level and at most
`K d^t` additional operations at the next level. -/
def work (base K ρ d : ℕ) : ℕ → ℕ
  | 0 => base
  | t + 1 => ρ * work base K ρ d t + K * d ^ t

@[simp] theorem work_zero (base K ρ d : ℕ) : work base K ρ d 0 = base := rfl

@[simp] theorem work_succ (base K ρ d t : ℕ) :
    work base K ρ d (t + 1) = ρ * work base K ρ d t + K * d ^ t := rfl

/-- The recurrence bound holds for any actual cost function satisfying the
initial and step inequalities. It remains valid when the input/output volume
factor equals the recursive branching factor. -/
theorem recurrence_bound (C : ℕ → ℕ) (base K ρ d : ℕ)
    (hρ : 1 ≤ ρ) (hd : d ≤ ρ) (hzero : C 0 ≤ base)
    (hstep : ∀ t, C (t + 1) ≤ ρ * C t + K * d ^ t) (t : ℕ) :
    C t ≤ (base + K * t) * ρ ^ t := by
  induction t with
  | zero => simpa using hzero
  | succ t ih =>
    have hp : d ^ t ≤ ρ ^ t := Nat.pow_le_pow_left hd t
    calc
      C (t + 1) ≤ ρ * C t + K * d ^ t := hstep t
      _ ≤ ρ * ((base + K * t) * ρ ^ t) + K * ρ ^ t := by
        exact Nat.add_le_add (Nat.mul_le_mul_left ρ ih) (Nat.mul_le_mul_left K hp)
      _ = ((base + K * t) * ρ + K) * ρ ^ t := by ring
      _ ≤ ((base + K * (t + 1)) * ρ) * ρ ^ t := by
        apply Nat.mul_le_mul_right
        nlinarith
      _ = (base + K * (t + 1)) * ρ ^ (t + 1) := by
        rw [pow_succ]
        ring

/-- A convenient bound using one fixed constant and one linear level factor. -/
theorem recurrence_bound_linear (C : ℕ → ℕ) (base K ρ d : ℕ)
    (hρ : 1 ≤ ρ) (hd : d ≤ ρ) (hzero : C 0 ≤ base)
    (hstep : ∀ t, C (t + 1) ≤ ρ * C t + K * d ^ t) (t : ℕ) :
    C t ≤ (base + K) * (t + 1) * ρ ^ t := by
  apply (recurrence_bound C base K ρ d hρ hd hzero hstep t).trans
  apply Nat.mul_le_mul_right
  nlinarith

/-- The explicit deterministic work envelope has the same bound. -/
theorem work_bound (base K ρ d : ℕ) (hρ : 1 ≤ ρ) (hd : d ≤ ρ) (t : ℕ) :
    work base K ρ d t ≤ (base + K) * (t + 1) * ρ ^ t := by
  exact recurrence_bound_linear (work base K ρ d) base K ρ d hρ hd
    (by simp) (fun t => by simp) t

/-- All three rectangular block volumes can be represented by one factor. -/
def blockVolume (a b c : ℕ) : ℕ := max (a * b) (max (b * c) (a * c))

/-- Each of the three block volumes is bounded by the chosen volume factor. -/
theorem blockVolume_bounds (a b c : ℕ) :
    a * b ≤ blockVolume a b c ∧ b * c ≤ blockVolume a b c ∧
      a * c ≤ blockVolume a b c := by
  simp only [blockVolume]
  exact ⟨Nat.le_max_left _ _,
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _),
    (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)⟩

/-- In the rectangular case, a branching factor dominating all input and
output block volumes gives a logarithmic number-of-levels overhead. -/
theorem rectangular_work_bound (base K ρ a b c : ℕ) (hρ : 1 ≤ ρ)
    (hvolume : blockVolume a b c ≤ ρ) (t : ℕ) :
    work base K ρ (blockVolume a b c) t ≤ (base + K) * (t + 1) * ρ ^ t :=
  work_bound base K ρ (blockVolume a b c) hρ hvolume t

open Filter Asymptotics

/-- Any fixed linear factor in the number of recursion levels is eventually
absorbed by an arbitrarily small exponential slack. -/
theorem linear_factor_absorbed (K q : ℝ) (hq : 1 < q) :
    ∀ᶠ t : ℕ in atTop, K * ((t : ℝ) + 1) ≤ q ^ t := by
  have h0 : (fun _ : ℕ => (1 : ℝ)) =o[atTop] (fun t => q ^ t) := by
    simpa using (isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) 0 hq)
  have h1 : (fun t : ℕ => (t : ℝ)) =o[atTop] (fun t => q ^ t) :=
    isLittleO_coe_const_pow_of_one_lt hq
  have h := ((h1.add h0).const_mul_left K).bound (by norm_num : (0 : ℝ) < 1)
  filter_upwards [h] with t ht
  simpa only [one_mul, Real.norm_eq_abs,
    abs_of_pos (pow_pos (lt_trans zero_lt_one hq) t)] using
    (le_abs_self (K * ((t : ℝ) + 1))).trans ht

/-- Exponential slack absorbs the linear number-of-levels factor in the work
envelope, for every real growth factor strictly greater than one. -/
theorem work_eventually_exponential (base K ρ d : ℕ) (hρ : 1 ≤ ρ) (hd : d ≤ ρ)
    (q : ℝ) (hq : 1 < q) :
    ∀ᶠ t : ℕ in atTop, (work base K ρ d t : ℝ) ≤ ((ρ : ℝ) * q) ^ t := by
  filter_upwards [linear_factor_absorbed (base + K) q hq] with t ht
  have hc : (work base K ρ d t : ℝ) ≤
      ((base : ℝ) + K) * ((t : ℝ) + 1) * (ρ : ℝ) ^ t := by
    exact_mod_cast work_bound base K ρ d hρ hd t
  calc
    (work base K ρ d t : ℝ) ≤
        ((base : ℝ) + K) * ((t : ℝ) + 1) * (ρ : ℝ) ^ t := hc
    _ ≤ q ^ t * (ρ : ℝ) ^ t := mul_le_mul_of_nonneg_right ht (by positivity)
    _ = ((ρ : ℝ) * q) ^ t := by rw [mul_pow]; ring

private theorem rpow_log_ratio (b q : ℝ) (hb : 1 < b) (hq : 0 < q) :
    b ^ (Real.log q / Real.log b) = q := by
  rw [Real.rpow_def_of_pos (lt_trans zero_lt_one hb)]
  have hbne : Real.log b ≠ 0 := ne_of_gt (Real.log_pos hb)
  have heq : Real.log b * (Real.log q / Real.log b) = Real.log q := by field_simp
  rw [heq, Real.exp_log hq]

/-- At the exact sizes `b^t`, the work envelope obeys the usual rank-ratio
exponent with every positive slack `ε`. -/
theorem work_eventually_rpow (base K ρ d b : ℕ) (hρ : 1 ≤ ρ) (hd : d ≤ ρ)
    (hb : 1 < b) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℕ in atTop, (work base K ρ d t : ℝ) ≤
      ((b : ℝ) ^ t) ^ (Real.log (ρ : ℝ) / Real.log (b : ℝ) + ε) := by
  have hbR : 1 < (b : ℝ) := by exact_mod_cast hb
  have hρR : 0 < (ρ : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hρ)
  have h := work_eventually_exponential base K ρ d hρ hd
    ((b : ℝ) ^ ε) (Real.one_lt_rpow hbR hε)
  filter_upwards [h] with t ht
  rw [← Real.rpow_pow_comm (le_of_lt (lt_trans zero_lt_one hbR)),
    Real.rpow_add (lt_trans zero_lt_one hbR), rpow_log_ratio b ρ hbR hρR]
  exact ht

/-- Padding to the next strictly larger base power loses at most a fixed
factor `b` in size. It also covers sizes that are already exact powers. -/
theorem padding_size_bounds (b n : ℕ) (hb : 1 < b) (hn : 0 < n) :
    n ≤ b ^ (Nat.log b n + 1) ∧ b ^ (Nat.log b n + 1) ≤ b * n := by
  constructor
  · exact (Nat.lt_pow_succ_log_self hb n).le
  · rw [pow_succ, mul_comm b n]
    exact Nat.mul_le_mul_right b (Nat.pow_log_le_self b hn.ne')

/-- The work envelope after padding an arbitrary positive size to a base
power. -/
def paddedWork (base K ρ d b n : ℕ) : ℕ :=
  work base K ρ d (Nat.log b n + 1)

/-- Logarithmic-depth padding preserves every positive exponent slack. The
fixed multiplicative loss is displayed explicitly as `b^(log_b ρ + ε)`. -/
theorem paddedWork_eventually_rpow (base K ρ d b : ℕ) (hρ : 1 ≤ ρ) (hd : d ≤ ρ)
    (hb : 1 < b) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (paddedWork base K ρ d b n : ℝ) ≤
      (b : ℝ) ^ (Real.log (ρ : ℝ) / Real.log (b : ℝ) + ε) *
        (n : ℝ) ^ (Real.log (ρ : ℝ) / Real.log (b : ℝ) + ε) := by
  obtain ⟨t₀, ht₀⟩ := eventually_atTop.mp (work_eventually_rpow base K ρ d b hρ hd hb ε hε)
  have hbR : 1 < (b : ℝ) := by exact_mod_cast hb
  have hρR : 1 ≤ (ρ : ℝ) := by exact_mod_cast hρ
  have hθ : 0 ≤ Real.log (ρ : ℝ) / Real.log (b : ℝ) + ε :=
    le_of_lt (add_pos_of_nonneg_of_pos
      (div_nonneg (Real.log_nonneg hρR) (Real.log_pos hbR).le) hε)
  filter_upwards [eventually_ge_atTop (max 1 (b ^ t₀))] with n hn
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one ((Nat.le_max_left _ _).trans hn)
  have hlog : t₀ ≤ Nat.log b n :=
    Nat.le_log_of_pow_le hb ((Nat.le_max_right _ _).trans hn)
  have ht : t₀ ≤ Nat.log b n + 1 := hlog.trans (Nat.le_add_right _ _)
  have hpad : (b : ℝ) ^ (Nat.log b n + 1) ≤ (b : ℝ) * n := by
    exact_mod_cast (padding_size_bounds b n hb hnpos).2
  calc
    (paddedWork base K ρ d b n : ℝ) ≤
        ((b : ℝ) ^ (Nat.log b n + 1)) ^
          (Real.log (ρ : ℝ) / Real.log (b : ℝ) + ε) := ht₀ _ ht
    _ ≤ ((b : ℝ) * n) ^ (Real.log (ρ : ℝ) / Real.log (b : ℝ) + ε) :=
      Real.rpow_le_rpow (by positivity) hpad hθ
    _ = (b : ℝ) ^ (Real.log (ρ : ℝ) / Real.log (b : ℝ) + ε) *
        (n : ℝ) ^ (Real.log (ρ : ℝ) / Real.log (b : ℝ) + ε) :=
      Real.mul_rpow (by positivity) (by positivity)

#print axioms recurrence_bound
#print axioms work_bound
#print axioms rectangular_work_bound
#print axioms work_eventually_rpow
#print axioms paddedWork_eventually_rpow

end Matmul.RecursiveCost
