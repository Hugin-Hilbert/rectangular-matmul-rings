import Matmul.IntegralSpectrum
import Matmul.AsymptoticLogRank

/-!
# Eliminating finite integral catalysts

The absorption comparison below is the generic semiring lemma from
OpenAI's `AuxiliarySeparation/Spectrum/Obstruction.lean` (Apache-2.0),
instantiated on unit-admitting integer tensors. The finite product and
fixed scalar iteration retain all constants explicitly.
-/

namespace Matmul.IntegralSpectrum

open OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring

noncomputable section
abbrev S := UnitTensorClass ℤ

/-- A common multiplicative factor stays fixed when a comparison is iterated.
No cancellation in the restriction order is used. -/
theorem fixed_factor_power_comparison (a b c : S) (h : a * c ≤ b * c) (p : ℕ) :
    a ^ p * c ≤ b ^ p * c := by
  induction p with
  | zero => simp
  | succ p ih =>
    calc
      a ^ (p + 1) * c = a ^ p * (a * c) := by ring
      _ ≤ a ^ p * (b * c) := UnitTensorClass.mul_mono le_rfl h
      _ = b * (a ^ p * c) := by ring
      _ ≤ b * (b ^ p * c) := UnitTensorClass.mul_mono le_rfl ih
      _ = b ^ (p + 1) * c := by ring

/-- Iterating an additive catalyst and absorbing it into a fixed tensor. -/
theorem catalytic_power_comparison (D t s : S) (k C : ℕ)
    (hcat : D + t * s ≤ D + (k : S) * s)
    (hD : D ≤ (C : S) * s) (n j : ℕ) :
    (n : S) ^ j * t ^ j * s ≤ ((n * k + C : ℕ) : S) ^ j * s := by
  have hiter : ∀ m : ℕ,
      D + (m : S) * (t * s) ≤ D + (m : S) * ((k : S) * s) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      calc
        D + ((m + 1 : ℕ) : S) * (t * s) =
            (D + t * s) + (m : S) * (t * s) := by push_cast; ring
        _ ≤ (D + (k : S) * s) + (m : S) * (t * s) :=
          UnitTensorClass.add_mono hcat le_rfl
        _ = (D + (m : S) * (t * s)) + (k : S) * s := by ring
        _ ≤ (D + (m : S) * ((k : S) * s)) + (k : S) * s :=
          UnitTensorClass.add_mono ih le_rfl
        _ = D + ((m + 1 : ℕ) : S) * ((k : S) * s) := by push_cast; ring
  have habsorb : (n : S) * t * s ≤ ((n * k + C : ℕ) : S) * s := by
    calc
      (n : S) * t * s = 0 + (n : S) * (t * s) := by ring
      _ ≤ D + (n : S) * (t * s) :=
        UnitTensorClass.add_mono (UnitTensorClass.zero_le D) le_rfl
      _ ≤ D + (n : S) * ((k : S) * s) := hiter n
      _ ≤ (C : S) * s + (n : S) * ((k : S) * s) :=
        UnitTensorClass.add_mono hD le_rfl
      _ = ((n * k + C : ℕ) : S) * s := by push_cast; ring
  simpa only [mul_comm, mul_left_comm, mul_assoc, mul_pow] using
    fixed_factor_power_comparison ((n : S) * t) ((n * k + C : ℕ) : S) s habsorb j

/-- A positive scalar direct summand cannot be absorbed by a fixed tensor. -/
theorem not_add_positive_nat_le_self (D : S) {m : ℕ} (hm : 0 < m) :
    ¬ D + (m : S) ≤ D := by
  intro h
  have hiter : ∀ n : ℕ, D + ((n * m : ℕ) : S) ≤ D := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        D + (((n + 1) * m : ℕ) : S) = (D + ((n * m : ℕ) : S)) + m := by
          push_cast; ring
        _ ≤ D + (m : S) := UnitTensorClass.add_mono ih le_rfl
        _ ≤ D := h
  let n := UnitTensorClass.rank D + 1
  have hscalar : ((n * m : ℕ) : S) ≤ D := by
    exact (show ((n * m : ℕ) : S) ≤ D + ((n * m : ℕ) : S) by
      simpa only [zero_add] using
        UnitTensorClass.add_mono (UnitTensorClass.zero_le D) le_rfl).trans (hiter n)
  have hrank : n * m ≤ UnitTensorClass.rank D := by
    simpa only [UnitTensorClass.rank_natCast] using UnitTensorClass.rank_mono hscalar
  have hnm : n ≤ n * m := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left n (Nat.succ_le_of_lt hm)
  have hlarge := hnm.trans hrank
  dsimp [n] at hlarge
  omega

/-- Multiplying comparisons at consecutive scalar sizes makes the factorial
factors telescope, keeping the resulting comparison entirely integral. -/
theorem factorial_power_comparison (t s : S) (q k L : ℕ)
    (h : ∀ n : ℕ, ((q * (n + 1) : ℕ) : S) ^ L * t ^ L ≤
      ((q * (n + 2) * k : ℕ) : S) ^ L * s) (j : ℕ) :
    (((q ^ j * j.factorial) ^ L : ℕ) : S) * t ^ (j * L) ≤
      (((q ^ j * (j + 1).factorial) ^ L * k ^ (j * L) : ℕ) : S) * s ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hp := UnitTensorClass.mul_mono ih (h j)
    have ha : (q ^ (j + 1) * (j + 1).factorial) ^ L =
        (q ^ j * j.factorial) ^ L * (q * (j + 1)) ^ L := by
      rw [← mul_pow]
      congr 1
      rw [pow_succ, Nat.factorial_succ]
      ring
    have hf : (j + 2).factorial = (j + 2) * (j + 1).factorial :=
      Nat.factorial_succ (j + 1)
    have hb : (q ^ (j + 1) * (j + 2).factorial) ^ L * k ^ ((j + 1) * L) =
        (q ^ j * (j + 1).factorial) ^ L * k ^ (j * L) * (q * (j + 2) * k) ^ L := by
      rw [hf, pow_succ]
      rw [show q ^ j * q * ((j + 2) * (j + 1).factorial) =
        (q ^ j * (j + 1).factorial) * (q * (j + 2)) by ring]
      simp only [mul_pow, Nat.add_mul, Nat.one_mul, pow_add]
      ring
    calc
      _ = (((q ^ j * j.factorial) ^ L : ℕ) : S) * t ^ (j * L) *
          (((q * (j + 1) : ℕ) : S) ^ L * t ^ L) := by
        rw [ha]
        simp only [Nat.cast_mul, Nat.cast_pow, Nat.add_mul, Nat.one_mul, pow_add]
        ring
      _ ≤ _ := hp
      _ = _ := by
        rw [hb]
        simp only [Nat.cast_mul, Nat.cast_pow, pow_succ]
        ring

/-- A common positive natural factor can be retained as a single constant
in the rank bound, instead of being raised to the number of iterations. -/
theorem rank_power_of_scalar_comparison (t : S) (Q B p : ℕ)
    (hQ : 0 < Q) (h : (Q : S) * t ≤ (Q * B : ℕ)) :
    UnitTensorClass.rank (t ^ p) ≤ Q * B ^ p := by
  have h' : t * (Q : S) ≤ (B : S) * (Q : S) := by
    simpa only [Nat.cast_mul, mul_comm] using h
  have hp := fixed_factor_power_comparison t (B : S) (Q : S) h' p
  have hunit : (1 : S) ≤ Q := by
    simpa only [Nat.cast_one] using (UnitTensorClass.natCast_le_natCast_iff 1 Q).mpr hQ
  have ht : t ^ p ≤ ((Q * B ^ p : ℕ) : S) := by
    calc
      t ^ p = t ^ p * 1 := by ring
      _ ≤ t ^ p * (Q : S) := UnitTensorClass.mul_mono le_rfl hunit
      _ ≤ (B : S) ^ p * (Q : S) := hp
      _ = _ := by push_cast; ring
  simpa only [UnitTensorClass.rank_natCast] using UnitTensorClass.rank_mono ht

/-- An additive catalytic comparison gives explicit near-geometric bounds
on arbitrarily large tensor powers. All auxiliary constants are natural
numbers and every intermediate comparison uses integral restriction. -/
theorem catalytic_rank_power_bound (D t s : S) (k : ℕ) (hk : 0 < k)
    (hs : s ≠ 0) (hcat : D + t * s ≤ D + (k : S) * s) :
    let q := UnitTensorClass.rank D + 1
    ∀ j L p : ℕ,
      UnitTensorClass.rank (t ^ (j * L * p)) ≤
        (q ^ j * j.factorial) ^ L *
          ((j + 1) ^ L * k ^ (j * L) * UnitTensorClass.rank s ^ j) ^ p := by
  dsimp only
  let C := UnitTensorClass.rank D
  let q := C + 1
  have hq : 0 < q := Nat.succ_pos C
  have hs1 : (1 : S) ≤ s := UnitTensorClass.one_le_of_ne_zero hs
  have hD : D ≤ (C : S) * s := by
    exact (UnitTensorClass.le_rank D).trans (by
      simpa only [mul_one] using UnitTensorClass.mul_mono (le_refl (C : S)) hs1)
  have hC : C ≤ q * k := by
    have h := Nat.mul_le_mul_left q hk
    dsimp [q] at *
    omega
  intro j L p
  have hone (n : ℕ) : ((q * (n + 1) : ℕ) : S) ^ L * t ^ L ≤
      ((q * (n + 2) * k : ℕ) : S) ^ L * s := by
    have hn : q * (n + 1) * k + C ≤ q * (n + 2) * k := by nlinarith
    have hnc : ((q * (n + 1) * k + C : ℕ) : S) ≤
        ((q * (n + 2) * k : ℕ) : S) :=
      (UnitTensorClass.natCast_le_natCast_iff _ _).mpr hn
    calc
      _ ≤ ((q * (n + 1) : ℕ) : S) ^ L * t ^ L * s := by
        simpa only [mul_one] using UnitTensorClass.mul_mono
          (le_refl (((q * (n + 1) : ℕ) : S) ^ L * t ^ L)) hs1
      _ ≤ ((q * (n + 1) * k + C : ℕ) : S) ^ L * s :=
        catalytic_power_comparison D t s k C hcat hD (q * (n + 1)) L
      _ ≤ _ := UnitTensorClass.mul_mono (pow_le_pow_left' hnc L) le_rfl
  have hprod := factorial_power_comparison t s q k L hone j
  let Q := (q ^ j * j.factorial) ^ L
  let B := (j + 1) ^ L * k ^ (j * L) * UnitTensorClass.rank s ^ j
  have hQ : 0 < Q := pow_pos (Nat.mul_pos (pow_pos hq j) (Nat.factorial_pos j)) L
  have hsc : s ^ j ≤ ((UnitTensorClass.rank s ^ j : ℕ) : S) := by
    simpa only [Nat.cast_pow] using pow_le_pow_left' (UnitTensorClass.le_rank s) j
  have hbase : (Q : S) * t ^ (j * L) ≤ ((Q * B : ℕ) : S) := by
    calc
      _ ≤ (((q ^ j * (j + 1).factorial) ^ L * k ^ (j * L) : ℕ) : S) * s ^ j := hprod
      _ ≤ (((q ^ j * (j + 1).factorial) ^ L * k ^ (j * L) : ℕ) : S) *
          ((UnitTensorClass.rank s ^ j : ℕ) : S) := UnitTensorClass.mul_mono le_rfl hsc
      _ = _ := by
        dsimp [Q, B]
        simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_pow, mul_pow]
        ring
  have hr := rank_power_of_scalar_comparison (t ^ (j * L)) Q B p hQ hbase
  simpa only [← pow_mul] using hr

/-- The logarithmic integral rank cost cannot exceed the scalar side of an
actual finite catalytic comparison. -/
theorem catalytic_logRankGrowth_le (D t s : S) (k : ℕ) (hk : 0 < k)
    (ht : t ≠ 0) (hs : s ≠ 0) (hcat : D + t * s ≤ D + (k : S) * s) :
    UnitTensorClass.logRankGrowth t ≤ Real.log k := by
  have hsr : 1 ≤ UnitTensorClass.rank s := by
    simpa only [pow_one] using UnitTensorClass.rank_pow_one_le hs 1
  apply UnitTensorClass.logRankGrowth_le_of_rank_bound (k := k)
    (S := UnitTensorClass.rank s) ht hk hsr
    (fun j L => ((UnitTensorClass.rank D + 1) ^ j * j.factorial) ^ L)
  · intro j L
    exact pow_pos (Nat.mul_pos (pow_pos (Nat.succ_pos _) j) (Nat.factorial_pos j)) L
  · intro j L p _ _ _
    exact catalytic_rank_power_bound D t s k hk hs hcat j L p

/-- The infimum of normalized logarithmic ranks, in ordinary rank units. -/
def asymptoticRank (t : S) : ℝ := by
  classical
  exact if t = 0 then 0 else Real.exp (UnitTensorClass.logRankGrowth t)

/-- A positive scalar-gain catalyst bounds the actual infimum of integral
power ranks. The proof treats the zero scalar side separately. -/
theorem catalytic_asymptoticRank_le_of_positive_gain (D t s : S)
    (k m : ℕ) (ht : t ≠ 0) (hm : 0 < m)
    (hcat : D + (m : S) + t * s ≤ D + (k : S) * s) :
    asymptoticRank t ≤ k := by
  have hs : s ≠ 0 := by
    intro hz
    subst s
    exact not_add_positive_nat_le_self D hm (by simpa using hcat)
  have hcat' : D + t * s ≤ D + (k : S) * s := by
    exact (show D + t * s ≤ D + (m : S) + t * s by
      simpa only [add_zero] using UnitTensorClass.add_mono
        (UnitTensorClass.add_mono le_rfl (UnitTensorClass.zero_le (m : S))) le_rfl).trans hcat
  have hk : 0 < k := by
    by_contra hz
    have hk0 : k = 0 := by omega
    rw [hk0] at hcat'
    have hp : (1 : S) ≤ t * s := by
      simpa only [mul_one] using UnitTensorClass.mul_mono
        (UnitTensorClass.one_le_of_ne_zero ht) (UnitTensorClass.one_le_of_ne_zero hs)
    have hbad : D + (1 : S) ≤ D := by
      simpa using (UnitTensorClass.add_mono le_rfl hp).trans hcat'
    exact not_add_positive_nat_le_self D (m := 1) (by omega) (by simpa using hbad)
  have hg := catalytic_logRankGrowth_le D t s k hk ht hs hcat'
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  simp only [asymptoticRank, if_neg ht]
  exact (Real.exp_le_exp.mpr hg).trans_eq (Real.exp_log hkR)

/-- Every integer strictly below the actual asymptotic integral rank is
witnessed by a normalized additive multiplicative monotone character. -/
theorem exists_detecting_character {t : S} (ht : t ≠ 0) {k : ℕ}
    (hk : (k : ℝ) < asymptoticRank t) :
    ∃ χ : Character, Monotone χ ∧
      (∀ x, 0 ≤ χ x ∧ χ x ≤ UnitTensorClass.rank x) ∧ (k : ℝ) ≤ χ t := by
  apply exists_detecting_character_of_no_catalyst t k
  intro D s m hm hcat
  exact (not_lt_of_ge (catalytic_asymptoticRank_le_of_positive_gain D t s k m ht hm hcat)) hk

end
end Matmul.IntegralSpectrum
