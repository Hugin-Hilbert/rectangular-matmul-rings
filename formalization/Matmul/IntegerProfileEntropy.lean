import OAI.LinearAlgebra.MatrixMultiplication.Entropy.ComplexFiniteEntropy
import Mathlib

/-! Finite entropy optimization for the integral convolution profiles. -/

namespace Matmul.IntegerProfileEntropy

open OAI.MatrixMultiplication.Foundation
open scoped BigOperators

noncomputable section

/-- The positive optimizing law normalizes the powered summands. -/
def poweredLaw {ι : Type*} [Fintype ι] (z : ι → ℝ) (t : ℝ)
    (hz : ∀ i, 0 < z i) (hS : 0 < ∑ i, z i ^ (1 / t)) : FiniteLaw ι where
  mass i := z i ^ (1 / t) / ∑ j, z j ^ (1 / t)
  nonneg i := div_nonneg (Real.rpow_nonneg (hz i).le _) hS.le
  total := by rw [← Finset.sum_div, div_self hS.ne']

/-- At the optimizing law, the entropy expression is the logarithm of the partition sum. -/
theorem poweredLaw_partition {ι : Type*} [Fintype ι] {z : ι → ℝ} {t : ℝ}
    (hz : ∀ i, 0 < z i) (ht : 0 < t)
    (hS : 0 < ∑ i, z i ^ (1 / t)) :
    t * finiteEntropy (poweredLaw z t hz hS).mass +
      ∑ i, (poweredLaw z t hz hS).mass i * Real.log (z i) =
        t * Real.log (∑ i, z i ^ (1 / t)) := by
  classical
  let w := poweredLaw z t hz hS
  have hlog (i : ι) : Real.log (w.mass i) =
      (1 / t) * Real.log (z i) - Real.log (∑ j, z j ^ (1 / t)) := by
    dsimp [w, poweredLaw]
    rw [Real.log_div (Real.rpow_pos_of_pos (hz i) _).ne' hS.ne',
      Real.log_rpow (hz i)]
  have hpoint (i : ι) :
      t * entropyTerm (w.mass i) + w.mass i * Real.log (z i) =
        w.mass i * (t * Real.log (∑ j, z j ^ (1 / t))) := by
    unfold entropyTerm
    rw [hlog]
    field_simp [ht.ne']
    ring
  change t * (∑ i, entropyTerm (w.mass i)) +
    (∑ i, w.mass i * Real.log (z i)) = t * Real.log (∑ i, z i ^ (1 / t))
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  simp_rw [hpoint]
  rw [← Finset.sum_mul, w.total, one_mul]

/-- Bounds for every finite law optimize to a bound for the powered sum. -/
theorem powered_sum_le_of_log_entropy_bound {ι : Type*} [Fintype ι]
    {z : ι → ℝ} {M t C : ℝ}
    (hz : ∀ i, 0 < z i) (hM : 0 < M) (ht : 0 < t)
    (hbound : ∀ w : FiniteLaw ι,
      t * finiteEntropy w.mass + ∑ i, w.mass i * Real.log (z i) ≤
        Real.log M + t * C) :
    ∑ i, z i ^ (1 / t) ≤ Real.exp C * M ^ (1 / t) := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl hempty =>
      letI := hempty
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
      positivity
  | inr hnonempty =>
      letI := hnonempty
      have hS : 0 < ∑ i, z i ^ (1 / t) :=
        Finset.sum_pos (fun i _ => Real.rpow_pos_of_pos (hz i) _) Finset.univ_nonempty
      have h := hbound (poweredLaw z t hz hS)
      rw [poweredLaw_partition hz ht hS] at h
      have hlog : Real.log (∑ i, z i ^ (1 / t)) ≤ C + Real.log M * (1 / t) := by
        apply (mul_le_mul_iff_of_pos_right ht).mp
        field_simp [ht.ne']
        nlinarith
      calc
        ∑ i, z i ^ (1 / t) = Real.exp (Real.log (∑ i, z i ^ (1 / t))) :=
          (Real.exp_log hS).symm
        _ ≤ Real.exp (C + Real.log M * (1 / t)) := Real.exp_le_exp.mpr hlog
        _ = Real.exp C * M ^ (1 / t) := by
          rw [Real.exp_add, Real.rpow_def_of_pos hM]

/-- A geometric mean turns two simultaneous entropy bounds into their average. -/
theorem geometric_mean_log_bound {ι : Type*} [Fintype ι]
    {x y : ι → ℝ} {A B p q C : ℝ}
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) (hA : 0 < A) (hB : 0 < B)
    (hboundx : ∀ w : FiniteLaw ι,
      p * finiteEntropy w.mass + ∑ i, w.mass i * Real.log (x i) ≤ Real.log A + C * p)
    (hboundy : ∀ w : FiniteLaw ι,
      q * finiteEntropy w.mass + ∑ i, w.mass i * Real.log (y i) ≤ Real.log B + C * q)
    (w : FiniteLaw ι) :
    ((p + q) / 2) * finiteEntropy w.mass +
      ∑ i, w.mass i * Real.log (Real.sqrt (x i * y i)) ≤
        Real.log (Real.sqrt (A * B)) + ((p + q) / 2) * C := by
  classical
  have hlog (i : ι) : Real.log (Real.sqrt (x i * y i)) =
      (Real.log (x i) + Real.log (y i)) / 2 := by
    rw [Real.log_sqrt (mul_pos (hx i) (hy i)).le, Real.log_mul (hx i).ne' (hy i).ne']
  have hlogAB : Real.log (Real.sqrt (A * B)) = (Real.log A + Real.log B) / 2 := by
    rw [Real.log_sqrt (mul_pos hA hB).le, Real.log_mul hA.ne' hB.ne']
  simp_rw [hlog]
  rw [hlogAB]
  have hsum : (∑ i, w.mass i * ((Real.log (x i) + Real.log (y i)) / 2)) =
      ((∑ i, w.mass i * Real.log (x i)) + (∑ i, w.mass i * Real.log (y i))) / 2 := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum]
  have hxw := hboundx w
  have hyw := hboundy w
  linarith

/-- Simultaneous bounds optimize to the powered sum of geometric means. -/
theorem geometric_mean_powered_sum_le {ι : Type*} [Fintype ι]
    {x y : ι → ℝ} {A B p q C : ℝ}
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) (hA : 0 < A) (hB : 0 < B)
    (hpq : 0 < (p + q) / 2)
    (hboundx : ∀ w : FiniteLaw ι,
      p * finiteEntropy w.mass + ∑ i, w.mass i * Real.log (x i) ≤ Real.log A + C * p)
    (hboundy : ∀ w : FiniteLaw ι,
      q * finiteEntropy w.mass + ∑ i, w.mass i * Real.log (y i) ≤ Real.log B + C * q) :
    ∑ i, Real.sqrt (x i * y i) ^ (1 / ((p + q) / 2)) ≤
      Real.exp C * Real.sqrt (A * B) ^ (1 / ((p + q) / 2)) := by
  apply powered_sum_le_of_log_entropy_bound
    (fun i => Real.sqrt_pos.mpr (mul_pos (hx i) (hy i)))
    (Real.sqrt_pos.mpr (mul_pos hA hB)) hpq
  exact geometric_mean_log_bound hx hy hA hB hboundx hboundy

#print axioms powered_sum_le_of_log_entropy_bound
#print axioms geometric_mean_powered_sum_le

end
end Matmul.IntegerProfileEntropy
