/-
Pure analytic part of upstream-allfields
`OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Entropy/Tag.lean`.
The Character namespace, its import, and its unused field variable are omitted.
The integral-type entropy-limit proofs below retain the upstream declaration names.
-/
import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Growth.PolynomialOverhead
import OAI.LinearAlgebra.MatrixMultiplication.Entropy.ComplexTypeEntropy
import OAI.LinearAlgebra.MatrixMultiplication.Entropy.ConditionalContinuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OAI


/-!
# The entropy limit for matched types

The finite hypothesis in this file is an inequality at every integral type.
The conclusion follows by first repeating a fixed type, and then approximating
an arbitrary probability law by rational laws. No entropy inequality is
included in the finite hypothesis.
-/

noncomputable section

open MatrixMultiplication.Foundation Filter
open scoped BigOperators Topology

namespace MatrixMultiplication.AuxiliarySeparation

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- The character contribution of all words of one prescribed type. -/
def typeContribution (values : A → ℝ) (p : ℝ) (counts : A → ℕ) (t : ℕ) : ℝ :=
  (Fintype.card (ExactWords (fun a => t * counts a)) : ℝ) ^ p *
    ∏ a, values a ^ (t * counts a)

theorem typeContribution_pos (values : A → ℝ) (p : ℝ) (counts : A → ℕ)
    (hvalues : ∀ a, 0 < values a) (t : ℕ) :
    0 < typeContribution values p counts t := by
  unfold typeContribution
  exact mul_pos
    (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (exactWords_card_pos _)) p)
    (Finset.prod_pos (fun a _ => pow_pos (hvalues a) _))

theorem log_typeContribution (values : A → ℝ) (p : ℝ) (counts : A → ℕ)
    (hvalues : ∀ a, 0 < values a) (t : ℕ) :
    Real.log (typeContribution values p counts t) =
      p * Real.log (Fintype.card (ExactWords (fun a => t * counts a)) : ℝ) +
        (t : ℝ) * ∑ a, (counts a : ℝ) * Real.log (values a) := by
  unfold typeContribution
  rw [Real.log_mul
    (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (exactWords_card_pos _)) p).ne'
    (Finset.prod_pos (fun a _ => pow_pos (hvalues a) _)).ne',
    Real.log_rpow (Nat.cast_pos.mpr (exactWords_card_pos _)),
    Real.log_prod (fun a _ => (pow_pos (hvalues a) _).ne')]
  simp only [Real.log_pow, Nat.cast_mul, mul_assoc, Finset.mul_sum]

/-- Repeating one exact type has its Shannon entropy growth rate. -/
theorem typeContribution_rate (values : A → ℝ) (p : ℝ) (counts : A → ℕ)
    (hvalues : ∀ a, 0 < values a) (hD : 0 < ∑ a, counts a) :
    Tendsto
      (fun t : ℕ => Real.log (typeContribution values p counts t) /
        ((t : ℝ) * (∑ a, counts a : ℕ))) atTop
      (𝓝 (p * finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) +
        ∑ a, ((counts a : ℝ) / (∑ a, counts a : ℕ)) * Real.log (values a))) := by
  have hlimit := ((tendsto_log_exactWords_card_mul counts hD).const_mul p).add_const
    (∑ a, ((counts a : ℝ) / (∑ a, counts a : ℕ)) * Real.log (values a))
  apply hlimit.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with t ht
  rw [log_typeContribution values p counts hvalues]
  have ht' : (t : ℝ) ≠ 0 := (Nat.cast_pos.mpr ht).ne'
  have hD' : (∑ a, counts a : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hD)
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  push_cast
  field_simp

/-- A finite bound on each repetition of a fixed type implies its logarithmic
entropy bound; the fixed loss `C` disappears in the limit. -/
theorem log_type_bound (values : A → ℝ) (p source C : ℝ) (counts : A → ℕ)
    (hvalues : ∀ a, 0 < values a) (hsource : 0 < source) (hC : 0 < C)
    (hD : 0 < ∑ a, counts a)
    (hfinite : ∀ t : ℕ, 0 < t →
      typeContribution values p counts t ≤ C * source ^ (t * ∑ a, counts a)) :
    p * finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) +
      ∑ a, ((counts a : ℝ) / (∑ a, counts a : ℕ)) * Real.log (values a) ≤
        Real.log source := by
  apply (Real.le_log_iff_exp_le hsource).2
  apply exp_le_of_tendsto_log_div hsource hC
    (tendsto_id.atTop_mul_const' hD)
    (Eventually.of_forall (typeContribution_pos values p counts hvalues))
  · simpa only [Nat.cast_mul, id_eq] using typeContribution_rate values p counts hvalues hD
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with t ht
    exact hfinite t ht

/-- Rational laws can be represented by one exact integral type. -/
theorem rational_log_tag_of_finite_type_bounds
    (q : RationalLaw A) (values : A → ℝ) (p source C : ℝ)
    (hvalues : ∀ a, 0 < values a) (hsource : 0 < source) (hC : 0 < C)
    (hfinite : ∀ counts : A → ℕ, 0 < ∑ a, counts a → ∀ t : ℕ, 0 < t →
      typeContribution values p counts t ≤ C * source ^ (t * ∑ a, counts a)) :
    p * finiteEntropy q.toFiniteLaw.mass +
      ∑ a, q.toFiniteLaw.mass a * Real.log (values a) ≤ Real.log source := by
  obtain ⟨counts, hD, hmass⟩ := q.exists_type_representation
  have h := log_type_bound values p source C counts hvalues hsource hC hD
    (hfinite counts hD)
  simpa only [hmass] using h

/-- Integral type bounds imply the tag inequality on the whole finite
probability simplex, including laws with zero coordinates. -/
theorem log_tag_of_finite_type_bounds
    (q : FiniteLaw A) (values : A → ℝ) (p source C : ℝ)
    (hvalues : ∀ a, 0 < values a) (hsource : 0 < source) (hC : 0 < C)
    (hfinite : ∀ counts : A → ℕ, 0 < ∑ a, counts a → ∀ t : ℕ, 0 < t →
      typeContribution values p counts t ≤ C * source ^ (t * ∑ a, counts a)) :
    p * finiteEntropy q.mass +
      ∑ a, q.mass a * Real.log (values a) ≤ Real.log source := by
  obtain ⟨r, hr⟩ := MatrixMultiplication.ConditionalLabels.exists_rational_law_sequence q
  have hlinear : Tendsto
      (fun n => ∑ a, (r n).toFiniteLaw.mass a * Real.log (values a)) atTop
      (𝓝 (∑ a, q.mass a * Real.log (values a))) :=
    tendsto_finsetSum Finset.univ (fun a _ => (hr a).mul_const _)
  have hlimit := ((FiniteLaw.entropy_tendsto hr).const_mul p).add hlinear
  exact le_of_tendsto hlimit (Eventually.of_forall (fun n =>
    rational_log_tag_of_finite_type_bounds (r n) values p source C
      hvalues hsource hC hfinite))

/-- Exponentiating gives the entropy-weighted geometric-mean form. -/
theorem tag_of_finite_type_bounds
    (q : FiniteLaw A) (values : A → ℝ) (p source C : ℝ)
    (hvalues : ∀ a, 0 < values a) (hsource : 0 < source) (hC : 0 < C)
    (hfinite : ∀ counts : A → ℕ, 0 < ∑ a, counts a → ∀ t : ℕ, 0 < t →
      typeContribution values p counts t ≤ C * source ^ (t * ∑ a, counts a)) :
    Real.exp (p * finiteEntropy q.mass) * ∏ a, values a ^ q.mass a ≤ source := by
  have h := Real.exp_le_exp.mpr
    (log_tag_of_finite_type_bounds q values p source C hvalues hsource hC hfinite)
  rw [Real.exp_log hsource, Real.exp_add, Real.exp_sum] at h
  convert h using 1
  congr 1
  apply Finset.prod_congr rfl
  intro a _
  rw [Real.rpow_def_of_pos (hvalues a), mul_comm]

/-- It suffices to prove one finite inequality for every integral type. -/
theorem log_tag_of_integral_bounds
    (q : FiniteLaw A) (values : A → ℝ) (p source C : ℝ)
    (hvalues : ∀ a, 0 < values a) (hsource : 0 < source) (hC : 0 < C)
    (hfinite : ∀ counts : A → ℕ, 0 < ∑ a, counts a →
      (Fintype.card (ExactWords counts) : ℝ) ^ p * ∏ a, values a ^ counts a ≤
        C * source ^ (∑ a, counts a)) :
    p * finiteEntropy q.mass +
      ∑ a, q.mass a * Real.log (values a) ≤ Real.log source := by
  apply log_tag_of_finite_type_bounds q values p source C hvalues hsource hC
  intro counts hD t ht
  have hsum : (∑ a, t * counts a) = t * ∑ a, counts a := by
    rw [Finset.mul_sum]
  have hpositive : 0 < ∑ a, t * counts a := by
    rw [hsum]
    exact Nat.mul_pos ht hD
  simpa only [typeContribution, hsum] using hfinite (fun a => t * counts a) hpositive

/-- The geometric-mean formulation from finite inequalities for integral types. -/
theorem tag_of_integral_bounds
    (q : FiniteLaw A) (values : A → ℝ) (p source C : ℝ)
    (hvalues : ∀ a, 0 < values a) (hsource : 0 < source) (hC : 0 < C)
    (hfinite : ∀ counts : A → ℕ, 0 < ∑ a, counts a →
      (Fintype.card (ExactWords counts) : ℝ) ^ p * ∏ a, values a ^ counts a ≤
        C * source ^ (∑ a, counts a)) :
    Real.exp (p * finiteEntropy q.mass) * ∏ a, values a ^ q.mass a ≤ source := by
  apply tag_of_finite_type_bounds q values p source C hvalues hsource hC
  intro counts hD t ht
  have hsum : (∑ a, t * counts a) = t * ∑ a, counts a := by
    rw [Finset.mul_sum]
  have hpositive : 0 < ∑ a, t * counts a := by
    rw [hsum]
    exact Nat.mul_pos ht hD
  simpa only [typeContribution, hsum] using hfinite (fun a => t * counts a) hpositive

end MatrixMultiplication.AuxiliarySeparation

end

end OAI
