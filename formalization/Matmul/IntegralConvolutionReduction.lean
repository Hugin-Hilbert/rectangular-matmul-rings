import Matmul.IntegralConvolutionInterpolation
import Mathlib.RingTheory.Norm.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Data.ZMod.Basic

/-!
# Reduction of finite free integer algebras

Compatible bases identify the integer multiplication matrix after reduction
with the multiplication matrix of the reduced algebra. Consequently norms
commute with reduction. This is used to obtain integer interpolation
multipliers that avoid a prescribed prime.
-/

namespace Matmul.IntegralConvolution

open scoped BigOperators
open Module

variable {B K F : Type*} [CommRing B] [CommRing K] [CommRing F]
  [Algebra K F]

/-- Coordinates commute with a ring homomorphism taking an integer basis
to a basis over the reduced coefficient ring. -/
theorem repr_map_of_compatible_basis {d : ℕ}
    (bZ : Basis (Fin d) ℤ B) (bK : Basis (Fin d) K F)
    (φ : B →+* F) (hb : ∀ i, φ (bZ i) = bK i) (x : B) (i : Fin d) :
    bK.repr (φ x) i = (bZ.repr x i : K) := by
  have heq : φ x = ∑ j, (bZ.repr x j : K) • bK j := by
    conv_lhs => rw [← bZ.sum_repr x]
    simp only [map_sum, map_zsmul, hb]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Algebra.smul_def (bZ.repr x j : K) (bK j)]
    simp only [map_intCast, zsmul_eq_mul]
  rw [heq, bK.repr_sum_self]

/-- The finite free algebra norm commutes with reduction whenever the
two chosen bases are compatible. -/
theorem norm_map_of_compatible_basis {d : ℕ}
    (bZ : Basis (Fin d) ℤ B) (bK : Basis (Fin d) K F)
    (φ : B →+* F) (hb : ∀ i, φ (bZ i) = bK i) (x : B) :
    (Algebra.norm ℤ x : K) = Algebra.norm K (φ x) := by
  classical
  rw [Algebra.norm_eq_matrix_det bZ, Algebra.norm_eq_matrix_det bK]
  change (Int.castRingHom K) ((Algebra.leftMulMatrix bZ x).det) = _
  rw [(Int.castRingHom K).map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply,
    Algebra.leftMulMatrix_eq_repr_mul]
  change (bZ.repr (x * bZ j) i : K) = _
  rw [← repr_map_of_compatible_basis bZ bK φ hb]
  simp only [map_mul, hb]

#print axioms norm_map_of_compatible_basis

/-- Compatible bases make reduction surjective: lift each of the finitely
many coordinates through the surjective integer cast to `ZMod p`. -/
theorem surjective_of_compatible_zmod_basis {p d : ℕ}
    {B F : Type*} [CommRing B] [CommRing F] [Algebra (ZMod p) F]
    (bZ : Basis (Fin d) ℤ B) (bK : Basis (Fin d) (ZMod p) F)
    (φ : B →+* F) (hb : ∀ i, φ (bZ i) = bK i) : Function.Surjective φ := by
  classical
  intro x
  choose c hc using fun i : Fin d => ZMod.intCast_surjective (bK.repr x i)
  refine ⟨∑ i, c i • bZ i, ?_⟩
  rw [map_sum]
  calc
    (∑ i, φ (c i • bZ i)) = ∑ i, (c i : ZMod p) • bK i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [map_zsmul, hb, Algebra.smul_def (c i : ZMod p) (bK i)]
      simp only [map_intCast, zsmul_eq_mul]
    _ = ∑ i, bK.repr x i • bK i := by simp only [hc]
    _ = x := bK.sum_repr x

#print axioms surjective_of_compatible_zmod_basis

end Matmul.IntegralConvolution
