import Mathlib.RingTheory.Norm.Defs
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Clearing a finite free algebra denominator by its norm

The adjugate of multiplication by `δ` produces `γ` with
`δ * γ = algebraMap ℤ B (Algebra.norm ℤ δ)`. No nonzero or invertibility
assumption is needed for this integral identity.
-/

namespace Matmul.IntegralConvolution

open Module
open scoped Matrix

set_option backward.isDefEq.respectTransparency false in
theorem exists_mul_eq_norm {B : Type*} [CommRing B]
    {d : ℕ} (basis : Basis (Fin d) ℤ B) (δ : B) :
    ∃ γ : B, δ * γ = algebraMap ℤ B (Algebra.norm ℤ δ) := by
  classical
  let M := Algebra.leftMulMatrix basis δ
  let γ := basis.equivFun.symm (Matrix.cramer M (basis.equivFun 1))
  refine ⟨γ, ?_⟩
  apply basis.equivFun.injective
  rw [Basis.equivFun_apply, ← Algebra.leftMulMatrix_mulVec_repr]
  change M *ᵥ basis.equivFun γ = basis.equivFun (algebraMap ℤ B (Algebra.norm ℤ δ))
  rw [show basis.equivFun γ = Matrix.cramer M (basis.equivFun 1) from
    basis.equivFun.apply_symm_apply _]
  rw [Matrix.mulVec_cramer]
  rw [show M.det = Algebra.norm ℤ δ from (Algebra.norm_eq_matrix_det basis δ).symm]
  rw [Algebra.algebraMap_eq_smul_one]
  exact (map_smul basis.equivFun (Algebra.norm ℤ δ) (1 : B)).symm

#print axioms exists_mul_eq_norm

end Matmul.IntegralConvolution
