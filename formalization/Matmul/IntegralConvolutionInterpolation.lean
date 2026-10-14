import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensor
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic

/-!
# Integral interpolation by the Vandermonde adjugate

The adjugate identity gives a rank decomposition for a scaled convolution
over every commutative ring. No interpolation nodes are inverted here.
-/

namespace Matmul.IntegralConvolution

open OAI.MatrixMultiplication.Foundation
open scoped BigOperators

def outputLength (r s : ℕ) : ℕ := r + s - 1

/-- Polynomial multiplication, with the third coordinate recording the sum
of the first two exponents. -/
def convolution (B : Type*) [CommSemiring B] (r s : ℕ) :
    Tensor B (Fin r) (Fin s) (Fin (outputLength r s)) :=
  fun x y z => if x.val + y.val = z.val then 1 else 0

def sumIndex {r s : ℕ} (x : Fin r) (y : Fin s) : Fin (outputLength r s) :=
  ⟨x.val + y.val, by unfold outputLength; have := x.isLt; have := y.isLt; omega⟩

/-- An adjugate clears the whole interpolation denominator at once.
This identity is valid even if the nodes coincide or the determinant is zero. -/
theorem rankAtMost_det_vandermonde {B : Type*} [CommRing B] {r s : ℕ}
    (nodes : Fin (outputLength r s) → B) :
    Tensor.RankAtMost
      (fun x y z => (Matrix.vandermonde nodes).det * convolution B r s x y z)
      (outputLength r s) := by
  classical
  let V := Matrix.vandermonde nodes
  refine ⟨(fun i x => nodes i ^ x.val), (fun i y => nodes i ^ y.val),
    (fun i z => V.adjugate z i), ?_⟩
  funext x y z
  let k := sumIndex x y
  have h := congrArg (fun A => A z k) (Matrix.adjugate_mul V)
  change (∑ i, V.adjugate z i * nodes i ^ k.val) =
    V.det * (if z = k then 1 else 0) at h
  have hindex : (z = k) ↔ (x.val + y.val = z.val) := by
    simp [Fin.ext_iff, k, sumIndex, eq_comm]
  have h' : (∑ i, V.adjugate z i * nodes i ^ k.val) =
      V.det * (if x.val + y.val = z.val then 1 else 0) := by
    simpa only [hindex] using h
  change V.det * (if x.val + y.val = z.val then 1 else 0) = _
  rw [← h']
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Tensor.rankOne, k, sumIndex, pow_add]
  ring

/-- Distinct ordinary integer nodes give a nonzero integer multiplier. -/
theorem integer_vandermonde_det_ne_zero (N : ℕ) :
    (Matrix.vandermonde (fun i : Fin N => (i.val : ℤ))).det ≠ 0 := by
  rw [Matrix.det_vandermonde_ne_zero_iff]
  intro i j h
  apply Fin.ext
  change (i.val : ℤ) = (j.val : ℤ) at h
  exact Int.ofNat_injective h

/-- A concrete rank certificate over the integers with one nonzero
multiplier. This is the rational place in the later local patching proof. -/
theorem exists_integer_scaled_rank (r s : ℕ) :
    ∃ E : ℤ, E ≠ 0 ∧ Tensor.RankAtMost
      (fun x y z => E * convolution ℤ r s x y z) (outputLength r s) := by
  refine ⟨(Matrix.vandermonde (fun i : Fin (outputLength r s) => (i.val : ℤ))).det,
    integer_vandermonde_det_ne_zero _, ?_⟩
  exact rankAtMost_det_vandermonde _

#print axioms rankAtMost_det_vandermonde
#print axioms exists_integer_scaled_rank

end Matmul.IntegralConvolution
