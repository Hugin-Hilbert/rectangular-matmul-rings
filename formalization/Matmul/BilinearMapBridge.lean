import Matmul.IntegerBilinear
import Mathlib.LinearAlgebra.Matrix.Bilinear

/-!
# Integer tensor certificates for arbitrary bilinear maps

An integer algorithm can substitute any integer bilinear operation for its
product slots. In particular, products of rectangular blocks have different
left-input, right-input, and output types. Their correctness follows from this
bilinear interpretation rather than a ring structure on the blocks.
-/

namespace Matmul.IntegerBilinear

open scoped BigOperators
open OAI.MatrixMultiplication.Foundation

variable {X Y Z U V W : Type*}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]

/-- Interpret an integer tensor using an arbitrary bilinear map between three
abelian groups, equipped with their canonical integer module structures. -/
def contractBilinear [Fintype X] [Fintype Y] (T : Tensor ℤ X Y Z)
    (μ : U →ₗ[ℤ] V →ₗ[ℤ] W) (A : X → U) (B : Y → V) (z : Z) : W :=
  ∑ x, ∑ y, T x y z • μ (A x) (B y)

/-- Evaluate the same integer coefficients with `r` calls to a bilinear map. -/
def Algorithm.evaluateBilinear [Fintype X] [Fintype Y] {r : ℕ}
    (alg : Algorithm X Y Z r) (μ : U →ₗ[ℤ] V →ₗ[ℤ] W)
    (A : X → U) (B : Y → V) (z : Z) : W :=
  ∑ i, alg.output i z •
    μ (∑ x, alg.left i x • A x) (∑ y, alg.right i y • B y)

private theorem bilinear_sum_sum [Fintype X] [Fintype Y]
    (μ : U →ₗ[ℤ] V →ₗ[ℤ] W) (A : X → U) (B : Y → V) :
    μ (∑ x, A x) (∑ y, B y) = ∑ x, ∑ y, μ (A x) (B y) := by
  rw [map_sum μ]
  simp only [LinearMap.sum_apply]
  simp only [map_sum]

private theorem bilinear_three_smul (μ : U →ₗ[ℤ] V →ₗ[ℤ] W)
    (a b c : ℤ) (u : U) (v : V) :
    c • μ (a • u) (b • v) = (a * b * c) • μ u v := by
  rw [μ.map_smul, LinearMap.smul_apply, (μ u).map_smul, ← mul_smul, ← mul_smul]
  congr 1
  ring

/-- Every integer tensor identity remains valid under any integer bilinear
operation, without needing the input and output spaces to be the same. -/
theorem Algorithm.evaluateBilinear_eq_contract [Fintype X] [Fintype Y] {r : ℕ}
    (alg : Algorithm X Y Z r) (μ : U →ₗ[ℤ] V →ₗ[ℤ] W)
    (A : X → U) (B : Y → V) (z : Z) :
    alg.evaluateBilinear μ A B z = contractBilinear alg.tensor μ A B z := by
  classical
  simp only [Algorithm.evaluateBilinear, Algorithm.tensor, contractBilinear,
    Tensor.rankOne, bilinear_sum_sum, Finset.smul_sum, bilinear_three_smul,
    Finset.sum_smul]
  calc
    (∑ i, ∑ x, ∑ y,
      (alg.left i x * alg.right i y * alg.output i z) • μ (A x) (B y)) =
        ∑ x, ∑ i, ∑ y,
          (alg.left i x * alg.right i y * alg.output i z) • μ (A x) (B y) :=
      Finset.sum_comm
    _ = ∑ x, ∑ y, ∑ i,
          (alg.left i x * alg.right i y * alg.output i z) • μ (A x) (B y) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact Finset.sum_comm

/-- A certified integer algorithm can be applied to any bilinear map. -/
theorem Algorithm.evaluateBilinear_correct [Fintype X] [Fintype Y] {r : ℕ}
    (alg : Algorithm X Y Z r) {T : Tensor ℤ X Y Z} (h : alg.tensor = T)
    (μ : U →ₗ[ℤ] V →ₗ[ℤ] W) (A : X → U) (B : Y → V) (z : Z) :
    alg.evaluateBilinear μ A B z = contractBilinear T μ A B z := by
  rw [alg.evaluateBilinear_eq_contract, h]

/-- Contracting the matrix tensor with a bilinear operation gives the sum over
the shared block index, with the order of the two inputs preserved. -/
theorem matrixTensor_contractBilinear {a b c : ℕ}
    (μ : U →ₗ[ℤ] V →ₗ[ℤ] W) (A : Matrix (Fin a) (Fin b) U)
    (B : Matrix (Fin b) (Fin c) V) (i : Fin a) (k : Fin c) :
    contractBilinear (matrixTensor a b c) μ (fun x => A x.1 x.2)
      (fun y => B y.1 y.2) (k, i) = ∑ j, μ (A i j) (B j k) := by
  classical
  simp only [contractBilinear, matrixTensor, Fintype.sum_prod_type]
  simp [ite_smul, ite_and, eq_comm]

/-- The matrix tensor algorithm is valid for rectangular block products,
whose left and right block matrices may have different shapes. -/
theorem Algorithm.rectangular_block_correct {R l m n : Type*}
    [NonUnitalRing R] [Fintype m] {a b c r : ℕ}
    (alg : Algorithm (Fin a × Fin b) (Fin b × Fin c) (Fin c × Fin a) r)
    (h : alg.tensor = matrixTensor a b c)
    (A : Matrix (Fin a) (Fin b) (Matrix l m R))
    (B : Matrix (Fin b) (Fin c) (Matrix m n R)) (i : Fin a) (k : Fin c) :
    alg.evaluateBilinear (mulLinearMap ℤ)
      (fun x => A x.1 x.2) (fun y => B y.1 y.2) (k, i) =
        ∑ j, A i j * B j k := by
  rw [alg.evaluateBilinear_correct h, matrixTensor_contractBilinear]
  rfl

/-- Lay out a matrix of rectangular blocks as one matrix. -/
def packBlocks {R l m : Type*} {a b : ℕ}
    (A : Matrix (Fin a) (Fin b) (Matrix l m R)) :
    Matrix (Fin a × l) (Fin b × m) R :=
  fun i j => A i.1 j.1 i.2 j.2

/-- Blockwise multiplication agrees entrywise with multiplication of the
packed matrices. This is the correctness step used by block recursion. -/
theorem packed_block_product {R l m n : Type*} [NonUnitalRing R] [Fintype m]
    {a b c : ℕ} (A : Matrix (Fin a) (Fin b) (Matrix l m R))
    (B : Matrix (Fin b) (Fin c) (Matrix m n R))
    (i : Fin a) (k : Fin c) (u : l) (v : n) :
    (∑ j, A i j * B j k) u v = (packBlocks A * packBlocks B) (i, u) (k, v) := by
  classical
  simp [packBlocks, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.sum_apply]

/-- An integer matrix-tensor certificate gives a correct algorithm for the
actual packed rectangular matrix product with `r` rectangular block products. -/
theorem Algorithm.packed_rectangular_correct {R l m n : Type*}
    [NonUnitalRing R] [Fintype m] {a b c r : ℕ}
    (alg : Algorithm (Fin a × Fin b) (Fin b × Fin c) (Fin c × Fin a) r)
    (h : alg.tensor = matrixTensor a b c)
    (A : Matrix (Fin a) (Fin b) (Matrix l m R))
    (B : Matrix (Fin b) (Fin c) (Matrix m n R))
    (i : Fin a) (k : Fin c) (u : l) (v : n) :
    (alg.evaluateBilinear (mulLinearMap ℤ)
      (fun x => A x.1 x.2) (fun y => B y.1 y.2) (k, i)) u v =
        (packBlocks A * packBlocks B) (i, u) (k, v) := by
  rw [alg.rectangular_block_correct h, packed_block_product]

#print axioms Algorithm.evaluateBilinear_eq_contract
#print axioms Algorithm.rectangular_block_correct
#print axioms Algorithm.packed_rectangular_correct

end Matmul.IntegerBilinear
