import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensor
import Mathlib.Algebra.Module.NatInt
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Data.Matrix.Mul

/-!
# Integer bilinear identities over arbitrary rings

An integer rank decomposition has an interpretation in every noncommutative,
nonunital ring: coefficients act by repeated addition and subtraction, and every
product has its left input from the first matrix and its right input from the
second matrix. No division, scalar embedding, or commutativity is needed.

This file proves the transfer of **integer** decompositions. A complex rank or
border-rank bound alone is not an integer decomposition.
-/

namespace Matmul.IntegerBilinear

open scoped BigOperators
open OAI.MatrixMultiplication.Foundation

variable {X Y Z : Type*}

/-- An integral bilinear straight-line algorithm with exactly `r` product slots.
The three arrays of coefficients are independent of the target ring. -/
structure Algorithm (X Y Z : Type*) (r : ℕ) where
  left : Fin r → X → ℤ
  right : Fin r → Y → ℤ
  output : Fin r → Z → ℤ

/-- Interpret a coefficient tensor using the canonical integer action on the
additive group of a ring, avoiding any assumption that the ring has a unit. -/
def contract {R : Type*} [NonUnitalRing R] [Fintype X] [Fintype Y]
    (T : Tensor ℤ X Y Z) (A : X → R) (B : Y → R) (z : Z) : R :=
  ∑ x, ∑ y, T x y z • (A x * B y)

/-- The only products of ring elements here are the `r` products indexed by
`Fin r`; all three coefficient maps use integer scalar actions. -/
def Algorithm.evaluate {R : Type*} [NonUnitalRing R]
    [Fintype X] [Fintype Y] {r : ℕ} (alg : Algorithm X Y Z r)
    (A : X → R) (B : Y → R) (z : Z) : R :=
  ∑ i, alg.output i z •
    ((∑ x, alg.left i x • A x) * (∑ y, alg.right i y • B y))

/-- The coefficient tensor certified by an algorithm. -/
def Algorithm.tensor {r : ℕ} (alg : Algorithm X Y Z r) : Tensor ℤ X Y Z :=
  fun x y z => ∑ i, Tensor.rankOne (alg.left i) (alg.right i) (alg.output i) x y z

private theorem three_smul_mul {R : Type*} [NonUnitalRing R]
    (a b c : ℤ) (u v : R) :
    c • ((a • u) * (b • v)) = (a * b * c) • (u * v) := by
  rw [smul_mul_assoc, mul_smul_comm, ← mul_smul, ← mul_smul]
  congr 1
  ring

/-- Evaluation of an integral algorithm equals contraction of its tensor in
any nonunital ring, with no interchange of the two ring-valued inputs. -/
theorem Algorithm.evaluate_eq_contract {R : Type*} [NonUnitalRing R]
    [Fintype X] [Fintype Y] {r : ℕ} (alg : Algorithm X Y Z r)
    (A : X → R) (B : Y → R) (z : Z) :
    alg.evaluate A B z = contract alg.tensor A B z := by
  classical
  simp only [Algorithm.evaluate, Algorithm.tensor, contract, Tensor.rankOne,
    Finset.sum_mul_sum, Finset.smul_sum, three_smul_mul, Finset.sum_smul]
  calc
    (∑ i, ∑ x, ∑ y,
      (alg.left i x * alg.right i y * alg.output i z) • (A x * B y)) =
        ∑ x, ∑ i, ∑ y,
          (alg.left i x * alg.right i y * alg.output i z) • (A x * B y) :=
      Finset.sum_comm
    _ = ∑ x, ∑ y, ∑ i,
          (alg.left i x * alg.right i y * alg.output i z) • (A x * B y) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact Finset.sum_comm

/-- Extract an algorithm whose coefficients are integers from an integer tensor
rank certificate. This is a constructive reuse of the upstream `RankAtMost`
definition, with the same number of product slots. -/
theorem rankAtMost_iff_exists_algorithm {T : Tensor ℤ X Y Z} {r : ℕ} :
    Tensor.RankAtMost T r ↔ ∃ alg : Algorithm X Y Z r, alg.tensor = T := by
  constructor
  · rintro ⟨a, b, c, h⟩
    exact ⟨⟨a, b, c⟩, h.symm⟩
  · rintro ⟨alg, h⟩
    exact ⟨alg.left, alg.right, alg.output, h.symm⟩

/-- A rank certificate over the integers gives a correct algorithm over every
nonunital ring. The algorithm witness is chosen before the target ring. -/
theorem integer_rank_gives_universal_algorithm
    [Fintype X] [Fintype Y] {T : Tensor ℤ X Y Z} {r : ℕ}
    (h : Tensor.RankAtMost T r) :
    ∃ alg : Algorithm X Y Z r, alg.tensor = T ∧
      ∀ (R : Type) [NonUnitalRing R] (A : X → R) (B : Y → R) (z : Z),
        alg.evaluate A B z = contract T A B z := by
  obtain ⟨alg, halg⟩ := rankAtMost_iff_exists_algorithm.mp h
  refine ⟨alg, halg, ?_⟩
  intro R inst A B z
  rw [alg.evaluate_eq_contract, halg]

/-- The integer coefficient tensor of rectangular matrix multiplication.
The output index is cyclically ordered as in the tensor convention. -/
def matrixTensor (a b c : ℕ) :
    Tensor ℤ (Fin a × Fin b) (Fin b × Fin c) (Fin c × Fin a) :=
  fun x y z => if x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1 then 1 else 0

/-- Contraction of the integer matrix tensor is the usual ordered matrix
product, including rectangular and zero-dimensional matrices. -/
theorem matrixTensor_contract {R : Type*} [NonUnitalRing R]
    {a b c : ℕ} (A : Matrix (Fin a) (Fin b) R)
    (B : Matrix (Fin b) (Fin c) R) (i : Fin a) (k : Fin c) :
    contract (matrixTensor a b c) (fun x => A x.1 x.2)
      (fun y => B y.1 y.2) (k, i) = (A * B) i k := by
  classical
  simp only [contract, matrixTensor, Fintype.sum_prod_type, Matrix.mul_apply]
  simp [ite_smul, ite_and, eq_comm]

/-- Any integral rank decomposition of a rectangular matrix multiplication
tensor gives an algorithm using its `r` ordered products in every ring, even a
noncommutative ring without a multiplicative identity. -/
theorem integer_matrix_rank_gives_ring_algorithm {a b c r : ℕ}
    (h : Tensor.RankAtMost (matrixTensor a b c) r) :
    ∃ alg : Algorithm (Fin a × Fin b) (Fin b × Fin c) (Fin c × Fin a) r,
      alg.tensor = matrixTensor a b c ∧
      ∀ (R : Type) [NonUnitalRing R]
        (A : Matrix (Fin a) (Fin b) R) (B : Matrix (Fin b) (Fin c) R)
        (i : Fin a) (k : Fin c),
        alg.evaluate (fun x => A x.1 x.2) (fun y => B y.1 y.2) (k, i) =
          (A * B) i k := by
  obtain ⟨alg, halg, hcorrect⟩ := integer_rank_gives_universal_algorithm h
  refine ⟨alg, halg, ?_⟩
  intro R inst A B i k
  rw [hcorrect R, matrixTensor_contract]

#print axioms Algorithm.evaluate_eq_contract
#print axioms integer_rank_gives_universal_algorithm
#print axioms integer_matrix_rank_gives_ring_algorithm

end Matmul.IntegerBilinear
