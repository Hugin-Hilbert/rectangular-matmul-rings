import Matmul.UniversalRecursiveAlgorithm
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fin.Embedding

/-!
# Zero padding for the counted universal rectangular algorithm

Embedding the input coordinates, filling unused entries with zero, and
restricting the output involve only indexing and copying. The recursive
evaluator records every arithmetic operation between those two stages.
-/

namespace Matmul.UniversalPaddedAlgorithm

open scoped BigOperators
open Matmul.IntegerBilinear Matmul.UniversalRecursion
open Matmul.UniversalRecursiveAlgorithm Matmul.UniversalCircuit

noncomputable section

/-- Extend a matrix by zero outside the images of two coordinate embeddings.
This definition selects existing entries and zero; it performs no arithmetic. -/
def pad {X Y X' Y' R : Type*} [Zero R]
    (eX : X ↪ X') (eY : Y ↪ Y') (A : Matrix X Y R) : Matrix X' Y' R :=
  Function.extend eX
    (fun x => Function.extend eY (A x) (fun _ => 0)) (fun _ _ => 0)

@[simp] theorem pad_apply_row {X Y X' Y' R : Type*} [Zero R]
    (eX : X ↪ X') (eY : Y ↪ Y') (A : Matrix X Y R) (x : X) (y : Y') :
    pad eX eY A (eX x) y = Function.extend eY (A x) (fun _ => 0) y := by
  rw [pad, eX.injective.extend_apply]

@[simp] theorem pad_apply {X Y X' Y' R : Type*} [Zero R]
    (eX : X ↪ X') (eY : Y ↪ Y') (A : Matrix X Y R) (x : X) (y : Y) :
    pad eX eY A (eX x) (eY y) = A x y := by
  rw [pad_apply_row, eY.injective.extend_apply]

/-- Extending the shared coordinate by zeros preserves matrix multiplication
on all the original output coordinates. -/
theorem pad_product {X Y Z X' Y' Z' R : Type*} [NonUnitalRing R]
    [Fintype Y] [Fintype Y']
    (eX : X ↪ X') (eY : Y ↪ Y') (eZ : Z ↪ Z')
    (A : Matrix X Y R) (B : Matrix Y Z R) :
    (pad eX eY A * pad eY eZ B).submatrix eX eZ = A * B := by
  classical
  ext i k
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  symm
  apply Fintype.sum_of_injective eY eY.injective
  · intro j hj
    rw [pad_apply_row, Function.extend_apply' _ _ _ hj, zero_mul]
  · intro j
    rw [pad_apply, pad_apply]

variable {R X Y Z : Type*} [NonUnitalRing R] {a b c ρ : ℕ}

/-- Execute the recursive algorithm on zero-padded inputs, then select the
original output coordinates without charging any extra arithmetic. -/
def runWithEmbeddings (alg : Scheme a b c ρ) (t : ℕ)
    (eX : X ↪ Index a t) (eY : Y ↪ Index b t) (eZ : Z ↪ Index c t)
    (A : Matrix X Y R) (B : Matrix Y Z R) : Matmul.UniversalCircuit.Computation (Matrix X Z R) :=
  Matmul.UniversalCircuit.Computation.map (fun C => C.submatrix eX eZ)
    (run alg t (pad eX eY A) (pad eY eZ B))

/-- The zero-padded counted algorithm computes the original matrix product. -/
theorem runWithEmbeddings_correct [Fintype Y]
    (alg : Scheme a b c ρ) (h : alg.tensor = matrixTensor a b c) (t : ℕ)
    (eX : X ↪ Index a t) (eY : Y ↪ Index b t) (eZ : Z ↪ Index c t)
    (A : Matrix X Y R) (B : Matrix Y Z R) :
    (runWithEmbeddings alg t eX eY eZ A B).value = A * B := by
  rw [runWithEmbeddings, Matmul.UniversalCircuit.Computation.map_value, run_correct alg h, pad_product]

/-- Zero padding and restriction preserve the recursive arithmetic bound. -/
theorem runWithEmbeddings_cost_le_work
    (alg : Scheme a b c ρ) (t : ℕ)
    (eX : X ↪ Index a t) (eY : Y ↪ Index b t) (eZ : Z ↪ Index c t)
    (A : Matrix X Y R) (B : Matrix Y Z R) :
    (runWithEmbeddings alg t eX eY eZ A B).cost ≤
      Matmul.RecursiveCost.work 1 (linearWeight alg) ρ
        (Matmul.RecursiveCost.blockVolume a b c) t := by
  rw [runWithEmbeddings, Matmul.UniversalCircuit.Computation.map_cost]
  exact run_cost_le_work alg t _ _

/-- Zero padding and restriction preserve the exact multiplication count. -/
theorem runWithEmbeddings_multiplications
    (alg : Scheme a b c ρ) (t : ℕ)
    (eX : X ↪ Index a t) (eY : Y ↪ Index b t) (eZ : Z ↪ Index c t)
    (A : Matrix X Y R) (B : Matrix Y Z R) :
    (runWithEmbeddings alg t eX eY eZ A B).multiplications = ρ ^ t := by
  rw [runWithEmbeddings, Matmul.UniversalCircuit.Computation.map_multiplications, run_multiplications]

/-- Embed an ordinary finite matrix coordinate into its recursive padded
coordinate type whenever the padded dimension is large enough. -/
def indexEmbedding {n a t : ℕ} (h : n ≤ a ^ t) : Fin n ↪ Index a t :=
  (Fin.castLEEmb h).trans
    (Fintype.equivFinOfCardEq (card_index a t)).symm.toEmbedding

variable {n m p : ℕ}

/-- A counted algorithm on arbitrary rectangular finite dimensions, with
explicit proofs that each recursive padded dimension is sufficient. -/
def runPadded (alg : Scheme a b c ρ) (t : ℕ)
    (hn : n ≤ a ^ t) (hm : m ≤ b ^ t) (hp : p ≤ c ^ t)
    (A : Matrix (Fin n) (Fin m) R) (B : Matrix (Fin m) (Fin p) R) :
    Matmul.UniversalCircuit.Computation (Matrix (Fin n) (Fin p) R) :=
  runWithEmbeddings alg t (indexEmbedding hn) (indexEmbedding hm)
    (indexEmbedding hp) A B

/-- The padded algorithm returns the original, unpadded matrix product. -/
theorem runPadded_correct (alg : Scheme a b c ρ)
    (h : alg.tensor = matrixTensor a b c) (t : ℕ)
    (hn : n ≤ a ^ t) (hm : m ≤ b ^ t) (hp : p ≤ c ^ t)
    (A : Matrix (Fin n) (Fin m) R) (B : Matrix (Fin m) (Fin p) R) :
    (runPadded alg t hn hm hp A B).value = A * B :=
  runWithEmbeddings_correct alg h t (indexEmbedding hn) (indexEmbedding hm) (indexEmbedding hp) A B

/-- The arbitrary rectangular dimensions incur the same arithmetic bound as
the fixed padded recursive shape. -/
theorem runPadded_cost_le_work (alg : Scheme a b c ρ) (t : ℕ)
    (hn : n ≤ a ^ t) (hm : m ≤ b ^ t) (hp : p ≤ c ^ t)
    (A : Matrix (Fin n) (Fin m) R) (B : Matrix (Fin m) (Fin p) R) :
    (runPadded alg t hn hm hp A B).cost ≤
      Matmul.RecursiveCost.work 1 (linearWeight alg) ρ
        (Matmul.RecursiveCost.blockVolume a b c) t :=
  runWithEmbeddings_cost_le_work alg t (indexEmbedding hn) (indexEmbedding hm) (indexEmbedding hp) A B

theorem runPadded_multiplications (alg : Scheme a b c ρ) (t : ℕ)
    (hn : n ≤ a ^ t) (hm : m ≤ b ^ t) (hp : p ≤ c ^ t)
    (A : Matrix (Fin n) (Fin m) R) (B : Matrix (Fin m) (Fin p) R) :
    (runPadded alg t hn hm hp A B).multiplications = ρ ^ t :=
  runWithEmbeddings_multiplications alg t (indexEmbedding hn) (indexEmbedding hm) (indexEmbedding hp) A B

#print axioms pad_product
#print axioms runPadded_correct
#print axioms runPadded_cost_le_work
#print axioms runPadded_multiplications

end

end Matmul.UniversalPaddedAlgorithm
