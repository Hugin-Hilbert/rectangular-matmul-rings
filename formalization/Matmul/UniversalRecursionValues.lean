import Matmul.BilinearMapBridge

/-!
# Recursive evaluation of an integer rectangular matrix algorithm

A fixed integer certificate is evaluated recursively on rectangular blocks.
The recursion keeps the two multiplication arguments in their original order,
so it is valid over every nonunital ring, including noncommutative rings.
The finite index type at depth `t` has exactly `a ^ t` entries.
-/

namespace Matmul.UniversalRecursion

open scoped BigOperators
open Matmul.IntegerBilinear

/-- Coordinates of a recursively blocked matrix of side length `a ^ t`. -/
def Index (a : ℕ) : ℕ → Type
  | 0 => PUnit
  | t + 1 => Fin a × Index a t

@[instance_reducible] private def indexFintype (a : ℕ) : (t : ℕ) → Fintype (Index a t)
  | 0 => inferInstanceAs (Fintype PUnit)
  | t + 1 =>
      letI := indexFintype a t
      inferInstanceAs (Fintype (Fin a × Index a t))

instance (a t : ℕ) : Fintype (Index a t) := indexFintype a t

/-- Recursive block coordinates have the intended matrix dimension. -/
@[simp] theorem card_index (a t : ℕ) : Fintype.card (Index a t) = a ^ t := by
  induction t with
  | zero =>
      change Fintype.card PUnit = 1
      exact Fintype.card_unique
  | succ t ih =>
      change Fintype.card (Fin a × Index a t) = a ^ (t + 1)
      rw [Fintype.card_prod, Fintype.card_fin, ih, pow_succ]
      exact Nat.mul_comm _ _

variable {R : Type*} [NonUnitalRing R] {a b c ρ : ℕ}

/-- View the outermost pair of coordinates as block coordinates. -/
def blocks (t : ℕ)
    (A : Matrix (Index a (t + 1)) (Index b (t + 1)) R) :
    Matrix (Fin a) (Fin b) (Matrix (Index a t) (Index b t) R) :=
  fun i j u v => A (i, u) (j, v)

omit [NonUnitalRing R] in
@[simp] theorem packBlocks_blocks (t : ℕ)
    (A : Matrix (Index a (t + 1)) (Index b (t + 1)) R) :
    packBlocks (blocks t A) = A := rfl

/-- Left matrix supplied to one recursive product slot. -/
def leftInput
    (alg : Algorithm (Fin a × Fin b) (Fin b × Fin c) (Fin c × Fin a) ρ)
    (t : ℕ) (A : Matrix (Index a (t + 1)) (Index b (t + 1)) R)
    (s : Fin ρ) : Matrix (Index a t) (Index b t) R :=
  ∑ x, alg.left s x • blocks t A x.1 x.2

/-- Right matrix supplied to the same recursive product slot. -/
def rightInput
    (alg : Algorithm (Fin a × Fin b) (Fin b × Fin c) (Fin c × Fin a) ρ)
    (t : ℕ) (B : Matrix (Index b (t + 1)) (Index c (t + 1)) R)
    (s : Fin ρ) : Matrix (Index b t) (Index c t) R :=
  ∑ y, alg.right s y • blocks t B y.1 y.2

/-- Deterministic recursive evaluator. At depth zero it performs one scalar
product. Each following level performs the certificate's `ρ` recursive
products, with integer linear combinations before and after those products. -/
def multiply
    (alg : Algorithm (Fin a × Fin b) (Fin b × Fin c) (Fin c × Fin a) ρ) :
    (t : ℕ) → Matrix (Index a t) (Index b t) R →
      Matrix (Index b t) (Index c t) R → Matrix (Index a t) (Index c t) R
  | 0, A, B => fun _ _ => A PUnit.unit PUnit.unit * B PUnit.unit PUnit.unit
  | t + 1, A, B =>
      packBlocks (fun i k =>
        ∑ s, alg.output s (k, i) •
          multiply alg t (leftInput alg t A s) (rightInput alg t B s))

/-- The recursively evaluated integer certificate computes the actual matrix
product at every depth over every nonunital ring. -/
theorem multiply_correct
    (alg : Algorithm (Fin a × Fin b) (Fin b × Fin c) (Fin c × Fin a) ρ)
    (h : alg.tensor = matrixTensor a b c) (t : ℕ)
    (A : Matrix (Index a t) (Index b t) R)
    (B : Matrix (Index b t) (Index c t) R) :
    multiply alg t A B = A * B := by
  induction t with
  | zero =>
      ext i k
      cases i
      cases k
      change A PUnit.unit PUnit.unit * B PUnit.unit PUnit.unit =
        ∑ j : PUnit, A PUnit.unit j * B j PUnit.unit
      exact (Fintype.sum_unique
        (fun j : PUnit => A PUnit.unit j * B j PUnit.unit)).symm
  | succ t ih =>
      ext ⟨i, u⟩ ⟨k, v⟩
      calc
        (multiply alg (t + 1) A B) (i, u) (k, v) =
            (alg.evaluateBilinear (mulLinearMap ℤ)
              (fun x => blocks t A x.1 x.2)
              (fun y => blocks t B y.1 y.2) (k, i)) u v := by
          simp only [multiply, packBlocks, ih, Algorithm.evaluateBilinear,
            leftInput, rightInput]
          rfl
        _ = (packBlocks (blocks t A) * packBlocks (blocks t B))
            (i, u) (k, v) :=
          alg.packed_rectangular_correct h (blocks t A) (blocks t B) i k u v
        _ = (A * B) (i, u) (k, v) := rfl

#print axioms multiply_correct
#print axioms card_index

end Matmul.UniversalRecursion
