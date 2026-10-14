import Matmul.UniversalRecursiveProgram
import Matmul.UniversalPaddedAlgorithm

/-!
# Strict arithmetic programs with zero padding

Padding is compiled to a finite collection of input wires and zero outputs.
Only static coordinate indices are inspected while generating the circuit.
The resulting program contains the recursive arithmetic syntax followed by
output wires; it contains no arbitrary instruction on ring values.
-/

namespace Matmul.UniversalPaddedProgram

open scoped BigOperators
open Matmul.IntegerBilinear Matmul.UniversalRecursion
open Matmul.UniversalRecursiveAlgorithm Matmul.UniversalProgram
open Matmul.UniversalPaddedAlgorithm

noncomputable section

/-- A scalar wire, or a zero output if no input coordinate was selected. -/
def optionalWire {I : Type} : Option I → Circuit I PUnit
  | some i => .wire (fun _ => i)
  | none => .zero

@[simp] theorem optionalWire_cost {I : Type} (i : Option I) :
    (optionalWire i).cost = 0 := by
  cases i <;> rfl

@[simp] theorem optionalWire_multiplications {I : Type} (i : Option I) :
    (optionalWire i).multiplications = 0 := by
  cases i <;> rfl

@[simp] theorem optionalWire_eval {I : Type} {R : Type*} [NonUnitalRing R]
    (i : Option I) (input : I → R) (o : PUnit) :
    (optionalWire i).eval input o = i.elim 0 input := by
  cases i <;> rfl

/-- Compile a finite array of optional input coordinates into wire and zero
syntax. The final wire discards the scalar branch's singleton coordinate. -/
def partialWire {I O : Type} [Fintype O] (select : O → Option I) : Circuit I O :=
  .comp (.bundle (fun o => optionalWire (select o)))
    (.wire (fun o => (o, PUnit.unit)))

@[simp] theorem partialWire_eval {I O : Type} [Fintype O]
    {R : Type*} [NonUnitalRing R] (select : O → Option I)
    (input : I → R) (o : O) :
    (partialWire select).eval input o = (select o).elim 0 input := by
  simp [partialWire]

@[simp] theorem partialWire_cost {I O : Type} [Fintype O]
    (select : O → Option I) : (partialWire select).cost = 0 := by
  simp [partialWire]

@[simp] theorem partialWire_multiplications {I O : Type} [Fintype O]
    (select : O → Option I) : (partialWire select).multiplications = 0 := by
  simp [partialWire]

/-- The original matrix coordinate of an embedded coordinate, or `none`
outside the row or column embedding. This selector depends only on indices. -/
def sourceIndex {X Y X' Y' : Type} (eX : X ↪ X') (eY : Y ↪ Y')
    (p : X' × Y') : Option (X × Y) := by
  classical
  exact if hx : ∃ x, eX x = p.1 then
    if hy : ∃ y, eY y = p.2 then some (Classical.choose hx, Classical.choose hy)
    else none
  else none

/-- Selecting a source coordinate or zero agrees with the semantic zero
extension used in the matrix padding theorem. -/
theorem sourceIndex_pad {X Y X' Y' : Type} {R : Type*} [Zero R]
    (eX : X ↪ X') (eY : Y ↪ Y') (A : Matrix X Y R) (p : X' × Y') :
    (sourceIndex eX eY p).elim 0 (fun q => A q.1 q.2) =
      pad eX eY A p.1 p.2 := by
  classical
  simp only [sourceIndex, pad, Function.extend_def]
  split_ifs <;> simp_all [Function.extend_def]

/-- Present arbitrary rectangular input matrices as one wire family. -/
def encode {X Y Z : Type} {R : Type*}
    (A : Matrix X Y R) (B : Matrix Y Z R) : (X × Y) ⊕ (Y × Z) → R
  | .inl p => A p.1 p.2
  | .inr p => B p.1 p.2

variable {X Y Z : Type} {a b c ρ : ℕ}

/-- Strict wire-and-zero syntax for both padded input matrices. -/
def paddingCircuit (t : ℕ) (eX : X ↪ Index a t)
    (eY : Y ↪ Index b t) (eZ : Z ↪ Index c t) :
    Circuit ((X × Y) ⊕ (Y × Z)) (Matmul.UniversalRecursiveProgram.Input a b c t) :=
  .pair
    (partialWire (fun p => (sourceIndex eX eY p).map Sum.inl))
    (partialWire (fun p => (sourceIndex eY eZ p).map Sum.inr))

@[simp] theorem paddingCircuit_cost (t : ℕ) (eX : X ↪ Index a t)
    (eY : Y ↪ Index b t) (eZ : Z ↪ Index c t) :
    (paddingCircuit t eX eY eZ).cost = 0 := by
  simp [paddingCircuit]

@[simp] theorem paddingCircuit_multiplications (t : ℕ) (eX : X ↪ Index a t)
    (eY : Y ↪ Index b t) (eZ : Z ↪ Index c t) :
    (paddingCircuit t eX eY eZ).multiplications = 0 := by
  simp [paddingCircuit]

/-- The padding circuit's complete input array is precisely the pair of
zero-padded matrices consumed by the strict recursive program. -/
theorem paddingCircuit_eval {R : Type*} [NonUnitalRing R]
    (t : ℕ) (eX : X ↪ Index a t) (eY : Y ↪ Index b t) (eZ : Z ↪ Index c t)
    (A : Matrix X Y R) (B : Matrix Y Z R) :
    (paddingCircuit t eX eY eZ).eval (encode A B) =
      Matmul.UniversalRecursiveProgram.encode (pad eX eY A) (pad eY eZ B) := by
  funext w
  cases w with
  | inl p =>
      simp only [paddingCircuit, Circuit.eval_pair_inl, partialWire_eval,
        Option.elim_map]
      exact sourceIndex_pad eX eY A p
  | inr p =>
      simp only [paddingCircuit, Circuit.eval_pair_inr, partialWire_eval,
        Option.elim_map]
      exact sourceIndex_pad eY eZ B p

/-- An actual strict arithmetic graph for zero-padded rectangular matrix
multiplication, followed by wires selecting the original output coordinates. -/
def programWithEmbeddings (alg : Scheme a b c ρ) (t : ℕ)
    (eX : X ↪ Index a t) (eY : Y ↪ Index b t) (eZ : Z ↪ Index c t) :
    Circuit ((X × Y) ⊕ (Y × Z)) (X × Z) :=
  .comp (paddingCircuit t eX eY eZ)
    (.comp (Matmul.UniversalRecursiveProgram.compile alg t)
      (.wire (fun p => (eX p.1, eZ p.2))))

/-- The strict padded program computes the ordinary, unpadded matrix product
over every noncommutative nonunital ring. -/
theorem programWithEmbeddings_correct {R : Type*} [NonUnitalRing R] [Fintype Y]
    (alg : Scheme a b c ρ) (h : alg.tensor = matrixTensor a b c) (t : ℕ)
    (eX : X ↪ Index a t) (eY : Y ↪ Index b t) (eZ : Z ↪ Index c t)
    (A : Matrix X Y R) (B : Matrix Y Z R) (u : X) (v : Z) :
    (programWithEmbeddings alg t eX eY eZ).eval (encode A B) (u, v) =
      (A * B) u v := by
  simp only [programWithEmbeddings, Circuit.eval_comp, Circuit.eval_wire]
  rw [paddingCircuit_eval, Matmul.UniversalRecursiveProgram.compile_correct alg h]
  exact congrFun (congrFun (pad_product eX eY eZ A B) u) v

/-- Padding and output wires introduce no arithmetic gates. -/
theorem programWithEmbeddings_cost (alg : Scheme a b c ρ) (t : ℕ)
    (eX : X ↪ Index a t) (eY : Y ↪ Index b t) (eZ : Z ↪ Index c t) :
    (programWithEmbeddings alg t eX eY eZ).cost =
      (Matmul.UniversalRecursiveProgram.compile alg t).cost := by
  simp [programWithEmbeddings]

theorem programWithEmbeddings_multiplications (alg : Scheme a b c ρ) (t : ℕ)
    (eX : X ↪ Index a t) (eY : Y ↪ Index b t) (eZ : Z ↪ Index c t) :
    (programWithEmbeddings alg t eX eY eZ).multiplications = ρ ^ t := by
  simp [programWithEmbeddings, Matmul.UniversalRecursiveProgram.compile_multiplications]

variable {n m p : ℕ}

/-- A strict arithmetic program for arbitrary finite rectangular matrix
dimensions, padded to a certified recursive shape. -/
def paddedProgram (alg : Scheme a b c ρ) (t : ℕ)
    (hn : n ≤ a ^ t) (hm : m ≤ b ^ t) (hp : p ≤ c ^ t) :
    Circuit ((Fin n × Fin m) ⊕ (Fin m × Fin p)) (Fin n × Fin p) :=
  programWithEmbeddings alg t (indexEmbedding hn) (indexEmbedding hm) (indexEmbedding hp)

theorem paddedProgram_correct {R : Type*} [NonUnitalRing R]
    (alg : Scheme a b c ρ) (h : alg.tensor = matrixTensor a b c) (t : ℕ)
    (hn : n ≤ a ^ t) (hm : m ≤ b ^ t) (hp : p ≤ c ^ t)
    (A : Matrix (Fin n) (Fin m) R) (B : Matrix (Fin m) (Fin p) R)
    (u : Fin n) (v : Fin p) :
    (paddedProgram alg t hn hm hp).eval (encode A B) (u, v) = (A * B) u v :=
  programWithEmbeddings_correct alg h t (indexEmbedding hn) (indexEmbedding hm)
    (indexEmbedding hp) A B u v

theorem paddedProgram_cost (alg : Scheme a b c ρ) (t : ℕ)
    (hn : n ≤ a ^ t) (hm : m ≤ b ^ t) (hp : p ≤ c ^ t) :
    (paddedProgram alg t hn hm hp).cost =
      (Matmul.UniversalRecursiveProgram.compile alg t).cost :=
  programWithEmbeddings_cost alg t (indexEmbedding hn) (indexEmbedding hm) (indexEmbedding hp)

theorem paddedProgram_multiplications (alg : Scheme a b c ρ) (t : ℕ)
    (hn : n ≤ a ^ t) (hm : m ≤ b ^ t) (hp : p ≤ c ^ t) :
    (paddedProgram alg t hn hm hp).multiplications = ρ ^ t :=
  programWithEmbeddings_multiplications alg t (indexEmbedding hn) (indexEmbedding hm)
    (indexEmbedding hp)

/-- The total primitive gate count obeys the fixed recursive work envelope. -/
theorem paddedProgram_cost_le_work (alg : Scheme a b c ρ) (t : ℕ)
    (hn : n ≤ a ^ t) (hm : m ≤ b ^ t) (hp : p ≤ c ^ t) :
    (paddedProgram alg t hn hm hp).cost ≤
      Matmul.RecursiveCost.work 1 (linearWeight alg) ρ
        (Matmul.RecursiveCost.blockVolume a b c) t := by
  rw [paddedProgram_cost]
  exact Matmul.UniversalRecursiveProgram.compile_cost_le_work alg t

/-- Concrete bound including the equality case between branching and largest
block volume. -/
theorem paddedProgram_cost_bound (alg : Scheme a b c ρ) (hρ : 1 ≤ ρ)
    (hvolume : Matmul.RecursiveCost.blockVolume a b c ≤ ρ) (t : ℕ)
    (hn : n ≤ a ^ t) (hm : m ≤ b ^ t) (hp : p ≤ c ^ t) :
    (paddedProgram alg t hn hm hp).cost ≤ (1 + linearWeight alg) * (t + 1) * ρ ^ t := by
  rw [paddedProgram_cost]
  exact Matmul.UniversalRecursiveProgram.compile_cost_bound alg hρ hvolume t

#print axioms paddedProgram_correct
#print axioms paddedProgram_cost
#print axioms paddedProgram_cost_le_work
#print axioms paddedProgram_multiplications

end

end Matmul.UniversalPaddedProgram
