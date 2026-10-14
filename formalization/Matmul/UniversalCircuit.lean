import Mathlib.Algebra.Module.NatInt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.EquivFin
import Init.Data.Vector.OfFn
import Mathlib.Tactic

/-!
# Counted arithmetic over a nonunital ring

The input to a primitive is an already available value.  Integer coefficients
are executed by repeated addition and a possible negation.  Combining or
collecting previously computed values only adds their recorded operation counts;
it does not charge again for a shared input.  There is no scalar multiplication
primitive in this computation model.
-/

namespace Matmul.UniversalCircuit

open scoped BigOperators

/-- A value together with the operations used to produce it.  The output may be
a scalar, a matrix, or a family of values. -/
structure Computation (α : Type*) where
  value : α
  additions : ℕ
  negations : ℕ
  multiplications : ℕ

namespace Computation

/-- Every ring addition, negation, and multiplication costs one operation. -/
def cost {α : Type*} (c : Computation α) : ℕ :=
  c.additions + c.negations + c.multiplications

/-- Reading an already available input incurs no arithmetic operations. -/
def pure {α : Type*} (x : α) : Computation α := ⟨x, 0, 0, 0⟩

/-- Relabel a previously computed output without doing ring arithmetic. -/
def map {α β : Type*} (f : α → β) (c : Computation α) : Computation β :=
  ⟨f c.value, c.additions, c.negations, c.multiplications⟩

/-- Combine two completed computations.  `f` specifies only how their outputs
are packaged; any ring arithmetic in a subsequent step is charged separately. -/
def combine {α β γ : Type*} (f : α → β → γ)
    (c : Computation α) (d : Computation β) : Computation γ :=
  ⟨f c.value d.value, c.additions + d.additions,
    c.negations + d.negations, c.multiplications + d.multiplications⟩

/-- Eagerly materialize each finite output computation in an array-backed
vector. Subsequent reads of a stored output do not rerun its producing function.
The finite equivalence fixes the storage order independently of the ring. -/
noncomputable def store {I α : Type*} [Fintype I]
    (c : I → Computation α) : Vector (Computation α) (Fintype.card I) :=
  Vector.ofFn (fun j => c ((Fintype.equivFin I).symm j))

@[simp] theorem store_get {I α : Type*} [Fintype I]
    (c : I → Computation α) (i : I) :
    (store c)[((Fintype.equivFin I) i).val] = c i := by
  simp [store]

/-- Package finite outputs after evaluating and storing each computation once.
Both the returned values and the counters read the same stored vector. Array
allocation and lookup perform no ring arithmetic, so do not add ring operations.
-/
noncomputable def collect {I α : Type*} [Fintype I]
    (c : I → Computation α) : Computation (I → α) :=
  let stored := store c
  let lookup := fun i => stored[((Fintype.equivFin I) i).val]
  ⟨fun i => (lookup i).value, ∑ i, (lookup i).additions,
    ∑ i, (lookup i).negations, ∑ i, (lookup i).multiplications⟩

@[simp] theorem pure_value {α : Type*} (x : α) : (pure x).value = x := rfl
@[simp] theorem pure_cost {α : Type*} (x : α) : (pure x).cost = 0 := rfl
@[simp] theorem pure_multiplications {α : Type*} (x : α) :
    (pure x).multiplications = 0 := rfl
@[simp] theorem map_value {α β : Type*} (f : α → β) (c : Computation α) :
    (map f c).value = f c.value := rfl
@[simp] theorem map_cost {α β : Type*} (f : α → β) (c : Computation α) :
    (map f c).cost = c.cost := rfl
@[simp] theorem map_multiplications {α β : Type*} (f : α → β) (c : Computation α) :
    (map f c).multiplications = c.multiplications := rfl
@[simp] theorem combine_value {α β γ : Type*} (f : α → β → γ)
    (c : Computation α) (d : Computation β) :
    (combine f c d).value = f c.value d.value := rfl
@[simp] theorem combine_multiplications {α β γ : Type*} (f : α → β → γ)
    (c : Computation α) (d : Computation β) :
    (combine f c d).multiplications = c.multiplications + d.multiplications := rfl
@[simp] theorem combine_cost {α β γ : Type*} (f : α → β → γ)
    (c : Computation α) (d : Computation β) :
    (combine f c d).cost = c.cost + d.cost := by
  simp only [cost, combine]
  omega
@[simp] theorem collect_value {I α : Type*} [Fintype I]
    (c : I → Computation α) (i : I) : (collect c).value i = (c i).value := by
  simp [collect]
@[simp] theorem collect_additions {I α : Type*} [Fintype I]
    (c : I → Computation α) : (collect c).additions = ∑ i, (c i).additions := by
  simp [collect]
@[simp] theorem collect_negations {I α : Type*} [Fintype I]
    (c : I → Computation α) : (collect c).negations = ∑ i, (c i).negations := by
  simp [collect]
@[simp] theorem collect_multiplications {I α : Type*} [Fintype I]
    (c : I → Computation α) :
    (collect c).multiplications = ∑ i, (c i).multiplications := by
  simp [collect]
@[simp] theorem collect_cost {I α : Type*} [Fintype I]
    (c : I → Computation α) : (collect c).cost = ∑ i, (c i).cost := by
  simp only [cost, collect_additions, collect_negations, collect_multiplications,
    Finset.sum_add_distrib]

variable {R : Type*} [NonUnitalRing R]

/-- The constant zero is available without arithmetic. -/
def zero : Computation R := pure 0

/-- Execute one addition after evaluating both operands once. -/
def add (c d : Computation R) : Computation R :=
  ⟨c.value + d.value, c.additions + d.additions + 1,
    c.negations + d.negations, c.multiplications + d.multiplications⟩

/-- Execute one negation after evaluating its operand once. -/
def neg (c : Computation R) : Computation R :=
  ⟨-c.value, c.additions, c.negations + 1, c.multiplications⟩

/-- Execute one ordered multiplication after evaluating both operands once. -/
def mul (c d : Computation R) : Computation R :=
  ⟨c.value * d.value, c.additions + d.additions,
    c.negations + d.negations, c.multiplications + d.multiplications + 1⟩

@[simp] theorem zero_value : (zero : Computation R).value = 0 := rfl
@[simp] theorem zero_cost : (zero : Computation R).cost = 0 := rfl
@[simp] theorem zero_multiplications : (zero : Computation R).multiplications = 0 := rfl
@[simp] theorem add_value (c d : Computation R) :
    (add c d).value = c.value + d.value := rfl
@[simp] theorem neg_value (c : Computation R) : (neg c).value = -c.value := rfl
@[simp] theorem mul_value (c d : Computation R) :
    (mul c d).value = c.value * d.value := rfl
@[simp] theorem add_multiplications (c d : Computation R) :
    (add c d).multiplications = c.multiplications + d.multiplications := rfl
@[simp] theorem neg_multiplications (c : Computation R) :
    (neg c).multiplications = c.multiplications := rfl
@[simp] theorem mul_multiplications (c d : Computation R) :
    (mul c d).multiplications = c.multiplications + d.multiplications + 1 := rfl
@[simp] theorem add_cost (c d : Computation R) :
    (add c d).cost = c.cost + d.cost + 1 := by
  simp only [cost, add]
  omega
@[simp] theorem neg_cost (c : Computation R) :
    (neg c).cost = c.cost + 1 := by
  simp only [cost, neg]
  omega
@[simp] theorem mul_cost (c d : Computation R) :
    (mul c d).cost = c.cost + d.cost + 1 := by
  simp only [cost, mul]
  omega

end Computation

variable {R : Type*} [NonUnitalRing R]

/-- Repeatedly add an already available input.  The input itself is reused and
has no evaluation cost at each repetition. -/
def nscaleValue : ℕ → R → Computation R
  | 0, _ => Computation.zero
  | n + 1, x => Computation.add (nscaleValue n x) (Computation.pure x)

@[simp] theorem nscaleValue_value (n : ℕ) (x : R) :
    (nscaleValue n x).value = n • x := by
  induction n with
  | zero => simp [nscaleValue]
  | succ n ih => simp [nscaleValue, ih, succ_nsmul]

@[simp] theorem nscaleValue_additions (n : ℕ) (x : R) :
    (nscaleValue n x).additions = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [nscaleValue, Computation.add, Computation.pure, ih]

@[simp] theorem nscaleValue_negations (n : ℕ) (x : R) :
    (nscaleValue n x).negations = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [nscaleValue, Computation.add, Computation.pure, ih]

@[simp] theorem nscaleValue_multiplications (n : ℕ) (x : R) :
    (nscaleValue n x).multiplications = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [nscaleValue, Computation.add, Computation.pure, ih]

@[simp] theorem nscaleValue_cost (n : ℕ) (x : R) :
    (nscaleValue n x).cost = n := by simp [Computation.cost]

/-- Execute an integer coefficient using additions and at most one negation. -/
def zscaleValue : ℤ → R → Computation R
  | .ofNat n, x => nscaleValue n x
  | .negSucc n, x => Computation.neg (nscaleValue (n + 1) x)

@[simp] theorem zscaleValue_value (n : ℤ) (x : R) :
    (zscaleValue n x).value = n • x := by
  cases n <;> simp [zscaleValue]

@[simp] theorem zscaleValue_additions (n : ℤ) (x : R) :
    (zscaleValue n x).additions = n.natAbs := by
  cases n <;> simp [zscaleValue, Computation.neg]

@[simp] theorem zscaleValue_multiplications (n : ℤ) (x : R) :
    (zscaleValue n x).multiplications = 0 := by
  cases n <;> simp [zscaleValue, Computation.neg]

theorem zscaleValue_negations_le (n : ℤ) (x : R) :
    (zscaleValue n x).negations ≤ 1 := by
  cases n <;> simp [zscaleValue, Computation.neg]

theorem zscaleValue_cost_le (n : ℤ) (x : R) :
    (zscaleValue n x).cost ≤ n.natAbs + 1 := by
  simp only [Computation.cost, zscaleValue_additions, zscaleValue_multiplications,
    Nat.add_zero]
  exact Nat.add_le_add_left (zscaleValue_negations_le n x) _

/-- Finite sequential execution of a linear combination.  A zero initial
accumulator and one addition per listed term give a simple uniform bound. -/
def linearCombinationList {I : Type*} (c : I → ℤ) (x : I → R) :
    List I → Computation R
  | [] => Computation.zero
  | i :: is => Computation.add (zscaleValue (c i) (x i))
      (linearCombinationList c x is)

@[simp] theorem linearCombinationList_value {I : Type*}
    (c : I → ℤ) (x : I → R) (is : List I) :
    (linearCombinationList c x is).value = (is.map fun i => c i • x i).sum := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [linearCombinationList, ih]

@[simp] theorem linearCombinationList_multiplications {I : Type*}
    (c : I → ℤ) (x : I → R) (is : List I) :
    (linearCombinationList c x is).multiplications = 0 := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [linearCombinationList, Computation.add, ih]

theorem linearCombinationList_cost_le {I : Type*}
    (c : I → ℤ) (x : I → R) (is : List I) :
    (linearCombinationList c x is).cost ≤
      (is.map fun i => (c i).natAbs + 2).sum := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [linearCombinationList, Computation.add_cost, List.map_cons,
      List.sum_cons]
    have hi := zscaleValue_cost_le (c i) (x i)
    omega

/-- Execute every coefficient once using the enumeration supplied by `Fintype`.
All inputs are already available, so their production costs are recorded by the
caller, once, before invoking this local linear combination. -/
noncomputable def linearCombination {I : Type*} [Fintype I]
    (c : I → ℤ) (x : I → R) : Computation R :=
  linearCombinationList c x Finset.univ.toList

@[simp] theorem linearCombination_value {I : Type*} [Fintype I]
    (c : I → ℤ) (x : I → R) :
    (linearCombination c x).value = ∑ i, c i • x i := by
  classical
  simp [linearCombination]

@[simp] theorem linearCombination_multiplications {I : Type*} [Fintype I]
    (c : I → ℤ) (x : I → R) :
    (linearCombination c x).multiplications = 0 := by
  simp [linearCombination]

theorem linearCombination_cost_le {I : Type*} [Fintype I]
    (c : I → ℤ) (x : I → R) :
    (linearCombination c x).cost ≤ ∑ i, ((c i).natAbs + 2) := by
  classical
  simpa [linearCombination] using
    linearCombinationList_cost_le c x Finset.univ.toList

#print axioms zscaleValue_value
#print axioms zscaleValue_cost_le
#print axioms linearCombination_value
#print axioms linearCombination_cost_le

end Matmul.UniversalCircuit
