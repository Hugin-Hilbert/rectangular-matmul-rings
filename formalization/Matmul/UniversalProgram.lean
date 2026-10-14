import Matmul.UniversalCircuit

/-!
# Ring programs with an explicit arithmetic syntax

Every ring operation is represented by an addition, negation, or multiplication
gate. Wires may only select inputs; the other free operations form zero outputs
and package or look up previously computed outputs. In particular the syntax
has no arbitrary map on ring values and no scalar-multiplication instruction.
-/

namespace Matmul.UniversalProgram

open scoped BigOperators

/-- A finite layered arithmetic graph. Composition shares its entire finite
intermediate family. Parallel branches have independently charged gates and
share their already available input family. -/
inductive Circuit : Type → Type → Type 1 where
  | wire {I O : Type} (select : O → I) : Circuit I O
  | zero {I O : Type} : Circuit I O
  | add : Circuit Bool PUnit
  | neg : Circuit PUnit PUnit
  | mul : Circuit Bool PUnit
  | comp {I J O : Type} [Fintype J] (first : Circuit I J)
      (second : Circuit J O) : Circuit I O
  | pair {I O P : Type} (left : Circuit I O) (right : Circuit I P) :
      Circuit I (O ⊕ P)
  | bundle {I J O : Type} [Fintype J] (branches : J → Circuit I O) :
      Circuit I (J × O)

/-- An eager array of values, presented through its original finite index.
The vector is constructed once before the lookup function is returned. -/
noncomputable def materialize {I : Type} {α : Type*} [Fintype I]
    (f : I → α) : I → α :=
  let values := Vector.ofFn (fun j => f ((Fintype.equivFin I).symm j))
  fun i => values[((Fintype.equivFin I) i).val]

@[simp] theorem materialize_apply {I : Type} {α : Type*} [Fintype I]
    (f : I → α) (i : I) : materialize f i = f i := by
  simp [materialize]

@[simp] theorem materialize_eq {I : Type} {α : Type*} [Fintype I]
    (f : I → α) : materialize f = f := funext (materialize_apply f)

namespace Circuit

variable {R : Type*} [NonUnitalRing R]

/-- Interpret the syntax. Each arithmetic gate computes its scalar before
returning the output function. A composition eagerly stores all intermediate
values, and a bundle eagerly evaluates and stores each branch once. -/
noncomputable def eval : {I O : Type} → Circuit I O → (I → R) → O → R
  | _, _, .wire select, input => fun o => input (select o)
  | _, _, .zero, _ => fun _ => 0
  | _, _, .add, input =>
      let value := input false + input true
      fun _ => value
  | _, _, .neg, input =>
      let value := -input PUnit.unit
      fun _ => value
  | _, _, .mul, input =>
      let value := input false * input true
      fun _ => value
  | _, _, @Circuit.comp _ J _ inst first second, input =>
      letI := inst
      let middle := materialize (I := J) (eval first input)
      eval second middle
  | _, _, .pair left right, input =>
      let leftValue := eval left input
      let rightValue := eval right input
      Sum.elim leftValue rightValue
  | _, _, @Circuit.bundle _ J _ inst branches, input =>
      letI := inst
      let outputs := materialize (fun j : J => eval (branches j) input)
      fun p => outputs p.1 p.2

/-- Number of explicit addition gates in the program. -/
def additions : {I O : Type} → Circuit I O → ℕ
  | _, _, .wire _ => 0
  | _, _, .zero => 0
  | _, _, .add => 1
  | _, _, .neg => 0
  | _, _, .mul => 0
  | _, _, @Circuit.comp _ _ _ _ first second => additions first + additions second
  | _, _, .pair left right => additions left + additions right
  | _, _, @Circuit.bundle _ J _ inst branches =>
      letI := inst
      ∑ j : J, additions (branches j)

/-- Number of explicit negation gates in the program. -/
def negations : {I O : Type} → Circuit I O → ℕ
  | _, _, .wire _ => 0
  | _, _, .zero => 0
  | _, _, .add => 0
  | _, _, .neg => 1
  | _, _, .mul => 0
  | _, _, @Circuit.comp _ _ _ _ first second => negations first + negations second
  | _, _, .pair left right => negations left + negations right
  | _, _, @Circuit.bundle _ J _ inst branches =>
      letI := inst
      ∑ j : J, negations (branches j)

/-- Number of explicit ordered multiplication gates in the program. -/
def multiplications : {I O : Type} → Circuit I O → ℕ
  | _, _, .wire _ => 0
  | _, _, .zero => 0
  | _, _, .add => 0
  | _, _, .neg => 0
  | _, _, .mul => 1
  | _, _, @Circuit.comp _ _ _ _ first second => multiplications first + multiplications second
  | _, _, .pair left right => multiplications left + multiplications right
  | _, _, @Circuit.bundle _ J _ inst branches =>
      letI := inst
      ∑ j : J, multiplications (branches j)

/-- Total arithmetic-gate cost of the syntax. -/
def cost {I O : Type} (program : Circuit I O) : ℕ :=
  program.additions + program.negations + program.multiplications

@[simp] theorem eval_wire {I O : Type} (select : O → I) (input : I → R) (o : O) :
    (wire select).eval input o = input (select o) := rfl
@[simp] theorem eval_zero {I O : Type} (input : I → R) (o : O) :
    (zero : Circuit I O).eval input o = 0 := rfl
@[simp] theorem eval_add (input : Bool → R) (o : PUnit) :
    add.eval input o = input false + input true := rfl
@[simp] theorem eval_neg (input : PUnit → R) (o : PUnit) :
    neg.eval input o = -input PUnit.unit := rfl
@[simp] theorem eval_mul (input : Bool → R) (o : PUnit) :
    mul.eval input o = input false * input true := rfl
@[simp] theorem eval_comp {I J O : Type} [Fintype J]
    (first : Circuit I J) (second : Circuit J O) (input : I → R) (o : O) :
    (comp first second).eval input o = second.eval (first.eval input) o := by
  simp [eval]
@[simp] theorem eval_pair_inl {I O P : Type} (left : Circuit I O)
    (right : Circuit I P) (input : I → R) (o : O) :
    (pair left right).eval input (.inl o) = left.eval input o := rfl
@[simp] theorem eval_pair_inr {I O P : Type} (left : Circuit I O)
    (right : Circuit I P) (input : I → R) (p : P) :
    (pair left right).eval input (.inr p) = right.eval input p := rfl
@[simp] theorem eval_bundle {I J O : Type} [Fintype J]
    (branches : J → Circuit I O) (input : I → R) (p : J × O) :
    (bundle branches).eval input p = (branches p.1).eval input p.2 := by
  simp [eval]

@[simp] theorem wire_cost {I O : Type} (select : O → I) :
    (wire select).cost = 0 := rfl
@[simp] theorem zero_cost {I O : Type} : (zero : Circuit I O).cost = 0 := rfl
@[simp] theorem add_cost : add.cost = 1 := rfl
@[simp] theorem neg_cost : neg.cost = 1 := rfl
@[simp] theorem mul_cost : mul.cost = 1 := rfl
@[simp] theorem comp_cost {I J O : Type} [Fintype J]
    (first : Circuit I J) (second : Circuit J O) :
    (comp first second).cost = first.cost + second.cost := by
  simp only [cost, additions, negations, multiplications]
  omega
@[simp] theorem pair_cost {I O P : Type} (left : Circuit I O) (right : Circuit I P) :
    (pair left right).cost = left.cost + right.cost := by
  simp only [cost, additions, negations, multiplications]
  omega
@[simp] theorem bundle_cost {I J O : Type} [Fintype J]
    (branches : J → Circuit I O) : (bundle branches).cost = ∑ j, (branches j).cost := by
  simp only [cost, additions, negations, multiplications, Finset.sum_add_distrib]

@[simp] theorem wire_multiplications {I O : Type} (select : O → I) :
    (wire select).multiplications = 0 := rfl
@[simp] theorem zero_multiplications {I O : Type} :
    (zero : Circuit I O).multiplications = 0 := rfl
@[simp] theorem add_multiplications : add.multiplications = 0 := rfl
@[simp] theorem neg_multiplications : neg.multiplications = 0 := rfl
@[simp] theorem mul_multiplications : mul.multiplications = 1 := rfl
@[simp] theorem comp_multiplications {I J O : Type} [Fintype J]
    (first : Circuit I J) (second : Circuit J O) :
    (comp first second).multiplications = first.multiplications + second.multiplications := rfl
@[simp] theorem pair_multiplications {I O P : Type}
    (left : Circuit I O) (right : Circuit I P) :
    (pair left right).multiplications = left.multiplications + right.multiplications := rfl
@[simp] theorem bundle_multiplications {I J O : Type} [Fintype J]
    (branches : J → Circuit I O) :
    (bundle branches).multiplications = ∑ j, (branches j).multiplications := rfl

/-- Sum two scalar-output programs using one explicit addition gate. -/
def sum {I : Type} (left right : Circuit I PUnit) : Circuit I PUnit :=
  comp (pair left right)
    (comp (wire (fun b : Bool => if b then Sum.inr PUnit.unit else Sum.inl PUnit.unit)) add)

/-- Negate a scalar-output program using one explicit negation gate. -/
def negative {I : Type} (program : Circuit I PUnit) : Circuit I PUnit :=
  comp program neg

@[simp] theorem eval_sum {I : Type} (left right : Circuit I PUnit)
    (input : I → R) (o : PUnit) :
    (sum left right).eval input o = left.eval input PUnit.unit + right.eval input PUnit.unit := by
  simp [sum]
@[simp] theorem eval_negative {I : Type} (program : Circuit I PUnit)
    (input : I → R) (o : PUnit) :
    (negative program).eval input o = -program.eval input PUnit.unit := by
  simp [negative]
@[simp] theorem sum_cost {I : Type} (left right : Circuit I PUnit) :
    (sum left right).cost = left.cost + right.cost + 1 := by simp [sum]
@[simp] theorem negative_cost {I : Type} (program : Circuit I PUnit) :
    (negative program).cost = program.cost + 1 := by simp [negative]
@[simp] theorem sum_multiplications {I : Type} (left right : Circuit I PUnit) :
    (sum left right).multiplications = left.multiplications + right.multiplications := by
  simp [sum, multiplications]
@[simp] theorem negative_multiplications {I : Type} (program : Circuit I PUnit) :
    (negative program).multiplications = program.multiplications := by
  simp [negative, multiplications]

end Circuit

/-- Execute a natural coefficient by adding a selected, shared input repeatedly. -/
def nscale {I : Type} (i : I) : ℕ → Circuit I PUnit
  | 0 => .zero
  | n + 1 => Circuit.sum (nscale i n) (.wire (fun _ => i))

@[simp] theorem nscale_eval {I : Type} {R : Type*} [NonUnitalRing R]
    (i : I) (n : ℕ) (input : I → R) (o : PUnit) :
    (nscale i n).eval input o = n • input i := by
  induction n with
  | zero => simp [nscale]
  | succ n ih => simp [nscale, ih, succ_nsmul]

@[simp] theorem nscale_cost {I : Type} (i : I) (n : ℕ) : (nscale i n).cost = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [nscale, ih]

@[simp] theorem nscale_multiplications {I : Type} (i : I) (n : ℕ) :
    (nscale i n).multiplications = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [nscale, ih, Circuit.multiplications]

/-- Execute an integer coefficient using only the circuit's addition and
negation gates. -/
def zscale {I : Type} (i : I) : ℤ → Circuit I PUnit
  | .ofNat n => nscale i n
  | .negSucc n => Circuit.negative (nscale i (n + 1))

@[simp] theorem zscale_eval {I : Type} {R : Type*} [NonUnitalRing R]
    (i : I) (n : ℤ) (input : I → R) (o : PUnit) :
    (zscale i n).eval input o = n • input i := by
  cases n <;> simp [zscale]

theorem zscale_cost_le {I : Type} (i : I) (n : ℤ) :
    (zscale i n).cost ≤ n.natAbs + 1 := by
  cases n <;> simp [zscale]

@[simp] theorem zscale_multiplications {I : Type} (i : I) (n : ℤ) :
    (zscale i n).multiplications = 0 := by
  cases n <;> simp [zscale]

/-- Compile a finite list of integer coefficients into arithmetic gates. -/
def linearCombinationList {I : Type} (coeff : I → ℤ) : List I → Circuit I PUnit
  | [] => .zero
  | i :: is => Circuit.sum (zscale i (coeff i)) (linearCombinationList coeff is)

@[simp] theorem linearCombinationList_eval {I : Type} {R : Type*} [NonUnitalRing R]
    (coeff : I → ℤ) (is : List I) (input : I → R) (o : PUnit) :
    (linearCombinationList coeff is).eval input o =
      (is.map fun i => coeff i • input i).sum := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [linearCombinationList, ih]

theorem linearCombinationList_cost_le {I : Type}
    (coeff : I → ℤ) (is : List I) :
    (linearCombinationList coeff is).cost ≤
      (is.map fun i => (coeff i).natAbs + 2).sum := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [linearCombinationList, Circuit.sum_cost, List.map_cons, List.sum_cons]
    have hi := zscale_cost_le i (coeff i)
    omega

@[simp] theorem linearCombinationList_multiplications {I : Type}
    (coeff : I → ℤ) (is : List I) :
    (linearCombinationList coeff is).multiplications = 0 := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [linearCombinationList, ih]

/-- Compile an integer linear combination over a finite input family. -/
noncomputable def linearCombination {I : Type} [Fintype I]
    (coeff : I → ℤ) : Circuit I PUnit :=
  linearCombinationList coeff Finset.univ.toList

@[simp] theorem linearCombination_eval {I : Type} {R : Type*} [NonUnitalRing R]
    [Fintype I] (coeff : I → ℤ) (input : I → R) (o : PUnit) :
    (linearCombination coeff).eval input o = ∑ i, coeff i • input i := by
  classical
  simp [linearCombination]

theorem linearCombination_cost_le {I : Type} [Fintype I] (coeff : I → ℤ) :
    (linearCombination coeff).cost ≤ ∑ i, ((coeff i).natAbs + 2) := by
  classical
  simpa [linearCombination] using linearCombinationList_cost_le coeff Finset.univ.toList

@[simp] theorem linearCombination_multiplications {I : Type} [Fintype I]
    (coeff : I → ℤ) : (linearCombination coeff).multiplications = 0 := by
  simp [linearCombination]

#print axioms zscale_eval
#print axioms linearCombination_eval
#print axioms linearCombination_cost_le

end Matmul.UniversalProgram
