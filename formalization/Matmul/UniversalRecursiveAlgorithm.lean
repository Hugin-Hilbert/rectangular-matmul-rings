import Matmul.UniversalCircuit
import Matmul.UniversalRecursionValues
import Matmul.RecursiveCost

/-!
# A counted recursive algorithm over every ring

All integer coefficients are executed using repeated additions and at most
one negation; there is no unit-cost scalar multiplication primitive. At each
level the left and right linear combinations are computed once, each recursive
product is computed once, and each output linear combination is computed once.
The resulting counts record actual additions, negations, and multiplications.
-/

set_option backward.isDefEq.respectTransparency false

namespace Matmul.UniversalRecursiveAlgorithm

open scoped BigOperators
open Matmul.IntegerBilinear Matmul.UniversalCircuit Matmul.UniversalRecursion

noncomputable section

/-- Integer linear-combination cost per output entry, including the term's
possible negation and its addition to the accumulator. -/
def coefficientWeight {I : Type*} [Fintype I] (coeff : I → ℤ) : ℕ :=
  ∑ i, ((coeff i).natAbs + 2)

/-- Compute a linear combination entry by entry, charging every addition and
negation used to execute the integer coefficients. Existing block entries are
reused as inputs, and their production costs belong to earlier stages. -/
def matrixLinearCombination {I u v R : Type*} [Fintype I] [Fintype u] [Fintype v]
    [NonUnitalRing R] (coeff : I → ℤ) (A : I → Matrix u v R) :
    Matmul.UniversalCircuit.Computation (Matrix u v R) :=
  Matmul.UniversalCircuit.Computation.map (fun f => Matrix.of (fun i j => f (i, j)))
    (Matmul.UniversalCircuit.Computation.collect (fun p : u × v => linearCombination coeff (fun i => A i p.1 p.2)))

@[simp] theorem matrixLinearCombination_value
    {I u v R : Type*} [Fintype I] [Fintype u] [Fintype v] [NonUnitalRing R]
    (coeff : I → ℤ) (A : I → Matrix u v R) :
    (matrixLinearCombination coeff A).value = ∑ i, coeff i • A i := by
  ext u v
  simp [matrixLinearCombination, Matmul.UniversalCircuit.Computation.map_value,
    Matmul.UniversalCircuit.Computation.collect_value, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply]

@[simp] theorem matrixLinearCombination_multiplications
    {I u v R : Type*} [Fintype I] [Fintype u] [Fintype v] [NonUnitalRing R]
    (coeff : I → ℤ) (A : I → Matrix u v R) :
    (matrixLinearCombination coeff A).multiplications = 0 := by
  simp [matrixLinearCombination, Matmul.UniversalCircuit.Computation.map, Matmul.UniversalCircuit.Computation.collect]

/-- The cost of the local computation is bounded by one fixed coefficient
weight times its number of matrix entries. -/
theorem matrixLinearCombination_cost_le
    {I u v R : Type*} [Fintype I] [Fintype u] [Fintype v] [NonUnitalRing R]
    (coeff : I → ℤ) (A : I → Matrix u v R) :
    (matrixLinearCombination coeff A).cost ≤
      Fintype.card u * Fintype.card v * coefficientWeight coeff := by
  unfold matrixLinearCombination
  rw [Matmul.UniversalCircuit.Computation.map_cost, Matmul.UniversalCircuit.Computation.collect_cost]
  calc
    (∑ p : u × v, (linearCombination coeff (fun i => A i p.1 p.2)).cost) ≤
        ∑ _p : u × v, coefficientWeight coeff := by
      apply Finset.sum_le_sum
      intro p hp
      simpa only [coefficientWeight] using linearCombination_cost_le coeff (fun i => A i p.1 p.2)
    _ = Fintype.card u * Fintype.card v * coefficientWeight coeff := by
      simp [Fintype.card_prod]

/-- Sequential composition after a pre whose result is already available.
Only packaging is free; all arithmetic is recorded by the two computations. -/
def after {α β : Type*} (pre : Matmul.UniversalCircuit.Computation α) (result : Matmul.UniversalCircuit.Computation β) :
    Matmul.UniversalCircuit.Computation β := Matmul.UniversalCircuit.Computation.combine (fun _ y => y) pre result

@[simp] theorem after_value {α β : Type*} (pre : Matmul.UniversalCircuit.Computation α)
    (result : Matmul.UniversalCircuit.Computation β) : (after pre result).value = result.value := rfl

@[simp] theorem after_cost {α β : Type*} (pre : Matmul.UniversalCircuit.Computation α)
    (result : Matmul.UniversalCircuit.Computation β) : (after pre result).cost = pre.cost + result.cost := by
  exact Matmul.UniversalCircuit.Computation.combine_cost _ _ _

@[simp] theorem after_multiplications {α β : Type*} (pre : Matmul.UniversalCircuit.Computation α)
    (result : Matmul.UniversalCircuit.Computation β) :
    (after pre result).multiplications = pre.multiplications + result.multiplications := rfl

variable {R : Type*} [NonUnitalRing R] {a b c ρ : ℕ}

abbrev Scheme (a b c ρ : ℕ) :=
  Algorithm (Fin a × Fin b) (Fin b × Fin c) (Fin c × Fin a) ρ

/-- Compute one recursive left input with its arithmetic counts. -/
def leftComputation (alg : Scheme a b c ρ) (t : ℕ)
    (A : Matrix (Index a (t + 1)) (Index b (t + 1)) R) (s : Fin ρ) :
    Matmul.UniversalCircuit.Computation (Matrix (Index a t) (Index b t) R) :=
  matrixLinearCombination (alg.left s) (fun x => blocks t A x.1 x.2)

/-- Compute the corresponding recursive right input. -/
def rightComputation (alg : Scheme a b c ρ) (t : ℕ)
    (B : Matrix (Index b (t + 1)) (Index c (t + 1)) R) (s : Fin ρ) :
    Matmul.UniversalCircuit.Computation (Matrix (Index b t) (Index c t) R) :=
  matrixLinearCombination (alg.right s) (fun y => blocks t B y.1 y.2)

@[simp] theorem leftComputation_value (alg : Scheme a b c ρ) (t : ℕ)
    (A : Matrix (Index a (t + 1)) (Index b (t + 1)) R) (s : Fin ρ) :
    (leftComputation alg t A s).value = leftInput alg t A s := by
  simp [leftComputation, leftInput]

@[simp] theorem rightComputation_value (alg : Scheme a b c ρ) (t : ℕ)
    (B : Matrix (Index b (t + 1)) (Index c (t + 1)) R) (s : Fin ρ) :
    (rightComputation alg t B s).value = rightInput alg t B s := by
  simp [rightComputation, rightInput]

/-- The deterministic counted evaluator. Its schedule shares every computed
left input, right input, and child result. Integer linear combinations are
performed with the counted arithmetic primitives above. -/
def run (alg : Scheme a b c ρ) :
    (t : ℕ) → Matrix (Index a t) (Index b t) R →
      Matrix (Index b t) (Index c t) R → Matmul.UniversalCircuit.Computation (Matrix (Index a t) (Index c t) R)
  | 0, A, B =>
      Matmul.UniversalCircuit.Computation.map (fun x => Matrix.of (fun _ _ => x))
        (Matmul.UniversalCircuit.Computation.mul (Matmul.UniversalCircuit.Computation.pure (A PUnit.unit PUnit.unit))
          (Matmul.UniversalCircuit.Computation.pure (B PUnit.unit PUnit.unit)))
  | t + 1, A, B =>
      let left := Matmul.UniversalCircuit.Computation.collect (leftComputation alg t A)
      let right := Matmul.UniversalCircuit.Computation.collect (rightComputation alg t B)
      let children := Matmul.UniversalCircuit.Computation.collect
        (fun s => run alg t (left.value s) (right.value s))
      let outputs := Matmul.UniversalCircuit.Computation.collect (fun z : Fin c × Fin a =>
        matrixLinearCombination (fun s => alg.output s z) children.value)
      after left (after right (after children
        (Matmul.UniversalCircuit.Computation.map (fun out => Matrix.of (fun (i : Index a (t + 1)) (k : Index c (t + 1)) =>
          out (k.1, i.1) i.2 k.2)) outputs)))

/-- The counted computation has the same value as the recursive block
algorithm, while implementing each coefficient using explicit arithmetic. -/
theorem run_value (alg : Scheme a b c ρ) (t : ℕ)
    (A : Matrix (Index a t) (Index b t) R) (B : Matrix (Index b t) (Index c t) R) :
    (run alg t A B).value = multiply alg t A B := by
  induction t with
  | zero => rfl
  | succ t ih =>
    ext ⟨i, u⟩ ⟨k, v⟩
    simp only [run, after_value, Matmul.UniversalCircuit.Computation.map_value,
      Matmul.UniversalCircuit.Computation.collect_value, Matrix.of_apply]
    rw [matrixLinearCombination_value]
    simp only [Matmul.UniversalCircuit.Computation.collect_value, leftComputation_value,
      rightComputation_value, ih, multiply, packBlocks]


/-- The counted computation returns the actual ordered matrix product over
any noncommutative, nonunital ring. -/
theorem run_correct (alg : Scheme a b c ρ) (h : alg.tensor = matrixTensor a b c)
    (t : ℕ) (A : Matrix (Index a t) (Index b t) R)
    (B : Matrix (Index b t) (Index c t) R) :
    (run alg t A B).value = A * B := by
  rw [run_value, multiply_correct alg h]

/-- Fixed coefficient costs of the two input stages and the output stage. -/
def leftWeight (alg : Scheme a b c ρ) : ℕ := ∑ s, coefficientWeight (alg.left s)
def rightWeight (alg : Scheme a b c ρ) : ℕ := ∑ s, coefficientWeight (alg.right s)
def outputWeight (alg : Scheme a b c ρ) : ℕ :=
  ∑ z : Fin c × Fin a, coefficientWeight (fun s => alg.output s z)
def linearWeight (alg : Scheme a b c ρ) : ℕ :=
  leftWeight alg + rightWeight alg + outputWeight alg

/-- Every scalar multiplication is a depth-zero leaf, and each non-leaf has
exactly `ρ` children. There are no multiplications in the coefficient stages. -/
theorem run_multiplications (alg : Scheme a b c ρ) (t : ℕ)
    (A : Matrix (Index a t) (Index b t) R) (B : Matrix (Index b t) (Index c t) R) :
    (run alg t A B).multiplications = ρ ^ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp [run, Matmul.UniversalCircuit.Computation.map, Matmul.UniversalCircuit.Computation.collect, after, Matmul.UniversalCircuit.Computation.combine,
      leftComputation, rightComputation, matrixLinearCombination_multiplications, ih,
      pow_succ, Nat.mul_comm]

/-- Sum the actual costs of all left input blocks. -/
theorem left_stage_cost_le (alg : Scheme a b c ρ) (t : ℕ)
    (A : Matrix (Index a (t + 1)) (Index b (t + 1)) R) :
    (Matmul.UniversalCircuit.Computation.collect (leftComputation alg t A)).cost ≤
      (a * b) ^ t * leftWeight alg := by
  rw [Matmul.UniversalCircuit.Computation.collect_cost]
  calc
    (∑ s, (leftComputation alg t A s).cost) ≤
        ∑ s, (a * b) ^ t * coefficientWeight (alg.left s) := by
      apply Finset.sum_le_sum
      intro s hs
      simpa only [leftComputation, card_index, mul_pow] using
        matrixLinearCombination_cost_le (alg.left s) (fun x => blocks t A x.1 x.2)
    _ = (a * b) ^ t * leftWeight alg := by rw [leftWeight, Finset.mul_sum]

/-- Sum the actual costs of all right input blocks. -/
theorem right_stage_cost_le (alg : Scheme a b c ρ) (t : ℕ)
    (B : Matrix (Index b (t + 1)) (Index c (t + 1)) R) :
    (Matmul.UniversalCircuit.Computation.collect (rightComputation alg t B)).cost ≤
      (b * c) ^ t * rightWeight alg := by
  rw [Matmul.UniversalCircuit.Computation.collect_cost]
  calc
    (∑ s, (rightComputation alg t B s).cost) ≤
        ∑ s, (b * c) ^ t * coefficientWeight (alg.right s) := by
      apply Finset.sum_le_sum
      intro s hs
      simpa only [rightComputation, card_index, mul_pow] using
        matrixLinearCombination_cost_le (alg.right s) (fun y => blocks t B y.1 y.2)
    _ = (b * c) ^ t * rightWeight alg := by rw [rightWeight, Finset.mul_sum]

/-- Sum the actual costs of all output blocks, with the child products reused
as already available inputs. -/
theorem output_stage_cost_le (alg : Scheme a b c ρ) (t : ℕ)
    (children : Fin ρ → Matrix (Index a t) (Index c t) R) :
    (Matmul.UniversalCircuit.Computation.collect (fun z : Fin c × Fin a =>
      matrixLinearCombination (fun s => alg.output s z) children)).cost ≤
        (a * c) ^ t * outputWeight alg := by
  rw [Matmul.UniversalCircuit.Computation.collect_cost]
  calc
    (∑ z : Fin c × Fin a,
      (matrixLinearCombination (fun s => alg.output s z) children).cost) ≤
        ∑ z : Fin c × Fin a,
          (a * c) ^ t * coefficientWeight (fun s => alg.output s z) := by
      apply Finset.sum_le_sum
      intro z hz
      simpa only [card_index, mul_pow] using
        matrixLinearCombination_cost_le (fun s => alg.output s z) children
    _ = (a * c) ^ t * outputWeight alg := by rw [outputWeight, Finset.mul_sum]

/-- The actual recursive operation counts obey the deterministic work
envelope. This includes every repeated addition used for integer coefficients,
all possible negations, and every multiplication at the recursive leaves. -/
theorem run_cost_le_work (alg : Scheme a b c ρ) (t : ℕ)
    (A : Matrix (Index a t) (Index b t) R) (B : Matrix (Index b t) (Index c t) R) :
    (run alg t A B).cost ≤
      Matmul.RecursiveCost.work 1 (linearWeight alg) ρ
        (Matmul.RecursiveCost.blockVolume a b c) t := by
  induction t with
  | zero =>
    simp [run, Matmul.UniversalCircuit.Computation.map_cost,
      Matmul.UniversalCircuit.Computation.mul_cost]
  | succ t ih =>
    let left := Matmul.UniversalCircuit.Computation.collect (leftComputation alg t A)
    let right := Matmul.UniversalCircuit.Computation.collect (rightComputation alg t B)
    let children := Matmul.UniversalCircuit.Computation.collect
      (fun s => run alg t (left.value s) (right.value s))
    let outputs := Matmul.UniversalCircuit.Computation.collect (fun z : Fin c × Fin a =>
      matrixLinearCombination (fun s => alg.output s z) children.value)
    let d := Matmul.RecursiveCost.blockVolume a b c
    have hvol := Matmul.RecursiveCost.blockVolume_bounds a b c
    have hleft : left.cost ≤ leftWeight alg * d ^ t := by
      apply (left_stage_cost_le alg t A).trans
      calc
        (a * b) ^ t * leftWeight alg ≤ d ^ t * leftWeight alg :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hvol.1 t)
        _ = leftWeight alg * d ^ t := Nat.mul_comm _ _
    have hright : right.cost ≤ rightWeight alg * d ^ t := by
      apply (right_stage_cost_le alg t B).trans
      calc
        (b * c) ^ t * rightWeight alg ≤ d ^ t * rightWeight alg :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hvol.2.1 t)
        _ = rightWeight alg * d ^ t := Nat.mul_comm _ _
    have hout : outputs.cost ≤ outputWeight alg * d ^ t := by
      apply (output_stage_cost_le alg t children.value).trans
      calc
        (a * c) ^ t * outputWeight alg ≤ d ^ t * outputWeight alg :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hvol.2.2 t)
        _ = outputWeight alg * d ^ t := Nat.mul_comm _ _
    have hchildren : children.cost ≤
        ρ * Matmul.RecursiveCost.work 1 (linearWeight alg) ρ d t := by
      change (Matmul.UniversalCircuit.Computation.collect
        (fun s => run alg t (left.value s) (right.value s))).cost ≤ _
      rw [Matmul.UniversalCircuit.Computation.collect_cost]
      calc
        (∑ s, (run alg t (left.value s) (right.value s)).cost) ≤
            ∑ _s : Fin ρ, Matmul.RecursiveCost.work 1 (linearWeight alg) ρ d t := by
          apply Finset.sum_le_sum
          intro s hs
          exact ih (left.value s) (right.value s)
        _ = ρ * Matmul.RecursiveCost.work 1 (linearWeight alg) ρ d t := by simp
    change (after left (after right (after children
      (Matmul.UniversalCircuit.Computation.map
        (fun out => Matrix.of (fun (i : Index a (t + 1)) (k : Index c (t + 1)) =>
          out (k.1, i.1) i.2 k.2)) outputs)))).cost ≤ _
    simp only [after_cost, Matmul.UniversalCircuit.Computation.map_cost,
      Matmul.RecursiveCost.work_succ]
    change left.cost + (right.cost + (children.cost + outputs.cost)) ≤
      ρ * Matmul.RecursiveCost.work 1 (linearWeight alg) ρ d t + linearWeight alg * d ^ t
    calc
      left.cost + (right.cost + (children.cost + outputs.cost)) ≤
          leftWeight alg * d ^ t + (rightWeight alg * d ^ t +
            (ρ * Matmul.RecursiveCost.work 1 (linearWeight alg) ρ d t +
              outputWeight alg * d ^ t)) :=
        Nat.add_le_add hleft (Nat.add_le_add hright (Nat.add_le_add hchildren hout))
      _ = ρ * Matmul.RecursiveCost.work 1 (linearWeight alg) ρ d t +
          linearWeight alg * d ^ t := by
        simp only [linearWeight]
        ring

/-- Domination of input and output block volumes yields the concrete operation
bound for the correctly counted recursive algorithm, including `d = ρ`. -/
theorem run_cost_bound (alg : Scheme a b c ρ) (hρ : 1 ≤ ρ)
    (hvolume : Matmul.RecursiveCost.blockVolume a b c ≤ ρ) (t : ℕ)
    (A : Matrix (Index a t) (Index b t) R) (B : Matrix (Index b t) (Index c t) R) :
    (run alg t A B).cost ≤ (1 + linearWeight alg) * (t + 1) * ρ ^ t :=
  (run_cost_le_work alg t A B).trans
    (Matmul.RecursiveCost.work_bound 1 (linearWeight alg) ρ
      (Matmul.RecursiveCost.blockVolume a b c) hρ hvolume t)

open Filter

universe u

/-- Every positive exponent slack absorbs the actual recursive operation
counts at the exact sizes `q^t`. The threshold is uniform in the ring and both
input matrices because the operation bound depends only on the fixed integer
coefficients and block shape. -/
theorem run_eventually_rpow (alg : Scheme a b c ρ) (hρ : 1 ≤ ρ)
    (hvolume : Matmul.RecursiveCost.blockVolume a b c ≤ ρ)
    (q : ℕ) (hq : 1 < q) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℕ in atTop, ∀ (S : Type u) [NonUnitalRing S]
      (A : Matrix (Index a t) (Index b t) S) (B : Matrix (Index b t) (Index c t) S),
      (run alg t A B).cost ≤
        ((q : ℝ) ^ t) ^ (Real.log (ρ : ℝ) / Real.log (q : ℝ) + ε) := by
  filter_upwards [Matmul.RecursiveCost.work_eventually_rpow
    1 (linearWeight alg) ρ (Matmul.RecursiveCost.blockVolume a b c)
      q hρ hvolume hq ε hε] with t ht
  intro S inst A B
  have hc : ((run alg t A B).cost : ℝ) ≤
      (Matmul.RecursiveCost.work 1 (linearWeight alg) ρ
        (Matmul.RecursiveCost.blockVolume a b c) t : ℝ) := by
    exact_mod_cast run_cost_le_work alg t A B
  exact hc.trans ht

/-- The same bound at logarithmic padding depth, uniformly over all target
rings and all input matrices of the padded rectangular shape. -/
theorem run_padded_eventually_rpow (alg : Scheme a b c ρ) (hρ : 1 ≤ ρ)
    (hvolume : Matmul.RecursiveCost.blockVolume a b c ≤ ρ)
    (q : ℕ) (hq : 1 < q) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (S : Type u) [NonUnitalRing S]
      (A : Matrix (Index a (Nat.log q n + 1)) (Index b (Nat.log q n + 1)) S)
      (B : Matrix (Index b (Nat.log q n + 1)) (Index c (Nat.log q n + 1)) S),
      (run alg (Nat.log q n + 1) A B).cost ≤
        (q : ℝ) ^ (Real.log (ρ : ℝ) / Real.log (q : ℝ) + ε) *
          (n : ℝ) ^ (Real.log (ρ : ℝ) / Real.log (q : ℝ) + ε) := by
  filter_upwards [Matmul.RecursiveCost.paddedWork_eventually_rpow
    1 (linearWeight alg) ρ (Matmul.RecursiveCost.blockVolume a b c)
      q hρ hvolume hq ε hε] with n hn
  intro S inst A B
  have hc : ((run alg (Nat.log q n + 1) A B).cost : ℝ) ≤
      (Matmul.RecursiveCost.paddedWork 1 (linearWeight alg) ρ
        (Matmul.RecursiveCost.blockVolume a b c) q n : ℝ) := by
    exact_mod_cast run_cost_le_work alg (Nat.log q n + 1) A B
  exact hc.trans hn

#print axioms run_correct
#print axioms run_multiplications
#print axioms run_cost_le_work
#print axioms run_cost_bound
#print axioms run_eventually_rpow
#print axioms run_padded_eventually_rpow

end

end Matmul.UniversalRecursiveAlgorithm
