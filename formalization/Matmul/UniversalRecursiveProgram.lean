import Matmul.UniversalProgram
import Matmul.UniversalLinearProgram
import Matmul.UniversalRecursiveAlgorithm

/-!
# Strict arithmetic programs for recursive matrix multiplication

The witness in this file is an arithmetic syntax, not an arbitrary value with
attached counters. Its only ring operations are addition, negation and ordered
multiplication gates. Integer coefficients compile to repeated addition, and
composition stores each finite intermediate family for reuse.
-/

set_option backward.isDefEq.respectTransparency false

namespace Matmul.UniversalRecursiveProgram

open scoped BigOperators
open Matmul.IntegerBilinear Matmul.UniversalRecursion Matmul.UniversalRecursiveAlgorithm
open Matmul.UniversalProgram Matmul.UniversalLinearProgram

noncomputable section

abbrev Entry (a b t : ℕ) := Index a t × Index b t
abbrev Input (a b c t : ℕ) := Entry a b t ⊕ Entry b c t
abbrev Prepared (a b c ρ t : ℕ) := (Fin ρ × Entry a b t) ⊕ (Fin ρ × Entry b c t)
abbrev ChildOutput (a c ρ t : ℕ) := Fin ρ × Entry a c t
abbrev OutputBlocks (a c t : ℕ) := (Fin c × Fin a) × Entry a c t

variable {a b c ρ : ℕ}

/-- Arithmetic programs for all prepared left and right block entries. -/
def prepare (alg : Scheme a b c ρ) (t : ℕ) :
    Circuit (Input a b c (t + 1)) (Prepared a b c ρ t) :=
  .pair
    (linearLayer (fun p : Fin ρ × Entry a b t => alg.left p.1)
      (fun p x => Sum.inl ((x.1, p.2.1), (x.2, p.2.2))))
    (linearLayer (fun p : Fin ρ × Entry b c t => alg.right p.1)
      (fun p y => Sum.inr ((y.1, p.2.1), (y.2, p.2.2))))

/-- Select one pair of prepared rectangular inputs, preserving left and right
roles. This only chooses wires and does no ring arithmetic. -/
def childWire (s : Fin ρ) : Input a b c t → Prepared a b c ρ t
  | .inl p => .inl (s, p)
  | .inr p => .inr (s, p)

/-- Arithmetic programs for every output entry, followed by a wire permutation
that packs the outer block coordinates. -/
def reconstruct (alg : Scheme a b c ρ) (t : ℕ) :
    Circuit (ChildOutput a c ρ t) (Entry a c (t + 1)) :=
  .comp
    (linearLayer (fun p : OutputBlocks a c t => fun s => alg.output s p.1)
      (fun p s => (s, p.2)))
    (.wire (fun p => ((p.2.1, p.1.1), (p.1.2, p.2.2))))

/-- Compile the recursion into a strict finite arithmetic graph. All arithmetic
is present as primitive syntax; there is no instruction for an arbitrary ring
function, arbitrary constant, or scalar multiplication. -/
def compile (alg : Scheme a b c ρ) : (t : ℕ) → Circuit (Input a b c t) (Entry a c t)
  | 0 =>
    .comp
      (.comp (.wire (fun side : Bool => if side then
        Sum.inr (PUnit.unit, PUnit.unit) else Sum.inl (PUnit.unit, PUnit.unit))) .mul)
      (.wire (fun _ => PUnit.unit))
  | t + 1 =>
    .comp (prepare alg t)
      (.comp (.bundle (fun s : Fin ρ => .comp (.wire (childWire s)) (compile alg t)))
        (reconstruct alg t))

/-- Present the two input matrices as one available wire family. -/
def encode {R : Type*} (A : Matrix (Index a t) (Index b t) R)
    (B : Matrix (Index b t) (Index c t) R) : Input a b c t → R
  | .inl p => A p.1 p.2
  | .inr p => B p.1 p.2

variable {R : Type*} [NonUnitalRing R]

/-- Wire selection from the computed input stage gives exactly the two
rectangular matrices required by the corresponding recursive product. -/
theorem prepared_input (alg : Scheme a b c ρ) (t : ℕ)
    (A : Matrix (Index a (t + 1)) (Index b (t + 1)) R)
    (B : Matrix (Index b (t + 1)) (Index c (t + 1)) R) (s : Fin ρ) :
    (fun w => (prepare alg t).eval (encode A B) (childWire s w)) =
      encode (leftInput alg t A s) (rightInput alg t B s) := by
  funext w
  cases w with
  | inl p =>
    simp [prepare, childWire, encode, leftInput, Matrix.sum_apply,
      Matrix.smul_apply, blocks]
  | inr p =>
    simp [prepare, childWire, encode, rightInput, Matrix.sum_apply,
      Matrix.smul_apply, blocks]

/-- The strict arithmetic syntax evaluates to the recursively blocked product
algorithm. This proves compilation correctness independently of any attached
cost fields on values. -/
theorem compile_eval (alg : Scheme a b c ρ) (t : ℕ)
    (A : Matrix (Index a t) (Index b t) R) (B : Matrix (Index b t) (Index c t) R)
    (u : Index a t) (v : Index c t) :
    (compile alg t).eval (encode A B) (u, v) = multiply alg t A B u v := by
  induction t with
  | zero => simp [compile, encode, multiply]
  | succ t ih =>
    rcases u with ⟨i, u⟩
    rcases v with ⟨k, v⟩
    rw [compile, multiply]
    simp only [reconstruct, Circuit.eval_comp, Circuit.eval_bundle,
      Circuit.eval_wire, linearLayer_eval, packBlocks, Matrix.sum_apply, Matrix.smul_apply]
    apply Finset.sum_congr rfl
    intro s hs
    congr 1
    have hp : (Circuit.wire (childWire s)).eval ((prepare alg t).eval (encode A B)) =
        encode (leftInput alg t A s) (rightInput alg t B s) :=
      prepared_input alg t A B s
    exact (congrArg (fun input => (compile alg t).eval input (u, v)) hp).trans
      (ih (leftInput alg t A s) (rightInput alg t B s) u v)

/-- A certified integer tensor scheme compiles to an actual division-free
arithmetic program correct over every nonunital ring. -/
theorem compile_correct (alg : Scheme a b c ρ)
    (h : alg.tensor = matrixTensor a b c) (t : ℕ)
    (A : Matrix (Index a t) (Index b t) R) (B : Matrix (Index b t) (Index c t) R)
    (u : Index a t) (v : Index c t) :
    (compile alg t).eval (encode A B) (u, v) = (A * B) u v := by
  rw [compile_eval, multiply_correct alg h]

/-- The input-stage gate count is the sum of the two actual linear-layer
counts; the coefficient weights are fixed integers independent of the ring. -/
theorem prepare_cost_le (alg : Scheme a b c ρ) (t : ℕ) :
    (prepare alg t).cost ≤ (a * b) ^ t * leftWeight alg +
      (b * c) ^ t * rightWeight alg := by
  have hleft := linearLayer_prod_cost_le (alg.left)
    (fun (p : Fin ρ × Entry a b t) x =>
      (Sum.inl ((x.1, p.2.1), (x.2, p.2.2)) : Input a b c (t + 1)))
  have hright := linearLayer_prod_cost_le (alg.right)
    (fun (p : Fin ρ × Entry b c t) y =>
      (Sum.inr ((y.1, p.2.1), (y.2, p.2.2)) : Input a b c (t + 1)))
  simpa only [prepare, Circuit.pair_cost, Entry, Fintype.card_prod, card_index,
    mul_pow, leftWeight, rightWeight, coefficientWeight] using Nat.add_le_add hleft hright


/-- The output stage also compiles entirely to charged additions and negations. -/
theorem reconstruct_cost_le (alg : Scheme a b c ρ) (t : ℕ) :
    (reconstruct alg t).cost ≤ (a * c) ^ t * outputWeight alg := by
  have h := linearLayer_prod_cost_le (fun z : Fin c × Fin a => fun s => alg.output s z)
    (fun (p : OutputBlocks a c t) s => (s, p.2))
  simpa only [reconstruct, Circuit.comp_cost, Circuit.wire_cost, Nat.add_zero,
    Entry, Fintype.card_prod, card_index, mul_pow, coefficientWeight,
    outputWeight] using h

/-- Every multiplication gate is a scalar leaf. Integer linear layers contain
no multiplication gates, so the syntax has exactly `ρ^t` multiplication gates. -/
theorem compile_multiplications (alg : Scheme a b c ρ) (t : ℕ) :
    (compile alg t).multiplications = ρ ^ t := by
  induction t with
  | zero => simp [compile]
  | succ t ih =>
    simp [compile, prepare, reconstruct, ih, pow_succ, Nat.mul_comm]

/-- The strict program gate count satisfies the same deterministic recurrence
as the counted evaluation, with coefficient additions fully charged. -/
theorem compile_cost_le_work (alg : Scheme a b c ρ) (t : ℕ) :
    (compile alg t).cost ≤ Matmul.RecursiveCost.work 1 (linearWeight alg) ρ
      (Matmul.RecursiveCost.blockVolume a b c) t := by
  induction t with
  | zero => simp [compile]
  | succ t ih =>
    let d := Matmul.RecursiveCost.blockVolume a b c
    have hvol := Matmul.RecursiveCost.blockVolume_bounds a b c
    have hl : (a * b) ^ t * leftWeight alg ≤ d ^ t * leftWeight alg :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hvol.1 t)
    have hr : (b * c) ^ t * rightWeight alg ≤ d ^ t * rightWeight alg :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hvol.2.1 t)
    have ho : (a * c) ^ t * outputWeight alg ≤ d ^ t * outputWeight alg :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hvol.2.2 t)
    have hprep : (prepare alg t).cost ≤
        d ^ t * leftWeight alg + d ^ t * rightWeight alg :=
      (prepare_cost_le alg t).trans (Nat.add_le_add hl hr)
    have hout : (reconstruct alg t).cost ≤ d ^ t * outputWeight alg :=
      (reconstruct_cost_le alg t).trans ho
    have hc : (∑ _s : Fin ρ, (compile alg t).cost) ≤
        ρ * Matmul.RecursiveCost.work 1 (linearWeight alg) ρ d t := by
      simpa using Nat.mul_le_mul_left ρ ih
    rw [compile]
    simp only [Circuit.comp_cost, Circuit.bundle_cost, Circuit.wire_cost,
      Nat.zero_add, Matmul.RecursiveCost.work_succ]
    calc
      (prepare alg t).cost + ((∑ _s : Fin ρ, (compile alg t).cost) +
          (reconstruct alg t).cost) ≤
          (d ^ t * leftWeight alg + d ^ t * rightWeight alg) +
            (ρ * Matmul.RecursiveCost.work 1 (linearWeight alg) ρ d t +
              d ^ t * outputWeight alg) :=
        Nat.add_le_add hprep (Nat.add_le_add hc hout)
      _ = ρ * Matmul.RecursiveCost.work 1 (linearWeight alg) ρ d t +
          linearWeight alg * d ^ t := by simp only [linearWeight]; ring

/-- Concrete operation bound for the strict program, including the critical
case in which recursive branching equals the largest block volume. -/
theorem compile_cost_bound (alg : Scheme a b c ρ) (hρ : 1 ≤ ρ)
    (hvolume : Matmul.RecursiveCost.blockVolume a b c ≤ ρ) (t : ℕ) :
    (compile alg t).cost ≤ (1 + linearWeight alg) * (t + 1) * ρ ^ t :=
  (compile_cost_le_work alg t).trans
    (Matmul.RecursiveCost.work_bound 1 (linearWeight alg) ρ
      (Matmul.RecursiveCost.blockVolume a b c) hρ hvolume t)

open Filter

/-- Arbitrarily small positive exponent slack absorbs the actual arithmetic
syntax gate count at exact base-power sizes. -/
theorem compile_eventually_rpow (alg : Scheme a b c ρ) (hρ : 1 ≤ ρ)
    (hvolume : Matmul.RecursiveCost.blockVolume a b c ≤ ρ)
    (q : ℕ) (hq : 1 < q) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℕ in atTop, ((compile alg t).cost : ℝ) ≤
      ((q : ℝ) ^ t) ^ (Real.log (ρ : ℝ) / Real.log (q : ℝ) + ε) := by
  filter_upwards [Matmul.RecursiveCost.work_eventually_rpow
    1 (linearWeight alg) ρ (Matmul.RecursiveCost.blockVolume a b c)
      q hρ hvolume hq ε hε] with t ht
  have hc : ((compile alg t).cost : ℝ) ≤
      (Matmul.RecursiveCost.work 1 (linearWeight alg) ρ
        (Matmul.RecursiveCost.blockVolume a b c) t : ℝ) := by
    exact_mod_cast compile_cost_le_work alg t
  exact hc.trans ht

/-- At logarithmic padding depth the actual syntax gate count has the same
rank-ratio exponent with every positive slack. -/
theorem compile_padded_eventually_rpow (alg : Scheme a b c ρ) (hρ : 1 ≤ ρ)
    (hvolume : Matmul.RecursiveCost.blockVolume a b c ≤ ρ)
    (q : ℕ) (hq : 1 < q) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ((compile alg (Nat.log q n + 1)).cost : ℝ) ≤
      (q : ℝ) ^ (Real.log (ρ : ℝ) / Real.log (q : ℝ) + ε) *
        (n : ℝ) ^ (Real.log (ρ : ℝ) / Real.log (q : ℝ) + ε) := by
  filter_upwards [Matmul.RecursiveCost.paddedWork_eventually_rpow
    1 (linearWeight alg) ρ (Matmul.RecursiveCost.blockVolume a b c)
      q hρ hvolume hq ε hε] with n hn
  have hc : ((compile alg (Nat.log q n + 1)).cost : ℝ) ≤
      (Matmul.RecursiveCost.paddedWork 1 (linearWeight alg) ρ
        (Matmul.RecursiveCost.blockVolume a b c) q n : ℝ) := by
    exact_mod_cast compile_cost_le_work alg (Nat.log q n + 1)
  exact hc.trans hn

#print axioms compile_correct
#print axioms compile_multiplications
#print axioms compile_cost_le_work
#print axioms compile_cost_bound
#print axioms compile_eventually_rpow
#print axioms compile_padded_eventually_rpow

end
end Matmul.UniversalRecursiveProgram
