import Matmul.UniversalProgram

/-!
# Compiling a layer of integer linear combinations

The indices selected by `source` are wires into an already available input
family. Every scalar coefficient is implemented by the arithmetic syntax in
`UniversalProgram`; no ring-valued function is a free instruction.
-/

namespace Matmul.UniversalLinearProgram

open scoped BigOperators
open Matmul.UniversalProgram

/-- A finite layer of integer linear combinations. The output's singleton
coordinate is discarded by a wire after each branch has been evaluated. -/
noncomputable def linearLayer {I J C : Type} [Fintype J] [Fintype C]
    (coeff : J → C → ℤ) (source : J → C → I) : Circuit I J :=
  .comp (.bundle (fun j => .comp (.wire (source j)) (linearCombination (coeff j))))
    (.wire (fun j => (j, PUnit.unit)))

@[simp] theorem linearLayer_eval {I J C : Type} [Fintype J] [Fintype C]
    {R : Type*} [NonUnitalRing R]
    (coeff : J → C → ℤ) (source : J → C → I) (input : I → R) (j : J) :
    (linearLayer coeff source).eval input j =
      ∑ c, coeff j c • input (source j c) := by
  simp [linearLayer]

/-- A uniform arithmetic-gate bound for the entire layer. -/
theorem linearLayer_cost_le {I J C : Type} [Fintype J] [Fintype C]
    (coeff : J → C → ℤ) (source : J → C → I) :
    (linearLayer coeff source).cost ≤ ∑ j, ∑ c, ((coeff j c).natAbs + 2) := by
  simp only [linearLayer, Circuit.comp_cost, Circuit.bundle_cost, Circuit.wire_cost,
    Nat.zero_add, Nat.add_zero]
  apply Finset.sum_le_sum
  intro j hj
  exact linearCombination_cost_le (coeff j)

@[simp] theorem linearLayer_multiplications {I J C : Type} [Fintype J] [Fintype C]
    (coeff : J → C → ℤ) (source : J → C → I) :
    (linearLayer coeff source).multiplications = 0 := by
  simp [linearLayer]

/-- If the same coefficient list is used at every entry of each slot, the
layer cost is its coefficient weight times the number of entries. -/
theorem linearLayer_prod_cost_le {I Slots Entry C : Type}
    [Fintype Slots] [Fintype Entry] [Fintype C]
    (coeff : Slots → C → ℤ) (source : Slots × Entry → C → I) :
    (linearLayer (fun p : Slots × Entry => coeff p.1) source).cost ≤
      Fintype.card Entry * (∑ s, ∑ c, ((coeff s c).natAbs + 2)) := by
  calc
    (linearLayer (fun p : Slots × Entry => coeff p.1) source).cost ≤
        ∑ p : Slots × Entry, ∑ c, ((coeff p.1 c).natAbs + 2) :=
      linearLayer_cost_le _ _
    _ = Fintype.card Entry * (∑ s, ∑ c, ((coeff s c).natAbs + 2)) := by
      simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, smul_eq_mul]
      rw [← Finset.mul_sum]

#print axioms linearLayer_eval
#print axioms linearLayer_cost_le
#print axioms linearLayer_prod_cost_le

end Matmul.UniversalLinearProgram
