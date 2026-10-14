import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorRestrictionComposition
import Mathlib.Logic.Equiv.Sum
import Mathlib.Logic.Equiv.Prod

namespace OAI

variable {K : Type*} [CommSemiring K]

/-!
# Exact tensor rank and its matrix multiplication exponent

The rank is the least size of an exact decomposition into simple tensors. The
exponent is the infimum of the finite matrix multiplication rank ratios from
Section 3; no attainment of this real infimum is assumed.
-/

noncomputable section

open MatrixMultiplication.Foundation


open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation

/-- Every finite coefficient tensor has a finite exact rank decomposition. -/
theorem exists_rankAtMost {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) : ∃ r : ℕ, Tensor.RankAtMost T r := by
  classical
  let a : X × Y × Z → X → K := fun p x => if x = p.1 then T p.1 p.2.1 p.2.2 else 0
  let b : X × Y × Z → Y → K := fun p y => if y = p.2.1 then 1 else 0
  let c : X × Y × Z → Z → K := fun p z => if z = p.2.2 then 1 else 0
  refine ⟨Fintype.card (X × Y × Z), ?_⟩
  have heq : T = fun x y z => ∑ p, Tensor.rankOne (a p) (b p) (c p) x y z := by
    funext x y z
    simp [a, b, c, Tensor.rankOne, Fintype.sum_prod_type, mul_ite]
  rw [heq]
  exact Tensor.rankAtMost_sum_rankOne a b c

/-- Exact rank of a finite coefficient tensor over `K`. -/
def exactRank {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) : ℕ := by
  classical
  exact Nat.find (exists_rankAtMost T)

/-- The least exact rank comes with an actual rank decomposition. -/
theorem exactRank_spec {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) : Tensor.RankAtMost T (exactRank T) := by
  classical
  exact Nat.find_spec (exists_rankAtMost T)

/-- Every exact decomposition bounds the least rank. -/
theorem exactRank_le {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    {T : Tensor K X Y Z} {r : ℕ} (h : Tensor.RankAtMost T r) : exactRank T ≤ r := by
  classical
  exact Nat.find_min' (exists_rankAtMost T) h

/-- Exact rank cannot increase under a linear restriction. -/
theorem exactRank_restrict_le {X Y Z X' Y' Z' : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z']
    (T : Tensor K X Y Z) (A : X' → X → K) (B : Y' → Y → K)
    (C : Z' → Z → K) : exactRank (Tensor.restrict A B C T) ≤ exactRank T :=
  exactRank_le ((exactRank_spec T).restrict A B C)

/-- Independent bijections of the three coordinate sets preserve exact rank. -/
theorem exactRank_reindex {X Y Z X' Y' Z' : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z']
    (T : Tensor K X Y Z) (ex : X' ≃ X) (ey : Y' ≃ Y) (ez : Z' ≃ Z) :
    exactRank (Tensor.pullback ex ey ez T) = exactRank T := by
  apply le_antisymm (exactRank_le ((exactRank_spec T).pullback ex ey ez))
  have h := exactRank_le
    ((exactRank_spec (Tensor.pullback ex ey ez T)).pullback ex.symm ey.symm ez.symm)
  have heq : Tensor.pullback ex.symm ey.symm ez.symm (Tensor.pullback ex ey ez T) = T := by
    funext x y z
    simp [Tensor.pullback]
  simpa only [heq] using h

/-- Tensor product decompositions give the usual submultiplicative rank bound. -/
theorem exactRank_product_le {X Y Z U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor K X Y Z) (S : Tensor K U V W) :
    exactRank (Tensor.product T S) ≤ exactRank T * exactRank S :=
  exactRank_le ((exactRank_spec T).product (exactRank_spec S))


/-- Base change carries every decomposition to a decomposition of the same
size, and therefore cannot increase exact tensor rank. -/
theorem exactRank_map_le {L X Y Z : Type*} [CommSemiring L]
    [Fintype X] [Fintype Y] [Fintype Z]
    (f : K →+* L) (T : Tensor K X Y Z) :
    exactRank (fun x y z => f (T x y z)) ≤ exactRank T :=
  exactRank_le ((exactRank_spec T).map f)

@[simp] theorem exactRank_zero {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] : exactRank (0 : Tensor K X Y Z) = 0 :=
  Nat.eq_zero_of_le_zero (exactRank_le Tensor.rankAtMost_zero)

/-- Rank zero means the coefficient tensor is zero, even over a semiring. -/
theorem exactRank_eq_zero_iff {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] (T : Tensor K X Y Z) :
    exactRank T = 0 ↔ T = 0 := by
  constructor
  · intro h
    have hs := exactRank_spec T
    rw [h] at hs
    rcases hs with ⟨a, b, c, hs⟩
    rw [hs]
    funext x y z
    simp
  · rintro rfl
    exact exactRank_zero

/-- Positive rank is exactly nonvanishing of the finite coefficient tensor. -/
theorem exactRank_pos_iff {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] (T : Tensor K X Y Z) :
    0 < exactRank T ↔ T ≠ 0 := by
  simpa only [Nat.pos_iff_ne_zero] using not_congr (exactRank_eq_zero_iff T)

end MatrixMultiplication.AuxiliarySeparation
end
end OAI

namespace OAI

/-!
# Binary sums of finite coefficient tensors

The coordinate types of the summands may differ.  The identities below give
the explicit changes of coordinates needed for the tensor semiring, together
with the block-diagonal restriction maps.
-/

open MatrixMultiplication.Foundation

namespace MatrixMultiplication.AuxiliarySeparation

variable {K X Y Z U V W A B C : Type*} [CommSemiring K]

/-- The binary direct sum, with each of its three block labels retained. -/
def sumTensor (T : Tensor K X Y Z) (S : Tensor K U V W) :
    Tensor K (X ⊕ U) (Y ⊕ V) (Z ⊕ W)
  | .inl x, .inl y, .inl z => T x y z
  | .inr u, .inr v, .inr w => S u v w
  | _, _, _ => 0

/-- The block-diagonal sum of two restriction matrices. -/
def sumRestriction {X' U' : Type*} (f : X' → X → K) (g : U' → U → K) :
    (X' ⊕ U') → (X ⊕ U) → K
  | .inl x', .inl x => f x' x
  | .inr u', .inr u => g u' u
  | _, _ => 0

/-- Independent restrictions of both summands give a restriction of the sum. -/
theorem sumTensor_restrict
    {X' Y' Z' U' V' W' : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W]
    (f : X' → X → K) (g : Y' → Y → K) (h : Z' → Z → K)
    (f' : U' → U → K) (g' : V' → V → K) (h' : W' → W → K)
    (T : Tensor K X Y Z) (S : Tensor K U V W) :
    Tensor.restrict (sumRestriction f f') (sumRestriction g g')
      (sumRestriction h h') (sumTensor T S) =
      sumTensor (Tensor.restrict f g h T) (Tensor.restrict f' g' h' S) := by
  funext x y z
  cases x <;> cases y <;> cases z <;>
    simp [Tensor.restrict, sumRestriction, sumTensor, Fintype.sum_sum_type]

/-- Exchanging the two blocks is a coordinate permutation. -/
theorem sumTensor_comm (T : Tensor K X Y Z) (S : Tensor K U V W) :
    Tensor.pullback (Equiv.sumComm X U) (Equiv.sumComm Y V)
      (Equiv.sumComm Z W) (sumTensor S T) = sumTensor T S := by
  funext x y z
  cases x <;> cases y <;> cases z <;> rfl

/-- Reassociating the three blocks is a coordinate permutation. -/
theorem sumTensor_assoc (T : Tensor K X Y Z) (S : Tensor K U V W)
    (R : Tensor K A B C) :
    Tensor.pullback (Equiv.sumAssoc X U A) (Equiv.sumAssoc Y V B)
      (Equiv.sumAssoc Z W C) (sumTensor T (sumTensor S R)) =
      sumTensor (sumTensor T S) R := by
  funext x y z
  rcases x with (x | x) | x <;>
    rcases y with (y | y) | y <;>
    rcases z with (z | z) | z <;> rfl

/-- An empty right summand disappears under its canonical coordinates. -/
theorem sumTensor_empty_right [IsEmpty U] [IsEmpty V] [IsEmpty W]
    (T : Tensor K X Y Z) (S : Tensor K U V W) :
    Tensor.pullback (Equiv.sumEmpty X U).symm (Equiv.sumEmpty Y V).symm
      (Equiv.sumEmpty Z W).symm (sumTensor T S) = T := by
  rfl

/-- An empty left summand disappears under its canonical coordinates. -/
theorem sumTensor_empty_left [IsEmpty X] [IsEmpty Y] [IsEmpty Z]
    (T : Tensor K X Y Z) (S : Tensor K U V W) :
    Tensor.pullback (Equiv.emptySum X U).symm (Equiv.emptySum Y V).symm
      (Equiv.emptySum Z W).symm (sumTensor T S) = S := by
  rfl

/-- Tensor product distributes over the first binary sum by coordinate
permutation. -/
theorem sumTensor_product (T : Tensor K X Y Z) (S : Tensor K U V W)
    (R : Tensor K A B C) :
    Tensor.pullback (Equiv.sumProdDistrib X U A).symm
      (Equiv.sumProdDistrib Y V B).symm (Equiv.sumProdDistrib Z W C).symm
      (Tensor.product (sumTensor T S) R) =
      sumTensor (Tensor.product T R) (Tensor.product S R) := by
  funext x y z
  cases x <;> cases y <;> cases z <;>
    simp [Tensor.pullback, Tensor.product, sumTensor]

/-- Tensor product distributes over the second binary sum by coordinate
permutation. -/
theorem product_sumTensor (T : Tensor K X Y Z) (S : Tensor K U V W)
    (R : Tensor K A B C) :
    Tensor.pullback (Equiv.prodSumDistrib X U A).symm
      (Equiv.prodSumDistrib Y V B).symm (Equiv.prodSumDistrib Z W C).symm
      (Tensor.product T (sumTensor S R)) =
      sumTensor (Tensor.product T S) (Tensor.product T R) := by
  funext x y z
  cases x <;> cases y <;> cases z <;>
    simp [Tensor.pullback, Tensor.product, sumTensor]

/-- Exchanging product factors is a coordinate permutation. -/
theorem tensorProduct_comm (T : Tensor K X Y Z) (S : Tensor K U V W) :
    Tensor.pullback (Equiv.prodComm X U) (Equiv.prodComm Y V)
      (Equiv.prodComm Z W) (Tensor.product S T) = Tensor.product T S := by
  funext x y z
  simp [Tensor.pullback, Tensor.product, mul_comm]

/-- Reassociating product factors is a coordinate permutation. -/
theorem tensorProduct_assoc (T : Tensor K X Y Z) (S : Tensor K U V W)
    (R : Tensor K A B C) :
    Tensor.pullback (Equiv.prodAssoc X U A) (Equiv.prodAssoc Y V B)
      (Equiv.prodAssoc Z W C) (Tensor.product T (Tensor.product S R)) =
      Tensor.product (Tensor.product T S) R := by
  funext x y z
  simp [Tensor.pullback, Tensor.product, mul_assoc]

/-- Scalar multiplication by one is the right unit for tensor product. -/
theorem tensorProduct_one_right (T : Tensor K X Y Z) :
    Tensor.pullback (Equiv.prodPUnit X).symm (Equiv.prodPUnit Y).symm
      (Equiv.prodPUnit Z).symm
      (Tensor.product T (fun (_ _ _ : PUnit) => (1 : K))) = T := by
  funext x y z
  simp [Tensor.pullback, Tensor.product]

/-- Scalar multiplication by one is the left unit for tensor product. -/
theorem tensorProduct_one_left (T : Tensor K X Y Z) :
    Tensor.pullback (Equiv.punitProd X).symm (Equiv.punitProd Y).symm
      (Equiv.punitProd Z).symm
      (Tensor.product (fun (_ _ _ : PUnit) => (1 : K)) T) = T := by
  funext x y z
  simp [Tensor.pullback, Tensor.product]

end MatrixMultiplication.AuxiliarySeparation

end OAI
