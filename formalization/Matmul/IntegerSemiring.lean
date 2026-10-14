import Matmul.IntegerTensor
import Matmul.IntegerBilinear
import Mathlib.Order.Antisymmetrization
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Subsemiring.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fin.Tuple.Basic

namespace OAI

variable {K : Type*} [CommSemiring K]

/-!
# Finite tensors modulo mutual restriction

Representatives have three natural-number dimensions and coefficients in `K`.
The order is actual linear restriction, and equality in the quotient is mutual
restriction. In particular, changing coordinates does not change the class.
-/

noncomputable section

open MatrixMultiplication.Foundation
open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation.TensorSemiring

section Restriction

variable {X Y Z U V W P Q R : Type*}
variable [Fintype X] [Fintype Y] [Fintype Z]
variable [Fintype U] [Fintype V] [Fintype W]
variable [Fintype P] [Fintype Q] [Fintype R]

/-- `T` is obtained from `S` by three linear maps on its coordinate spaces. -/
def IsRestriction (T : Tensor K X Y Z) (S : Tensor K U V W) : Prop :=
  ∃ (A : X → U → K) (B : Y → V → K) (C : Z → W → K),
    T = Tensor.restrict A B C S

theorem IsRestriction.refl (T : Tensor K X Y Z) : IsRestriction T T := by
  classical
  exact ⟨_, _, _, (Tensor.restrict_identity T).symm⟩

omit [Fintype X] [Fintype Y] [Fintype Z] in
theorem IsRestriction.trans {T : Tensor K X Y Z} {S : Tensor K U V W}
    {L : Tensor K P Q R} (hTS : IsRestriction T S) (hSL : IsRestriction S L) :
    IsRestriction T L := by
  rcases hTS with ⟨A, B, C, rfl⟩
  rcases hSL with ⟨D, E, F, rfl⟩
  exact ⟨Tensor.composeRestrictionMatrix A D, Tensor.composeRestrictionMatrix B E,
    Tensor.composeRestrictionMatrix C F, Tensor.restrict_restrict D E F A B C L⟩

omit [Fintype U] [Fintype V] [Fintype W] in
theorem IsRestriction.pullback (T : Tensor K X Y Z)
    (fx : U → X) (fy : V → Y) (fz : W → Z) :
    IsRestriction (Tensor.pullback fx fy fz T) T := by
  classical
  exact ⟨_, _, _, Tensor.pullback_eq_restrict fx fy fz T⟩

omit [Fintype X] [Fintype Y] [Fintype Z] in
theorem IsRestriction.of_reindex (T : Tensor K X Y Z)
    (ex : U ≃ X) (ey : V ≃ Y) (ez : W ≃ Z) :
    IsRestriction T (Tensor.pullback ex ey ez T) := by
  have h := IsRestriction.pullback (Tensor.pullback ex ey ez T) ex.symm ey.symm ez.symm
  have heq : Tensor.pullback ex.symm ey.symm ez.symm (Tensor.pullback ex ey ez T) = T := by
    funext x y z
    simp [Tensor.pullback]
  rwa [heq] at h

theorem IsRestriction.reindex_iff
    (T : Tensor K X Y Z) (S : Tensor K U V W)
    {X' Y' Z' U' V' W' : Type*}
    [Fintype X'] [Fintype Y'] [Fintype Z']
    [Fintype U'] [Fintype V'] [Fintype W']
    (ex : X' ≃ X) (ey : Y' ≃ Y) (ez : Z' ≃ Z)
    (eu : U' ≃ U) (ev : V' ≃ V) (ew : W' ≃ W) :
    IsRestriction (Tensor.pullback ex ey ez T) (Tensor.pullback eu ev ew S) ↔
      IsRestriction T S := by
  constructor
  · intro h
    exact (IsRestriction.of_reindex T ex ey ez).trans
      (h.trans (IsRestriction.pullback S eu ev ew))
  · intro h
    exact (IsRestriction.pullback T ex ey ez).trans
      (h.trans (IsRestriction.of_reindex S eu ev ew))

omit [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W] in
theorem IsRestriction.product {T : Tensor K X Y Z} {S : Tensor K U V W}
    {T' : Tensor K P Q R} {U' V' W' : Type*}
    [Fintype U'] [Fintype V'] [Fintype W'] {S' : Tensor K U' V' W'}
    (hT : IsRestriction T T') (hS : IsRestriction S S') :
    IsRestriction (Tensor.product T S) (Tensor.product T' S') := by
  rcases hT with ⟨A, B, C, rfl⟩
  rcases hS with ⟨D, E, F, rfl⟩
  exact ⟨_, _, _, (Tensor.restrict_product A B C D E F T' S').symm⟩

omit [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W] in
theorem IsRestriction.sum {T : Tensor K X Y Z} {S : Tensor K U V W}
    {T' : Tensor K P Q R} {U' V' W' : Type*}
    [Fintype U'] [Fintype V'] [Fintype W'] {S' : Tensor K U' V' W'}
    (hT : IsRestriction T T') (hS : IsRestriction S S') :
    IsRestriction (sumTensor T S) (sumTensor T' S') := by
  rcases hT with ⟨A, B, C, rfl⟩
  rcases hS with ⟨D, E, F, rfl⟩
  exact ⟨_, _, _, (sumTensor_restrict A B C D E F T' S').symm⟩

omit [Fintype X] [Fintype Y] [Fintype Z] in
theorem IsRestriction.zero (S : Tensor K U V W) :
    IsRestriction (0 : Tensor K X Y Z) S := by
  refine ⟨0, 0, 0, ?_⟩
  funext x y z
  simp [Tensor.restrict]

omit [Fintype X] [Fintype Y] [Fintype Z] in
/-- Integral or semiring restriction witnesses survive base change. -/
theorem IsRestriction.map {L : Type*} [CommSemiring L]
    (f : K →+* L) {T : Tensor K X Y Z} {S : Tensor K U V W}
    (h : IsRestriction T S) :
    IsRestriction (fun x y z => f (T x y z)) (fun u v w => f (S u v w)) := by
  rcases h with ⟨A, B, C, rfl⟩
  refine ⟨(fun x u => f (A x u)), (fun y v => f (B y v)),
    (fun z w => f (C z w)), ?_⟩
  funext x y z
  simp [Tensor.restrict]

theorem IsRestriction.rank_le {T : Tensor K X Y Z} {S : Tensor K U V W}
    (h : IsRestriction T S) : exactRank T ≤ exactRank S := by
  rcases h with ⟨A, B, C, rfl⟩
  exact exactRank_restrict_le S A B C

omit [Fintype X] [Fintype Y] [Fintype Z] in
theorem IsRestriction.eq_zero_of_zero {T : Tensor K X Y Z}
    (h : IsRestriction T (0 : Tensor K U V W)) : T = 0 := by
  rcases h with ⟨A, B, C, h⟩
  funext x y z
  rw [h]
  simp [Tensor.restrict]

end Restriction

variable (K) in
/-- A set-sized presentation of any finite coefficient tensor over `K`. -/
structure FiniteTensor where
  nx : ℕ
  ny : ℕ
  nz : ℕ
  coeff : Tensor K (Fin nx) (Fin ny) (Fin nz)

namespace FiniteTensor

/-- Replace arbitrary finite coordinate sets by standard finite sets. -/
def ofTensor {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) : (FiniteTensor K) where
  nx := Fintype.card X
  ny := Fintype.card Y
  nz := Fintype.card Z
  coeff := Tensor.pullback (Fintype.equivFin X).symm
    (Fintype.equivFin Y).symm (Fintype.equivFin Z).symm T

instance : LE (FiniteTensor K) := ⟨fun T S => IsRestriction T.coeff S.coeff⟩

instance : Preorder (FiniteTensor K) where
  le_refl T := IsRestriction.refl T.coeff
  le_trans _ _ _ := IsRestriction.trans

theorem ofTensor_le_iff {X Y Z U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor K X Y Z) (S : Tensor K U V W) :
    ofTensor T ≤ ofTensor S ↔ IsRestriction T S :=
  IsRestriction.reindex_iff T S _ _ _ _ _ _

def product (T S : (FiniteTensor K)) : (FiniteTensor K) :=
  ofTensor (Tensor.product T.coeff S.coeff)

def sum (T S : (FiniteTensor K)) : (FiniteTensor K) :=
  ofTensor (sumTensor T.coeff S.coeff)

theorem product_mono {T T' S S' : (FiniteTensor K)} (hT : T ≤ T') (hS : S ≤ S') :
    product T S ≤ product T' S' :=
  (ofTensor_le_iff _ _).mpr (IsRestriction.product hT hS)

theorem sum_mono {T T' S S' : (FiniteTensor K)} (hT : T ≤ T') (hS : S ≤ S') :
    sum T S ≤ sum T' S' :=
  (ofTensor_le_iff _ _).mpr (IsRestriction.sum hT hS)

end FiniteTensor

variable (K) in
/-- Finite tensors over `K`, with two presentations identified exactly when
each is a linear restriction of the other. -/
abbrev TensorClass := Antisymmetrization (FiniteTensor K) (· ≤ ·)

/-- The class of a finite tensor presentation. -/
def tensorClass (T : (FiniteTensor K)) : (TensorClass K) := toAntisymmetrization (· ≤ ·) T

@[simp] theorem tensorClass_eq_iff (T S : (FiniteTensor K)) :
    tensorClass T = tensorClass S ↔ T ≤ S ∧ S ≤ T :=
  Quotient.eq

@[simp] theorem tensorClass_le_iff (T S : (FiniteTensor K)) :
    tensorClass T ≤ tensorClass S ↔ T ≤ S := Iff.rfl

/-- The quotient class of a tensor on any three finite coordinate sets. -/
def classOf {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) : (TensorClass K) := tensorClass (FiniteTensor.ofTensor T)

theorem classOf_le_iff {X Y Z U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor K X Y Z) (S : Tensor K U V W) :
    classOf T ≤ classOf S ↔ IsRestriction T S := FiniteTensor.ofTensor_le_iff T S

theorem classOf_eq_iff {X Y Z U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor K X Y Z) (S : Tensor K U V W) :
    classOf T = classOf S ↔ IsRestriction T S ∧ IsRestriction S T := by
  rw [le_antisymm_iff, classOf_le_iff, classOf_le_iff]

theorem classOf_reindex {X Y Z U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor K X Y Z) (ex : U ≃ X) (ey : V ≃ Y) (ez : W ≃ Z) :
    classOf (Tensor.pullback ex ey ez T) = classOf T :=
  (classOf_eq_iff _ _).mpr ⟨IsRestriction.pullback T ex ey ez,
    IsRestriction.of_reindex T ex ey ez⟩

theorem classOf_eq_of_reindex {X Y Z U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    {T : Tensor K X Y Z} {S : Tensor K U V W}
    (ex : X ≃ U) (ey : Y ≃ V) (ez : Z ≃ W)
    (h : Tensor.pullback ex ey ez S = T) : classOf T = classOf S :=
  (congrArg classOf h).symm.trans (classOf_reindex S ex ey ez)

@[simp] theorem classOf_coeff (T : (FiniteTensor K)) : classOf T.coeff = tensorClass T := by
  apply (tensorClass_eq_iff _ _).mpr
  exact ⟨IsRestriction.pullback T.coeff _ _ _, IsRestriction.of_reindex T.coeff _ _ _⟩

instance : Mul (TensorClass K) where
  mul := Quotient.map₂ FiniteTensor.product (by
    intro T T' hT S S' hS
    exact ⟨FiniteTensor.product_mono hT.1 hS.1,
      FiniteTensor.product_mono hT.2 hS.2⟩)

instance : Add (TensorClass K) where
  add := Quotient.map₂ FiniteTensor.sum (by
    intro T T' hT S S' hS
    exact ⟨FiniteTensor.sum_mono hT.1 hS.1, FiniteTensor.sum_mono hT.2 hS.2⟩)

@[simp] theorem tensorClass_product (T S : (FiniteTensor K)) :
    tensorClass T * tensorClass S = tensorClass (FiniteTensor.product T S) := rfl

@[simp] theorem tensorClass_sum (T S : (FiniteTensor K)) :
    tensorClass T + tensorClass S = tensorClass (FiniteTensor.sum T S) := rfl

theorem classOf_product {X Y Z U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor K X Y Z) (S : Tensor K U V W) :
    classOf (Tensor.product T S) = classOf T * classOf S := by
  symm
  exact classOf_reindex (Tensor.product T S)
    (Equiv.prodCongr (Fintype.equivFin X).symm (Fintype.equivFin U).symm)
    (Equiv.prodCongr (Fintype.equivFin Y).symm (Fintype.equivFin V).symm)
    (Equiv.prodCongr (Fintype.equivFin Z).symm (Fintype.equivFin W).symm)

theorem classOf_sum {X Y Z U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor K X Y Z) (S : Tensor K U V W) :
    classOf (sumTensor T S) = classOf T + classOf S := by
  symm
  have h := classOf_reindex (sumTensor T S)
    (Equiv.sumCongr (Fintype.equivFin X).symm (Fintype.equivFin U).symm)
    (Equiv.sumCongr (Fintype.equivFin Y).symm (Fintype.equivFin V).symm)
    (Equiv.sumCongr (Fintype.equivFin Z).symm (Fintype.equivFin W).symm)
  change classOf (sumTensor (FiniteTensor.ofTensor T).coeff
    (FiniteTensor.ofTensor S).coeff) = _
  have heq : sumTensor (FiniteTensor.ofTensor T).coeff (FiniteTensor.ofTensor S).coeff =
      Tensor.pullback
        (Equiv.sumCongr (Fintype.equivFin X).symm (Fintype.equivFin U).symm)
        (Equiv.sumCongr (Fintype.equivFin Y).symm (Fintype.equivFin V).symm)
        (Equiv.sumCongr (Fintype.equivFin Z).symm (Fintype.equivFin W).symm)
        (sumTensor T S) := by
    funext x y z
    cases x <;> cases y <;> cases z <;> rfl
  rw [heq]
  exact h

instance : Zero (TensorClass K) := ⟨classOf (0 : Tensor K Empty Empty Empty)⟩
instance : One (TensorClass K) := ⟨classOf (fun (_ _ _ : PUnit.{1}) => (1 : K))⟩

theorem classOf_zero {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z] :
    classOf (0 : Tensor K X Y Z) = 0 :=
  (classOf_eq_iff _ _).mpr ⟨IsRestriction.zero _, IsRestriction.zero _⟩

private theorem class_add_assoc (a b c : (TensorClass K)) : (a + b) + c = a + (b + c) := by
  induction a using Quotient.inductionOn with | h a =>
  induction b using Quotient.inductionOn with | h b =>
  induction c using Quotient.inductionOn with | h c =>
  change (tensorClass a + tensorClass b) + tensorClass c =
    tensorClass a + (tensorClass b + tensorClass c)
  rw [← classOf_coeff a, ← classOf_coeff b, ← classOf_coeff c]
  simp only [← classOf_sum]
  exact classOf_eq_of_reindex _ _ _ (sumTensor_assoc a.coeff b.coeff c.coeff)

private theorem class_add_comm (a b : (TensorClass K)) : a + b = b + a := by
  induction a using Quotient.inductionOn with | h a =>
  induction b using Quotient.inductionOn with | h b =>
  change tensorClass a + tensorClass b = tensorClass b + tensorClass a
  rw [← classOf_coeff a, ← classOf_coeff b]
  simp only [← classOf_sum]
  exact classOf_eq_of_reindex _ _ _ (sumTensor_comm a.coeff b.coeff)

private theorem class_add_zero (a : (TensorClass K)) : a + 0 = a := by
  induction a using Quotient.inductionOn with | h a =>
  change tensorClass a + 0 = tensorClass a
  rw [← classOf_coeff a]
  change classOf a.coeff + classOf (0 : Tensor K Empty Empty Empty) = classOf a.coeff
  rw [← classOf_sum]
  exact (classOf_eq_of_reindex _ _ _ (sumTensor_empty_right a.coeff
    (0 : Tensor K Empty Empty Empty))).symm

private theorem class_zero_add (a : (TensorClass K)) : 0 + a = a :=
  (class_add_comm 0 a).trans (class_add_zero a)

private theorem class_mul_assoc (a b c : (TensorClass K)) : (a * b) * c = a * (b * c) := by
  induction a using Quotient.inductionOn with | h a =>
  induction b using Quotient.inductionOn with | h b =>
  induction c using Quotient.inductionOn with | h c =>
  change (tensorClass a * tensorClass b) * tensorClass c =
    tensorClass a * (tensorClass b * tensorClass c)
  rw [← classOf_coeff a, ← classOf_coeff b, ← classOf_coeff c]
  simp only [← classOf_product]
  exact classOf_eq_of_reindex _ _ _ (tensorProduct_assoc a.coeff b.coeff c.coeff)

private theorem class_mul_comm (a b : (TensorClass K)) : a * b = b * a := by
  induction a using Quotient.inductionOn with | h a =>
  induction b using Quotient.inductionOn with | h b =>
  change tensorClass a * tensorClass b = tensorClass b * tensorClass a
  rw [← classOf_coeff a, ← classOf_coeff b]
  simp only [← classOf_product]
  exact classOf_eq_of_reindex _ _ _ (tensorProduct_comm a.coeff b.coeff)

private theorem class_mul_one (a : (TensorClass K)) : a * 1 = a := by
  induction a using Quotient.inductionOn with | h a =>
  change tensorClass a * 1 = tensorClass a
  rw [← classOf_coeff a]
  change classOf a.coeff * classOf (fun (_ _ _ : PUnit.{1}) => (1 : K)) = classOf a.coeff
  rw [← classOf_product]
  exact (classOf_eq_of_reindex _ _ _ (tensorProduct_one_right a.coeff)).symm

private theorem class_one_mul (a : (TensorClass K)) : 1 * a = a :=
  (class_mul_comm 1 a).trans (class_mul_one a)

private theorem class_mul_zero (a : (TensorClass K)) : a * 0 = 0 := by
  induction a using Quotient.inductionOn with | h a =>
  change tensorClass a * 0 = 0
  rw [← classOf_coeff a]
  change classOf a.coeff * classOf (0 : Tensor K Empty Empty Empty) = 0
  rw [← classOf_product]
  have heq : Tensor.product a.coeff (0 : Tensor K Empty Empty Empty) = 0 := by
    funext x y z
    simp [Tensor.product]
  rw [heq, classOf_zero]

private theorem class_zero_mul (a : (TensorClass K)) : 0 * a = 0 :=
  (class_mul_comm 0 a).trans (class_mul_zero a)

private theorem class_left_distrib (a b c : (TensorClass K)) : a * (b + c) = a * b + a * c := by
  induction a using Quotient.inductionOn with | h a =>
  induction b using Quotient.inductionOn with | h b =>
  induction c using Quotient.inductionOn with | h c =>
  change tensorClass a * (tensorClass b + tensorClass c) =
    tensorClass a * tensorClass b + tensorClass a * tensorClass c
  rw [← classOf_coeff a, ← classOf_coeff b, ← classOf_coeff c]
  simp only [← classOf_product, ← classOf_sum]
  exact (classOf_eq_of_reindex _ _ _ (product_sumTensor a.coeff b.coeff c.coeff)).symm

private theorem class_right_distrib (a b c : (TensorClass K)) : (a + b) * c = a * c + b * c := by
  rw [class_mul_comm, class_left_distrib, class_mul_comm c a, class_mul_comm c b]

instance : CommSemiring (TensorClass K) where
  add_assoc := class_add_assoc
  add_comm := class_add_comm
  zero_add := class_zero_add
  add_zero := class_add_zero
  nsmul := nsmulRec
  mul_assoc := class_mul_assoc
  mul_comm := class_mul_comm
  one_mul := class_one_mul
  mul_one := class_mul_one
  zero_mul := class_zero_mul
  mul_zero := class_mul_zero
  left_distrib := class_left_distrib
  right_distrib := class_right_distrib

theorem mul_mono {T T' S S' : (TensorClass K)} (hT : T ≤ T') (hS : S ≤ S') :
    T * S ≤ T' * S' := by
  induction T using Quotient.inductionOn with | h T =>
  induction T' using Quotient.inductionOn with | h T' =>
  induction S using Quotient.inductionOn with | h S =>
  induction S' using Quotient.inductionOn with | h S' =>
  exact FiniteTensor.product_mono hT hS

theorem add_mono {T T' S S' : (TensorClass K)} (hT : T ≤ T') (hS : S ≤ S') :
    T + S ≤ T' + S' := by
  induction T using Quotient.inductionOn with | h T =>
  induction T' using Quotient.inductionOn with | h T' =>
  induction S using Quotient.inductionOn with | h S =>
  induction S' using Quotient.inductionOn with | h S' =>
  exact FiniteTensor.sum_mono hT hS

/-- Every tensor class is nonnegative in the restriction order. -/
theorem zero_le (T : (TensorClass K)) : 0 ≤ T := by
  induction T using Quotient.inductionOn with | h T =>
  change (0 : (TensorClass K)) ≤ tensorClass T
  rw [← classOf_coeff T]
  exact (classOf_le_iff _ _).mpr (IsRestriction.zero T.coeff)

instance : OrderBot (TensorClass K) where
  bot := 0
  bot_le := zero_le

instance : IsOrderedAddMonoid (TensorClass K) where
  add_le_add_left _ _ h _c := add_mono h le_rfl

instance : IsOrderedMonoid (TensorClass K) where
  mul_le_mul_left _ _ h _c := mul_mono h le_rfl

instance : IsOrderedRing (TensorClass K) where
  zero_le_one := zero_le 1
  mul_le_mul_of_nonneg_left := by
    intro a ha b c hbc
    exact mul_mono le_rfl hbc
  mul_le_mul_of_nonneg_right := by
    intro a ha b c hbc
    exact mul_mono hbc le_rfl

/-- Exact rank descends to mutual-restriction classes. -/
def rank : (TensorClass K) → ℕ := Quotient.lift (fun T : (FiniteTensor K) => exactRank T.coeff)
  (by
    intro T S h
    exact le_antisymm (IsRestriction.rank_le h.1) (IsRestriction.rank_le h.2))

@[simp] theorem rank_tensorClass (T : (FiniteTensor K)) :
    rank (tensorClass T) = exactRank T.coeff := rfl

@[simp] theorem rank_classOf {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) : rank (classOf T) = exactRank T :=
  exactRank_reindex T _ _ _

theorem rank_mono {T S : (TensorClass K)} (h : T ≤ S) : rank T ≤ rank S := by
  induction T using Quotient.inductionOn with | h T =>
  induction S using Quotient.inductionOn with | h S =>
  exact IsRestriction.rank_le h

theorem rank_mul_le (T S : (TensorClass K)) : rank (T * S) ≤ rank T * rank S := by
  induction T using Quotient.inductionOn with | h T =>
  induction S using Quotient.inductionOn with | h S =>
  change rank (tensorClass T * tensorClass S) ≤ rank (tensorClass T) * rank (tensorClass S)
  rw [← classOf_coeff T, ← classOf_coeff S, ← classOf_product]
  simp only [rank_classOf]
  exact exactRank_product_le _ _

theorem classOf_eq_zero_iff {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) : classOf T = 0 ↔ T = 0 := by
  constructor
  · intro h
    have hr : IsRestriction T (0 : Tensor K Empty Empty Empty) :=
      ((classOf_eq_iff _ _).mp h).1
    exact hr.eq_zero_of_zero
  · rintro rfl
    exact classOf_zero

instance [Nontrivial K] : Nontrivial (TensorClass K) := by
  refine ⟨⟨1, 0, ?_⟩⟩
  intro h
  have heq : (fun (_ _ _ : PUnit.{1}) => (1 : K)) = 0 :=
    (classOf_eq_zero_iff _).mp h
  have := congrFun (congrFun (congrFun heq PUnit.unit) PUnit.unit) PUnit.unit
  exact one_ne_zero this

@[simp] theorem rank_zero : rank (0 : TensorClass K) = 0 := by
  change rank (classOf (0 : Tensor K Empty Empty Empty)) = 0
  rw [rank_classOf, exactRank_zero]

theorem rank_eq_zero_iff (T : TensorClass K) : rank T = 0 ↔ T = 0 := by
  induction T using Quotient.inductionOn with
  | h T =>
    change rank (tensorClass T) = 0 ↔ tensorClass T = 0
    rw [← classOf_coeff T, rank_classOf, exactRank_eq_zero_iff, classOf_eq_zero_iff]

theorem rank_pos_iff (T : TensorClass K) : 0 < rank T ↔ T ≠ 0 := by
  simpa only [Nat.pos_iff_ne_zero] using not_congr (rank_eq_zero_iff T)

/-- A coefficient equal to one supplies an integral restriction to the unit.
This proof uses coordinate selection only, and has no division step. -/
theorem one_le_classOf_of_coefficient_one {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) (x : X) (y : Y) (z : Z) (h : T x y z = 1) :
    1 ≤ classOf T := by
  classical
  apply (classOf_le_iff _ _).mpr
  refine ⟨(fun _ u => if u = x then 1 else 0),
    (fun _ v => if v = y then 1 else 0),
    (fun _ w => if w = z then 1 else 0), ?_⟩
  funext a b c
  simp [Tensor.restrict, ite_mul, mul_ite, h]

/-- Every zero-one coefficient tensor is zero or admits the unit by an
integral coordinate-selection restriction. -/
theorem classOf_zeroOne_admissible {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] (T : Tensor K X Y Z)
    (h : ∀ x y z, T x y z = 0 ∨ T x y z = 1) :
    classOf T = 0 ∨ 1 ≤ classOf T := by
  classical
  by_cases hT : T = 0
  · exact Or.inl ((classOf_eq_zero_iff T).mpr hT)
  · right
    have hex : ∃ x y z, T x y z ≠ 0 := by
      by_contra! hz
      exact hT (by funext x y z; exact hz x y z)
    obtain ⟨x, y, z, hxyz⟩ := hex
    exact one_le_classOf_of_coefficient_one T x y z ((h x y z).resolve_left hxyz)

section DirectSums

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

private theorem classOf_directSum_reindex {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (T : κ → Tensor K X Y Z) (e : ι ≃ κ) :
    classOf (Tensor.directSum (fun i => T (e i))) = classOf (Tensor.directSum T) := by
  apply classOf_eq_of_reindex (Equiv.prodCongr e (Equiv.refl X))
    (Equiv.prodCongr e (Equiv.refl Y)) (Equiv.prodCongr e (Equiv.refl Z))
  funext x y z
  simp [Tensor.pullback, Tensor.directSum, e.injective.eq_iff]

private theorem classOf_directSum_option {ι : Type*} [Fintype ι] [di : DecidableEq ι]
    [dopt : DecidableEq (Option ι)]
    (T : Option ι → Tensor K X Y Z) :
    classOf (Tensor.directSum T) =
      classOf (T none) + classOf (Tensor.directSum (fun i => T (some i))) := by
  rw [← classOf_sum]
  symm
  apply classOf_eq_of_reindex optionProdEquiv.symm
    optionProdEquiv.symm optionProdEquiv.symm
  funext x y z
  cases x with
  | inl x =>
    cases y <;> cases z <;> simp [Tensor.pullback, Tensor.directSum, sumTensor]
  | inr x =>
    cases y <;> cases z <;> simp [Tensor.pullback, Tensor.directSum, sumTensor]

/-- Passing to tensor classes converts every finite block direct sum to a sum. -/
theorem classOf_directSum {ι : Type*} [Fintype ι] [dec : DecidableEq ι]
    (T : ι → Tensor K X Y Z) :
    classOf (Tensor.directSum T) = ∑ i, classOf (T i) := by
  have hdec : dec = (fun a b => Classical.propDecidable (a = b)) := Subsingleton.elim _ _
  subst dec
  classical
  refine Fintype.induction_empty_option
    (P := fun ι _ => ∀ T : ι → Tensor K X Y Z,
      classOf (Tensor.directSum T) = ∑ i, classOf (T i)) ?_ ?_ ?_ ι T
  · intro α β _ e ih S
    let : Fintype α := Fintype.ofEquiv β e.symm
    rw [← classOf_directSum_reindex S e, ih]
    exact e.sum_comp (fun i => classOf (S i))
  · intro S
    have he : (∑ i, classOf (S i)) = 0 := Finset.sum_eq_zero (fun i _ => i.elim)
    rw [he]
    apply (classOf_eq_zero_iff _).mpr
    funext x
    exact x.1.elim
  · intro α _ ih S
    rw [classOf_directSum_option
      (di := fun a b => Classical.propDecidable (a = b))
      (dopt := fun a b => Classical.propDecidable (a = b)), ih, Fintype.sum_option]

end DirectSums

/-- Function-indexed tensor powers are semiring powers up to coordinate
permutation, so they have the same integral restriction class. -/
@[simp] theorem classOf_power {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] (T : Tensor K X Y Z) (n : ℕ) :
    classOf (Tensor.power T n) = classOf T ^ n := by
  induction n with
  | zero =>
    have heq : Tensor.power T 0 = Tensor.pullback
        (Equiv.equivPUnit (Fin 0 → X))
        (Equiv.equivPUnit (Fin 0 → Y))
        (Equiv.equivPUnit (Fin 0 → Z)) (fun (_ _ _ : PUnit) => (1 : K)) := by
      funext x y z
      simp [Tensor.power, Tensor.pullback]
    rw [heq, classOf_reindex]
    rfl
  | succ n ih =>
    have heq : Tensor.power T (n + 1) = Tensor.pullback
        (Fin.consEquiv (fun _ : Fin (n + 1) => X)).symm
        (Fin.consEquiv (fun _ : Fin (n + 1) => Y)).symm
        (Fin.consEquiv (fun _ : Fin (n + 1) => Z)).symm
        (Tensor.product T (Tensor.power T n)) := by
      funext x y z
      simp [Tensor.power, Tensor.pullback, Tensor.product, Fin.consEquiv,
        Fin.prod_univ_succ, Fin.tail]
    rw [heq, classOf_reindex, classOf_product, ih, pow_succ, mul_comm]

/-- The tensors on which the Strassen preorder has the unit lower bound.
Over rings a nonzero coefficient need not be invertible, so this condition is
recorded explicitly instead of inferred from nonvanishing. -/
def unitAdmittingSubsemiring (K : Type*) [CommSemiring K] : Subsemiring (TensorClass K) where
  carrier := {T | T = 0 ∨ 1 ≤ T}
  zero_mem' := Or.inl rfl
  one_mem' := Or.inr le_rfl
  add_mem' := by
    intro T S hT hS
    rcases hT with rfl | hT
    · simpa using hS
    · right
      have h := add_mono hT (zero_le S)
      simpa using h
  mul_mem' := by
    intro T S hT hS
    rcases hT with rfl | hT
    · left
      simp
    rcases hS with rfl | hS
    · left
      simp
    · right
      simpa using mul_mono hT hS

/-- Unit-admitting finite tensors modulo mutual integral restriction. -/
abbrev UnitTensorClass (K : Type*) [CommSemiring K] := ↥(unitAdmittingSubsemiring K)

namespace UnitTensorClass

/-- Form a unit-admitting class from an actual unit restriction certificate. -/
def ofTensor {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z)
    (h : T = 0 ∨ IsRestriction (fun (_ _ _ : PUnit.{1}) => (1 : K)) T) :
    UnitTensorClass K :=
  ⟨classOf T, h.elim (fun h => Or.inl ((classOf_eq_zero_iff T).mpr h))
    (fun h => Or.inr ((classOf_le_iff _ _).mpr h))⟩

@[simp] theorem coe_ofTensor {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z)
    (h : T = 0 ∨ IsRestriction (fun (_ _ _ : PUnit.{1}) => (1 : K)) T) :
    ((ofTensor T h : UnitTensorClass K) : TensorClass K) = classOf T := rfl

/-- Canonical packaging of any zero-one tensor in the unit-admitting
subsemiring. In particular, this covers finite convolution support tensors. -/
def ofZeroOneTensor {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) (h : ∀ x y z, T x y z = 0 ∨ T x y z = 1) :
    UnitTensorClass K := ⟨classOf T, classOf_zeroOne_admissible T h⟩

@[simp] theorem coe_ofZeroOneTensor {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) (h : ∀ x y z, T x y z = 0 ∨ T x y z = 1) :
    ((ofZeroOneTensor T h : UnitTensorClass K) : TensorClass K) = classOf T := rfl

@[simp] theorem coe_zero : ((0 : UnitTensorClass K) : TensorClass K) = 0 := rfl
@[simp] theorem coe_one : ((1 : UnitTensorClass K) : TensorClass K) = 1 := rfl
@[simp] theorem coe_add (T S : UnitTensorClass K) :
    ((T + S : UnitTensorClass K) : TensorClass K) = T + S := rfl
@[simp] theorem coe_mul (T S : UnitTensorClass K) :
    ((T * S : UnitTensorClass K) : TensorClass K) = T * S := rfl
@[simp] theorem coe_natCast (n : ℕ) :
    ((n : UnitTensorClass K) : TensorClass K) = n := rfl

@[simp] theorem coe_pow (T : UnitTensorClass K) (n : ℕ) :
    ((T ^ n : UnitTensorClass K) : TensorClass K) = T.val ^ n :=
  map_pow (unitAdmittingSubsemiring K).subtype T n

@[simp] theorem coe_sum {ι : Type*} (s : Finset ι) (T : ι → UnitTensorClass K) :
    ((∑ i ∈ s, T i : UnitTensorClass K) : TensorClass K) = ∑ i ∈ s, (T i).val :=
  map_sum (unitAdmittingSubsemiring K).subtype T s

/-- Product identities pass from actual zero-one tensors to the admitted
subsemiring; the proof is independent of the support certificates. -/
theorem ofZeroOneTensor_product {X Y Z U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor K X Y Z) (S : Tensor K U V W)
    (hT : ∀ x y z, T x y z = 0 ∨ T x y z = 1)
    (hS : ∀ u v w, S u v w = 0 ∨ S u v w = 1)
    (hTS : ∀ x y z, Tensor.product T S x y z = 0 ∨ Tensor.product T S x y z = 1) :
    ofZeroOneTensor (Tensor.product T S) hTS = ofZeroOneTensor T hT * ofZeroOneTensor S hS := by
  apply Subtype.ext
  exact classOf_product T S

theorem ofZeroOneTensor_directSum {ι X Y Z : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype X] [Fintype Y] [Fintype Z] (T : ι → Tensor K X Y Z)
    (hT : ∀ i x y z, T i x y z = 0 ∨ T i x y z = 1)
    (hDS : ∀ x y z, Tensor.directSum T x y z = 0 ∨ Tensor.directSum T x y z = 1) :
    ofZeroOneTensor (Tensor.directSum T) hDS = ∑ i, ofZeroOneTensor (T i) (hT i) := by
  apply Subtype.ext
  exact (classOf_directSum T).trans
    (map_sum (unitAdmittingSubsemiring K).subtype (fun i => ofZeroOneTensor (T i) (hT i))
      Finset.univ).symm

theorem ofZeroOneTensor_power {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] (T : Tensor K X Y Z) (n : ℕ)
    (hT : ∀ x y z, T x y z = 0 ∨ T x y z = 1)
    (hPow : ∀ x y z, Tensor.power T n x y z = 0 ∨ Tensor.power T n x y z = 1) :
    ofZeroOneTensor (Tensor.power T n) hPow = ofZeroOneTensor T hT ^ n := by
  apply Subtype.ext
  exact (classOf_power T n).trans (coe_pow (ofZeroOneTensor T hT) n).symm

theorem zero_le (T : UnitTensorClass K) : 0 ≤ T := TensorSemiring.zero_le T.val

theorem one_le_of_ne_zero {T : UnitTensorClass K} (hT : T ≠ 0) : 1 ≤ T := by
  rcases T.property with h | h
  · exact False.elim (hT (Subtype.ext h))
  · exact h

theorem add_mono {T T' S S' : UnitTensorClass K} (hT : T ≤ T') (hS : S ≤ S') :
    T + S ≤ T' + S' := TensorSemiring.add_mono hT hS

theorem mul_mono {T T' S S' : UnitTensorClass K} (hT : T ≤ T') (hS : S ≤ S') :
    T * S ≤ T' * S' := TensorSemiring.mul_mono hT hS

instance : OrderBot (UnitTensorClass K) where
  bot := 0
  bot_le := zero_le

instance : IsOrderedAddMonoid (UnitTensorClass K) where
  add_le_add_left _ _ h _ := add_mono h le_rfl

instance : IsOrderedMonoid (UnitTensorClass K) where
  mul_le_mul_left _ _ h _ := mul_mono h le_rfl

instance : IsOrderedRing (UnitTensorClass K) where
  zero_le_one := zero_le 1
  mul_le_mul_of_nonneg_left := by
    intro a ha b c hbc
    exact mul_mono le_rfl hbc
  mul_le_mul_of_nonneg_right := by
    intro a ha b c hbc
    exact mul_mono hbc le_rfl

/-- Integral exact rank, evaluated on the underlying tensor class. -/
def rank (T : UnitTensorClass K) : ℕ := TensorSemiring.rank T.val

@[simp] theorem rank_ofZeroOneTensor {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) (h : ∀ x y z, T x y z = 0 ∨ T x y z = 1) :
    rank (ofZeroOneTensor T h) = exactRank T := rank_classOf T

/-- The rank of a semiring power is the actual integral coefficient rank
of the function-indexed tensor power. -/
theorem rank_power_ofZeroOneTensor {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) (h : ∀ x y z, T x y z = 0 ∨ T x y z = 1) (n : ℕ) :
    rank (ofZeroOneTensor T h ^ n) = exactRank (Tensor.power T n) := by
  rw [rank, coe_pow, coe_ofZeroOneTensor, ← classOf_power, rank_classOf]

/-- Rank bounds in the admitted semiring therefore provide actual coefficient
algorithms of that rank, rather than a formal order assertion only. -/
theorem rank_power_spec_ofZeroOneTensor {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) (h : ∀ x y z, T x y z = 0 ∨ T x y z = 1) (n : ℕ) :
    Tensor.RankAtMost (Tensor.power T n) (rank (ofZeroOneTensor T h ^ n)) := by
  rw [rank_power_ofZeroOneTensor]
  exact exactRank_spec _

theorem rank_mono {T S : UnitTensorClass K} (h : T ≤ S) : rank T ≤ rank S :=
  TensorSemiring.rank_mono h

theorem rank_mul_le (T S : UnitTensorClass K) : rank (T * S) ≤ rank T * rank S :=
  TensorSemiring.rank_mul_le T.val S.val

@[simp] theorem rank_zero : rank (0 : UnitTensorClass K) = 0 := TensorSemiring.rank_zero

theorem rank_eq_zero_iff (T : UnitTensorClass K) : rank T = 0 ↔ T = 0 := by
  rw [rank, TensorSemiring.rank_eq_zero_iff]
  constructor
  · intro h
    exact Subtype.ext h
  · intro h
    exact congrArg Subtype.val h

theorem rank_pos_iff (T : UnitTensorClass K) : 0 < rank T ↔ T ≠ 0 := by
  simpa only [Nat.pos_iff_ne_zero] using not_congr (rank_eq_zero_iff T)

/-- The ordinary rectangular algorithm is an actual integral decomposition,
with one product for each triple of matrix indices. -/
theorem matrixTensor_rankAtMost_cubic (a b c : ℕ) :
    Tensor.RankAtMost (Matmul.IntegerBilinear.matrixTensor a b c) (a * b * c) := by
  classical
  let A : Fin a × Fin b × Fin c → Fin a × Fin b → ℤ :=
    fun p x => if x = (p.1, p.2.1) then 1 else 0
  let B : Fin a × Fin b × Fin c → Fin b × Fin c → ℤ :=
    fun p y => if y = (p.2.1, p.2.2) then 1 else 0
  let C : Fin a × Fin b × Fin c → Fin c × Fin a → ℤ :=
    fun p z => if z = (p.2.2, p.1) then 1 else 0
  have heq : Matmul.IntegerBilinear.matrixTensor a b c =
      fun x y z => ∑ p, Tensor.rankOne (A p) (B p) (C p) x y z := by
    funext x y z
    simp [A, B, C, Tensor.rankOne, Matmul.IntegerBilinear.matrixTensor,
      Fintype.sum_prod_type, Prod.ext_iff, ite_and, mul_ite]
    split_ifs <;> simp_all
  rw [heq]
  convert Tensor.rankAtMost_sum_rankOne A B C using 1
  simp [Fintype.card_prod, Nat.mul_assoc]

/-- The rectangular matrix multiplication class uses integer coefficients.
Its unit-admitting property is proved by the zero-one support formula. -/
def matrixClass (a b c : ℕ) : UnitTensorClass ℤ :=
  ofZeroOneTensor (Matmul.IntegerBilinear.matrixTensor a b c) (by
    intro x y z
    simp only [Matmul.IntegerBilinear.matrixTensor]
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl)

@[simp] theorem coe_matrixClass (a b c : ℕ) :
    ((matrixClass a b c : UnitTensorClass ℤ) : TensorClass ℤ) =
      classOf (Matmul.IntegerBilinear.matrixTensor a b c) := rfl

@[simp] theorem rank_matrixClass (a b c : ℕ) :
    rank (matrixClass a b c) = exactRank (Matmul.IntegerBilinear.matrixTensor a b c) :=
  rank_classOf _

/-- The integral matrix rank has the ordinary cubic upper bound. -/
theorem rank_matrixClass_upper (a b c : ℕ) : rank (matrixClass a b c) ≤ a * b * c := by
  rw [rank_matrixClass]
  exact exactRank_le (matrixTensor_rankAtMost_cubic a b c)

theorem matrixClass_zero_left (b c : ℕ) : matrixClass 0 b c = 0 := by
  apply Subtype.ext
  apply (classOf_eq_zero_iff _).mpr
  funext x
  exact Fin.elim0 x.1

theorem matrixClass_zero_middle (a c : ℕ) : matrixClass a 0 c = 0 := by
  apply Subtype.ext
  apply (classOf_eq_zero_iff _).mpr
  funext x
  exact Fin.elim0 x.2

theorem matrixClass_zero_right (a b : ℕ) : matrixClass a b 0 = 0 := by
  apply Subtype.ext
  apply (classOf_eq_zero_iff _).mpr
  funext x y
  exact Fin.elim0 y.2

/-- Positive matrix dimensions supply a coefficient equal to one, giving the
unit restriction using only integer coefficients. -/
theorem one_le_matrixClass {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    1 ≤ matrixClass a b c := by
  let i : Fin a := ⟨0, ha⟩
  let j : Fin b := ⟨0, hb⟩
  let k : Fin c := ⟨0, hc⟩
  exact one_le_classOf_of_coefficient_one _ (i, j) (j, k) (k, i) (by
    simp [Matmul.IntegerBilinear.matrixTensor])

theorem matrixClass_ne_zero {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    matrixClass a b c ≠ 0 := by
  intro h
  have hz := one_le_matrixClass ha hb hc
  rw [h] at hz
  have heq : (1 : UnitTensorClass ℤ) = 0 := le_antisymm hz (zero_le 1)
  exact one_ne_zero heq

/-- Grouping each pair of dimensions identifies tensor products of matrix
multiplication tensors with multiplication of their dimensions. -/
theorem matrixClass_product (a b c d e f : ℕ) :
    matrixClass (a * d) (b * e) (c * f) = matrixClass a b c * matrixClass d e f := by
  apply Subtype.ext
  change classOf (Matmul.IntegerBilinear.matrixTensor (a * d) (b * e) (c * f)) =
    classOf (Matmul.IntegerBilinear.matrixTensor a b c) *
      classOf (Matmul.IntegerBilinear.matrixTensor d e f)
  rw [← classOf_product]
  let ea : Fin (a * d) ≃ Fin a × Fin d := Fintype.equivOfCardEq (by simp)
  let eb : Fin (b * e) ≃ Fin b × Fin e := Fintype.equivOfCardEq (by simp)
  let ec : Fin (c * f) ≃ Fin c × Fin f := Fintype.equivOfCardEq (by simp)
  let ex := (Equiv.prodProdProdComm (Fin a) (Fin b) (Fin d) (Fin e)).trans
    (Equiv.prodCongr ea.symm eb.symm)
  let ey := (Equiv.prodProdProdComm (Fin b) (Fin c) (Fin e) (Fin f)).trans
    (Equiv.prodCongr eb.symm ec.symm)
  let ez := (Equiv.prodProdProdComm (Fin c) (Fin a) (Fin f) (Fin d)).trans
    (Equiv.prodCongr ec.symm ea.symm)
  symm
  apply classOf_eq_of_reindex ex ey ez
  funext x y z
  simp only [Tensor.pullback, Tensor.product, Matmul.IntegerBilinear.matrixTensor,
    ex, ey, ez, Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.prodProdProdComm_apply,
    ]
  split_ifs <;> simp_all

@[simp] theorem matrixClass_one : matrixClass 1 1 1 = 1 := by
  apply Subtype.ext
  change classOf (Matmul.IntegerBilinear.matrixTensor 1 1 1) =
    classOf (fun (_ _ _ : PUnit.{1}) => (1 : ℤ))
  let e : Fin 1 × Fin 1 ≃ PUnit.{1} := Fintype.equivOfCardEq (by simp)
  apply classOf_eq_of_reindex e e e
  funext x y z
  simp [Tensor.pullback, Matmul.IntegerBilinear.matrixTensor, Subsingleton.elim x.2 y.1,
    Subsingleton.elim y.2 z.1, Subsingleton.elim z.2 x.1]

/-- Powering matrix dimensions gives tensor powers in the integral semiring. -/
theorem matrixClass_pow (a b c n : ℕ) :
    matrixClass (a ^ n) (b ^ n) (c ^ n) = matrixClass a b c ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [pow_succ, matrixClass_product, ih]

end UnitTensorClass

end MatrixMultiplication.AuxiliarySeparation.TensorSemiring

end

end OAI
