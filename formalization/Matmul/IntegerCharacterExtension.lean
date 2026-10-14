import Matmul.IntegralSpectrum

/-!
# Extending integral spectral points to every integer tensor

A tensor need not admit the unit over the integers. Adjoining one scalar
summand always gives a unit-admitting tensor. Subtracting the value of that
summand extends a spectral point to all integral coefficient tensors.

The coefficient-level interface and reindex/rank arguments follow OpenAI's
`AuxiliarySeparation/Character/Basic.lean` (Apache-2.0), without the field-only
claim that every nonzero tensor has positive value.
-/

namespace Matmul

open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring

noncomputable section
open scoped BigOperators

namespace IntegerCharacterExtension

/-- Adjoin one independent scalar multiplication to an arbitrary tensor class. -/
def adjoinUnit (t : TensorClass ℤ) : UnitTensorClass ℤ :=
  ⟨t + 1, Or.inr (by
    simpa only [zero_add] using TensorSemiring.add_mono (TensorSemiring.zero_le t) le_rfl)⟩

@[simp] theorem coe_adjoinUnit (t : TensorClass ℤ) :
    (adjoinUnit t : TensorClass ℤ) = t + 1 := rfl

@[simp] theorem adjoinUnit_zero : adjoinUnit 0 = 1 := by
  apply Subtype.ext
  simp [adjoinUnit]

@[simp] theorem adjoinUnit_unitClass (s : UnitTensorClass ℤ) :
    adjoinUnit (s : TensorClass ℤ) = s + 1 := by
  apply Subtype.ext
  rfl

/-- The scalar summands in two unit adjunctions combine by direct sum. -/
theorem adjoinUnit_add (t u : TensorClass ℤ) :
    adjoinUnit t + adjoinUnit u = adjoinUnit (t + u) + 1 := by
  apply Subtype.ext
  change (t + 1) + (u + 1) = (t + u + 1) + 1
  ring

/-- The product expansion is an identity among unit-admitting objects. -/
theorem adjoinUnit_mul (t u : TensorClass ℤ) :
    adjoinUnit t * adjoinUnit u + 1 = adjoinUnit (t * u) + adjoinUnit (t + u) := by
  apply Subtype.ext
  change (t + 1) * (u + 1) + 1 = (t * u + 1) + (t + u + 1)
  ring

/-- Extend a spectral point by removing the adjoined scalar value. -/
def extendedValue (χ : UnitTensorClass ℤ →+* ℝ) (t : TensorClass ℤ) : ℝ :=
  χ (adjoinUnit t) - 1

@[simp] theorem extendedValue_unitClass (χ : UnitTensorClass ℤ →+* ℝ)
    (s : UnitTensorClass ℤ) : extendedValue χ s.val = χ s := by
  simp [extendedValue]

@[simp] theorem extendedValue_zero (χ : UnitTensorClass ℤ →+* ℝ) :
    extendedValue χ 0 = 0 := by simp [extendedValue]

@[simp] theorem extendedValue_one (χ : UnitTensorClass ℤ →+* ℝ) :
    extendedValue χ 1 = 1 := by
  simpa only [UnitTensorClass.coe_one, map_one] using extendedValue_unitClass χ 1

theorem extendedValue_add (χ : UnitTensorClass ℤ →+* ℝ) (t u : TensorClass ℤ) :
    extendedValue χ (t + u) = extendedValue χ t + extendedValue χ u := by
  have h := congrArg χ (adjoinUnit_add t u)
  simp only [map_add, map_one] at h
  dsimp [extendedValue]
  linarith

theorem extendedValue_mul (χ : UnitTensorClass ℤ →+* ℝ) (t u : TensorClass ℤ) :
    extendedValue χ (t * u) = extendedValue χ t * extendedValue χ u := by
  have h := congrArg χ (adjoinUnit_mul t u)
  have h' := congrArg χ (adjoinUnit_add t u)
  simp only [map_add, map_mul, map_one] at h h'
  dsimp [extendedValue]
  nlinarith

/-- A genuine semiring homomorphism on all integral tensor classes. -/
def extendedHom (χ : UnitTensorClass ℤ →+* ℝ) : TensorClass ℤ →+* ℝ where
  toFun := extendedValue χ
  map_zero' := extendedValue_zero χ
  map_one' := extendedValue_one χ
  map_add' := extendedValue_add χ
  map_mul' := extendedValue_mul χ

@[simp] theorem extendedHom_apply (χ : UnitTensorClass ℤ →+* ℝ)
    (t : TensorClass ℤ) : extendedHom χ t = extendedValue χ t := rfl

@[simp] theorem extendedHom_unitClass (χ : UnitTensorClass ℤ →+* ℝ)
    (s : UnitTensorClass ℤ) : extendedHom χ s.val = χ s := extendedValue_unitClass χ s

theorem extendedHom_monotone (χ : UnitTensorClass ℤ →+* ℝ) (hχ : Monotone χ) :
    Monotone (extendedHom χ) := by
  intro t u htu
  exact sub_le_sub_right (hχ (show adjoinUnit t ≤ adjoinUnit u from
    TensorSemiring.add_mono htu le_rfl)) 1

theorem extendedHom_nonneg (χ : UnitTensorClass ℤ →+* ℝ) (hχ : Monotone χ)
    (t : TensorClass ℤ) : 0 ≤ extendedHom χ t := by
  simpa only [map_zero] using extendedHom_monotone χ hχ (TensorSemiring.zero_le t)

theorem extendedHom_le_rank (χ : UnitTensorClass ℤ →+* ℝ) (hχ : Monotone χ)
    (t : TensorClass ℤ) : extendedHom χ t ≤ TensorSemiring.rank t := by
  simpa only [map_natCast] using extendedHom_monotone χ hχ (TensorSemiring.le_rank t)

end IntegerCharacterExtension

/-- Normalized additive, multiplicative, restriction-monotone valuations on
all finite integral coefficient tensors. Faithfulness is not required. -/
structure IntegralCharacter where
  value : {X Y Z : Type} → [Fintype X] → [Fintype Y] → [Fintype Z] →
    Tensor ℤ X Y Z → ℝ
  nonneg : ∀ {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor ℤ X Y Z), 0 ≤ value T
  map_zero : ∀ {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z],
    value (0 : Tensor ℤ X Y Z) = 0
  map_one : value (fun (_ _ _ : PUnit.{1}) => (1 : ℤ)) = 1
  map_sumTensor : ∀ {X Y Z U V W : Type}
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor ℤ X Y Z) (S : Tensor ℤ U V W),
    value (sumTensor T S) = value T + value S
  map_directSum : ∀ {ι X Y Z : Type} [Fintype ι] [DecidableEq ι]
    [Fintype X] [Fintype Y] [Fintype Z] (T : ι → Tensor ℤ X Y Z),
    value (Tensor.directSum T) = ∑ i, value (T i)
  map_product : ∀ {X Y Z U V W : Type}
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor ℤ X Y Z) (S : Tensor ℤ U V W),
    value (Tensor.product T S) = value T * value S
  monotone : ∀ {X Y Z U V W : Type}
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor ℤ X Y Z) (A : U → X → ℤ) (B : V → Y → ℤ) (C : W → Z → ℤ),
    value (Tensor.restrict A B C T) ≤ value T

namespace IntegralCharacter

/-- Convert every monotone spectral point on unit-admitting integral tensors
into the coefficient-level character needed for the polynomial constructions. -/
def ofUnitTensorClassHom (χ : UnitTensorClass ℤ →+* ℝ) (hχ : Monotone χ) :
    IntegralCharacter where
  value T := IntegerCharacterExtension.extendedHom χ (classOf T)
  nonneg T := IntegerCharacterExtension.extendedHom_nonneg χ hχ (classOf T)
  map_zero := by
    intro X Y Z _ _ _
    rw [classOf_zero]
    exact RingHom.map_zero _
  map_one := by
    change IntegerCharacterExtension.extendedHom χ 1 = 1
    exact RingHom.map_one _
  map_sumTensor T S := by rw [classOf_sum, map_add]
  map_directSum T := by rw [classOf_directSum, map_sum]
  map_product T S := by rw [classOf_product, map_mul]
  monotone T A B C :=
    IntegerCharacterExtension.extendedHom_monotone χ hχ
      ((classOf_le_iff _ _).mpr ⟨A, B, C, rfl⟩)

@[simp] theorem ofUnitTensorClassHom_value (χ : UnitTensorClass ℤ →+* ℝ)
    (hχ : Monotone χ) {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor ℤ X Y Z) :
    (ofUnitTensorClassHom χ hχ).value T =
      IntegerCharacterExtension.extendedHom χ (classOf T) := rfl

/-- The extension agrees with the original spectral point on every admitted
coefficient tensor, independently of the chosen membership proof. -/
theorem ofUnitTensorClassHom_value_eq (χ : UnitTensorClass ℤ →+* ℝ)
    (hχ : Monotone χ) {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor ℤ X Y Z) (hT : classOf T = 0 ∨ 1 ≤ classOf T) :
    (ofUnitTensorClassHom χ hχ).value T = χ ⟨classOf T, hT⟩ :=
  IntegerCharacterExtension.extendedHom_unitClass χ ⟨classOf T, hT⟩

@[simp] theorem ofUnitTensorClassHom_value_ofZeroOneTensor
    (χ : UnitTensorClass ℤ →+* ℝ) (hχ : Monotone χ)
    {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor ℤ X Y Z) (hT : ∀ x y z, T x y z = 0 ∨ T x y z = 1) :
    (ofUnitTensorClassHom χ hχ).value T = χ (UnitTensorClass.ofZeroOneTensor T hT) :=
  ofUnitTensorClassHom_value_eq χ hχ T (classOf_zeroOne_admissible T hT)

/-- Coordinate pullbacks are integral restrictions. -/
theorem value_pullback_le (χ : IntegralCharacter)
    {X Y Z U V W : Type} [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W] (T : Tensor ℤ X Y Z)
    (fx : U → X) (fy : V → Y) (fz : W → Z) :
    χ.value (Tensor.pullback fx fy fz T) ≤ χ.value T := by
  classical
  rw [Tensor.pullback_eq_restrict]
  exact χ.monotone T _ _ _

/-- Independent bijections of coordinate spaces preserve the valuation. -/
theorem value_reindex (χ : IntegralCharacter)
    {X Y Z U V W : Type} [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W] (T : Tensor ℤ X Y Z)
    (ex : U ≃ X) (ey : V ≃ Y) (ez : W ≃ Z) :
    χ.value (Tensor.pullback ex ey ez T) = χ.value T := by
  apply le_antisymm (χ.value_pullback_le T ex ey ez)
  have h := χ.value_pullback_le (Tensor.pullback ex ey ez T) ex.symm ey.symm ez.symm
  have heq : Tensor.pullback ex.symm ey.symm ez.symm (Tensor.pullback ex ey ez T) = T := by
    funext x y z
    simp [Tensor.pullback]
  simpa only [heq] using h

/-- Diagonal scalar tensors have the expected natural-number value. -/
@[simp] theorem value_scalarTensor (χ : IntegralCharacter) (r : ℕ) :
    χ.value (scalarTensor ℤ r) = r := by
  let U : Fin r → Tensor ℤ PUnit.{1} PUnit.{1} PUnit.{1} := fun _ => fun _ _ _ => 1
  have heq : Tensor.pullback (Equiv.prodPUnit (Fin r)).symm
      (Equiv.prodPUnit (Fin r)).symm (Equiv.prodPUnit (Fin r)).symm
      (Tensor.directSum U) = scalarTensor ℤ r := by rfl
  rw [← heq, χ.value_reindex, χ.map_directSum]
  simp only [U, χ.map_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]

/-- Character values are bounded by every actual integral rank decomposition. -/
theorem value_le_rank (χ : IntegralCharacter)
    {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    {T : Tensor ℤ X Y Z} {r : ℕ} (hr : Tensor.RankAtMost T r) : χ.value T ≤ r := by
  rcases (TensorSemiring.rankAtMost_iff_isRestriction_scalarTensor T r).mp hr with ⟨A, B, C, rfl⟩
  exact (χ.monotone _ A B C).trans_eq (χ.value_scalarTensor r)

/-- A coefficient equal to one gives a unit restriction without division. -/
theorem one_le_value_of_coefficient_one (χ : IntegralCharacter)
    {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor ℤ X Y Z) (x : X) (y : Y) (z : Z) (h : T x y z = 1) :
    1 ≤ χ.value T := by
  classical
  let A : PUnit.{1} → X → ℤ := fun _ u => if u = x then 1 else 0
  let B : PUnit.{1} → Y → ℤ := fun _ v => if v = y then 1 else 0
  let C : PUnit.{1} → Z → ℤ := fun _ w => if w = z then 1 else 0
  have heq : Tensor.restrict A B C T = (fun (_ _ _ : PUnit.{1}) => (1 : ℤ)) := by
    funext a b c
    simp [Tensor.restrict, A, B, C, ite_mul, mul_ite, h]
  simpa only [heq, χ.map_one] using χ.monotone T A B C

theorem value_pos_of_coefficient_one (χ : IntegralCharacter)
    {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor ℤ X Y Z) (x : X) (y : Y) (z : Z) (h : T x y z = 1) :
    0 < χ.value T := zero_lt_one.trans_le (χ.one_le_value_of_coefficient_one T x y z h)

/-- Any integral restriction to the scalar unit gives the unit lower bound,
including tensors whose unit certificate combines several coefficients. -/
theorem one_le_value_of_unitRestriction (χ : IntegralCharacter)
    {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor ℤ X Y Z)
    (hT : IsRestriction (fun (_ _ _ : PUnit.{1}) => (1 : ℤ)) T) :
    1 ≤ χ.value T := by
  obtain ⟨A, B, C, h⟩ := hT
  have hχ := χ.monotone T A B C
  simpa only [← h, χ.map_one] using hχ

theorem value_pos_of_unitRestriction (χ : IntegralCharacter)
    {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor ℤ X Y Z)
    (hT : IsRestriction (fun (_ _ _ : PUnit.{1}) => (1 : ℤ)) T) :
    0 < χ.value T := zero_lt_one.trans_le (χ.one_le_value_of_unitRestriction T hT)

/-- Every coefficient character takes an integral tensor power to the
corresponding ordinary real power, without a zero-one support assumption. -/
theorem value_power (χ : IntegralCharacter)
    {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor ℤ X Y Z) (n : ℕ) : χ.value (Tensor.power T n) = χ.value T ^ n := by
  induction n with
  | zero =>
    have heq : Tensor.power T 0 = Tensor.pullback
        (Equiv.equivPUnit (Fin 0 → X))
        (Equiv.equivPUnit (Fin 0 → Y))
        (Equiv.equivPUnit (Fin 0 → Z)) (fun (_ _ _ : PUnit.{1}) => (1 : ℤ)) := by
      funext x y z
      simp [Tensor.power, Tensor.pullback]
    rw [heq, χ.value_reindex, χ.map_one, pow_zero]
  | succ n ih =>
    have heq : Tensor.power T (n + 1) = Tensor.pullback
        (Fin.consEquiv (fun _ : Fin (n + 1) => X)).symm
        (Fin.consEquiv (fun _ : Fin (n + 1) => Y)).symm
        (Fin.consEquiv (fun _ : Fin (n + 1) => Z)).symm
        (Tensor.product T (Tensor.power T n)) := by
      funext x y z
      simp [Tensor.power, Tensor.pullback, Tensor.product, Fin.consEquiv,
        Fin.prod_univ_succ, Fin.tail]
    rw [heq, χ.value_reindex, χ.map_product, ih, pow_succ, mul_comm]

end IntegralCharacter
end
end Matmul
