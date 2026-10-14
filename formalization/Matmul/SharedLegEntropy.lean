import Matmul.IntegerCharacter
import Matmul.IntegralSeparator
import Matmul.EntropyAnalytic.Tag
import Matmul.PolynomialCoefficient

/-!
# Integral shared-leg separation and exact type restrictions

This module retains arbitrary branch tensors rather than assuming all sectors
contain the same tensor.  Its separator is an actual polynomial restriction
over the integers, with nonnegative powers on each individual leg.
-/

namespace Matmul.SharedLegEntropy

open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
open Matmul.IntegralSeparator
open scoped BigOperators

noncomputable section

variable {X Y Z : Type*} {M : ℕ}

/-- The first coordinate is shared, and the other two coordinates remember
    the matching branch label. -/
def sharedFirstTensor (B : Fin M → Tensor ℤ X Y Z) :
    Tensor ℤ X (Fin M × Y) (Fin M × Z) :=
  fun x y z => if y.1 = z.1 then B y.1 x y.2 z.2 else 0

def selectedBranches (B : Fin M → Tensor ℤ X Y Z) :
    Tensor ℤ (SepX M X) (SepY M Y) (SepZ M Z) :=
  Tensor.pullback mapX mapY mapZ
    (Tensor.product (sharedFirstTensor B) (convolution ℤ M))

theorem selectedBranches_apply (B : Fin M → Tensor ℤ X Y Z)
    (x : SepX M X) (y : SepY M Y) (z : SepZ M Z) :
    selectedBranches B x y z =
      if y.1 = z.1 ∧
        label y.2.2 - label z.2.2 + 2 * (label x.1 - label y.1) = 0
      then B y.1 x.2 y.2.1 z.2.1 else 0 := by
  change (if y.1 = z.1 then B y.1 x.2 y.2.1 z.2.1 else 0) *
    (if xIndex (label x.1) + yIndex M (label y.1) (label y.2.2) =
      zIndex M (label z.1) (label z.2.2) then 1 else 0) = _
  by_cases hyz : y.1 = z.1
  · simp only [← hyz, if_true, true_and, convolution_equation]
    split <;> simp_all
  · simp [hyz]

theorem selectedBranches_nonnegative_weight (B : Fin M → Tensor ℤ X Y Z)
    (x : SepX M X) (y : SepY M Y) (z : SepZ M Z)
    (h : selectedBranches B x y z ≠ 0) : 0 ≤ weight x y z := by
  rw [selectedBranches_apply] at h
  split at h
  · rename_i hp
    rw [weight_eq_square x y z hp.1 hp.2]
    exact sq_nonneg _
  · exact False.elim (h rfl)

def separationTarget (B : Fin M → Tensor ℤ X Y Z) :
    Tensor ℤ (SepX M X) (SepY M Y) (SepZ M Z) :=
  Tensor.directSum (fun g : Fin M =>
    fun (x : X) (y : Y × Fin M) (z : Z × Fin M) =>
      if y.2 = z.2 then B g x y.1 z.1 else 0)

theorem weight_zero_coefficient (B : Fin M → Tensor ℤ X Y Z) :
    (fun x y z => if weight x y z = 0 then selectedBranches B x y z else 0) =
      separationTarget B := by
  funext x y z
  unfold separationTarget Tensor.directSum
  rw [selectedBranches_apply]
  by_cases hyz : y.1 = z.1
  · by_cases heq : label y.2.2 - label z.2.2 +
        2 * (label x.1 - label y.1) = 0
    · have hw := weight_eq_square x y z hyz heq
      simp only [if_pos (show y.1 = z.1 ∧ label y.2.2 - label z.2.2 +
        2 * (label x.1 - label y.1) = 0 from ⟨hyz, heq⟩)]
      have hz : weight x y z = 0 ↔ x.1 = y.1 ∧ y.2.2 = z.2.2 := by
        rw [hw]
        constructor
        · intro h
          have hxy : label x.1 = label y.1 := by nlinarith [sq_nonneg (label x.1 - label y.1)]
          have huv : label y.2.2 = label z.2.2 := by omega
          exact ⟨label_injective hxy, label_injective huv⟩
        · rintro ⟨hxy, huv⟩
          simp [hxy]
      by_cases hxy : x.1 = y.1
      · by_cases huv : y.2.2 = z.2.2 <;> simp [hyz, hz, hxy, huv]
      · have hxz : x.1 ≠ z.1 := by simpa [← hyz] using hxy
        simp [hyz, hz, hxz]
    · simp only [if_neg (show ¬(y.1 = z.1 ∧ label y.2.2 - label z.2.2 +
        2 * (label x.1 - label y.1) = 0) from fun hp => heq hp.2), ite_self]
      have htarget : ¬ (x.1 = y.1 ∧ x.1 = z.1 ∧ y.2.2 = z.2.2) := by
        rintro ⟨hxy, _, huv⟩
        apply heq
        simp [hxy, huv]
      by_cases hxy : x.1 = y.1
      · have huv : y.2.2 ≠ z.2.2 := by
          intro huv
          exact htarget ⟨hxy, hxy.trans hyz, huv⟩
        simp [hyz, hxy, huv]
      · have hxz : x.1 ≠ z.1 := by simpa [← hyz] using hxy
        simp [hxz]
  · have htarget : ¬ (x.1 = y.1 ∧ x.1 = z.1) := by
      rintro ⟨hxy, hxz⟩
      exact hyz (hxy.symm.trans hxz)
    simp [hyz, htarget]

def branchPolynomial (B : Fin M → Tensor ℤ X Y Z) :
    Tensor (Polynomial ℤ) (SepX M X) (SepY M Y) (SepZ M Z) :=
  fun x y z => Polynomial.monomial (xExponent x) 1 *
    Polynomial.monomial (yExponent y) 1 *
    Polynomial.monomial (zExponent z) 1 * Polynomial.C (selectedBranches B x y z)

theorem branchPolynomial_apply (B : Fin M → Tensor ℤ X Y Z)
    (x : SepX M X) (y : SepY M Y) (z : SepZ M Z) :
    branchPolynomial B x y z =
      Polynomial.monomial (xExponent x + yExponent y + zExponent z)
        (selectedBranches B x y z) := by
  unfold branchPolynomial
  rw [← Polynomial.monomial_zero_left]
  simp only [Polynomial.monomial_mul_monomial, one_mul, Nat.add_zero]

theorem branchPolynomial_eq_restrict [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (B : Fin M → Tensor ℤ X Y Z) :
    branchPolynomial B = Tensor.restrict
      (fun x' x => if x = mapX x' then Polynomial.monomial (xExponent x') 1 else 0)
      (fun y' y => if y = mapY y' then Polynomial.monomial (yExponent y') 1 else 0)
      (fun z' z => if z = mapZ z' then Polynomial.monomial (zExponent z') 1 else 0)
      (fun x y z => Polynomial.C
        ((Tensor.product (sharedFirstTensor B) (convolution ℤ M)) x y z)) := by
  classical
  funext x y z
  simp [Tensor.restrict, branchPolynomial, selectedBranches, Tensor.pullback,
    ite_mul, mul_ite]

theorem branchPolynomial_coeff_below_shift (B : Fin M → Tensor ℤ X Y Z)
    {d : ℕ} (hd : d < shift M) :
    (fun x y z => (branchPolynomial B x y z).coeff d) = 0 := by
  funext x y z
  rw [branchPolynomial_apply, Polynomial.coeff_monomial]
  by_cases hT : selectedBranches B x y z = 0
  · simp [hT]
  · have hw := selectedBranches_nonnegative_weight B x y z hT
    have hid := exponent_weight_identity x y z
    have hne : xExponent x + yExponent y + zExponent z ≠ d := by omega
    simp [hne]

theorem branchPolynomial_leading (B : Fin M → Tensor ℤ X Y Z) :
    (fun x y z => (branchPolynomial B x y z).coeff (shift M)) =
      separationTarget B := by
  classical
  rw [← weight_zero_coefficient B]
  funext x y z
  rw [branchPolynomial_apply, Polynomial.coeff_monomial]
  have heq := exponent_eq_shift_iff x y z 0
  have heq' : xExponent x + yExponent y + zExponent z = shift M ↔ weight x y z = 0 := by
    simpa using heq
  simp only [heq']

theorem separationTarget_eq_product_directSum (B : Fin M → Tensor ℤ X Y Z) :
    separationTarget B = Tensor.pullback
      (Equiv.prodCongr (Equiv.refl (Fin M)) (Equiv.prodPUnit X).symm)
      (Equiv.refl _) (Equiv.refl _)
      (Tensor.directSum (fun g => Tensor.product (B g) (IntegerCharacter.dotX M))) := by
  funext x y z
  simp [separationTarget, Tensor.pullback, Tensor.product, Tensor.directSum,
    IntegerCharacter.dotX]
  split_ifs <;> simp_all

#print axioms branchPolynomial_eq_restrict
#print axioms branchPolynomial_leading

section Characters

variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]

/-- A generic coefficient-extraction backend.  Its premise is an actual
polynomial restriction and leading coefficient, not a tensor entropy bound. -/
def PolynomialRestrictionMonotone (φ : IntegralCharacter) : Prop :=
  ∀ {X Y Z U V W : Type} [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor ℤ X Y Z) (Utarget : Tensor ℤ U V W)
    (A : U → X → Polynomial ℤ) (B : V → Y → Polynomial ℤ)
    (C : W → Z → Polynomial ℤ) (ℓ : ℕ),
    (∀ d : ℕ, d < ℓ →
      (fun u v w => (Tensor.restrict A B C (fun x y z => Polynomial.C (T x y z))
        u v w).coeff d) = 0) →
    (fun u v w => (Tensor.restrict A B C (fun x y z => Polynomial.C (T x y z))
      u v w).coeff ℓ) = Utarget → φ.value Utarget ≤ φ.value T

/-- The coefficient-extraction backend is proved over the integers. -/
theorem polynomialRestrictionMonotone (φ : IntegralCharacter) :
    PolynomialRestrictionMonotone φ :=
  Matmul.PolynomialCoefficient.polynomialRestrictionMonotone φ

theorem value_separationTarget_le_product (φ : IntegralCharacter)
    (hdeg : PolynomialRestrictionMonotone φ) (B : Fin M → Tensor ℤ X Y Z) :
    φ.value (separationTarget B) ≤
      φ.value (Tensor.product (sharedFirstTensor B) (convolution ℤ M)) := by
  classical
  apply hdeg (Tensor.product (sharedFirstTensor B) (convolution ℤ M))
    (separationTarget B)
    (fun x' x => if x = mapX x' then Polynomial.monomial (xExponent x') 1 else 0)
    (fun y' y => if y = mapY y' then Polynomial.monomial (yExponent y') 1 else 0)
    (fun z' z => if z = mapZ z' then Polynomial.monomial (zExponent z') 1 else 0)
    (shift M)
  · intro d hd
    rw [← branchPolynomial_eq_restrict B]
    exact branchPolynomial_coeff_below_shift B hd
  · rw [← branchPolynomial_eq_restrict B]
    exact branchPolynomial_leading B

theorem value_separationTarget (φ : IntegralCharacter) (hM : 0 < M)
    (B : Fin M → Tensor ℤ X Y Z) :
    φ.value (separationTarget B) = (∑ h, φ.value (B h)) * (M : ℝ) ^ φ.pX := by
  rw [separationTarget_eq_product_directSum, φ.value_reindex, φ.map_directSum]
  simp only [φ.map_product, φ.value_dotX hM, Finset.sum_mul]

/-- Finite separation from the explicit integral separator and the generic
convolution bound. The two backend properties are separate from entropy. -/
theorem finiteSeparation_bound (φ : IntegralCharacter)
    (hdeg : PolynomialRestrictionMonotone φ)
    (hconv : ∀ M : ℕ, 0 < M → φ.value (convolution ℤ M) ≤ 5 * (M : ℝ))
    (hM : 0 < M) (B : Fin M → Tensor ℤ X Y Z) :
    (∑ h, φ.value (B h)) * (M : ℝ) ^ φ.pX ≤
      5 * (M : ℝ) * φ.value (sharedFirstTensor B) := by
  rw [← value_separationTarget φ hM B]
  calc
    φ.value (separationTarget B) ≤
        φ.value (Tensor.product (sharedFirstTensor B) (convolution ℤ M)) :=
      value_separationTarget_le_product φ hdeg B
    _ = φ.value (sharedFirstTensor B) * φ.value (convolution ℤ M) := φ.map_product _ _
    _ ≤ φ.value (sharedFirstTensor B) * (5 * (M : ℝ)) :=
      mul_le_mul_of_nonneg_left (hconv M hM) (φ.nonneg _)
    _ = _ := by ring

variable {s : ℕ}

def branchWordTensor (B : Fin s → Tensor ℤ X Y Z) {n : ℕ} (w : Fin n → Fin s) :
    Tensor ℤ (Fin n → X) (Fin n → Y) (Fin n → Z) :=
  fun x y z => ∏ i, B (w i) (x i) (y i) (z i)

theorem value_branchWordTensor (φ : IntegralCharacter)
    (B : Fin s → Tensor ℤ X Y Z) {n : ℕ} (w : Fin n → Fin s) :
    φ.value (branchWordTensor B w) = ∏ i, φ.value (B (w i)) := by
  induction n with
  | zero =>
      have hzero : branchWordTensor B w = Tensor.pullback
          (Equiv.equivPUnit (Fin 0 → X))
          (Equiv.equivPUnit (Fin 0 → Y))
          (Equiv.equivPUnit (Fin 0 → Z)) (fun (_ _ _ : PUnit.{1}) => (1 : ℤ)) := by
        funext x y z
        simp [branchWordTensor, Tensor.pullback]
      rw [hzero, φ.value_reindex, φ.map_one]
      simp
  | succ n ih =>
      have heq : branchWordTensor B w = Tensor.pullback
          (Fin.consEquiv (fun _ : Fin (n + 1) => X)).symm
          (Fin.consEquiv (fun _ : Fin (n + 1) => Y)).symm
          (Fin.consEquiv (fun _ : Fin (n + 1) => Z)).symm
          (Tensor.product (B (w 0)) (branchWordTensor B (Fin.tail w))) := by
        funext x y z
        simp [branchWordTensor, Tensor.pullback, Tensor.product, Fin.consEquiv,
          Fin.prod_univ_succ, Fin.tail]
      rw [heq, φ.value_reindex, φ.map_product, ih, Fin.prod_univ_succ]
      rfl

theorem value_exact_branchWordTensor (φ : IntegralCharacter)
    (B : Fin s → Tensor ℤ X Y Z) (counts : Fin s → ℕ) (w : ExactWords counts) :
    φ.value (branchWordTensor B w.val) = ∏ a, φ.value (B a) ^ counts a := by
  rw [value_branchWordTensor,
    ← Fintype.prod_fiberwise' w.val (fun a => φ.value (B a))]
  simp only [Finset.prod_const, Finset.card_univ]
  apply Finset.prod_congr rfl
  intro a _
  rw [show Fintype.card {i // w.val i = a} = counts a from w.property a]

def typeWordCoordinate (counts : Fin s → ℕ)
    (e : Fin (Fintype.card (ExactWords counts)) ≃ ExactWords counts)
    {U : Type} (y : Fin (Fintype.card (ExactWords counts)) ×
      (Fin (∑ a, counts a) → U)) : Fin (∑ a, counts a) → (Fin s × U) :=
  fun i => ((e y.1).val i, y.2 i)

omit [Fintype X] [Fintype Y] [Fintype Z] in
theorem exactType_power_pullback (B : Fin s → Tensor ℤ X Y Z)
    (counts : Fin s → ℕ)
    (e : Fin (Fintype.card (ExactWords counts)) ≃ ExactWords counts) :
    Tensor.pullback id (typeWordCoordinate counts e) (typeWordCoordinate counts e)
        (Tensor.power (sharedFirstTensor B) (∑ a, counts a)) =
      sharedFirstTensor (fun h => branchWordTensor B (e h).val) := by
  funext x y z
  by_cases h : y.1 = z.1
  · simp [Tensor.pullback, Tensor.power, typeWordCoordinate, sharedFirstTensor,
      branchWordTensor, h]
  · have hword : (e y.1).val ≠ (e z.1).val := by
      intro heq
      exact h (e.injective (Subtype.ext heq))
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hword
    simp only [Tensor.pullback, Tensor.power, sharedFirstTensor, h, ↓reduceIte,
      typeWordCoordinate, id_eq]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

theorem value_power (φ : IntegralCharacter) (T : Tensor ℤ X Y Z) (n : ℕ) :
    φ.value (Tensor.power T n) = φ.value T ^ n := by
  have heq : Tensor.power T n = branchWordTensor (fun _ : Fin 1 => T) (fun _ => 0) := rfl
  rw [heq, value_branchWordTensor]
  simp

theorem exactType_value_le_power (φ : IntegralCharacter)
    (B : Fin s → Tensor ℤ X Y Z) (counts : Fin s → ℕ)
    (e : Fin (Fintype.card (ExactWords counts)) ≃ ExactWords counts) :
    φ.value (sharedFirstTensor (fun h => branchWordTensor B (e h).val)) ≤
      φ.value (sharedFirstTensor B) ^ (∑ a, counts a) := by
  rw [← exactType_power_pullback B counts e, ← value_power]
  exact φ.value_pullback_le _ _ _ _

theorem integral_type_comparison (φ : IntegralCharacter)
    (hdeg : PolynomialRestrictionMonotone φ)
    (hconv : ∀ M : ℕ, 0 < M → φ.value (convolution ℤ M) ≤ 5 * (M : ℝ))
    (B : Fin s → Tensor ℤ X Y Z) (counts : Fin s → ℕ) :
    (Fintype.card (ExactWords counts) : ℝ) ^ φ.pX *
        ∏ a, φ.value (B a) ^ counts a ≤
      5 * φ.value (sharedFirstTensor B) ^ (∑ a, counts a) := by
  classical
  let M := Fintype.card (ExactWords counts)
  let e : Fin M ≃ ExactWords counts := (Fintype.equivFin _).symm
  let W : Fin M → Tensor ℤ (Fin (∑ a, counts a) → X)
      (Fin (∑ a, counts a) → Y) (Fin (∑ a, counts a) → Z) :=
    fun h => branchWordTensor B (e h).val
  have hM : 0 < M := by
    simpa only [M, Fintype.card_eq_nat_card] using exactWords_card_pos counts
  have hsep : ((M : ℝ) * ∏ a, φ.value (B a) ^ counts a) * (M : ℝ) ^ φ.pX ≤
      5 * (M : ℝ) * φ.value (sharedFirstTensor W) := by
    simpa only [W, value_exact_branchWordTensor, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
      finiteSeparation_bound φ hdeg hconv hM W
  have hsource : φ.value (sharedFirstTensor W) ≤
      φ.value (sharedFirstTensor B) ^ (∑ a, counts a) :=
    exactType_value_le_power φ B counts e
  have hcancel : (M : ℝ) *
      ((M : ℝ) ^ φ.pX * ∏ a, φ.value (B a) ^ counts a) ≤
        (M : ℝ) * (5 * φ.value (sharedFirstTensor B) ^ (∑ a, counts a)) := by
    calc
      _ = ((M : ℝ) * ∏ a, φ.value (B a) ^ counts a) * (M : ℝ) ^ φ.pX := by ring
      _ ≤ 5 * (M : ℝ) * φ.value (sharedFirstTensor W) := hsep
      _ ≤ 5 * (M : ℝ) * φ.value (sharedFirstTensor B) ^ (∑ a, counts a) :=
        mul_le_mul_of_nonneg_left hsource (by positivity)
      _ = _ := by ring
  exact (mul_le_mul_iff_right₀ (Nat.cast_pos.mpr hM : (0 : ℝ) < M)).mp hcancel

/-- Once the generic integral backends are supplied, the entropy inequality
    follows from the proved exact-type restriction and counting limit. -/
theorem log_sharedFirst_tag (φ : IntegralCharacter)
    (hdeg : PolynomialRestrictionMonotone φ)
    (hconv : ∀ M : ℕ, 0 < M → φ.value (convolution ℤ M) ≤ 5 * (M : ℝ))
    (q : FiniteLaw (Fin s)) (B : Fin s → Tensor ℤ X Y Z)
    (hB : ∀ a, 0 < φ.value (B a)) :
    φ.pX * finiteEntropy q.mass + ∑ a, q.mass a * Real.log (φ.value (B a)) ≤
      Real.log (φ.value (sharedFirstTensor B)) := by
  have hs : 0 < s := by
    by_contra hn
    have hs0 : s = 0 := Nat.eq_zero_of_not_pos hn
    subst s
    have htotal := q.total
    simp at htotal
  have hsource : 0 < φ.value (sharedFirstTensor B) := by
    let a : Fin s := ⟨0, hs⟩
    have heq : Tensor.pullback id (fun y => (a, y)) (fun z => (a, z))
        (sharedFirstTensor B) = B a := by
      funext x y z
      simp [Tensor.pullback, sharedFirstTensor]
    have hm := φ.value_pullback_le (sharedFirstTensor B) id
      (fun y => (a, y)) (fun z => (a, z))
    rw [heq] at hm
    exact (hB a).trans_le hm
  apply OAI.MatrixMultiplication.AuxiliarySeparation.log_tag_of_integral_bounds
    q (fun a => φ.value (B a)) φ.pX (φ.value (sharedFirstTensor B)) 5 hB hsource (by norm_num)
  intro counts _
  simpa only [Fintype.card_eq_nat_card] using integral_type_comparison φ hdeg hconv B counts

theorem sharedFirst_tag (φ : IntegralCharacter)
    (hdeg : PolynomialRestrictionMonotone φ)
    (hconv : ∀ M : ℕ, 0 < M → φ.value (convolution ℤ M) ≤ 5 * (M : ℝ))
    (q : FiniteLaw (Fin s)) (B : Fin s → Tensor ℤ X Y Z)
    (hB : ∀ a, 0 < φ.value (B a)) :
    Real.exp (φ.pX * finiteEntropy q.mass) *
        ∏ a, φ.value (B a) ^ q.mass a ≤ φ.value (sharedFirstTensor B) := by
  have hlog := log_sharedFirst_tag φ hdeg hconv q B hB
  have he := Real.exp_le_exp.mpr hlog
  rw [Real.exp_add, Real.exp_sum] at he
  have hprod : (∏ a, Real.exp (q.mass a * Real.log (φ.value (B a)))) =
      ∏ a, φ.value (B a) ^ q.mass a := by
    apply Finset.prod_congr rfl
    intro a _
    rw [Real.rpow_def_of_pos (hB a), mul_comm]
  rw [hprod] at he
  by_cases hsource : 0 < φ.value (sharedFirstTensor B)
  · simpa only [Real.exp_log hsource] using he
  · have hn := φ.nonneg (sharedFirstTensor B)
    have hz : φ.value (sharedFirstTensor B) = 0 := by linarith
    have hpos : 0 < Real.exp (φ.pX * finiteEntropy q.mass) *
        ∏ a, φ.value (B a) ^ q.mass a :=
      mul_pos (Real.exp_pos _) (Finset.prod_pos (fun a _ => Real.rpow_pos_of_pos (hB a) _))
    have hs : 0 < s := by
      by_contra hn
      have hs0 : s = 0 := Nat.eq_zero_of_not_pos hn
      subst s
      have htotal := q.total
      simp at htotal
    let a : Fin s := ⟨0, hs⟩
    have heq : Tensor.pullback id (fun y => (a, y)) (fun z => (a, z))
        (sharedFirstTensor B) = B a := by
      funext x y z
      simp [Tensor.pullback, sharedFirstTensor]
    have hm := φ.value_pullback_le (sharedFirstTensor B) id
      (fun y => (a, y)) (fun z => (a, z))
    rw [heq, hz] at hm
    exact False.elim (not_le_of_gt (hB a) hm)

#print axioms integral_type_comparison
#print axioms log_sharedFirst_tag

end Characters


section Padding

open Classical

variable {M : ℕ} {X : Type} {Y Z : Fin M → Type}
variable [Fintype X] [∀ i, Fintype (Y i)] [∀ i, Fintype (Z i)]

theorem value_extendByZero (φ : IntegralCharacter)
    {U V W A B C : Type} [Fintype U] [Fintype V] [Fintype W]
    [Fintype A] [Fintype B] [Fintype C]
    (T : Tensor ℤ U V W) (fx : U → A) (fy : V → B) (fz : W → C)
    (hfx : Function.Injective fx) (hfy : Function.Injective fy) (hfz : Function.Injective fz) :
    φ.value (Tensor.restrict (fun x' x => if fx x = x' then 1 else 0)
      (fun y' y => if fy y = y' then 1 else 0)
      (fun z' z => if fz z = z' then 1 else 0) T) = φ.value T := by
  apply le_antisymm (φ.monotone _ _ _ _)
  have heq : Tensor.pullback fx fy fz
      (Tensor.restrict (fun x' x => if fx x = x' then 1 else 0)
        (fun y' y => if fy y = y' then 1 else 0)
        (fun z' z => if fz z = z' then 1 else 0) T) = T := by
    funext x y z
    simp [Tensor.pullback, Tensor.restrict, hfx.eq_iff, hfy.eq_iff, hfz.eq_iff,
      ite_mul, mul_ite]
  have hp := φ.value_pullback_le
    (Tensor.restrict (fun x' x => if fx x = x' then 1 else 0)
      (fun y' y => if fy y = y' then 1 else 0)
      (fun z' z => if fz z = z' then 1 else 0) T) fx fy fz
  rwa [heq] at hp

/- The following padding identities reuse the integral algebraic proofs from
OpenAI's Tensor/SharedPadding; they use no division or field structure. -/
/-- Branches sharing their first input but with independently sized other legs. -/
def sharedFirstDependentTensor (B : ∀ i, Tensor ℤ X (Y i) (Z i)) :
    Tensor ℤ X (Σ i, Y i) (Σ i, Z i) :=
  fun x y z => if h : z.1 = y.1 then B y.1 x y.2 (h ▸ z.2) else 0

/-- A branch in the two common sigma coordinate spaces, with zero padding. -/
def paddedSharedBranch (B : ∀ i, Tensor ℤ X (Y i) (Z i)) (i : Fin M) :
    Tensor ℤ X (Σ i, Y i) (Σ i, Z i) :=
  Tensor.restrict (fun x' x => if x = x' then 1 else 0)
    (fun y b => if Sigma.mk i b = y then 1 else 0)
    (fun z c => if Sigma.mk i c = z then 1 else 0) (B i)

omit [Fintype X] [∀ i, Fintype (Y i)] [∀ i, Fintype (Z i)] in
@[simp] theorem sharedFirstDependentTensor_matching
    (B : ∀ i, Tensor ℤ X (Y i) (Z i)) (i : Fin M)
    (x : X) (y : Y i) (z : Z i) :
    sharedFirstDependentTensor B x ⟨i, y⟩ ⟨i, z⟩ = B i x y z := by
  simp [sharedFirstDependentTensor]

@[simp] theorem paddedSharedBranch_matching
    (B : ∀ i, Tensor ℤ X (Y i) (Z i)) (i : Fin M)
    (x : X) (y : Y i) (z : Z i) :
    paddedSharedBranch B i x ⟨i, y⟩ ⟨i, z⟩ = B i x y z := by
  simp [paddedSharedBranch, Tensor.restrict, ite_mul, mul_ite]

theorem paddedSharedBranch_pullback
    (B : ∀ i, Tensor ℤ X (Y i) (Z i)) (i : Fin M) :
    Tensor.pullback id (Sigma.mk i) (Sigma.mk i) (paddedSharedBranch B i) = B i := by
  funext x y z
  exact paddedSharedBranch_matching B i x y z

/-- A nonzero branch remains nonzero after padding. -/
theorem paddedSharedBranch_ne_zero
    (B : ∀ i, Tensor ℤ X (Y i) (Z i)) (i : Fin M) (hB : B i ≠ 0) :
    paddedSharedBranch B i ≠ 0 := by
  intro h
  apply hB
  rw [← paddedSharedBranch_pullback B i, h]
  rfl

theorem paddedSharedBranch_zero_middle
    (B : ∀ i, Tensor ℤ X (Y i) (Z i)) (i : Fin M)
    (x : X) (y : Σ i, Y i) (z : Σ i, Z i) (hy : y.1 ≠ i) :
    paddedSharedBranch B i x y z = 0 := by
  have hzero : ∀ b : Y i, Sigma.mk i b ≠ y :=
    fun b h => hy (congrArg Sigma.fst h).symm
  simp [paddedSharedBranch, Tensor.restrict, hzero]

theorem paddedSharedBranch_zero_right
    (B : ∀ i, Tensor ℤ X (Y i) (Z i)) (i : Fin M)
    (x : X) (y : Σ i, Y i) (z : Σ i, Z i) (hz : z.1 ≠ i) :
    paddedSharedBranch B i x y z = 0 := by
  have hzero : ∀ c : Z i, Sigma.mk i c ≠ z :=
    fun c h => hz (congrArg Sigma.fst h).symm
  simp [paddedSharedBranch, Tensor.restrict, hzero]

/-- Redundant branch labels zero-extend the varying-dimension shared tensor. -/
theorem sharedFirstTensor_paddedSharedBranch
    (B : ∀ i, Tensor ℤ X (Y i) (Z i)) :
    sharedFirstTensor (paddedSharedBranch B) = Tensor.restrict
      (fun (x' : X) x => if x = x' then 1 else 0)
      (fun (y' : Fin M × (Σ i, Y i)) y => if (y.1, y) = y' then 1 else 0)
      (fun (z' : Fin M × (Σ i, Z i)) z => if (z.1, z) = z' then 1 else 0)
      (sharedFirstDependentTensor B) := by
  funext x' y' z'
  rcases y' with ⟨i, ⟨iy, y⟩⟩
  rcases z' with ⟨j, ⟨iz, z⟩⟩
  have hgraph {A : Type} (f : A → Fin M) (a x : A) (i : Fin M) :
      (f a, a) = (i, x) ↔ a = x ∧ f x = i := by
    constructor
    · intro h
      have ha : a = x := congrArg Prod.snd h
      refine ⟨ha, ?_⟩
      rw [← ha]
      exact congrArg Prod.fst h
    · rintro ⟨rfl, h⟩
      simp [h]
  simp only [Tensor.restrict, hgraph, ite_and]
  simp only [ite_mul, zero_mul, mul_ite, mul_zero]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  by_cases hi : iy = i
  · subst iy
    by_cases hz : iz = i
    · subst iz
      by_cases hij : i = j
      · subst j
        simp [sharedFirstTensor, sharedFirstDependentTensor]
      · simp [sharedFirstTensor, hij]
    · simp [sharedFirstTensor, sharedFirstDependentTensor,
        paddedSharedBranch_zero_right B i x' ⟨i, y⟩ ⟨iz, z⟩ hz, hz]
  · simp [sharedFirstTensor,
      paddedSharedBranch_zero_middle B i x' ⟨iy, y⟩ ⟨iz, z⟩ hi, hi]
/-- Padding a branch changes no character value. -/
@[simp] theorem value_paddedSharedBranch (χ : IntegralCharacter)
    (B : ∀ i, Tensor ℤ X (Y i) (Z i)) (i : Fin M) :
    χ.value (paddedSharedBranch B i) = χ.value (B i) := by
  apply le_antisymm (χ.monotone (B i) _ _ _)
  have hp := χ.value_pullback_le (paddedSharedBranch B i) id (Sigma.mk i) (Sigma.mk i)
  rwa [paddedSharedBranch_pullback] at hp

/-- Passing to uniform ambient branch spaces adds no character cost. -/
@[simp] theorem value_sharedFirstTensor_padded (χ : IntegralCharacter)
    (B : ∀ i, Tensor ℤ X (Y i) (Z i)) :
    χ.value (sharedFirstTensor (paddedSharedBranch B)) =
      χ.value (sharedFirstDependentTensor B) := by
  rw [sharedFirstTensor_paddedSharedBranch]
  have hp := value_extendByZero χ (sharedFirstDependentTensor B) id
      (fun y => (y.1, y)) (fun z => (z.1, z)) Function.injective_id
      (fun _ _ h => congrArg Prod.snd h) (fun _ _ h => congrArg Prod.snd h)
  convert hp using 1
  congr 1
  funext x y z
  simp [Tensor.restrict]


theorem sharedFirstDependent_tag (φ : IntegralCharacter)
    (hdeg : PolynomialRestrictionMonotone φ)
    (hconv : ∀ M : ℕ, 0 < M → φ.value (convolution ℤ M) ≤ 5 * (M : ℝ))
    (q : FiniteLaw (Fin M)) (B : ∀ a, Tensor ℤ X (Y a) (Z a))
    (hB : ∀ a, 0 < φ.value (B a)) :
    Real.exp (φ.pX * finiteEntropy q.mass) *
        ∏ a, φ.value (B a) ^ q.mass a ≤ φ.value (sharedFirstDependentTensor B) := by
  simpa only [value_paddedSharedBranch, value_sharedFirstTensor_padded] using
    sharedFirst_tag φ hdeg hconv q (paddedSharedBranch B)
      (fun a => by simpa only [value_paddedSharedBranch] using hB a)

theorem log_sharedFirstDependent_tag (φ : IntegralCharacter)
    (hdeg : PolynomialRestrictionMonotone φ)
    (hconv : ∀ M : ℕ, 0 < M → φ.value (convolution ℤ M) ≤ 5 * (M : ℝ))
    (q : FiniteLaw (Fin M)) (B : ∀ a, Tensor ℤ X (Y a) (Z a))
    (hB : ∀ a, 0 < φ.value (B a)) :
    φ.pX * finiteEntropy q.mass + ∑ a, q.mass a * Real.log (φ.value (B a)) ≤
      Real.log (φ.value (sharedFirstDependentTensor B)) := by
  simpa only [value_paddedSharedBranch, value_sharedFirstTensor_padded] using
    log_sharedFirst_tag φ hdeg hconv q (paddedSharedBranch B)
      (fun a => by simpa only [value_paddedSharedBranch] using hB a)

#print axioms sharedFirstDependent_tag

end Padding

end
end Matmul.SharedLegEntropy
