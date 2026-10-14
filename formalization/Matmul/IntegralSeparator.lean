import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensor
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# An integral separator for a shared tensor leg

All coordinate maps and weights below are integral.  The coefficient theorem is
valid over an arbitrary commutative semiring, without division or characteristic
assumptions.  The parameter `M` is arbitrary and positive, not a fixed example.
-/

namespace Matmul.IntegralSeparator

open OAI.MatrixMultiplication.Foundation
open scoped BigOperators

def label {M : ℕ} (g : Fin M) : ℤ := (g.val : ℤ) + 1

theorem label_bounds {M : ℕ} (g : Fin M) :
    1 ≤ label g ∧ label g ≤ (M : ℤ) := by
  unfold label
  have := g.isLt
  omega

theorem label_injective {M : ℕ} : Function.Injective (@label M) := by
  intro g h heq
  apply Fin.ext
  unfold label at heq
  omega

def xIndex (g : ℤ) : ℤ := 2 * g - 2
def yIndex (M h u : ℤ) : ℤ := u - h + M - 1
def zIndex (M h v : ℤ) : ℤ := v + h + M - 3

theorem xIndex_bounds {M g : ℤ} (hg : 1 ≤ g ∧ g ≤ M) :
    0 ≤ xIndex g ∧ xIndex g < 2 * M - 1 := by
  unfold xIndex
  omega

theorem yIndex_bounds {M h u : ℤ}
    (hh : 1 ≤ h ∧ h ≤ M) (hu : 1 ≤ u ∧ u ≤ M) :
    0 ≤ yIndex M h u ∧ yIndex M h u < 2 * M - 1 := by
  unfold yIndex
  omega

theorem zIndex_bounds {M h v : ℤ}
    (hh : 1 ≤ h ∧ h ≤ M) (hv : 1 ≤ v ∧ v ≤ M) :
    0 ≤ zIndex M h v ∧ zIndex M h v < 4 * M - 3 := by
  unfold zIndex
  omega

theorem convolution_equation {M g h u v : ℤ} :
    xIndex g + yIndex M h u = zIndex M h v ↔
      u - v + 2 * (g - h) = 0 := by
  unfold xIndex yIndex zIndex
  omega

theorem square_weight {g h u v : ℤ}
    (heq : u - v + 2 * (g - h) = 0) :
    g ^ 2 + h * u - h ^ 2 - h * v = (g - h) ^ 2 := by
  have hm := congrArg (fun t : ℤ => h * t) heq
  nlinarith

theorem square_weight_nonneg {g h u v : ℤ}
    (heq : u - v + 2 * (g - h) = 0) :
    0 ≤ g ^ 2 + h * u - h ^ 2 - h * v := by
  rw [square_weight heq]
  exact sq_nonneg _

theorem square_weight_zero_iff {g h u v : ℤ}
    (heq : u - v + 2 * (g - h) = 0) :
    g ^ 2 + h * u - h ^ 2 - h * v = 0 ↔ g = h ∧ u = v := by
  rw [square_weight heq]
  constructor
  · intro hw
    have hgh : g = h := by nlinarith [sq_nonneg (g - h)]
    exact ⟨hgh, by omega⟩
  · rintro ⟨rfl, rfl⟩
    simp

abbrev ConvInput (M : ℕ) := Set.Ico (0 : ℤ) (2 * (M : ℤ) - 1)
abbrev ConvOutput (M : ℕ) := Set.Ico (0 : ℤ) (4 * (M : ℤ) - 3)

theorem card_convInput (M : ℕ) (hM : 0 < M) :
    Fintype.card (ConvInput M) = 2 * M - 1 := by
  have h := Int.card_fintype_Ico_of_le
    (a := 0) (b := 2 * (M : ℤ) - 1) (by omega)
  change (Fintype.card (ConvInput M) : ℤ) = 2 * (M : ℤ) - 1 - 0 at h
  omega

theorem card_convOutput (M : ℕ) (hM : 0 < M) :
    Fintype.card (ConvOutput M) = 4 * M - 3 := by
  have h := Int.card_fintype_Ico_of_le
    (a := 0) (b := 4 * (M : ℤ) - 3) (by omega)
  change (Fintype.card (ConvOutput M) : ℤ) = 4 * (M : ℤ) - 3 - 0 at h
  omega

def selectX {M : ℕ} (g : Fin M) : ConvInput M :=
  ⟨xIndex (label g), xIndex_bounds (label_bounds g)⟩

def selectY {M : ℕ} (h u : Fin M) : ConvInput M :=
  ⟨yIndex M (label h) (label u), yIndex_bounds (label_bounds h) (label_bounds u)⟩

def selectZ {M : ℕ} (h v : Fin M) : ConvOutput M :=
  ⟨zIndex M (label h) (label v), zIndex_bounds (label_bounds h) (label_bounds v)⟩

section Tensors

variable {K X Y Z : Type*} [CommSemiring K] {M : ℕ}

/-- The sector index is shared by the second and third legs only. -/
def sharedSector (T : Tensor K X Y Z) :
    Tensor K X (Fin M × Y) (Fin M × Z) :=
  fun x y z => if y.1 = z.1 then T x y.2 z.2 else 0

/-- Ordinary, untruncated polynomial convolution with input length `2M-1`. -/
def convolution (K : Type*) [CommSemiring K] (M : ℕ) :
    Tensor K (ConvInput M) (ConvInput M) (ConvOutput M) :=
  fun i j k => if i.val + j.val = k.val then 1 else 0

abbrev SepX (M : ℕ) (X : Type*) := Fin M × X
abbrev SepY (M : ℕ) (Y : Type*) := Fin M × (Y × Fin M)
abbrev SepZ (M : ℕ) (Z : Type*) := Fin M × (Z × Fin M)

def mapX (x : SepX M X) : X × ConvInput M := (x.2, selectX x.1)
def mapY (y : SepY M Y) : (Fin M × Y) × ConvInput M :=
  ((y.1, y.2.1), selectY y.1 y.2.2)
def mapZ (z : SepZ M Z) : (Fin M × Z) × ConvOutput M :=
  ((z.1, z.2.1), selectZ z.1 z.2.2)

/-- The tensor obtained by selecting actual coordinates from the product. -/
def selectedTensor (T : Tensor K X Y Z) :
    Tensor K (SepX M X) (SepY M Y) (SepZ M Z) :=
  Tensor.pullback mapX mapY mapZ
    (Tensor.product (sharedSector T) (convolution K M))

theorem selectedTensor_apply (T : Tensor K X Y Z)
    (x : SepX M X) (y : SepY M Y) (z : SepZ M Z) :
    selectedTensor T x y z =
      if y.1 = z.1 ∧
        label y.2.2 - label z.2.2 + 2 * (label x.1 - label y.1) = 0
      then T x.2 y.2.1 z.2.1 else 0 := by
  change (if y.1 = z.1 then T x.2 y.2.1 z.2.1 else 0) *
    (if xIndex (label x.1) + yIndex M (label y.1) (label y.2.2) =
      zIndex M (label z.1) (label z.2.2) then 1 else 0) = _
  by_cases hyz : y.1 = z.1
  · simp only [← hyz, if_true, true_and, convolution_equation]
    split <;> simp_all
  · simp [hyz]

/-- Explicit Kronecker-delta restriction matrices, rather than an assumed
    relation between the source and the selected tensor. -/
theorem selectedTensor_eq_restrict [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (T : Tensor K X Y Z) :
    selectedTensor T = Tensor.restrict
      (fun x' x => if x = mapX x' then 1 else 0)
      (fun y' y => if y = mapY y' then 1 else 0)
      (fun z' z => if z = mapZ z' then 1 else 0)
      (Tensor.product (sharedSector T) (convolution K M)) := by
  classical
  exact Tensor.pullback_eq_restrict mapX mapY mapZ _

/-- Each summand depends on just one target leg, so these are admissible
    diagonal degeneration weights. -/
def xWeight (x : SepX M X) : ℤ := label x.1 ^ 2
def yWeight (y : SepY M Y) : ℤ :=
  label y.1 * label y.2.2 - label y.1 ^ 2
def zWeight (z : SepZ M Z) : ℤ := -(label z.1 * label z.2.2)
def weight (x : SepX M X) (y : SepY M Y) (z : SepZ M Z) : ℤ :=
  xWeight x + yWeight y + zWeight z

theorem weight_eq_square (x : SepX M X) (y : SepY M Y) (z : SepZ M Z)
    (hyz : y.1 = z.1)
    (heq : label y.2.2 - label z.2.2 +
      2 * (label x.1 - label y.1) = 0) :
    weight x y z = (label x.1 - label y.1) ^ 2 := by
  unfold weight xWeight yWeight zWeight
  rw [← hyz]
  have h := square_weight heq
  linear_combination h

theorem selectedTensor_nonnegative_weight (T : Tensor K X Y Z)
    (x : SepX M X) (y : SepY M Y) (z : SepZ M Z)
    (h : selectedTensor T x y z ≠ 0) : 0 ≤ weight x y z := by
  rw [selectedTensor_apply] at h
  split at h
  · rename_i hp
    rw [weight_eq_square x y z hp.1 hp.2]
    exact sq_nonneg _
  · exact False.elim (h rfl)

/-- Degree coefficients of the integral diagonal weight family.  The preceding
    theorem proves that every nonzero coefficient has nonnegative degree. -/
def filteredCoefficient (T : Tensor K X Y Z) (d : ℕ) :
    Tensor K (SepX M X) (SepY M Y) (SepZ M Z) :=
  fun x y z => if weight x y z = (d : ℤ) then selectedTensor T x y z else 0

/-- `M` separate copies of `T` with an additional diagonal leg of size `M`. -/
def separatedTensor (T : Tensor K X Y Z) :
    Tensor K (SepX M X) (SepY M Y) (SepZ M Z) :=
  Tensor.directSum (fun _ : Fin M =>
    fun (x : X) (y : Y × Fin M) (z : Z × Fin M) =>
      if y.2 = z.2 then T x y.1 z.1 else 0)

theorem filteredCoefficient_zero (T : Tensor K X Y Z) :
    filteredCoefficient (M := M) T 0 = separatedTensor T := by
  funext x y z
  unfold filteredCoefficient separatedTensor Tensor.directSum
  rw [selectedTensor_apply]
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

/-- A uniform shift makes the three individual leg weights nonnegative. -/
def shift (M : ℕ) : ℕ := 2 * M ^ 2

def xExponent (x : SepX M X) : ℕ := (xWeight x).toNat
def yExponent (y : SepY M Y) : ℕ := (yWeight y + (M : ℤ) ^ 2).toNat
def zExponent (z : SepZ M Z) : ℕ := (zWeight z + (M : ℤ) ^ 2).toNat

theorem yWeight_shift_nonneg (y : SepY M Y) :
    0 ≤ yWeight y + (M : ℤ) ^ 2 := by
  have hh := label_bounds y.1
  have hu := label_bounds y.2.2
  have hhM : label y.1 ^ 2 ≤ (M : ℤ) ^ 2 := by
    nlinarith [sq_nonneg ((M : ℤ) - label y.1)]
  have hhu : 0 ≤ label y.1 * label y.2.2 :=
    mul_nonneg (by omega) (by omega)
  unfold yWeight
  omega

theorem zWeight_shift_nonneg (z : SepZ M Z) :
    0 ≤ zWeight z + (M : ℤ) ^ 2 := by
  have hh := label_bounds z.1
  have hv := label_bounds z.2.2
  have hhv : label z.1 * label z.2.2 ≤ (M : ℤ) * (M : ℤ) :=
    mul_le_mul hh.2 hv.2 (by omega) (by omega)
  unfold zWeight
  nlinarith

theorem exponent_weight_identity
    (x : SepX M X) (y : SepY M Y) (z : SepZ M Z) :
    ((xExponent x + yExponent y + zExponent z : ℕ) : ℤ) =
      weight x y z + shift M := by
  have hx : 0 ≤ xWeight x := sq_nonneg _
  simp only [xExponent, yExponent, zExponent, Nat.cast_add,
    Int.toNat_of_nonneg hx, Int.toNat_of_nonneg (yWeight_shift_nonneg y),
    Int.toNat_of_nonneg (zWeight_shift_nonneg z)]
  unfold weight shift
  push_cast
  ring

theorem exponent_eq_shift_iff (x : SepX M X) (y : SepY M Y) (z : SepZ M Z)
    (d : ℕ) :
    xExponent x + yExponent y + zExponent z = shift M + d ↔
      weight x y z = (d : ℤ) := by
  have h := exponent_weight_identity x y z
  omega

/-- An actual polynomial tensor family, with separated nonnegative powers on
    its three legs.  Its first possible degree is `shift M`. -/
noncomputable def polynomialFamily (T : Tensor K X Y Z) :
    Tensor (Polynomial K) (SepX M X) (SepY M Y) (SepZ M Z) :=
  fun x y z => Polynomial.monomial (xExponent x) 1 *
    Polynomial.monomial (yExponent y) 1 *
    Polynomial.monomial (zExponent z) 1 * Polynomial.C (selectedTensor T x y z)

theorem polynomialFamily_apply (T : Tensor K X Y Z)
    (x : SepX M X) (y : SepY M Y) (z : SepZ M Z) :
    polynomialFamily T x y z =
      Polynomial.monomial (xExponent x + yExponent y + zExponent z)
        (selectedTensor T x y z) := by
  unfold polynomialFamily
  rw [← Polynomial.monomial_zero_left]
  simp [Polynomial.monomial_mul_monomial]

/-- The family is obtained by restriction matrices over `K[t]`; the matrices
    explicitly have one monomial in each selected coordinate. -/
theorem polynomialFamily_eq_restrict [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (T : Tensor K X Y Z) :
    polynomialFamily (M := M) T = Tensor.restrict
      (fun x' x => if x = mapX x' then Polynomial.monomial (xExponent x') 1 else 0)
      (fun y' y => if y = mapY y' then Polynomial.monomial (yExponent y') 1 else 0)
      (fun z' z => if z = mapZ z' then Polynomial.monomial (zExponent z') 1 else 0)
      (fun x y z => Polynomial.C
        ((Tensor.product (sharedSector T) (convolution K M)) x y z)) := by
  classical
  funext x y z
  simp [Tensor.restrict, polynomialFamily, selectedTensor, Tensor.pullback,
    ite_mul, mul_ite]

/-- Every degree coefficient agrees with the integral weight filtration. -/
theorem polynomialFamily_coeff_shift (T : Tensor K X Y Z) (d : ℕ) :
    (fun x y z => (polynomialFamily (M := M) T x y z).coeff (shift M + d)) =
      filteredCoefficient T d := by
  funext x y z
  rw [polynomialFamily_apply, Polynomial.coeff_monomial]
  simp [filteredCoefficient, exponent_eq_shift_iff]

/-- Coefficients preceding the claimed leading degree vanish. -/
theorem polynomialFamily_coeff_below_shift (T : Tensor K X Y Z)
    {d : ℕ} (hd : d < shift M) :
    (fun x y z => (polynomialFamily (M := M) T x y z).coeff d) = 0 := by
  funext x y z
  rw [polynomialFamily_apply, Polynomial.coeff_monomial]
  by_cases hT : selectedTensor T x y z = 0
  · simp [hT]
  · have hw := selectedTensor_nonnegative_weight T x y z hT
    have hid := exponent_weight_identity x y z
    have hne : xExponent x + yExponent y + zExponent z ≠ d := by omega
    simp [hne]

/-- Integral polynomial degeneration to the desired separated tensor. -/
theorem polynomialFamily_leading_coefficient (T : Tensor K X Y Z) :
    (fun x y z => (polynomialFamily (M := M) T x y z).coeff (shift M)) =
      separatedTensor T := by
  simpa using (polynomialFamily_coeff_shift T 0).trans (filteredCoefficient_zero T)

/-- The integral construction commutes with any coefficient change, including
    reduction to positive characteristic. -/
theorem filteredCoefficient_map {L : Type*} [CommSemiring L]
    (f : K →+* L) (T : Tensor K X Y Z) (d : ℕ) :
    filteredCoefficient (M := M) (fun x y z => f (T x y z)) d =
      fun x y z => f (filteredCoefficient T d x y z) := by
  funext x y z
  simp only [filteredCoefficient, selectedTensor_apply]
  split
  · split <;> simp_all
  · simp

theorem separatedTensor_map {L : Type*} [CommSemiring L]
    (f : K →+* L) (T : Tensor K X Y Z) :
    separatedTensor (M := M) (fun x y z => f (T x y z)) =
      fun x y z => f (separatedTensor T x y z) := by
  funext x y z
  simp only [separatedTensor, Tensor.directSum]
  split
  · split <;> simp_all
  · simp

end Tensors

#print axioms filteredCoefficient_zero
#print axioms selectedTensor_eq_restrict
#print axioms selectedTensor_nonnegative_weight
#print axioms polynomialFamily_eq_restrict
#print axioms polynomialFamily_coeff_below_shift
#print axioms polynomialFamily_leading_coefficient

end Matmul.IntegralSeparator
