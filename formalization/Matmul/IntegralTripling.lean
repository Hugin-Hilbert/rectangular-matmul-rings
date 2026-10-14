import Matmul.IntegerScalar
import Matmul.IntegralConvolutionInterpolation
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Fin.Rev

/-!
# The integral three-sector polynomial degeneration

Adapted from the upstream `AuxiliarySeparation/Sector/{Weights,Degeneration,
Branches}.lean` construction. All coefficient tensors and polynomial maps here
are over ℤ. The actual simultaneous restriction has order one, with three
retained copies in their common first-input space and degrees `(0, 1, 1)`.
-/

namespace OAI.MatrixMultiplication.AuxiliarySeparation

open MatrixMultiplication.Foundation

/-- Integral convolution in the original three finite coordinate sets. -/
abbrev convolution (a h : ℕ) : Tensor ℤ (Fin a) (Fin h) (Fin (a + h - 1)) :=
  Matmul.IntegralConvolution.convolution ℤ a h

@[simp] theorem convolution_eq_one_iff {a h : ℕ} (i : Fin a) (j : Fin h)
    (k : Fin (a + h - 1)) : convolution a h i j k = 1 ↔ i.val + j.val = k.val := by
  simp [convolution, Matmul.IntegralConvolution.convolution]

@[simp] theorem convolution_ne_zero_iff {a h : ℕ} (i : Fin a) (j : Fin h)
    (k : Fin (a + h - 1)) : convolution a h i j k ≠ 0 ↔ i.val + j.val = k.val := by
  simp [convolution, Matmul.IntegralConvolution.convolution]

/-- Positive dimensions supply a coefficient equal to one. -/
theorem convolution_nonzero {a h : ℕ} (ha : 0 < a) (hh : 0 < h) :
    convolution a h ≠ 0 := by
  let i : Fin a := ⟨0, ha⟩
  let j : Fin h := ⟨0, hh⟩
  let k : Fin (a + h - 1) := ⟨0, by omega⟩
  intro hz
  have heq := congrFun (congrFun (congrFun hz i) j) k
  simp [convolution, Matmul.IntegralConvolution.convolution, i, j, k] at heq

end OAI.MatrixMultiplication.AuxiliarySeparation

namespace OAI

/-!
# Interval weights for the three-sector convolution degeneration

Section 5.2 assigns weights to the second and third coordinates of
`C(a, 3 * h + a - 1)`. The total weight is nonnegative on convolution support,
and its zero set consists exactly of the three matching sector blocks.
The middle block is a convolution with the last two legs exchanged and the
first coordinate reversed.
-/

namespace MatrixMultiplication.AuxiliarySeparation.Sector

/-- Number of second-leg coordinates in the original convolution. -/
def sourceWidth (a h : ℕ) : ℕ := 3 * h + a - 1

/-- Beginning of the right sector on both the second and third legs. -/
def rightStart (a h : ℕ) : ℕ := 2 * h + a - 1

/-- A coefficient-one term of the original convolution tensor. -/
def Support (a h i j k : ℕ) : Prop :=
  i < a ∧ j < sourceWidth a h ∧ k = i + j

/-- The middle interval on the second tensor leg. -/
def MiddleY (a h j : ℕ) : Prop := h ≤ j ∧ j < rightStart a h

/-- The middle interval on the third tensor leg. -/
def MiddleZ (a h k : ℕ) : Prop := h + a - 1 ≤ k ∧ k < rightStart a h

instance (a h j : ℕ) : Decidable (MiddleY a h j) := inferInstanceAs
  (Decidable (h ≤ j ∧ j < rightStart a h))

instance (a h k : ℕ) : Decidable (MiddleZ a h k) := inferInstanceAs
  (Decidable (h + a - 1 ≤ k ∧ k < rightStart a h))

/-- No weight is assigned to the common first leg. -/
def firstWeight (_i : ℕ) : ℤ := 0

/-- Weight one on the middle second-leg interval, zero elsewhere. -/
def secondWeight (a h j : ℕ) : ℤ := if MiddleY a h j then 1 else 0

/-- Weight minus one on the middle third-leg interval, zero elsewhere. -/
def thirdWeight (a h k : ℕ) : ℤ := if MiddleZ a h k then -1 else 0

/-- Exponent of the degeneration parameter on one term. -/
def totalWeight (a h i j k : ℕ) : ℤ :=
  firstWeight i + secondWeight a h j + thirdWeight a h k

/-- The three retained blocks have matching sector labels. -/
def MatchingSectors (a h j k : ℕ) : Prop :=
  (j < h ∧ k < h + a - 1) ∨
  (MiddleY a h j ∧ MiddleZ a h k) ∨
  (rightStart a h ≤ j ∧ rightStart a h ≤ k)

/-- A middle third-leg coordinate can only be reached from the middle second leg. -/
theorem middleY_of_middleZ {a h i j k : ℕ}
    (hs : Support a h i j k) (hz : MiddleZ a h k) : MiddleY a h j := by
  unfold Support at hs
  unfold MiddleY MiddleZ rightStart at *
  omega

/-- Every term has exponent zero or one, so no negative powers occur. -/
theorem totalWeight_eq_zero_or_one {a h i j k : ℕ}
    (hs : Support a h i j k) :
    totalWeight a h i j k = 0 ∨ totalWeight a h i j k = 1 := by
  have hmiddle := middleY_of_middleZ hs
  by_cases hy : MiddleY a h j <;> by_cases hz : MiddleZ a h k
  all_goals simp [totalWeight, firstWeight, secondWeight, thirdWeight, hy, hz] at *

theorem totalWeight_nonneg {a h i j k : ℕ}
    (hs : Support a h i j k) : 0 ≤ totalWeight a h i j k := by
  rcases totalWeight_eq_zero_or_one hs with hw | hw <;> omega

/-- The constant coefficient consists exactly of the three matching blocks. -/
theorem totalWeight_eq_zero_iff {a h i j k : ℕ}
    (hs : Support a h i j k) :
    totalWeight a h i j k = 0 ↔ MatchingSectors a h j k := by
  unfold Support sourceWidth at hs
  unfold MatchingSectors MiddleY MiddleZ rightStart
  unfold totalWeight firstWeight secondWeight thirdWeight MiddleY MiddleZ rightStart
  split_ifs <;> omega

/-- Only a middle second-leg coordinate paired with an outer third-leg coordinate
is erased by the degeneration. -/
theorem totalWeight_eq_one_iff {a h i j k : ℕ}
    (hs : Support a h i j k) :
    totalWeight a h i j k = 1 ↔ MiddleY a h j ∧ ¬ MiddleZ a h k := by
  have hmiddle := middleY_of_middleZ hs
  by_cases hy : MiddleY a h j <;> by_cases hz : MiddleZ a h k
  all_goals simp [totalWeight, firstWeight, secondWeight, thirdWeight, hy, hz] at *

/-- Parametrization of the left copy of `C(a,h)`. -/
def LeftBranch (a h i j k : ℕ) : Prop :=
  ∃ u r, u < a ∧ r < h ∧ i = u ∧ j = r ∧ k = u + r

/-- Parametrization of the middle copy with the second and third legs exchanged. -/
def MiddleBranch (a h i j k : ℕ) : Prop :=
  ∃ u r, u < a ∧ r < h ∧ i = a - 1 - u ∧
    j = h + u + r ∧ k = h + a - 1 + r

/-- Parametrization of the right translated copy of `C(a,h)`. -/
def RightBranch (a h i j k : ℕ) : Prop :=
  ∃ u r, u < a ∧ r < h ∧ i = u ∧
    j = rightStart a h + r ∧ k = rightStart a h + u + r

/-- The left block preserves the actual first coordinate. -/
theorem leftBranch_iff {a h i j k : ℕ} (hs : Support a h i j k) :
    LeftBranch a h i j k ↔ j < h ∧ k < h + a - 1 := by
  rcases hs with ⟨hi, hj, hk⟩
  constructor
  · rintro ⟨u, r, hu, hr, rfl, rfl, rfl⟩
    omega
  · rintro ⟨hleft, _⟩
    exact ⟨i, j, hi, hleft, rfl, rfl, hk⟩

/-- The middle support equation becomes convolution after reversing the first
coordinate and exchanging the second and third legs. -/
theorem middleBranch_iff {a h i j k : ℕ} (hs : Support a h i j k) :
    MiddleBranch a h i j k ↔ MiddleY a h j ∧ MiddleZ a h k := by
  rcases hs with ⟨hi, hj, hk⟩
  unfold MiddleY MiddleZ rightStart
  constructor
  · rintro ⟨u, r, hu, hr, rfl, rfl, rfl⟩
    omega
  · rintro ⟨hy, hz⟩
    refine ⟨a - 1 - i, k - (h + a - 1), ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- The right block is the same convolution after translating the two outer
coordinates. -/
theorem rightBranch_iff {a h i j k : ℕ} (hs : Support a h i j k) :
    RightBranch a h i j k ↔ rightStart a h ≤ j ∧ rightStart a h ≤ k := by
  rcases hs with ⟨hi, hj, hk⟩
  unfold sourceWidth at hj
  unfold RightBranch rightStart
  constructor
  · rintro ⟨u, r, hu, hr, rfl, rfl, rfl⟩
    omega
  · rintro ⟨hjr, hkr⟩
    refine ⟨i, j - (2 * h + a - 1), hi, ?_, rfl, ?_, ?_⟩ <;> omega

/-- On the left coordinate block, the support equation is the ordinary
convolution equation. -/
theorem left_support_coordinates {a h i r s : ℕ} (hi : i < a) (hr : r < h) :
    Support a h i r s ↔ s = i + r := by
  unfold Support sourceWidth
  omega

/-- Translation of the right block preserves the convolution equation. -/
theorem right_support_coordinates {a h i r s : ℕ} (hi : i < a) (hr : r < h) :
    Support a h i (rightStart a h + r) (rightStart a h + s) ↔ s = i + r := by
  unfold Support sourceWidth rightStart
  omega

/-- In middle-block coordinates the support equation is convolution with the
first coordinate reversed and the other two coordinates exchanged. -/
theorem middle_support_coordinates {a h i s r : ℕ}
    (hi : i < a) (hr : r < h) :
    Support a h i (h + s) (h + a - 1 + r) ↔ s = a - 1 - i + r := by
  unfold Support sourceWidth
  omega

/-- Exact retained support of the three-sector degeneration. -/
theorem retained_support_iff {a h i j k : ℕ} (hs : Support a h i j k) :
    totalWeight a h i j k = 0 ↔
      LeftBranch a h i j k ∨ MiddleBranch a h i j k ∨ RightBranch a h i j k := by
  rw [totalWeight_eq_zero_iff hs, leftBranch_iff hs, middleBranch_iff hs,
    rightBranch_iff hs]
  rfl

/-- Every displayed left-branch term belongs to the original convolution. -/
theorem LeftBranch.support {a h i j k : ℕ} (hb : LeftBranch a h i j k) :
    Support a h i j k := by
  rcases hb with ⟨u, r, hu, hr, rfl, rfl, rfl⟩
  unfold Support sourceWidth
  omega

/-- Every displayed middle-branch term belongs to the original convolution. -/
theorem MiddleBranch.support {a h i j k : ℕ} (hb : MiddleBranch a h i j k) :
    Support a h i j k := by
  rcases hb with ⟨u, r, hu, hr, rfl, rfl, rfl⟩
  unfold Support sourceWidth
  omega

/-- Every displayed right-branch term belongs to the original convolution. -/
theorem RightBranch.support {a h i j k : ℕ} (hb : RightBranch a h i j k) :
    Support a h i j k := by
  rcases hb with ⟨u, r, hu, hr, rfl, rfl, rfl⟩
  unfold Support sourceWidth rightStart
  omega

/-- Exact equality of the retained support and the three explicitly
parametrized convolution branches, without a pre-existing support assumption. -/
theorem support_and_weight_zero_iff (a h i j k : ℕ) :
    (Support a h i j k ∧ totalWeight a h i j k = 0) ↔
      LeftBranch a h i j k ∨ MiddleBranch a h i j k ∨ RightBranch a h i j k := by
  constructor
  · rintro ⟨hs, hw⟩
    exact (retained_support_iff hs).mp hw
  · intro hb
    have hs : Support a h i j k := hb.elim LeftBranch.support
      (fun hb => hb.elim MiddleBranch.support RightBranch.support)
    exact ⟨hs, (retained_support_iff hs).mpr hb⟩

/-- The first-coordinate reversal is involutive on its natural range. -/
theorem reverse_reverse {a u : ℕ} (hu : u < a) :
    a - 1 - (a - 1 - u) = u := by
  omega

/-- The middle branch has unique reversed-convolution coordinates. -/
theorem middleBranch_coordinates_unique {a h i k u r u' r' : ℕ}
    (hu : u < a) (hu' : u' < a)
    (hi : i = a - 1 - u) (hi' : i = a - 1 - u')
    (hk : k = h + a - 1 + r) (hk' : k = h + a - 1 + r') :
    u = u' ∧ r = r' := by
  omega

/-- The left and middle branches use disjoint second-leg coordinates. -/
theorem leftBranch_not_middleBranch {a h i j k : ℕ}
    (hl : LeftBranch a h i j k) : ¬ MiddleBranch a h i j k := by
  intro hm
  have hl' := (leftBranch_iff hl.support).mp hl
  have hm' := (middleBranch_iff hm.support).mp hm
  unfold MiddleY at hm'
  omega

/-- The left and right branches use disjoint second-leg coordinates. -/
theorem leftBranch_not_rightBranch {a h i j k : ℕ}
    (hl : LeftBranch a h i j k) : ¬ RightBranch a h i j k := by
  intro hr
  have hl' := (leftBranch_iff hl.support).mp hl
  have hr' := (rightBranch_iff hr.support).mp hr
  have hi := hr.support.1
  unfold rightStart at hr'
  omega

/-- The middle and right branches use disjoint second-leg coordinates. -/
theorem middleBranch_not_rightBranch {a h i j k : ℕ}
    (hm : MiddleBranch a h i j k) : ¬ RightBranch a h i j k := by
  intro hr
  have hm' := (middleBranch_iff hm.support).mp hm
  have hr' := (rightBranch_iff hr.support).mp hr
  unfold MiddleY at hm'
  omega

/-- Positivity of the two original dimensions makes the left branch nonempty. -/
theorem leftBranch_nonempty {a h : ℕ} (ha : 0 < a) (hh : 0 < h) :
    ∃ i j k, LeftBranch a h i j k :=
  ⟨0, 0, 0, 0, 0, ha, hh, rfl, rfl, rfl⟩

/-- Positivity makes the exchanged middle branch nonempty as well. -/
theorem middleBranch_nonempty {a h : ℕ} (ha : 0 < a) (hh : 0 < h) :
    ∃ i j k, MiddleBranch a h i j k := by
  refine ⟨a - 1, h, h + a - 1, 0, 0, ha, hh, ?_, ?_, ?_⟩ <;> omega

/-- Positivity also makes the translated right branch nonempty. -/
theorem rightBranch_nonempty {a h : ℕ} (ha : 0 < a) (hh : 0 < h) :
    ∃ i j k, RightBranch a h i j k := by
  refine ⟨0, rightStart a h, rightStart a h, 0, 0, ha, hh, ?_, ?_, ?_⟩ <;> omega

end MatrixMultiplication.AuxiliarySeparation.Sector

end OAI

namespace OAI

/-!
# Recovering tensors from their supported coordinate subspaces

If a tensor has support inside three injectively embedded coordinate sets, it
is exactly the extension by zero of its pullback to those sets. Characters
therefore have the same value on the ambient tensor and this smaller tensor.
-/

namespace MatrixMultiplication.AuxiliarySeparation

open MatrixMultiplication.Foundation
open scoped Classical

variable {K : Type*} [CommSemiring K]
variable {X Y Z X' Y' Z' : Type*}
variable [Fintype X] [Fintype Y] [Fintype Z]
variable [Fintype X'] [Fintype Y'] [Fintype Z']

omit [Fintype X'] [Fintype Y'] [Fintype Z'] in
/-- Support in embedded coordinate sets reconstructs the tensor by zero extension. -/
theorem tensor_eq_extendByZero_pullback (T : Tensor K X' Y' Z')
    (fx : X → X') (fy : Y → Y') (fz : Z → Z')
    (hx : Function.Injective fx) (hy : Function.Injective fy)
    (hz : Function.Injective fz)
    (hs : ∀ x' y' z', T x' y' z' ≠ 0 →
      x' ∈ Set.range fx ∧ y' ∈ Set.range fy ∧ z' ∈ Set.range fz) :
    T = Tensor.restrict
      (fun x' x => if fx x = x' then 1 else 0)
      (fun y' y => if fy y = y' then 1 else 0)
      (fun z' z => if fz z = z' then 1 else 0)
      (Tensor.pullback fx fy fz T) := by
  classical
  funext x' y' z'
  by_cases hx' : x' ∈ Set.range fx
  · obtain ⟨x, rfl⟩ := hx'
    by_cases hy' : y' ∈ Set.range fy
    · obtain ⟨y, rfl⟩ := hy'
      by_cases hz' : z' ∈ Set.range fz
      · obtain ⟨z, rfl⟩ := hz'
        simp [Tensor.restrict, Tensor.pullback, hx.eq_iff, hy.eq_iff, hz.eq_iff,
          ite_mul, mul_ite]
      · have hzero : T (fx x) (fy y) z' = 0 := by
          by_contra h
          exact hz' (hs _ _ _ h).2.2
        have hnone : ∀ z, fz z ≠ z' := fun z h => hz' ⟨z, h⟩
        simp [Tensor.restrict, hzero, hnone]
    · have hzero : T (fx x) y' z' = 0 := by
        by_contra h
        exact hy' (hs _ _ _ h).2.1
      have hnone : ∀ y, fy y ≠ y' := fun y h => hy' ⟨y, h⟩
      simp [Tensor.restrict, hzero, hnone]
  · have hzero : T x' y' z' = 0 := by
      by_contra h
      exact hx' (hs _ _ _ h).1
    have hnone : ∀ x, fx x ≠ x' := fun x h => hx' ⟨x, h⟩
    simp [Tensor.restrict, hzero, hnone]

end MatrixMultiplication.AuxiliarySeparation
end OAI

namespace OAI

/-!
# The actual three-sector polynomial degeneration

The interval weights of `SectorWeights` act by diagonal local maps on the
coefficient tensor `C(a, 3h+a-1)`. Shifting every third-leg weight by one makes
the local maps polynomial. Their restriction is exactly `X * retained +
X^2 * erased`, so the existing polynomial-restriction degeneration interface
applies with leading order one and local degree bounds `(0,1,1)`.
-/

noncomputable section

open scoped BigOperators Classical

namespace MatrixMultiplication.AuxiliarySeparation.Sector

open MatrixMultiplication.Foundation
open Polynomial

abbrev YIndex (a h : ℕ) := Fin (sourceWidth a h)
abbrev ZIndex (a h : ℕ) := Fin (a + sourceWidth a h - 1)

/-- The source coefficient tensor, with its actual shared first-input space. -/
def source (a h : ℕ) : Tensor ℤ (Fin a) (YIndex a h) (ZIndex a h) :=
  convolution a (sourceWidth a h)

theorem source_ne_zero_iff {a h : ℕ} (i : Fin a) (j : YIndex a h)
    (k : ZIndex a h) :
    source a h i j k ≠ 0 ↔ Support a h i.val j.val k.val := by
  simp only [source, convolution_ne_zero_iff, Support]
  constructor
  · intro heq
    exact ⟨i.isLt, j.isLt, heq.symm⟩
  · intro hs
    exact hs.2.2.symm

/-- The weight-zero part in the original coordinate spaces. -/
def retained (a h : ℕ) : Tensor ℤ (Fin a) (YIndex a h) (ZIndex a h) :=
  fun i j k => if totalWeight a h i.val j.val k.val = 0 then source a h i j k else 0

/-- The positive-weight part, all of whose supported terms have weight one. -/
def erased (a h : ℕ) : Tensor ℤ (Fin a) (YIndex a h) (ZIndex a h) :=
  fun i j k => if totalWeight a h i.val j.val k.val = 1 then source a h i j k else 0

/-- The left retained branch, still in the common ambient coordinate spaces. -/
def leftTensor (a h : ℕ) : Tensor ℤ (Fin a) (YIndex a h) (ZIndex a h) :=
  fun i j k => if LeftBranch a h i.val j.val k.val then 1 else 0

/-- The middle retained branch; its first leg is the actual shared first leg. -/
def middleTensor (a h : ℕ) : Tensor ℤ (Fin a) (YIndex a h) (ZIndex a h) :=
  fun i j k => if MiddleBranch a h i.val j.val k.val then 1 else 0

/-- The right retained branch in the original coordinate spaces. -/
def rightTensor (a h : ℕ) : Tensor ℤ (Fin a) (YIndex a h) (ZIndex a h) :=
  fun i j k => if RightBranch a h i.val j.val k.val then 1 else 0

/-- The retained tensor is exactly the sum of the three stated branches,
with coefficient one on each and the original first-leg coordinates shared. -/
theorem retained_eq_three_branches (a h : ℕ) :
    retained a h = leftTensor a h + middleTensor a h + rightTensor a h := by
  funext i j k
  by_cases hs : Support a h i.val j.val k.val
  · have hsource : source a h i j k = 1 := by
      exact (convolution_eq_one_iff i j k).mpr hs.2.2.symm
    have hw := retained_support_iff hs
    have hlm := leftBranch_not_middleBranch (a := a) (h := h)
      (i := i.val) (j := j.val) (k := k.val)
    have hlr := leftBranch_not_rightBranch (a := a) (h := h)
      (i := i.val) (j := j.val) (k := k.val)
    have hmr := middleBranch_not_rightBranch (a := a) (h := h)
      (i := i.val) (j := j.val) (k := k.val)
    by_cases hl : LeftBranch a h i.val j.val k.val <;>
      by_cases hm : MiddleBranch a h i.val j.val k.val <;>
      by_cases hr : RightBranch a h i.val j.val k.val
    all_goals simp_all [retained, leftTensor, middleTensor, rightTensor]
  · have hsource : source a h i j k = 0 := by
      by_contra hz
      exact hs ((source_ne_zero_iff i j k).mp hz)
    have hl : ¬ LeftBranch a h i.val j.val k.val := fun hb => hs hb.support
    have hm : ¬ MiddleBranch a h i.val j.val k.val := fun hb => hs hb.support
    have hr : ¬ RightBranch a h i.val j.val k.val := fun hb => hs hb.support
    simp [retained, leftTensor, middleTensor, rightTensor, hsource, hl, hm, hr]

/-- Every source term belongs either to the retained tensor or the erased one. -/
theorem source_eq_retained_add_erased (a h : ℕ) :
    source a h = retained a h + erased a h := by
  funext i j k
  by_cases hs : source a h i j k = 0
  · simp [retained, erased, hs]
  · rcases totalWeight_eq_zero_or_one ((source_ne_zero_iff i j k).mp hs) with hw | hw
    all_goals simp [retained, erased, hw]

/-- The normalized polynomial family appearing in the unshifted weights. -/
def normalizedPolynomial (a h : ℕ) :
    Tensor (Polynomial ℤ) (Fin a) (YIndex a h) (ZIndex a h) :=
  fun i j k => C (retained a h i j k) + X * C (erased a h i j k)

/-- The first local map fixes the common input basis. -/
def leftMap (a : ℕ) (output input : Fin a) : Polynomial ℤ :=
  if input = output then 1 else 0

/-- The second local map assigns weight one to the middle interval. -/
def middleMap (a h : ℕ) (output input : YIndex a h) : Polynomial ℤ :=
  if input = output then (if MiddleY a h output.val then X else 1) else 0

/-- Shift the third-leg weights by one, giving weight zero to the middle
interval and weight one to the two outer intervals. -/
def rightMap (a h : ℕ) (output input : ZIndex a h) : Polynomial ℤ :=
  if input = output then (if MiddleZ a h output.val then 1 else X) else 0

/-- One simultaneous polynomial restriction of the whole source tensor. -/
def polynomial (a h : ℕ) :
    Tensor (Polynomial ℤ) (Fin a) (YIndex a h) (ZIndex a h) :=
  Tensor.restrict (leftMap a) (middleMap a h) (rightMap a h)
    (fun i j k => C (source a h i j k))

theorem polynomial_apply (a h : ℕ) (i : Fin a) (j : YIndex a h)
    (k : ZIndex a h) :
    polynomial a h i j k =
      (if MiddleY a h j.val then X else 1) *
      (if MiddleZ a h k.val then 1 else X) * C (source a h i j k) := by
  simp [polynomial, Tensor.restrict, leftMap, middleMap, rightMap, ite_mul, mul_ite]

/-- The shifted polynomial restriction has precisely two possible degrees. -/
theorem polynomial_identity (a h : ℕ) (i : Fin a) (j : YIndex a h)
    (k : ZIndex a h) :
    polynomial a h i j k =
      X * C (retained a h i j k) + X ^ 2 * C (erased a h i j k) := by
  by_cases hs : source a h i j k = 0
  · simp [polynomial_apply, retained, erased, hs]
  · have hsupport := (source_ne_zero_iff i j k).mp hs
    have hmiddle := middleY_of_middleZ hsupport
    by_cases hy : MiddleY a h j.val <;> by_cases hz : MiddleZ a h k.val
    all_goals
      simp_all [polynomial_apply, retained, erased, totalWeight, firstWeight,
        secondWeight, thirdWeight, pow_two]

theorem polynomial_eq_X_mul_normalized (a h : ℕ) (i : Fin a) (j : YIndex a h)
    (k : ZIndex a h) :
    polynomial a h i j k = X * normalizedPolynomial a h i j k := by
  rw [polynomial_identity, normalizedPolynomial]
  ring

theorem polynomial_coeff (a h : ℕ) (i : Fin a) (j : YIndex a h)
    (k : ZIndex a h) (n : ℕ) :
    (polynomial a h i j k).coeff n =
      (if n = 1 then retained a h i j k else 0) +
      (if n = 2 then erased a h i j k else 0) := by
  rw [polynomial_identity, Polynomial.coeff_add,
    mul_comm X (C (retained a h i j k)),
    mul_comm (X ^ 2) (C (erased a h i j k)),
    Polynomial.coeff_C_mul_X, Polynomial.coeff_C_mul_X_pow]

theorem leftMap_degree (a : ℕ) (output input : Fin a) :
    (leftMap a output input).degree ≤ 0 := by
  by_cases heq : input = output <;> simp [leftMap, heq]

theorem middleMap_degree (a h : ℕ) (output input : YIndex a h) :
    (middleMap a h output input).degree ≤ 1 := by
  by_cases heq : input = output <;> by_cases hy : MiddleY a h output.val <;>
    simp [middleMap, heq, hy]

theorem rightMap_degree (a h : ℕ) (output input : ZIndex a h) :
    (rightMap a h output input).degree ≤ 1 := by
  by_cases heq : input = output <;> by_cases hz : MiddleZ a h output.val <;>
    simp [rightMap, heq, hz]

/-- Evaluation of the normalized family has exactly the paper's form. -/
theorem normalizedPolynomial_eval (a h : ℕ) (t : ℤ) (i : Fin a)
    (j : YIndex a h) (k : ZIndex a h) :
    (normalizedPolynomial a h i j k).eval t =
      retained a h i j k + t * erased a h i j k := by
  simp only [normalizedPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]

/-- The zero coefficient vanishes in the actual simultaneous restriction. -/
@[simp] theorem polynomial_coeff_zero (a h : ℕ) (i : Fin a) (j : YIndex a h)
    (k : ZIndex a h) : (polynomial a h i j k).coeff 0 = 0 := by
  simp [polynomial_coeff]

/-- The first coefficient is exactly the retained tensor. -/
@[simp] theorem polynomial_coeff_one (a h : ℕ) (i : Fin a) (j : YIndex a h)
    (k : ZIndex a h) : (polynomial a h i j k).coeff 1 = retained a h i j k := by
  simp [polynomial_coeff]

/-- The leading coefficient consists of the three explicit oriented branches,
all in their original common first-leg coordinates. -/
theorem polynomial_leading_three_branches (a h : ℕ) :
    (fun i j k => (polynomial a h i j k).coeff 1) =
      leftTensor a h + middleTensor a h + rightTensor a h := by
  simp only [polynomial_coeff_one]
  exact retained_eq_three_branches a h

end MatrixMultiplication.AuxiliarySeparation.Sector

end

end OAI

namespace OAI

/-!
# Coordinate identifications of the three retained sectors

Each outer branch is a zero extension of `C(a,h)`, using the same first-leg
coordinates. The middle branch is a zero extension after reversing the first
coordinate and exchanging the second and third tensor legs.
-/

noncomputable section

open MatrixMultiplication.Foundation
open scoped Classical


namespace MatrixMultiplication.AuxiliarySeparation.Sector

/-- Embed the left second-leg interval. -/
def leftY (a h : ℕ) (r : Fin h) : YIndex a h :=
  ⟨r.val, by have hr := r.isLt; unfold sourceWidth; omega⟩

/-- Embed the left third-leg interval. -/
def leftZ (a h : ℕ) (s : Fin (a + h - 1)) : ZIndex a h :=
  ⟨s.val, by have hs := s.isLt; unfold sourceWidth; omega⟩

/-- Embed the middle second-leg interval, which carries the convolution output. -/
def middleY (a h : ℕ) (s : Fin (a + h - 1)) : YIndex a h :=
  ⟨h + s.val, by have hs := s.isLt; unfold sourceWidth; omega⟩

/-- Embed the middle third-leg interval, which carries the second input. -/
def middleZ (a h : ℕ) (r : Fin h) : ZIndex a h :=
  ⟨h + a - 1 + r.val, by have hr := r.isLt; unfold sourceWidth; omega⟩

/-- Embed the right second-leg interval. -/
def rightY (a h : ℕ) (r : Fin h) : YIndex a h :=
  ⟨rightStart a h + r.val,
    by have hr := r.isLt; unfold rightStart sourceWidth; omega⟩

/-- Embed the right third-leg interval. -/
def rightZ (a h : ℕ) (s : Fin (a + h - 1)) : ZIndex a h :=
  ⟨rightStart a h + s.val,
    by have hs := s.isLt; unfold rightStart sourceWidth; omega⟩

theorem leftY_injective (a h : ℕ) : Function.Injective (leftY a h) := by
  intro r s heq
  apply Fin.ext
  exact congrArg (fun t : YIndex a h => t.val) heq

theorem leftZ_injective (a h : ℕ) : Function.Injective (leftZ a h) := by
  intro r s heq
  apply Fin.ext
  exact congrArg (fun t : ZIndex a h => t.val) heq

theorem middleY_injective (a h : ℕ) : Function.Injective (middleY a h) := by
  intro r s heq
  apply Fin.ext
  have hv := congrArg Fin.val heq
  dsimp [middleY] at hv
  omega

theorem middleZ_injective (a h : ℕ) : Function.Injective (middleZ a h) := by
  intro r s heq
  apply Fin.ext
  have hv := congrArg Fin.val heq
  dsimp [middleZ] at hv
  omega

theorem rightY_injective (a h : ℕ) : Function.Injective (rightY a h) := by
  intro r s heq
  apply Fin.ext
  have hv := congrArg Fin.val heq
  dsimp [rightY] at hv
  omega

theorem rightZ_injective (a h : ℕ) : Function.Injective (rightZ a h) := by
  intro r s heq
  apply Fin.ext
  have hv := congrArg Fin.val heq
  dsimp [rightZ] at hv
  omega

/-- Pulling back the left block gives ordinary convolution. -/
theorem leftTensor_pullback (a h : ℕ) :
    Tensor.pullback id (leftY a h) (leftZ a h) (leftTensor a h) =
      convolution a h := by
  funext i r s
  have hb : LeftBranch a h i.val r.val s.val ↔ i.val + r.val = s.val := by
    constructor
    · rintro ⟨u, t, hu, ht, hi, hr, hs⟩
      omega
    · intro hs
      exact ⟨i.val, r.val, i.isLt, r.isLt, rfl, rfl, hs.symm⟩
  simp only [Tensor.pullback, leftTensor, leftY, leftZ, id_eq, convolution, Matmul.IntegralConvolution.convolution, hb]

/-- Pulling back the translated right block also gives ordinary convolution. -/
theorem rightTensor_pullback (a h : ℕ) :
    Tensor.pullback id (rightY a h) (rightZ a h) (rightTensor a h) =
      convolution a h := by
  funext i r s
  have hb : RightBranch a h i.val (rightStart a h + r.val)
      (rightStart a h + s.val) ↔ i.val + r.val = s.val := by
    constructor
    · rintro ⟨u, t, hu, ht, hi, hr, hs⟩
      omega
    · intro hs
      refine ⟨i.val, r.val, i.isLt, r.isLt, rfl, rfl, ?_⟩
      omega
  simp only [Tensor.pullback, rightTensor, rightY, rightZ, id_eq, convolution, Matmul.IntegralConvolution.convolution, hb]

/-- Exchange the two outer convolution legs while retaining the original input
order in the displayed coefficient equation. -/
def exchangedConvolution (a h : ℕ) :
    Tensor ℤ (Fin a) (Fin (a + h - 1)) (Fin h) :=
  fun i s r => convolution a h i r s

/-- The middle branch is exactly convolution with its last two legs exchanged;
the first-leg reversal occurs solely in this individual branch identification. -/
theorem middleTensor_pullback (a h : ℕ) :
    Tensor.pullback Fin.rev (middleY a h) (middleZ a h) (middleTensor a h) =
      exchangedConvolution a h := by
  funext i s r
  have hi := i.isLt
  have hr := r.isLt
  have hb : MiddleBranch a h (a - (i.val + 1)) (h + s.val)
      (h + a - 1 + r.val) ↔ i.val + r.val = s.val := by
    constructor
    · rintro ⟨u, t, hu, ht, hx, hy, hz⟩
      omega
    · intro hs
      refine ⟨i.val, r.val, hi, hr, ?_, ?_, rfl⟩ <;> omega
  simp only [Tensor.pullback, middleTensor, middleY, middleZ,
    exchangedConvolution, convolution, Matmul.IntegralConvolution.convolution, Fin.val_rev, hb]

/-- All nonzero left-branch coordinates lie in the displayed embeddings. -/
theorem leftTensor_support (a h : ℕ) (i : Fin a) (j : YIndex a h)
    (k : ZIndex a h) (hn : leftTensor a h i j k ≠ 0) :
    (∃ r, leftY a h r = j) ∧ (∃ s, leftZ a h s = k) := by
  have hb : LeftBranch a h i.val j.val k.val := by
    by_contra hn'
    exact hn (by simp [leftTensor, hn'])
  rcases hb with ⟨u, r, hu, hr, hi, hj, hk⟩
  constructor
  · exact ⟨⟨r, hr⟩, Fin.ext hj.symm⟩
  · exact ⟨⟨u + r, by omega⟩, Fin.ext hk.symm⟩

/-- All nonzero right-branch coordinates lie in the translated embeddings. -/
theorem rightTensor_support (a h : ℕ) (i : Fin a) (j : YIndex a h)
    (k : ZIndex a h) (hn : rightTensor a h i j k ≠ 0) :
    (∃ r, rightY a h r = j) ∧ (∃ s, rightZ a h s = k) := by
  have hb : RightBranch a h i.val j.val k.val := by
    by_contra hn'
    exact hn (by simp [rightTensor, hn'])
  rcases hb with ⟨u, r, hu, hr, hi, hj, hk⟩
  constructor
  · exact ⟨⟨r, hr⟩, Fin.ext hj.symm⟩
  · refine ⟨⟨u + r, by omega⟩, Fin.ext ?_⟩
    dsimp [rightZ]
    omega

/-- All nonzero middle-branch coordinates lie in the exchanged embeddings. -/
theorem middleTensor_support (a h : ℕ) (i : Fin a) (j : YIndex a h)
    (k : ZIndex a h) (hn : middleTensor a h i j k ≠ 0) :
    (∃ u, Fin.rev u = i) ∧ (∃ s, middleY a h s = j) ∧
      (∃ r, middleZ a h r = k) := by
  have hb : MiddleBranch a h i.val j.val k.val := by
    by_contra hn'
    exact hn (by simp [middleTensor, hn'])
  rcases hb with ⟨u, r, hu, hr, hi, hj, hk⟩
  refine ⟨⟨⟨u, hu⟩, Fin.ext ?_⟩, ⟨⟨u + r, by omega⟩, Fin.ext ?_⟩,
    ⟨⟨r, hr⟩, Fin.ext ?_⟩⟩
  · simp only [Fin.val_rev]
    omega
  · dsimp [middleY]
    omega
  · exact hk.symm

/-- The left block is the zero extension of the ordinary convolution tensor. -/
theorem leftTensor_eq_extension (a h : ℕ) :
    leftTensor a h = Tensor.restrict
      (fun x i => if i = x then 1 else 0)
      (fun y r => if leftY a h r = y then 1 else 0)
      (fun z s => if leftZ a h s = z then 1 else 0) (convolution a h) := by
  have hs (i : Fin a) (j : YIndex a h) (k : ZIndex a h)
      (hn : leftTensor a h i j k ≠ 0) :
      i ∈ Set.range (id : Fin a → Fin a) ∧
        j ∈ Set.range (leftY a h) ∧ k ∈ Set.range (leftZ a h) := by
    exact ⟨⟨i, rfl⟩, leftTensor_support a h i j k hn⟩
  classical
  have heq := tensor_eq_extendByZero_pullback (leftTensor a h) id (leftY a h) (leftZ a h)
    Function.injective_id (leftY_injective a h) (leftZ_injective a h) hs
  rw [leftTensor_pullback] at heq
  convert heq using 1
  congr 1 <;> funext x i <;> (try dsimp only [id_eq]) <;> split_ifs <;> rfl

/-- The right block is the zero extension along the translated coordinates. -/
theorem rightTensor_eq_extension (a h : ℕ) :
    rightTensor a h = Tensor.restrict
      (fun x i => if i = x then 1 else 0)
      (fun y r => if rightY a h r = y then 1 else 0)
      (fun z s => if rightZ a h s = z then 1 else 0) (convolution a h) := by
  have hs (i : Fin a) (j : YIndex a h) (k : ZIndex a h)
      (hn : rightTensor a h i j k ≠ 0) :
      i ∈ Set.range (id : Fin a → Fin a) ∧
        j ∈ Set.range (rightY a h) ∧ k ∈ Set.range (rightZ a h) := by
    exact ⟨⟨i, rfl⟩, rightTensor_support a h i j k hn⟩
  classical
  have heq := tensor_eq_extendByZero_pullback (rightTensor a h) id (rightY a h) (rightZ a h)
    Function.injective_id (rightY_injective a h) (rightZ_injective a h) hs
  rw [rightTensor_pullback] at heq
  convert heq using 1
  congr 1 <;> funext x i <;> (try dsimp only [id_eq]) <;> split_ifs <;> rfl

/-- The middle block is the zero extension of the exchanged convolution, Matmul.IntegralConvolution.convolution, with
one reversible change of basis on its first leg. -/
theorem middleTensor_eq_extension (a h : ℕ) :
    middleTensor a h = Tensor.restrict
      (fun x i => if Fin.rev i = x then 1 else 0)
      (fun y s => if middleY a h s = y then 1 else 0)
      (fun z r => if middleZ a h r = z then 1 else 0) (exchangedConvolution a h) := by
  classical
  have heq := tensor_eq_extendByZero_pullback (middleTensor a h) Fin.rev (middleY a h)
    (middleZ a h) Fin.rev_injective (middleY_injective a h) (middleZ_injective a h)
    (middleTensor_support a h)
  rw [middleTensor_pullback] at heq
  convert heq using 1
  congr 1 <;> funext x i <;> split_ifs <;> rfl

/-- Exchanging two tensor legs preserves nonzeroness. -/
theorem exchangedConvolution_nonzero {a h : ℕ} (ha : 0 < a) (hh : 0 < h) :
    exchangedConvolution a h ≠ 0 := by
  intro hz
  apply convolution_nonzero ha hh
  funext i r s
  exact congrFun (congrFun (congrFun hz i) s) r

/-- The left retained branch is nonzero in every positive size. -/
theorem leftTensor_nonzero {a h : ℕ} (ha : 0 < a) (hh : 0 < h) :
    leftTensor a h ≠ 0 := by
  intro hz
  have hp := leftTensor_pullback a h
  rw [hz] at hp
  exact convolution_nonzero ha hh hp.symm

/-- The translated right branch is nonzero in every positive size. -/
theorem rightTensor_nonzero {a h : ℕ} (ha : 0 < a) (hh : 0 < h) :
    rightTensor a h ≠ 0 := by
  intro hz
  have hp := rightTensor_pullback a h
  rw [hz] at hp
  exact convolution_nonzero ha hh hp.symm

/-- The exchanged middle branch is nonzero in every positive size. -/
theorem middleTensor_nonzero {a h : ℕ} (ha : 0 < a) (hh : 0 < h) :
    middleTensor a h ≠ 0 := by
  intro hz
  have hp := middleTensor_pullback a h
  rw [hz] at hp
  exact exchangedConvolution_nonzero ha hh hp.symm

end MatrixMultiplication.AuxiliarySeparation.Sector

end

end OAI

namespace OAI

/-! The three retained branches have matching second- and third-leg labels. -/

noncomputable section

open scoped BigOperators Classical
open MatrixMultiplication.Foundation

namespace MatrixMultiplication.AuxiliarySeparation.Sector

/-- The actual three retained tensors in their original ambient spaces. -/
def branchFamily (a h : ℕ) (b : Fin 3) :
    Tensor ℤ (Fin a) (YIndex a h) (ZIndex a h) :=
  if b = 0 then leftTensor a h else if b = 1 then middleTensor a h else rightTensor a h

@[simp] theorem branchFamily_zero (a h : ℕ) :
    branchFamily a h 0 = leftTensor a h := by simp [branchFamily]

@[simp] theorem branchFamily_one (a h : ℕ) :
    branchFamily a h 1 = middleTensor a h := by simp [branchFamily]

@[simp] theorem branchFamily_two (a h : ℕ) :
    branchFamily a h 2 = rightTensor a h := by simp [branchFamily]

/-- Label a second-leg coordinate by its interval. -/
def yLabel (a h : ℕ) (j : YIndex a h) : Fin 3 :=
  if j.val < h then 0 else if j.val < rightStart a h then 1 else 2

/-- Label a third-leg coordinate by its corresponding interval. -/
def zLabel (a h : ℕ) (k : ZIndex a h) : Fin 3 :=
  if k.val < h + a - 1 then 0 else if k.val < rightStart a h then 1 else 2

/-- Every nonzero branch coefficient lies in the two matching labelled sectors. -/
theorem branchFamily_labels (a h : ℕ) (b : Fin 3) (i : Fin a)
    (j : YIndex a h) (k : ZIndex a h) (hn : branchFamily a h b i j k ≠ 0) :
    yLabel a h j = b ∧ zLabel a h k = b := by
  fin_cases b
  · have hb : LeftBranch a h i.val j.val k.val := by
      by_contra hb
      exact hn (by simp [branchFamily, leftTensor, hb])
    have h := (leftBranch_iff hb.support).mp hb
    simp [yLabel, zLabel, h.1, h.2]
  · have hb : MiddleBranch a h i.val j.val k.val := by
      by_contra hb
      exact hn (by simp [branchFamily, middleTensor, hb])
    rcases (middleBranch_iff hb.support).mp hb with ⟨⟨hy₀, hy₁⟩, ⟨hz₀, hz₁⟩⟩
    simp [yLabel, zLabel, not_lt.mpr hy₀, hy₁, not_lt.mpr hz₀, hz₁]
  · have hb : RightBranch a h i.val j.val k.val := by
      by_contra hb
      exact hn (by simp [branchFamily, rightTensor, hb])
    rcases (rightBranch_iff hb.support).mp hb with ⟨hy, hz⟩
    have hi := i.isLt
    have hy₀ : h ≤ j.val := by unfold rightStart at hy; omega
    have hz₀ : h + a - 1 ≤ k.val := by unfold rightStart at hz; omega
    simp [yLabel, zLabel, not_lt.mpr hy₀, not_lt.mpr hy,
      not_lt.mpr hz₀, not_lt.mpr hz]

/-- The branch family sums to exactly the retained tensor. -/
theorem sum_branchFamily (a h : ℕ) :
    (∑ b : Fin 3, branchFamily a h b) = retained a h := by
  simp only [Fin.sum_univ_three, branchFamily_zero, branchFamily_one, branchFamily_two]
  exact (retained_eq_three_branches a h).symm


theorem branchFamily_nonzero {a h : ℕ} (ha : 0 < a) (hh : 0 < h)
    (b : Fin 3) : branchFamily a h b ≠ 0 := by
  fin_cases b
  · simpa [branchFamily] using leftTensor_nonzero ha hh
  · simpa [branchFamily] using middleTensor_nonzero ha hh
  · simpa [branchFamily] using rightTensor_nonzero ha hh

end MatrixMultiplication.AuxiliarySeparation.Sector
end
end OAI
