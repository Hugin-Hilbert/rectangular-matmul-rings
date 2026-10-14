import Matmul.IntegerSemiring
import Matmul.IntegralTripling
import Matmul.IntegralConvolutionInterpolation
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic

/-!
# The integral determinant filtration

The quotient and determinant-kernel coordinates are related to the monomial
coordinates by explicit matrices with entries zero, one, and minus one.
The inverse matrices and the polynomial degeneration are checked below;
no field-valued basis or inverse coefficient is used.
-/

namespace Matmul.IntegralDeterminant

noncomputable section

open OAI.MatrixMultiplication.Foundation Polynomial
open scoped BigOperators

abbrev Index (e : ℕ) := Fin (e + 2) ⊕ Fin e
abbrev OriginalIndex (e : ℕ) := Fin (e + 1) ⊕ Fin (e + 1)

/-- The original convolution on each of the two matching components. -/
def sourceTensor (d e : ℕ) :
    Tensor ℤ (Fin (d + 1)) (OriginalIndex e) (OriginalIndex (d + e))
  | i, .inl j, .inl k => if i.val + j.val = k.val then 1 else 0
  | i, .inr j, .inr k => if i.val + j.val = k.val then 1 else 0
  | _, _, _ => 0

/-- Two-coordinate pairing with the singleton on the fixed first leg. -/
def pairingTensor : Tensor ℤ PUnit Bool Bool := fun _ j k => if j = k then 1 else 0

def originalCoordinate (e : ℕ) : OriginalIndex e → Fin (e + 1) × Bool
  | .inl j => (j, false)
  | .inr j => (j, true)

def originalCoordinateEquiv (e : ℕ) : OriginalIndex e ≃ Fin (e + 1) × Bool where
  toFun := originalCoordinate e
  invFun p := if p.2 then .inr p.1 else .inl p.1
  left_inv p := by cases p <;> rfl
  right_inv p := by rcases p with ⟨i, b⟩; cases b <;> rfl

/-- The original tensor is convolution tensored with the actual two-coordinate
pairing. The singleton lies on the unchanged first leg. -/
theorem sourceTensor_product (d e : ℕ) :
    sourceTensor d e =
      Tensor.pullback (fun i : Fin (d + 1) => (i, PUnit.unit)) (originalCoordinate e)
        (fun k => (Fin.cast (by unfold IntegralConvolution.outputLength; omega)
          (originalCoordinate (d + e) k).1, (originalCoordinate (d + e) k).2))
        (Tensor.product (IntegralConvolution.convolution ℤ (d + 1) (e + 1)) pairingTensor) := by
  funext i j k
  cases j <;> cases k <;>
    simp [Tensor.pullback, Tensor.product, IntegralConvolution.convolution,
      pairingTensor, originalCoordinate, sourceTensor] <;> rfl

/-- The two-coordinate pairing has an actual rank-two integral decomposition. -/
theorem pairingTensor_rankAtMost : Tensor.RankAtMost pairingTensor 2 := by
  let a : Bool → PUnit → ℤ := fun _ _ => 1
  let b : Bool → Bool → ℤ := fun i j => if i = j then 1 else 0
  have h : pairingTensor = fun x y z => ∑ i, Tensor.rankOne (a i) (b i) (b i) x y z := by
    funext x y z
    simp [pairingTensor, a, b, Tensor.rankOne, mul_ite]
    split_ifs <;> simp_all
  rw [h]
  simpa only [Fintype.card_bool] using Tensor.rankAtMost_sum_rankOne a b b

/-- The actual multiplication tensor in quotient/kernel coordinates. -/
def adaptedTensor (d e : ℕ) : Tensor ℤ (Fin (d + 1)) (Index e) (Index (d + e))
  | i, .inl j, .inl k => if i.val + j.val = k.val then 1 else 0
  | i, .inl j, .inr k =>
      if j.val = e + 1 ∧ i.val < d ∧ e + i.val = k.val then 1 else 0
  | _, .inr _, .inl _ => 0
  | i, .inr j, .inr k => if i.val + j.val = k.val then 1 else 0

/-- The two matching convolution branches share the unchanged first leg. -/
def gradedTensor (d e : ℕ) : Tensor ℤ (Fin (d + 1)) (Index e) (Index (d + e))
  | i, .inl j, .inl k => if i.val + j.val = k.val then 1 else 0
  | _, .inl _, .inr _ => 0
  | _, .inr _, .inl _ => 0
  | i, .inr j, .inr k => if i.val + j.val = k.val then 1 else 0

/-- Columns of the integral adapted basis in the old monomial basis. -/
def inputChange (e : ℕ) : Index e → OriginalIndex e → ℤ
  | .inl j, .inl k => if j.val < e + 1 ∧ j.val = k.val then 1 else 0
  | .inl j, .inr k => if j.val = e + 1 ∧ k.val = e then 1 else 0
  | .inr j, .inl k => -(if j.val + 1 = k.val then 1 else 0)
  | .inr j, .inr k => if j.val = k.val then 1 else 0

/-- The inverse basis change, acting on the dual output coordinates. -/
def outputDualChange (e : ℕ) : Index e → OriginalIndex e → ℤ
  | .inl j, .inl k => if j.val = k.val then 1 else 0
  | .inl j, .inr k => if j.val = k.val + 1 then 1 else 0
  | .inr _, .inl _ => 0
  | .inr j, .inr k => if j.val = k.val then 1 else 0

def fixedFirst (d : ℕ) (i j : Fin (d + 1)) : ℤ := if i = j then 1 else 0

private theorem sum_coordinate {n r : ℕ} (hr : r < n) (v : Fin n → ℤ) :
    (∑ k : Fin n, (if r = k.val then (1 : ℤ) else 0) * v k) = v ⟨r, hr⟩ := by
  have h (k : Fin n) : r = k.val ↔ k = ⟨r, hr⟩ := by
    constructor
    · intro hk
      exact Fin.ext hk.symm
    · intro hk
      exact congrArg Fin.val hk.symm
  simp_rw [h]
  simp

private theorem sum_coordinate_right {n r : ℕ} (hr : r < n) (v : Fin n → ℤ) :
    (∑ k : Fin n, v k * (if r = k.val then (1 : ℤ) else 0)) = v ⟨r, hr⟩ := by
  simpa only [mul_comm] using sum_coordinate hr v

/-- Restriction by the adapted input columns is an explicit integral change
of coordinates on the whole finite coefficient space. -/
theorem sum_inputChange (e : ℕ) (v : OriginalIndex e → ℤ) (j : Index e) :
    (∑ k, inputChange e j k * v k) =
      match j with
      | .inl j => if h : j.val < e + 1 then v (.inl ⟨j.val, h⟩)
          else v (.inr ⟨e, Nat.lt_succ_self e⟩)
      | .inr j => -v (.inl ⟨j.val + 1, by omega⟩) + v (.inr ⟨j.val, by omega⟩) := by
  cases j with
  | inl j =>
    by_cases hj : j.val < e + 1
    · have hjtop : j.val ≠ e + 1 := by omega
      simp only [Fintype.sum_sum_type, inputChange, hj, true_and, hjtop,
        false_and, ↓reduceIte, zero_mul, Finset.sum_const_zero, add_zero]
      exact sum_coordinate hj _
    · have hjtop : j.val = e + 1 := by omega
      dsimp only
      rw [dif_neg hj]
      simp only [Fintype.sum_sum_type, inputChange, hjtop, lt_self_iff_false, false_and,
        true_and, ↓reduceIte, zero_mul, Finset.sum_const_zero, zero_add]
      simpa only [eq_comm] using (sum_coordinate (Nat.lt_succ_self e) (fun k => v (.inr k))).symm
  | inr j =>
    simp only [Fintype.sum_sum_type, inputChange, neg_mul, Finset.sum_neg_distrib]
    rw [sum_coordinate (by omega), sum_coordinate (by omega)]

/-- The inverse coordinate matrices multiply to the identity on the
adapted index space, including the boundary kernel of dimension zero. -/
theorem inputChange_outputDual_identity (e : ℕ) (j k : Index e) :
    (∑ old, inputChange e j old * outputDualChange e k old) =
      if j = k then 1 else 0 := by
  rw [sum_inputChange]
  cases j with
  | inl j =>
    by_cases hj : j.val < e + 1
    · cases k <;> simp [hj, outputDualChange, Fin.ext_iff, eq_comm]
    · have hjtop : j.val = e + 1 := by omega
      cases k with
      | inl k => simp [outputDualChange, Fin.ext_iff, hjtop, eq_comm]
      | inr k =>
        have hk : k.val ≠ e := by have := k.isLt; omega
        simp [hj, outputDualChange, hk]
  | inr j =>
    cases k <;> simp [outputDualChange, Fin.ext_iff, eq_comm]

/-- The two index spaces have equal cardinality, so the same integral
matrices multiply to the identity in the reverse order as well. -/
theorem outputDual_inputChange_identity (e : ℕ) (j k : OriginalIndex e) :
    (∑ new, inputChange e new j * outputDualChange e new k) =
      if j = k then 1 else 0 := by
  let A : Matrix (Index e) (OriginalIndex e) ℤ := outputDualChange e
  let B : Matrix (OriginalIndex e) (Index e) ℤ := fun old new => inputChange e new old
  have hAB : A * B = 1 := by
    ext j k
    change (∑ old, outputDualChange e j old * inputChange e k old) = _
    rw [show (∑ old, outputDualChange e j old * inputChange e k old) =
        ∑ old, inputChange e k old * outputDualChange e j old by
      apply Finset.sum_congr rfl; intro old hold; ring]
    rw [inputChange_outputDual_identity]
    simp [Matrix.one_apply, eq_comm]
  let ei : Index e ≃ OriginalIndex e := Fintype.equivOfCardEq (by
    simp [Index, OriginalIndex]
    omega)
  have hBA : B * A = 1 := (Matrix.mul_eq_one_comm_of_equiv ei).mp hAB
  exact congrFun (congrFun hBA j) k

/-- Apply the output inverse coordinates to one original monomial product. -/
theorem sum_output_source (d e : ℕ) (i : Fin (d + 1))
    (j : OriginalIndex e) (k : Index (d + e)) :
    (∑ z, outputDualChange (d + e) k z * sourceTensor d e i j z) =
      match j with
      | .inl j => outputDualChange (d + e) k (.inl ⟨i.val + j.val, by omega⟩)
      | .inr j => outputDualChange (d + e) k (.inr ⟨i.val + j.val, by omega⟩) := by
  cases j with
  | inl j =>
    simp only [Fintype.sum_sum_type, sourceTensor, mul_zero, Finset.sum_const_zero, add_zero]
    exact sum_coordinate_right (by omega) _
  | inr j =>
    simp only [Fintype.sum_sum_type, sourceTensor, mul_zero, Finset.sum_const_zero, zero_add]
    exact sum_coordinate_right (by omega) _

private theorem restrict_fixedFirst (d e : ℕ)
    (B : Index e → OriginalIndex e → ℤ)
    (C : Index (d + e) → OriginalIndex (d + e) → ℤ)
    (T : Tensor ℤ (Fin (d + 1)) (OriginalIndex e) (OriginalIndex (d + e)))
    (i : Fin (d + 1)) (j : Index e) (k : Index (d + e)) :
    Tensor.restrict (fixedFirst d) B C T i j k =
      ∑ y, ∑ z, B j y * C k z * T i y z := by
  simp [Tensor.restrict, fixedFirst, ite_mul]

/-- A concrete integral three-leg restriction, with the first leg fixed,
produces the simultaneously triangular multiplication tensor. -/
theorem sourceTensor_coordinate_change (d e : ℕ) :
    Tensor.restrict (fixedFirst d) (inputChange e) (outputDualChange (d + e))
      (sourceTensor d e) = adaptedTensor d e := by
  funext i j k
  rw [restrict_fixedFirst]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  simp_rw [sum_output_source]
  rw [sum_inputChange]
  cases j with
  | inl j =>
    by_cases hj : j.val < e + 1
    · cases k <;> simp only [dif_pos hj, outputDualChange, adaptedTensor]
      · simp [eq_comm]
      · have hjtop : j.val ≠ e + 1 := by omega
        simp [hjtop]
    · have hjtop : j.val = e + 1 := by omega
      cases k with
      | inl k => simp [hjtop, outputDualChange, adaptedTensor, Nat.add_assoc, eq_comm]
      | inr k =>
        simp only [dif_neg hj, outputDualChange, adaptedTensor, hjtop, true_and]
        have hcond : (k.val = i.val + e) ↔ (i.val < d ∧ e + i.val = k.val) := by
          have := k.isLt
          omega
        simp only [hcond]
  | inr j =>
    cases k <;> simp [outputDualChange, adaptedTensor, Nat.add_assoc, eq_comm]

/-- The only cross block is the quotient-to-kernel correction. -/
def erasedTensor (d e : ℕ) : Tensor ℤ (Fin (d + 1)) (Index e) (Index (d + e))
  | i, .inl j, .inr k =>
      if j.val = e + 1 ∧ i.val < d ∧ e + i.val = k.val then 1 else 0
  | _, _, _ => 0

theorem adaptedTensor_eq_graded_add_erased (d e : ℕ) :
    adaptedTensor d e = gradedTensor d e + erasedTensor d e := by
  funext i j k
  cases j <;> cases k <;> simp [adaptedTensor, gradedTensor, erasedTensor]

def inputScale (e : ℕ) : Index e → ℤ[X]
  | .inl _ => X
  | .inr _ => 1

def outputScale (e : ℕ) : Index e → ℤ[X]
  | .inl _ => 1
  | .inr _ => X

def diagonalMap {I : Type*} [DecidableEq I] (s : I → ℤ[X]) : I → I → ℤ[X] :=
  fun i j => if i = j then s i else 0

private theorem restrict_diagonal {I J K : Type*}
    [Fintype I] [Fintype J] [Fintype K]
    [DecidableEq I] [DecidableEq J] [DecidableEq K]
    (a : I → ℤ[X]) (b : J → ℤ[X]) (c : K → ℤ[X])
    (T : Tensor ℤ[X] I J K) (i : I) (j : J) (k : K) :
    Tensor.restrict (diagonalMap a) (diagonalMap b) (diagonalMap c) T i j k =
      a i * b j * c k * T i j k := by
  simp [Tensor.restrict, diagonalMap, ite_mul, mul_ite]

/-- A family on the adapted coordinates, before composing the integral
constant coordinate change on the original source. -/
def polynomialFamily (d e : ℕ) :
    Tensor ℤ[X] (Fin (d + 1)) (Index e) (Index (d + e)) :=
  Tensor.restrict (diagonalMap (fun _ => 1)) (diagonalMap (inputScale e))
    (diagonalMap (outputScale (d + e))) (fun i j k => C (adaptedTensor d e i j k))

/-- Actual polynomial maps from the original monomial tensor. -/
def leftMap (d : ℕ) (i j : Fin (d + 1)) : ℤ[X] := C (fixedFirst d i j)
def middleMap (e : ℕ) (j : Index e) (old : OriginalIndex e) : ℤ[X] :=
  inputScale e j * C (inputChange e j old)
def rightMap (e : ℕ) (k : Index e) (old : OriginalIndex e) : ℤ[X] :=
  outputScale e k * C (outputDualChange e k old)

/-- The family is a genuine three-leg polynomial restriction of the original
two-copy convolution, with the first leg unchanged. -/
theorem polynomialFamily_is_sourceRestriction (d e : ℕ) :
    polynomialFamily d e =
      Tensor.restrict (leftMap d) (middleMap e) (rightMap (d + e))
        (fun i j k => C (sourceTensor d e i j k)) := by
  have hc : (fun i j k => C (adaptedTensor d e i j k)) =
      Tensor.restrict (fun i j => C (fixedFirst d i j))
        (fun j old => C (inputChange e j old))
        (fun k old => C (outputDualChange (d + e) k old))
        (fun i j k => C (sourceTensor d e i j k)) := by
    rw [← sourceTensor_coordinate_change]
    funext i j k
    simp [Tensor.restrict]
  unfold polynomialFamily
  rw [hc, Tensor.restrict_restrict]
  have hleft : Tensor.composeRestrictionMatrix (diagonalMap (fun _ : Fin (d + 1) => 1))
      (fun i j => C (fixedFirst d i j)) = leftMap d := by
    funext i j
    simp [Tensor.composeRestrictionMatrix, diagonalMap, leftMap, ite_mul]
  have hmiddle : Tensor.composeRestrictionMatrix (diagonalMap (inputScale e))
      (fun j old => C (inputChange e j old)) = middleMap e := by
    funext j old
    simp [Tensor.composeRestrictionMatrix, diagonalMap, middleMap, ite_mul]
  have hright : Tensor.composeRestrictionMatrix (diagonalMap (outputScale (d + e)))
      (fun k old => C (outputDualChange (d + e) k old)) = rightMap (d + e) := by
    funext k old
    simp [Tensor.composeRestrictionMatrix, diagonalMap, rightMap, ite_mul]
  rw [hleft, hmiddle, hright]

theorem polynomialFamily_apply (d e : ℕ) (i : Fin (d + 1))
    (j : Index e) (k : Index (d + e)) :
    polynomialFamily d e i j k =
      inputScale e j * outputScale (d + e) k * C (adaptedTensor d e i j k) := by
  rw [polynomialFamily, restrict_diagonal]
  simp

/-- The exact integral lowest-order identity: the two matching blocks have
order one, while the cross block has order two. -/
theorem polynomialFamily_identity (d e : ℕ) (i : Fin (d + 1))
    (j : Index e) (k : Index (d + e)) :
    polynomialFamily d e i j k =
      X * C (gradedTensor d e i j k) + X ^ 2 * C (erasedTensor d e i j k) := by
  rw [polynomialFamily_apply]
  cases j <;> cases k
  all_goals simp only [inputScale, outputScale, adaptedTensor, gradedTensor, erasedTensor]
  all_goals (try split_ifs) <;> simp [pow_two]

/-- Complete coefficient certificate for the polynomial restriction. -/
theorem polynomialFamily_coeff (d e : ℕ) (i : Fin (d + 1))
    (j : Index e) (k : Index (d + e)) (n : ℕ) :
    (polynomialFamily d e i j k).coeff n =
      (if n = 1 then gradedTensor d e i j k else 0) +
        (if n = 2 then erasedTensor d e i j k else 0) := by
  rw [polynomialFamily_identity, Polynomial.coeff_add,
    mul_comm X (C (gradedTensor d e i j k)),
    mul_comm (X ^ 2) (C (erasedTensor d e i j k)),
    Polynomial.coeff_C_mul_X, Polynomial.coeff_C_mul_X_pow]

@[simp] theorem polynomialFamily_coeff_zero (d e : ℕ) (i : Fin (d + 1))
    (j : Index e) (k : Index (d + e)) : (polynomialFamily d e i j k).coeff 0 = 0 := by
  simp [polynomialFamily_coeff]

@[simp] theorem polynomialFamily_leading (d e : ℕ) (i : Fin (d + 1))
    (j : Index e) (k : Index (d + e)) :
    (polynomialFamily d e i j k).coeff 1 = gradedTensor d e i j k := by
  simp [polynomialFamily_coeff]

theorem leftMap_degree (d : ℕ) (i j : Fin (d + 1)) :
    (leftMap d i j).degree ≤ 0 := by
  simp [leftMap, fixedFirst]
  split_ifs <;> simp

theorem middleMap_degree (e : ℕ) (j : Index e) (old : OriginalIndex e) :
    (middleMap e j old).degree ≤ 1 := by
  cases j <;> cases old
  all_goals simp only [middleMap, inputScale, inputChange]
  all_goals (try split_ifs) <;> simp

theorem rightMap_degree (e : ℕ) (k : Index e) (old : OriginalIndex e) :
    (rightMap e k old).degree ≤ 1 := by
  cases k <;> cases old
  all_goals simp only [rightMap, outputScale, outputDualChange]
  all_goals (try split_ifs) <;> simp

/-- The quotient branch is exactly convolution with second width increased
by one; this is an equality of actual integer coefficients. -/
theorem gradedTensor_quotient (d e : ℕ) (i : Fin (d + 1))
    (j : Fin (e + 2)) (k : Fin (d + e + 2)) :
    gradedTensor d e i (.inl j) (.inl k) =
      IntegralConvolution.convolution ℤ (d + 1) (e + 2) i j (Fin.cast (by
        unfold IntegralConvolution.outputLength
        omega) k) := by
  simp [gradedTensor, IntegralConvolution.convolution]

/-- The kernel branch is convolution with second width decreased by one. -/
theorem gradedTensor_kernel (d e : ℕ) (i : Fin (d + 1))
    (j : Fin e) (k : Fin (d + e)) :
    gradedTensor d e i (.inr j) (.inr k) =
      IntegralConvolution.convolution ℤ (d + 1) e i j (Fin.cast (by
        unfold IntegralConvolution.outputLength
        omega) k) := by
  simp [gradedTensor, IntegralConvolution.convolution]

/-- The quotient matching sector, in its common original ambient spaces. -/
def quotientBranch (d e : ℕ) : Tensor ℤ (Fin (d + 1)) (Index e) (Index (d + e))
  | i, .inl j, .inl k => if i.val + j.val = k.val then 1 else 0
  | _, _, _ => 0

/-- The determinant-kernel matching sector in the same ambient spaces. -/
def kernelBranch (d e : ℕ) : Tensor ℤ (Fin (d + 1)) (Index e) (Index (d + e))
  | i, .inr j, .inr k => if i.val + j.val = k.val then 1 else 0
  | _, _, _ => 0

def branchFamily (d e : ℕ) (b : Fin 2) :
    Tensor ℤ (Fin (d + 1)) (Index e) (Index (d + e)) :=
  if b = 0 then quotientBranch d e else kernelBranch d e

def label (e : ℕ) : Index e → Fin 2
  | .inl _ => 0
  | .inr _ => 1

theorem branchFamily_labels (d e : ℕ) (b : Fin 2) (i : Fin (d + 1))
    (j : Index e) (k : Index (d + e)) (hn : branchFamily d e b i j k ≠ 0) :
    label e j = b ∧ label (d + e) k = b := by
  fin_cases b <;> cases j <;> cases k <;>
    simp_all [branchFamily, quotientBranch, kernelBranch, label]

/-- The lowest coefficient is precisely the sum of the two labelled sectors. -/
theorem sum_branchFamily (d e : ℕ) :
    (∑ b : Fin 2, branchFamily d e b) = gradedTensor d e := by
  funext i j k
  cases j <;> cases k <;>
    simp [Fin.sum_univ_two, branchFamily, quotientBranch, kernelBranch, gradedTensor]

theorem polynomialFamily_leading_branches (d e : ℕ) (i : Fin (d + 1))
    (j : Index e) (k : Index (d + e)) :
    (polynomialFamily d e i j k).coeff 1 = ∑ b : Fin 2, branchFamily d e b i j k := by
  rw [polynomialFamily_leading]
  have h := congrFun (congrFun (congrFun (sum_branchFamily d e) i) j) k
  simpa only [Finset.sum_apply] using h.symm

def quotientY (e : ℕ) (j : Fin (e + 2)) : Index e := .inl j

def quotientZ (d e : ℕ)
    (k : Fin (IntegralConvolution.outputLength (d + 1) (e + 2))) : Index (d + e) :=
  .inl ⟨k.val, by have := k.isLt; unfold IntegralConvolution.outputLength at this; omega⟩

def kernelY (e : ℕ) (j : Fin e) : Index e := .inr j

def kernelZ (d e : ℕ)
    (k : Fin (IntegralConvolution.outputLength (d + 1) e)) : Index (d + e) :=
  .inr ⟨k.val, by have := k.isLt; unfold IntegralConvolution.outputLength at this; omega⟩

theorem quotientY_injective (e : ℕ) : Function.Injective (quotientY e) := Sum.inl_injective

theorem kernelY_injective (e : ℕ) : Function.Injective (kernelY e) := Sum.inr_injective

theorem quotientZ_injective (d e : ℕ) : Function.Injective (quotientZ d e) := by
  intro j k h
  apply Fin.ext
  have hf := Sum.inl_injective h
  exact congrArg (fun t : Fin (d + e + 2) => t.val) hf

theorem kernelZ_injective (d e : ℕ) : Function.Injective (kernelZ d e) := by
  intro j k h
  apply Fin.ext
  have hf := Sum.inr_injective h
  exact congrArg (fun t : Fin (d + e) => t.val) hf

theorem quotientBranch_pullback (d e : ℕ) :
    Tensor.pullback id (quotientY e) (quotientZ d e) (quotientBranch d e) =
      IntegralConvolution.convolution ℤ (d + 1) (e + 2) := by
  rfl

theorem kernelBranch_pullback (d e : ℕ) :
    Tensor.pullback id (kernelY e) (kernelZ d e) (kernelBranch d e) =
      IntegralConvolution.convolution ℤ (d + 1) e := by
  rfl

/-- The larger branch is the actual zero extension of its convolution. -/
theorem quotientBranch_eq_extension (d e : ℕ) :
    quotientBranch d e = Tensor.restrict
      (fun x i => if i = x then 1 else 0)
      (fun y j => if quotientY e j = y then 1 else 0)
      (fun z k => if quotientZ d e k = z then 1 else 0)
      (IntegralConvolution.convolution ℤ (d + 1) (e + 2)) := by
  have hs (i : Fin (d + 1)) (j : Index e) (k : Index (d + e))
      (hn : quotientBranch d e i j k ≠ 0) :
      i ∈ Set.range (id : Fin (d + 1) → Fin (d + 1)) ∧
        j ∈ Set.range (quotientY e) ∧ k ∈ Set.range (quotientZ d e) := by
    cases j with
    | inl j =>
      cases k with
      | inl k =>
        refine ⟨⟨i, rfl⟩, ⟨j, rfl⟩, ⟨⟨k.val, ?_⟩, rfl⟩⟩
        have := k.isLt
        unfold IntegralConvolution.outputLength
        omega
      | inr k => exact False.elim (hn rfl)
    | inr j => exact False.elim (hn rfl)
  have heq := OAI.MatrixMultiplication.AuxiliarySeparation.tensor_eq_extendByZero_pullback
    (quotientBranch d e) id (quotientY e) (quotientZ d e)
    Function.injective_id (quotientY_injective e) (quotientZ_injective d e) hs
  rw [quotientBranch_pullback] at heq
  convert heq using 1
  congr 1 <;> funext x i <;> (try dsimp only [id_eq]) <;> split_ifs <;> rfl

/-- The smaller branch is likewise the integral zero extension of convolution. -/
theorem kernelBranch_eq_extension (d e : ℕ) :
    kernelBranch d e = Tensor.restrict
      (fun x i => if i = x then 1 else 0)
      (fun y j => if kernelY e j = y then 1 else 0)
      (fun z k => if kernelZ d e k = z then 1 else 0)
      (IntegralConvolution.convolution ℤ (d + 1) e) := by
  have hs (i : Fin (d + 1)) (j : Index e) (k : Index (d + e))
      (hn : kernelBranch d e i j k ≠ 0) :
      i ∈ Set.range (id : Fin (d + 1) → Fin (d + 1)) ∧
        j ∈ Set.range (kernelY e) ∧ k ∈ Set.range (kernelZ d e) := by
    cases j with
    | inr j =>
      cases k with
      | inr k =>
        refine ⟨⟨i, rfl⟩, ⟨j, rfl⟩, ⟨⟨k.val, ?_⟩, rfl⟩⟩
        have := k.isLt
        unfold IntegralConvolution.outputLength
        omega
      | inl k => exact False.elim (hn rfl)
    | inl j => exact False.elim (hn rfl)
  have heq := OAI.MatrixMultiplication.AuxiliarySeparation.tensor_eq_extendByZero_pullback
    (kernelBranch d e) id (kernelY e) (kernelZ d e)
    Function.injective_id (kernelY_injective e) (kernelZ_injective d e) hs
  rw [kernelBranch_pullback] at heq
  convert heq using 1
  congr 1 <;> funext x i <;> (try dsimp only [id_eq]) <;> split_ifs <;> rfl

open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring

theorem classOf_quotientBranch (d e : ℕ) :
    classOf (quotientBranch d e) =
      classOf (IntegralConvolution.convolution ℤ (d + 1) (e + 2)) := by
  apply (classOf_eq_iff _ _).mpr
  constructor
  · exact ⟨_, _, _, quotientBranch_eq_extension d e⟩
  · have h := IsRestriction.pullback (quotientBranch d e) id (quotientY e) (quotientZ d e)
    rw [quotientBranch_pullback] at h
    exact h

theorem classOf_kernelBranch (d e : ℕ) :
    classOf (kernelBranch d e) = classOf (IntegralConvolution.convolution ℤ (d + 1) e) := by
  apply (classOf_eq_iff _ _).mpr
  constructor
  · exact ⟨_, _, _, kernelBranch_eq_extension d e⟩
  · have h := IsRestriction.pullback (kernelBranch d e) id (kernelY e) (kernelZ d e)
    rw [kernelBranch_pullback] at h
    exact h

/-- Integral coordinate permutations identify the original class with the
product class of convolution and the two-coordinate pairing. -/
theorem classOf_sourceTensor_product (d e : ℕ) :
    classOf (sourceTensor d e) =
      classOf (IntegralConvolution.convolution ℤ (d + 1) (e + 1)) * classOf pairingTensor := by
  let ex : Fin (d + 1) ≃ Fin (d + 1) × PUnit := (Equiv.prodPUnit (Fin (d + 1))).symm
  let ey := originalCoordinateEquiv e
  let ez : OriginalIndex (d + e) ≃
      Fin (IntegralConvolution.outputLength (d + 1) (e + 1)) × Bool :=
    (originalCoordinateEquiv (d + e)).trans
    (Equiv.prodCongr (finCongr (by unfold IntegralConvolution.outputLength; omega))
      (Equiv.refl Bool))
  rw [← classOf_product]
  apply classOf_eq_of_reindex ex ey ez
  funext i j k
  cases j <;> cases k <;>
    simp [ex, ey, ez, originalCoordinateEquiv, originalCoordinate, Tensor.pullback,
      Tensor.product, pairingTensor, sourceTensor, IntegralConvolution.convolution]

theorem classOf_adapted_le_source (d e : ℕ) :
    classOf (adaptedTensor d e) ≤ classOf (sourceTensor d e) :=
  (classOf_le_iff _ _).mpr ⟨_, _, _, (sourceTensor_coordinate_change d e).symm⟩

theorem sourceTensor_zeroOne (d e : ℕ) (i : Fin (d + 1))
    (j : OriginalIndex e) (k : OriginalIndex (d + e)) :
    sourceTensor d e i j k = 0 ∨ sourceTensor d e i j k = 1 := by
  cases j <;> cases k <;> simp only [sourceTensor]
  all_goals (try split_ifs) <;> simp

theorem adaptedTensor_zeroOne (d e : ℕ) (i : Fin (d + 1))
    (j : Index e) (k : Index (d + e)) :
    adaptedTensor d e i j k = 0 ∨ adaptedTensor d e i j k = 1 := by
  cases j <;> cases k <;> simp only [adaptedTensor]
  all_goals (try split_ifs) <;> simp

theorem gradedTensor_zeroOne (d e : ℕ) (i : Fin (d + 1))
    (j : Index e) (k : Index (d + e)) :
    gradedTensor d e i j k = 0 ∨ gradedTensor d e i j k = 1 := by
  cases j <;> cases k <;> simp only [gradedTensor]
  all_goals (try split_ifs) <;> simp

theorem branchFamily_zeroOne (d e : ℕ) (b : Fin 2) (i : Fin (d + 1))
    (j : Index e) (k : Index (d + e)) :
    branchFamily d e b i j k = 0 ∨ branchFamily d e b i j k = 1 := by
  unfold branchFamily
  split_ifs <;> cases j <;> cases k
  all_goals simp only [quotientBranch, kernelBranch]
  all_goals (try split_ifs) <;> simp

#print axioms inputChange_outputDual_identity
#print axioms outputDual_inputChange_identity
#print axioms sourceTensor_coordinate_change
#print axioms polynomialFamily_is_sourceRestriction
#print axioms polynomialFamily_leading_branches
#print axioms classOf_sourceTensor_product

end
end Matmul.IntegralDeterminant
