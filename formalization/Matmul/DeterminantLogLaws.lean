import Matmul.ConvolutionCharacter
import Matmul.SharedLegEntropyBackend
import Matmul.IntegralDeterminant

/-!
# Character inequalities from the integral determinant filtration

The two matching sectors are identified with the actual shared-first tensor
by integral graph embeddings. The graded tensor is the first coefficient of
the polynomial restriction constructed in `IntegralDeterminant`.
-/

namespace Matmul.DeterminantLogLaws

open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
open Matmul.IntegralDeterminant Matmul.SharedLegEntropy
open Matmul.ConvolutionCharacter Matmul.IntegerCharacter
open scoped BigOperators

noncomputable section

/-- Mutual integral restrictions give equality for every coefficient character. -/
theorem value_of_classOf_eq (φ : IntegralCharacter)
    {X Y Z U V W : Type} [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor ℤ X Y Z) (S : Tensor ℤ U V W)
    (h : classOf T = classOf S) : φ.value T = φ.value S := by
  obtain ⟨hTS, hST⟩ := (classOf_eq_iff T S).mp h
  obtain ⟨A, B, C, hT⟩ := hTS
  obtain ⟨D, E, F, hS⟩ := hST
  apply le_antisymm
  · rw [hT]
    exact φ.monotone S A B C
  · rw [hS]
    exact φ.monotone T D E F

theorem value_pairingTensor (φ : IntegralCharacter) :
    φ.value pairingTensor = (2 : ℝ) ^ φ.pX := by
  have heq : pairingTensor = Tensor.pullback (Equiv.refl PUnit)
      finTwoEquiv.symm finTwoEquiv.symm (dotX 2) := by
    funext x y z
    simp [pairingTensor, Tensor.pullback, dotX]
  rw [heq, φ.value_reindex]
  exact φ.value_dotX (by norm_num)

theorem value_sourceTensor (φ : IntegralCharacter) (d e : ℕ) :
    φ.value (sourceTensor d e) = valueXY φ (d + 1) (e + 1) * (2 : ℝ) ^ φ.pX := by
  have hc : classOf (sourceTensor d e) = classOf
      (Tensor.product (CXY (d + 1) (e + 1)) pairingTensor) := by
    rw [classOf_product]
    exact classOf_sourceTensor_product d e
  rw [value_of_classOf_eq φ _ _ hc, φ.map_product, value_pairingTensor]
  rfl

/-- The polynomial coordinate maps yield the genuine determinant degeneration. -/
theorem value_graded_le_source (φ : IntegralCharacter) (d e : ℕ) :
    φ.value (gradedTensor d e) ≤ φ.value (sourceTensor d e) := by
  apply Matmul.PolynomialCoefficient.polynomialRestrictionMonotone φ
    (sourceTensor d e) (gradedTensor d e) (leftMap d) (middleMap e)
    (rightMap (d + e)) 1
  · intro n hn
    have hn0 : n = 0 := by omega
    subst n
    rw [← polynomialFamily_is_sourceRestriction]
    funext i j k
    exact polynomialFamily_coeff_zero d e i j k
  · rw [← polynomialFamily_is_sourceRestriction]
    funext i j k
    exact polynomialFamily_leading d e i j k

/-- Adding a remembered sector label only inserts zero coordinates. -/
theorem sharedFirst_branches_pullback (d e : ℕ) :
    Tensor.pullback id (fun j => (label e j, j))
      (fun k => (label (d + e) k, k)) (sharedFirstTensor (branchFamily d e)) =
      gradedTensor d e := by
  funext i j k
  cases j <;> cases k <;>
    simp [Tensor.pullback, sharedFirstTensor, label, branchFamily,
      quotientBranch, kernelBranch, gradedTensor]

theorem sharedFirst_branches_extension (d e : ℕ) :
    sharedFirstTensor (branchFamily d e) = Tensor.restrict
      (fun x' x => if x = x' then 1 else 0)
      (fun y' j => if (label e j, j) = y' then 1 else 0)
      (fun z' k => if (label (d + e) k, k) = z' then 1 else 0)
      (gradedTensor d e) := by
  have hs (i : Fin (d + 1)) (j : Fin 2 × Index e) (k : Fin 2 × Index (d + e))
      (hn : sharedFirstTensor (branchFamily d e) i j k ≠ 0) :
      i ∈ Set.range (id : Fin (d + 1) → Fin (d + 1)) ∧
        j ∈ Set.range (fun y => (label e y, y)) ∧
        k ∈ Set.range (fun z => (label (d + e) z, z)) := by
    have hjk : j.1 = k.1 := by
      by_contra h
      exact hn (by simp [sharedFirstTensor, h])
    have hb : branchFamily d e j.1 i j.2 k.2 ≠ 0 := by
      simpa [sharedFirstTensor, hjk] using hn
    obtain ⟨hj, hk⟩ := branchFamily_labels d e j.1 i j.2 k.2 hb
    exact ⟨⟨i, rfl⟩, ⟨j.2, by simp [hj]⟩, ⟨k.2, by simp [hk, hjk]⟩⟩
  have ht := tensor_eq_extendByZero_pullback (sharedFirstTensor (branchFamily d e))
    id (fun j => (label e j, j)) (fun k => (label (d + e) k, k))
    Function.injective_id (fun _ _ h => congrArg Prod.snd h)
    (fun _ _ h => congrArg Prod.snd h) hs
  rw [sharedFirst_branches_pullback] at ht
  convert ht using 1
  congr 1 <;> funext x i <;> (try dsimp only [id_eq]) <;> split_ifs <;> rfl

/-- Exact character equality follows from the graph restriction and its inverse. -/
theorem value_sharedFirst_branches (φ : IntegralCharacter) (d e : ℕ) :
    φ.value (sharedFirstTensor (branchFamily d e)) = φ.value (gradedTensor d e) := by
  apply le_antisymm
  · rw [sharedFirst_branches_extension]
    exact φ.monotone _ _ _ _
  · have hp := φ.value_pullback_le (sharedFirstTensor (branchFamily d e)) id
      (fun j => (label e j, j)) (fun k => (label (d + e) k, k))
    rwa [sharedFirst_branches_pullback] at hp

theorem value_quotientBranch (φ : IntegralCharacter) (d e : ℕ) :
    φ.value (quotientBranch d e) = valueXY φ (d + 1) (e + 2) :=
  value_of_classOf_eq φ _ _ (classOf_quotientBranch d e)

theorem value_kernelBranch (φ : IntegralCharacter) (d e : ℕ) :
    φ.value (kernelBranch d e) = valueXY φ (d + 1) e :=
  value_of_classOf_eq φ _ _ (classOf_kernelBranch d e)

theorem value_branchFamily (φ : IntegralCharacter) (d e : ℕ) (b : Fin 2) :
    φ.value (branchFamily d e b) =
      if b = 0 then valueXY φ (d + 1) (e + 2) else valueXY φ (d + 1) e := by
  unfold branchFamily
  split_ifs <;> simp only [value_quotientBranch, value_kernelBranch]

/-- Both nonempty determinant sectors give the exact finite entropy inequality. -/
theorem determinant_log_succ (φ : IntegralCharacter) (q : FiniteLaw (Fin 2))
    (d e : ℕ) (he : 1 ≤ e) :
    φ.pX * finiteEntropy q.mass +
      q.mass 0 * Real.log (valueXY φ (d + 1) (e + 2)) +
      q.mass 1 * Real.log (valueXY φ (d + 1) e) ≤
        Real.log (valueXY φ (d + 1) (e + 1)) + φ.pX * Real.log 2 := by
  have hB (b : Fin 2) : 0 < φ.value (branchFamily d e b) := by
    rw [value_branchFamily]
    split_ifs <;> exact valueXY_pos φ _ _ (by omega) (by omega)
  have h := Matmul.SharedLegEntropyBackend.fullLogSharedFirst_tag φ q (branchFamily d e) hB
  rw [value_sharedFirst_branches] at h
  have hg := value_graded_le_source φ d e
  have hgp : 0 < φ.value (gradedTensor d e) := by
    have hp := φ.value_pullback_le (gradedTensor d e) id (quotientY e) (quotientZ d e)
    have heq : Tensor.pullback id (quotientY e) (quotientZ d e) (gradedTensor d e) =
        CXY (d + 1) (e + 2) := by rfl
    rw [heq] at hp
    exact (valueXY_pos φ _ _ (by omega) (by omega)).trans_le hp
  have hlog := Real.log_le_log hgp hg
  rw [value_sourceTensor, Real.log_mul (valueXY_pos φ _ _ (by omega) (by omega)).ne'
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).ne',
    Real.log_rpow (by norm_num : (0 : ℝ) < 2)] at hlog
  simp [Fin.sum_univ_two, value_branchFamily] at h
  linarith

/-- The determinant law on arbitrary positive integer widths. -/
theorem determinant_log (φ : IntegralCharacter) (q : FiniteLaw (Fin 2))
    (r s : ℕ) (hr : 1 ≤ r) (hs : 2 ≤ s) :
    φ.pX * finiteEntropy q.mass +
      q.mass 0 * Real.log (valueXY φ r (s + 1)) +
      q.mass 1 * Real.log (valueXY φ r (s - 1)) ≤
        Real.log (valueXY φ r s) + φ.pX * Real.log 2 := by
  have h := determinant_log_succ φ q (r - 1) (s - 1) (by omega)
  simpa only [show r - 1 + 1 = r by omega, show s - 1 + 2 = s + 1 by omega,
    show s - 1 + 1 = s by omega] using h

/-- At second width one the kernel is empty, so only the quotient is used. -/
theorem determinant_endpoint (φ : IntegralCharacter) (r : ℕ) (hr : 1 ≤ r) :
    valueXY φ r 2 ≤ valueXY φ r 1 * (2 : ℝ) ^ φ.pX := by
  have hg := value_graded_le_source φ (r - 1) 0
  have hp := φ.value_pullback_le (gradedTensor (r - 1) 0) id (quotientY 0)
    (quotientZ (r - 1) 0)
  have heq : Tensor.pullback id (quotientY 0) (quotientZ (r - 1) 0)
      (gradedTensor (r - 1) 0) = CXY (r - 1 + 1) 2 := by rfl
  rw [heq] at hp
  change valueXY φ (r - 1 + 1) 2 ≤ φ.value (gradedTensor (r - 1) 0) at hp
  rw [value_sourceTensor] at hg
  simpa only [show r - 1 + 1 = r by omega, Nat.zero_add] using hp.trans hg

#print axioms value_graded_le_source
#print axioms value_sharedFirst_branches
#print axioms determinant_log
#print axioms determinant_endpoint

end
end Matmul.DeterminantLogLaws
