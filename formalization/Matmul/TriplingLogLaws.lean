import Matmul.ConvolutionCharacter
import Matmul.SharedLegEntropyBackend
import Matmul.IntegralTripling

/-!
# Character inequalities from the integral three-sector filtration

The three retained branches share the original first coordinate space. Each
branch is identified with its actual oriented convolution by integral graph
embeddings, including the first-coordinate reversal in the middle branch.
-/

namespace Matmul.TriplingLogLaws

open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.AuxiliarySeparation.Sector
open Matmul.SharedLegEntropy Matmul.ConvolutionCharacter
open scoped BigOperators

noncomputable section

theorem value_source (φ : IntegralCharacter) (r s : ℕ) :
    φ.value (source r s) = valueXY φ r (3 * s + r - 1) := rfl

/-- The shifted polynomial restriction has the retained tensor as its first
coefficient, so every integral character decreases under this degeneration. -/
theorem value_retained_le_source (φ : IntegralCharacter) (r s : ℕ) :
    φ.value (retained r s) ≤ φ.value (source r s) := by
  apply Matmul.PolynomialCoefficient.polynomialRestrictionMonotone φ
    (source r s) (retained r s) (leftMap r) (middleMap r s) (rightMap r s) 1
  · intro n hn
    have hn0 : n = 0 := by omega
    subst n
    funext i j k
    exact polynomial_coeff_zero r s i j k
  · funext i j k
    exact polynomial_coeff_one r s i j k

/-- Ordinary convolution is recovered from the left branch by its integral
coordinate embedding, and extension in the opposite direction loses nothing. -/
theorem value_leftTensor (φ : IntegralCharacter) (r s : ℕ) :
    φ.value (leftTensor r s) = valueXY φ r s := by
  apply le_antisymm
  · rw [leftTensor_eq_extension]
    exact φ.monotone _ _ _ _
  · have hp := φ.value_pullback_le (leftTensor r s) id (leftY r s) (leftZ r s)
    rwa [leftTensor_pullback] at hp

theorem value_rightTensor (φ : IntegralCharacter) (r s : ℕ) :
    φ.value (rightTensor r s) = valueXY φ r s := by
  apply le_antisymm
  · rw [rightTensor_eq_extension]
    exact φ.monotone _ _ _ _
  · have hp := φ.value_pullback_le (rightTensor r s) id (rightY r s) (rightZ r s)
    rwa [rightTensor_pullback] at hp

/-- The middle branch has the last two convolution axes exchanged. Its
first-coordinate reversal is part of the proved restriction maps. -/
theorem value_middleTensor (φ : IntegralCharacter) (r s : ℕ) :
    φ.value (middleTensor r s) = valueXZ φ r s := by
  apply le_antisymm
  · rw [middleTensor_eq_extension]
    exact φ.monotone _ _ _ _
  · have hp := φ.value_pullback_le (middleTensor r s) Fin.rev (middleY r s) (middleZ r s)
    rwa [middleTensor_pullback] at hp

theorem value_branchFamily (φ : IntegralCharacter) (r s : ℕ) (b : Fin 3) :
    φ.value (branchFamily r s b) = if b = 1 then valueXZ φ r s else valueXY φ r s := by
  fin_cases b <;>
    simp [branchFamily, value_leftTensor, value_middleTensor, value_rightTensor]

/-- Recalling the two matching interval labels recovers the actual retained
coefficient tensor, rather than an independently assumed shared-leg model. -/
theorem sharedFirst_branches_pullback (r s : ℕ) :
    Tensor.pullback id (fun j => (yLabel r s j, j))
      (fun k => (zLabel r s k, k)) (sharedFirstTensor (branchFamily r s)) =
      retained r s := by
  funext i j k
  have hsum : (∑ b : Fin 3, branchFamily r s b i j k) = retained r s i j k := by
    have h := congrFun (congrFun (congrFun (sum_branchFamily r s) i) j) k
    simpa only [Finset.sum_apply] using h
  change (if yLabel r s j = zLabel r s k then
    branchFamily r s (yLabel r s j) i j k else 0) = retained r s i j k
  rw [← hsum]
  by_cases hjk : yLabel r s j = zLabel r s k
  · rw [if_pos hjk]
    symm
    apply Finset.sum_eq_single (yLabel r s j)
    · intro b hb hbl
      by_contra hn
      exact hbl (branchFamily_labels r s b i j k hn).1.symm
    · simp
  · rw [if_neg hjk]
    symm
    apply Finset.sum_eq_zero
    intro b hb
    by_contra hn
    obtain ⟨hy, hz⟩ := branchFamily_labels r s b i j k hn
    exact hjk (hy.trans hz.symm)

/-- Matching interval labels give an actual zero extension of the retained
tensor into the shared-leg ambient coordinates. -/
theorem sharedFirst_branches_extension (r s : ℕ) :
    sharedFirstTensor (branchFamily r s) = Tensor.restrict
      (fun x' x => if x = x' then 1 else 0)
      (fun y' j => if (yLabel r s j, j) = y' then 1 else 0)
      (fun z' k => if (zLabel r s k, k) = z' then 1 else 0)
      (retained r s) := by
  have hs (i : Fin r) (j : Fin 3 × YIndex r s) (k : Fin 3 × ZIndex r s)
      (hn : sharedFirstTensor (branchFamily r s) i j k ≠ 0) :
      i ∈ Set.range (id : Fin r → Fin r) ∧
        j ∈ Set.range (fun y => (yLabel r s y, y)) ∧
        k ∈ Set.range (fun z => (zLabel r s z, z)) := by
    have hjk : j.1 = k.1 := by
      by_contra h
      exact hn (by simp [sharedFirstTensor, h])
    have hb : branchFamily r s j.1 i j.2 k.2 ≠ 0 := by
      simpa [sharedFirstTensor, hjk] using hn
    obtain ⟨hj, hk⟩ := branchFamily_labels r s j.1 i j.2 k.2 hb
    exact ⟨⟨i, rfl⟩, ⟨j.2, by simp [hj]⟩, ⟨k.2, by simp [hk, hjk]⟩⟩
  have ht := tensor_eq_extendByZero_pullback (sharedFirstTensor (branchFamily r s))
    id (fun j => (yLabel r s j, j)) (fun k => (zLabel r s k, k))
    Function.injective_id (fun _ _ h => congrArg Prod.snd h)
    (fun _ _ h => congrArg Prod.snd h) hs
  rw [sharedFirst_branches_pullback] at ht
  convert ht using 1
  congr 1 <;> funext x i <;> (try dsimp only [id_eq]) <;> split_ifs <;> rfl

theorem value_sharedFirst_branches (φ : IntegralCharacter) (r s : ℕ) :
    φ.value (sharedFirstTensor (branchFamily r s)) = φ.value (retained r s) := by
  apply le_antisymm
  · rw [sharedFirst_branches_extension]
    exact φ.monotone _ _ _ _
  · have hp := φ.value_pullback_le (sharedFirstTensor (branchFamily r s)) id
      (fun j => (yLabel r s j, j)) (fun k => (zLabel r s k, k))
    rwa [sharedFirst_branches_pullback] at hp

theorem value_retained_pos (φ : IntegralCharacter) (r s : ℕ)
    (hr : 1 ≤ r) (hs : 1 ≤ s) : 0 < φ.value (retained r s) := by
  have hp := φ.value_pullback_le (sharedFirstTensor (branchFamily r s)) id
    (fun j => ((0 : Fin 3), j)) (fun k => ((0 : Fin 3), k))
  have heq : Tensor.pullback id (fun j => ((0 : Fin 3), j))
      (fun k => ((0 : Fin 3), k)) (sharedFirstTensor (branchFamily r s)) =
      branchFamily r s 0 := by
    funext i j k
    simp [Tensor.pullback, sharedFirstTensor]
  rw [heq, value_sharedFirst_branches, value_branchFamily] at hp
  simp only [show (0 : Fin 3) ≠ 1 by decide, if_false] at hp
  exact (valueXY_pos φ r s hr hs).trans_le hp

/-- Exact finite entropy inequality for the three actual integral sectors. -/
theorem tripling_log (φ : IntegralCharacter) (q : FiniteLaw (Fin 3))
    (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s) :
    φ.pX * finiteEntropy q.mass + q.mass 0 * Real.log (valueXY φ r s) +
      q.mass 1 * Real.log (valueXZ φ r s) + q.mass 2 * Real.log (valueXY φ r s) ≤
        Real.log (valueXY φ r (3 * s + r - 1)) := by
  have hB (b : Fin 3) : 0 < φ.value (branchFamily r s b) := by
    rw [value_branchFamily]
    split_ifs
    · exact valueXZ_pos φ r s hr hs
    · exact valueXY_pos φ r s hr hs
  have h := Matmul.SharedLegEntropyBackend.fullLogSharedFirst_tag φ q (branchFamily r s) hB
  rw [value_sharedFirst_branches] at h
  have hg := Real.log_le_log (value_retained_pos φ r s hr hs)
    (value_retained_le_source φ r s)
  rw [value_source] at hg
  simp [Fin.sum_univ_three, value_branchFamily] at h
  linarith

/-- Grouping the equal outer-branch convolution values gives the scalar law
used by the integer profiles. -/
theorem tripling_log_grouped (φ : IntegralCharacter) (q : FiniteLaw (Fin 3))
    (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s) :
    φ.pX * finiteEntropy q.mass + (q.mass 0 + q.mass 2) * Real.log (valueXY φ r s) +
      q.mass 1 * Real.log (valueXZ φ r s) ≤
        Real.log (valueXY φ r (3 * s + r - 1)) := by
  have h := tripling_log φ q r s hr hs
  nlinarith

#print axioms value_retained_le_source
#print axioms value_middleTensor
#print axioms value_sharedFirst_branches
#print axioms tripling_log
#print axioms tripling_log_grouped

end
end Matmul.TriplingLogLaws
