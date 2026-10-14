import Matmul.IntegerProfileCap
import Matmul.MatrixCharacter
import Matmul.IntegralSpectrumDuality
import Matmul.UniversalRecursiveAlgorithm
import Matmul.RectangularContinuity

/-!
# Finite integral schemes on the rectangular curve

The actual character cap, integral spectral duality, and a tensor power
produce one finite integer scheme. Its coefficients and gate-count parameters
are chosen before choosing the ring in which the scheme is evaluated.
-/

namespace Matmul.RectangularRankBridge

open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
open Matmul.IntegralSpectrum Matmul.UniversalRecursiveAlgorithm
open Matmul.IntegerBilinear Matmul.RectangularOptimization

noncomputable section

theorem pow_rpow_comm {x : ℝ} (hx : 0 ≤ x) (n : ℕ) (y : ℝ) :
    (x ^ n) ^ y = (x ^ y) ^ n := by
  rw [← Real.rpow_natCast_mul hx, ← Real.rpow_mul_natCast hx, mul_comm]

/-- A single finite base algorithm sufficient for recursive rectangular
programs of aspect exponent `k` and target exponent `E`. -/
structure SchemeCertificate (k E : ℝ) where
  a : ℕ
  b : ℕ
  ρ : ℕ
  alg : Scheme a b a ρ
  a_ge_two : 2 ≤ a
  b_pos : 0 < b
  correct : alg.tensor = matrixTensor a b a
  shape : (a : ℝ) ^ k ≤ (b : ℝ)
  volume : Matmul.RecursiveCost.blockVolume a b a ≤ ρ
  rankExponent_lt : Real.log (ρ : ℝ) / Real.log (a : ℝ) < E

theorem matrix_asymptoticRank_ceil_le {q : ℕ} (hq : 2 ≤ q)
    {k : ℝ} (hk : 0 ≤ k) :
    asymptoticRank (UnitTensorClass.matrixClass q (Nat.ceil ((q : ℝ) ^ k)) q) ≤
      2 * (q : ℝ) ^ rectangularBound k := by
  apply asymptoticRank_le_of_character_bound
  · have hqR : 1 ≤ (q : ℝ) := by exact_mod_cast (show 1 ≤ q by omega)
    have hf : 0 ≤ rectangularBound k :=
      (by norm_num : (0 : ℝ) ≤ 2).trans (two_le_rectangularBound hk)
    have hp := Real.one_le_rpow hqR hf
    linarith
  · intro χ hχ
    apply Matmul.MatrixCharacter.matrixClass_ceil_le χ hχ hq hk
    exact Matmul.IntegerProfileCap.actual_rectangular_objective_le
      (Matmul.IntegralCharacter.ofUnitTensorClassHom χ hχ) k hk

theorem exists_large_power_two {δ : ℝ} (hδ : 0 < δ) :
    ∃ q : ℕ, 2 ≤ q ∧ 2 < (q : ℝ) ^ δ := by
  have hp : 1 < (2 : ℝ) ^ δ := Real.one_lt_rpow (by norm_num) hδ
  obtain ⟨t, ht⟩ := pow_unbounded_of_one_lt (2 : ℝ) hp
  have htpos : 0 < t := by
    by_contra h
    have hz : t = 0 := by omega
    simp [hz] at ht
  refine ⟨2 ^ t, ?_, ?_⟩
  · exact Nat.le_pow htpos
  · simpa only [Nat.cast_pow, Nat.cast_ofNat, pow_rpow_comm (by norm_num : (0 : ℝ) ≤ 2)]
      using ht

/-- The bound is realized by actual integer rank certificates, with every
positive slack. No profile law or spectral-duality assumption remains. -/
theorem exists_scheme_certificate {k ε : ℝ} (hk : 0 ≤ k) (hε : 0 < ε) :
    Nonempty (SchemeCertificate k (rectangularBound k + ε)) := by
  classical
  obtain ⟨q, hq, hlarge⟩ := exists_large_power_two hε
  let inner := Nat.ceil ((q : ℝ) ^ k)
  have hqpos : 0 < q := by omega
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hqpos
  have hqone : 1 < (q : ℝ) := by exact_mod_cast (show 1 < q by omega)
  have hi : 0 < inner := by
    have hc := Nat.le_ceil ((q : ℝ) ^ k)
    have hp := Real.one_le_rpow hqone.le hk
    by_contra h
    have hz : inner = 0 := by omega
    change Nat.ceil ((q : ℝ) ^ k) = 0 at hz
    rw [hz, Nat.cast_zero] at hc
    linarith
  have hstrict : asymptoticRank (UnitTensorClass.matrixClass q inner q) <
      (q : ℝ) ^ (rectangularBound k + ε) := by
    have hupper := matrix_asymptoticRank_ceil_le hq hk
    have hmul := mul_lt_mul_of_pos_right hlarge
      (Real.rpow_pos_of_pos hqR (rectangularBound k))
    rw [Real.rpow_add hqR]
    exact hupper.trans_lt (by simpa only [mul_comm] using hmul)
  obtain ⟨m, hm, hrank⟩ := exists_rank_power_lt
    (UnitTensorClass.matrixClass_ne_zero hqpos hi hqpos) hstrict
  let a := q ^ m
  let b := inner ^ m
  let ρ := UnitTensorClass.rank (UnitTensorClass.matrixClass a b a)
  have ha : 0 < a := pow_pos hqpos m
  have hb : 0 < b := pow_pos hi m
  have ha2 : 2 ≤ a := by
    exact hq.trans (Nat.le_pow hm)
  have hρeq : ρ = UnitTensorClass.rank
      (UnitTensorClass.matrixClass q inner q ^ m) := by
    dsimp [ρ, a, b]
    rw [UnitTensorClass.matrixClass_pow]
  have hρlt : (ρ : ℝ) < (a : ℝ) ^ (rectangularBound k + ε) := by
    rw [hρeq]
    simpa only [a, Nat.cast_pow, pow_rpow_comm hqR.le] using hrank
  have hvolume : Matmul.RecursiveCost.blockVolume a b a ≤ ρ := by
    have h := UnitTensorClass.rank_matrixClass_lower ha hb ha
    dsimp [Matmul.RecursiveCost.blockVolume]
    dsimp [ρ] at h ⊢
    simpa only [max_assoc, Nat.mul_comm] using h
  have hρpos : 0 < ρ := by
    have hv : 0 < Matmul.RecursiveCost.blockVolume a b a :=
      lt_of_lt_of_le (Nat.mul_pos ha hb) (le_max_left _ _)
    omega
  obtain ⟨alg, halg⟩ := rankAtMost_iff_exists_algorithm.mp
    (show Tensor.RankAtMost (matrixTensor a b a) ρ by
      simpa only [ρ, UnitTensorClass.rank_matrixClass] using exactRank_spec (matrixTensor a b a))
  refine ⟨⟨a, b, ρ, alg, ha2, hb, halg, ?_, hvolume, ?_⟩⟩
  · have hp := pow_le_pow_left₀ (Real.rpow_nonneg hqR.le k)
      (Nat.le_ceil ((q : ℝ) ^ k)) m
    simpa only [a, b, inner, Nat.cast_pow, pow_rpow_comm hqR.le] using hp
  · have haR : 1 < (a : ℝ) := by exact_mod_cast (show 1 < a by omega)
    have hρR : 0 < (ρ : ℝ) := by exact_mod_cast hρpos
    have hlog := Real.log_lt_log hρR hρlt
    rw [Real.log_rpow (by linarith : 0 < (a : ℝ))] at hlog
    exact (div_lt_iff₀ (Real.log_pos haR)).mpr (by simpa only [mul_comm] using hlog)

#print axioms matrix_asymptoticRank_ceil_le
#print axioms exists_scheme_certificate

end
end Matmul.RectangularRankBridge
