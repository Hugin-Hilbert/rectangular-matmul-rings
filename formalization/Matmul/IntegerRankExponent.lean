import Matmul.IntegerScalar
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# The concrete integral matrix multiplication rank exponent

This follows the real-analysis definitions and proofs in the upstream
`AuxiliarySeparation/Arithmetic/RankExponent.lean`, with exact tensor rank
computed over ℤ. In particular, an exponent approximation supplies an actual
integral rank decomposition, which can be evaluated over every ring.
-/

namespace OAI

noncomputable section

open MatrixMultiplication.Foundation

namespace MatrixMultiplication.AuxiliarySeparation

/-- Exact rank over ℤ of the square matrix multiplication tensor. -/
def exactMatrixRank (n : ℕ) : ℕ :=
  exactRank (Matmul.IntegerBilinear.matrixTensor n n n)

/-- Integral exact rank comes with an integral rank decomposition. -/
theorem exactMatrixRank_spec (n : ℕ) :
    Tensor.RankAtMost (Matmul.IntegerBilinear.matrixTensor n n n) (exactMatrixRank n) :=
  exactRank_spec _

/-- The usual algorithm uses `n³` integral simple tensors. -/
theorem matrixMultiplication_rankAtMost_cubic (n : ℕ) :
    Tensor.RankAtMost (Matmul.IntegerBilinear.matrixTensor n n n) (n ^ 3) := by
  simpa only [pow_succ, pow_zero, Nat.mul_one, Nat.one_mul, Nat.mul_assoc] using
    TensorSemiring.UnitTensorClass.matrixTensor_rankAtMost_cubic n n n

theorem exactMatrixRank_upper (n : ℕ) : exactMatrixRank n ≤ n ^ 3 :=
  exactRank_le (matrixMultiplication_rankAtMost_cubic n)

/-- An integral identity flattening forces the quadratic lower bound. -/
theorem matrixMultiplication_rank_lower {n R : ℕ} (hn : 0 < n)
    (hRank : Tensor.RankAtMost (Matmul.IntegerBilinear.matrixTensor n n n) R) :
    n ^ 2 ≤ R := by
  simpa only [pow_two] using matrixTensor_rank_lower_output hn hRank

theorem exactMatrixRank_lower {n : ℕ} (hn : 0 < n) : n ^ 2 ≤ exactMatrixRank n :=
  matrixMultiplication_rank_lower hn (exactMatrixRank_spec n)

theorem exactMatrixRank_pos {n : ℕ} (hn : 0 < n) : 0 < exactMatrixRank n :=
  lt_of_lt_of_le (pow_pos hn 2) (exactMatrixRank_lower hn)

@[simp] theorem exactMatrixRank_zero : exactMatrixRank 0 = 0 :=
  Nat.eq_zero_of_le_zero (by simpa using exactMatrixRank_upper 0)

@[simp] theorem exactMatrixRank_one : exactMatrixRank 1 = 1 := by
  apply le_antisymm
  · simpa using exactMatrixRank_upper 1
  · simpa using exactMatrixRank_lower (n := 1) zero_lt_one

/-- The set of finite exact-rank exponents in the definition of `ν`. -/
def exactRankExponentSet : Set ℝ :=
  {τ | ∃ n : ℕ, 2 ≤ n ∧ τ = Real.logb n (exactMatrixRank n)}

/-- The exact-rank exponent `ν = inf_{n ≥ 2} log(R(Tₙ))/log(n)`. -/
def exactRankExponent : ℝ := sInf exactRankExponentSet

theorem exactRankExponentSet_nonempty : exactRankExponentSet.Nonempty :=
  ⟨Real.logb 2 (exactMatrixRank 2), 2, le_rfl, rfl⟩

theorem exactMatrixRank_logb_lower {n : ℕ} (hn : 2 ≤ n) :
    2 ≤ Real.logb n (exactMatrixRank n) := by
  have hn1 : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hr : 0 < (exactMatrixRank n : ℝ) := by
    exact_mod_cast exactMatrixRank_pos (show 0 < n by omega)
  apply (Real.le_logb_iff_rpow_le hn1 hr).mpr
  rw [Real.rpow_two]
  exact_mod_cast exactMatrixRank_lower (show 0 < n by omega)

theorem exactMatrixRank_logb_upper {n : ℕ} (hn : 2 ≤ n) :
    Real.logb n (exactMatrixRank n) ≤ 3 := by
  have hn1 : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hr : 0 < (exactMatrixRank n : ℝ) := by
    exact_mod_cast exactMatrixRank_pos (show 0 < n by omega)
  apply (Real.logb_le_iff_le_rpow hn1 hr).mpr
  rw [show (3 : ℝ) = (3 : ℕ) by norm_num, Real.rpow_natCast]
  exact_mod_cast exactMatrixRank_upper n

theorem exactRankExponentSet_bddBelow : BddBelow exactRankExponentSet := by
  refine ⟨2, ?_⟩
  rintro τ ⟨n, hn, rfl⟩
  exact exactMatrixRank_logb_lower hn

theorem exactRankExponent_lower : 2 ≤ exactRankExponent :=
  le_csInf exactRankExponentSet_nonempty (by
    rintro τ ⟨n, hn, rfl⟩
    exact exactMatrixRank_logb_lower hn)

theorem exactRankExponent_le_logb {n : ℕ} (hn : 2 ≤ n) :
    exactRankExponent ≤ Real.logb n (exactMatrixRank n) :=
  csInf_le exactRankExponentSet_bddBelow ⟨n, hn, rfl⟩

theorem exactRankExponent_upper : exactRankExponent ≤ 3 :=
  (exactRankExponent_le_logb (n := 2) le_rfl).trans
    (exactMatrixRank_logb_upper (n := 2) le_rfl)

/-- Each matrix multiplication tensor has rank at least `n^ν`. -/
theorem exactMatrixRank_rpow_lower {n : ℕ} (hn : 2 ≤ n) :
    (n : ℝ) ^ exactRankExponent ≤ exactMatrixRank n := by
  have hn1 : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hr : 0 < (exactMatrixRank n : ℝ) := by
    exact_mod_cast exactMatrixRank_pos (show 0 < n by omega)
  exact (Real.le_logb_iff_rpow_le hn1 hr).mp (exactRankExponent_le_logb hn)

/-- The rank lower bound includes the one-dimensional boundary case. -/
theorem exactMatrixRank_rpow_lower_of_pos {n : ℕ} (hn : 0 < n) :
    (n : ℝ) ^ exactRankExponent ≤ exactMatrixRank n := by
  by_cases hn2 : 2 ≤ n
  · exact exactMatrixRank_rpow_lower hn2
  · have hn1 : n = 1 := by omega
    simp [hn1]

/-- A strict upper bound for the infimum is witnessed by an actual finite block. -/
theorem exists_exactMatrixRank_lt_rpow {τ : ℝ} (hτ : exactRankExponent < τ) :
    ∃ n : ℕ, 2 ≤ n ∧ (exactMatrixRank n : ℝ) < (n : ℝ) ^ τ := by
  obtain ⟨σ, ⟨n, hn, rfl⟩, hσ⟩ :=
    exists_lt_of_csInf_lt exactRankExponentSet_nonempty hτ
  refine ⟨n, hn, ?_⟩
  have hn1 : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hr : 0 < (exactMatrixRank n : ℝ) := by
    exact_mod_cast exactMatrixRank_pos (show 0 < n by omega)
  exact (Real.logb_lt_iff_lt_rpow hn1 hr).mp hσ

/-- Finite decompositions approximate the exact-rank exponent with any positive slack. -/
theorem exists_rankAtMost_of_exponent_slack {ε : ℝ} (hε : 0 < ε) :
    ∃ n R : ℕ, 2 ≤ n ∧ Tensor.RankAtMost (Matmul.IntegerBilinear.matrixTensor n n n) R ∧
      (R : ℝ) ≤ (n : ℝ) ^ (exactRankExponent + ε) := by
  obtain ⟨n, hn, hR⟩ := exists_exactMatrixRank_lt_rpow (lt_add_of_pos_right _ hε)
  exact ⟨n, exactMatrixRank n, hn, exactMatrixRank_spec n, hR.le⟩

end MatrixMultiplication.AuxiliarySeparation

end

end OAI
