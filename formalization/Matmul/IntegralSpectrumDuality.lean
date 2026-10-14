import Matmul.IntegralCatalyst

/-!
# The integral spectral rank upper bound

Integer-threshold detecting characters are amplified by tensor powers to
recover a real asymptotic-rank upper bound. This proof uses the actual
infimum of normalized integral power ranks and the constructed spectrum.
-/

namespace Matmul.IntegralSpectrum

open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring

noncomputable section

/-- Tensor powers only increase the normalized infimum after restricting to
multiples of the power exponent. -/
theorem asymptoticRank_pow_lower {t : S} (ht : t ≠ 0) {n : ℕ} (hn : 0 < n) :
    asymptoticRank t ^ n ≤ asymptoticRank (t ^ n) := by
  simp only [asymptoticRank, if_neg ht,
    if_neg (UnitTensorClass.pow_ne_zero_of_unit ht n)]
  rw [← Real.exp_nat_mul]
  exact Real.exp_le_exp.mpr (UnitTensorClass.logRankGrowth_pow_lower ht hn)

/-- Bounding every monotone integral character bounds the actual asymptotic
integral rank. No spectral-duality hypothesis is assumed. -/
theorem asymptoticRank_le_of_character_bound {t : S} {B : ℝ} (hB : 1 ≤ B)
    (h : ∀ χ : Character, Monotone χ → χ t ≤ B) :
    asymptoticRank t ≤ B := by
  classical
  by_cases ht : t = 0
  · simp only [asymptoticRank, if_pos ht]
    exact zero_le_one.trans hB
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  by_contra! hA
  have hratio : 1 < asymptoticRank t / B := (one_lt_div hBpos).mpr hA
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 : ℝ) hratio
  have hnpos : 0 < n := by
    by_contra hz
    have hnzero : n = 0 := by omega
    simp only [hnzero, pow_zero] at hn
    norm_num at hn
  have hn' : 2 * B ^ n < asymptoticRank t ^ n := by
    apply (lt_div_iff₀ (pow_pos hBpos n)).mp
    simpa only [div_pow] using hn
  have hBpow : 1 ≤ B ^ n := one_le_pow₀ hB
  let k := ⌊B ^ n⌋₊ + 1
  have hkupper : (k : ℝ) ≤ B ^ n + 1 := by
    dsimp [k]
    push_cast
    simpa only [add_comm] using add_le_add_right (Nat.floor_le (by positivity : 0 ≤ B ^ n)) 1
  have hkbelow : (k : ℝ) < asymptoticRank (t ^ n) :=
    (hkupper.trans (by linarith : B ^ n + 1 ≤ 2 * B ^ n)).trans_lt
      (hn'.trans_le (asymptoticRank_pow_lower ht hnpos))
  obtain ⟨χ, hχ, hχbounds, hdetect⟩ :=
    exists_detecting_character (UnitTensorClass.pow_ne_zero_of_unit ht n) hkbelow
  have hp : χ (t ^ n) ≤ B ^ n := by
    rw [map_pow]
    exact pow_le_pow_left₀ (hχbounds t).1 (h χ hχ) n
  have hklarge : B ^ n < (k : ℝ) := by
    dsimp [k]
    push_cast
    exact Nat.lt_floor_add_one (B ^ n)
  exact (not_lt_of_ge (hdetect.trans hp)) hklarge

/-- Any strict upper bound on integral asymptotic rank gives a genuine finite
power rank bound; the witness is an exact integral decomposition size. -/
theorem exists_rank_power_lt {t : S} (ht : t ≠ 0) {r : ℝ}
    (hr : asymptoticRank t < r) :
    ∃ n : ℕ, 0 < n ∧ (UnitTensorClass.rank (t ^ n) : ℝ) < r ^ n := by
  have hAr : Real.exp (UnitTensorClass.logRankGrowth t) < r := by
    simpa only [asymptoticRank, if_neg ht] using hr
  have hrpos : 0 < r := (Real.exp_pos _).trans hAr
  have hg : UnitTensorClass.logRankGrowth t < Real.log r := by
    simpa only [Real.log_exp] using Real.log_lt_log (Real.exp_pos _) hAr
  obtain ⟨x, hx, hxr⟩ := exists_lt_of_csInf_lt
    (UnitTensorClass.logRankGrowth_set_nonempty t) hg
  obtain ⟨n, hn, rfl⟩ := hx
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : Real.log (UnitTensorClass.rank (t ^ n)) < (n : ℝ) * Real.log r := by
    have h' := (div_lt_iff₀ hnR).mp hxr
    simpa only [mul_comm] using h'
  have hrankpos : (0 : ℝ) < UnitTensorClass.rank (t ^ n) := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one (UnitTensorClass.rank_pow_one_le ht n))
  refine ⟨n, hn, ?_⟩
  calc
    (UnitTensorClass.rank (t ^ n) : ℝ) =
        Real.exp (Real.log (UnitTensorClass.rank (t ^ n))) := (Real.exp_log hrankpos).symm
    _ < Real.exp ((n : ℝ) * Real.log r) := Real.exp_lt_exp.mpr hlog
    _ = r ^ n := by rw [Real.exp_nat_mul, Real.exp_log hrpos]

/-- Every monotone normalized integral character is bounded by the actual
infimum of integral tensor-power ranks. -/
theorem character_le_asymptoticRank (χ : Character) (hχ : Monotone χ) (t : S) :
    χ t ≤ asymptoticRank t := by
  classical
  by_cases ht : t = 0
  · subst t
    simp [asymptoticRank]
  have hχpos : 0 < χ t := zero_lt_one.trans_le (one_le_character_of_ne_zero χ hχ ht)
  have hlog : Real.log (χ t) ≤ UnitTensorClass.logRankGrowth t := by
    apply le_csInf (UnitTensorClass.logRankGrowth_set_nonempty t)
    rintro x ⟨n, hn, rfl⟩
    have hr : χ t ^ n ≤ UnitTensorClass.rank (t ^ n) := by
      simpa only [map_pow] using character_le_rank χ hχ (t ^ n)
    have hp := Real.log_le_log (pow_pos hχpos n) hr
    rw [Real.log_pow] at hp
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    exact (le_div_iff₀ hnR).mpr (by simpa only [mul_comm] using hp)
  simp only [asymptoticRank, if_neg ht]
  exact (Real.exp_log hχpos).symm.le.trans (Real.exp_le_exp.mpr hlog)

/-- Integral asymptotic rank equals the supremum over the actual monotone
semiring characters. The two directions are proved from integer rank
certificates and the generic separation/fixed-point construction. -/
theorem asymptoticRank_eq_sSup_characterValues {t : S} (ht : t ≠ 0) :
    asymptoticRank t = sSup {x : ℝ | ∃ χ : Character, Monotone χ ∧ x = χ t} := by
  classical
  let V : Set ℝ := {x : ℝ | ∃ χ : Character, Monotone χ ∧ x = χ t}
  have hpos : 0 < asymptoticRank t := by
    simp only [asymptoticRank, if_neg ht]
    exact Real.exp_pos _
  obtain ⟨χ₀, hχ₀, _, _⟩ := exists_detecting_character ht (k := 0) (by simpa using hpos)
  have hVne : V.Nonempty := ⟨χ₀ t, χ₀, hχ₀, rfl⟩
  have hVbdd : BddAbove V := by
    refine ⟨asymptoticRank t, ?_⟩
    rintro x ⟨χ, hχ, rfl⟩
    exact character_le_asymptoticRank χ hχ t
  apply le_antisymm
  · apply asymptoticRank_le_of_character_bound
    · exact (one_le_character_of_ne_zero χ₀ hχ₀ ht).trans
        (le_csSup hVbdd (show χ₀ t ∈ V from ⟨χ₀, hχ₀, rfl⟩))
    · intro χ hχ
      exact le_csSup hVbdd (show χ t ∈ V from ⟨χ, hχ, rfl⟩)
  · apply csSup_le hVne
    rintro x ⟨χ, hχ, rfl⟩
    exact character_le_asymptoticRank χ hχ t

end
end Matmul.IntegralSpectrum
