import Matmul.IntegerScalar
import Mathlib

/-!
# Logarithmic asymptotic rank over the integers

The infimum of the normalized logarithmic ranks records the exponential rank
cost. Polynomial interpolation costs disappear from this infimum by taking
three successive limits.
-/

namespace OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring.UnitTensorClass

noncomputable section
open Filter Topology

/-- The exponential rank cost, expressed in logarithmic coordinates. -/
def logRankGrowth (T : UnitTensorClass ℤ) : ℝ :=
  sInf {x : ℝ | ∃ n : ℕ, 0 < n ∧ x = Real.log (rank (T ^ n)) / n}

theorem rank_pow_one_le {T : UnitTensorClass ℤ} (hT : T ≠ 0) (n : ℕ) :
    1 ≤ rank (T ^ n) := by
  have h : (1 : UnitTensorClass ℤ) ≤ T ^ n := by
    simpa using pow_le_pow_left' (one_le_of_ne_zero hT) n
  have hnat : rank (1 : UnitTensorClass ℤ) = 1 := by
    simpa only [Nat.cast_one] using rank_natCast 1
  simpa only [hnat] using rank_mono h

theorem logRankGrowth_set_nonempty (T : UnitTensorClass ℤ) :
    {x : ℝ | ∃ n : ℕ, 0 < n ∧ x = Real.log (rank (T ^ n)) / n}.Nonempty :=
  ⟨_, 1, Nat.zero_lt_one, rfl⟩

theorem logRankGrowth_set_bddBelow {T : UnitTensorClass ℤ} (hT : T ≠ 0) :
    BddBelow {x : ℝ | ∃ n : ℕ, 0 < n ∧ x = Real.log (rank (T ^ n)) / n} := by
  refine ⟨0, ?_⟩
  rintro x ⟨n, hn, rfl⟩
  exact div_nonneg (Real.log_nonneg (by exact_mod_cast rank_pow_one_le hT n))
    (Nat.cast_nonneg n)

theorem logRankGrowth_nonneg {T : UnitTensorClass ℤ} (hT : T ≠ 0) :
    0 ≤ logRankGrowth T := by
  apply le_csInf (logRankGrowth_set_nonempty T)
  rintro x ⟨n, hn, rfl⟩
  exact div_nonneg (Real.log_nonneg (by exact_mod_cast rank_pow_one_le hT n))
    (Nat.cast_nonneg n)

theorem logRankGrowth_le {T : UnitTensorClass ℤ} (hT : T ≠ 0)
    {n : ℕ} (hn : 0 < n) :
    logRankGrowth T ≤ Real.log (rank (T ^ n)) / n :=
  csInf_le (logRankGrowth_set_bddBelow hT) ⟨n, hn, rfl⟩


/-- Tensor powers of a nonzero unit-admitting integral tensor remain nonzero. -/
theorem pow_ne_zero_of_unit {T : UnitTensorClass ℤ} (hT : T ≠ 0) (n : ℕ) :
    T ^ n ≠ 0 :=
  (rank_pos_iff _).mp (Nat.lt_of_lt_of_le Nat.zero_lt_one (rank_pow_one_le hT n))

/-- Restricting the infimum to powers whose exponents are divisible by `n`
gives the power lower bound; no convergence theorem for subadditive sequences
is needed. -/
theorem logRankGrowth_pow_lower {T : UnitTensorClass ℤ} (hT : T ≠ 0)
    {n : ℕ} (hn : 0 < n) :
    (n : ℝ) * logRankGrowth T ≤ logRankGrowth (T ^ n) := by
  apply le_csInf (logRankGrowth_set_nonempty (T ^ n))
  rintro x ⟨m, hm, rfl⟩
  have hnR : (n : ℝ) ≠ 0 := by positivity
  have hmR : (m : ℝ) ≠ 0 := by positivity
  calc
    (n : ℝ) * logRankGrowth T ≤
        (n : ℝ) * (Real.log (rank (T ^ (n * m))) / (n * m : ℕ)) :=
      mul_le_mul_of_nonneg_left (logRankGrowth_le hT (Nat.mul_pos hn hm))
        (Nat.cast_nonneg n)
    _ = Real.log (rank ((T ^ n) ^ m)) / m := by
      rw [← pow_mul]
      push_cast
      field_simp [hnR, hmR]

/-- The elementary logarithmic overhead in the support parameter vanishes. -/
theorem tendsto_log_nat_add_one_div_nat :
    Tendsto (fun j : ℕ => Real.log ((j : ℝ) + 1) / j) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp
    (tendsto_atTop_add_const_right atTop (1 : ℝ)
      (tendsto_natCast_atTop_atTop : Tendsto (fun j : ℕ => (j : ℝ)) atTop atTop))
  simpa [Function.comp_def, add_assoc] using h

/-- Taking the amplification, block-size, and support limits removes all three
finite overheads. No regularity of the cost function `Q` is required. -/
theorem le_of_three_overheads {ν κ σ : ℝ} (Q : ℕ → ℕ → ℝ)
    (h : ∀ j L p : ℕ, 0 < j → 0 < L → 0 < p →
      ν ≤ Q j L / ((j : ℝ) * L * p) + Real.log ((j : ℝ) + 1) / j + σ / L + κ) :
    ν ≤ κ := by
  have hfirst (j L : ℕ) (hj : 0 < j) (hL : 0 < L) :
      ν ≤ Real.log ((j : ℝ) + 1) / j + σ / L + κ := by
    have hz : Tendsto (fun p : ℕ => Q j L / ((j : ℝ) * L * p)) atTop (𝓝 0) := by
      have hp := (tendsto_natCast_atTop_atTop :
        Tendsto (fun p : ℕ => (p : ℝ)) atTop atTop)
      have hden := hp.const_mul_atTop (by positivity : 0 < (j : ℝ) * L)
      exact tendsto_const_nhds.div_atTop hden
    have hlim := ((hz.add_const (Real.log ((j : ℝ) + 1) / j)).add_const (σ / L)).add_const κ
    apply ge_of_tendsto (by simpa using hlim)
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with p hp using h j L p hj hL hp
  have hsecond (j : ℕ) (hj : 0 < j) :
      ν ≤ Real.log ((j : ℝ) + 1) / j + κ := by
    have hz : Tendsto (fun L : ℕ => σ / (L : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have hlim := ((tendsto_const_nhds (x := Real.log ((j : ℝ) + 1) / j)).add hz).add_const κ
    apply ge_of_tendsto (by simpa using hlim)
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with L hL using hfirst j L hj hL
  apply ge_of_tendsto (by simpa using tendsto_log_nat_add_one_div_nat.add_const κ)
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with j hj using hsecond j hj

/-- A logarithmic rank estimate with finite interpolation costs suffices to
bound the asymptotic integral rank cost. -/
theorem logRankGrowth_le_of_log_bound {T : UnitTensorClass ℤ} (hT : T ≠ 0)
    {κ σ : ℝ} (Q : ℕ → ℕ → ℝ)
    (h : ∀ j L p : ℕ, 0 < j → 0 < L → 0 < p →
      Real.log (rank (T ^ (j * L * p))) / (j * L * p : ℕ) ≤
        Q j L / ((j : ℝ) * L * p) + Real.log ((j : ℝ) + 1) / j + σ / L + κ) :
    logRankGrowth T ≤ κ := by
  apply le_of_three_overheads Q
  intro j L p hj hL hp
  exact (logRankGrowth_le hT (Nat.mul_pos (Nat.mul_pos hj hL) hp)).trans
    (h j L p hj hL hp)

/-- An exact integral rank bound with an arbitrary fixed interpolation cost,
polynomial support overhead, and fixed auxiliary size has exponential cost at
most `k`. All parameters and rank certificates are integral. -/
theorem logRankGrowth_le_of_rank_bound {T : UnitTensorClass ℤ} (hT : T ≠ 0)
    {k S : ℕ} (hk : 1 ≤ k) (hS : 1 ≤ S) (Q : ℕ → ℕ → ℕ)
    (hQ : ∀ j L : ℕ, 1 ≤ Q j L)
    (h : ∀ j L p : ℕ, 0 < j → 0 < L → 0 < p →
      rank (T ^ (j * L * p)) ≤ Q j L * ((j + 1) ^ L * k ^ (j * L) * S ^ j) ^ p) :
    logRankGrowth T ≤ Real.log k := by
  apply logRankGrowth_le_of_log_bound hT (κ := Real.log k) (σ := Real.log S)
    (fun j L => Real.log (Q j L))
  intro j L p hj hL hp
  have hjR : (j : ℝ) ≠ 0 := by positivity
  have hLR : (L : ℝ) ≠ 0 := by positivity
  have hpR : (p : ℝ) ≠ 0 := by positivity
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have hSR : (S : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hS)
  have hQR : (Q j L : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hQ j L))
  have hjone : ((j : ℝ) + 1) ≠ 0 := by positivity
  have hrank : (0 : ℝ) < rank (T ^ (j * L * p)) := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one (rank_pow_one_le hT _))
  have hcast : (rank (T ^ (j * L * p)) : ℝ) ≤
      (Q j L * ((j + 1) ^ L * k ^ (j * L) * S ^ j) ^ p : ℕ) := by
    exact_mod_cast h j L p hj hL hp
  have hlog := Real.log_le_log hrank hcast
  have hlog' := div_le_div_of_nonneg_right hlog (Nat.cast_nonneg (j * L * p) :
    (0 : ℝ) ≤ (j * L * p : ℕ))
  calc
    Real.log (rank (T ^ (j * L * p))) / (j * L * p : ℕ) ≤
        Real.log (Q j L * ((j + 1) ^ L * k ^ (j * L) * S ^ j) ^ p : ℕ) /
          (j * L * p : ℕ) := hlog'
    _ = Real.log (Q j L) / ((j : ℝ) * L * p) +
        Real.log ((j : ℝ) + 1) / j + Real.log S / L + Real.log k := by
      push_cast
      rw [Real.log_mul hQR (pow_ne_zero p (mul_ne_zero
        (mul_ne_zero (pow_ne_zero L hjone) (pow_ne_zero (j * L) hkR))
        (pow_ne_zero j hSR))), Real.log_pow]
      rw [Real.log_mul (mul_ne_zero (pow_ne_zero L hjone) (pow_ne_zero (j * L) hkR))
        (pow_ne_zero j hSR), Real.log_mul (pow_ne_zero L hjone)
        (pow_ne_zero (j * L) hkR), Real.log_pow, Real.log_pow, Real.log_pow]
      push_cast
      field_simp [hjR, hLR, hpR]
      ring

end
end OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring.UnitTensorClass
