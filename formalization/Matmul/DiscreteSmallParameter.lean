import Matmul.DiscreteProfiles
import Matmul.DiscreteSlopes
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace Matmul.DiscreteSmallParameter

open Filter
open scoped Topology
open Matmul.DiscreteProfiles

/-- A positive discrete concave sequence has a uniform linear upper bound. -/
theorem positive_concave_le_linear {f : ℕ → ℝ}
    (hpos : ∀ k : ℕ, 1 ≤ k → 0 < f k)
    (hconc : Antitone (fun k : ℕ => f (k + 2) - f (k + 1)))
    (n : ℕ) (hn : 2 ≤ n) : f n ≤ (n : ℝ) * f 2 := by
  have hd : Antitone (fun k : ℕ => f ((k + 1) + 1) - f (k + 1)) := by
    simpa only [Nat.add_assoc] using hconc
  have ha := Matmul.DiscreteSlopes.concave_sequence_le_affine
    (u := fun k => f (k + 1)) hd 0 (n - 1)
  have hindex : n - 1 + 1 = n := by omega
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  simp only [Nat.zero_add] at ha
  rw [hindex, hcast] at ha
  have hf1 := hpos 1 (by omega)
  have hf2 := hpos 2 (by omega)
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith [mul_nonneg (show 0 ≤ (n : ℝ) - 2 by linarith) hf1.le]

/-- Separate discrete concavity gives a quadratic diagonal upper bound. -/
theorem diagonal_P_le_quadratic {P Q : ℕ → ℕ → ℝ} {p θ : ℝ}
    (H : DiscreteData P Q p θ) (n : ℕ) (hn : 2 ≤ n) :
    P n n ≤ P 2 2 * (n : ℝ) ^ 2 := by
  have hn1 : 1 ≤ n := by omega
  have hfirst := positive_concave_le_linear
    (fun k hk => H.P_pos k n hk hn1) (H.P_concave_first n hn1) n hn
  have hsecond := positive_concave_le_linear
    (fun k hk => H.P_pos 2 k (by omega) hk)
    (H.P_concave_second 2 (by omega)) n hn
  have hscaled := mul_le_mul_of_nonneg_left hsecond (Nat.cast_nonneg n)
  nlinarith

/-- Coupled tripling and row concavity control the oriented diagonal by the symmetric one. -/
theorem diagonal_Q_le_four_P {P Q : ℕ → ℕ → ℝ} {p θ : ℝ}
    (H : DiscreteData P Q p θ) (n : ℕ) (hn : 2 ≤ n) :
    Q n n ≤ 4 * P n n := by
  have hn1 : 1 ≤ n := by omega
  let f : ℕ → ℝ := fun k => P n (k + 1)
  have hd : Antitone (fun k : ℕ => f (k + 1) - f k) := by
    simpa only [f, Nat.add_assoc] using H.P_concave_second n hn1
  have hsec := antitone_increment_secant hd (n - 1) (4 * n - 2) (by omega) (by omega)
  have hnindex : n - 1 + 1 = n := by omega
  have hfarindex : 4 * n - 2 + 1 = 4 * n - 1 := by omega
  have hncast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn1, Nat.cast_one]
  have hfarcast : ((4 * n - 2 : ℕ) : ℝ) = 4 * (n : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ 4 * n), Nat.cast_mul, Nat.cast_ofNat, Nat.cast_ofNat]
  dsimp [f] at hsec
  rw [hnindex, hfarindex, hncast, hfarcast] at hsec
  have htrip := H.P_tripling n n hn1 hn1
  have htripindex : 3 * n + n - 1 = 4 * n - 1 := by omega
  rw [htripindex] at htrip
  have hp1 := H.P_pos n 1 hn1 (by omega)
  have hpnn := H.P_pos n n hn1 hn1
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have htripscaled := mul_le_mul_of_nonneg_left htrip
    (show 0 ≤ (n : ℝ) - 1 by linarith)
  have hdrop : 0 ≤ (3 * (n : ℝ) - 1) * P n 1 :=
    mul_nonneg (by linarith) hp1.le
  have hcoeff : 2 * (n : ℝ) * P n n ≤ 4 * ((n : ℝ) - 1) * P n n := by
    nlinarith [mul_nonneg (show 0 ≤ (n : ℝ) - 2 by linarith) hpnn.le]
  nlinarith

/-- A natural real power bounded by a fixed quadratic has exponent at most two. -/
theorem exponent_le_two_of_nat_quadratic {θ C : ℝ}
    (hbound : ∀ n : ℕ, 2 ≤ n → (n : ℝ) ^ θ ≤ C * (n : ℝ) ^ 2) : θ ≤ 2 := by
  by_contra hnot
  have hdelta : 0 < θ - 2 := by linarith
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ (θ - 2)) atTop atTop :=
    (tendsto_rpow_atTop hdelta).comp tendsto_natCast_atTop_atTop
  obtain ⟨n, hn2, hnlarge⟩ :=
    ((eventually_ge_atTop 2).and (hlim.eventually_gt_atTop C)).exists
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hsmall : (n : ℝ) ^ (θ - 2) ≤ C := by
    rw [Real.rpow_sub hnpos, Real.rpow_two]
    apply (div_le_iff₀ (sq_pos_of_pos hnpos)).mpr
    exact hbound n hn2
  exact (not_lt_of_ge hsmall) hnlarge

/-- The actual discrete profile hypotheses force the small parameter into `[0,2]`. -/
theorem theta_le_two {P Q : ℕ → ℕ → ℝ} {p θ : ℝ}
    (H : DiscreteData P Q p θ) : θ ≤ 2 := by
  apply exponent_le_two_of_nat_quadratic (C := 4 * P 2 2)
  intro n hn
  have hn1 : 1 ≤ n := by omega
  have hboundary := H.Q_boundary n hn1
  have hmono := H.Q_mono_second n 1 n hn1 (by omega) hn1
  rw [hboundary] at hmono
  have hQP := diagonal_Q_le_four_P H n hn
  have hP := diagonal_P_le_quadratic H n hn
  nlinarith

#print axioms theta_le_two

end Matmul.DiscreteSmallParameter
