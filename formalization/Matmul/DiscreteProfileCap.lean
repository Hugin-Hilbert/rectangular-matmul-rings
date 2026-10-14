import Matmul.DiscretePotential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Order.Archimedean

/-!
The discrete potential argument for the rectangular parameter cap.

The sequence interface records multiplicative steps of actual diagonal and
oriented profile values. It assumes neither the final growth coefficient nor
the parabolic parameter bound.
-/

namespace Matmul.DiscreteProfileCap

open Matmul.DiscretePotential

noncomputable def slopeFraction (τ x : ℝ) : ℝ :=
  τ * x / ((τ + 2) * x - 1)

theorem slopeFraction_bounds {τ x : ℝ} (hτ : 0 < τ) (hx : 1 / 2 ≤ x) :
    0 < (τ + 2) * x - 1 ∧ 0 ≤ slopeFraction τ x ∧ slopeFraction τ x ≤ 1 := by
  have hxpos : 0 < x := by linarith
  have hden : 0 < (τ + 2) * x - 1 := by
    nlinarith [mul_pos hτ hxpos]
  refine ⟨hden, ?_, ?_⟩
  · unfold slopeFraction
    positivity
  · unfold slopeFraction
    apply (div_le_iff₀ hden).2
    nlinarith

/-- The exact tangent identity for the rational function in the potential. -/
theorem slopeFraction_tangent_identity {τ x y : ℝ}
    (hx : (τ + 2) * x - 1 ≠ 0) (hy : (τ + 2) * y - 1 ≠ 0) :
    slopeFraction τ x - slopeFraction τ y +
        τ / ((τ + 2) * y - 1) ^ 2 * (x - y) =
      τ * (τ + 2) * (x - y) ^ 2 /
        (((τ + 2) * x - 1) * ((τ + 2) * y - 1) ^ 2) := by
  unfold slopeFraction
  generalize hdx : (τ + 2) * x - 1 = dx at *
  generalize hdy : (τ + 2) * y - 1 = dy at *
  field_simp [hx, hy]
  rw [← hdx, ← hdy]
  ring

theorem slopeFraction_tangent {τ x y : ℝ} (hτ : 0 < τ)
    (hx : (τ + 2) * x - 1 > 0) (hy : (τ + 2) * y - 1 > 0) :
    slopeFraction τ y - τ / ((τ + 2) * y - 1) ^ 2 * (x - y) ≤
      slopeFraction τ x := by
  have hi := slopeFraction_tangent_identity (ne_of_gt hx) (ne_of_gt hy)
  have hn : 0 ≤ τ * (τ + 2) * (x - y) ^ 2 /
      (((τ + 2) * x - 1) * ((τ + 2) * y - 1) ^ 2) := by positivity
  linarith

theorem log_one_add_bounded {x M t : ℝ} (hx : 0 ≤ x) (hxM : x ≤ M)
    (ht : 0 < t) :
    x / t - M ^ 2 / (2 * t ^ 2) ≤ Real.log (1 + x / t) := by
  have hM : 0 ≤ M := le_trans hx hxM
  have hl := log_one_add_lower (div_nonneg hx ht.le)
  have hs := (sq_le_sq₀ hx hM).2 hxM
  have hsdiv := div_le_div_of_nonneg_right hs (sq_nonneg t)
  simp only [div_pow] at hl
  have heq : M ^ 2 / (2 * t ^ 2) = (M ^ 2 / t ^ 2) / 2 := by ring
  rw [heq]
  linarith

/-- A shifted denominator costs only another explicit quadratic error. -/
theorem log_one_add_shifted {γ z t : ℝ} (hγ0 : 0 ≤ γ) (_hγ1 : γ ≤ 1)
    (hz : 0 ≤ z) (ht : 0 < t) :
    γ / t - (γ * z + γ ^ 2 / 2) / t ^ 2 ≤ Real.log (1 + γ / (t + z)) := by
  have htz : 0 < t + z := by linarith
  have hdiv : γ / t - γ * z / t ^ 2 ≤ γ / (t + z) := by
    apply (le_div_iff₀ htz).2
    field_simp
    nlinarith [mul_nonneg hγ0 (sq_nonneg z)]
  have hle : γ / (t + z) ≤ γ / t :=
    div_le_div_of_nonneg_left hγ0 ht (by linarith)
  have hl := log_one_add_lower (div_nonneg hγ0 htz.le)
  have hs := (sq_le_sq₀ (div_nonneg hγ0 htz.le) (div_nonneg hγ0 ht.le)).2 hle
  simp only [div_pow] at hs hl
  have heq : (γ * z + γ ^ 2 / 2) / t ^ 2 =
      γ * z / t ^ 2 + (γ ^ 2 / t ^ 2) / 2 := by ring
  rw [heq]
  linarith

theorem log_increment_product {X Y u v θ : ℝ} (hX : 0 < X)
    (hu : 0 < u) (hv : 0 < v) (hstep : X * u * v ^ θ ≤ Y) :
    Real.log u + θ * Real.log v ≤ Real.log Y - Real.log X := by
  have hp := Real.rpow_pos_of_pos hv θ
  have hl := Real.log_le_log (mul_pos (mul_pos hX hu) hp) hstep
  rw [Real.log_mul (ne_of_gt (mul_pos hX hu)) (ne_of_gt hp),
    Real.log_mul (ne_of_gt hX) (ne_of_gt hu), Real.log_rpow hv] at hl
  linarith

/-- Explicit multiplicative sequence steps force the exact rectangular ratio
inequality. The upper assumptions are logarithms of the profile rank bounds. -/
theorem sequence_ratio {p θ τ z : ℝ} (hp : 1 ≤ p) (hθ : 0 ≤ θ)
    (hτ : 0 < τ) (hz : 0 ≤ z)
    (D Q lam : ℕ → ℝ) (CD CQ : ℝ)
    (hDpos : ∀ t : ℕ, 2 ≤ t → 0 < D t)
    (hQpos : ∀ t : ℕ, 2 ≤ t → 0 < Q t)
    (hlam : ∀ t : ℕ, 2 ≤ t → 1 / 2 ≤ lam t ∧ lam t ≤ 2)
    (hDstep : ∀ t : ℕ, 2 ≤ t →
      D t * (1 + 2 * lam t / (t : ℝ)) ≤ D (t + 1))
    (hQstep : ∀ t : ℕ, 2 ≤ t →
      Q t * (1 + slopeFraction τ (lam t) / (t : ℝ)) *
        (1 + (2 / (2 + τ)) / ((t : ℝ) + z)) ^ θ ≤ Q (t + 1))
    (hDupper : ∀ t : ℕ, 2 ≤ t → Real.log (D t) ≤ p * Real.log t + CD)
    (hQupper : ∀ t : ℕ, 2 ≤ t → Real.log (Q t) ≤ p * Real.log t + CQ) :
    2 * θ / (2 + τ) + τ / (τ + 2 - 2 / p) ≤ p := by
  let γ : ℝ := 2 / (2 + τ)
  let d : ℝ := (τ + 2) * (p / 2) - 1
  let c : ℝ := τ / d ^ 2
  let E : ℝ := 1 / 2 + θ * (γ * z + γ ^ 2 / 2)
  let F : ℝ := slopeFraction τ (p / 2)
  have hp0 : 0 < p := by linarith
  have hd : 0 < d := by
    dsimp [d]
    nlinarith [mul_pos hτ hp0]
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hγ0 : 0 ≤ γ := by dsimp [γ]; positivity
  have hγ1 : γ ≤ 1 := by
    dsimp [γ]
    apply (div_le_iff₀ (by linarith : 0 < 2 + τ)).2
    linarith
  have hsteps (t : ℕ) (ht : 2 ≤ t) :
      (θ * γ + F + c * p / 2) / (t : ℝ) - (E + 4 * c) / (t : ℝ) ^ 2 ≤
        (Real.log (Q (t + 1)) + c / 2 * Real.log (D (t + 1))) -
          (Real.log (Q t) + c / 2 * Real.log (D t)) := by
    have ht0 : 0 < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
    have hlt := hlam t ht
    have hf := slopeFraction_bounds hτ hlt.1
    have hlam0 : 0 ≤ lam t := by linarith
    have hLD := log_increment_product (hDpos t ht)
      (by positivity : 0 < 1 + 2 * lam t / (t : ℝ))
      (by norm_num : (0 : ℝ) < 1)
      (by simpa using hDstep t ht :
        D t * (1 + 2 * lam t / (t : ℝ)) * (1 : ℝ) ^ (0 : ℝ) ≤ D (t + 1))
    simp only [Real.log_one, mul_zero, add_zero] at hLD
    have hBD := log_one_add_bounded (by positivity : 0 ≤ 2 * lam t)
      (by linarith : 2 * lam t ≤ 4) ht0
    have hBDnorm : (4 : ℝ) ^ 2 / (2 * (t : ℝ) ^ 2) = 8 / (t : ℝ) ^ 2 := by ring
    rw [hBDnorm] at hBD
    have hLQ := log_increment_product (hQpos t ht)
      (by have hh := div_nonneg hf.2.1 ht0.le; linarith :
        0 < 1 + slopeFraction τ (lam t) / (t : ℝ))
      (by positivity : 0 < 1 + (2 / (2 + τ)) / ((t : ℝ) + z))
      (hQstep t ht)
    change Real.log (1 + slopeFraction τ (lam t) / (t : ℝ)) +
      θ * Real.log (1 + γ / ((t : ℝ) + z)) ≤
        Real.log (Q (t + 1)) - Real.log (Q t) at hLQ
    have hBF := log_one_add_bounded hf.2.1 hf.2.2 ht0
    have hBFnorm : (1 : ℝ) ^ 2 / (2 * (t : ℝ) ^ 2) = (1 / 2) / (t : ℝ) ^ 2 := by ring
    rw [hBFnorm] at hBF
    have hBG := log_one_add_shifted hγ0 hγ1 hz ht0
    have hBGmul := mul_le_mul_of_nonneg_left hBG hθ
    have hT := slopeFraction_tangent hτ hf.1 hd
    change F - c * (lam t - p / 2) ≤ slopeFraction τ (lam t) at hT
    have hTdiv := div_le_div_of_nonneg_right hT ht0.le
    have hDmul := mul_le_mul_of_nonneg_left (le_trans hBD hLD) (by positivity : 0 ≤ c / 2)
    dsimp [E]
    simp only [div_eq_mul_inv] at *
    nlinarith only [hBF, hBGmul, hLQ, hTdiv, hDmul]
  have hupper (t : ℕ) (ht : 2 ≤ t) :
      Real.log (Q t) + c / 2 * Real.log (D t) ≤
        p * (1 + c / 2) * Real.log t + (CQ + c / 2 * CD) := by
    have hdU := mul_le_mul_of_nonneg_left (hDupper t ht) (by positivity : 0 ≤ c / 2)
    have hqU := hQupper t ht
    nlinarith
  have hg := growth_coefficient_le
    (fun t => Real.log (Q t) + c / 2 * Real.log (D t))
    (θ * γ + F + c * p / 2) (E + 4 * c)
    (p * (1 + c / 2)) (CQ + c / 2 * CD) hsteps hupper
  have hF : F = τ / (τ + 2 - 2 / p) := by
    dsimp [F, slopeFraction]
    have hden : τ + 2 - 2 / p ≠ 0 := by
      apply ne_of_gt
      have hpinv : 2 / p ≤ (2 : ℝ) := (div_le_iff₀ hp0).2 (by linarith)
      linarith
    field_simp
  rw [hF] at hg
  dsimp [γ] at hg
  simp only [div_eq_mul_inv] at hg ⊢
  nlinarith

/-- Positive rational aspect ratios suffice, by continuity at every positive
real ratio. This density step needs no profile compactness. -/
theorem real_ratio_of_rational_ratio {p θ : ℝ} (hp : 1 ≤ p)
    (hratio : ∀ q : ℚ, 0 < (q : ℝ) →
      2 * θ / (2 + (q : ℝ)) + (q : ℝ) / ((q : ℝ) + 2 - 2 / p) ≤ p)
    (τ : ℝ) (hτ : 0 < τ) :
    2 * θ / (2 + τ) + τ / (τ + 2 - 2 / p) ≤ p := by
  have hp0 : 0 < p := by linarith
  have hpinv : 2 / p ≤ (2 : ℝ) := (div_le_iff₀ hp0).2 (by linarith)
  have hd1 : 2 + τ ≠ 0 := by linarith
  have hd2 : τ + 2 - 2 / p ≠ 0 := by linarith
  have hc : ContinuousAt
      (fun x : ℝ => 2 * θ / (2 + x) + x / (x + 2 - 2 / p)) τ := by
    fun_prop (disch := assumption)
  by_contra hnot
  have hb : p < 2 * θ / (2 + τ) + τ / (τ + 2 - 2 / p) := lt_of_not_ge hnot
  have hnb : ∀ᶠ x in nhds τ,
      0 < x ∧ p < 2 * θ / (2 + x) + x / (x + 2 - 2 / p) :=
    (eventually_gt_nhds hτ).and (hc.eventually (eventually_gt_nhds hb))
  obtain ⟨q, hq⟩ := (Rat.denseRange_cast : DenseRange ((↑) : ℚ → ℝ)).mem_nhds hnb
  exact (not_lt_of_ge (hratio q hq.1)) hq.2

/-- Optimizing the proved family of discrete ratio inequalities gives the
precise exponent cap. `θ ≤ 2` is the separate-concavity growth bound. -/
theorem theta_cap_of_rational_ratio {p θ : ℝ} (hp : 1 ≤ p) (hθ2 : θ ≤ 2)
    (hratio : ∀ q : ℚ, 0 < (q : ℝ) →
      2 * θ / (2 + (q : ℝ)) + (q : ℝ) / ((q : ℝ) + 2 - 2 / p) ≤ p) :
    θ ≤ 4 * (p - 1) / p := by
  have hp0 : 0 < p := by linarith
  by_cases hp2 : 2 ≤ p
  · apply le_trans hθ2
    apply (le_div_iff₀ hp0).2
    linarith
  · have hp2' : p < 2 := lt_of_not_ge hp2
    let τ : ℝ := 4 / p - 2
    have hτ : 0 < τ := by
      dsimp [τ]
      have hh : (2 : ℝ) < 4 / p := (lt_div_iff₀ hp0).2 (by linarith)
      linarith
    have hr := real_ratio_of_rational_ratio hp hratio τ hτ
    have hi1 : 2 * θ / (2 + τ) = θ * p / 2 := by
      dsimp [τ]
      field_simp
      ring
    have hi2 : τ / (τ + 2 - 2 / p) = 2 - p := by
      dsimp [τ]
      field_simp
      ring
    rw [hi1, hi2] at hr
    apply (le_div_iff₀ hp0).2
    nlinarith

/-- The scalar exponent cap in the original shared-leg parameters. -/
theorem parameter_cap_of_rational_ratio {a b : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1)
    (hb2 : b ≤ 2 * a)
    (hratio : ∀ q : ℚ, 0 < (q : ℝ) →
      2 * (b / a) / (2 + (q : ℝ)) +
        (q : ℝ) / ((q : ℝ) + 2 - 2 / (1 / a)) ≤ 1 / a) :
    b ≤ 4 * a * (1 - a) := by
  have hp : (1 : ℝ) ≤ 1 / a := (le_div_iff₀ ha0).2 (by simpa using ha1)
  have hθ2 : b / a ≤ (2 : ℝ) := (div_le_iff₀ ha0).2 (by linarith)
  have hcap := theta_cap_of_rational_ratio hp hθ2 hratio
  have hi : 4 * (1 / a - 1) / (1 / a) = 4 * (1 - a) := by
    field_simp
  rw [hi] at hcap
  have hh := (div_le_iff₀ ha0).1 hcap
  nlinarith

#print axioms sequence_ratio
#print axioms theta_cap_of_rational_ratio
#print axioms parameter_cap_of_rational_ratio

end Matmul.DiscreteProfileCap
