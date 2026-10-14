import Matmul.DiscreteSmallParameter
import Matmul.RectangularOptimization

/-!
The complete real-variable implication from the exact discrete oriented
profiles to the rectangular parameter cap. No homogenization or compactness
principle is needed by this proof.
-/

namespace Matmul.DiscreteProfiles

/-- The exact powered parameter cap derived from the discrete profile data. -/
theorem theta_cap {P Q : ℕ → ℕ → ℝ} {p θ : ℝ}
    (H : DiscreteData P Q p θ) : θ ≤ 4*(p-1)/p :=
  Matmul.DiscreteProfileCap.theta_cap_of_rational_ratio H.p_ge_one
    (Matmul.DiscreteSmallParameter.theta_le_two H) (rational_ratio H)

/-- The parabolic cap in the original shared-leg parameters. -/
theorem parameter_cap {P Q : ℕ → ℕ → ℝ} {a b : ℝ}
    (ha : 0 < a) (H : DiscreteData P Q (1/a) (b/a)) : b ≤ 4*a*(1-a) := by
  have hc := theta_cap H
  have heq : 4*(1/a-1)/(1/a) = 4*(1-a) := by field_simp
  rw [heq] at hc
  have hmul := (div_le_iff₀ ha).1 hc
  nlinarith

/-- Every nonnegative aspect ratio satisfies the exact rectangular curve,
once the oriented discrete tensor profiles have been established. -/
theorem rectangular_objective_le {P Q : ℕ → ℕ → ℝ} {a b k : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) (hk : 0 ≤ k)
    (H : DiscreteData P Q (1/a) (b/a)) :
    2*a+k*b ≤ Matmul.RectangularOptimization.rectangularBound k := by
  have ha1 : a ≤ 1 := by
    have h := (le_div_iff₀ ha).1 H.p_ge_one
    nlinarith
  exact Matmul.RectangularOptimization.objective_le ha.le ha1 hb (parameter_cap ha H) hk

#print axioms theta_cap
#print axioms parameter_cap
#print axioms rectangular_objective_le

end Matmul.DiscreteProfiles
