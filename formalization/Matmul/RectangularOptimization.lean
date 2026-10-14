import Mathlib.Data.Real.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
The exact real optimization of the shared-leg parabolic parameter region.

This is the analytic optimization step only: it does not assert that a tensor
construction or a matrix-multiplication algorithm realizes the region.
-/

namespace Matmul.RectangularOptimization

/-- The feasible parameter region for the parabolic shared-leg bound. -/
def Feasible (a b : ℝ) : Prop :=
  0 ≤ a ∧ a ≤ 1 ∧ 0 ≤ b ∧ b ≤ 4 * a * (1 - a)

/-- The exact maximum of `2 * a + k * b` over `Feasible a b`, for `k ≥ 0`. -/
noncomputable def rectangularBound (k : ℝ) : ℝ :=
  if k ≤ 1 / 2 then 2 else 1 + k + 1 / (4 * k)

/-- Completing the square in the branch `k > 0`. -/
theorem completion_square {k : ℝ} (hk : 0 < k) (a : ℝ) :
    1 + k + 1 / (4 * k) - (2 * a + k * (4 * a * (1 - a))) =
      4 * k * (a - (1 / 2 + 1 / (4 * k))) ^ 2 := by
  have hk0 : k ≠ 0 := ne_of_gt hk
  field_simp
  ring

/-- Every feasible point is bounded by the exact piecewise optimum. -/
theorem objective_le {a b k : ℝ} (_ha0 : 0 ≤ a) (_ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb : b ≤ 4 * a * (1 - a)) (hk0 : 0 ≤ k) :
    2 * a + k * b ≤ rectangularBound k := by
  unfold rectangularBound
  split_ifs with hk
  · have hab : b ≤ 4 * (1 - a) := by
      nlinarith [sq_nonneg (1 - a)]
    have hkb : k * b ≤ (1 / 2) * b :=
      mul_le_mul_of_nonneg_right hk hb0
    nlinarith
  · have hkpos : 0 < k := by linarith
    have hnonneg : 0 ≤ 4 * k * (a - (1 / 2 + 1 / (4 * k))) ^ 2 := by
      positivity
    have hupper := mul_le_mul_of_nonneg_left hb hk0
    have hidentity := completion_square hkpos a
    linarith

theorem objective_le_of_feasible {a b k : ℝ} (hab : Feasible a b) (hk : 0 ≤ k) :
    2 * a + k * b ≤ rectangularBound k :=
  objective_le hab.1 hab.2.1 hab.2.2.1 hab.2.2.2 hk

/-- The explicit maximizing first parameter in the curved branch. -/
noncomputable def optimizerA (k : ℝ) : ℝ := 1 / 2 + 1 / (4 * k)

/-- The explicit maximizing second parameter in the curved branch. -/
noncomputable def optimizerB (k : ℝ) : ℝ := 1 - 1 / (4 * k ^ 2)

theorem optimizer_boundary {k : ℝ} (hk : 0 < k) :
    optimizerB k = 4 * optimizerA k * (1 - optimizerA k) := by
  unfold optimizerA optimizerB
  have hk0 : k ≠ 0 := ne_of_gt hk
  field_simp
  ring

/-- The displayed optimizer is feasible for every `k ≥ 1/2`, including the join. -/
theorem optimizer_feasible {k : ℝ} (hk : 1 / 2 ≤ k) :
    Feasible (optimizerA k) (optimizerB k) := by
  have hkpos : 0 < k := by linarith
  have hden : 0 < 4 * k := by positivity
  have ha0 : 0 ≤ optimizerA k := by
    unfold optimizerA
    positivity
  have ha1 : optimizerA k ≤ 1 := by
    unfold optimizerA
    have hinv : 1 / (4 * k) ≤ (1 : ℝ) / 2 :=
      (div_le_iff₀ hden).2 (by linarith)
    linarith
  have hksq : 1 ≤ 4 * k ^ 2 := by
    nlinarith [sq_nonneg (k - 1 / 2)]
  have hden2 : 0 < 4 * k ^ 2 := by positivity
  have hb0 : 0 ≤ optimizerB k := by
    unfold optimizerB
    have hinv : 1 / (4 * k ^ 2) ≤ (1 : ℝ) :=
      (div_le_iff₀ hden2).2 (by simpa using hksq)
    linarith
  exact ⟨ha0, ha1, hb0, le_of_eq (optimizer_boundary hkpos)⟩

/-- The curved-branch parameters achieve `1 + k + 1/(4k)`. -/
theorem optimizer_value {k : ℝ} (hk : 0 < k) :
    2 * optimizerA k + k * optimizerB k = 1 + k + 1 / (4 * k) := by
  have hidentity := completion_square hk (optimizerA k)
  rw [← optimizer_boundary hk] at hidentity
  simp only [optimizerA, sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero] at hidentity
  unfold optimizerA
  linarith

/-- For every nonnegative aspect ratio the bound is attained in the feasible region. -/
theorem bound_attained {k : ℝ} (_hk : 0 ≤ k) :
    ∃ a b : ℝ, Feasible a b ∧ 2 * a + k * b = rectangularBound k := by
  by_cases hsmall : k ≤ 1 / 2
  · refine ⟨1, 0, ?_, ?_⟩
    · norm_num [Feasible]
    · unfold rectangularBound
      rw [if_pos hsmall]
      ring
  · have hkhalf : 1 / 2 ≤ k := le_of_lt (lt_of_not_ge hsmall)
    have hkpos : 0 < k := by linarith
    refine ⟨optimizerA k, optimizerB k, optimizer_feasible hkhalf, ?_⟩
    unfold rectangularBound
    rw [if_neg hsmall]
    exact optimizer_value hkpos

/-- A maximum, and therefore the supremum, is exactly the piecewise bound. -/
theorem bound_isGreatest {k : ℝ} (hk : 0 ≤ k) :
    IsGreatest {v : ℝ | ∃ a b : ℝ, Feasible a b ∧ v = 2 * a + k * b}
      (rectangularBound k) := by
  constructor
  · obtain ⟨a, b, hab, hvalue⟩ := bound_attained hk
    exact ⟨a, b, hab, hvalue.symm⟩
  · intro v hv
    obtain ⟨a, b, hab, rfl⟩ := hv
    exact objective_le_of_feasible hab hk

/-- The same exact value expressed as the least upper bound. -/
theorem bound_isLUB {k : ℝ} (hk : 0 ≤ k) :
    IsLUB {v : ℝ | ∃ a b : ℝ, Feasible a b ∧ v = 2 * a + k * b}
      (rectangularBound k) :=
  (bound_isGreatest hk).isLUB

@[simp] theorem rectangularBound_zero : rectangularBound 0 = 2 := by
  norm_num [rectangularBound]

@[simp] theorem rectangularBound_half : rectangularBound (1 / 2) = 2 := by
  norm_num [rectangularBound]

@[simp] theorem rectangularBound_one : rectangularBound 1 = (9 : ℝ) / 4 := by
  norm_num [rectangularBound]

#print axioms objective_le
#print axioms optimizer_feasible
#print axioms bound_attained
#print axioms bound_isGreatest
#print axioms bound_isLUB

end Matmul.RectangularOptimization
