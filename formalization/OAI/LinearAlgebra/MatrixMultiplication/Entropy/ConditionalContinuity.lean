/-
Adapted from openai/math, commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Licensed under Apache-2.0. Modified for Lean 4.33.0-rc1 compatibility;
see formalization/PROVENANCE.txt and the repository NOTICE.
-/

/-
Pure analytic excerpt from upstream-allfields ConditionalContinuity.lean.
Only the rational law approximation theorem is retained; its proof is unchanged.
-/
import OAI.LinearAlgebra.MatrixMultiplication.Separation.ComplexRationalTypes
import OAI.LinearAlgebra.MatrixMultiplication.Entropy.ComplexEntropyContinuity
import Mathlib.Analysis.SpecificLimits.Normed

namespace OAI
noncomputable section
namespace MatrixMultiplication.ConditionalLabels
open MatrixMultiplication.Foundation Filter
open scoped BigOperators Topology Classical
variable {A : Type*} [Fintype A]

theorem exists_rational_law_sequence (p : FiniteLaw A) :
    ∃ q : ℕ → RationalLaw A,
      ∀ a, Tendsto (fun n => (q n).toFiniteLaw.mass a) atTop (𝓝 (p.mass a)) := by
  have hexists (n : ℕ) := p.exists_rational_approximation
    (1 / ((n : ℝ) + 1)) (by positivity)
  choose q _support close using hexists
  refine ⟨q, fun a => ?_⟩
  have hdifference : Tendsto
      (fun n => (q n).toFiniteLaw.mass a - p.mass a) atTop (𝓝 0) := by
    apply squeeze_zero_norm _ tendsto_one_div_add_atTop_nhds_zero_nat
    intro n
    simpa only [Real.norm_eq_abs, RationalLaw.toFiniteLaw_mass] using (close n a).le
  simpa only [sub_add_cancel, zero_add] using hdifference.add_const (p.mass a)

end MatrixMultiplication.ConditionalLabels
end
end OAI
