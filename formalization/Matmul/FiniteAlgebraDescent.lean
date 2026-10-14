import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensor
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Algebra.Algebra.Basic

/-!
# Descent through a fixed finite free integer algebra

If a commutative integer algebra `B` has a basis of size `d` and an integer
linear retraction `q` with `q 1 = 1`, exact rank over `B` descends to integer
rank with a factor `d²`. Only the first two factors of each simple tensor are
expanded in the basis. The third factor is paired with `q`.

In particular, take tensor powers over the *same fixed algebra* first, then
descend once. The factor is `d²`, rather than `(d²)^m`.
-/

namespace Matmul.FiniteAlgebraDescent

open scoped BigOperators
open Module OAI.MatrixMultiplication.Foundation

variable {B X Y Z : Type*} [CommRing B]

/-- A linear retraction that sends one to one fixes the image of every integer.
No choice of basis containing one is required. -/
theorem linear_retraction_algebraMap [Algebra ℤ B] (q : B →ₗ[ℤ] ℤ) (hq : q 1 = 1) (n : ℤ) :
    q (algebraMap ℤ B n) = n := by
  have heq : algebraMap ℤ B n = (n : B) := by simp
  rw [heq, ← zsmul_one, map_zsmul, hq]
  simp

/-- Expand only the first two factors of a triple product, keeping the third
factor inside the integer-valued linear functional. -/
theorem linearMap_triple_product {d : ℕ} (basis : Basis (Fin d) ℤ B)
    (q : B →ₗ[ℤ] ℤ) (u v w : B) :
    q (u * v * w) =
      ∑ a, ∑ b, basis.repr u a * basis.repr v b * q (basis a * basis b * w) := by
  conv_lhs => rw [← basis.sum_repr u, ← basis.sum_repr v]
  rw [Finset.sum_mul_sum]
  simp only [Finset.sum_mul, map_sum, smul_mul_assoc, mul_smul_comm,
    LinearMap.map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

/-- Applying an integer linear functional to a tensor over a finite free
integer algebra increases its rank by at most the square of the algebra rank.
The functional is not assumed to be multiplicative. -/
theorem rankAtMost_apply_linearMap {d r : ℕ} (basis : Basis (Fin d) ℤ B)
    (q : B →ₗ[ℤ] ℤ) {S : Tensor B X Y Z} (h : Tensor.RankAtMost S r) :
    Tensor.RankAtMost (fun x y z => q (S x y z)) (r * d * d) := by
  classical
  rcases h with ⟨u, v, w, h⟩
  let a : (Fin r × Fin d × Fin d) → X → ℤ := fun p x => basis.repr (u p.1 x) p.2.1
  let b : (Fin r × Fin d × Fin d) → Y → ℤ := fun p y => basis.repr (v p.1 y) p.2.2
  let c : (Fin r × Fin d × Fin d) → Z → ℤ :=
    fun p z => q (basis p.2.1 * basis p.2.2 * w p.1 z)
  have heq : (fun x y z => q (S x y z)) =
      fun x y z => ∑ p, Tensor.rankOne (a p) (b p) (c p) x y z := by
    funext x y z
    rw [h]
    simp only [map_sum, Tensor.rankOne, Fintype.sum_prod_type, a, b, c]
    apply Finset.sum_congr rfl
    intro i hi
    exact linearMap_triple_product basis q (u i x) (v i y) (w i z)
  rw [heq]
  simpa only [Fintype.card_prod, Fintype.card_fin, mul_assoc] using
    Tensor.rankAtMost_sum_rankOne a b c

/-- Descend an exact rank certificate for an integer tensor after scalar
extension to a fixed finite free integer algebra. -/
theorem integer_rank_descent [Algebra ℤ B] {d r : ℕ} (basis : Basis (Fin d) ℤ B)
    (q : B →ₗ[ℤ] ℤ) (hq : q 1 = 1) {T : Tensor ℤ X Y Z}
    (h : Tensor.RankAtMost (fun x y z => algebraMap ℤ B (T x y z)) r) :
    Tensor.RankAtMost T (r * d * d) := by
  have hdesc := rankAtMost_apply_linearMap basis q h
  simpa only [linear_retraction_algebraMap q hq] using hdesc

/-- Form a power over `B` and then descend once. The constant `d²` does not
enter the exponent, even though the coordinate sets grow with `m`. -/
theorem integer_power_rank_descent [Algebra ℤ B] {d r m : ℕ} (basis : Basis (Fin d) ℤ B)
    (q : B →ₗ[ℤ] ℤ) (hq : q 1 = 1) {T : Tensor ℤ X Y Z}
    (h : Tensor.RankAtMost
      (Tensor.power (fun x y z => algebraMap ℤ B (T x y z)) m) r) :
    Tensor.RankAtMost (Tensor.power T m) (r * d * d) := by
  apply integer_rank_descent basis q hq
  have heq : (fun x y z => algebraMap ℤ B (Tensor.power T m x y z)) =
      Tensor.power (fun x y z => algebraMap ℤ B (T x y z)) m := by
    funext x y z
    simp only [Tensor.power, map_prod]
  rw [heq]
  exact h

/-- One base certificate over `B` gives rank at most `r^m * d²` for the integer
power. This theorem powers the certificate over `B` before doing any descent. -/
theorem integer_power_rank_descent_of_base [Algebra ℤ B] {d r : ℕ} (basis : Basis (Fin d) ℤ B)
    (q : B →ₗ[ℤ] ℤ) (hq : q 1 = 1) {T : Tensor ℤ X Y Z}
    (h : Tensor.RankAtMost (fun x y z => algebraMap ℤ B (T x y z)) r) (m : ℕ) :
    Tensor.RankAtMost (Tensor.power T m) (r ^ m * d * d) :=
  integer_power_rank_descent basis q hq (h.power m)

/-- Concatenate finitely many exact rank certificates. The dependent sum of
product slots has cardinality equal to the sum of the individual bounds. -/
theorem rankAtMost_finite_sum {K ι X Y Z : Type*} [CommSemiring K] [Fintype ι]
    (T : ι → Tensor K X Y Z) (r : ι → ℕ)
    (h : ∀ i, Tensor.RankAtMost (T i) (r i)) :
    Tensor.RankAtMost (fun x y z => ∑ i, T i x y z) (∑ i, r i) := by
  classical
  choose a b c h using h
  let aa : (Σ i, Fin (r i)) → X → K := fun p => a p.1 p.2
  let bb : (Σ i, Fin (r i)) → Y → K := fun p => b p.1 p.2
  let cc : (Σ i, Fin (r i)) → Z → K := fun p => c p.1 p.2
  have heq : (fun x y z => ∑ i, T i x y z) =
      fun x y z => ∑ p, Tensor.rankOne (aa p) (bb p) (cc p) x y z := by
    funext x y z
    simp only [Fintype.sum_sigma, aa, bb, cc]
    apply Finset.sum_congr rfl
    intro i hi
    exact congrFun (congrFun (congrFun (h i) x) y) z
  rw [heq]
  simpa only [Fintype.card_sigma, Fintype.card_fin] using
    Tensor.rankAtMost_sum_rankOne aa bb cc

/-- A finite Bézout identity patches rank certificates for scalar multiples of
an integer tensor. The rank cost is the sum of the local costs. -/
theorem integer_rank_patch {ι X Y Z : Type*} [Fintype ι]
    (T : Tensor ℤ X Y Z) (E coeff : ι → ℤ) (r : ι → ℕ)
    (hbezout : ∑ i, coeff i * E i = 1)
    (hrank : ∀ i, Tensor.RankAtMost (fun x y z => E i * T x y z) (r i)) :
    Tensor.RankAtMost T (∑ i, r i) := by
  have hsum := rankAtMost_finite_sum
    (fun i x y z => coeff i * (E i * T x y z)) r
    (fun i => (hrank i).scale (coeff i))
  have heq : (fun x y z => ∑ i, coeff i * (E i * T x y z)) = T := by
    funext x y z
    simp only [← mul_assoc, ← Finset.sum_mul, hbezout, one_mul]
  rw [heq] at hsum
  exact hsum

/-- Abstract patching at the `m`th power: all local costs have the common
exponential factor `N^m`, and the finitely many constants add only once.
Construction of the integers `E` and of their Bézout coefficients is separate. -/
theorem integer_power_rank_patch {ι X Y Z : Type*} [Fintype ι]
    (T : Tensor ℤ X Y Z) (E coeff : ι → ℤ) (K : ι → ℕ) (N m : ℕ)
    (hbezout : ∑ i, coeff i * E i ^ m = 1)
    (hrank : ∀ i, Tensor.RankAtMost
      (fun x y z => E i ^ m * T x y z) (K i * N ^ m)) :
    Tensor.RankAtMost T ((∑ i, K i) * N ^ m) := by
  have h := integer_rank_patch T (fun i => E i ^ m) coeff
    (fun i => K i * N ^ m) hbezout hrank
  simpa only [Finset.sum_mul] using h

#print axioms integer_rank_descent
#print axioms integer_power_rank_descent
#print axioms integer_power_rank_descent_of_base
#print axioms integer_rank_patch
#print axioms integer_power_rank_patch

end Matmul.FiniteAlgebraDescent
