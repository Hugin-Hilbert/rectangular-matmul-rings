import Mathlib.RingTheory.Int.Basic

/-!
# Finite integral Bézout identities

A finite family of integers with no common prime divisor generates the unit
ideal. The same holds for every common power of the family, so its scalar
rank certificates can be patched with actual integer coefficients.
-/

namespace Matmul.IntegralConvolutionBezout

open scoped BigOperators

/-- If every rational prime fails to divide some member of a finite integer
family, its normalized greatest common divisor is one. -/
theorem gcd_eq_one_of_prime_cover {ι : Type*} [Fintype ι] (E : ι → ℤ)
    (hE : ∀ p : ℕ, Nat.Prime p → ∃ i, ¬ (p : ℤ) ∣ E i) :
    Finset.univ.gcd E = 1 := by
  classical
  have habs : (Finset.univ.gcd E).natAbs = 1 := by
    apply Nat.eq_one_iff_not_exists_prime_dvd.mpr
    intro p hp hpdiv
    obtain ⟨i, hi⟩ := hE p hp
    apply hi
    exact (Int.natCast_dvd.mpr hpdiv).trans
      (Finset.gcd_dvd (Finset.mem_univ i))
  have hu : IsUnit (Finset.univ.gcd E) := Int.isUnit_iff_natAbs_eq.mpr habs
  rw [← Finset.normalize_gcd, normalize_eq_one.mpr hu]

/-- A finite family of integers with no common prime divisor admits a finite
Bézout identity with integer coefficients. -/
theorem finite_bezout_of_prime_cover {ι : Type*} [Fintype ι] (E : ι → ℤ)
    (hE : ∀ p : ℕ, Nat.Prime p → ∃ i, ¬ (p : ℤ) ∣ E i) :
    ∃ coeff : ι → ℤ, ∑ i, coeff i * E i = 1 := by
  classical
  obtain ⟨coeff, hcoeff⟩ := Finset.gcd_eq_sum_mul Finset.univ E
  refine ⟨coeff, ?_⟩
  simpa only [gcd_eq_one_of_prime_cover E hE, mul_comm] using hcoeff.symm

/-- Taking a common power preserves the absence of a common prime divisor. -/
theorem prime_cover_pow {ι : Type*} (E : ι → ℤ)
    (hE : ∀ p : ℕ, Nat.Prime p → ∃ i, ¬ (p : ℤ) ∣ E i) (m : ℕ) :
    ∀ p : ℕ, Nat.Prime p → ∃ i, ¬ (p : ℤ) ∣ E i ^ m := by
  intro p hp
  obtain ⟨i, hi⟩ := hE p hp
  exact ⟨i, fun h => hi (Int.Prime.dvd_pow' hp h)⟩

/-- Each common power admits its own integer Bézout coefficients. The
statement includes the zeroth power. -/
theorem finite_bezout_pow_of_prime_cover {ι : Type*} [Fintype ι] (E : ι → ℤ)
    (hE : ∀ p : ℕ, Nat.Prime p → ∃ i, ¬ (p : ℤ) ∣ E i) (m : ℕ) :
    ∃ coeff : ι → ℤ, ∑ i, coeff i * E i ^ m = 1 :=
  finite_bezout_of_prime_cover (fun i => E i ^ m) (prime_cover_pow E hE m)

#print axioms finite_bezout_of_prime_cover
#print axioms finite_bezout_pow_of_prime_cover

end Matmul.IntegralConvolutionBezout
