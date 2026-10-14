import Matmul.IntegralConvolutionFiniteField
import Matmul.IntegralConvolutionNorm
import Matmul.IntegralConvolutionPowers
import Matmul.IntegralConvolutionBezout
import Matmul.IntegerTensor
import Mathlib.Data.Nat.PrimeFin

/-!
# Integral convolution has the optimal exponential rank bound

Adjugate interpolation gives local certificates with a scalar denominator.
For every prime, a fixed finite free integer algebra supplies a denominator
whose norm avoids that prime. Tensor powers are formed over that same algebra
before the single integer descent, retaining only its constant dimension
overhead. Finitely many such certificates, together with ordinary integer
interpolation, are patched by integer Bézout identities.
-/

namespace Matmul.IntegralConvolution

set_option backward.isDefEq.respectTransparency false

open OAI.MatrixMultiplication.Foundation Module
open scoped BigOperators

/-- Clearing the Vandermonde determinant by its algebra norm preserves the
number of interpolation slots. All coefficients remain integral. -/
theorem rankAtMost_norm_vandermonde {B : Type*} [CommRing B] {d r s : ℕ}
    (basis : Basis (Fin d) ℤ B) (nodes : Fin (outputLength r s) → B) :
    Tensor.RankAtMost
      (fun x y z => algebraMap ℤ B
        (Algebra.norm ℤ (Matrix.vandermonde nodes).det * convolution ℤ r s x y z))
      (outputLength r s) := by
  obtain ⟨γ, hγ⟩ := exists_mul_eq_norm basis (Matrix.vandermonde nodes).det
  have h := (rankAtMost_det_vandermonde nodes).scale γ
  have heq : (fun x y z => γ *
      ((Matrix.vandermonde nodes).det * convolution B r s x y z)) =
      (fun x y z => algebraMap ℤ B
        (Algebra.norm ℤ (Matrix.vandermonde nodes).det * convolution ℤ r s x y z)) := by
    funext x y z
    rw [← mul_assoc, mul_comm γ, hγ, map_mul]
    simp [convolution]
  simpa only [heq] using h

/-- A prescribed prime admits a single integer multiplier and a single
constant overhead valid for every tensor power. -/
theorem exists_prime_avoiding_power_rank (r s p : ℕ) (hp : p.Prime) :
    ∃ E : ℤ, ∃ K : ℕ, ¬ (p : ℤ) ∣ E ∧
      ∀ m : ℕ, Tensor.RankAtMost
        (fun x y z => E ^ m * Tensor.power (convolution ℤ r s) m x y z)
        (K * outputLength r s ^ m) := by
  classical
  obtain ⟨g, hg, hd, nodes, hE⟩ := exists_prime_avoiding_nodes p (outputLength r s) hp
  let pb := AdjoinRoot.powerBasis' hg
  refine ⟨Algebra.norm ℤ (Matrix.vandermonde nodes).det,
    g.natDegree * g.natDegree, hE, ?_⟩
  intro m
  have h := scaled_integer_power_rank_of_base pb hd _
    (rankAtMost_norm_vandermonde pb.basis nodes) m
  simpa only [pb, AdjoinRoot.powerBasis'_dim, mul_comm, mul_left_comm, mul_assoc] using h

/-- A finite family of integer multipliers covers all rational primes.
Only the prime factors of one nonzero ordinary interpolation denominator
require an auxiliary finite free algebra. -/
theorem exists_finite_power_rank_cover (r s : ℕ) :
    ∃ E₀ : ℤ, ∃ E : Option ↑E₀.natAbs.primeFactors → ℤ,
      ∃ K : Option ↑E₀.natAbs.primeFactors → ℕ,
        (∀ p : ℕ, p.Prime → ∃ i, ¬ (p : ℤ) ∣ E i) ∧
        (∀ i m, Tensor.RankAtMost
          (fun x y z => E i ^ m * Tensor.power (convolution ℤ r s) m x y z)
          (K i * outputLength r s ^ m)) := by
  classical
  obtain ⟨E₀, hE₀, hbase⟩ := exists_integer_scaled_rank r s
  let P := ↑E₀.natAbs.primeFactors
  have hlocal : ∀ p : P, ∃ E : ℤ, ∃ K : ℕ, ¬ (p.val : ℤ) ∣ E ∧
      ∀ m : ℕ, Tensor.RankAtMost
        (fun x y z => E ^ m * Tensor.power (convolution ℤ r s) m x y z)
        (K * outputLength r s ^ m) := by
    intro p
    exact exists_prime_avoiding_power_rank r s p.val (Nat.prime_of_mem_primeFactors p.property)
  choose Ep Kp hp hpower using hlocal
  let E : Option P → ℤ := fun i => i.elim E₀ Ep
  let K : Option P → ℕ := fun i => i.elim 1 Kp
  refine ⟨E₀, E, K, ?_, ?_⟩
  · intro p hpprime
    by_cases hdiv : (p : ℤ) ∣ E₀
    · have hmem : p ∈ E₀.natAbs.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hpprime, Int.natCast_dvd.mp hdiv,
          Int.natAbs_ne_zero.mpr hE₀⟩
      exact ⟨some ⟨p, hmem⟩, hp ⟨p, hmem⟩⟩
    · exact ⟨none, hdiv⟩
  · intro i m
    cases i with
    | none =>
      simpa only [E, K, Option.elim_none, one_mul, tensor_power_scale] using hbase.power m
    | some p =>
      exact hpower p m

/-- For fixed lengths, integer convolution has rank at most a constant
times `(r + s - 1)^m` at every tensor power. The constant is independent of
the power, including the zeroth power and empty input coordinate types. -/
theorem exists_power_rank_bound (r s : ℕ) :
    ∃ K : ℕ, ∀ m : ℕ, Tensor.RankAtMost
      (Tensor.power (convolution ℤ r s) m) (K * outputLength r s ^ m) := by
  classical
  obtain ⟨E₀, E, K, hcover, hpower⟩ := exists_finite_power_rank_cover r s
  refine ⟨∑ i, K i, ?_⟩
  intro m
  obtain ⟨coeff, hcoeff⟩ :=
    Matmul.IntegralConvolutionBezout.finite_bezout_pow_of_prime_cover E hcover m
  exact Matmul.FiniteAlgebraDescent.integer_power_rank_patch
    (Tensor.power (convolution ℤ r s) m) E coeff K (outputLength r s) m hcoeff
    (fun i => hpower i m)

/-- The constant can be taken positive: the zeroth tensor power is the
nonzero unit tensor, even when an input coordinate type is empty. -/
theorem exists_pos_power_rank_bound (r s : ℕ) :
    ∃ K : ℕ, 0 < K ∧ ∀ m : ℕ, Tensor.RankAtMost
      (Tensor.power (convolution ℤ r s) m) (K * outputLength r s ^ m) := by
  obtain ⟨K, hK⟩ := exists_power_rank_bound r s
  refine ⟨K, ?_, hK⟩
  have hnz : Tensor.power (convolution ℤ r s) 0 ≠ 0 := by
    intro hzero
    have h := congrArg (fun T => T Fin.elim0 Fin.elim0 Fin.elim0) hzero
    simp [Tensor.power] at h
  have hpos :=
    (OAI.MatrixMultiplication.AuxiliarySeparation.exactRank_pos_iff _).mpr hnz
  have hle := OAI.MatrixMultiplication.AuxiliarySeparation.exactRank_le (hK 0)
  simpa only [pow_zero, mul_one] using hpos.trans_le hle

/-- The existential rank certificate also bounds the least exact rank. -/
theorem exists_exactRank_power_bound (r s : ℕ) :
    ∃ K : ℕ, ∀ m : ℕ,
      OAI.MatrixMultiplication.AuxiliarySeparation.exactRank
        (Tensor.power (convolution ℤ r s) m) ≤ K * outputLength r s ^ m := by
  obtain ⟨K, hK⟩ := exists_power_rank_bound r s
  exact ⟨K, fun m => OAI.MatrixMultiplication.AuxiliarySeparation.exactRank_le (hK m)⟩

#print axioms rankAtMost_norm_vandermonde
#print axioms exists_prime_avoiding_power_rank
#print axioms exists_finite_power_rank_cover
#print axioms exists_power_rank_bound
#print axioms exists_pos_power_rank_bound
#print axioms exists_exactRank_power_bound

end Matmul.IntegralConvolution
