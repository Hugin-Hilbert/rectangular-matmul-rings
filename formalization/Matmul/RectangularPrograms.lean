import Matmul.UniversalPaddedProgram
import Matmul.RectangularPaddingShape
import Matmul.RectangularOptimization
import Matmul.RectangularRankBridge

/-!
# Universal strict arithmetic programs for rectangular multiplication

An integer base scheme produces one finite arithmetic circuit for every input
size. Its wires and gates do not depend on the coefficient ring. The finite
initial sizes are absorbed into one constant, giving an operation bound for
every positive size rather than only an eventual asymptotic statement.
-/

namespace Matmul.RectangularPrograms

open Matmul.IntegerBilinear Matmul.UniversalRecursion
open Matmul.UniversalRecursiveAlgorithm Matmul.UniversalProgram
open Matmul.UniversalPaddedProgram
open Filter
open scoped BigOperators

noncomputable section

/-- The requested rounded rectangular inner dimension. -/
def width (k : ℝ) (n : ℕ) : ℕ := Nat.ceil ((n : ℝ) ^ k)

@[simp] theorem width_one (n : ℕ) : width 1 n = n := by
  simp [width]

abbrev RectangularCircuit (k : ℝ) (n : ℕ) :=
  Circuit ((Fin n × Fin (width k n)) ⊕ (Fin (width k n) × Fin n)) (Fin n × Fin n)

/-- Padding depth is the next strictly larger power of the fixed outer base. -/
def depth (a n : ℕ) : ℕ := Nat.log a n + 1

theorem outer_fits (a n : ℕ) (ha : 1 < a) : n ≤ a ^ depth a n :=
  (Nat.lt_pow_succ_log_self ha n).le

theorem inner_fits (a b n : ℕ) (k : ℝ) (ha : 1 < a)
    (hk : 0 ≤ k) (hab : (a : ℝ) ^ k ≤ (b : ℝ)) :
    width k n ≤ b ^ depth a n :=
  Matmul.RectangularPaddingShape.ceil_rpow_le_pow_of_le_pow a b n (depth a n)
    k hk hab (outer_fits a n ha)

variable {a b ρ : ℕ}

/-- A fixed integer scheme is compiled to actual arithmetic syntax at every
rounded rectangular input size. Only indices are used to choose padding wires. -/
def program (alg : Scheme a b a ρ) (k : ℝ) (ha : 1 < a)
    (hk : 0 ≤ k) (hab : (a : ℝ) ^ k ≤ (b : ℝ)) (n : ℕ) :
    RectangularCircuit k n :=
  paddedProgram alg (depth a n) (outer_fits a n ha)
    (inner_fits a b n k ha hk hab) (outer_fits a n ha)

/-- Every circuit computes the ordered product over an arbitrary associative
ring; no multiplicative unit or commutativity is used. -/
theorem program_correct {R : Type*} [NonUnitalRing R]
    (alg : Scheme a b a ρ) (h : alg.tensor = matrixTensor a b a)
    (k : ℝ) (ha : 1 < a) (hk : 0 ≤ k) (hab : (a : ℝ) ^ k ≤ (b : ℝ))
    (n : ℕ) (A : Matrix (Fin n) (Fin (width k n)) R)
    (B : Matrix (Fin (width k n)) (Fin n) R) (i j : Fin n) :
    (program alg k ha hk hab n).eval (encode A B) (i, j) = (A * B) i j :=
  paddedProgram_correct alg h (depth a n) (outer_fits a n ha)
    (inner_fits a b n k ha hk hab) (outer_fits a n ha) A B i j

theorem program_cost_le_work (alg : Scheme a b a ρ) (k : ℝ) (ha : 1 < a)
    (hk : 0 ≤ k) (hab : (a : ℝ) ^ k ≤ (b : ℝ)) (n : ℕ) :
    (program alg k ha hk hab n).cost ≤
      Matmul.RecursiveCost.paddedWork 1 (linearWeight alg) ρ
        (Matmul.RecursiveCost.blockVolume a b a) a n :=
  paddedProgram_cost_le_work alg (depth a n) (outer_fits a n ha)
    (inner_fits a b n k ha hk hab) (outer_fits a n ha)

/-- A finite initial segment of a ring-independent gate count is absorbed
into a single positive constant whenever the asymptotic power is nonnegative. -/
theorem all_sizes_of_eventual_bound (cost : ℕ → ℕ) (E A : ℝ)
    (hE : 0 ≤ E) (hA : 0 ≤ A)
    (h : ∀ᶠ n : ℕ in atTop, (cost n : ℝ) ≤ A * (n : ℝ) ^ E) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → (cost n : ℝ) ≤ C * (n : ℝ) ^ E := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  let S : ℝ := ∑ n ∈ Finset.range N, (cost n : ℝ)
  have hS : 0 ≤ S := Finset.sum_nonneg (fun n hn => Nat.cast_nonneg _)
  let C : ℝ := A + S + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro n hn
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hp : 1 ≤ (n : ℝ) ^ E := Real.one_le_rpow hnR hE
  have hAC : A ≤ C := by dsimp [C]; linarith
  by_cases hlarge : N ≤ n
  · exact (hN n hlarge).trans (mul_le_mul_of_nonneg_right hAC (by positivity))
  · have hnN : n ∈ Finset.range N := Finset.mem_range.mpr (by omega)
    have hcS : (cost n : ℝ) ≤ S :=
      Finset.single_le_sum (fun m hm => Nat.cast_nonneg (cost m)) hnN
    have hSC : S ≤ C := by dsimp [C]; linarith
    calc
      (cost n : ℝ) ≤ S := hcS
      _ ≤ C := hSC
      _ = C * 1 := (mul_one C).symm
      _ ≤ C * (n : ℝ) ^ E := mul_le_mul_of_nonneg_left hp hC.le

/-- Every target exponent strictly above the base rank ratio bounds all the
actual gate counts by one constant independent of the coefficient ring. -/
theorem program_cost_bound (alg : Scheme a b a ρ) (k E : ℝ)
    (ha : 1 < a) (hk : 0 ≤ k) (hab : (a : ℝ) ^ k ≤ (b : ℝ))
    (hρ : 1 ≤ ρ) (hvolume : Matmul.RecursiveCost.blockVolume a b a ≤ ρ)
    (hE : Real.log (ρ : ℝ) / Real.log (a : ℝ) < E) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ((program alg k ha hk hab n).cost : ℝ) ≤ C * (n : ℝ) ^ E := by
  let θ : ℝ := Real.log (ρ : ℝ) / Real.log (a : ℝ)
  let δ : ℝ := (E - θ) / 2
  have hδ : 0 < δ := by dsimp [δ, θ]; linarith
  have haR : 1 < (a : ℝ) := by exact_mod_cast ha
  have hρR : 1 ≤ (ρ : ℝ) := by exact_mod_cast hρ
  have hθ : 0 ≤ θ :=
    div_nonneg (Real.log_nonneg hρR) (Real.log_pos haR).le
  have hE0 : 0 ≤ E := hθ.trans hE.le
  have hθδ : θ + δ ≤ E := by dsimp [δ]; linarith
  have hwork := Matmul.RecursiveCost.paddedWork_eventually_rpow
    1 (linearWeight alg) ρ (Matmul.RecursiveCost.blockVolume a b a) a
    hρ hvolume ha δ hδ
  let A : ℝ := (a : ℝ) ^ (θ + δ)
  have hA : 0 ≤ A := Real.rpow_nonneg (by positivity) _
  apply all_sizes_of_eventual_bound (fun n => (program alg k ha hk hab n).cost)
    E A hE0 hA
  filter_upwards [hwork, eventually_ge_atTop 1] with n hn hnpos
  have hc : ((program alg k ha hk hab n).cost : ℝ) ≤
      (Matmul.RecursiveCost.paddedWork 1 (linearWeight alg) ρ
        (Matmul.RecursiveCost.blockVolume a b a) a n : ℝ) := by
    exact_mod_cast program_cost_le_work alg k ha hk hab n
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnpos
  exact (hc.trans hn).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hnR hθδ) hA)

universe u

/-- A base scheme yields a family of strict circuits, uniformly valid over
every ring in any universe, with one common arithmetic-gate bound for all
positive input sizes. -/
theorem exists_programs_of_scheme (alg : Scheme a b a ρ)
    (h : alg.tensor = matrixTensor a b a) (k E : ℝ)
    (ha : 1 < a) (hk : 0 ≤ k) (hab : (a : ℝ) ^ k ≤ (b : ℝ))
    (hρ : 1 ≤ ρ) (hvolume : Matmul.RecursiveCost.blockVolume a b a ≤ ρ)
    (hE : Real.log (ρ : ℝ) / Real.log (a : ℝ) < E) :
    ∃ (P : ∀ n : ℕ, RectangularCircuit k n) (C : ℝ), 0 < C ∧
      (∀ (R : Type u) [NonUnitalRing R] (n : ℕ)
        (A : Matrix (Fin n) (Fin (width k n)) R)
        (B : Matrix (Fin (width k n)) (Fin n) R) (i j : Fin n),
        (P n).eval (encode A B) (i, j) = (A * B) i j) ∧
      (∀ n : ℕ, 1 ≤ n → ((P n).cost : ℝ) ≤ C * (n : ℝ) ^ E) := by
  obtain ⟨C, hC, hcost⟩ := program_cost_bound alg k E ha hk hab hρ hvolume hE
  refine ⟨program alg k ha hk hab, C, hC, ?_, hcost⟩
  intro R inst n A B i j
  exact program_correct alg h k ha hk hab n A B i j

/-- Every aspect exponent `k ≥ 0` admits one family of strict arithmetic
circuits with the rectangular-curve operation bound, uniformly over all
associative rings and every positive input size. The circuit family and the
constant are chosen before the ring. -/
theorem rectangular_multiplication_programs {k ε : ℝ} (hk : 0 ≤ k) (hε : 0 < ε) :
    ∃ (P : ∀ n : ℕ, RectangularCircuit k n) (C : ℝ), 0 < C ∧
      (∀ (R : Type u) [NonUnitalRing R] (n : ℕ)
        (A : Matrix (Fin n) (Fin (width k n)) R)
        (B : Matrix (Fin (width k n)) (Fin n) R) (i j : Fin n),
        (P n).eval (encode A B) (i, j) = (A * B) i j) ∧
      (∀ n : ℕ, 1 ≤ n → ((P n).cost : ℝ) ≤
        C * (n : ℝ) ^ (Matmul.RectangularOptimization.rectangularBound k + ε)) := by
  obtain ⟨cert⟩ := Matmul.RectangularRankBridge.exists_scheme_certificate hk
    (by positivity : 0 < ε / 2)
  have ha : 1 < cert.a := by have := cert.a_ge_two; omega
  have hρ : 1 ≤ cert.ρ := by
    have hb := Matmul.RecursiveCost.blockVolume_bounds cert.a cert.b cert.a
    have hapos : 0 < cert.a := by omega
    have hpos := (Nat.mul_pos hapos hapos).trans_le (hb.2.2.trans cert.volume)
    omega
  apply exists_programs_of_scheme cert.alg cert.correct k
    (Matmul.RectangularOptimization.rectangularBound k + ε)
    ha hk cert.shape hρ cert.volume
  have hratio := cert.rankExponent_lt
  linarith

/-- An equality of finite inner dimensions only changes static index types. -/
def castInner {n m p : ℕ} (h : m = p)
    (P : Circuit ((Fin n × Fin m) ⊕ (Fin m × Fin n)) (Fin n × Fin n)) :
    Circuit ((Fin n × Fin p) ⊕ (Fin p × Fin n)) (Fin n × Fin n) := h ▸ P

theorem castInner_cost {n m p : ℕ} (h : m = p)
    (P : Circuit ((Fin n × Fin m) ⊕ (Fin m × Fin n)) (Fin n × Fin n)) :
    (castInner h P).cost = P.cost := by
  cases h
  rfl

theorem castInner_correct {n m p : ℕ} (h : m = p)
    (P : Circuit ((Fin n × Fin m) ⊕ (Fin m × Fin n)) (Fin n × Fin n))
    (hP : ∀ (R : Type u) [NonUnitalRing R]
      (A : Matrix (Fin n) (Fin m) R) (B : Matrix (Fin m) (Fin n) R) (i j : Fin n),
      P.eval (encode A B) (i, j) = (A * B) i j) :
    ∀ (R : Type u) [NonUnitalRing R]
      (A : Matrix (Fin n) (Fin p) R) (B : Matrix (Fin p) (Fin n) R) (i j : Fin n),
      (castInner h P).eval (encode A B) (i, j) = (A * B) i j := by
  cases h
  exact hP

/-- Ordinary square multiplication has the universal `9/4 + ε` bound in
strict addition, negation, and multiplication syntax. -/
theorem square_multiplication_programs {ε : ℝ} (hε : 0 < ε) :
    ∃ (P : ∀ n : ℕ,
      Circuit ((Fin n × Fin n) ⊕ (Fin n × Fin n)) (Fin n × Fin n))
      (C : ℝ), 0 < C ∧
      (∀ (R : Type u) [NonUnitalRing R] (n : ℕ)
        (A B : Matrix (Fin n) (Fin n) R) (i j : Fin n),
        (P n).eval (encode A B) (i, j) = (A * B) i j) ∧
      (∀ n : ℕ, 1 ≤ n → ((P n).cost : ℝ) ≤
        C * (n : ℝ) ^ ((9 : ℝ) / 4 + ε)) := by
  obtain ⟨P, C, hC, hcorrect, hcost⟩ :=
    rectangular_multiplication_programs.{u} (k := 1) (by norm_num) hε
  let Q := fun n => castInner (width_one n) (P n)
  refine ⟨Q, C, hC, ?_, ?_⟩
  · intro R inst n A B i j
    exact castInner_correct (width_one n) (P n)
      (fun R inst A B i j => hcorrect R n A B i j) R A B i j
  · intro n hn
    change ((castInner (width_one n) (P n)).cost : ℝ) ≤ _
    rw [castInner_cost]
    simpa only [Matmul.RectangularOptimization.rectangularBound_one] using hcost n hn

/-- Multiplication of an `n × ceil (sqrt n)` matrix by a
`ceil (sqrt n) × n` matrix has the universal `2 + ε` gate bound. -/
theorem half_rectangular_multiplication_programs {ε : ℝ} (hε : 0 < ε) :
    ∃ (P : ∀ n : ℕ, RectangularCircuit (1 / 2) n) (C : ℝ), 0 < C ∧
      (∀ (R : Type u) [NonUnitalRing R] (n : ℕ)
        (A : Matrix (Fin n) (Fin (width (1 / 2) n)) R)
        (B : Matrix (Fin (width (1 / 2) n)) (Fin n) R) (i j : Fin n),
        (P n).eval (encode A B) (i, j) = (A * B) i j) ∧
      (∀ n : ℕ, 1 ≤ n → ((P n).cost : ℝ) ≤ C * (n : ℝ) ^ (2 + ε)) := by
  simpa only [Matmul.RectangularOptimization.rectangularBound_half] using
    (rectangular_multiplication_programs (k := 1 / 2) (by norm_num) hε)

#print axioms program_correct
#print axioms all_sizes_of_eventual_bound
#print axioms program_cost_bound
#print axioms exists_programs_of_scheme
#print axioms rectangular_multiplication_programs
#print axioms square_multiplication_programs
#print axioms half_rectangular_multiplication_programs

end
end Matmul.RectangularPrograms
