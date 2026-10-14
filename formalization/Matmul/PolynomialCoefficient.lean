import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensor
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.BigOperators
import Matmul.PolynomialPower
import Matmul.IntegerCharacterExtension
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-!
# Integral coefficient extraction for polynomial tensor restrictions

The coefficient tensor has quadratic rank and uses only zeros and ones.
This replaces interpolation when the coefficient ring has no invertible
integer denominators. All degree bounds below are finite, explicit bounds.
-/

namespace Matmul.PolynomialCoefficient

open scoped BigOperators
open OAI.MatrixMultiplication.Foundation

variable {K : Type*} [CommSemiring K]

/-- The three-input coefficient selector for total degree `n`. -/
def coefficientTensor (n : ℕ) :
    Tensor K (Fin (n + 1)) (Fin (n + 1)) (Fin (n + 1)) :=
  fun i j k => if i.val + j.val + k.val = n then 1 else 0

theorem coefficientTensor_zero_one (n : ℕ) :
    ∀ i j k, coefficientTensor (K := K) n i j k = 0 ∨
      coefficientTensor (K := K) n i j k = 1 := by
  intro i j k
  unfold coefficientTensor
  split <;> simp

/-- The coefficient selector admits the unit at every selected degree. -/
theorem coefficientTensor_has_unit (n : ℕ) :
    ∃ i j k, coefficientTensor (K := K) n i j k = 1 := by
  refine ⟨0, 0, ⟨n, by omega⟩, ?_⟩
  simp [coefficientTensor]

/-- Monomial expansion on the first two legs gives quadratic exact rank. -/
theorem coefficientTensor_rank (n : ℕ) :
    Tensor.RankAtMost (coefficientTensor (K := K) n) ((n + 1) ^ 2) := by
  classical
  let a : Fin (n + 1) × Fin (n + 1) → Fin (n + 1) → K :=
    fun p i => if p.1 = i then 1 else 0
  let b : Fin (n + 1) × Fin (n + 1) → Fin (n + 1) → K :=
    fun p j => if p.2 = j then 1 else 0
  let c : Fin (n + 1) × Fin (n + 1) → Fin (n + 1) → K :=
    fun p k => coefficientTensor n p.1 p.2 k
  have heq : coefficientTensor (K := K) n =
      fun i j k => ∑ p, Tensor.rankOne (a p) (b p) (c p) i j k := by
    funext i j k
    simp [a, b, c, Tensor.rankOne, Fintype.sum_prod_type, ite_mul, mul_ite]
  rw [heq]
  convert Tensor.rankAtMost_sum_rankOne a b c using 1
  simp [pow_two]

/-- A rectangular finite-box formula for the coefficient of a product.
The box may be larger than the degree being selected. -/
theorem coeff_mul_box (p q : Polynomial K) {n N : ℕ} (hn : n ≤ N) :
    (p * q).coeff n =
      ∑ i : Fin (N + 1), ∑ j : Fin (N + 1),
        if i.val + j.val = n then p.coeff i.val * q.coeff j.val else 0 := by
  classical
  have inner (i : Fin (N + 1)) :
      (∑ j : Fin (N + 1),
        if i.val + j.val = n then p.coeff i.val * q.coeff j.val else 0) =
        if i.val ≤ n then p.coeff i.val * q.coeff (n - i.val) else 0 := by
    by_cases hi : i.val ≤ n
    · let j₀ : Fin (N + 1) := ⟨n - i.val, by omega⟩
      rw [if_pos hi, Finset.sum_eq_single j₀]
      · simp [j₀, Nat.add_sub_of_le hi]
      · intro j hj hjne
        have hne : i.val + j.val ≠ n := by
          intro heq
          apply hjne
          apply Fin.ext
          dsimp [j₀]
          omega
        simp [hne]
      · simp
    · rw [if_neg hi]
      apply Finset.sum_eq_zero
      intro j hj
      have hne : i.val + j.val ≠ n := by omega
      simp [hne]
  simp_rw [inner]
  rw [Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => p.coeff i * q.coeff j) n,
    Fin.sum_univ_eq_sum_range
      (fun i => if i ≤ n then p.coeff i * q.coeff (n - i) else 0) (N + 1)]
  have hsub : Finset.range (n + 1) ⊆ Finset.range (N + 1) := by
    exact Finset.range_mono (by omega)
  calc
    (∑ i ∈ Finset.range n.succ, p.coeff i * q.coeff (n - i)) =
        ∑ i ∈ Finset.range (n + 1),
          if i ≤ n then p.coeff i * q.coeff (n - i) else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [if_pos (by simpa only [Finset.mem_range, Nat.lt_add_one_iff] using hi)]
    _ = ∑ i ∈ Finset.range (N + 1),
          if i ≤ n then p.coeff i * q.coeff (n - i) else 0 := by
      apply Finset.sum_subset hsub
      intro i hi hnot
      have hni : ¬i ≤ n := by
        simpa only [Finset.mem_range, Nat.lt_add_one_iff] using hnot
      simp [hni]

/-- Three polynomial inputs may all use the same finite coefficient cap. -/
theorem coeff_mul_triple_box (p q r : Polynomial K) {n N : ℕ} (hn : n ≤ N) :
    (p * q * r).coeff n =
      ∑ i : Fin (N + 1), ∑ j : Fin (N + 1), ∑ k : Fin (N + 1),
        if i.val + j.val + k.val = n then
          p.coeff i.val * q.coeff j.val * r.coeff k.val else 0 := by
  classical
  let f : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → K :=
    fun h k i j => if i.val + j.val = h.val ∧ h.val + k.val = n then
      p.coeff i.val * q.coeff j.val * r.coeff k.val else 0
  have hexpand (h k : Fin (N + 1)) :
      (if h.val + k.val = n then (p * q).coeff h.val * r.coeff k.val else 0) =
        ∑ i, ∑ j, f h k i j := by
    rw [coeff_mul_box p q (by omega : h.val ≤ N)]
    by_cases hh : h.val + k.val = n
    · simp [f, hh, Finset.sum_mul, ite_mul]
    · simp [f, hh]
  have hinner (i j k : Fin (N + 1)) :
      (∑ h, f h k i j) =
        if i.val + j.val + k.val = n then
          p.coeff i.val * q.coeff j.val * r.coeff k.val else 0 := by
    by_cases hij : i.val + j.val + k.val = n
    · let h₀ : Fin (N + 1) := ⟨i.val + j.val, by omega⟩
      rw [if_pos hij, Finset.sum_eq_single h₀]
      · simp [f, h₀, hij]
      · intro h hh hne
        have hbad : i.val + j.val ≠ h.val := by
          intro heq
          apply hne
          apply Fin.ext
          simpa [h₀] using heq.symm
        simp [f, hbad]
      · simp
    · rw [if_neg hij]
      apply Finset.sum_eq_zero
      intro h hh
      have hbad : ¬(i.val + j.val = h.val ∧ h.val + k.val = n) := by omega
      simp [f, hbad]
  rw [coeff_mul_box (p * q) r hn]
  simp_rw [hexpand]
  calc
    (∑ h, ∑ k, ∑ i, ∑ j, f h k i j) =
        ∑ h, ∑ i, ∑ k, ∑ j, f h k i j := by
      apply Finset.sum_congr rfl
      intro h hh
      rw [Finset.sum_comm]
    _ = ∑ i, ∑ h, ∑ k, ∑ j, f h k i j := by rw [Finset.sum_comm]
    _ = ∑ i, ∑ j, ∑ k, ∑ h, f h k i j := by
      apply Finset.sum_congr rfl
      intro i hi
      calc
        (∑ h, ∑ k, ∑ j, f h k i j) = ∑ h, ∑ j, ∑ k, f h k i j := by
          apply Finset.sum_congr rfl
          intro h hh
          rw [Finset.sum_comm]
        _ = ∑ j, ∑ h, ∑ k, f h k i j := by rw [Finset.sum_comm]
        _ = ∑ j, ∑ k, ∑ h, f h k i j := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.sum_comm]
    _ = _ := by simp_rw [hinner]

/-- Rearrange the six finite indices without any infinite sums. -/
theorem sum_three_prod_types {X Y Z I J L : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype I] [Fintype J] [Fintype L]
    (f : X → Y → Z → I → J → L → K) :
    (∑ xi : X × I, ∑ yj : Y × J, ∑ zl : Z × L,
      f xi.1 yj.1 zl.1 xi.2 yj.2 zl.2) =
      ∑ x, ∑ y, ∑ z, ∑ i, ∑ j, ∑ l, f x y z i j l := by
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x hx
  calc
    (∑ i, ∑ y, ∑ j, ∑ z, ∑ l, f x y z i j l) =
        ∑ y, ∑ i, ∑ j, ∑ z, ∑ l, f x y z i j l := by rw [Finset.sum_comm]
    _ = ∑ y, ∑ i, ∑ z, ∑ j, ∑ l, f x y z i j l := by
      apply Finset.sum_congr rfl
      intro y hy
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = ∑ y, ∑ z, ∑ i, ∑ j, ∑ l, f x y z i j l := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [Finset.sum_comm]

/-- The three coefficient maps used by actual integral extraction. -/
def coefficientMap {X U : Type*} (A : U → X → Polynomial K) (n : ℕ) :
    U → X × Fin (n + 1) → K :=
  fun u xi => (A u xi.1).coeff xi.2.val

/-- Extracting a coefficient of polynomial restriction is an actual
restriction of the original tensor times a finite zero-one selector. -/
theorem coefficient_restrict_eq {X Y Z U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) (A : U → X → Polynomial K)
    (B : V → Y → Polynomial K) (C : W → Z → Polynomial K) (n : ℕ) :
    (fun u v w => (Tensor.restrict A B C
      (fun x y z => Polynomial.C (T x y z)) u v w).coeff n) =
      Tensor.restrict (coefficientMap A n) (coefficientMap B n) (coefficientMap C n)
        (Tensor.product T (coefficientTensor (K := K) n)) := by
  classical
  have hcoeff (p q r : Polynomial K) (t : K) :
      (p * q * r * Polynomial.C t).coeff n =
        ∑ i : Fin (n + 1), ∑ j : Fin (n + 1), ∑ k : Fin (n + 1),
          p.coeff i.val * q.coeff j.val * r.coeff k.val *
            (t * coefficientTensor n i j k) := by
    rw [Polynomial.coeff_mul_C, coeff_mul_triple_box p q r (le_refl n)]
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hsum : i.val + j.val + k.val = n <;>
      simp [coefficientTensor, hsum]
  funext u v w
  simp only [Tensor.restrict, Polynomial.finsetSum_coeff, coefficientMap, Tensor.product]
  rw [sum_three_prod_types (fun x y z (i j k : Fin (n + 1)) =>
    (A u x).coeff i.val * (B v y).coeff j.val * (C w z).coeff k.val *
      (T x y z * coefficientTensor n i j k))]
  simp_rw [hcoeff]

/-- Every tensor power of the leading coefficient is an actual restriction
of an original tensor power times a quadratic-rank coefficient selector. -/
theorem leading_power_restriction {X Y Z U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) (Utarget : Tensor K U V W)
    (A : U → X → Polynomial K) (B : V → Y → Polynomial K)
    (C : W → Z → Polynomial K) (ℓ m : ℕ)
    (hbelow : ∀ d : ℕ, d < ℓ →
      (fun u v w => (Tensor.restrict A B C
        (fun x y z => Polynomial.C (T x y z)) u v w).coeff d) = 0)
    (hleading : (fun u v w => (Tensor.restrict A B C
      (fun x y z => Polynomial.C (T x y z)) u v w).coeff ℓ) = Utarget) :
    ∃ (Am : (Fin m → U) → (Fin m → X) × Fin (m * ℓ + 1) → K)
      (Bm : (Fin m → V) → (Fin m → Y) × Fin (m * ℓ + 1) → K)
      (Cm : (Fin m → W) → (Fin m → Z) × Fin (m * ℓ + 1) → K),
      Tensor.power Utarget m = Tensor.restrict Am Bm Cm
        (Tensor.product (Tensor.power T m) (coefficientTensor (K := K) (m * ℓ))) := by
  classical
  let F := Tensor.restrict A B C (fun x y z => Polynomial.C (T x y z))
  let Ap : (Fin m → U) → (Fin m → X) → Polynomial K :=
    fun u x => ∏ i, A (u i) (x i)
  let Bp : (Fin m → V) → (Fin m → Y) → Polynomial K :=
    fun v y => ∏ i, B (v i) (y i)
  let Cp : (Fin m → W) → (Fin m → Z) → Polynomial K :=
    fun w z => ∏ i, C (w i) (z i)
  have hlow : ∀ u v w d, d < ℓ → (F u v w).coeff d = 0 := by
    intro u v w d hd
    exact congrFun (congrFun (congrFun (hbelow d hd) u) v) w
  have hlead : ∀ u v w, (F u v w).coeff ℓ = Utarget u v w := by
    intro u v w
    exact congrFun (congrFun (congrFun hleading u) v) w
  have hpower := Matmul.PolynomialPower.tensor_power_leading_coeff F Utarget ℓ m hlow hlead
  have hpconst : Tensor.power (fun x y z => Polynomial.C (T x y z)) m =
      (fun x y z => Polynomial.C (Tensor.power T m x y z)) := by
    funext x y z
    simp [Tensor.power, map_prod]
  have hrestrict : Tensor.power F m = Tensor.restrict Ap Bp Cp
      (fun x y z => Polynomial.C (Tensor.power T m x y z)) := by
    simpa only [F, Ap, Bp, Cp, hpconst] using
      Matmul.PolynomialPower.tensor_restrict_power A B C
        (fun x y z => Polynomial.C (T x y z)) m
  refine ⟨coefficientMap Ap (m * ℓ), coefficientMap Bp (m * ℓ),
    coefficientMap Cp (m * ℓ), ?_⟩
  rw [← hpower, hrestrict]
  exact coefficient_restrict_eq (Tensor.power T m) Ap Bp Cp (m * ℓ)

/-- Polynomial overhead in a tensor-power bound disappears at the level of
a nonnegative multiplicative valuation. -/
theorem le_of_powers_with_quadratic_overhead {a b : ℝ} (_ha : 0 ≤ a) (hb : 0 ≤ b)
    (ℓ : ℕ) (h : ∀ m : ℕ, a ^ m ≤ b ^ m * ((m : ℝ) * ℓ + 1) ^ 2) : a ≤ b := by
  open Filter Topology in
  by_contra hnot
  have hab : b < a := lt_of_not_ge hnot
  have ha0 : 0 < a := lt_of_le_of_lt hb hab
  let q : ℝ := b / a
  have hq0 : 0 ≤ q := div_nonneg hb ha0.le
  have hq1 : q < 1 := (div_lt_one ha0).2 hab
  have h2 := tendsto_pow_const_mul_const_pow_of_lt_one 2 hq0 hq1
  have h1 := tendsto_pow_const_mul_const_pow_of_lt_one 1 hq0 hq1
  have h0 := tendsto_pow_const_mul_const_pow_of_lt_one 0 hq0 hq1
  have hlim : Filter.Tendsto (fun m : ℕ => ((m : ℝ) * ℓ + 1) ^ 2 * q ^ m)
      Filter.atTop (nhds 0) := by
    convert ((h2.const_mul ((ℓ : ℝ) ^ 2)).add (h1.const_mul (2 * (ℓ : ℝ)))).add h0 using 1
    · ext m
      ring
    · simp
  have hbound (m : ℕ) : (1 : ℝ) ≤ ((m : ℝ) * ℓ + 1) ^ 2 * q ^ m := by
    have hm : (1 : ℝ) ≤ b ^ m * ((m : ℝ) * ℓ + 1) ^ 2 / a ^ m :=
      (le_div_iff₀ (pow_pos ha0 m)).2 (by simpa using h m)
    have heq : b ^ m * ((m : ℝ) * ℓ + 1) ^ 2 / a ^ m =
        ((m : ℝ) * ℓ + 1) ^ 2 * q ^ m := by
      dsimp [q]
      rw [div_pow]
      ring
    rw [heq] at hm
    exact hm
  have hbad : (1 : ℝ) ≤ 0 :=
    ge_of_tendsto hlim (Filter.Eventually.of_forall hbound)
  norm_num at hbad

/-- Every integral coefficient character is monotone under a polynomial
restriction whose first nonzero coefficient is the target tensor. The proof
uses actual integral restrictions of all tensor powers and removes the
quadratic rank of the coefficient selectors. -/
theorem polynomialRestrictionMonotone (χ : Matmul.IntegralCharacter)
    {X Y Z U V W : Type} [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor ℤ X Y Z) (Utarget : Tensor ℤ U V W)
    (A : U → X → Polynomial ℤ) (B : V → Y → Polynomial ℤ)
    (C : W → Z → Polynomial ℤ) (ℓ : ℕ)
    (hbelow : ∀ d : ℕ, d < ℓ →
      (fun u v w => (Tensor.restrict A B C
        (fun x y z => Polynomial.C (T x y z)) u v w).coeff d) = 0)
    (hleading : (fun u v w => (Tensor.restrict A B C
      (fun x y z => Polynomial.C (T x y z)) u v w).coeff ℓ) = Utarget) :
    χ.value Utarget ≤ χ.value T := by
  apply le_of_powers_with_quadratic_overhead (χ.nonneg Utarget) (χ.nonneg T) ℓ
  intro m
  obtain ⟨Am, Bm, Cm, hrestriction⟩ :=
    leading_power_restriction T Utarget A B C ℓ m hbelow hleading
  have hmono := χ.monotone
    (Tensor.product (Tensor.power T m) (coefficientTensor (K := ℤ) (m * ℓ))) Am Bm Cm
  rw [← hrestriction, χ.value_power, χ.map_product, χ.value_power] at hmono
  have hselector := χ.value_le_rank (coefficientTensor_rank (K := ℤ) (m * ℓ))
  have hbound := mul_le_mul_of_nonneg_left hselector (pow_nonneg (χ.nonneg T) m)
  have hh := hmono.trans hbound
  push_cast at hh
  exact hh

#print axioms coefficientTensor_rank
#print axioms coeff_mul_box
#print axioms coeff_mul_triple_box
#print axioms coefficient_restrict_eq
#print axioms leading_power_restriction
#print axioms le_of_powers_with_quadratic_overhead
#print axioms polynomialRestrictionMonotone

end Matmul.PolynomialCoefficient
