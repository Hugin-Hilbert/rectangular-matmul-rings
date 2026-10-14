import Matmul.IntegerCharacter
import Matmul.IntegralConvolution
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Character values of the three integral convolution orientations

Every value in this module is evaluated on an actual integral tensor.  The
linear upper bound follows from the integral power-rank certificates, with
its fixed constant removed by taking arbitrarily large powers.
-/

namespace Matmul.ConvolutionCharacter

open OAI.MatrixMultiplication.Foundation
open Matmul.IntegralConvolution Matmul.IntegralCharacter Matmul.IntegerCharacter
open scoped BigOperators

noncomputable section

abbrev CXY (r s : ℕ) := convolution ℤ r s

def CXZ (r s : ℕ) : Tensor ℤ (Fin r) (Fin (outputLength r s)) (Fin s) :=
  fun x z y => CXY r s x y z

def CYZ (r s : ℕ) : Tensor ℤ (Fin (outputLength r s)) (Fin r) (Fin s) :=
  fun z x y => CXY r s x y z

def valueXY (φ : IntegralCharacter) (r s : ℕ) : ℝ := φ.value (CXY r s)
def valueXZ (φ : IntegralCharacter) (r s : ℕ) : ℝ := φ.value (CXZ r s)
def valueYZ (φ : IntegralCharacter) (r s : ℕ) : ℝ := φ.value (CYZ r s)

theorem valueXY_nonneg (φ : IntegralCharacter) (r s : ℕ) : 0 ≤ valueXY φ r s :=
  φ.nonneg _
theorem valueXZ_nonneg (φ : IntegralCharacter) (r s : ℕ) : 0 ≤ valueXZ φ r s :=
  φ.nonneg _
theorem valueYZ_nonneg (φ : IntegralCharacter) (r s : ℕ) : 0 ≤ valueYZ φ r s :=
  φ.nonneg _

theorem valueXY_pos (φ : IntegralCharacter) (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s) :
    0 < valueXY φ r s := by
  apply φ.value_pos_of_coefficient_one (CXY r s) ⟨0, by omega⟩ ⟨0, by omega⟩
    ⟨0, by unfold outputLength; omega⟩
  simp [CXY, convolution]

theorem valueXZ_pos (φ : IntegralCharacter) (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s) :
    0 < valueXZ φ r s := by
  apply φ.value_pos_of_coefficient_one (CXZ r s) ⟨0, by omega⟩
    ⟨0, by unfold outputLength; omega⟩ ⟨0, by omega⟩
  simp [CXZ, CXY, convolution]

theorem valueYZ_pos (φ : IntegralCharacter) (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s) :
    0 < valueYZ φ r s := by
  apply φ.value_pos_of_coefficient_one (CYZ r s)
    ⟨0, by unfold outputLength; omega⟩ ⟨0, by omega⟩ ⟨0, by omega⟩
  simp [CYZ, CXY, convolution]

/-- A fixed multiplicative overhead disappears under unbounded powers. -/
theorem le_of_powers_with_constant {a b K : ℝ} (hb : 0 ≤ b)
    (h : ∀ m : ℕ, a ^ m ≤ K * b ^ m) : a ≤ b := by
  open Filter Topology in
  by_contra hnot
  have hab : b < a := lt_of_not_ge hnot
  have ha : 0 < a := hb.trans_lt hab
  have hq0 : 0 ≤ b / a := div_nonneg hb ha.le
  have hq1 : b / a < 1 := (div_lt_one ha).2 hab
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul K
  have hbound (m : ℕ) : (1 : ℝ) ≤ K * (b / a) ^ m := by
    rw [div_pow, ← mul_div_assoc]
    exact (le_div_iff₀ (pow_pos ha m)).2 (by simpa using h m)
  have hbad : (1 : ℝ) ≤ 0 := by
    simpa using ge_of_tendsto ht (Filter.Eventually.of_forall hbound)
  norm_num at hbad

/-- Permuting the last two coordinate spaces preserves integral rank. -/
theorem rankAtMost_swapYZ {X Y Z : Type} {T : Tensor ℤ X Y Z} {n : ℕ}
    (h : Tensor.RankAtMost T n) : Tensor.RankAtMost (fun x z y => T x y z) n := by
  rcases h with ⟨a, b, c, heq⟩
  refine ⟨a, c, b, ?_⟩
  funext x z y
  rw [heq]
  apply Finset.sum_congr rfl
  intro i hi
  dsimp [Tensor.rankOne]
  ring

/-- Cycling the coordinate spaces preserves integral rank. -/
theorem rankAtMost_cycle {X Y Z : Type} {T : Tensor ℤ X Y Z} {n : ℕ}
    (h : Tensor.RankAtMost T n) : Tensor.RankAtMost (fun z x y => T x y z) n := by
  rcases h with ⟨a, b, c, heq⟩
  refine ⟨c, a, b, ?_⟩
  funext z x y
  rw [heq]
  apply Finset.sum_congr rfl
  intro i hi
  dsimp [Tensor.rankOne]
  ring

theorem valueXY_le_outputLength (φ : IntegralCharacter) (r s : ℕ) :
    valueXY φ r s ≤ (outputLength r s : ℝ) := by
  obtain ⟨K, hK⟩ := exists_power_rank_bound r s
  apply le_of_powers_with_constant (by positivity) (K := (K : ℝ))
  intro m
  have h := φ.value_le_rank (hK m)
  rw [φ.value_power] at h
  simpa only [Nat.cast_mul, Nat.cast_pow, valueXY, CXY] using h

theorem valueXZ_le_outputLength (φ : IntegralCharacter) (r s : ℕ) :
    valueXZ φ r s ≤ (outputLength r s : ℝ) := by
  obtain ⟨K, hK⟩ := exists_power_rank_bound r s
  apply le_of_powers_with_constant (by positivity) (K := (K : ℝ))
  intro m
  have h := φ.value_le_rank (rankAtMost_swapYZ (hK m))
  change φ.value (Tensor.power (CXZ r s) m) ≤ (K * outputLength r s ^ m : ℕ) at h
  rw [φ.value_power] at h
  simpa only [Nat.cast_mul, Nat.cast_pow, valueXZ] using h

theorem valueYZ_le_outputLength (φ : IntegralCharacter) (r s : ℕ) :
    valueYZ φ r s ≤ (outputLength r s : ℝ) := by
  obtain ⟨K, hK⟩ := exists_power_rank_bound r s
  apply le_of_powers_with_constant (by positivity) (K := (K : ℝ))
  intro m
  have h := φ.value_le_rank (rankAtMost_cycle (hK m))
  change φ.value (Tensor.power (CYZ r s) m) ≤ (K * outputLength r s ^ m : ℕ) at h
  rw [φ.value_power] at h
  simpa only [Nat.cast_mul, Nat.cast_pow, valueYZ] using h

theorem outputLength_cast (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s) :
    (outputLength r s : ℝ) = (r : ℝ) + s - 1 := by
  unfold outputLength
  rw [Nat.cast_sub (by omega : 1 ≤ r + s), Nat.cast_add, Nat.cast_one]

theorem valueXY_le (φ : IntegralCharacter) (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s) :
    valueXY φ r s ≤ (r : ℝ) + s - 1 :=
  (valueXY_le_outputLength φ r s).trans_eq (outputLength_cast r s hr hs)
theorem valueXZ_le (φ : IntegralCharacter) (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s) :
    valueXZ φ r s ≤ (r : ℝ) + s - 1 :=
  (valueXZ_le_outputLength φ r s).trans_eq (outputLength_cast r s hr hs)
theorem valueYZ_le (φ : IntegralCharacter) (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s) :
    valueYZ φ r s ≤ (r : ℝ) + s - 1 :=
  (valueYZ_le_outputLength φ r s).trans_eq (outputLength_cast r s hr hs)

theorem outputLength_mono {r r' s s' : ℕ} (hr : r ≤ r') (hs : s ≤ s') :
    outputLength r s ≤ outputLength r' s' := by
  unfold outputLength
  omega

theorem valueXY_mono (φ : IntegralCharacter) {r r' s s' : ℕ}
    (hr : r ≤ r') (hs : s ≤ s') : valueXY φ r s ≤ valueXY φ r' s' := by
  have heq : Tensor.pullback (Fin.castLE hr) (Fin.castLE hs)
      (Fin.castLE (outputLength_mono hr hs)) (CXY r' s') = CXY r s := by
    funext x y z
    simp [Tensor.pullback, CXY, convolution]
  rw [valueXY, ← heq]
  exact φ.value_pullback_le _ _ _ _

theorem valueXZ_mono (φ : IntegralCharacter) {r r' s s' : ℕ}
    (hr : r ≤ r') (hs : s ≤ s') : valueXZ φ r s ≤ valueXZ φ r' s' := by
  have heq : Tensor.pullback (Fin.castLE hr) (Fin.castLE (outputLength_mono hr hs))
      (Fin.castLE hs) (CXZ r' s') = CXZ r s := by
    funext x z y
    simp [Tensor.pullback, CXZ, CXY, convolution]
  rw [valueXZ, ← heq]
  exact φ.value_pullback_le _ _ _ _

theorem valueYZ_mono (φ : IntegralCharacter) {r r' s s' : ℕ}
    (hr : r ≤ r') (hs : s ≤ s') : valueYZ φ r s ≤ valueYZ φ r' s' := by
  have heq : Tensor.pullback (Fin.castLE (outputLength_mono hr hs)) (Fin.castLE hr)
      (Fin.castLE hs) (CYZ r' s') = CYZ r s := by
    funext z x y
    simp [Tensor.pullback, CYZ, CXY, convolution]
  rw [valueYZ, ← heq]
  exact φ.value_pullback_le _ _ _ _

theorem valueXY_mono_first (φ : IntegralCharacter) (r r' s : ℕ) (h : r ≤ r') :
    valueXY φ r s ≤ valueXY φ r' s := valueXY_mono φ h le_rfl
theorem valueXY_mono_second (φ : IntegralCharacter) (r s s' : ℕ) (h : s ≤ s') :
    valueXY φ r s ≤ valueXY φ r s' := valueXY_mono φ le_rfl h
theorem valueXZ_mono_first (φ : IntegralCharacter) (r r' s : ℕ) (h : r ≤ r') :
    valueXZ φ r s ≤ valueXZ φ r' s := valueXZ_mono φ h le_rfl
theorem valueXZ_mono_second (φ : IntegralCharacter) (r s s' : ℕ) (h : s ≤ s') :
    valueXZ φ r s ≤ valueXZ φ r s' := valueXZ_mono φ le_rfl h
theorem valueYZ_mono_first (φ : IntegralCharacter) (r r' s : ℕ) (h : r ≤ r') :
    valueYZ φ r s ≤ valueYZ φ r' s := valueYZ_mono φ h le_rfl
theorem valueYZ_mono_second (φ : IntegralCharacter) (r s s' : ℕ) (h : s ≤ s') :
    valueYZ φ r s ≤ valueYZ φ r s' := valueYZ_mono φ le_rfl h

/-- The six endpoint values identify the three dot exponents. -/
theorem valueXY_one_left (φ : IntegralCharacter) (s : ℕ) (hs : 1 ≤ s) :
    valueXY φ 1 s = (s : ℝ) ^ φ.pX := by
  have heq : CXY 1 s = Tensor.pullback (Equiv.equivPUnit (Fin 1)) (Equiv.refl (Fin s))
      (finCongr (by simp [outputLength])) (dotX s) := by
    funext x y z
    simp [Tensor.pullback, CXY, convolution, dotX, Fin.ext_iff]
  rw [valueXY, heq, φ.value_reindex]
  exact φ.value_dotX (by omega)

theorem valueXY_one_right (φ : IntegralCharacter) (r : ℕ) (hr : 1 ≤ r) :
    valueXY φ r 1 = (r : ℝ) ^ φ.pY := by
  have heq : CXY r 1 = Tensor.pullback (Equiv.refl (Fin r)) (Equiv.equivPUnit (Fin 1))
      (finCongr (by simp [outputLength])) (cyclic (cyclic (dotX r))) := by
    funext x y z
    simp [Tensor.pullback, CXY, convolution, cyclic, dotX, Fin.ext_iff, eq_comm]
  rw [valueXY, heq, φ.value_reindex]
  exact φ.value_cyclic_cyclic_dotX (by omega)

theorem valueXZ_one_left (φ : IntegralCharacter) (s : ℕ) (hs : 1 ≤ s) :
    valueXZ φ 1 s = (s : ℝ) ^ φ.pX := by
  have heq : CXZ 1 s = Tensor.pullback (Equiv.equivPUnit (Fin 1))
      (finCongr (by simp [outputLength])) (Equiv.refl (Fin s)) (dotX s) := by
    funext x z y
    simp [Tensor.pullback, CXZ, CXY, convolution, dotX, Fin.ext_iff, eq_comm]
  rw [valueXZ, heq, φ.value_reindex]
  exact φ.value_dotX (by omega)

theorem valueYZ_one_left (φ : IntegralCharacter) (s : ℕ) (hs : 1 ≤ s) :
    valueYZ φ 1 s = (s : ℝ) ^ φ.pY := by
  have heq : CYZ 1 s = Tensor.pullback (finCongr (by simp [outputLength]))
      (Equiv.equivPUnit (Fin 1)) (Equiv.refl (Fin s)) (cyclic (cyclic (dotX s))) := by
    funext z x y
    simp [Tensor.pullback, CYZ, CXY, convolution, cyclic, dotX, Fin.ext_iff, eq_comm]
  rw [valueYZ, heq, φ.value_reindex]
  exact φ.value_cyclic_cyclic_dotX (by omega)

theorem valueXZ_one_right (φ : IntegralCharacter) (r : ℕ) (hr : 1 ≤ r) :
    valueXZ φ r 1 = (r : ℝ) ^ φ.pZ := by
  have heq : CXZ r 1 = Tensor.pullback (Equiv.refl (Fin r))
      (finCongr (by simp [outputLength])) (Equiv.equivPUnit (Fin 1)) (cyclic (dotX r)) := by
    funext x z y
    simp [Tensor.pullback, CXZ, CXY, convolution, cyclic, dotX, Fin.ext_iff]
  rw [valueXZ, heq, φ.value_reindex]
  exact φ.value_cyclic_dotX (by omega)

theorem valueYZ_one_right (φ : IntegralCharacter) (r : ℕ) (hr : 1 ≤ r) :
    valueYZ φ r 1 = (r : ℝ) ^ φ.pZ := by
  have heq : CYZ r 1 = Tensor.pullback (finCongr (by simp [outputLength]))
      (Equiv.refl (Fin r)) (Equiv.equivPUnit (Fin 1)) (cyclic (dotX r)) := by
    funext z x y
    simp [Tensor.pullback, CYZ, CXY, convolution, cyclic, dotX, Fin.ext_iff, eq_comm]
  rw [valueYZ, heq, φ.value_reindex]
  exact φ.value_cyclic_dotX (by omega)

#print axioms valueXY_le
#print axioms valueXZ_le
#print axioms valueYZ_le
#print axioms valueXY_mono
#print axioms valueXY_one_left
#print axioms valueYZ_one_right

end
end Matmul.ConvolutionCharacter
