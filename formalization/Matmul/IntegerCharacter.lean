import Matmul.IntegralSpectrumDuality
import Matmul.IntegerCharacterExtension
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic

/-!
# Actual integral characters on zero-one tensors and dot products

The valuation below is the given monotone semiring homomorphism on actual
unit-admitting integral tensor classes.  No new character axioms are assumed.
In particular the dot exponent is derived from integral restrictions and
products, including the empty dot tensor.
-/

namespace Matmul.IntegerCharacter

open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
open Matmul.IntegralSpectrum
open scoped BigOperators

noncomputable section

abbrev ZeroOne {X Y Z : Type*} (T : Tensor ℤ X Y Z) : Prop :=
  ∀ x y z, T x y z = 0 ∨ T x y z = 1

namespace ZeroOne

theorem zero {X Y Z : Type*} : ZeroOne (0 : Tensor ℤ X Y Z) := by
  intro x y z
  exact Or.inl rfl

theorem product {X Y Z U V W : Type*} {T : Tensor ℤ X Y Z} {S : Tensor ℤ U V W}
    (hT : ZeroOne T) (hS : ZeroOne S) : ZeroOne (Tensor.product T S) := by
  intro x y z
  rcases hT x.1 y.1 z.1 with ht | ht <;>
    rcases hS x.2 y.2 z.2 with hs | hs <;>
    simp [Tensor.product, ht, hs]

theorem pullback {X Y Z U V W : Type*} {T : Tensor ℤ X Y Z}
    (hT : ZeroOne T) (fx : U → X) (fy : V → Y) (fz : W → Z) :
    ZeroOne (Tensor.pullback fx fy fz T) :=
  fun x y z => hT (fx x) (fy y) (fz z)

theorem directSum {ι X Y Z : Type*} [DecidableEq ι]
    {T : ι → Tensor ℤ X Y Z} (hT : ∀ i, ZeroOne (T i)) :
    ZeroOne (Tensor.directSum T) := by
  intro x y z
  unfold Tensor.directSum
  split
  · exact hT x.1 x.2 y.2 z.2
  · exact Or.inl rfl

theorem finset_prod {ι : Type*} (s : Finset ι) (f : ι → ℤ)
    (hf : ∀ i ∈ s, f i = 0 ∨ f i = 1) : (∏ i ∈ s, f i) = 0 ∨ (∏ i ∈ s, f i) = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hf' : ∀ j ∈ s, f j = 0 ∨ f j = 1 := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    rcases hf i (Finset.mem_insert_self i s) with h0 | h1
    · simp [Finset.prod_insert hi, h0]
    · simpa [Finset.prod_insert hi, h1] using ih hf'

theorem power {X Y Z : Type*} {T : Tensor ℤ X Y Z} (hT : ZeroOne T) (n : ℕ) :
    ZeroOne (Tensor.power T n) := by
  intro x y z
  exact finset_prod Finset.univ (fun i => T (x i) (y i) (z i)) (fun i _ => hT _ _ _)

end ZeroOne

def value (χ : Character) {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor ℤ X Y Z) (hT : ZeroOne T) : ℝ :=
  χ (UnitTensorClass.ofZeroOneTensor T hT)

theorem value_nonneg (χ : Character) (hχ : Monotone χ)
    {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor ℤ X Y Z) (hT : ZeroOne T) : 0 ≤ value χ T hT := by
  simpa [value] using hχ (UnitTensorClass.zero_le (UnitTensorClass.ofZeroOneTensor T hT))

theorem value_zero (χ : Character) {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] (h : ZeroOne (0 : Tensor ℤ X Y Z)) :
    value χ 0 h = 0 := by
  have heq : UnitTensorClass.ofZeroOneTensor (0 : Tensor ℤ X Y Z) h = 0 := by
    apply Subtype.ext
    exact classOf_zero
  simp [value, heq]

theorem value_mono (χ : Character) (hχ : Monotone χ)
    {X Y Z U V W : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    {T : Tensor ℤ X Y Z} {S : Tensor ℤ U V W}
    (hT : ZeroOne T) (hS : ZeroOne S) (h : IsRestriction T S) :
    value χ T hT ≤ value χ S hS :=
  hχ ((classOf_le_iff T S).mpr h)

theorem value_reindex (χ : Character)
    {X Y Z U V W : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor ℤ X Y Z) (hT : ZeroOne T)
    (ex : U ≃ X) (ey : V ≃ Y) (ez : W ≃ Z) :
    value χ (Tensor.pullback ex ey ez T) (hT.pullback ex ey ez) = value χ T hT := by
  unfold value
  apply congrArg χ
  apply Subtype.ext
  exact classOf_reindex T ex ey ez

theorem value_product (χ : Character)
    {X Y Z U V W : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor ℤ X Y Z) (S : Tensor ℤ U V W) (hT : ZeroOne T) (hS : ZeroOne S) :
    value χ (Tensor.product T S) (hT.product hS) = value χ T hT * value χ S hS := by
  unfold value
  rw [UnitTensorClass.ofZeroOneTensor_product T S hT hS, map_mul]

theorem value_directSum (χ : Character)
    {ι X Y Z : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype X] [Fintype Y] [Fintype Z]
    (T : ι → Tensor ℤ X Y Z) (hT : ∀ i, ZeroOne (T i)) :
    value χ (Tensor.directSum T) (ZeroOne.directSum hT) = ∑ i, value χ (T i) (hT i) := by
  unfold value
  rw [UnitTensorClass.ofZeroOneTensor_directSum T hT, map_sum]

theorem value_power (χ : Character)
    {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor ℤ X Y Z) (hT : ZeroOne T) (n : ℕ) :
    value χ (Tensor.power T n) (hT.power n) = value χ T hT ^ n := by
  unfold value
  rw [UnitTensorClass.ofZeroOneTensor_power T n hT, map_pow]

theorem one_le_value (χ : Character) (hχ : Monotone χ)
    {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    {T : Tensor ℤ X Y Z} (hT : ZeroOne T) (hTne : T ≠ 0) : 1 ≤ value χ T hT := by
  apply one_le_character_of_ne_zero χ hχ
  intro heq
  apply hTne
  apply (classOf_eq_zero_iff T).mp
  exact congrArg Subtype.val heq

theorem value_pos (χ : Character) (hχ : Monotone χ)
    {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    {T : Tensor ℤ X Y Z} (hT : ZeroOne T) (hTne : T ≠ 0) : 0 < value χ T hT :=
  zero_lt_one.trans_le (one_le_value χ hχ hT hTne)

theorem value_le_rankAtMost (χ : Character) (hχ : Monotone χ)
    {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    {T : Tensor ℤ X Y Z} (hT : ZeroOne T) {r : ℕ} (hr : Tensor.RankAtMost T r) :
    value χ T hT ≤ (r : ℝ) := by
  have h := character_le_rank χ hχ (UnitTensorClass.ofZeroOneTensor T hT)
  have hrank : UnitTensorClass.rank (UnitTensorClass.ofZeroOneTensor T hT) = exactRank T :=
    rank_classOf T
  rw [hrank] at h
  exact h.trans (by exact_mod_cast exactRank_le hr)

/-- The dot tensor with a one-dimensional first leg. -/
def dotX (n : ℕ) : Tensor ℤ PUnit.{1} (Fin n) (Fin n) :=
  fun _ y z => if y = z then 1 else 0

theorem dotX_zeroOne (n : ℕ) : ZeroOne (dotX n) := by
  intro x y z
  unfold dotX
  split <;> simp

def dotClass (n : ℕ) : UnitTensorClass ℤ :=
  UnitTensorClass.ofZeroOneTensor (dotX n) (dotX_zeroOne n)

theorem dotX_ne_zero {n : ℕ} (hn : 0 < n) : dotX n ≠ 0 := by
  intro h
  have hv := congrFun (congrFun (congrFun h PUnit.unit) ⟨0, hn⟩) ⟨0, hn⟩
  simp [dotX] at hv

theorem dotX_rank (n : ℕ) : Tensor.RankAtMost (dotX n) n := by
  let a : Fin n → PUnit.{1} → ℤ := fun _ _ => 1
  let b : Fin n → Fin n → ℤ := fun i j => if j = i then 1 else 0
  refine ⟨a, b, b, ?_⟩
  funext x y z
  simp [dotX, Tensor.rankOne, a, b, mul_ite]

theorem dotClass_zero : dotClass 0 = 0 := by
  apply Subtype.ext
  apply (classOf_eq_zero_iff _).mpr
  funext x y
  exact Fin.elim0 y

theorem dotClass_one : dotClass 1 = 1 := by
  apply Subtype.ext
  change classOf (dotX 1) = classOf (fun (_ _ _ : PUnit.{1}) => (1 : ℤ))
  apply classOf_eq_of_reindex (Equiv.refl PUnit.{1})
    (Equiv.equivPUnit (Fin 1)) (Equiv.equivPUnit (Fin 1))
  funext x y z
  simp [Tensor.pullback, dotX, Subsingleton.elim y z]

theorem dotClass_mono {m n : ℕ} (hmn : m ≤ n) : dotClass m ≤ dotClass n := by
  have heq : Tensor.pullback id (Fin.castLE hmn) (Fin.castLE hmn) (dotX n) = dotX m := by
    funext x y z
    simp [Tensor.pullback, dotX]
  exact (classOf_le_iff _ _).mpr (heq ▸ IsRestriction.pullback (dotX n) _ _ _)

theorem dotClass_mul (m n : ℕ) : dotClass (m * n) = dotClass m * dotClass n := by
  apply Subtype.ext
  change classOf (dotX (m * n)) = classOf (dotX m) * classOf (dotX n)
  rw [← classOf_product]
  apply classOf_eq_of_reindex (Equiv.prodUnique PUnit.{1} PUnit.{1}).symm
    finProdFinEquiv.symm finProdFinEquiv.symm
  funext x y z
  simp only [Tensor.pullback, Tensor.product, dotX, ite_zero_mul_ite_zero,
    one_mul, ← Prod.ext_iff, Equiv.apply_eq_iff_eq]

theorem value_dotClass_pos (χ : Character) (hχ : Monotone χ)
    {n : ℕ} (hn : 0 < n) : 0 < χ (dotClass n) :=
  value_pos χ hχ (dotX_zeroOne n) (dotX_ne_zero hn)

theorem value_dotClass_le (χ : Character) (hχ : Monotone χ) (n : ℕ) :
    χ (dotClass n) ≤ (n : ℝ) :=
  value_le_rankAtMost χ hχ (dotX_zeroOne n) (dotX_rank n)

/- The following scalar classification proof is reused from OpenAI's
Growth/MultiplicativePower, whose hypotheses are purely ordered scalar facts. -/

/-- Multiplicativity and positivity determine the value at one. -/
theorem positiveMultiplicative_one
    {f : ℕ → ℝ} (hpos : ∀ n, 0 < n → 0 < f n)
    (hmul : ∀ m n, 0 < m → 0 < n → f (m * n) = f m * f n) :
    f 1 = 1 := by
  have hm := hmul 1 1 (by omega) (by omega)
  have hp := hpos 1 (by omega)
  norm_num at hm
  nlinarith

/-- A positive multiplicative function preserves natural powers. -/
theorem positiveMultiplicative_pow
    {f : ℕ → ℝ} (hpos : ∀ n, 0 < n → 0 < f n)
    (hmul : ∀ m n, 0 < m → 0 < n → f (m * n) = f m * f n)
    {n : ℕ} (hn : 0 < n) (k : ℕ) : f (n ^ k) = f n ^ k := by
  induction k with
  | zero => simpa using positiveMultiplicative_one hpos hmul
  | succ k ih =>
      rw [pow_succ, hmul (n ^ k) n (pow_pos hn k) hn, ih, pow_succ]

/-- Monotonicity transfers comparisons of natural powers to the values. -/
theorem positiveMultiplicative_pow_le_pow
    {f : ℕ → ℝ} (hpos : ∀ n, 0 < n → 0 < f n)
    (hmul : ∀ m n, 0 < m → 0 < n → f (m * n) = f m * f n)
    (hmono : MonotoneOn f (Set.Ioi 0))
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) {j k : ℕ}
    (h : m ^ j ≤ n ^ k) : f m ^ j ≤ f n ^ k := by
  rw [← positiveMultiplicative_pow hpos hmul hm,
    ← positiveMultiplicative_pow hpos hmul hn]
  exact hmono (pow_pos hm j) (pow_pos hn k) h

/-- The same comparison after taking logarithms. -/
theorem positiveMultiplicative_log_pow_le
    {f : ℕ → ℝ} (hpos : ∀ n, 0 < n → 0 < f n)
    (hmul : ∀ m n, 0 < m → 0 < n → f (m * n) = f m * f n)
    (hmono : MonotoneOn f (Set.Ioi 0))
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) {j k : ℕ}
    (h : m ^ j ≤ n ^ k) :
    (j : ℝ) * Real.log (f m) ≤ (k : ℝ) * Real.log (f n) := by
  have hv := positiveMultiplicative_pow_le_pow hpos hmul hmono hm hn h
  simpa only [Real.log_pow] using
    Real.log_le_log (pow_pos (hpos m hm) j) hv

/-- Bounds from neighboring powers of two have a fixed logarithmic error,
independent of the exponent `k`. -/
theorem positiveMultiplicative_log_error_bounds
    {f : ℕ → ℝ} (hpos : ∀ n, 0 < n → 0 < f n)
    (hmul : ∀ m n, 0 < m → 0 < n → f (m * n) = f m * f n)
    (hmono : MonotoneOn f (Set.Ioi 0))
    {n : ℕ} (hn : 0 < n) (k : ℕ) :
    (k : ℝ) * (Real.log (f n) * Real.log 2 -
      Real.log (n : ℝ) * Real.log (f 2)) ≤ Real.log (f 2) * Real.log 2 ∧
    (k : ℝ) * (Real.log (n : ℝ) * Real.log (f 2) -
      Real.log (f n) * Real.log 2) ≤ Real.log (f 2) * Real.log 2 := by
  have hf2 : 0 ≤ Real.log (f 2) := by
    apply Real.log_nonneg
    have hm := hmono (show (1 : ℕ) ∈ Set.Ioi 0 by norm_num)
      (show (2 : ℕ) ∈ Set.Ioi 0 by norm_num) (by norm_num)
    rwa [positiveMultiplicative_one hpos hmul] at hm
  have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  obtain ⟨m, hlow, hupp⟩ :=
    exists_nat_pow_near (show 1 ≤ n ^ k from Nat.one_le_iff_ne_zero.mpr (by positivity))
      (show 1 < (2 : ℕ) by omega)
  have hflow := positiveMultiplicative_log_pow_le hpos hmul hmono
    (show 0 < (2 : ℕ) by omega) hn hlow
  have hfupp := positiveMultiplicative_log_pow_le hpos hmul hmono hn
    (show 0 < (2 : ℕ) by omega) hupp.le
  have hlow' : (2 : ℝ) ^ m ≤ (n : ℝ) ^ k := by exact_mod_cast hlow
  have hupp' : (n : ℝ) ^ k ≤ (2 : ℝ) ^ (m + 1) := by exact_mod_cast hupp.le
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  have hnlow := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 2) m) hlow'
  have hnupp := Real.log_le_log (pow_pos hnp k) hupp'
  simp only [Real.log_pow, Nat.cast_add, Nat.cast_one] at hflow hfupp hnlow hnupp
  have h₁ := mul_le_mul_of_nonneg_right hfupp hlog2
  have h₂ := mul_le_mul_of_nonneg_right hnlow hf2
  have h₃ := mul_le_mul_of_nonneg_right hnupp hf2
  have h₄ := mul_le_mul_of_nonneg_right hflow hlog2
  constructor <;> nlinarith

/-- If every natural multiple of both differences has a common upper bound,
the two real numbers coincide. -/
theorem eq_of_nat_mul_sub_bounded {x y C : ℝ}
    (hxy : ∀ k : ℕ, (k : ℝ) * (x - y) ≤ C)
    (hyx : ∀ k : ℕ, (k : ℝ) * (y - x) ≤ C) : x = y := by
  apply le_antisymm
  · by_contra h
    have hd : 0 < x - y := sub_pos.mpr (lt_of_not_ge h)
    obtain ⟨k, hk⟩ := exists_nat_gt (C / (x - y))
    have hk' : C < (k : ℝ) * (x - y) := (div_lt_iff₀ hd).mp hk
    exact (not_lt_of_ge (hxy k)) hk'
  · by_contra h
    have hd : 0 < y - x := sub_pos.mpr (lt_of_not_ge h)
    obtain ⟨k, hk⟩ := exists_nat_gt (C / (y - x))
    have hk' : C < (k : ℝ) * (y - x) := (div_lt_iff₀ hd).mp hk
    exact (not_lt_of_ge (hyx k)) hk'

/-- The logarithmic exponent is the same at every positive natural number. -/
theorem positiveMultiplicative_log_eq
    {f : ℕ → ℝ} (hpos : ∀ n, 0 < n → 0 < f n)
    (hmul : ∀ m n, 0 < m → 0 < n → f (m * n) = f m * f n)
    (hmono : MonotoneOn f (Set.Ioi 0))
    {n : ℕ} (hn : 0 < n) :
    Real.log (f n) = Real.log (n : ℝ) * (Real.log (f 2) / Real.log 2) := by
  have heq : Real.log (f n) * Real.log 2 =
      Real.log (n : ℝ) * Real.log (f 2) :=
    eq_of_nat_mul_sub_bounded
      (fun k => (positiveMultiplicative_log_error_bounds hpos hmul hmono hn k).1)
      (fun k => (positiveMultiplicative_log_error_bounds hpos hmul hmono hn k).2)
  calc
    Real.log (f n) = (Real.log (n : ℝ) * Real.log (f 2)) / Real.log 2 :=
      (eq_div_iff (Real.log_pos (show (1 : ℝ) < 2 by norm_num)).ne').2 heq
    _ = Real.log (n : ℝ) * (Real.log (f 2) / Real.log 2) := by ring

/-- The explicit exponent in the classification of positive monotone
multiplicative functions on the positive natural numbers. -/
theorem positiveMultiplicative_eq_rpow
    {f : ℕ → ℝ} (hpos : ∀ n, 0 < n → 0 < f n)
    (hmul : ∀ m n, 0 < m → 0 < n → f (m * n) = f m * f n)
    (hmono : MonotoneOn f (Set.Ioi 0))
    {n : ℕ} (hn : 0 < n) :
    f n = (n : ℝ) ^ (Real.log (f 2) / Real.log 2) := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.rpow_def_of_pos hnp, ← positiveMultiplicative_log_eq hpos hmul hmono hn,
    Real.exp_log (hpos n hn)]

/-- Every positive monotone multiplicative function on the positive natural
numbers is a nonnegative real power, as used in Section 3.1. -/
theorem positiveMultiplicative_is_rpow
    {f : ℕ → ℝ} (hpos : ∀ n, 0 < n → 0 < f n)
    (hmul : ∀ m n, 0 < m → 0 < n → f (m * n) = f m * f n)
    (hmono : MonotoneOn f (Set.Ioi 0)) :
    ∃ p : ℝ, 0 ≤ p ∧ ∀ n : ℕ, 0 < n → f n = (n : ℝ) ^ p := by
  refine ⟨Real.log (f 2) / Real.log 2, ?_, fun n hn =>
    positiveMultiplicative_eq_rpow hpos hmul hmono hn⟩
  apply div_nonneg _ (Real.log_nonneg (by norm_num))
  apply Real.log_nonneg
  have hm := hmono (show (1 : ℕ) ∈ Set.Ioi 0 by norm_num)
    (show (2 : ℕ) ∈ Set.Ioi 0 by norm_num) (by norm_num)
  rwa [positiveMultiplicative_one hpos hmul] at hm


def pX (χ : Character) : ℝ := Real.log (χ (dotClass 2)) / Real.log 2

theorem pX_nonneg (χ : Character) (hχ : Monotone χ) : 0 ≤ pX χ := by
  apply div_nonneg _ (Real.log_nonneg (by norm_num))
  exact Real.log_nonneg (one_le_value χ hχ (dotX_zeroOne 2) (dotX_ne_zero (by norm_num)))

theorem pX_le_one (χ : Character) (hχ : Monotone χ) : pX χ ≤ 1 := by
  apply (div_le_one (Real.log_pos (by norm_num))).2
  exact Real.log_le_log (value_dotClass_pos χ hχ (by norm_num)) (value_dotClass_le χ hχ 2)

theorem value_dotClass (χ : Character) (hχ : Monotone χ) {n : ℕ} (hn : 0 < n) :
    χ (dotClass n) = (n : ℝ) ^ pX χ := by
  exact positiveMultiplicative_eq_rpow
    (fun n hn => value_dotClass_pos χ hχ hn)
    (fun m n _ _ => by rw [dotClass_mul, map_mul])
    (fun m n _ _ hmn => hχ (dotClass_mono hmn)) hn

theorem value_dotX (χ : Character) (hχ : Monotone χ) {n : ℕ} (hn : 0 < n) :
    value χ (dotX n) (dotX_zeroOne n) = (n : ℝ) ^ pX χ := value_dotClass χ hχ hn

#print axioms value_dotClass
#print axioms pX_le_one
#print axioms dotClass_mul

end
end Matmul.IntegerCharacter

namespace Matmul.IntegralCharacter

open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open Matmul.IntegerCharacter
open scoped BigOperators

noncomputable section

theorem value_dotX_pos (φ : IntegralCharacter) {n : ℕ} (hn : 0 < n) :
    0 < φ.value (dotX n) := by
  exact φ.value_pos_of_coefficient_one (dotX n) PUnit.unit ⟨0, hn⟩ ⟨0, hn⟩ (by simp [dotX])

theorem value_dotX_le (φ : IntegralCharacter) (n : ℕ) :
    φ.value (dotX n) ≤ (n : ℝ) := φ.value_le_rank (dotX_rank n)

theorem value_dotX_mono (φ : IntegralCharacter) {m n : ℕ} (hmn : m ≤ n) :
    φ.value (dotX m) ≤ φ.value (dotX n) := by
  have heq : Tensor.pullback id (Fin.castLE hmn) (Fin.castLE hmn) (dotX n) = dotX m := by
    funext x y z
    simp [Tensor.pullback, dotX]
  rw [← heq]
  exact φ.value_pullback_le _ _ _ _

theorem value_dotX_mul (φ : IntegralCharacter) (m n : ℕ) :
    φ.value (dotX (m * n)) = φ.value (dotX m) * φ.value (dotX n) := by
  have heq : Tensor.pullback (Equiv.prodUnique PUnit.{1} PUnit.{1}).symm
      finProdFinEquiv.symm finProdFinEquiv.symm
      (Tensor.product (dotX m) (dotX n)) = dotX (m * n) := by
    funext x y z
    simp only [Tensor.pullback, Tensor.product, dotX, ite_zero_mul_ite_zero,
      one_mul, ← Prod.ext_iff, Equiv.apply_eq_iff_eq]
  rw [← heq, φ.value_reindex, φ.map_product]

def pX (φ : IntegralCharacter) : ℝ := Real.log (φ.value (dotX 2)) / Real.log 2

theorem pX_nonneg (φ : IntegralCharacter) : 0 ≤ φ.pX := by
  apply div_nonneg _ (Real.log_nonneg (by norm_num))
  apply Real.log_nonneg
  exact φ.one_le_value_of_coefficient_one (dotX 2) PUnit.unit 0 0 (by simp [dotX])

theorem pX_le_one (φ : IntegralCharacter) : φ.pX ≤ 1 := by
  apply (div_le_one (Real.log_pos (by norm_num))).2
  exact Real.log_le_log (φ.value_dotX_pos (by norm_num)) (φ.value_dotX_le 2)

theorem value_dotX (φ : IntegralCharacter) {n : ℕ} (hn : 0 < n) :
    φ.value (dotX n) = (n : ℝ) ^ φ.pX :=
  positiveMultiplicative_eq_rpow
    (fun _ hn => φ.value_dotX_pos hn)
    (fun m n _ _ => φ.value_dotX_mul m n)
    (fun _ _ _ _ hmn => φ.value_dotX_mono hmn) hn

theorem pX_ofUnitTensorClassHom (χ : Matmul.IntegralSpectrum.Character) (hχ : Monotone χ) :
    (ofUnitTensorClassHom χ hχ).pX = IntegerCharacter.pX χ := by
  unfold IntegralCharacter.pX IntegerCharacter.pX
  rw [ofUnitTensorClassHom_value_ofZeroOneTensor χ hχ (dotX 2) (dotX_zeroOne 2)]
  rfl

def cyclic {X Y Z : Type*} (T : Tensor ℤ X Y Z) : Tensor ℤ Y Z X :=
  fun y z x => T x y z

def cyclicCharacter (φ : IntegralCharacter) : IntegralCharacter where
  value T := φ.value (cyclic T)
  nonneg T := φ.nonneg _
  map_zero := φ.map_zero
  map_one := φ.map_one
  map_sumTensor T S := by
    have heq : cyclic (sumTensor T S) = sumTensor (cyclic T) (cyclic S) := by
      funext y z x
      cases x <;> cases y <;> cases z <;> rfl
    rw [heq, φ.map_sumTensor]
  map_directSum T := by
    have heq : cyclic (Tensor.directSum T) = Tensor.directSum (fun i => cyclic (T i)) := by
      funext y z x
      by_cases h : y.1 = z.1 ∧ y.1 = x.1
      · simp [cyclic, Tensor.directSum, h.1, ← h.2]
      · have h' : ¬ (x.1 = y.1 ∧ x.1 = z.1) := by
          rintro ⟨hxy, hxz⟩
          exact h ⟨hxy.symm.trans hxz, hxy.symm⟩
        simp [cyclic, Tensor.directSum, h, h']
    rw [heq, φ.map_directSum]
  map_product T S := φ.map_product (cyclic T) (cyclic S)
  monotone T A B C := by
    have heq : cyclic (Tensor.restrict A B C T) =
        Tensor.restrict B C A (cyclic T) := by
      funext y z x
      simp only [cyclic, Tensor.restrict]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [heq]
    exact φ.monotone _ _ _ _

def pZ (φ : IntegralCharacter) : ℝ := φ.cyclicCharacter.pX
def pY (φ : IntegralCharacter) : ℝ := φ.cyclicCharacter.cyclicCharacter.pX

theorem pY_nonneg (φ : IntegralCharacter) : 0 ≤ φ.pY :=
  φ.cyclicCharacter.cyclicCharacter.pX_nonneg
theorem pY_le_one (φ : IntegralCharacter) : φ.pY ≤ 1 :=
  φ.cyclicCharacter.cyclicCharacter.pX_le_one
theorem pZ_nonneg (φ : IntegralCharacter) : 0 ≤ φ.pZ := φ.cyclicCharacter.pX_nonneg
theorem pZ_le_one (φ : IntegralCharacter) : φ.pZ ≤ 1 := φ.cyclicCharacter.pX_le_one

theorem value_cyclic_dotX (φ : IntegralCharacter) {n : ℕ} (hn : 0 < n) :
    φ.value (cyclic (dotX n)) = (n : ℝ) ^ φ.pZ := φ.cyclicCharacter.value_dotX hn

theorem value_cyclic_cyclic_dotX (φ : IntegralCharacter) {n : ℕ} (hn : 0 < n) :
    φ.value (cyclic (cyclic (dotX n))) = (n : ℝ) ^ φ.pY :=
  φ.cyclicCharacter.cyclicCharacter.value_dotX hn

#print axioms IntegralCharacter.value_dotX
#print axioms IntegralCharacter.pX_ofUnitTensorClassHom
#print axioms IntegralCharacter.cyclicCharacter

end
end Matmul.IntegralCharacter
