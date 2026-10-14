import Matmul.IntegerSemiring
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Integral scalar tensors and rank

The diagonal and restriction identities work over every commutative semiring.
The rank lower bound and the reflection of natural-number order below use ℤ,
proved by mapping a decomposition to ℚ and taking an identity flattening.
-/

namespace OAI

variable {K : Type} [CommSemiring K]

/-!
# Natural numbers and rank in the tensor semiring

The natural number `r` is the class of the diagonal scalar tensor with `r`
terms.  Consequently, comparison with `r` in the restriction order is exactly
the existence of a rank decomposition with `r` terms.
-/

noncomputable section

open MatrixMultiplication.Foundation
open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation

variable (K) in
/-- The diagonal tensor for `r` independent scalar multiplications. -/
def scalarTensor (r : ℕ) : Tensor K (Fin r) (Fin r) (Fin r) :=
  fun i j k => if i = j ∧ i = k then 1 else 0

/-- Splitting the diagonal index set splits its scalar tensor into two blocks. -/
theorem scalarTensor_add_reindex (m n : ℕ) :
    Tensor.pullback (finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n))
      finSumFinEquiv finSumFinEquiv (scalarTensor K (m + n)) =
      sumTensor (scalarTensor K m) (scalarTensor K n) := by
  funext x y z
  simp only [Tensor.pullback, scalarTensor,
    (finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n)).injective.eq_iff]
  cases x <;> cases y <;> cases z <;> simp [sumTensor, scalarTensor]

/-- A diagonal scalar tensor has its evident decomposition into simple terms. -/
theorem scalarTensor_rankAtMost (r : ℕ) : Tensor.RankAtMost (scalarTensor K r) r := by
  classical
  refine ⟨(fun i x => if x = i then 1 else 0),
    (fun i y => if y = i then 1 else 0), (fun i z => if z = i then 1 else 0), ?_⟩
  funext x y z
  simp [scalarTensor, Tensor.rankOne, mul_ite, ite_and]
  split_ifs <;> simp_all

/-- A field flattening gives the lower bound after mapping an integral
rank decomposition to the rationals. -/
private theorem card_le_of_identity_rat {X Y Z : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {T : Tensor ℚ X Y Z} {r : ℕ} (hT : Tensor.RankAtMost T r)
    (x : ι → X) (y : ι → Y) (z : ι → Z)
    (hidentity : ∀ i j, T (x i) (y i) (z j) = if i = j then 1 else 0) :
    Fintype.card ι ≤ r := by
  rcases hT with ⟨a, b, c, heq⟩
  let L : Matrix ι (Fin r) ℚ := fun i q => a q (x i) * b q (y i)
  let R : Matrix (Fin r) ι ℚ := fun q j => c q (z j)
  have hmul : L * R = (1 : Matrix ι ι ℚ) := by
    funext i j
    change (∑ q, (a q (x i) * b q (y i)) * c q (z j)) = if i = j then 1 else 0
    calc
      (∑ q, (a q (x i) * b q (y i)) * c q (z j)) = T (x i) (y i) (z j) :=
        (congrFun (congrFun (congrFun heq (x i)) (y i)) (z j)).symm
      _ = _ := hidentity i j
  have hle : (1 : Matrix ι ι ℚ).rank ≤ r := by
    rw [← hmul]
    exact (Matrix.rank_mul_le_left L R).trans (by
      simpa only [Fintype.card_fin] using Matrix.rank_le_card_width L)
  simpa only [Matrix.rank_one] using hle

/-- An identity flattening bounds the number of terms in an integral tensor
decomposition, by mapping the decomposition to the rationals. -/
theorem integer_card_le_of_identity {X Y Z : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {T : Tensor ℤ X Y Z} {r : ℕ} (hT : Tensor.RankAtMost T r)
    (x : ι → X) (y : ι → Y) (z : ι → Z)
    (hidentity : ∀ i j, T (x i) (y i) (z j) = if i = j then 1 else 0) :
    Fintype.card ι ≤ r := by
  apply card_le_of_identity_rat (hT.map (Int.castRingHom ℚ)) x y z
  intro i j
  rw [hidentity]
  split_ifs <;> simp

/-- The output flattening of a nonempty rectangular matrix product is an
identity matrix of dimension `c * a`. -/
theorem matrixTensor_rank_lower_output {a b c r : ℕ} (hb : 0 < b)
    (h : Tensor.RankAtMost (Matmul.IntegerBilinear.matrixTensor a b c) r) :
    c * a ≤ r := by
  let j₀ : Fin b := ⟨0, hb⟩
  have hlower := integer_card_le_of_identity h
    (fun i : Fin c × Fin a => (i.2, j₀))
    (fun i : Fin c × Fin a => (j₀, i.1)) id (by
      intro i j
      simp only [Matmul.IntegerBilinear.matrixTensor]
      split_ifs <;> simp_all [Prod.ext_iff])
  simpa only [Fintype.card_prod, Fintype.card_fin] using hlower

/-- Cyclically rotating a rank decomposition preserves its number of terms. -/
private theorem rankAtMost_cycle {X Y Z : Type*} {T : Tensor K X Y Z} {r : ℕ}
    (h : Tensor.RankAtMost T r) :
    Tensor.RankAtMost (fun y z x => T x y z) r := by
  rcases h with ⟨a, b, c, heq⟩
  refine ⟨b, c, a, ?_⟩
  funext y z x
  rw [heq]
  apply Finset.sum_congr rfl
  intro i hi
  dsimp [Tensor.rankOne]
  ring

/-- Integral matrix multiplication rank bounds rotate with the three legs. -/
theorem matrixTensor_rankAtMost_cycle {a b c r : ℕ}
    (h : Tensor.RankAtMost (Matmul.IntegerBilinear.matrixTensor a b c) r) :
    Tensor.RankAtMost (Matmul.IntegerBilinear.matrixTensor b c a) r := by
  convert rankAtMost_cycle h using 1
  funext x y z
  simp only [Matmul.IntegerBilinear.matrixTensor]
  split_ifs <;> simp_all

/-- The first-input flattening has dimension `a * b`. -/
theorem matrixTensor_rank_lower_left {a b c r : ℕ} (hc : 0 < c)
    (h : Tensor.RankAtMost (Matmul.IntegerBilinear.matrixTensor a b c) r) :
    a * b ≤ r :=
  matrixTensor_rank_lower_output hc (matrixTensor_rankAtMost_cycle h)

/-- The second-input flattening has dimension `b * c`. -/
theorem matrixTensor_rank_lower_right {a b c r : ℕ} (ha : 0 < a)
    (h : Tensor.RankAtMost (Matmul.IntegerBilinear.matrixTensor a b c) r) :
    b * c ≤ r :=
  matrixTensor_rank_lower_output ha
    (matrixTensor_rankAtMost_cycle (matrixTensor_rankAtMost_cycle h))

/-- Every integral matrix multiplication rank decomposition dominates all
three coordinate dimensions when the matrix dimensions are positive. -/
theorem matrixTensor_rank_lower {a b c r : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : Tensor.RankAtMost (Matmul.IntegerBilinear.matrixTensor a b c) r) :
    max (max (a * b) (b * c)) (c * a) ≤ r :=
  max_le (max_le (matrixTensor_rank_lower_left hc h)
    (matrixTensor_rank_lower_right ha h)) (matrixTensor_rank_lower_output hb h)

/-- Integral diagonal rank is exactly its number of terms. The lower bound is
proved over the rationals and transported from an actual integral decomposition. -/
@[simp] theorem exactRank_scalarTensor (r : ℕ) : exactRank (scalarTensor ℤ r) = r := by
  apply le_antisymm (exactRank_le (scalarTensor_rankAtMost r))
  have h := integer_card_le_of_identity (exactRank_spec (scalarTensor ℤ r)) id id id
    (by intro i j; simp [scalarTensor])
  simpa only [Fintype.card_fin] using h

namespace TensorSemiring

/-- Addition of the diagonal index sets is semiring addition. -/
theorem classOf_scalarTensor_add (m n : ℕ) :
    classOf (scalarTensor K (m + n)) =
      classOf (scalarTensor K m) + classOf (scalarTensor K n) := by
  have h := classOf_eq_of_reindex _ _ _ (scalarTensor_add_reindex (K := K) m n)
  exact h.symm.trans (classOf_sum _ _)

@[simp] theorem classOf_scalarTensor_zero :
    classOf (scalarTensor K 0) = (0 : (TensorClass K)) := by
  have h : scalarTensor K 0 = 0 := by
    funext x
    exact Fin.elim0 x
  rw [h, classOf_zero]

@[simp] theorem classOf_scalarTensor_one :
    classOf (scalarTensor K 1) = (1 : (TensorClass K)) := by
  change classOf (scalarTensor K 1) = classOf (fun (_ _ _ : PUnit.{1}) => (1 : K))
  apply classOf_eq_of_reindex (Equiv.equivPUnit (Fin 1))
    (Equiv.equivPUnit (Fin 1)) (Equiv.equivPUnit (Fin 1))
  funext x y z
  simp [Tensor.pullback, scalarTensor, Subsingleton.elim x y, Subsingleton.elim y z]

/-- Natural numbers in the quotient semiring have their intended tensor meaning. -/
@[simp] theorem classOf_scalarTensor (r : ℕ) :
    classOf (scalarTensor K r) = (r : (TensorClass K)) := by
  induction r with
  | zero => exact classOf_scalarTensor_zero
  | succ r ih =>
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_succ,
        classOf_scalarTensor_one, ih] using
        classOf_scalarTensor_add (K := K) r 1

/-- Exact rank decompositions are precisely restrictions of diagonal tensors. -/
theorem rankAtMost_iff_isRestriction_scalarTensor
    {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) (r : ℕ) :
    Tensor.RankAtMost T r ↔ IsRestriction T (scalarTensor K r) := by
  constructor
  · rintro ⟨a, b, c, h⟩
    refine ⟨(fun x i => a i x), (fun y i => b i y), (fun z i => c i z), ?_⟩
    apply h.trans
    funext x y z
    simp [Tensor.restrict, scalarTensor, Tensor.rankOne, mul_ite, ite_and]
  · rintro ⟨A, B, C, rfl⟩
    exact (scalarTensor_rankAtMost r).restrict A B C

/-- The restriction order below a natural number is exactly the usual rank bound. -/
theorem classOf_le_nat_iff_rankAtMost
    {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) (r : ℕ) :
    classOf T ≤ (r : (TensorClass K)) ↔ Tensor.RankAtMost T r := by
  rw [← classOf_scalarTensor r, classOf_le_iff]
  exact (rankAtMost_iff_isRestriction_scalarTensor T r).symm

/-- Rank takes its usual value on natural numbers in the tensor semiring. -/
@[simp] theorem rank_natCast (r : ℕ) : rank (r : (TensorClass ℤ)) = r := by
  rw [← classOf_scalarTensor r, rank_classOf, exactRank_scalarTensor]

/-- The rank is a natural-number upper bound in the restriction order. -/
theorem le_rank (T : (TensorClass K)) : T ≤ (rank T : (TensorClass K)) := by
  induction T using Quotient.inductionOn with
  | h T =>
    change tensorClass T ≤ (exactRank T.coeff : (TensorClass K))
    rw [← classOf_coeff T]
    exact (classOf_le_nat_iff_rankAtMost T.coeff (exactRank T.coeff)).mpr
      (exactRank_spec T.coeff)

/-- The tensor restriction order induces the usual order on natural numbers. -/
@[simp] theorem natCast_le_natCast_iff (m n : ℕ) :
    (m : (TensorClass ℤ)) ≤ (n : (TensorClass ℤ)) ↔ m ≤ n := by
  constructor
  · intro h
    simpa only [rank_natCast] using rank_mono h
  · intro h
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [Nat.cast_add]
    simpa only [add_zero] using add_mono (le_refl (m : (TensorClass ℤ))) (zero_le (k : (TensorClass ℤ)))

namespace UnitTensorClass

/-- Exact rank is an upper bound also in the unit-admitting subsemiring. -/
theorem le_rank (T : UnitTensorClass K) : T ≤ (rank T : UnitTensorClass K) :=
  TensorSemiring.le_rank T.val

@[simp] theorem rank_natCast (r : ℕ) : rank (r : UnitTensorClass ℤ) = r :=
  TensorSemiring.rank_natCast r

/-- Integral natural-number order is reflected by the unit-admitting classes. -/
@[simp] theorem natCast_le_natCast_iff (m n : ℕ) :
    (m : UnitTensorClass ℤ) ≤ (n : UnitTensorClass ℤ) ↔ m ≤ n :=
  TensorSemiring.natCast_le_natCast_iff m n

/-- A nonzero unit-admitting tensor is an order unit, with its multiplier
bounded by the exact rank of the tensor to be dominated. -/
theorem le_nat_mul_of_ne_zero (T S : UnitTensorClass K) (hS : S ≠ 0) :
    T ≤ (rank T : UnitTensorClass K) * S := by
  apply (le_rank T).trans
  simpa only [mul_one] using
    mul_mono (le_refl (rank T : UnitTensorClass K)) (one_le_of_ne_zero hS)

/-- Integral rectangular rank is at least every coordinate dimension. -/
theorem rank_matrixClass_lower {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    max (max (a * b) (b * c)) (c * a) ≤ rank (matrixClass a b c) := by
  rw [rank_matrixClass]
  exact matrixTensor_rank_lower ha hb hc (exactRank_spec _)

/-- Integral square matrix multiplication rank is at least `n²`. -/
theorem rank_square_matrixClass_lower (n : ℕ) :
    n ^ 2 ≤ rank (matrixClass n n n) := by
  by_cases hn : 0 < n
  · simpa only [max_self, pow_two] using rank_matrixClass_lower hn hn hn
  · have hzero : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    simp

end UnitTensorClass

end TensorSemiring
end MatrixMultiplication.AuxiliarySeparation

end

end OAI
