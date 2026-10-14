import Matmul.ProfileValues
import Matmul.SharedLegEntropyBackend
import Matmul.IntegralDeterminant
import Matmul.IntegralTripling
import Matmul.IntegerProfileEntropy
import Matmul.DeterminantLogLaws
import Matmul.ConvolutionDotRestriction
import Matmul.TriplingLogLaws

namespace Matmul.IntegerProfileLaws

open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open Matmul.IntegralCharacter Matmul.IntegerCharacter
open Matmul.ConvolutionCharacter Matmul.ProfileValues
open scoped BigOperators

noncomputable section

def swapXY {X Y Z : Type*} (T : Tensor ℤ X Y Z) : Tensor ℤ Y X Z :=
  fun y x z => T x y z

/-- Interchanging the two input legs defines another actual integral character. -/
def swapXYCharacter (φ : IntegralCharacter) : IntegralCharacter where
  value T := φ.value (swapXY T)
  nonneg T := φ.nonneg _
  map_zero := φ.map_zero
  map_one := φ.map_one
  map_sumTensor T S := by
    have heq : swapXY (sumTensor T S) = sumTensor (swapXY T) (swapXY S) := by
      funext y x z
      cases x <;> cases y <;> cases z <;> rfl
    rw [heq, φ.map_sumTensor]
  map_directSum T := by
    have heq : swapXY (Tensor.directSum T) = Tensor.directSum (fun i => swapXY (T i)) := by
      funext y x z
      by_cases h : y.1 = x.1 ∧ y.1 = z.1
      · simp [swapXY, Tensor.directSum, h.1]
      · have h' : ¬ (x.1 = y.1 ∧ x.1 = z.1) := by
          rintro ⟨hxy, hxz⟩
          exact h ⟨hxy.symm, hxy.symm.trans hxz⟩
        simp [swapXY, Tensor.directSum, h, h']
    rw [heq, φ.map_directSum]
  map_product T S := φ.map_product (swapXY T) (swapXY S)
  monotone T A B C := by
    have heq : swapXY (Tensor.restrict A B C T) =
        Tensor.restrict B A C (swapXY T) := by
      funext y x z
      simp only [swapXY, Tensor.restrict]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro k hk
      ring
    rw [heq]
    exact φ.monotone _ _ _ _

theorem swapXY_pX (φ : IntegralCharacter) : (swapXYCharacter φ).pX = φ.pY := by
  unfold IntegralCharacter.pX IntegralCharacter.pY
  have heq : swapXY (dotX 2) = cyclic (cyclic (dotX 2)) := by
    funext x y z
    simp [swapXY, cyclic, dotX, eq_comm]
  change Real.log (φ.value (swapXY (dotX 2)))/Real.log 2 = _
  rw [heq]
  rfl

theorem swapXY_pZ (φ : IntegralCharacter) : (swapXYCharacter φ).pZ = φ.pZ := by
  unfold IntegralCharacter.pZ IntegralCharacter.pX
  have heq : swapXY (cyclic (dotX 2)) = cyclic (dotX 2) := by
    funext x y z
    simp [swapXY, cyclic, dotX, eq_comm]
  change Real.log (φ.value (swapXY (cyclic (dotX 2))))/Real.log 2 = _
  rw [heq]
  rfl

theorem cyclic_pX (φ : IntegralCharacter) : φ.cyclicCharacter.pX = φ.pZ := rfl

theorem swapXY_valueXY (φ : IntegralCharacter) (r s : ℕ) :
    valueXY (swapXYCharacter φ) r s = valueXY φ s r := by
  have heq : swapXY (CXY r s) = Tensor.pullback (Equiv.refl (Fin s))
      (Equiv.refl (Fin r))
      (finCongr (by unfold Matmul.IntegralConvolution.outputLength; omega)) (CXY s r) := by
    funext x y z
    simp [swapXY, CXY, Tensor.pullback, Matmul.IntegralConvolution.convolution, add_comm]
  change φ.value (swapXY (CXY r s)) = _
  rw [heq, φ.value_reindex]
  rfl

theorem swapXY_valueXZ (φ : IntegralCharacter) (r s : ℕ) :
    valueXZ (swapXYCharacter φ) r s = valueYZ φ r s := rfl

/-- Input exchange after cycling retains the oriented convolution. -/
theorem cyclic_valueXY (φ : IntegralCharacter) (r s : ℕ) :
    valueXY φ.cyclicCharacter s r = valueXZ φ r s := by
  have heq : cyclic (CXY s r) = Tensor.pullback (Equiv.refl (Fin r))
      (finCongr (by unfold Matmul.IntegralConvolution.outputLength; omega))
      (Equiv.refl (Fin s)) (CXZ r s) := by
    funext x y z
    simp [cyclic, CXZ, CXY, Tensor.pullback, Matmul.IntegralConvolution.convolution, add_comm]
  change φ.value (cyclic (CXY s r)) = _
  rw [heq, φ.value_reindex]
  rfl

theorem cyclic_valueXZ (φ : IntegralCharacter) (r s : ℕ) :
    valueXZ φ.cyclicCharacter s r = valueYZ φ r s := by
  have heq : cyclic (CXZ s r) = Tensor.pullback
      (finCongr (by unfold Matmul.IntegralConvolution.outputLength; omega))
      (Equiv.refl (Fin r)) (Equiv.refl (Fin s)) (CYZ r s) := by
    funext x y z
    simp [cyclic, CXZ, CYZ, CXY, Tensor.pullback,
      Matmul.IntegralConvolution.convolution, add_comm]
  change φ.value (cyclic (CXZ s r)) = _
  rw [heq, φ.value_reindex]
  rfl

theorem swapXY_valueYZ (φ : IntegralCharacter) (r s : ℕ) :
    valueYZ (swapXYCharacter φ) r s = valueXZ φ r s := rfl

/-- Conjugating the input interchange by a cycle interchanges the last two legs. -/
def swapYZCharacter (φ : IntegralCharacter) : IntegralCharacter :=
  (swapXYCharacter φ.cyclicCharacter.cyclicCharacter).cyclicCharacter

theorem swapYZ_pX (φ : IntegralCharacter) : (swapYZCharacter φ).pX = φ.pX := by
  have heq : cyclic (cyclic (swapXY (cyclic (dotX 2)))) = dotX 2 := by
    funext x y z
    simp [cyclic, swapXY, dotX, eq_comm]
  unfold IntegralCharacter.pX
  change Real.log (φ.value (cyclic (cyclic (swapXY (cyclic (dotX 2))))))/Real.log 2 = _
  rw [heq]

theorem swapYZ_valueXY (φ : IntegralCharacter) (r s : ℕ) :
    valueXY (swapYZCharacter φ) r s = valueXZ φ r s := rfl

theorem swapYZ_valueXZ (φ : IntegralCharacter) (r s : ℕ) :
    valueXZ (swapYZCharacter φ) r s = valueXY φ r s := rfl

def poweredV (φ : IntegralCharacter) (r s : ℕ) : ℝ := rawV φ r s ^ (1/a φ)
def poweredU (φ : IntegralCharacter) (r s : ℕ) : ℝ := rawU φ r s ^ (1/a φ)

def pairedXY (φ ψ : IntegralCharacter) (r s : ℕ) : ℝ :=
  Real.sqrt (valueXY φ r s*valueXY ψ r s)

theorem pairedXY_second_difference (φ ψ : IntegralCharacter)
    (hp : 0 < (φ.pX+ψ.pX)/2) (r s : ℕ) (hr : 1 ≤ r) (hs : 2 ≤ s) :
    pairedXY φ ψ r (s+1)^(1/((φ.pX+ψ.pX)/2))+
      pairedXY φ ψ r (s-1)^(1/((φ.pX+ψ.pX)/2)) ≤
      2*pairedXY φ ψ r s^(1/((φ.pX+ψ.pX)/2)) := by
  let x : Fin 2 → ℝ := ![valueXY φ r (s+1), valueXY φ r (s-1)]
  let y : Fin 2 → ℝ := ![valueXY ψ r (s+1), valueXY ψ r (s-1)]
  have hx : ∀ i, 0 < x i := by
    intro i
    fin_cases i <;> exact valueXY_pos φ _ _ hr (by omega)
  have hy : ∀ i, 0 < y i := by
    intro i
    fin_cases i <;> exact valueXY_pos ψ _ _ hr (by omega)
  have hbx (q : FiniteLaw (Fin 2)) :
      φ.pX*finiteEntropy q.mass+∑ i,q.mass i*Real.log (x i) ≤
        Real.log (valueXY φ r s)+Real.log 2*φ.pX := by
    have h := Matmul.DeterminantLogLaws.determinant_log φ q r s hr hs
    simpa [x, Fin.sum_univ_two, add_assoc, mul_comm] using h
  have hby (q : FiniteLaw (Fin 2)) :
      ψ.pX*finiteEntropy q.mass+∑ i,q.mass i*Real.log (y i) ≤
        Real.log (valueXY ψ r s)+Real.log 2*ψ.pX := by
    have h := Matmul.DeterminantLogLaws.determinant_log ψ q r s hr hs
    simpa [y, Fin.sum_univ_two, add_assoc, mul_comm] using h
  have h := Matmul.IntegerProfileEntropy.geometric_mean_powered_sum_le hx hy
    (valueXY_pos φ r s hr (by omega)) (valueXY_pos ψ r s hr (by omega)) hp hbx hby
  simpa [x,y,Fin.sum_univ_two,pairedXY, Real.exp_log (by norm_num : (0:ℝ)<2)] using h

theorem antitone_positive_increments_of_second_difference {f : ℕ → ℝ}
    (hf : ∀ s, 2 ≤ s → f (s+1)+f (s-1) ≤ 2*f s) :
    Antitone (fun n => f (n+2)-f (n+1)) := by
  apply antitone_nat_of_succ_le
  intro n
  have h := hf (n+2) (by omega)
  have hi : n+2-1=n+1 := by omega
  rw [hi] at h
  have hi2 : n+1+2=n+2+1 := by omega
  rw [hi2]
  linarith

theorem pairedXY_rawV (φ : IntegralCharacter) (r s : ℕ) :
    pairedXY φ (swapXYCharacter φ) r s = rawV φ r s := by
  simp [pairedXY,rawV,swapXY_valueXY]

theorem pairedXY_rawU (φ : IntegralCharacter) (r s : ℕ) :
    pairedXY (swapYZCharacter φ) (swapYZCharacter (swapXYCharacter φ)) r s =
      rawU φ r s := by
  simp [pairedXY,rawU,swapYZ_valueXY,swapXY_valueXZ]

theorem pairedXY_rawU_first (φ : IntegralCharacter) (r s : ℕ) :
    pairedXY φ.cyclicCharacter (swapXYCharacter φ).cyclicCharacter s r =
      rawU φ r s := by
  simp [pairedXY,rawU,cyclic_valueXY,swapXY_valueXZ]

theorem V_concave_second (φ : IntegralCharacter) (ha : 0 < a φ)
    (r : ℕ) (hr : 1 ≤ r) :
    Antitone (fun s => poweredV φ r (s+2)-poweredV φ r (s+1)) := by
  apply antitone_positive_increments_of_second_difference
  intro s hs
  have h := pairedXY_second_difference φ (swapXYCharacter φ)
    (by simpa [swapXY_pX,a] using ha) r s hr hs
  simpa [pairedXY_rawV,swapXY_pX,a,poweredV] using h

theorem V_concave_first (φ : IntegralCharacter) (ha : 0 < a φ)
    (s : ℕ) (hs : 1 ≤ s) :
    Antitone (fun r => poweredV φ (r+2) s-poweredV φ (r+1) s) := by
  simpa [poweredV,rawV_symm φ s] using V_concave_second φ ha s hs

theorem U_concave_second (φ : IntegralCharacter) (ha : 0 < a φ)
    (r : ℕ) (hr : 1 ≤ r) :
    Antitone (fun s => poweredU φ r (s+2)-poweredU φ r (s+1)) := by
  apply antitone_positive_increments_of_second_difference
  intro s hs
  have h := pairedXY_second_difference (swapYZCharacter φ)
    (swapYZCharacter (swapXYCharacter φ))
    (by simpa [swapYZ_pX,swapXY_pX,a] using ha) r s hr hs
  simpa [pairedXY_rawU,swapYZ_pX,swapXY_pX,a,poweredU] using h

theorem U_concave_first (φ : IntegralCharacter) (hb : 0 < b φ)
    (s : ℕ) (hs : 1 ≤ s) :
    Antitone (fun r => rawU φ (r+2) s^(1/b φ)-rawU φ (r+1) s^(1/b φ)) := by
  apply antitone_positive_increments_of_second_difference
    (f:=fun r => rawU φ r s^(1/b φ))
  intro r hr
  have h := pairedXY_second_difference φ.cyclicCharacter (swapXYCharacter φ).cyclicCharacter
    (by simpa [cyclic_pX,swapXY_pZ,b] using hb) s r hs hr
  simpa [pairedXY_rawU_first,cyclic_pX,swapXY_pZ,b] using h

theorem rawV_two_two_le_of_a_zero (φ : IntegralCharacter) (ha : a φ = 0) :
    rawV φ 2 2 ≤ 1 := by
  have hX : φ.pX = 0 := by
    have hx := φ.pX_nonneg
    have hy := φ.pY_nonneg
    dsimp [a] at ha
    linarith
  have hY : φ.pY = 0 := by
    have hx := φ.pX_nonneg
    have hy := φ.pY_nonneg
    dsimp [a] at ha
    linarith
  have h := Matmul.DeterminantLogLaws.determinant_endpoint φ 2 (by omega)
  rw [valueXY_one_right φ 2 (by omega),hX,hY] at h
  simpa [Matmul.ConvolutionDotRestriction.rawV_square_eq] using h

def pairedXZ (φ ψ : IntegralCharacter) (r s : ℕ) : ℝ :=
  Real.sqrt (valueXZ φ r s*valueXZ ψ r s)

theorem pairedXY_tripling (φ ψ : IntegralCharacter)
    (hp : 0 < (φ.pX+ψ.pX)/2) (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s) :
    2*pairedXY φ ψ r s^(1/((φ.pX+ψ.pX)/2))+
      pairedXZ φ ψ r s^(1/((φ.pX+ψ.pX)/2)) ≤
      pairedXY φ ψ r (3*s+r-1)^(1/((φ.pX+ψ.pX)/2)) := by
  let x : Fin 3 → ℝ := ![valueXY φ r s,valueXZ φ r s,valueXY φ r s]
  let y : Fin 3 → ℝ := ![valueXY ψ r s,valueXZ ψ r s,valueXY ψ r s]
  have hx : ∀ i, 0 < x i := by
    intro i
    fin_cases i
    · exact valueXY_pos φ r s hr hs
    · exact valueXZ_pos φ r s hr hs
    · exact valueXY_pos φ r s hr hs
  have hy : ∀ i, 0 < y i := by
    intro i
    fin_cases i
    · exact valueXY_pos ψ r s hr hs
    · exact valueXZ_pos ψ r s hr hs
    · exact valueXY_pos ψ r s hr hs
  have hbx (q : FiniteLaw (Fin 3)) :
      φ.pX*finiteEntropy q.mass+∑ i,q.mass i*Real.log (x i) ≤
        Real.log (valueXY φ r (3*s+r-1))+0*φ.pX := by
    have h := Matmul.TriplingLogLaws.tripling_log φ q r s hr hs
    simpa [x, Fin.sum_univ_three, add_assoc] using h
  have hby (q : FiniteLaw (Fin 3)) :
      ψ.pX*finiteEntropy q.mass+∑ i,q.mass i*Real.log (y i) ≤
        Real.log (valueXY ψ r (3*s+r-1))+0*ψ.pX := by
    have h := Matmul.TriplingLogLaws.tripling_log ψ q r s hr hs
    simpa [y, Fin.sum_univ_three, add_assoc] using h
  have h := Matmul.IntegerProfileEntropy.geometric_mean_powered_sum_le hx hy
    (valueXY_pos φ r (3*s+r-1) hr (by omega))
    (valueXY_pos ψ r (3*s+r-1) hr (by omega)) hp hbx hby
  simpa [x,y,Fin.sum_univ_three,pairedXY,pairedXZ,two_mul,add_assoc,
    add_comm,add_left_comm] using h

theorem pairedXZ_rawU (φ : IntegralCharacter) (r s : ℕ) :
    pairedXZ φ (swapXYCharacter φ) r s = rawU φ r s := by
  simp [pairedXZ,rawU,swapXY_valueXZ]

theorem pairedXZ_rawV (φ : IntegralCharacter) (r s : ℕ) :
    pairedXZ (swapYZCharacter φ) (swapYZCharacter (swapXYCharacter φ)) r s =
      rawV φ r s := by
  simp [pairedXZ,rawV,swapYZ_valueXZ,swapXY_valueXY]

theorem pairedXZ_rawU_first (φ : IntegralCharacter) (r s : ℕ) :
    pairedXZ φ.cyclicCharacter (swapXYCharacter φ).cyclicCharacter s r =
      rawU φ r s := by
  simp [pairedXZ,rawU,cyclic_valueXZ,swapXY_valueYZ,mul_comm]

theorem V_tripling (φ : IntegralCharacter) (ha : 0 < a φ)
    (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s) :
    2*poweredV φ r s+poweredU φ r s ≤ poweredV φ r (3*s+r-1) := by
  have h := pairedXY_tripling φ (swapXYCharacter φ)
    (by simpa [swapXY_pX,a] using ha) r s hr hs
  simpa [pairedXY_rawV,pairedXZ_rawU,swapXY_pX,a,poweredV,poweredU] using h

theorem U_tripling (φ : IntegralCharacter) (ha : 0 < a φ)
    (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s) :
    2*poweredU φ r s+poweredV φ r s ≤ poweredU φ r (3*s+r-1) := by
  have h := pairedXY_tripling (swapYZCharacter φ)
    (swapYZCharacter (swapXYCharacter φ))
    (by simpa [swapYZ_pX,swapXY_pX,a] using ha) r s hr hs
  simpa [pairedXY_rawU,pairedXZ_rawV,swapYZ_pX,swapXY_pX,a,poweredV,poweredU] using h

theorem U_self_tripling (φ : IntegralCharacter) (hb : 0 < b φ)
    (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s) :
    3*rawU φ r s^(1/b φ) ≤ rawU φ (3*r+s-1) s^(1/b φ) := by
  have h := pairedXY_tripling φ.cyclicCharacter (swapXYCharacter φ).cyclicCharacter
    (by simpa [cyclic_pX,swapXY_pZ,b] using hb) s r hs hr
  simpa [pairedXY_rawU_first,pairedXZ_rawU_first,cyclic_pX,
    swapXY_pZ,b,show (3:ℝ)=2+1 by norm_num,add_mul] using h

#print axioms V_concave_second
#print axioms U_concave_first
#print axioms V_tripling
#print axioms U_tripling
#print axioms U_self_tripling
#print axioms rawV_two_two_le_of_a_zero

end
end Matmul.IntegerProfileLaws
