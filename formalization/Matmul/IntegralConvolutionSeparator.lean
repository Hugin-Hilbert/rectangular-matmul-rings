import Matmul.IntegralConvolution
import Matmul.IntegralSeparator

/-!
# The convolution used by the integral shared-leg separator

The separator uses integer interval coordinates. Sending each coordinate to
its natural-number value gives a pullback of ordinary finite convolution,
so the integral exponential rank bound applies without any new interpolation.
-/

namespace Matmul.IntegralConvolution

open OAI.MatrixMultiplication.Foundation

def separatorInputIndex {M : ℕ} (hM : 0 < M)
    (i : Matmul.IntegralSeparator.ConvInput M) : Fin (2 * M - 1) :=
  ⟨i.val.toNat, by have h0 := i.property.1; have hlt := i.property.2; omega⟩

def separatorOutputIndex {M : ℕ} (hM : 0 < M)
    (i : Matmul.IntegralSeparator.ConvOutput M) :
    Fin (outputLength (2 * M - 1) (2 * M - 1)) :=
  ⟨i.val.toNat, by
    have h0 := i.property.1
    have hlt := i.property.2
    unfold outputLength
    omega⟩

theorem separator_outputLength {M : ℕ} (hM : 0 < M) :
    outputLength (2 * M - 1) (2 * M - 1) = 4 * M - 3 := by
  unfold outputLength
  omega

theorem separator_convolution_eq_pullback {K : Type*} [CommSemiring K]
    {M : ℕ} (hM : 0 < M) :
    Matmul.IntegralSeparator.convolution K M =
      Tensor.pullback (separatorInputIndex hM) (separatorInputIndex hM)
        (separatorOutputIndex hM) (convolution K (2 * M - 1) (2 * M - 1)) := by
  funext i j k
  have hsum : i.val.toNat + j.val.toNat = k.val.toNat ↔ i.val + j.val = k.val := by
    have hi := i.property.1
    have hj := j.property.1
    have hk := k.property.1
    omega
  simp only [Matmul.IntegralSeparator.convolution, Tensor.pullback,
    convolution, separatorInputIndex, separatorOutputIndex, hsum]

theorem tensor_power_pullback {K X Y Z X' Y' Z' : Type*} [CommSemiring K]
    (T : Tensor K X Y Z) (f : X' → X) (g : Y' → Y) (h : Z' → Z) (m : ℕ) :
    Tensor.power (Tensor.pullback f g h T) m =
      Tensor.pullback (fun x i => f (x i)) (fun y i => g (y i))
        (fun z i => h (z i)) (Tensor.power T m) := rfl

/-- The separator's actual interval-indexed convolution has the optimal
integer exponential upper bound, with a positive constant independent of
the tensor power. -/
theorem exists_separator_power_rank_bound (M : ℕ) (hM : 0 < M) :
    ∃ K : ℕ, 0 < K ∧ ∀ m : ℕ, Tensor.RankAtMost
      (Tensor.power (Matmul.IntegralSeparator.convolution ℤ M) m)
      (K * (4 * M - 3) ^ m) := by
  obtain ⟨K, hpos, hK⟩ := exists_pos_power_rank_bound (2 * M - 1) (2 * M - 1)
  refine ⟨K, hpos, ?_⟩
  intro m
  have h := (hK m).pullback
    (fun (x : Fin m → Matmul.IntegralSeparator.ConvInput M) i => separatorInputIndex hM (x i))
    (fun (y : Fin m → Matmul.IntegralSeparator.ConvInput M) i => separatorInputIndex hM (y i))
    (fun (z : Fin m → Matmul.IntegralSeparator.ConvOutput M) i => separatorOutputIndex hM (z i))
  rw [← tensor_power_pullback, ← separator_convolution_eq_pullback hM] at h
  simpa only [separator_outputLength hM] using h

theorem exists_separator_exactRank_power_bound (M : ℕ) (hM : 0 < M) :
    ∃ K : ℕ, 0 < K ∧ ∀ m : ℕ,
      OAI.MatrixMultiplication.AuxiliarySeparation.exactRank
        (Tensor.power (Matmul.IntegralSeparator.convolution ℤ M) m) ≤
          K * (4 * M - 3) ^ m := by
  obtain ⟨K, hpos, hK⟩ := exists_separator_power_rank_bound M hM
  exact ⟨K, hpos, fun m => OAI.MatrixMultiplication.AuxiliarySeparation.exactRank_le (hK m)⟩

#print axioms separator_convolution_eq_pullback
#print axioms exists_separator_power_rank_bound
#print axioms exists_separator_exactRank_power_bound

end Matmul.IntegralConvolution
