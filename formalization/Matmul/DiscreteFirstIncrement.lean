import Mathlib

namespace Matmul.DiscreteFirstIncrement

/-- Average secants decrease with their length for decreasing increments. -/
theorem antitone_increment_secant {f : ℕ → ℝ}
    (hf : Antitone (fun n => f (n+1)-f n))
    (h d : ℕ) (hh : 1 ≤ h) (hhd : h ≤ d) :
    (h:ℝ)*(f d-f 0) ≤ (d:ℝ)*(f h-f 0) := by
  let z : ℝ := f h-f (h-1)
  have hz (i : ℕ) (hi : i < h) : z ≤ f (i+1)-f i := by
    have hn : i ≤ h-1 := by omega
    have he := hf hn
    dsimp [z]
    have heq : h-1+1=h := by omega
    simpa [heq] using he
  have ht (i : ℕ) (hi : h ≤ i) : f (i+1)-f i ≤ z := by
    have he := hf (show h-1 ≤ i by omega)
    dsimp [z]
    have heq : h-1+1=h := by omega
    simpa [heq] using he
  have hprefix : (h:ℝ)*z ≤ f h-f 0 := by
    have he := Finset.sum_le_sum (s:=Finset.range h)
      (fun i hi => hz i (Finset.mem_range.mp hi))
    rw [Finset.sum_range_sub] at he
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using he
  have htail : f d-f h ≤ ((d-h:ℕ):ℝ)*z := by
    have he := Finset.sum_le_sum (s:=Finset.range (d-h))
      (fun i _ => ht (h+i) (by omega))
    have htel : ∑ i ∈ Finset.range (d-h), (f (h+i+1)-f (h+i)) = f d-f h := by
      have heq : h+(d-h)=d := by omega
      simpa [heq, Nat.add_assoc] using Finset.sum_range_sub (fun i => f (h+i)) (d-h)
    simpa only [htel, Finset.sum_const, Finset.card_range, nsmul_eq_mul] using he
  have hcast : ((d-h:ℕ):ℝ)=(d:ℝ)-h := Nat.cast_sub hhd
  rw [hcast] at htail
  have hnonneg : 0 ≤ (d:ℝ)-h := sub_nonneg.mpr (Nat.cast_le.mpr hhd)
  have hm := mul_le_mul_of_nonneg_left hprefix hnonneg
  have hm2 := mul_le_mul_of_nonneg_left htail (show 0 ≤ (h:ℝ) by positivity)
  nlinarith


/-- Positive powered self-tripling forces a finite first-coordinate increment. -/
theorem first_increment_of_self_tripling {Q : ℕ → ℝ} {θ : ℝ}
    (hθ : 0 < θ)
    (hpos : ∀ k : ℕ, 1 ≤ k → 0 < Q k)
    (hconc : Antitone (fun k : ℕ => Q (k + 2) ^ (1 / θ) - Q (k + 1) ^ (1 / θ)))
    (n s h : ℕ) (hn : 1 ≤ n) (hs : 1 ≤ s) (hh : 1 ≤ h)
    (hhd : h ≤ 2 * n + s - 1)
    (htrip : 3 * Q n ^ (1 / θ) ≤ Q (3 * n + s - 1) ^ (1 / θ)) :
    Q n * (1 + 2 * (h : ℝ) / (2 * (n : ℝ) + (s : ℝ) - 1)) ^ θ ≤ Q (n + h) := by
  let f : ℕ → ℝ := fun i => Q (n + i) ^ (1 / θ)
  let d : ℕ := 2 * n + s - 1
  have hanti : Antitone (fun i : ℕ => f (i + 1) - f i) := by
    intro i j hij
    have h := hconc (show n + i - 1 ≤ n + j - 1 by omega)
    have hi1 : n + i - 1 + 1 = n + i := by omega
    have hi2 : n + i - 1 + 2 = n + (i + 1) := by omega
    have hj1 : n + j - 1 + 1 = n + j := by omega
    have hj2 : n + j - 1 + 2 = n + (j + 1) := by omega
    simpa only [hi1, hi2, hj1, hj2, f] using h
  have hhd' : h ≤ d := hhd
  have hsec := antitone_increment_secant hanti h d hh hhd'
  have hfarindex : n + d = 3 * n + s - 1 := by dsimp [d]; omega
  have hfar : 2 * f 0 ≤ f d - f 0 := by
    dsimp [f]
    rw [hfarindex]
    linarith
  have hfar_mul := mul_le_mul_of_nonneg_left hfar (Nat.cast_nonneg h)
  have hdc : (d : ℝ) = 2 * (n : ℝ) + (s : ℝ) - 1 := by
    dsimp [d]
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * n + s), Nat.cast_add,
      Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  have hdpos : (0 : ℝ) < d := by
    exact_mod_cast (show 0 < d by dsimp [d]; omega)
  have hpow : Q n ^ (1 / θ) * (1 + 2 * (h : ℝ) / (d : ℝ)) ≤
      Q (n + h) ^ (1 / θ) := by
    have hscaled : 2 * (h : ℝ) * f 0 ≤ (d : ℝ) * (f h - f 0) := by
      nlinarith
    dsimp [f] at hscaled
    apply (mul_le_mul_iff_of_pos_right hdpos).mp
    have heq :
        (Q n ^ (1 / θ) * (1 + 2 * (h : ℝ) / (d : ℝ))) * (d : ℝ) =
          (d : ℝ) * Q n ^ (1 / θ) + 2 * (h : ℝ) * Q n ^ (1 / θ) := by
      field_simp
    rw [heq]
    nlinarith
  have hbase : 0 ≤ 1 + 2 * (h : ℝ) / (d : ℝ) := by positivity
  have hraise := Real.rpow_le_rpow
    (mul_nonneg (Real.rpow_nonneg (hpos n hn).le _) hbase) hpow hθ.le
  rw [Real.mul_rpow (Real.rpow_nonneg (hpos n hn).le _) hbase] at hraise
  simp only [one_div, Real.rpow_inv_rpow (hpos n hn).le hθ.ne',
    Real.rpow_inv_rpow (hpos (n + h) (by omega)).le hθ.ne'] at hraise
  simpa only [hdc] using hraise

#print axioms first_increment_of_self_tripling

end Matmul.DiscreteFirstIncrement
