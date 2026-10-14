import Mathlib

/-! Adapted from the upstream ConcaveSlopes and ProfileSlopes modules.
Their license is recorded in formalization/UPSTREAM-LICENSE. -/

namespace Matmul.DiscreteSlopes

open Filter
open scoped Topology

/-- The usual second-difference inequality makes the increments decreasing. -/
theorem antitone_increments_of_discrete_concavity {u : ℕ → ℝ}
    (hu : ∀ n, u (n + 2) + u n ≤ 2 * u (n + 1)) :
    Antitone (fun n => u (n + 1) - u n) := by
  apply antitone_nat_of_succ_le
  intro n
  have h := hu n
  simp only [Nat.add_assoc] at *
  linarith

/-- A tangent-line upper bound for a sequence with decreasing increments. -/
theorem concave_sequence_le_affine {u : ℕ → ℝ}
    (hd : Antitone (fun n => u (n + 1) - u n)) (n k : ℕ) :
    u (n + k) ≤ u n + (k : ℝ) * (u (n + 1) - u n) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hstep := hd (show n ≤ n + k by omega)
      simp only at hstep
      rw [Nat.cast_add, Nat.cast_one]
      have hindex : n + (k + 1) = n + k + 1 := by omega
      rw [hindex]
      nlinarith

/-- Every increment of a nonnegative discretely concave sequence is nonnegative. -/
theorem increment_nonneg_of_antitone {u : ℕ → ℝ}
    (hu : ∀ n, 0 ≤ u n) (hd : Antitone (fun n => u (n + 1) - u n))
    (n : ℕ) : 0 ≤ u (n + 1) - u n := by
  by_contra hn
  have hneg : u (n + 1) - u n < 0 := lt_of_not_ge hn
  obtain ⟨k, hk⟩ := exists_lt_nsmul (neg_pos.mpr hneg) (u n)
  have hk' : u n < (k : ℝ) * -(u (n + 1) - u n) := by
    simpa only [nsmul_eq_mul] using hk
  have hbound := concave_sequence_le_affine hd n k
  have hnonneg := hu (n + k)
  nlinarith

/-- A nonnegative discretely concave sequence is increasing. -/
theorem monotone_of_nonneg_of_antitone_increments {u : ℕ → ℝ}
    (hu : ∀ n, 0 ≤ u n) (hd : Antitone (fun n => u (n + 1) - u n)) :
    Monotone u := by
  apply monotone_nat_of_le_succ
  intro n
  have := increment_nonneg_of_antitone hu hd n
  linarith

/-- Telescoping and Cesàro convergence identify the linear growth rate. -/
theorem tendsto_div_nat_of_tendsto_increments {u : ℕ → ℝ} {g : ℝ}
    (hd : Tendsto (fun n => u (n + 1) - u n) atTop (𝓝 g)) :
    Tendsto (fun n => u n / (n : ℝ)) atTop (𝓝 g) := by
  have hmean := hd.cesaro
  simp only [Finset.sum_range_sub] at hmean
  have hconst := tendsto_const_div_atTop_nhds_zero_nat (u 0)
  have hsum := hmean.add hconst
  simpa only [add_zero, div_eq_mul_inv, mul_sub, sub_add_cancel, mul_comm] using hsum

/-- The limiting increment of a nonnegative discretely concave sequence is
nonnegative, and it is also its linear growth rate. -/
theorem exists_nonneg_limit_of_antitone_increments {u : ℕ → ℝ}
    (hu : ∀ n, 0 ≤ u n) (hd : Antitone (fun n => u (n + 1) - u n)) :
    ∃ g : ℝ, 0 ≤ g ∧
      Tendsto (fun n => u (n + 1) - u n) atTop (𝓝 g) ∧
      Tendsto (fun n => u n / (n : ℝ)) atTop (𝓝 g) := by
  have hnonneg := increment_nonneg_of_antitone hu hd
  have hbdd : BddBelow (Set.range (fun n => u (n + 1) - u n)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact hnonneg n
  have hlim := tendsto_atTop_ciInf hd hbdd
  refine ⟨⨅ n, u (n + 1) - u n, ?_, hlim,
    tendsto_div_nat_of_tendsto_increments hlim⟩
  exact ge_of_tendsto hlim (Eventually.of_forall hnonneg)

/-- Positive-index version, suitable for the rows in Section 6. The value at
index zero is irrelevant. -/
theorem exists_concave_slope_limit {P : ℕ → ℝ}
    (hP : ∀ n, 0 < P (n + 1))
    (hd : Antitone (fun n => P (n + 2) - P (n + 1))) :
    ∃ g : ℝ, 0 ≤ g ∧
      (∀ n, g ≤ P (n + 2) - P (n + 1)) ∧
      Tendsto (fun n => P (n + 2) - P (n + 1)) atTop (𝓝 g) ∧
      Tendsto (fun n => P n / (n : ℝ)) atTop (𝓝 g) := by
  have hd' : Antitone (fun n => P ((n + 1) + 1) - P (n + 1)) := by
    simpa only [Nat.add_assoc] using hd
  obtain ⟨g, hg, hlim, hratio⟩ := exists_nonneg_limit_of_antitone_increments
    (u := fun n => P (n + 1)) (fun n => (hP n).le) hd'
  have hmul := hratio.mul (tendsto_natCast_div_add_atTop (1 : ℝ))
  have hshift : Tendsto (fun n => P (n + 1) / ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 g) := by
    rw [mul_one] at hmul
    apply hmul.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    rw [Nat.cast_add, Nat.cast_one]
    field_simp
  refine ⟨g, hg, ?_, ?_, (tendsto_add_atTop_iff_nat 1).mp hshift⟩
  · intro n
    exact hd.le_of_tendsto (by simpa only [Nat.add_assoc] using hlim) n
  · simpa only [Nat.add_assoc] using hlim



open Filter
open scoped Topology

/-- The indices obtained by repeatedly applying the affine tripling map. -/
def shiftedTriplingIndex (c h : ℕ) : ℕ → ℕ
  | 0 => h
  | j + 1 => 3 * shiftedTriplingIndex c h j + c

/-- Starting at a positive index, affine tripling escapes to infinity. -/
theorem shiftedTriplingIndex_lower (c h : ℕ) (hh : 1 ≤ h) (j : ℕ) :
    h + j ≤ shiftedTriplingIndex c h j := by
  induction j with
  | zero => simp [shiftedTriplingIndex]
  | succ j ih =>
      simp only [shiftedTriplingIndex]
      omega

theorem shiftedTriplingIndex_tendsto (c h : ℕ) (hh : 1 ≤ h) :
    Tendsto (shiftedTriplingIndex c h) atTop atTop := by
  apply tendsto_atTop_mono _ tendsto_id
  intro j
  change j ≤ shiftedTriplingIndex c h j
  have := shiftedTriplingIndex_lower c h hh j
  omega

/-- The exact affine solution, written without truncated natural subtraction. -/
theorem shiftedTriplingIndex_cast (c h j : ℕ) :
    (shiftedTriplingIndex c h j : ℝ) + (c : ℝ) / 2 =
      (3 : ℝ) ^ j * ((h : ℝ) + (c : ℝ) / 2) := by
  induction j with
  | zero => simp [shiftedTriplingIndex]
  | succ j ih =>
      simp only [shiftedTriplingIndex, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
        pow_succ]
      nlinarith

/-- Iterating the tripling inequality multiplies the profile by powers of three. -/
theorem shiftedTripling_profile_lower {P : ℕ → ℝ} {c h : ℕ} (hh : 1 ≤ h)
    (htrip : ∀ n : ℕ, 1 ≤ n → 3 * P n ≤ P (3 * n + c)) (j : ℕ) :
    (3 : ℝ) ^ j * P h ≤ P (shiftedTriplingIndex c h j) := by
  induction j with
  | zero => simp [shiftedTriplingIndex]
  | succ j ih =>
      have hj : 1 ≤ shiftedTriplingIndex c h j := by
        have := shiftedTriplingIndex_lower c h hh j
        omega
      have hstep := htrip (shiftedTriplingIndex c h j) hj
      simp only [shiftedTriplingIndex, pow_succ]
      nlinarith

/-- A row with a limiting linear slope and shifted tripling lies below the
corresponding affine multiple of that slope. -/
theorem profile_le_affine_slope {P : ℕ → ℝ} {g : ℝ} {c h : ℕ}
    (hh : 1 ≤ h)
    (htrip : ∀ n : ℕ, 1 ≤ n → 3 * P n ≤ P (3 * n + c))
    (hlim : Tendsto (fun n : ℕ => P n / (n : ℝ)) atTop (𝓝 g)) :
    P h ≤ ((h : ℝ) + (c : ℝ) / 2) * g := by
  have hpow : Tendsto (fun j : ℕ => (3 : ℝ) ^ j) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hzero : Tendsto (fun j : ℕ => ((c : ℝ) / 2) / (3 : ℝ) ^ j)
      atTop (𝓝 0) := hpow.const_div_atTop _
  have hindex : Tendsto
      (fun j : ℕ => (shiftedTriplingIndex c h j : ℝ) / (3 : ℝ) ^ j)
      atTop (𝓝 ((h : ℝ) + (c : ℝ) / 2)) := by
    have heq (j : ℕ) :
        (shiftedTriplingIndex c h j : ℝ) / (3 : ℝ) ^ j =
          (h : ℝ) + (c : ℝ) / 2 - ((c : ℝ) / 2) / (3 : ℝ) ^ j := by
      have hj := shiftedTriplingIndex_cast c h j
      have hp : (3 : ℝ) ^ j ≠ 0 := pow_ne_zero _ (by norm_num)
      field_simp
      nlinarith
    simpa only [heq, sub_zero] using tendsto_const_nhds.sub hzero
  have hproduct := (hlim.comp (shiftedTriplingIndex_tendsto c h hh)).mul hindex
  have hprofile : Tendsto
      (fun j : ℕ => P (shiftedTriplingIndex c h j) / (3 : ℝ) ^ j)
      atTop (𝓝 (g * ((h : ℝ) + (c : ℝ) / 2))) := by
    apply hproduct.congr'
    apply Eventually.of_forall
    intro j
    have hj : (shiftedTriplingIndex c h j : ℝ) ≠ 0 := by
      have := shiftedTriplingIndex_lower c h hh j
      exact_mod_cast (show shiftedTriplingIndex c h j ≠ 0 by omega)
    dsimp only [Function.comp_def]
    field_simp
  have hbound : ∀ j : ℕ, P h ≤ P (shiftedTriplingIndex c h j) / (3 : ℝ) ^ j := by
    intro j
    apply (le_div_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 3) j)).mpr
    simpa only [mul_comm] using shiftedTripling_profile_lower hh htrip j
  simpa only [mul_comm] using ge_of_tendsto hprofile (Eventually.of_forall hbound)

/-- The row estimate in the positive-index notation of the paper. -/
theorem profile_row_le_slope {P : ℕ → ℕ → ℝ} {g : ℕ → ℝ}
    (htrip : ∀ a : ℕ, 1 ≤ a → ∀ h : ℕ, 1 ≤ h →
      3 * P a h ≤ P a (3 * h + a - 1))
    (hlim : ∀ a : ℕ, 1 ≤ a →
      Tendsto (fun h : ℕ => P a h / (h : ℝ)) atTop (𝓝 (g a)))
    (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h) :
    P a h ≤ ((h : ℝ) + ((a : ℝ) - 1) / 2) * g a := by
  have ht : ∀ n : ℕ, 1 ≤ n → 3 * P a n ≤ P a (3 * n + (a - 1)) := by
    intro n hn
    have hi : 3 * n + (a - 1) = 3 * n + a - 1 := by omega
    rw [hi]
    exact htrip a ha n hn
  have hcast : ((a - 1 : ℕ) : ℝ) = (a : ℝ) - 1 := by
    rw [Nat.cast_sub ha, Nat.cast_one]
  simpa only [hcast] using profile_le_affine_slope hh ht (hlim a ha)

/-- The diagonal is bounded above by the limiting row slope with the precise
coefficient `(3a-1)/2`. -/
theorem profile_diagonal_le_slope {P : ℕ → ℕ → ℝ} {g : ℕ → ℝ}
    (htrip : ∀ a : ℕ, 1 ≤ a → ∀ h : ℕ, 1 ≤ h →
      3 * P a h ≤ P a (3 * h + a - 1))
    (hlim : ∀ a : ℕ, 1 ≤ a →
      Tendsto (fun h : ℕ => P a h / (h : ℝ)) atTop (𝓝 (g a)))
    (a : ℕ) (ha : 1 ≤ a) :
    P a a ≤ ((3 * (a : ℝ) - 1) / 2) * g a := by
  have hc : (a : ℝ) + ((a : ℝ) - 1) / 2 = (3 * (a : ℝ) - 1) / 2 := by ring
  simpa only [hc] using profile_row_le_slope htrip hlim a a ha ha

/-- Symmetry identifies a diagonal step with one increment in each adjacent
row. Only positive-index symmetry and slope bounds are used. -/
theorem diagonal_increment_of_slope_lower {P : ℕ → ℕ → ℝ} {g : ℕ → ℝ}
    (hsymm : ∀ a : ℕ, 1 ≤ a → ∀ b : ℕ, 1 ≤ b → P a b = P b a)
    (hinc : ∀ a : ℕ, 1 ≤ a → ∀ h : ℕ, 1 ≤ h →
      g a ≤ P a (h + 1) - P a h)
    (n : ℕ) (hn : 1 ≤ n) :
    P n n + g n + g (n + 1) ≤ P (n + 1) (n + 1) := by
  have hfirst := hinc n hn n hn
  have hsecond := hinc (n + 1) (by omega) n hn
  have hsym := hsymm n hn (n + 1) (by omega)
  linarith


/-- The asymmetric discrete tripling inequality orders the row slopes. -/
theorem slope_le_of_coupled_tripling {P Q : ℕ → ℝ} {L M : ℝ} {c : ℕ}
    (hP : Tendsto (fun s : ℕ => P s / (s : ℝ)) atTop (𝓝 L))
    (hQ : Tendsto (fun s : ℕ => Q s / (s : ℝ)) atTop (𝓝 M))
    (htrip : ∀ s : ℕ, 1 ≤ s → 2 * P s + Q s ≤ P (3 * s + c)) : M ≤ L := by
  have hmap : Tendsto (fun s : ℕ => 3 * s + c) atTop atTop := by
    apply tendsto_atTop_mono _ tendsto_id
    intro s
    change s ≤ 3 * s + c
    omega
  have hzero : Tendsto (fun s : ℕ => (c : ℝ) / (s : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hfactor : Tendsto (fun s : ℕ => ((3 * s + c : ℕ) : ℝ) / (s : ℝ))
      atTop (𝓝 (3 : ℝ)) := by
    have h := (tendsto_const_nhds (x := (3 : ℝ))).add hzero
    simp only [add_zero] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop 1] with s hs
    have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast (show s ≠ 0 by omega)
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    field_simp [hs0]
  have hright : Tendsto (fun s : ℕ => P (3 * s + c) / (s : ℝ))
      atTop (𝓝 (3 * L)) := by
    have h := (hP.comp hmap).mul hfactor
    rw [mul_comm L 3] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop 1] with s hs
    have ht : ((3 * s + c : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (show 3 * s + c ≠ 0 by omega)
    dsimp only [Function.comp_def]
    field_simp [ht]
  have hleft : Tendsto (fun s : ℕ => (2 * P s + Q s) / (s : ℝ))
      atTop (𝓝 (2 * L + M)) := by
    have h := (hP.const_mul 2).add hQ
    apply h.congr'
    exact Eventually.of_forall fun s => by simp [add_div, mul_div_assoc]
  have he : ∀ᶠ s : ℕ in atTop,
      (2 * P s + Q s) / (s : ℝ) ≤ P (3 * s + c) / (s : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with s hs
    exact div_le_div_of_nonneg_right (htrip s hs) (Nat.cast_nonneg _)
  have h := le_of_tendsto_of_tendsto hleft hright he
  linarith

/-- Consecutive increment bounds telescope over any finite discrete interval. -/
theorem long_increment_of_lower {P : ℕ → ℝ} {L : ℝ}
    (hinc : ∀ s : ℕ, 1 ≤ s → L ≤ P (s + 1) - P s)
    (s k : ℕ) (hs : 1 ≤ s) : (k : ℝ) * L ≤ P (s + k) - P s := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hstep := hinc (s + k) (by omega)
      rw [Nat.cast_succ, Nat.add_succ]
      nlinarith

/-- Coupled positive concave discrete rows have one positive asymptotic slope. -/
theorem exists_common_row_slope {P Q : ℕ → ℝ} {c : ℕ}
    (hPpos : ∀ s : ℕ, 1 ≤ s → 0 < P s)
    (hQpos : ∀ s : ℕ, 1 ≤ s → 0 < Q s)
    (hPd : Antitone (fun s : ℕ => P (s + 2) - P (s + 1)))
    (hQd : Antitone (fun s : ℕ => Q (s + 2) - Q (s + 1)))
    (hPt : ∀ s : ℕ, 1 ≤ s → 2 * P s + Q s ≤ P (3 * s + c))
    (hQt : ∀ s : ℕ, 1 ≤ s → 2 * Q s + P s ≤ Q (3 * s + c)) :
    ∃ L : ℝ, 0 < L ∧
      Tendsto (fun s : ℕ => P s / (s : ℝ)) atTop (𝓝 L) ∧
      Tendsto (fun s : ℕ => Q s / (s : ℝ)) atTop (𝓝 L) ∧
      (∀ s : ℕ, 1 ≤ s → P s + Q s ≤ L * (2 * (s : ℝ) + (c : ℝ))) ∧
      (∀ s : ℕ, 1 ≤ s → L ≤ P (s + 1) - P s) ∧
      (∀ s : ℕ, 1 ≤ s → L ≤ Q (s + 1) - Q s) ∧
      (∀ s : ℕ, 1 ≤ s → L * ((s : ℝ) - 1) ≤ P s) ∧
      (∀ s : ℕ, 1 ≤ s → L * ((s : ℝ) - 1) ≤ Q s) := by
  obtain ⟨L, hL, hPi, hPlimi, hPlim⟩ := exists_concave_slope_limit
    (fun s => hPpos (s + 1) (by omega)) hPd
  obtain ⟨M, hM, hQi, hQlimi, hQlim⟩ := exists_concave_slope_limit
    (fun s => hQpos (s + 1) (by omega)) hQd
  have heq : M = L := le_antisymm
    (slope_le_of_coupled_tripling hPlim hQlim hPt)
    (slope_le_of_coupled_tripling hQlim hPlim hQt)
  subst M
  have hPinc (s : ℕ) (hs : 1 ≤ s) : L ≤ P (s + 1) - P s := by
    have h := hPi (s - 1)
    have h1 : s - 1 + 1 = s := by omega
    have h2 : s - 1 + 2 = s + 1 := by omega
    simpa only [h1, h2] using h
  have hQinc (s : ℕ) (hs : 1 ≤ s) : L ≤ Q (s + 1) - Q s := by
    have h := hQi (s - 1)
    have h1 : s - 1 + 1 = s := by omega
    have h2 : s - 1 + 2 = s + 1 := by omega
    simpa only [h1, h2] using h
  have hsumlim : Tendsto (fun s : ℕ => (P s + Q s) / (s : ℝ))
      atTop (𝓝 (2 * L)) := by
    have h := hPlim.add hQlim
    convert h using 1 <;> simp [add_div, two_mul]
  have hsumtrip : ∀ s : ℕ, 1 ≤ s →
      3 * (P s + Q s) ≤ P (3 * s + c) + Q (3 * s + c) := by
    intro s hs
    have hp := hPt s hs
    have hq := hQt s hs
    linarith
  have hbound (s : ℕ) (hs : 1 ≤ s) :
      P s + Q s ≤ L * (2 * (s : ℝ) + (c : ℝ)) := by
    have h := profile_le_affine_slope hs hsumtrip hsumlim
    nlinarith
  have hLpos : 0 < L := by
    have hb := hbound 1 (by omega)
    have hp := hPpos 1 (by omega)
    have hq := hQpos 1 (by omega)
    have hc : (0 : ℝ) ≤ c := Nat.cast_nonneg c
    have hL0 : L ≠ 0 := by intro hz; simp [hz] at hb; linarith
    exact lt_of_le_of_ne hL (Ne.symm hL0)
  have hPlower (s : ℕ) (hs : 1 ≤ s) : L * ((s : ℝ) - 1) ≤ P s := by
    have h := long_increment_of_lower hPinc 1 (s - 1) (by omega)
    have hp := hPpos 1 (by omega)
    have hindex : 1 + (s - 1) = s := by omega
    have hcast : ((s - 1 : ℕ) : ℝ) = (s : ℝ) - 1 := by
      rw [Nat.cast_sub hs, Nat.cast_one]
    rw [hindex, hcast] at h
    nlinarith
  have hQlower (s : ℕ) (hs : 1 ≤ s) : L * ((s : ℝ) - 1) ≤ Q s := by
    have h := long_increment_of_lower hQinc 1 (s - 1) (by omega)
    have hp := hQpos 1 (by omega)
    have hindex : 1 + (s - 1) = s := by omega
    have hcast : ((s - 1 : ℕ) : ℝ) = (s : ℝ) - 1 := by
      rw [Nat.cast_sub hs, Nat.cast_one]
    rw [hindex, hcast] at h
    nlinarith
  exact ⟨L, hLpos, hPlim, hQlim, hbound, hPinc, hQinc, hPlower, hQlower⟩

/-- Simultaneous positive-index row slopes for the two discrete profiles. -/
theorem exists_common_profile_slopes {P Q : ℕ → ℕ → ℝ}
    (hPpos : ∀ n s : ℕ, 1 ≤ n → 1 ≤ s → 0 < P n s)
    (hQpos : ∀ n s : ℕ, 1 ≤ n → 1 ≤ s → 0 < Q n s)
    (hPd : ∀ n : ℕ, 1 ≤ n → Antitone (fun s : ℕ => P n (s + 2) - P n (s + 1)))
    (hQd : ∀ n : ℕ, 1 ≤ n → Antitone (fun s : ℕ => Q n (s + 2) - Q n (s + 1)))
    (hPt : ∀ n s : ℕ, 1 ≤ n → 1 ≤ s →
      2 * P n s + Q n s ≤ P n (3 * s + n - 1))
    (hQt : ∀ n s : ℕ, 1 ≤ n → 1 ≤ s →
      2 * Q n s + P n s ≤ Q n (3 * s + n - 1)) :
    ∃ L : ℕ → ℝ, ∀ n : ℕ, 1 ≤ n → 0 < L n ∧
      Tendsto (fun s : ℕ => P n s / (s : ℝ)) atTop (𝓝 (L n)) ∧
      Tendsto (fun s : ℕ => Q n s / (s : ℝ)) atTop (𝓝 (L n)) ∧
      (∀ s : ℕ, 1 ≤ s → P n s + Q n s ≤ L n * (2 * (s : ℝ) + (n : ℝ) - 1)) ∧
      (∀ s : ℕ, 1 ≤ s → L n ≤ P n (s + 1) - P n s) ∧
      (∀ s : ℕ, 1 ≤ s → L n ≤ Q n (s + 1) - Q n s) ∧
      (∀ s : ℕ, 1 ≤ s → L n * ((s : ℝ) - 1) ≤ P n s) ∧
      (∀ s : ℕ, 1 ≤ s → L n * ((s : ℝ) - 1) ≤ Q n s) := by
  classical
  have hrow (n : ℕ) : ∃ l : ℝ, 1 ≤ n → 0 < l ∧
      Tendsto (fun s : ℕ => P n s / (s : ℝ)) atTop (𝓝 l) ∧
      Tendsto (fun s : ℕ => Q n s / (s : ℝ)) atTop (𝓝 l) ∧
      (∀ s : ℕ, 1 ≤ s → P n s + Q n s ≤ l * (2 * (s : ℝ) + (n : ℝ) - 1)) ∧
      (∀ s : ℕ, 1 ≤ s → l ≤ P n (s + 1) - P n s) ∧
      (∀ s : ℕ, 1 ≤ s → l ≤ Q n (s + 1) - Q n s) ∧
      (∀ s : ℕ, 1 ≤ s → l * ((s : ℝ) - 1) ≤ P n s) ∧
      (∀ s : ℕ, 1 ≤ s → l * ((s : ℝ) - 1) ≤ Q n s) := by
    by_cases hn : 1 ≤ n
    · have hp : ∀ s : ℕ, 1 ≤ s → 2 * P n s + Q n s ≤ P n (3 * s + (n - 1)) := by
        intro s hs
        have heq : 3 * s + (n - 1) = 3 * s + n - 1 := by omega
        rw [heq]
        exact hPt n s hn hs
      have hq : ∀ s : ℕ, 1 ≤ s → 2 * Q n s + P n s ≤ Q n (3 * s + (n - 1)) := by
        intro s hs
        have heq : 3 * s + (n - 1) = 3 * s + n - 1 := by omega
        rw [heq]
        exact hQt n s hn hs
      obtain ⟨l, hl, hpl, hql, hcap, hpi, hqi, hplo, hqlo⟩ :=
        exists_common_row_slope (fun s hs => hPpos n s hn hs)
          (fun s hs => hQpos n s hn hs) (hPd n hn) (hQd n hn) hp hq
      refine ⟨l, fun _ => ⟨hl, hpl, hql, ?_, hpi, hqi, hplo, hqlo⟩⟩
      intro s hs
      have h := hcap s hs
      rw [Nat.cast_sub hn, Nat.cast_one] at h
      convert h using 1
      ring
    · exact ⟨0, fun hn' => False.elim (hn hn')⟩
  choose L hL using hrow
  exact ⟨L, hL⟩

/-- First-coordinate monotonicity passes to the limiting row slopes. -/
theorem slope_monotone_of_profile_monotone {P : ℕ → ℕ → ℝ} {L : ℕ → ℝ}
    (hmono : ∀ n n' s : ℕ, 1 ≤ n → n ≤ n' → 1 ≤ s → P n s ≤ P n' s)
    (hlim : ∀ n : ℕ, 1 ≤ n →
      Tendsto (fun s : ℕ => P n s / (s : ℝ)) atTop (𝓝 (L n))) :
    ∀ n n' : ℕ, 1 ≤ n → n ≤ n' → L n ≤ L n' := by
  intro n n' hn hnn'
  have hn' : 1 ≤ n' := le_trans hn hnn'
  have he : ∀ᶠ s : ℕ in atTop, P n s / (s : ℝ) ≤ P n' s / (s : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with s hs
    exact div_le_div_of_nonneg_right (hmono n n' s hn hnn' hs) (Nat.cast_nonneg s)
  exact le_of_tendsto_of_tendsto (hlim n hn) (hlim n' hn') he

#print axioms exists_common_profile_slopes
#print axioms long_increment_of_lower

end Matmul.DiscreteSlopes
