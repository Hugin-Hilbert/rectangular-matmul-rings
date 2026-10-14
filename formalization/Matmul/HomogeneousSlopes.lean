import Mathlib

namespace Matmul.Homogeneous

open Filter
open scoped Topology

/-- Positivity on the open half line supplies the missing nonnegative intercept. -/
theorem concave_ratio_antitone {f : ℝ → ℝ}
    (hf : ConcaveOn ℝ (Set.Ioi 0) f) (hp : ∀ s, 0 < s → 0 < f s) :
    AntitoneOn (fun s => f s / s) (Set.Ioi 0) := by
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with rfl | hxy
  · rfl
  have hevent : ∀ᶠ z : ℝ in 𝓝[>] (0 : ℝ),
      (y - z) * f x ≥ (x - z) * f y := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hx).filter_mono nhdsWithin_le_nhds] with z hz hzx
    have h := hf.neg.secant_mono_aux1 hz hy hzx hxy
    simp only [Pi.neg_apply] at h
    have hzpos := hp z hz
    nlinarith [mul_pos (sub_pos.mpr hxy) hzpos]
  have hid : Tendsto (fun z : ℝ => z) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hleft := ((tendsto_const_nhds (x := y)).sub hid).mul_const (f x)
  have hright := ((tendsto_const_nhds (x := x)).sub hid).mul_const (f y)
  have hbound : x * f y ≤ y * f x := by
    simpa using le_of_tendsto_of_tendsto hright hleft hevent
  exact (div_le_div_iff₀ hy hx).mpr (by nlinarith)

/-- A positive concave real row has a finite nonnegative asymptotic slope. -/
theorem exists_real_concave_slope {f : ℝ → ℝ}
    (hf : ConcaveOn ℝ (Set.Ioi 0) f) (hp : ∀ s, 0 < s → 0 < f s) :
    ∃ L : ℝ, 0 ≤ L ∧
      Tendsto (fun s : ℝ => f s / s) atTop (𝓝 L) ∧
      (∀ s, 0 < s → L * s ≤ f s) ∧
      (∀ x y, 0 < x → x < y → L * (y - x) ≤ f y - f x) := by
  have ha := concave_ratio_antitone hf hp
  let u : ℝ → ℝ := fun s => f (max s 1) / max s 1
  have hu : Antitone u := by
    intro x y hxy
    apply ha
    · exact lt_of_lt_of_le (zero_lt_one : (0 : ℝ) < 1) (le_max_right _ _)
    · exact lt_of_lt_of_le (zero_lt_one : (0 : ℝ) < 1) (le_max_right _ _)
    · exact max_le_max_right _ hxy
  have hup : ∀ s, 0 ≤ u s := by
    intro s
    have hs : 0 < max s 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    exact le_of_lt (div_pos (hp _ hs) hs)
  have hbdd : BddBelow (Set.range u) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨s, rfl⟩
    exact hup s
  let L : ℝ := ⨅ s, u s
  have hlimu : Tendsto u atTop (𝓝 L) := tendsto_atTop_ciInf hu hbdd
  have hlim : Tendsto (fun s : ℝ => f s / s) atTop (𝓝 L) := by
    apply hlimu.congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
    simp [u, max_eq_left hs]
  refine ⟨L, ge_of_tendsto hlimu (Eventually.of_forall hup), hlim, ?_, ?_⟩
  · intro s hs
    have he : ∀ᶠ z : ℝ in atTop, f z / z ≤ f s / s := by
      filter_upwards [eventually_ge_atTop s] with z hz
      exact ha hs (lt_of_lt_of_le hs hz) hz
    have h := le_of_tendsto hlim he
    exact (le_div_iff₀ hs).mp h
  · intro x y hx hxy
    have hy : 0 < y := lt_trans hx hxy
    have he : ∀ᶠ z : ℝ in atTop,
        (y - x) * (f z / z - f y / z) ≤
          (1 - y / z) * (f y - f x) := by
      filter_upwards [eventually_gt_atTop y] with z hz
      have hzpos : 0 < z := lt_trans hy hz
      have h := hf.neg.secant_mono_aux1 hx hzpos hxy hz
      simp only [Pi.neg_apply] at h
      have hz0 : z ≠ 0 := ne_of_gt hzpos
      field_simp [hz0]
      nlinarith
    have hzfy : Tendsto (fun z : ℝ => f y / z) atTop (𝓝 0) :=
      tendsto_id.const_div_atTop (f y)
    have hzy : Tendsto (fun z : ℝ => y / z) atTop (𝓝 0) :=
      tendsto_id.const_div_atTop y
    have hleft := (hlim.sub hzfy).const_mul (y - x)
    have hright := ((tendsto_const_nhds (x := (1 : ℝ))).sub hzy).mul_const (f y - f x)
    have h := le_of_tendsto_of_tendsto hleft hright he
    simpa [mul_comm] using h

/-- The asymmetric tripling inequality compares the two limiting slopes. -/
theorem slope_le_of_coupled_tripling {f g : ℝ → ℝ} {L M : ℝ}
    (hf : Tendsto (fun s : ℝ => f s / s) atTop (𝓝 L))
    (hg : Tendsto (fun s : ℝ => g s / s) atTop (𝓝 M))
    (htrip : ∀ s, 0 < s → 2 * f s + g s ≤ f (3 * s + 1)) : M ≤ L := by
  have hmap : Tendsto (fun s : ℝ => 3 * s + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1
      (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 3))
  have hzero : Tendsto (fun s : ℝ => 1 / s) atTop (𝓝 (0 : ℝ)) :=
    tendsto_id.const_div_atTop 1
  have hfactor : Tendsto (fun s : ℝ => (3 * s + 1) / s) atTop (𝓝 (3 : ℝ)) := by
    have h := (tendsto_const_nhds (x := (3 : ℝ))).add hzero
    simp only [add_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    field_simp [ne_of_gt hs]
  have hright : Tendsto (fun s : ℝ => f (3 * s + 1) / s) atTop (𝓝 (3 * L)) := by
    have h := (hf.comp hmap).mul hfactor
    simp only [mul_comm L 3] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    have ht : 3 * s + 1 ≠ 0 := by linarith
    dsimp only [Function.comp_def]
    field_simp [ne_of_gt hs, ht]
  have hleft : Tendsto (fun s : ℝ => (2 * f s + g s) / s) atTop
      (𝓝 (2 * L + M)) := by
    have h := (hf.const_mul 2).add hg
    apply h.congr'
    exact Eventually.of_forall fun s => by simp [add_div, mul_div_assoc]
  have he : ∀ᶠ s : ℝ in atTop, (2 * f s + g s) / s ≤ f (3 * s + 1) / s := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    exact div_le_div_of_nonneg_right (htrip s hs) hs.le
  have h := le_of_tendsto_of_tendsto hleft hright he
  linarith

/-- The exact shifted real tripling orbit. -/
noncomputable def realTriplingOrbit (s : ℝ) (j : ℕ) : ℝ :=
  (3 : ℝ) ^ j * (s + 1 / 2) - 1 / 2

@[simp] theorem realTriplingOrbit_zero (s : ℝ) : realTriplingOrbit s 0 = s := by
  simp [realTriplingOrbit]

theorem realTriplingOrbit_succ (s : ℝ) (j : ℕ) :
    realTriplingOrbit s (j + 1) = 3 * realTriplingOrbit s j + 1 := by
  simp [realTriplingOrbit, pow_succ]
  ring

theorem realTriplingOrbit_pos {s : ℝ} (hs : 0 < s) (j : ℕ) :
    0 < realTriplingOrbit s j := by
  induction j with
  | zero => simpa using hs
  | succ j ih => rw [realTriplingOrbit_succ]; linarith

theorem realTriplingOrbit_tendsto {s : ℝ} (hs : 0 < s) :
    Tendsto (realTriplingOrbit s) atTop atTop := by
  have hp : Tendsto (fun j : ℕ => (3 : ℝ) ^ j) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hc : 0 < s + 1 / 2 := by linarith
  have h := tendsto_atTop_add_const_right atTop (-(1 / 2 : ℝ))
    (hp.atTop_mul_const hc)
  change Tendsto (fun j : ℕ => (3 : ℝ) ^ j * (s + 1 / 2) - 1 / 2) atTop atTop
  simpa only [sub_eq_add_neg] using h

/-- Shifted tripling converts an asymptotic slope into a finite affine bound. -/
theorem real_tripling_le_affine_slope {f : ℝ → ℝ} {A s : ℝ}
    (hs : 0 < s)
    (htrip : ∀ t, 0 < t → 3 * f t ≤ f (3 * t + 1))
    (hlim : Tendsto (fun t : ℝ => f t / t) atTop (𝓝 A)) :
    f s ≤ (s + 1 / 2) * A := by
  have hiter (j : ℕ) : (3 : ℝ) ^ j * f s ≤ f (realTriplingOrbit s j) := by
    induction j with
    | zero => simp
    | succ j ih =>
        have hstep := htrip _ (realTriplingOrbit_pos hs j)
        rw [← realTriplingOrbit_succ] at hstep
        rw [pow_succ]
        nlinarith
  have hpow : Tendsto (fun j : ℕ => (3 : ℝ) ^ j) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hzero : Tendsto (fun j : ℕ => (1 / 2 : ℝ) / (3 : ℝ) ^ j)
      atTop (𝓝 0) := hpow.const_div_atTop _
  have hfactor : Tendsto (fun j : ℕ => realTriplingOrbit s j / (3 : ℝ) ^ j)
      atTop (𝓝 (s + 1 / 2)) := by
    have h := (tendsto_const_nhds (x := s + 1 / 2)).sub hzero
    simp only [sub_zero] at h
    apply h.congr'
    apply Eventually.of_forall
    intro j
    dsimp [realTriplingOrbit]
    field_simp
  have hprofile : Tendsto (fun j : ℕ => f (realTriplingOrbit s j) / (3 : ℝ) ^ j)
      atTop (𝓝 ((s + 1 / 2) * A)) := by
    have h := (hlim.comp (realTriplingOrbit_tendsto hs)).mul hfactor
    rw [mul_comm A] at h
    apply h.congr'
    apply Eventually.of_forall
    intro j
    have hj := ne_of_gt (realTriplingOrbit_pos hs j)
    dsimp only [Function.comp_def]
    field_simp [hj]
  have he : ∀ᶠ j : ℕ in atTop, f s ≤ f (realTriplingOrbit s j) / (3 : ℝ) ^ j := by
    apply Eventually.of_forall
    intro j
    apply (le_div_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 3) j)).mpr
    simpa only [mul_comm] using hiter j
  exact ge_of_tendsto hprofile he

/-- Positive concave coupled rows have one positive slope and precise affine bounds. -/
theorem exists_common_slope {f g : ℝ → ℝ}
    (hf : ConcaveOn ℝ (Set.Ioi 0) f) (hg : ConcaveOn ℝ (Set.Ioi 0) g)
    (hfp : ∀ s, 0 < s → 0 < f s) (hgp : ∀ s, 0 < s → 0 < g s)
    (htf : ∀ s, 0 < s → 2 * f s + g s ≤ f (3 * s + 1))
    (htg : ∀ s, 0 < s → 2 * g s + f s ≤ g (3 * s + 1)) :
    ∃ L : ℝ, 0 < L ∧
      Tendsto (fun s : ℝ => f s / s) atTop (𝓝 L) ∧
      Tendsto (fun s : ℝ => g s / s) atTop (𝓝 L) ∧
      (∀ s, 0 < s → f s + g s ≤ L * (2 * s + 1)) ∧
      (∀ s, 0 < s → L * s ≤ f s) ∧
      (∀ s, 0 < s → L * s ≤ g s) ∧
      (∀ x y, 0 < x → x < y → L * (y - x) ≤ f y - f x) ∧
      (∀ x y, 0 < x → x < y → L * (y - x) ≤ g y - g x) := by
  obtain ⟨L, hL, hlf, hlowf, hincf⟩ := exists_real_concave_slope hf hfp
  obtain ⟨M, hM, hlg, hlowg, hincg⟩ := exists_real_concave_slope hg hgp
  have heq : M = L := le_antisymm
    (slope_le_of_coupled_tripling hlf hlg htf)
    (slope_le_of_coupled_tripling hlg hlf htg)
  subst M
  have hsumlim : Tendsto (fun s : ℝ => (f s + g s) / s) atTop (𝓝 (2 * L)) := by
    have h := hlf.add hlg
    convert h using 1 <;> simp [add_div, two_mul]
  have hsumtrip : ∀ s, 0 < s → 3 * (f s + g s) ≤ f (3 * s + 1) + g (3 * s + 1) := by
    intro s hs
    have h1 := htf s hs
    have h2 := htg s hs
    linarith
  have hbound (s : ℝ) (hs : 0 < s) : f s + g s ≤ L * (2 * s + 1) := by
    have h := real_tripling_le_affine_slope hs hsumtrip hsumlim
    nlinarith
  have hLpos : 0 < L := by
    have h := hbound 1 (by norm_num)
    have h1 := hfp 1 (by norm_num)
    have h2 := hgp 1 (by norm_num)
    nlinarith
  exact ⟨L, hLpos, hlf, hlg, hbound, hlowf, hlowg, hincf, hincg⟩

/-- An increment lower bound makes the affine residual increasing. -/
theorem residual_monotone {f : ℝ → ℝ} {L : ℝ}
    (hinc : ∀ x y, 0 < x → x < y → L * (y - x) ≤ f y - f x) :
    MonotoneOn (fun s => f s - L * s) (Set.Ioi 0) := by
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with rfl | hxy
  · rfl
  · have h := hinc x y hx hxy
    dsimp
    nlinarith

/-- Normalizing the first row at one gives the two distinct intercept bounds. -/
theorem normalized_row_affine_bounds {f g : ℝ → ℝ} {L : ℝ}
    (hunit : f 1 = 1)
    (hcap : ∀ s, 0 < s → f s + g s ≤ L * (2 * s + 1))
    (hlowg : ∀ s, 0 < s → L * s ≤ g s)
    (hincf : ∀ x y, 0 < x → x < y → L * (y - x) ≤ f y - f x)
    (hincg : ∀ x y, 0 < x → x < y → L * (y - x) ≤ g y - g x) :
    (∀ s, 0 < s → f s ≤ L * s + L) ∧
    (∀ s, 0 < s → g s ≤ L * s + 2 * L - 1) := by
  have hmf := residual_monotone hincf
  have hmg := residual_monotone hincg
  constructor
  · intro s hs
    have hc := hcap s hs
    have hl := hlowg s hs
    nlinarith
  · intro s hs
    by_cases hsmall : s ≤ 1
    · have hm := hmg hs (by norm_num : (1 : ℝ) ∈ Set.Ioi 0) hsmall
      have hc := hcap 1 (by norm_num)
      rw [hunit] at hc
      dsimp at hm
      nlinarith
    · have hlarge : 1 ≤ s := le_of_lt (lt_of_not_ge hsmall)
      have hm := hmf (by norm_num : (1 : ℝ) ∈ Set.Ioi 0) hs hlarge
      have hc := hcap s hs
      dsimp at hm
      rw [hunit] at hm
      nlinarith

#print axioms exists_common_slope
#print axioms normalized_row_affine_bounds

end Matmul.Homogeneous
