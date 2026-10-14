import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic
import Matmul.HomogeneousSlopes
import Matmul.HomogeneousIncrements

/-!
Finite secant proofs for the homogeneous profiles in the rectangular
shared-leg argument. Only elementary explicit functions are differentiated;
the tensor profiles themselves need not be differentiable.
-/

namespace Matmul.HomogeneousProfiles

open Filter
open scoped Topology

/-- An explicit comparison on the right of zero bounds its derivative. -/
theorem deriv_le_of_right_comparison {f : ℝ → ℝ} {d : ℝ}
    (hd : HasDerivAt f d 0) (hzero : f 0 = 1)
    (hbound : ∀ᶠ t in 𝓝[>] (0 : ℝ), f t ≤ 1 + t) : d ≤ 1 := by
  have hlim := hd.tendsto_slope_zero_right
  have hb : ∀ᶠ t in 𝓝[>] (0 : ℝ), t⁻¹ • (f (0 + t) - f 0) ≤ (1 : ℝ) := by
    filter_upwards [hbound, self_mem_nhdsWithin] with t ht hpos
    simp only [Set.mem_Ioi] at hpos
    simp only [zero_add, hzero, smul_eq_mul]
    have := mul_le_mul_of_nonneg_left (show f t - 1 ≤ t by linarith)
      (inv_nonneg.mpr hpos.le)
    simpa [inv_mul_cancel₀ (ne_of_gt hpos)] using this
  exact le_of_tendsto hlim hb

/-- Homogeneity and symmetry constrain any common secant lower bound. -/
theorem slope_le_half_degree {f : ℝ → ℝ} {D L : ℝ}
    (hunit : f 1 = 1)
    (hrecip : ∀ s, 0 < s → f s = s ^ D * f (1 / s))
    (hinc : ∀ x y, 0 < x → x < y → L * (y - x) ≤ f y - f x) :
    L ≤ D / 2 := by
  let H : ℝ → ℝ := fun t => (1 + t) ^ D * (1 - L + L / (1 + t))
  have hp : HasDerivAt (fun t : ℝ => (1 + t) ^ D) D 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).const_add 1).rpow_const
      (p := D) (Or.inl (by norm_num)) using 1 <;> norm_num
  have hi : HasDerivAt (fun t : ℝ => 1 / (1 + t)) (-1) 0 := by
    simpa only [one_div, Pi.inv_def, id_eq, add_zero, one_pow, div_one] using
      (((hasDerivAt_id (0 : ℝ)).const_add (1 : ℝ)).inv (by norm_num))
  have hh : HasDerivAt H (D - L) 0 := by
    convert hp.mul ((hi.const_mul L).const_add (1 - L)) using 1 <;>
      first | rfl | (funext t; dsimp [H]; ring) | (norm_num [H]; ring)
  have hlim := hh.tendsto_slope_zero_right
  have hb : ∀ᶠ t in 𝓝[>] (0 : ℝ), L ≤ t⁻¹ • (H (0 + t) - H 0) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht : 0 < t := ht
    have hs : 0 < 1 + t := by linarith
    have hs1 : 1 < 1 + t := by linarith
    have hi0 : 0 < 1 / (1 + t) := by positivity
    have hi1 : 1 / (1 + t) < 1 := (div_lt_iff₀ hs).2 (by linarith)
    have hlo := hinc 1 (1 + t) (by norm_num) hs1
    have hhi := hinc (1 / (1 + t)) 1 hi0 hi1
    rw [hunit] at hlo hhi
    simp only [mul_sub, mul_one, mul_one_div] at hhi
    have hineq : 1 + L * t ≤ H t := by
      rw [hrecip (1 + t) hs] at hlo
      have hmul := mul_le_mul_of_nonneg_left
        (show f (1 / (1 + t)) ≤ 1 - L + L / (1 + t) by nlinarith)
        (Real.rpow_pos_of_pos hs D).le
      dsimp [H]
      linarith
    simp only [zero_add, H, add_zero, Real.one_rpow, div_one, one_mul,
      sub_add_cancel, smul_eq_mul]
    have hmul := mul_le_mul_of_nonneg_left
      (show L * t ≤ H t - 1 by linarith) (inv_nonneg.mpr ht.le)
    simpa [H, mul_left_comm, inv_mul_cancel₀ ht.ne'] using hmul
  have hl : L ≤ D - L := ge_of_tendsto hlim hb
  linarith

/-- Positivity supplies the missing nonnegative endpoint at zero in the
doubling estimate for a concave profile on the open positive ray. -/
theorem positive_concave_doubling {f : ℝ → ℝ}
    (hf : ConcaveOn ℝ (Set.Ioi 0) f) (hpos : ∀ x, 0 < x → 0 < f x)
    {x : ℝ} (hx : 0 < x) : f (2 * x) ≤ 2 * f x := by
  have hb : ∀ᶠ e in 𝓝[>] (0 : ℝ),
      (x - e) * (f (2 * x) - f x) ≤ x * f x := by
    filter_upwards [(eventually_lt_nhds hx).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with e hex he0
    have he0 : 0 < e := he0
    have hs := hf.slope_anti_adjacent he0 (show 0 < 2 * x by positivity)
      hex (show x < 2 * x by linarith)
    have hd : 0 < x - e := sub_pos.mpr hex
    have hs' : (x - e) * (f (2 * x) - f x) ≤ x * (f x - f e) := by
      simp only [show 2*x-x=x by ring] at hs
      have hs' := (div_le_div_iff₀ hx hd).1 hs
      nlinarith
    have := hpos e he0
    nlinarith
  have hlim : Tendsto (fun e : ℝ => (x - e) * (f (2*x) - f x))
      (𝓝[>] 0) (𝓝 (x * (f (2*x) - f x))) := by
    simpa using (((tendsto_const_nhds : Tendsto (fun _ : ℝ => x)
      (𝓝[>] 0) (𝓝 x)).sub
      (tendsto_id.mono_left nhdsWithin_le_nhds)).mul_const (f (2*x) - f x))
  have hs := le_of_tendsto hlim hb
  nlinarith

/-- Separate positive concavity bounds a homogeneous degree by two. -/
theorem degree_le_two {P : ℝ → ℝ → ℝ} {D : ℝ}
    (hpos : ∀ r s, 0 < r → 0 < s → 0 < P r s)
    (hc1 : ∀ s, 0 < s → ConcaveOn ℝ (Set.Ioi 0) (fun r => P r s))
    (hc2 : ∀ r, 0 < r → ConcaveOn ℝ (Set.Ioi 0) (P r))
    (hhom : ∀ c r s, 0 < c → 0 < r → 0 < s →
      P (c*r) (c*s) = c ^ D * P r s) : D ≤ 2 := by
  have h1 := positive_concave_doubling (hc1 2 (by norm_num))
    (fun r hr => hpos r 2 hr (by norm_num)) (x := 1) (by norm_num)
  have h2 := positive_concave_doubling (hc2 1 (by norm_num))
    (fun s hs => hpos 1 s (by norm_num) hs) (x := 1) (by norm_num)
  have hp := hpos 1 1 (by norm_num) (by norm_num)
  have hh := hhom 2 1 1 (by norm_num) (by norm_num) (by norm_num)
  norm_num at h1 h2 hh
  have hpow : (2 : ℝ) ^ D ≤ (2 : ℝ) ^ (2 : ℝ) := by
    rw [Real.rpow_two]
    nlinarith
  exact (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).1 hpow

/-- Concavity transfers a far secant lower bound to a nearer secant. -/
theorem concave_increment_of_far_increment {f : ℝ → ℝ}
    (hf : ConcaveOn ℝ (Set.Ioi 0) f) {x d h K : ℝ}
    (hx : 0 < x) (hd : 0 < d) (hh : 0 < h) (hhd : h < d)
    (hfar : K * d ≤ f (x + d) - f x) :
    K * h ≤ f (x + h) - f x := by
  have hs := hf.neg.secant_mono hx (show 0 < x+h by linarith)
    (show 0 < x+d by linarith) (show x+h ≠ x by linarith)
    (show x+d ≠ x by linarith) (show x+h ≤ x+d by linarith)
  dsimp at hs
  simp only [add_sub_cancel_left] at hs
  have hs' : (f (x+d) - f x) * h ≤ (f (x+h) - f x) * d := by
    have hs' := (div_le_div_iff₀ hh hd).1 hs
    nlinarith
  nlinarith

/-- Passing a positive powered inequality back to the original profile. -/
theorem recover_power_increment {x y p z : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hp : 0 < p) (hz : 0 ≤ z)
    (hpow : x ^ (1/p) * z ≤ y ^ (1/p)) : x * z ^ p ≤ y := by
  have h := Real.rpow_le_rpow (mul_nonneg (Real.rpow_nonneg hx.le _) hz)
    hpow hp.le
  rw [Real.mul_rpow (Real.rpow_nonneg hx.le _) hz] at h
  simpa only [one_div, Real.rpow_inv_rpow hx.le hp.ne',
    Real.rpow_inv_rpow hy.le hp.ne'] using h

/-- The finite first-coordinate increment forced by self-tripling. -/
theorem first_coordinate_increment {U : ℝ → ℝ → ℝ} {b r s h : ℝ}
    (hb : 0 < b) (hr : 0 < r) (hs : 0 < s) (hh : 0 < h)
    (hhd : h < 2*r+s)
    (hpos : ∀ x y, 0 < x → 0 < y → 0 < U x y)
    (hc : ConcaveOn ℝ (Set.Ioi 0) (fun x => U x s ^ (1/b)))
    (ht : 3 * U r s ^ (1/b) ≤ U (3*r+s) s ^ (1/b)) :
    U r s * (1+2*h/(2*r+s)) ^ b ≤ U (r+h) s := by
  have hd : 0 < 2*r+s := by positivity
  have hp : 0 < U r s ^ (1/b) := Real.rpow_pos_of_pos (hpos r s hr hs) _
  have hfar : (2 * U r s ^ (1/b) / (2*r+s)) * (2*r+s) ≤
      U (r+(2*r+s)) s ^ (1/b) - U r s ^ (1/b) := by
    rw [div_mul_cancel₀ _ hd.ne', show r+(2*r+s)=3*r+s by ring]
    linarith
  have hsec := concave_increment_of_far_increment hc hr hd hh hhd hfar
  apply recover_power_increment (hpos r s hr hs)
    (hpos (r+h) s (by linarith) hs) hb (by positivity)
  have heq : U r s ^ (1/b) * (2*h/(2*r+s)) =
      (2 * U r s ^ (1/b) / (2*r+s))*h := by ring
  nlinarith

/-- The derivative of the explicit rational increment factor. -/
theorem hasDerivAt_fraction_factor {n d e : ℝ} (hd : d ≠ 0) :
    HasDerivAt (fun t : ℝ => 1+n*t/(d+e*t)) (n/d) 0 := by
  have hn : HasDerivAt (fun t : ℝ => n*t) n 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul n
  have hden : HasDerivAt (fun t : ℝ => d+e*t) e 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul e).const_add d
  convert (hn.div hden (by simpa using hd)).const_add 1 using 1 <;>
    first | rfl | (norm_num; field_simp [hd])

/-- Finite secants in both coordinates, together with degree-one homogeneity,
give the Euler-type parameter inequality. The only differentiated expression
is a product of explicit rational powers. -/
theorem ratio_inequality_of_finite_increments {U : ℝ → ℝ → ℝ} {a b c r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hc : 0 ≤ c)
    (hpos : 0 < U r s)
    (hhom : ∀ t, 0 < t → U (t*r) (t*s) = t*U r s)
    (hsecond : ∀ h, 0 < h →
      U r s*(1+h/(s+c*r))^a ≤ U r (s+h))
    (hfirst : ∀ t h, 0 < t → 0 < h → h < 2*r+t →
      U r t*(1+2*h/(2*r+t))^b ≤ U (r+h) t) :
    a*s/(s+c*r)+2*b*r/(2*r+s) ≤ 1 := by
  have hd1 : 0 < s+c*r := by positivity
  have hd2 : 0 < 2*r+s := by positivity
  let A : ℝ → ℝ := fun t => 1+s*t/(s+c*r)
  let B : ℝ → ℝ := fun t => 1+2*r*t/(2*r+s+s*t)
  let F : ℝ → ℝ := fun t => A t ^ a * B t ^ b
  have hAd : HasDerivAt A (s/(s+c*r)) 0 := by
    convert hasDerivAt_fraction_factor (n:=s) (d:=s+c*r) (e:=0) hd1.ne' using 1
    first | rfl | (funext t; dsimp [A]; ring)
  have hBd : HasDerivAt B (2*r/(2*r+s)) 0 :=
    hasDerivAt_fraction_factor hd2.ne'
  have hFd : HasDerivAt F (a*s/(s+c*r)+2*b*r/(2*r+s)) 0 := by
    convert (hAd.rpow_const (p:=a) (Or.inl (by simp [A]))).mul
      (hBd.rpow_const (p:=b) (Or.inl (by simp [B]))) using 1 <;>
      first | rfl | (simp [A, B]; ring)
  apply deriv_le_of_right_comparison hFd
  · simp [F, A, B]
  · filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono
        nhdsWithin_le_nhds] with t ht ht1
    have ht : 0 < t := ht
    have hs' : 0 < s+t*s := by positivity
    have hsec := hsecond (t*s) (by positivity)
    have hfir := hfirst (s+t*s) (t*r) hs' (by positivity) (by nlinarith)
    have hBp : 0 ≤ B t ^ b := Real.rpow_nonneg (by dsimp [B]; positivity) _
    have hsec' : U r s * A t ^ a ≤ U r (s+t*s) := by
      simpa [A, mul_comm] using hsec
    have hfir' : U r (s+t*s) * B t ^ b ≤ U (r+t*r) (s+t*s) := by
      simpa [B, mul_assoc, mul_left_comm, mul_comm, add_assoc] using hfir
    have hh := hhom (1+t) (by linarith)
    have htgt : U r s * F t ≤ (1+t)*U r s := by
      have hm := mul_le_mul_of_nonneg_right hsec' hBp
      dsimp [F]
      rw [show r+t*r=(1+t)*r by ring,
        show s+t*s=(1+t)*s by ring, hh] at hfir'
      rw [show s+t*s=(1+t)*s by ring] at hm
      nlinarith
    exact (mul_le_mul_iff_left₀ hpos).1 (by simpa [mul_comm] using htgt)

/-- Exact algebraic optimization of the inequality at all positive ratios. -/
theorem parabolic_cap_of_ratio_inequality {a b : ℝ}
    (ha : 1/2 ≤ a) (ha1 : a ≤ 1) (hb : b ≤ 1)
    (hratio : ∀ r s : ℝ, 0 < r → 0 < s →
      a*s/(s+2*(1-a)*r)+2*b*r/(2*r+s) ≤ 1) : b ≤ 4*a*(1-a) := by
  by_cases hhalf : a = 1/2
  · norm_num [hhalf]
    exact hb
  by_cases hone : a = 1
  · have h := hratio 1 1 (by norm_num) (by norm_num)
    norm_num [hone] at h ⊢
    linarith
  have hahalf : 1/2 < a := lt_of_le_of_ne ha (Ne.symm hhalf)
  have halt : a < 1 := lt_of_le_of_ne ha1 hone
  have ha2 : 0 < 2*a-1 := by linarith
  have hx : 0 < 1 / (2*(2*a-1)) := by positivity
  have h := hratio (1/(2*(2*a-1))) 1 hx (by norm_num)
  have hd1 : 0 < 1+2*(1-a)*(1/(2*(2*a-1))) := by
    have hA : 0 < 1-a := by linarith
    positivity
  have hd2 : 0 < 2*(1/(2*(2*a-1)))+1 := by positivity
  have hapos : 0 < 2*a := by linarith
  have heq : a*1/(1+2*(1-a)*(1/(2*(2*a-1))))+
      2*b*(1/(2*(2*a-1)))/(2*(1/(2*(2*a-1)))+1) =
      (2*a-1)+b/(2*a) := by
    have hden1 : 1+2*(1-a)*(1/(2*(2*a-1))) = a/(2*a-1) := by
      field_simp [ha2.ne']
      ring
    have hden2 : 2*(1/(2*(2*a-1)))+1 = 2*a/(2*a-1) := by
      field_simp [ha2.ne']
      ring
    have hnum : 2*b*(1/(2*(2*a-1))) = b/(2*a-1) := by
      field_simp [ha2.ne']
    rw [hden1, hden2]
    simp only [mul_one, hnum, div_div_cancel₀ (show a ≠ 0 by linarith),
      div_div_div_cancel_right₀ ha2.ne']
  rw [heq] at h
  have hdiv : b/(2*a) ≤ 2-2*a := by linarith
  have hmul := (div_le_iff₀ hapos).1 hdiv
  nlinarith

/-- The normalized continuum hypotheses from the oriented tensor profiles.
The powers are on real positive values, and all concavity assertions concern
the open positive ray. No slope, intercept, or parameter bound is assumed. -/
structure HomogeneousData (V U : ℝ → ℝ → ℝ) (a b : ℝ) : Prop where
  a_pos : 0 < a
  a_le_one : a ≤ 1
  b_nonneg : 0 ≤ b
  b_le_one : b ≤ 1
  V_pos : ∀ r s, 0 < r → 0 < s → 0 < V r s
  U_pos : ∀ r s, 0 < r → 0 < s → 0 < U r s
  V_hom : ∀ c r s, 0 < c → 0 < r → 0 < s → V (c*r) (c*s) = c*V r s
  U_hom : ∀ c r s, 0 < c → 0 < r → 0 < s → U (c*r) (c*s) = c*U r s
  V_symm : ∀ r s, 0 < r → 0 < s → V r s = V s r
  V_unit : V 1 1 = 1
  V_concave_first : ∀ s, 0 < s →
    ConcaveOn ℝ (Set.Ioi 0) (fun r => V r s ^ (1/a))
  V_concave_second : ∀ r, 0 < r →
    ConcaveOn ℝ (Set.Ioi 0) (fun s => V r s ^ (1/a))
  U_concave_second : ∀ r, 0 < r →
    ConcaveOn ℝ (Set.Ioi 0) (fun s => U r s ^ (1/a))
  V_tripling : ∀ r s, 0 < r → 0 < s →
    2*V r s ^ (1/a)+U r s ^ (1/a) ≤ V r (3*s+r) ^ (1/a)
  U_tripling : ∀ r s, 0 < r → 0 < s →
    2*U r s ^ (1/a)+V r s ^ (1/a) ≤ U r (3*s+r) ^ (1/a)
  U_concave_first : 0 < b → ∀ s, 0 < s →
    ConcaveOn ℝ (Set.Ioi 0) (fun r => U r s ^ (1/b))
  U_self_tripling : 0 < b → ∀ r s, 0 < r → 0 < s →
    3*U r s ^ (1/b) ≤ U (3*r+s) s ^ (1/b)

/-- The parabolic cap follows from the exact normalized continuum profile
hypotheses, including the endpoint values of both parameters. -/
theorem parameter_cap {V U : ℝ → ℝ → ℝ} {a b : ℝ}
    (H : HomogeneousData V U a b) : b ≤ 4*a*(1-a) := by
  by_cases hb0 : b = 0
  · rw [hb0]
    exact mul_nonneg (mul_nonneg (by norm_num) H.a_pos.le)
      (sub_nonneg.mpr H.a_le_one)
  have hb : 0 < b := lt_of_le_of_ne H.b_nonneg (Ne.symm hb0)
  let P : ℝ → ℝ → ℝ := fun r s => V r s ^ (1/a)
  let Q : ℝ → ℝ → ℝ := fun r s => U r s ^ (1/a)
  have hPpos : ∀ r s, 0 < r → 0 < s → 0 < P r s := by
    intro r s hr hs
    exact Real.rpow_pos_of_pos (H.V_pos r s hr hs) _
  have hQpos : ∀ r s, 0 < r → 0 < s → 0 < Q r s := by
    intro r s hr hs
    exact Real.rpow_pos_of_pos (H.U_pos r s hr hs) _
  have hPunit : P 1 1 = 1 := by simp [P, H.V_unit]
  have hPhom : ∀ c r s, 0 < c → 0 < r → 0 < s →
      P (c*r) (c*s) = c^(1/a)*P r s := by
    intro c r s hc hr hs
    dsimp [P]
    rw [H.V_hom c r s hc hr hs, Real.mul_rpow hc.le (H.V_pos r s hr hs).le]
  have hD : 1/a ≤ 2 := degree_le_two hPpos
    H.V_concave_first H.V_concave_second hPhom
  have ha : 1/2 ≤ a := by
    have hmul := (div_le_iff₀ H.a_pos).1 hD
    linarith
  obtain ⟨L, hL, _hLP, _hLQ, hsum, _hlowP, hlowQ, hincP, hincQ⟩ :=
    Matmul.Homogeneous.exists_common_slope
      (H.V_concave_second 1 (by norm_num))
      (H.U_concave_second 1 (by norm_num))
      (hPpos 1 · (by norm_num) ·) (hQpos 1 · (by norm_num) ·)
      (H.V_tripling 1 · (by norm_num) ·) (H.U_tripling 1 · (by norm_num) ·)
  have hrecip : ∀ s, 0 < s → P 1 s = s^(1/a)*P 1 (1/s) := by
    intro s hs
    have hh := hPhom s (1/s) 1 hs (by positivity) (by norm_num)
    have hcancel : s*(1/s)=1 := by field_simp
    rw [hcancel, mul_one] at hh
    rw [show P (1/s) 1 = P 1 (1/s) by
      dsimp [P]
      rw [H.V_symm (1/s) 1 (by positivity) (by norm_num)]] at hh
    exact hh
  have hLupper : L ≤ (1/a)/2 := slope_le_half_degree hPunit hrecip hincP
  have hLa : 2*a*L ≤ 1 := by
    have hmul := mul_le_mul_of_nonneg_right hLupper H.a_pos.le
    have heq : ((1/a)/2)*a = 1/2 := by field_simp
    rw [heq] at hmul
    nlinarith
  obtain ⟨_hPupper, hQupper⟩ := Matmul.Homogeneous.normalized_row_affine_bounds
    hPunit hsum hlowQ hincP hincQ
  have hQcap : ∀ s, 0 < s → U 1 s^(1/a) ≤ L*(s+2*(1-a)) := by
    intro s hs
    have hh := hQupper s hs
    nlinarith
  have hc : 0 ≤ 2*(1-a) := by linarith [H.a_le_one]
  have hUrow : ∀ r s, 0 < r → 0 < s → U r s = r*U 1 (s/r) := by
    intro r s hr hs
    have hh := H.U_hom r 1 (s/r) hr (by norm_num) (div_pos hs hr)
    rw [mul_one, mul_div_cancel₀ _ hr.ne'] at hh
    exact hh
  have hsecond : ∀ r s h, 0 < r → 0 < s → 0 < h →
      U r s*(1+h/(s+2*(1-a)*r))^a ≤ U r (s+h) :=
    Matmul.Homogeneous.increment_of_row_affine_bound H.U_pos hUrow
      H.a_pos hL hc hQcap hincQ
  have hratio : ∀ r s, 0 < r → 0 < s →
      a*s/(s+2*(1-a)*r)+2*b*r/(2*r+s) ≤ 1 := by
    intro r s hr hs
    apply ratio_inequality_of_finite_increments hr hs hc (H.U_pos r s hr hs)
    · intro t ht
      exact H.U_hom t r s ht hr hs
    · exact fun h hh => hsecond r s h hr hs hh
    · intro t h ht hh hhd
      exact first_coordinate_increment hb hr ht hh hhd H.U_pos
        (H.U_concave_first hb t ht) (H.U_self_tripling hb r t hr ht)
  exact parabolic_cap_of_ratio_inequality ha H.a_le_one H.b_le_one hratio

#print axioms parameter_cap

end Matmul.HomogeneousProfiles
