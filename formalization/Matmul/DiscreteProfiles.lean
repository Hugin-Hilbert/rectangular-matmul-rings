import Mathlib
import Matmul.DiscreteSlopes
import Matmul.DiscreteFirstIncrement
import Matmul.DiscreteProfileCap

/-! The oriented discrete profiles, before any continuum limiting argument. -/

namespace Matmul.DiscreteProfiles

open Filter
open scoped Topology

/-- Exact profile hypotheses supplied by the shared-leg tensor constructions.
Indices zero are unused. `p=1/a₀` and `θ=b₀/a₀`. -/
structure DiscreteData (P Q : ℕ → ℕ → ℝ) (p θ : ℝ) : Prop where
  p_ge_one : 1 ≤ p
  theta_nonneg : 0 ≤ θ
  P_pos : ∀ n s, 1 ≤ n → 1 ≤ s → 0 < P n s
  Q_pos : ∀ n s, 1 ≤ n → 1 ≤ s → 0 < Q n s
  P_symm : ∀ n s, 1 ≤ n → 1 ≤ s → P n s = P s n
  P_boundary : ∀ s, 1 ≤ s → P 1 s = (s : ℝ)
  Q_boundary : ∀ n, 1 ≤ n → Q n 1 = (n : ℝ)^θ
  P_mono_first : ∀ n m s, 1 ≤ n → n ≤ m → 1 ≤ s → P n s ≤ P m s
  P_mono_second : ∀ n s t, 1 ≤ n → 1 ≤ s → s ≤ t → P n s ≤ P n t
  Q_mono_first : ∀ n m s, 1 ≤ n → n ≤ m → 1 ≤ s → Q n s ≤ Q m s
  Q_mono_second : ∀ n s t, 1 ≤ n → 1 ≤ s → s ≤ t → Q n s ≤ Q n t
  P_concave_first : ∀ s, 1 ≤ s →
    Antitone (fun n => P (n+2) s-P (n+1) s)
  P_concave_second : ∀ n, 1 ≤ n →
    Antitone (fun s => P n (s+2)-P n (s+1))
  Q_concave_second : ∀ n, 1 ≤ n →
    Antitone (fun s => Q n (s+2)-Q n (s+1))
  Q_concave_first : 0 < θ → ∀ s, 1 ≤ s →
    Antitone (fun n => Q (n+2) s ^ (1/θ)-Q (n+1) s ^ (1/θ))
  P_tripling : ∀ n s, 1 ≤ n → 1 ≤ s →
    2*P n s+Q n s ≤ P n (3*s+n-1)
  Q_tripling : ∀ n s, 1 ≤ n → 1 ≤ s →
    2*Q n s+P n s ≤ Q n (3*s+n-1)
  Q_self_tripling : 0 < θ → ∀ n s, 1 ≤ n → 1 ≤ s →
    3*Q n s ^ (1/θ) ≤ Q (3*n+s-1) s ^ (1/θ)
  P_rank_upper : ∀ n s, 1 ≤ n → 1 ≤ s →
    P n s ≤ ((n:ℝ)+s-1)^p
  Q_rank_upper : ∀ n s, 1 ≤ n → 1 ≤ s →
    Q n s ≤ ((n:ℝ)+s-1)^p

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

/-- Telescoping a pointwise slope lower bound over a finite interval. -/
theorem long_increment_lower {f : ℕ → ℝ} {L : ℝ}
    (hf : ∀ s, 1 ≤ s → L ≤ f (s+1)-f s)
    (s k : ℕ) (hs : 1 ≤ s) : (k:ℝ)*L ≤ f (s+k)-f s := by
  induction k with
  | zero => simp
  | succ k ih =>
    have he := hf (s+k) (by omega)
    have heq : s+(k+1)=s+k+1 := by omega
    rw [heq, Nat.cast_add, Nat.cast_one]
    nlinarith

/-- Data proved by the coupled row slope argument. -/
structure SlopeData (P Q : ℕ → ℕ → ℝ) (L : ℕ → ℝ) : Prop where
  pos : ∀ n, 1 ≤ n → 0 < L n
  P_limit : ∀ n, 1 ≤ n → Tendsto (fun s : ℕ => P n s/(s:ℝ)) atTop (𝓝 (L n))
  Q_limit : ∀ n, 1 ≤ n → Tendsto (fun s : ℕ => Q n s/(s:ℝ)) atTop (𝓝 (L n))
  cap : ∀ n s, 1 ≤ n → 1 ≤ s → P n s+Q n s ≤ L n*(2*(s:ℝ)+n-1)
  P_inc : ∀ n s, 1 ≤ n → 1 ≤ s → L n ≤ P n (s+1)-P n s
  Q_inc : ∀ n s, 1 ≤ n → 1 ≤ s → L n ≤ Q n (s+1)-Q n s
  Q_lower : ∀ n s : ℕ, 1 ≤ n → 1 ≤ s → L n*((s:ℝ)-1) ≤ Q n s
  mono : ∀ n m, 1 ≤ n → n ≤ m → L n ≤ L m

/-- The actual discrete hypotheses supply all of the slope data. -/
theorem exists_slope_data {P Q : ℕ → ℕ → ℝ} {p θ : ℝ}
    (H : DiscreteData P Q p θ) : ∃ L, SlopeData P Q L := by
  obtain ⟨L, hL⟩ := Matmul.DiscreteSlopes.exists_common_profile_slopes
    H.P_pos H.Q_pos H.P_concave_second H.Q_concave_second
    H.P_tripling H.Q_tripling
  refine ⟨L, ?_⟩
  have hlim := fun n hn => (hL n hn).2.1
  constructor
  · exact fun n hn => (hL n hn).1
  · exact hlim
  · exact fun n hn => (hL n hn).2.2.1
  · exact fun n s hn hs => (hL n hn).2.2.2.1 s hs
  · exact fun n s hn hs => (hL n hn).2.2.2.2.1 s hs
  · exact fun n s hn hs => (hL n hn).2.2.2.2.2.1 s hs
  · exact fun n s hn hs => (hL n hn).2.2.2.2.2.2.2 s hs
  · exact Matmul.DiscreteSlopes.slope_monotone_of_profile_monotone H.P_mono_first hlim

/-- The two row increment bounds give the sharper orientation intercept. -/
theorem oriented_affine_upper {P Q : ℕ → ℕ → ℝ} {L : ℕ → ℝ}
    (S : SlopeData P Q L) (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    Q n m ≤ L n*((m:ℝ)+2*n-1)-P n n := by
  let h := max n m
  have hnh : n ≤ h := le_max_left _ _
  have hmh : m ≤ h := le_max_right _ _
  have hcap := S.cap n h hn (le_trans hn hnh)
  have hP := long_increment_lower (S.P_inc n · hn ·) n (h-n) hn
  have hQ := long_increment_lower (S.Q_inc n · hn ·) m (h-m) hm
  rw [Nat.add_sub_of_le hnh] at hP
  rw [Nat.add_sub_of_le hmh] at hQ
  rw [Nat.cast_sub hnh] at hP
  rw [Nat.cast_sub hmh] at hQ
  nlinarith

/-- The normalized slope lies between one half and two at indices at least two. -/
theorem normalized_slope_bounds {P Q : ℕ → ℕ → ℝ} {p θ : ℝ} {L : ℕ → ℝ}
    (H : DiscreteData P Q p θ) (S : SlopeData P Q L)
    (n : ℕ) (hn : 2 ≤ n) :
    1/2 ≤ (n:ℝ)*L n/P n n ∧ (n:ℝ)*L n/P n n ≤ 2 := by
  have hn1 : 1 ≤ n := by omega
  have hp := H.P_pos n n hn1 hn1
  have hLn := S.pos n hn1
  have hcap := S.cap n n hn1 hn1
  have hlow := S.Q_lower n n hn1 hn1
  have hupper : P n n ≤ 2*(n:ℝ)*L n := by nlinarith
  have hinc := long_increment_lower (S.P_inc n · hn1 ·) 1 (n-1) (by omega)
  have hindex : 1+(n-1)=n := by omega
  rw [hindex, Nat.cast_sub hn1, Nat.cast_one] at hinc
  have hbound : P n 1 = (n:ℝ) := by
    rw [H.P_symm n 1 hn1 (by omega), H.P_boundary n hn1]
  rw [hbound] at hinc
  have hnreal : (2:ℝ) ≤ n := by exact_mod_cast hn
  constructor
  · apply (le_div_iff₀ hp).2
    nlinarith
  · apply (div_le_iff₀ hp).2
    nlinarith

/-- Two symmetric coordinate steps, and monotonicity of the common slope,
give the diagonal growth step. -/
theorem diagonal_increment {P Q : ℕ → ℕ → ℝ} {p θ : ℝ} {L : ℕ → ℝ}
    (H : DiscreteData P Q p θ) (S : SlopeData P Q L)
    (n v : ℕ) (hn : 1 ≤ n) :
    P n n+2*(v:ℝ)*L n ≤ P (n+v) (n+v) := by
  have hfirst := long_increment_lower (S.P_inc n · hn ·) n v hn
  have hsecond := long_increment_lower (S.P_inc (n+v) · (by omega) ·) n v hn
  rw [H.P_symm (n+v) n (by omega) hn] at hsecond
  have hmono := S.mono n (n+v) hn (by omega)
  have hmul := mul_le_mul_of_nonneg_left hmono (show 0 ≤ (v:ℝ) by positivity)
  nlinarith

/-- The sharper intercept estimate converts second-coordinate increments to
a multiplicative gain. The constant `-1` is discarded only in this bound. -/
theorem second_coordinate_increment {P Q : ℕ → ℕ → ℝ} {p θ : ℝ} {L : ℕ → ℝ}
    (H : DiscreteData P Q p θ) (S : SlopeData P Q L)
    (n m u : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    Q n m*(1+(u:ℝ)*L n/(L n*((m:ℝ)+2*n)-P n n)) ≤ Q n (m+u) := by
  have hL := S.pos n hn
  have hQ := H.Q_pos n m hn hm
  have hupper := oriented_affine_upper S n m hn hm
  let C := L n*((m:ℝ)+2*n)-P n n
  have hcap : Q n m ≤ C := by dsimp [C]; nlinarith
  have hC : 0 < C := lt_of_lt_of_le hQ hcap
  have hinc := long_increment_lower (S.Q_inc n · hn ·) m u hm
  have hmul := mul_le_mul_of_nonneg_right hcap
    (show 0 ≤ (u:ℝ)*L n by positivity)
  have hterm : Q n m*((u:ℝ)*L n/C) ≤ (u:ℝ)*L n := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hC).2
    nlinarith
  dsimp [C] at hterm
  nlinarith

/-- The diagonal, the oriented profile, and the normalized common slope
along an integer ray. -/
def diagonalSequence (P : ℕ → ℕ → ℝ) (v t : ℕ) : ℝ := P (v*t) (v*t)

def rectangularSequence (Q : ℕ → ℕ → ℝ) (u v t : ℕ) : ℝ := Q (v*t) (u*t)

noncomputable def slopeSequence (P : ℕ → ℕ → ℝ) (L : ℕ → ℝ) (v t : ℕ) : ℝ :=
  ((v*t:ℕ):ℝ)*L (v*t)/diagonalSequence P v t

/-- The exact diagonal sequence gain used by the logarithmic potential. -/
theorem diagonal_sequence_step {P Q : ℕ → ℕ → ℝ} {p θ : ℝ} {L : ℕ → ℝ}
    (H : DiscreteData P Q p θ) (S : SlopeData P Q L)
    (v t : ℕ) (hv : 1 ≤ v) (ht : 2 ≤ t) :
    diagonalSequence P v t*(1+2*slopeSequence P L v t/(t:ℝ)) ≤
      diagonalSequence P v (t+1) := by
  have hn : 1 ≤ v*t := by nlinarith
  have hp := H.P_pos (v*t) (v*t) hn hn
  have htne : (t:ℝ) ≠ 0 := by exact_mod_cast (by omega : t ≠ 0)
  have he := diagonal_increment H S (v*t) v hn
  have heq : diagonalSequence P v t*(1+2*slopeSequence P L v t/(t:ℝ)) =
      P (v*t) (v*t)+2*(v:ℝ)*L (v*t) := by
    dsimp [diagonalSequence, slopeSequence]
    push_cast
    field_simp [hp.ne', htne]
  rw [heq]
  simpa [diagonalSequence, Nat.mul_add] using he

/-- Rank upper bounds give the fixed logarithmic upper bound along a ray. -/
theorem log_rank_upper_on_ray {F : ℕ → ℕ → ℝ} {p : ℝ}
    (hp : 0 ≤ p)
    (hpos : ∀ n s, 1 ≤ n → 1 ≤ s → 0 < F n s)
    (hupper : ∀ n s, 1 ≤ n → 1 ≤ s → F n s ≤ ((n:ℝ)+s-1)^p)
    (u v t : ℕ) (hu : 1 ≤ u) (hv : 1 ≤ v) (ht : 2 ≤ t) :
    Real.log (F (v*t) (u*t)) ≤ p*Real.log (t:ℝ)+p*Real.log ((u:ℝ)+v) := by
  have hvt : 1 ≤ v*t := by nlinarith
  have hut : 1 ≤ u*t := by nlinarith
  have hbase : 0 ≤ ((v*t:ℕ):ℝ)+(u*t)-1 := by
    have hvtr : (1:ℝ) ≤ v*t := by exact_mod_cast hvt
    have hutr : (1:ℝ) ≤ u*t := by exact_mod_cast hut
    nlinarith
  have hfactor : 0 < ((u:ℝ)+v)*(t:ℝ) := by positivity
  have hpow := Real.rpow_le_rpow hbase
    (show ((v*t:ℕ):ℝ)+(u*t)-1 ≤ ((u:ℝ)+v)*(t:ℝ) by push_cast; nlinarith) hp
  have hpow' : (((v*t:ℕ):ℝ)+((u*t:ℕ):ℝ)-1)^p ≤ (((u:ℝ)+v)*(t:ℝ))^p := by
    simpa only [Nat.cast_mul] using hpow
  have hfinal := le_trans (hupper (v*t) (u*t) hvt hut) hpow'
  have hlog := Real.log_le_log (hpos (v*t) (u*t) hvt hut) hfinal
  rw [Real.log_rpow hfactor, Real.log_mul (by positivity) (by positivity)] at hlog
  nlinarith

/-- The finite first-coordinate gain, including the zero-parameter case. -/
theorem first_coordinate_increment {P Q : ℕ → ℕ → ℝ} {p θ : ℝ}
    (H : DiscreteData P Q p θ) (n s h : ℕ)
    (hn : 1 ≤ n) (hs : 1 ≤ s) (hh : 1 ≤ h) (hhd : h ≤ 2*n+s-1) :
    Q n s*(1+2*(h:ℝ)/(2*(n:ℝ)+s-1))^θ ≤ Q (n+h) s := by
  by_cases hθ0 : θ = 0
  · simpa [hθ0] using H.Q_mono_first n (n+h) s hn (by omega) hs
  · have hθ : 0 < θ := lt_of_le_of_ne H.theta_nonneg (Ne.symm hθ0)
    exact Matmul.DiscreteFirstIncrement.first_increment_of_self_tripling hθ
      (fun n hn => H.Q_pos n s hn hs) (H.Q_concave_first hθ s hs)
      n s h hn hs hh hhd (H.Q_self_tripling hθ n s hn hs)

/-- The exact two-coordinate multiplicative gain on an integer ray. -/
theorem rectangular_sequence_step {P Q : ℕ → ℕ → ℝ} {p θ : ℝ} {L : ℕ → ℝ}
    (H : DiscreteData P Q p θ) (S : SlopeData P Q L)
    (u v t : ℕ) (hu : 1 ≤ u) (hv : 1 ≤ v) (ht : 2 ≤ t) :
    rectangularSequence Q u v t *
        (1+(((u:ℝ)/v)*slopeSequence P L v t/
          ((((u:ℝ)/v)+2)*slopeSequence P L v t-1))/(t:ℝ)) *
        (1+(2/(2+(u:ℝ)/v))/((t:ℝ)+((u:ℝ)-1)/(2*(v:ℝ)+u)))^θ ≤
      rectangularSequence Q u v (t+1) := by
  have hn : 1 ≤ v*t := by nlinarith
  have hm : 1 ≤ u*t := by nlinarith
  have hs : 1 ≤ u*(t+1) := by nlinarith
  have hp := H.P_pos (v*t) (v*t) hn hn
  have hq := H.Q_pos (v*t) (u*t) hn hm
  have hL := S.pos (v*t) hn
  have hvreal : 0 < (v:ℝ) := by exact_mod_cast (by omega : 0<v)
  have hureal : 0 < (u:ℝ) := by exact_mod_cast (by omega : 0<u)
  have htreal : 0 < (t:ℝ) := by exact_mod_cast (by omega : 0<t)
  have hsecond := second_coordinate_increment H S (v*t) (u*t) u hn hm
  have hvn : v ≤ v*t := by
    calc v = v*1 := by simp
         _ ≤ v*t := Nat.mul_le_mul_left v (by omega)
  have hfirst := first_coordinate_increment H (v*t) (u*(t+1)) v hn hs hv
    (by omega)
  have hC : 0 < L (v*t)*(((u*t:ℕ):ℝ)+2*((v*t:ℕ):ℝ))-P (v*t) (v*t) := by
    have hup := oriented_affine_upper S (v*t) (u*t) hn hm
    nlinarith
  have hfactor1 :
      (u:ℝ)*L (v*t)/(L (v*t)*(((u*t:ℕ):ℝ)+2*((v*t:ℕ):ℝ))-P (v*t) (v*t)) =
      (((u:ℝ)/v)*slopeSequence P L v t/
        ((((u:ℝ)/v)+2)*slopeSequence P L v t-1))/(t:ℝ) := by
    dsimp [slopeSequence, diagonalSequence]
    push_cast
    field_simp [hp.ne', hvreal.ne', htreal.ne']
  have hfactor2 : 2*(v:ℝ)/(2*((v*t:ℕ):ℝ)+((u*(t+1):ℕ):ℝ)-1) =
      (2/(2+(u:ℝ)/v))/((t:ℝ)+((u:ℝ)-1)/(2*(v:ℝ)+u)) := by
    have hd : 0 < 2*((v*t:ℕ):ℝ)+((u*(t+1):ℕ):ℝ)-1 := by
      have hnr : (1:ℝ) ≤ ((v*t:ℕ):ℝ) := by exact_mod_cast hn
      have hsr : (1:ℝ) ≤ ((u*(t+1):ℕ):ℝ) := by exact_mod_cast hs
      nlinarith
    have hd2 : 0 < 2*(v:ℝ)+u := by positivity
    have huz : 0 ≤ (u:ℝ)-1 := by
      have hu1 : (1:ℝ) ≤ u := by exact_mod_cast hu
      linarith
    have hd3 : 0 < (t:ℝ)+((u:ℝ)-1)/(2*(v:ℝ)+u) := by positivity
    have hgamma : 2/(2+(u:ℝ)/v) = (2*(v:ℝ))/(2*(v:ℝ)+u) := by
      field_simp [hvreal.ne']
    have hden : 2*((v*t:ℕ):ℝ)+((u*(t+1):ℕ):ℝ)-1 =
        (2*(v:ℝ)+u)*((t:ℝ)+((u:ℝ)-1)/(2*(v:ℝ)+u)) := by
      push_cast
      field_simp [hd2.ne']
      ring
    rw [hgamma, hden, div_div]
  have hfactor_nonneg : 0 ≤
      (1+2*(v:ℝ)/(2*((v*t:ℕ):ℝ)+((u*(t+1):ℕ):ℝ)-1))^θ := by
    apply Real.rpow_nonneg
    have hnr : (1:ℝ) ≤ ((v*t:ℕ):ℝ) := by exact_mod_cast hn
    have hsr : (1:ℝ) ≤ ((u*(t+1):ℕ):ℝ) := by exact_mod_cast hs
    have hd : 0 < 2*((v*t:ℕ):ℝ)+((u*(t+1):ℕ):ℝ)-1 := by nlinarith
    positivity
  have hmult := mul_le_mul_of_nonneg_right hsecond hfactor_nonneg
  have heq : u*t+u=u*(t+1) := by ring
  rw [heq] at hmult
  have htotal := le_trans hmult hfirst
  rw [hfactor1, hfactor2] at htotal
  simpa [rectangularSequence, Nat.mul_add] using htotal

/-- The discrete profile hypotheses force the spectral ratio inequality at
every positive rational aspect ratio. -/
theorem rational_ratio_of_discrete_data {P Q : ℕ → ℕ → ℝ} {p θ : ℝ}
    (H : DiscreteData P Q p θ) (u v : ℕ) (hu : 1 ≤ u) (hv : 1 ≤ v) :
    2*θ/(2+(u:ℝ)/v)+((u:ℝ)/v)/((u:ℝ)/v+2-2/p) ≤ p := by
  obtain ⟨L, S⟩ := exists_slope_data H
  have hτ : 0 < (u:ℝ)/v := by positivity
  have hz : 0 ≤ ((u:ℝ)-1)/(2*(v:ℝ)+u) := by
    have hu1 : (1:ℝ) ≤ u := by exact_mod_cast hu
    positivity
  apply Matmul.DiscreteProfileCap.sequence_ratio H.p_ge_one H.theta_nonneg hτ hz
    (diagonalSequence P v) (rectangularSequence Q u v) (slopeSequence P L v)
    (p*Real.log ((v:ℝ)+v)) (p*Real.log ((u:ℝ)+v))
  · intro t ht
    have hn : 1 ≤ v*t := by nlinarith
    exact H.P_pos (v*t) (v*t) hn hn
  · intro t ht
    have hn : 1 ≤ v*t := by nlinarith
    have hm : 1 ≤ u*t := by nlinarith
    exact H.Q_pos (v*t) (u*t) hn hm
  · intro t ht
    exact normalized_slope_bounds H S (v*t) (by nlinarith)
  · exact fun t ht => diagonal_sequence_step H S v t hv ht
  · intro t ht
    simpa only [Matmul.DiscreteProfileCap.slopeFraction] using
      rectangular_sequence_step H S u v t hu hv ht
  · intro t ht
    exact log_rank_upper_on_ray (by linarith [H.p_ge_one])
      H.P_pos H.P_rank_upper v v t hv hv ht
  · intro t ht
    exact log_rank_upper_on_ray (by linarith [H.p_ge_one])
      H.Q_pos H.Q_rank_upper u v t hu hv ht

/-- All positive rational ratios have positive integer representatives. -/
theorem rational_ratio {P Q : ℕ → ℕ → ℝ} {p θ : ℝ}
    (H : DiscreteData P Q p θ) (q : ℚ) (hq : 0 < (q:ℝ)) :
    2*θ/(2+(q:ℝ))+(q:ℝ)/((q:ℝ)+2-2/p) ≤ p := by
  have hqrat : 0 < q := by exact_mod_cast hq
  have hnum : 0 < q.num := Rat.num_pos.mpr hqrat
  have hu : 1 ≤ q.num.toNat := by omega
  have hv : 1 ≤ q.den := q.pos
  have hcast : (q:ℝ) = (q.num.toNat:ℝ)/(q.den:ℝ) := by
    rw [Rat.cast_def]
    congr 1
    exact_mod_cast (Int.toNat_of_nonneg hnum.le).symm
  rw [hcast]
  exact rational_ratio_of_discrete_data H q.num.toNat q.den hu hv

#print axioms exists_slope_data
#print axioms diagonal_sequence_step
#print axioms rational_ratio_of_discrete_data
#print axioms rational_ratio

end Matmul.DiscreteProfiles
