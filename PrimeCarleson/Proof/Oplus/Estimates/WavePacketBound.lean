module

public import PrimeCarleson.Proof.Oplus.Defs.All
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Decay of the wave packets, uniformly in the tile ([O+] L1187-L1204)

[O+] L1187-L1204: with
`w_I(x) = |I|^{-1}(1 + |x - c(I)|/|I|)^{-N}` "for a fixed large `N`", the wave packet of a
multitile `P = (I, ω_u)` obeys, for each `n ≥ 0`,
`|(d/dx)^n (e^{-2πi c(ω_u) ·} φ_P)(x)| ≤ C'(n) |I|^{1/2 - n} |w_I(x)|`.
Source: [O+] `wavepacketadaptedbound`, L1187–L1204 (stated without proof; the delicate point
is the uniformity of `C'(n)` in the tile and in the profile).

* `Dyadic.weight N I x` is `w_I(x)`, with `integral_weight : ∫ w_I = 2/(N - 1)` for `N ≥ 2`.
* `IsProfile.exists_adaptedBound hχ n N`: for a fixed profile `χ` (`IsProfile χ`) there is `C ≥ 0`
  such that for **every** pair of dyadic intervals `I, J` with `|I||J| = 1/2` (the tile
  condition `I.k + J.k = -1`) and every `x`,
  `‖(d/dx)^n (e(-c(J)·) φ_{I × J})(x)‖ ≤ C √|I| |I|^{-n} w_I(x)`; `C` depends only on
  `χ, n, N`.
* `ProfileChoice.exists_adaptedBound n N`: the same constant works for the six profiles `ν_i`,
  `ν_i(-·)`, `i ∈ {-1, 0, 1}` (`ProfileChoice`), and `Multitile.exists_adaptedBound` states it
  for `ρ`-multitiles of every index `ρ`, every profile choice, every `n, N`.
* Consequences: the pointwise bounds `|φ_P(x)| ≤ C |I|^{-1/2}(1 + |x - c(I)|/|I|)^{-N}` (`n = 0`).

The proof: `e(-c(J)x) φ_{I×J}(x) = κ G(|J|(x - c(I)))` with `|κ| = √|I| |J|` and `G = 𝓕⁻[√χ]` a
fixed Schwartz function (`modulated_wavePacketOf`); differentiating `n` times gives `|J|^n G^{(n)}`
(`iteratedDeriv_comp_const_smul`), the Schwartz seminorms bound `G^{(n)}`
(`IsProfile.exists_decay_iteratedDeriv`), and `|I||J| = 1/2` converts `|J|` into `|I|`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped FourierTransform SchwartzMap ContDiff

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

open PrimeCarleson PrimeCarleson.Proof.Common PrimeCarleson.Proof.Goal0

/-! ### The weight `w_I` and its integrals -/

/-- The weight `w_I(x) = |I|⁻¹ (1 + |x - c(I)|/|I|)^{-N}` ([O+] L1196). -/
def Dyadic.weight (N : ℕ) (I : Dyadic) (x : ℝ) : ℝ :=
  I.length⁻¹ * (1 + |x - I.center| / I.length) ^ (-(N : ℤ))

/-- The weight `w_I` is positive. -/
theorem Dyadic.weight_pos (N : ℕ) (I : Dyadic) (x : ℝ) : 0 < I.weight N x := by
  have := I.length_pos
  unfold weight; positivity

/-- The weight `w_I` is nonnegative. -/
theorem Dyadic.weight_nonneg (N : ℕ) (I : Dyadic) (x : ℝ) : 0 ≤ I.weight N x :=
  (I.weight_pos N x).le

/-- The weight `w_I` is continuous. -/
theorem Dyadic.continuous_weight (N : ℕ) (I : Dyadic) : Continuous (I.weight N) := by
  have := I.length_pos
  unfold weight
  refine continuous_const.mul (Continuous.zpow₀ (by fun_prop) _ fun x => Or.inl ?_)
  positivity

/-- `√|I| w_I(x) = |I|^{-1/2} (1 + |x - c(I)|/|I|)^{-N}`. -/
theorem Dyadic.sqrt_length_mul_weight (N : ℕ) (I : Dyadic) (x : ℝ) :
    √I.length * I.weight N x = (√I.length)⁻¹ * (1 + |x - I.center| / I.length) ^ (-(N : ℤ)) := by
  have hI := I.length_pos
  have h : √I.length * I.length⁻¹ = (√I.length)⁻¹ := by
    have h1 : √I.length * √I.length = I.length := Real.mul_self_sqrt hI.le
    have h2 : 0 < √I.length := Real.sqrt_pos.2 hI
    field_simp
    linarith
  unfold weight
  rw [← mul_assoc, h]

theorem hasDerivAt_neg_one_add_zpow {N : ℕ} (hN : 2 ≤ N) (x : ℝ) (hx : 0 ≤ x) :
    HasDerivAt (fun x : ℝ => -(1 + x) ^ (-((N : ℤ) - 1)) / ((N : ℝ) - 1))
      ((1 + x) ^ (-(N : ℤ))) x := by
  have hpos : (0 : ℝ) < 1 + x := by linarith
  have h1 : HasDerivAt (fun x : ℝ => (1 + x) ^ (-((N : ℤ) - 1)))
      (((-((N : ℤ) - 1) : ℤ) : ℝ) * (1 + x) ^ (-((N : ℤ) - 1) - 1) * 1) x :=
    (hasDerivAt_zpow (-((N : ℤ) - 1)) (1 + x) (Or.inl hpos.ne')).comp x
      ((hasDerivAt_id x).const_add 1)
  have h2 := (h1.neg).div_const ((N : ℝ) - 1)
  convert h2 using 1
  have hN' : ((N : ℝ) - 1) ≠ 0 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have : (-(N : ℤ)) = -((N : ℤ) - 1) - 1 := by ring
  rw [this]
  push_cast
  field_simp

/-- `∫_0^∞ (1 + x)^{-N} dx = 1/(N - 1)` for `N ≥ 2`. -/
theorem integral_Ioi_one_add_zpow {N : ℕ} (hN : 2 ≤ N) :
    ∫ x in Ioi (0 : ℝ), (1 + x) ^ (-(N : ℤ)) = 1 / ((N : ℝ) - 1) := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlim : Tendsto (fun x : ℝ => -(1 + x) ^ (-((N : ℤ) - 1)) / ((N : ℝ) - 1)) atTop
      (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => (1 + x) ^ (-((N : ℤ) - 1))) atTop (𝓝 0) :=
      (tendsto_zpow_atTop_zero (by omega)).comp (tendsto_atTop_add_const_left _ 1 tendsto_id)
    simpa using (h1.neg).div_const ((N : ℝ) - 1)
  rw [integral_Ioi_of_hasDerivAt_of_nonneg
    (g := fun x : ℝ => -(1 + x) ^ (-((N : ℤ) - 1)) / ((N : ℝ) - 1))
    (l := 0) ?_ (fun x hx => hasDerivAt_neg_one_add_zpow hN x (le_of_lt hx)) ?_ hlim]
  · simp [div_eq_inv_mul]
  · exact (hasDerivAt_neg_one_add_zpow hN 0 le_rfl).continuousAt.continuousWithinAt
  · intro x hx; exact (zpow_pos (by linarith [hx.out]) _).le

/-- `(1 + |x|)^{-N}` is integrable for `N ≥ 2`. -/
theorem integrable_one_add_abs_zpow {N : ℕ} (hN : 2 ≤ N) :
    Integrable (fun x : ℝ => (1 + |x|) ^ (-(N : ℤ))) := by
  have h := integrable_one_add_norm (E := ℝ) (μ := volume) (r := (N : ℝ)) (by
    simp only [Module.finrank_self, Nat.cast_one]; exact_mod_cast hN)
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [Real.norm_eq_abs]
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast, zpow_neg, zpow_natCast]

/-- `∫_ℝ (1 + |x|)^{-N} dx = 2/(N - 1)` for `N ≥ 2`. -/
theorem integral_one_add_abs_zpow {N : ℕ} (hN : 2 ≤ N) :
    ∫ x : ℝ, (1 + |x|) ^ (-(N : ℤ)) = 2 / ((N : ℝ) - 1) := by
  rw [integral_comp_abs (f := fun y : ℝ => (1 + y) ^ (-(N : ℤ))), integral_Ioi_one_add_zpow hN]
  ring

/-- `x ↦ (1 + |x - c|/L)^{-N}` is integrable for `N ≥ 2` and `L > 0`. -/
theorem integrable_one_add_abs_div_zpow {N : ℕ} (hN : 2 ≤ N) (c : ℝ) {L : ℝ} (hL : 0 < L) :
    Integrable (fun x : ℝ => (1 + |x - c| / L) ^ (-(N : ℤ))) := by
  have h := ((integrable_one_add_abs_zpow hN).comp_div hL.ne').comp_sub_right c
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [abs_div, abs_of_pos hL]

/-- `∫ (1 + |x - c|/L)^{-N} dx = 2L/(N - 1)` for `N ≥ 2` and `L > 0`. -/
theorem integral_one_add_abs_div_zpow {N : ℕ} (hN : 2 ≤ N) (c : ℝ) {L : ℝ} (hL : 0 < L) :
    ∫ x : ℝ, (1 + |x - c| / L) ^ (-(N : ℤ)) = L * (2 / ((N : ℝ) - 1)) := by
  have h1 : ∀ x : ℝ, (1 + |x - c| / L) ^ (-(N : ℤ)) =
      (fun y : ℝ => (1 + |y|) ^ (-(N : ℤ))) ((x - c) / L) := fun x => by
    simp only [abs_div, abs_of_pos hL]
  simp_rw [h1]
  rw [integral_sub_right_eq_self (fun x : ℝ => (fun y : ℝ => (1 + |y|) ^ (-(N : ℤ))) (x / L)) c,
    Measure.integral_comp_div (fun y : ℝ => (1 + |y|) ^ (-(N : ℤ))) L, abs_of_pos hL,
    integral_one_add_abs_zpow hN, smul_eq_mul]

/-- The weight `w_I` is integrable for `N ≥ 2`. -/
theorem Dyadic.integrable_weight {N : ℕ} (hN : 2 ≤ N) (I : Dyadic) : Integrable (I.weight N) :=
  (integrable_one_add_abs_div_zpow hN I.center I.length_pos).const_mul _

/-- **`∫ w_I = 2/(N - 1)`** for `N ≥ 2`. -/
theorem Dyadic.integral_weight {N : ℕ} (hN : 2 ≤ N) (I : Dyadic) :
    ∫ x, I.weight N x = 2 / ((N : ℝ) - 1) := by
  have := I.length_pos
  unfold weight
  rw [integral_const_mul, integral_one_add_abs_div_zpow hN I.center I.length_pos]
  field_simp

/-! ### The profile `√χ` as a Schwartz function -/

/-- The profile `η ↦ √χ(η)` as a complex-valued function. -/
def sqrtProfile (χ : ℝ → ℝ) (η : ℝ) : ℂ := ((√(χ η) : ℝ) : ℂ)

/-- `√χ((ξ - c(J))/|J|)` is the frequency profile of `J`. -/
theorem freqProfile_eq_sqrtProfile (χ : ℝ → ℝ) (J : Dyadic) (ξ : ℝ) :
    freqProfile χ J ξ = sqrtProfile χ ((ξ - J.center) / J.length) := rfl

variable {χ : ℝ → ℝ}

/-- `√χ` is `C^∞` for a profile. -/
theorem IsProfile.contDiff_sqrtProfile (hχ : IsProfile χ) : ContDiff ℝ ∞ (sqrtProfile χ) :=
  Complex.ofRealCLM.contDiff.comp hχ.contDiff_sqrt

/-- `√χ` has compact support for a profile. -/
theorem IsProfile.hasCompactSupport_sqrtProfile (hχ : IsProfile χ) :
    HasCompactSupport (sqrtProfile χ) :=
  HasCompactSupport.intro (isCompact_Icc (a := (-13 / 25 : ℝ)) (b := 13 / 25)) fun η hη => by
    simp [sqrtProfile, hχ.eq_zero η hη]

/-- `√χ` as a Schwartz function. -/
def IsProfile.sqrtSchwartz (hχ : IsProfile χ) : 𝓢(ℝ, ℂ) :=
  hχ.hasCompactSupport_sqrtProfile.toSchwartzMap hχ.contDiff_sqrtProfile

/-- The inverse Fourier transform of `√χ`, as a Schwartz function, is `𝓕⁻ (sqrtProfile χ)`. -/
theorem IsProfile.coe_fourierInv_sqrtSchwartz (hχ : IsProfile χ) :
    (⇑(𝓕⁻ hχ.sqrtSchwartz : 𝓢(ℝ, ℂ))) = 𝓕⁻ (sqrtProfile χ) := by
  rw [SchwartzMap.fourierInv_coe]; rfl

/-! ### The inverse Fourier transform of a translated and dilated profile -/

/-- `𝓕⁻[√χ((· - c(J))/|J|)](y) = |J| e(c(J) y) 𝓕⁻[√χ](|J| y)`. -/
theorem fourierInv_freqProfile (χ : ℝ → ℝ) (J : Dyadic) (y : ℝ) :
    𝓕⁻ (freqProfile χ J) y =
      (J.length : ℂ) * e (J.center * y) * 𝓕⁻ (sqrtProfile χ) (J.length * y) := by
  have hL := J.length_pos
  rw [fourierInv_eq_integral_e, fourierInv_eq_integral_e]
  set c := J.center with hc
  set L := J.length with hL'
  have h1 : ∀ ξ : ℝ, e (ξ * y) * freqProfile χ J ξ =
      (fun u : ℝ => e (c * y) * (e (u * (L * y)) * sqrtProfile χ u)) ((ξ - c) / L) := by
    intro ξ
    simp only
    rw [freqProfile_eq_sqrtProfile, ← mul_assoc, ← e_add]
    congr 2
    field_simp
    ring
  simp_rw [h1]
  rw [integral_sub_right_eq_self (fun ξ : ℝ => (fun u : ℝ =>
      e (c * y) * (e (u * (L * y)) * sqrtProfile χ u)) (ξ / L)) c]
  rw [Measure.integral_comp_div (fun u : ℝ => e (c * y) * (e (u * (L * y)) * sqrtProfile χ u)) L,
    integral_const_mul, abs_of_pos hL, Complex.real_smul]
  ring

/-- **The modulated wave packet**: `e(-c(J) x) φ_{I×J}(x) = κ 𝓕⁻[√χ](|J|(x - c(I)))` with the
constant `κ = √|I| |J| e(-c(J)c(I))`, `|κ| = √|I| |J|`. -/
theorem modulated_wavePacketOf (χ : ℝ → ℝ) (I J : Dyadic) (x : ℝ) :
    e (-(J.center * x)) * wavePacketOf χ I J x =
      ((√I.length : ℝ) : ℂ) * (J.length : ℂ) * e (-(J.center * I.center)) *
        𝓕⁻ (sqrtProfile χ) (J.length * (x - I.center)) := by
  unfold wavePacketOf
  rw [fourierInv_freqProfile]
  have h : e (-(J.center * x)) * e (J.center * (x - I.center)) = e (-(J.center * I.center)) := by
    rw [← e_add]; congr 1; ring
  calc e (-(J.center * x)) * (((√I.length : ℝ) : ℂ) * ((J.length : ℂ) *
        e (J.center * (x - I.center)) * 𝓕⁻ (sqrtProfile χ) (J.length * (x - I.center))))
      = ((√I.length : ℝ) : ℂ) * (J.length : ℂ) *
        (e (-(J.center * x)) * e (J.center * (x - I.center))) *
        𝓕⁻ (sqrtProfile χ) (J.length * (x - I.center)) := by ring
    _ = _ := by rw [h]

/-! ### Decay of the derivatives of `𝓕⁻[√χ]` -/

/-- The derivatives of the Schwartz function `𝓕⁻[√χ]` decay faster than any power. -/
theorem IsProfile.exists_decay_iteratedDeriv (hχ : IsProfile χ) (n N : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y : ℝ,
      ‖iteratedDeriv n (𝓕⁻ (sqrtProfile χ)) y‖ ≤ B * (1 + |y|) ^ (-(N : ℤ)) := by
  set G : 𝓢(ℝ, ℂ) := 𝓕⁻ hχ.sqrtSchwartz with hG
  rw [← hχ.coe_fourierInv_sqrtSchwartz]
  refine ⟨2 ^ N * (SchwartzMap.seminorm ℝ 0 n G + SchwartzMap.seminorm ℝ N n G), by positivity,
    fun y => ?_⟩
  have h0 := SchwartzMap.le_seminorm' ℝ 0 n G y
  have hN := SchwartzMap.le_seminorm' ℝ N n G y
  rw [pow_zero, one_mul] at h0
  have hpos : (0 : ℝ) < (1 + |y|) ^ N := by positivity
  have hle : (1 + |y|) ^ N ≤ 2 ^ N * (1 + |y| ^ N) := by
    rcases le_total |y| 1 with h | h
    · calc (1 + |y|) ^ N ≤ 2 ^ N := pow_le_pow_left₀ (by positivity) (by linarith) N
        _ ≤ 2 ^ N * (1 + |y| ^ N) := by
          have : (0 : ℝ) ≤ |y| ^ N := by positivity
          nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) N]
    · calc (1 + |y|) ^ N ≤ (2 * |y|) ^ N := pow_le_pow_left₀ (by positivity) (by linarith) N
        _ = 2 ^ N * |y| ^ N := mul_pow _ _ _
        _ ≤ 2 ^ N * (1 + |y| ^ N) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
  rw [zpow_neg, zpow_natCast, ← div_eq_mul_inv, le_div_iff₀ hpos]
  calc ‖iteratedDeriv n (⇑G) y‖ * (1 + |y|) ^ N
      ≤ ‖iteratedDeriv n (⇑G) y‖ * (2 ^ N * (1 + |y| ^ N)) :=
        mul_le_mul_of_nonneg_left hle (norm_nonneg _)
    _ = 2 ^ N * (‖iteratedDeriv n (⇑G) y‖ + |y| ^ N * ‖iteratedDeriv n (⇑G) y‖) := by ring
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith

/-- `(1 + a/2)^{-N} ≤ 2^N (1 + a)^{-N}` for `a ≥ 0`. -/
theorem one_add_div_two_zpow_le (a : ℝ) (ha : 0 ≤ a) (N : ℕ) :
    (1 + a / 2) ^ (-(N : ℤ)) ≤ 2 ^ N * (1 + a) ^ (-(N : ℤ)) := by
  rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
  have h1 : (0 : ℝ) < (1 + a) ^ N := by positivity
  have h2 : (1 + a) ^ N / 2 ^ N ≤ (1 + a / 2) ^ N := by
    rw [← div_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) N
  have h3 : (0 : ℝ) < (1 + a) ^ N / 2 ^ N := by positivity
  calc ((1 + a / 2) ^ N)⁻¹ ≤ ((1 + a) ^ N / 2 ^ N)⁻¹ := inv_anti₀ h3 h2
    _ = 2 ^ N * ((1 + a) ^ N)⁻¹ := by rw [inv_div, div_eq_mul_inv]

/-! ### The adapted bound for one profile -/

/-- **Wave packet decay for a fixed profile** ([O+] `wavepacketadaptedbound`, L1187-L1204): for
each `n, N` there is `C ≥ 0` (depending only on `χ, n, N`) such that for every tile `I × J`
(`|I||J| = 1/2`) and every `x`,
`|(d/dx)^n (e(-c(J)·) φ_{I×J})(x)| ≤ C |I|^{1/2 - n} w_I(x)`, with
`w_I(x) = |I|⁻¹ (1 + |x - c(I)|/|I|)^{-N}` and `|I|^{1/2 - n} = √|I| (|I|^n)⁻¹`. -/
theorem IsProfile.exists_adaptedBound (hχ : IsProfile χ) (n N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ I J : Dyadic, I.k + J.k = -1 → ∀ x : ℝ,
      ‖iteratedDeriv n (fun y => e (-(J.center * y)) * wavePacketOf χ I J y) x‖ ≤
        C * (√I.length * (I.length ^ n)⁻¹) * I.weight N x := by
  obtain ⟨B, hB0, hB⟩ := hχ.exists_decay_iteratedDeriv n N
  refine ⟨B * 2 ^ N * (1 / 2) ^ (n + 1), by positivity, fun I J hk x => ?_⟩
  have hI := I.length_pos
  have hJ := J.length_pos
  have harea : I.length * J.length = 1 / 2 := (Dyadic.area_iff I J).1 hk
  have hLI : J.length = (2 * I.length)⁻¹ := by
    field_simp; linarith
  set G : 𝓢(ℝ, ℂ) := 𝓕⁻ hχ.sqrtSchwartz with hG
  have hGc : (⇑G) = 𝓕⁻ (sqrtProfile χ) := hχ.coe_fourierInv_sqrtSchwartz
  set κ : ℂ := ((√I.length : ℝ) : ℂ) * (J.length : ℂ) * e (-(J.center * I.center)) with hκ
  have hfun : (fun y => e (-(J.center * y)) * wavePacketOf χ I J y) =
      fun y => κ * (fun z => (⇑G) (J.length * z)) (y - I.center) := by
    funext y
    rw [modulated_wavePacketOf, hGc]
  have hderiv : iteratedDeriv n (fun y => e (-(J.center * y)) * wavePacketOf χ I J y) x =
      κ * (((J.length : ℝ) ^ n : ℝ) • iteratedDeriv n (⇑G) (J.length * (x - I.center))) := by
    rw [hfun, iteratedDeriv_const_mul κ ?_]
    · rw [iteratedDeriv_comp_sub_const n (fun z => (⇑G) (J.length * z)) I.center]
      simp only
      rw [iteratedDeriv_comp_const_smul (G.smooth n) J.length]
    · exact (((G.smooth n).comp (contDiff_const.mul contDiff_id)).comp
        (contDiff_id.sub contDiff_const)).contDiffAt
  rw [hderiv, norm_mul, norm_smul]
  have hκn : ‖κ‖ = √I.length * J.length := by
    rw [hκ, norm_mul, norm_mul, norm_e, mul_one, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), abs_of_pos hJ]
  rw [hκn, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hD := hB (J.length * (x - I.center))
  rw [← hGc] at hD
  have hLa : |J.length * (x - I.center)| = (|x - I.center| / I.length) / 2 := by
    rw [abs_mul, abs_of_pos hJ, hLI]; field_simp
  rw [hLa] at hD
  have ha : 0 ≤ |x - I.center| / I.length := by positivity
  have hD2 := hD.trans (mul_le_mul_of_nonneg_left (one_add_div_two_zpow_le _ ha N) hB0)
  have hLn : J.length ^ n * J.length = (1 / 2) ^ (n + 1) * ((I.length ^ n)⁻¹ * I.length⁻¹) := by
    rw [hLI]
    ring
  have hs : 0 ≤ √I.length := Real.sqrt_nonneg _
  have hw : Dyadic.weight N I x = I.length⁻¹ * (1 + |x - I.center| / I.length) ^ (-(N : ℤ)) := rfl
  rw [hw]
  calc √I.length * J.length * (J.length ^ n * ‖iteratedDeriv n (⇑G) (J.length * (x - I.center))‖)
      = √I.length * (J.length ^ n * J.length) *
          ‖iteratedDeriv n (⇑G) (J.length * (x - I.center))‖ := by ring
    _ ≤ √I.length * (J.length ^ n * J.length) *
          (B * (2 ^ N * (1 + |x - I.center| / I.length) ^ (-(N : ℤ)))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa [mul_assoc] using hD2
    _ = _ := by rw [hLn]; ring

/-- **The pointwise bound** (`n = 0`):
`|φ_{I×J}(x)| ≤ C √|I| w_I(x) = C |I|^{-1/2} (1 + |x - c(I)|/|I|)^{-N}` for every tile `I × J`
and a profile `χ`. -/
theorem IsProfile.exists_norm_wavePacketOf_le (hχ : IsProfile χ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ I J : Dyadic, I.k + J.k = -1 → ∀ x : ℝ,
      ‖wavePacketOf χ I J x‖ ≤
        C * (√I.length)⁻¹ * (1 + |x - I.center| / I.length) ^ (-(N : ℤ)) := by
  obtain ⟨C, hC0, hC⟩ := hχ.exists_adaptedBound 0 N
  refine ⟨C, hC0, fun I J hk x => ?_⟩
  have h := hC I J hk x
  simp only [iteratedDeriv_zero, norm_mul, norm_e, one_mul, pow_zero, inv_one, mul_one] at h
  calc ‖wavePacketOf χ I J x‖ ≤ C * √I.length * I.weight N x := h
    _ = C * (√I.length * I.weight N x) := by ring
    _ = _ := by rw [Dyadic.sqrt_length_mul_weight]; ring

/-! ### Uniformity over the six profiles -/

instance Orientation.instFinite : Finite Orientation :=
  Finite.of_injective (fun o : Orientation => (o = Orientation.plain)) (by
    intro a b h
    cases a <;> cases b <;> simp_all)

instance ProfileChoice.instFinite : Finite ProfileChoice :=
  Finite.of_injective
    (fun c : ProfileChoice => ((⟨c.i, c.neg_one_le, c.le_one⟩ : Icc (-1 : ℤ) 1), c.orientation))
    (by
      intro a b h
      obtain ⟨i, h1, h2, o⟩ := a
      obtain ⟨i', h1', h2', o'⟩ := b
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1h, rfl⟩ := h
      have := congrArg Subtype.val h1h
      simp only at this
      subst this
      rfl)

/-- A property of a constant `C` that is monotone in `C` and holds for some `C` for each of the
six profile choices holds for one `C` for all of them. -/
theorem exists_uniform_profileChoice (Q : ProfileChoice → ℝ → Prop)
    (hmono : ∀ c C C', C ≤ C' → Q c C → Q c C') (h : ∀ c, ∃ C, 0 ≤ C ∧ Q c C) :
    ∃ C, 0 ≤ C ∧ ∀ c, Q c C := by
  have : Fintype ProfileChoice := Fintype.ofFinite _
  choose C hC0 hC using h
  refine ⟨∑ c, C c, Finset.sum_nonneg fun c _ => hC0 c, fun c => ?_⟩
  exact hmono c (C c) _ (Finset.single_le_sum (f := C) (fun c _ => hC0 c) (Finset.mem_univ c))
    (hC c)

/-- **Wave packet decay, uniform in the tile and in the profile**
([O+] `wavepacketadaptedbound`): for all `n, N` there is `C ≥ 0` such that for every
profile choice `ν_i` or `ν_i(-·)` (`i ∈ {-1, 0, 1}`), every tile `I × J` and every `x`,
`|(d/dx)^n (e(-c(J)·) φ_{I×J})(x)| ≤ C |I|^{1/2 - n} w_I(x)`. -/
theorem ProfileChoice.exists_adaptedBound (n N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : ProfileChoice) (I J : Dyadic), I.k + J.k = -1 → ∀ x : ℝ,
      ‖iteratedDeriv n (fun y => e (-(J.center * y)) * wavePacketOf c.fn I J y) x‖ ≤
        C * (√I.length * (I.length ^ n)⁻¹) * I.weight N x := by
  refine exists_uniform_profileChoice
    (fun c C => ∀ (I J : Dyadic), I.k + J.k = -1 → ∀ x : ℝ,
      ‖iteratedDeriv n (fun y => e (-(J.center * y)) * wavePacketOf c.fn I J y) x‖ ≤
        C * (√I.length * (I.length ^ n)⁻¹) * I.weight N x) ?_ fun c => ?_
  · intro c C C' hCC' h I J hk x
    refine (h I J hk x).trans ?_
    have : 0 ≤ √I.length * (I.length ^ n)⁻¹ * I.weight N x := by
      have := I.length_pos
      have := I.weight_nonneg N x
      positivity
    nlinarith
  · exact c.isProfile.exists_adaptedBound n N

/-- **The adapted bound for `ρ`-multitiles** ([O+] `wavepacketadaptedbound`, L1187-L1204, both
profiles `ν_i`, `ν_i(-·)` of L1119-L1121): for all `n, N` there is `C ≥ 0`, independent of the
index `ρ`, the profile choice, the multitile `P = (I, ω_u)` and `x`, with
`|(d/dx)^n (e(-c(ω_u)·) φ_P)(x)| ≤ C |I|^{1/2 - n} w_I(x)`. -/
theorem Multitile.exists_adaptedBound (n N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ρ : Idx) (ch : ProfileChoice) (P : Multitile ρ) (x : ℝ),
      ‖iteratedDeriv n (fun y => e (-(P.ωu.center * y)) * P.wavePacket ch y) x‖ ≤
        C * (√P.I.length * (P.I.length ^ n)⁻¹) * P.I.weight N x := by
  obtain ⟨C, hC0, hC⟩ := ProfileChoice.exists_adaptedBound n N
  exact ⟨C, hC0, fun ρ ch P x => hC ch P.I P.ωu P.area x⟩

/-- **The pointwise bound for `ρ`-multitiles** (`n = 0`): `|φ_P(x)| ≤ C |I|^{-1/2}
(1 + |x - c(I)|/|I|)^{-N}`, with `C` independent of `ρ`, the profile choice and `P`. -/
theorem Multitile.exists_norm_wavePacket_le (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ρ : Idx) (ch : ProfileChoice) (P : Multitile ρ) (x : ℝ),
      ‖P.wavePacket ch x‖ ≤
        C * (√P.I.length)⁻¹ * (1 + |x - P.I.center| / P.I.length) ^ (-(N : ℤ)) := by
  obtain ⟨C, hC0, hC⟩ := exists_uniform_profileChoice
    (fun c C => ∀ I J : Dyadic, I.k + J.k = -1 → ∀ x : ℝ,
      ‖wavePacketOf c.fn I J x‖ ≤
        C * (√I.length)⁻¹ * (1 + |x - I.center| / I.length) ^ (-(N : ℤ)))
    (fun c C C' hCC' h I J hk x => by
      refine (h I J hk x).trans ?_
      have := I.length_pos
      have : 0 ≤ (√I.length)⁻¹ * (1 + |x - I.center| / I.length) ^ (-(N : ℤ)) := by positivity
      nlinarith)
    (fun c => c.isProfile.exists_norm_wavePacketOf_le N)
  exact ⟨C, hC0, fun ρ ch P x => hC ch P.I P.ωu P.area x⟩

end PrimeCarleson.Proof.Oplus
