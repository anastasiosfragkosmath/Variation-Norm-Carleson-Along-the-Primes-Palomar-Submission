module

public import PrimeCarleson.Proof.Oplus.Defs.WavePacket
public import PrimeCarleson.Proof.Oplus.Defs.Linearization
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The wave-packet expansion of a multiplier `φ_J f̂` ([O+] L978-L1019)

[O+] L978-L1019: "We now write each multiplier `φ_J` as the
sum of wave packets. [...] For each `J`, we then have
`∑_{|I| = 1/(2|J|)} ⟨f, φ_{I×J}⟩ φ̂_{I×J} = f̂ φ_J`. To see this we use a Fourier series
expansion". Source: [O+], L978–L980.

The proof uses Poisson summation (`Common/FourierR`) in place of the Fourier series of `g_J`:
for `h = √χ_J f̂ ∈ C_c^∞` the coefficients are `⟨f, φ_{I×J}⟩ = √L ĥ(-c(I))` and, for the
smooth compactly supported `Ψ_ξ(y) = 2|J| h(ξ - 2|J| y)`, `L ĥ(-c(I)) e(-c(I) ξ) = L Ψ̂_ξ(1/2 + m)`
with `c(I) = L(m + 1/2)`, `L = 1/(2|J|)`; Poisson summation turns `∑_m Ψ̂_ξ(1/2 + m)` into
`∑_n Ψ_ξ(n) e(-n/2)`, of which only `n = 0` survives because the supports of `√χ_J` and its
translates by `2|J| n` (`n ≠ 0`) are disjoint (`supp √χ ⊆ [-13/25, 13/25]`).

* `Dyadic.dual J m = ⟨-1 - k_J, m⟩`, the interval `I` of length `L = 1/(2|J|)` at position `m`
  (the tile `I × J` has `|I||J| = 1/2`);
* `multJ χ J f = √χ_J f̂`, `psiFn`; `pairing_wavePacketOf_eq` (Parseval: `⟨f, φ_{I×J}⟩ =
  √|I| ∫ √χ_J f̂ e(c(I) ·)`), `fourier_psiFn`, `coeff_mul_fourier`;
* `hasSum_expansion` (the expansion, for every profile `χ`: `χ = ν_i` or `ν_i(-·)`);
* `summable_pairing_dual` (absolutely summable coefficients) and `hasSum_wavePacket_series` (the
  termwise inverse Fourier transform).
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped FourierTransform SchwartzMap ContDiff

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

open PrimeCarleson PrimeCarleson.Proof.Common PrimeCarleson.Proof.Goal0

variable {χ : ℝ → ℝ}

/-- The multiplier `√χ((η - c(J))/|J|) f̂(η)` (`= √φ_J f̂` for `χ = ν_i`). -/
def multJ (χ : ℝ → ℝ) (J : Dyadic) (f : 𝓢(ℝ, ℂ)) (η : ℝ) : ℂ :=
  freqProfile χ J η * 𝓕 (⇑f) η

/-- **Parseval for the coefficients**: `⟨f, φ_{I×J}⟩ = √|I| ∫ √χ_J(η) f̂(η) e(c(I) η) dη`
(`⟨f, φ⟩ = ⟨f̂, φ̂⟩` with `φ̂_{I×J}(η) = √|I| √χ_J(η) e(-c(I) η)`, [O+] L984-L987). -/
theorem pairing_wavePacketOf_eq (hχ : IsProfile χ) (f : 𝓢(ℝ, ℂ)) (I J : Dyadic) :
    pairing f (wavePacketOf χ I J) =
      ((√I.length : ℝ) : ℂ) * ∫ η, multJ χ J f η * e (I.center * η) := by
  set g := hχ.wavePacketSchwartz I J with hg
  have hgf : (⇑g : ℝ → ℂ) = wavePacketOf χ I J := funext (hχ.wavePacketSchwartz_apply I J)
  have h1 := SchwartzMap.integral_inner_fourier_fourier g f
  have e1 : (⇑(𝓕 g : 𝓢(ℝ, ℂ)) : ℝ → ℂ) = 𝓕 (wavePacketOf χ I J) := by
    rw [SchwartzMap.fourier_coe, hgf]
  have e2 : (⇑(𝓕 f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) = 𝓕 (⇑f) := SchwartzMap.fourier_coe f
  have h2 : ∀ ξ, inner ℂ ((𝓕 g : 𝓢(ℝ, ℂ)) ξ) ((𝓕 f : 𝓢(ℝ, ℂ)) ξ) =
      ((√I.length : ℝ) : ℂ) * (multJ χ J f ξ * e (I.center * ξ)) := by
    intro ξ
    rw [RCLike.inner_apply, e1, e2, fourier_wavePacketOf hχ, map_mul, map_mul, ← e_neg]
    simp only [neg_neg, multJ]
    have hr : (starRingEnd ℂ) ((√I.length : ℝ) : ℂ) = ((√I.length : ℝ) : ℂ) := Complex.conj_ofReal _
    have hf : (starRingEnd ℂ) (freqProfile χ J ξ) = freqProfile χ J ξ := by
      unfold freqProfile; exact Complex.conj_ofReal _
    rw [hr, hf]
    ring
  simp_rw [h2] at h1
  rw [integral_const_mul] at h1
  have h3 : ∀ x, inner ℂ (g x) (f x) = f x * (starRingEnd ℂ) (g x) := fun x => by
    simp [RCLike.inner_apply]
  simp_rw [h3] at h1
  unfold pairing
  rw [← hgf]
  exact h1.symm

namespace Dyadic

/-- The dyadic interval of length `1/(2|J|)` at position `m`: the time interval `I` of the tile
`I × J` (`|I||J| = 1/2`). -/
def dual (J : Dyadic) (m : ℤ) : Dyadic := ⟨-1 - J.k, m⟩

/-- The length `1/(2|J|)` of the time intervals of the tiles `I × J`. -/
def dualL (J : Dyadic) : ℝ := (2 : ℝ) ^ (-1 - J.k)

theorem dual_k (J : Dyadic) (m : ℤ) : (J.dual m).k + J.k = -1 := by simp [dual]

theorem center_dual (J : Dyadic) (m : ℤ) : (J.dual m).center = J.dualL * (m + 1 / 2) := rfl

theorem dualL_pos (J : Dyadic) : 0 < J.dualL := zpow_pos (by norm_num) _

theorem dualL_mul (J : Dyadic) : J.dualL * (2 * J.length) = 1 := by
  unfold dualL length
  have h : (2 : ℝ) ^ (-1 - J.k) * 2 ^ J.k = 2⁻¹ := by
    rw [← zpow_add₀ (by norm_num), show -1 - J.k + J.k = -1 by ring, zpow_neg_one]
  calc (2 : ℝ) ^ (-1 - J.k) * (2 * 2 ^ J.k) = 2 * ((2 : ℝ) ^ (-1 - J.k) * 2 ^ J.k) := by ring
    _ = 1 := by rw [h]; norm_num

end Dyadic

theorem contDiff_multJ (hχ : IsProfile χ) (J : Dyadic) (f : 𝓢(ℝ, ℂ)) :
    ContDiff ℝ ∞ (multJ χ J f) := by
  have h1 : ContDiff ℝ ∞ (⇑(𝓕 f : 𝓢(ℝ, ℂ))) := (𝓕 f : 𝓢(ℝ, ℂ)).smooth ⊤
  rw [SchwartzMap.fourier_coe] at h1
  exact (hχ.contDiff_freqProfile J).mul h1

theorem hasCompactSupport_multJ (hχ : IsProfile χ) (J : Dyadic) (f : 𝓢(ℝ, ℂ)) :
    HasCompactSupport (multJ χ J f) :=
  (hχ.hasCompactSupport_freqProfile J).mul_right

/-- The function `Ψ(y) = 2|J| h(ξ - 2|J| y)` -/
def psiFn (χ : ℝ → ℝ) (J : Dyadic) (f : 𝓢(ℝ, ℂ)) (ξ y : ℝ) : ℂ :=
  ((2 * J.length : ℝ) : ℂ) * multJ χ J f (ξ - 2 * J.length * y)

theorem contDiff_psiFn (hχ : IsProfile χ) (J : Dyadic) (f : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    ContDiff ℝ ∞ (psiFn χ J f ξ) := by
  unfold psiFn
  exact contDiff_const.mul ((contDiff_multJ hχ J f).comp
    (contDiff_const.sub (contDiff_const.mul contDiff_id)))

theorem hasCompactSupport_psiFn (hχ : IsProfile χ) (J : Dyadic) (f : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    HasCompactSupport (psiFn χ J f ξ) := by
  have hs : (2 * J.length : ℝ) ≠ 0 := by have := J.length_pos; positivity
  have hemb : Topology.IsClosedEmbedding (fun y : ℝ => ξ - 2 * J.length * y) := by
    have : (fun y : ℝ => ξ - 2 * J.length * y) =
        ⇑((Homeomorph.mulLeft₀ (-(2 * J.length)) (neg_ne_zero.2 hs)).trans
          (Homeomorph.addLeft ξ)) := by
      funext y; simp [sub_eq_add_neg]
    rw [this]
    exact Homeomorph.isClosedEmbedding _
  have := ((hasCompactSupport_multJ hχ J f).comp_isClosedEmbedding hemb).mul_left
    (f := fun _ : ℝ => ((2 * J.length : ℝ) : ℂ))
  exact this

theorem fourier_psiFn (J : Dyadic) (f : 𝓢(ℝ, ℂ)) (ξ w : ℝ) :
    𝓕 (psiFn χ J f ξ) w = ∫ u, multJ χ J f (ξ + u) * e (J.dualL * w * u) := by
  have hs : (0 : ℝ) < 2 * J.length := by have := J.length_pos; positivity
  have hLs := J.dualL_mul
  rw [fourier_eq_integral_e]
  set Φ : ℝ → ℂ := fun u => multJ χ J f (ξ + u) * e (J.dualL * w * u) with hΦ
  have h1 : ∀ y : ℝ, e (-(y * w)) * psiFn χ J f ξ y =
      ((2 * J.length : ℝ) : ℂ) * Φ (-(2 * J.length) * y) := by
    intro y
    simp only [psiFn, hΦ]
    have : J.dualL * w * (-(2 * J.length) * y) = -(y * w) := by
      rw [show J.dualL * w * (-(2 * J.length) * y) = -(J.dualL * (2 * J.length)) * (w * y) by ring,
        hLs]; ring
    rw [this, show ξ + -(2 * J.length) * y = ξ - 2 * J.length * y by ring]
    ring
  simp_rw [h1]
  rw [integral_const_mul, Measure.integral_comp_mul_left Φ (-(2 * J.length))]
  rw [abs_inv, abs_neg, abs_of_pos hs, Complex.real_smul]
  push_cast
  have hne : (J.length : ℂ) ≠ 0 := by exact_mod_cast J.length_ne_zero
  field_simp

/-- The product `⟨f, φ_{I×J}⟩ φ̂_{I×J}(ξ)` in terms of the Fourier transform of `Ψ`. -/
theorem coeff_mul_fourier (hχ : IsProfile χ) (f : 𝓢(ℝ, ℂ)) (J : Dyadic) (m : ℤ) (ξ : ℝ) :
    pairing f (wavePacketOf χ (J.dual m) J) * 𝓕 (wavePacketOf χ (J.dual m) J) ξ =
      (J.dualL : ℂ) * freqProfile χ J ξ * 𝓕 (psiFn χ J f ξ) (1 / 2 + m) := by
  rw [pairing_wavePacketOf_eq hχ, fourier_wavePacketOf hχ, fourier_psiFn]
  set c := (J.dual m).center with hc
  have hc' : c = J.dualL * (1 / 2 + m) := by rw [hc, Dyadic.center_dual]; ring
  have hlen : (J.dual m).length = J.dualL := rfl
  rw [hlen]
  have hsq : ((√J.dualL : ℝ) : ℂ) * ((√J.dualL : ℝ) : ℂ) = (J.dualL : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt J.dualL_pos.le]
  have hshift : (∫ η, multJ χ J f η * e (c * η)) * e (-(c * ξ)) =
      ∫ u, multJ χ J f (ξ + u) * e (J.dualL * (1 / 2 + m) * u) := by
    rw [← integral_mul_const, ← integral_add_left_eq_self (fun η => multJ χ J f η * e (c * η) *
      e (-(c * ξ))) ξ]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only
    rw [mul_assoc, ← e_add, hc']
    congr 2
    ring
  calc ((√J.dualL : ℝ) : ℂ) * (∫ η, multJ χ J f η * e (c * η)) *
        (((√J.dualL : ℝ) : ℂ) * freqProfile χ J ξ * e (-(c * ξ)))
      = (((√J.dualL : ℝ) : ℂ) * ((√J.dualL : ℝ) : ℂ)) * freqProfile χ J ξ *
        ((∫ η, multJ χ J f η * e (c * η)) * e (-(c * ξ))) := by ring
    _ = _ := by rw [hsq, hshift]

theorem contDiff_two_psiFn (hχ : IsProfile χ) (J : Dyadic) (f : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    ContDiff ℝ 2 (psiFn χ J f ξ) := (contDiff_psiFn hχ J f ξ).of_le (by simp)

/-- Poisson summation for `Ψ`: `∑_v Ψ̂(β + v) = ∑_n Ψ(n) e(-nβ)`, both absolutely convergent. -/
theorem hasSum_fourier_psiFn (hχ : IsProfile χ) (f : 𝓢(ℝ, ℂ)) (J : Dyadic) (ξ β : ℝ) :
    HasSum (fun v : ℤ => 𝓕 (psiFn χ J f ξ) (β + v))
      (∑' n : ℤ, psiFn χ J f ξ n * e (-((n : ℝ) * β))) := by
  rw [tsum_mul_e_eq_tsum_fourier_add_of_contDiff_two (contDiff_two_psiFn hχ J f ξ)
    (hasCompactSupport_psiFn hχ J f ξ) β]
  exact (summable_fourier_add_int_of_contDiff_two (contDiff_two_psiFn hχ J f ξ)
    (hasCompactSupport_psiFn hχ J f ξ) β).hasSum

/-- Only the term `n = 0` survives in the periodization where `√χ_J(ξ) ≠ 0`. -/
theorem tsum_psiFn_eq (hχ : IsProfile χ) (f : 𝓢(ℝ, ℂ)) (J : Dyadic) {ξ : ℝ}
    (hξ : freqProfile χ J ξ ≠ 0) :
    ∑' n : ℤ, psiFn χ J f ξ n * e (-((n : ℝ) * (1 / 2))) = psiFn χ J f ξ 0 := by
  rw [tsum_eq_single 0]
  · simp [e_zero]
  · intro n hn
    have hℓ := J.length_pos
    have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      have : (1 : ℤ) ≤ |n| := Int.one_le_abs hn
      exact_mod_cast this
    have hin : (ξ - J.center) / J.length ∈ Icc (-13 / 25 : ℝ) (13 / 25) := by
      by_contra hout
      exact hξ (by simp [freqProfile, hχ.eq_zero _ hout])
    have hout : (ξ - 2 * J.length * n - J.center) / J.length ∉ Icc (-13 / 25 : ℝ) (13 / 25) := by
      intro hmem
      have e1 : (ξ - 2 * J.length * n - J.center) / J.length =
          (ξ - J.center) / J.length - 2 * n := by
        field_simp
        ring
      rw [e1] at hmem
      obtain ⟨a1, a2⟩ := hmem
      obtain ⟨b1, b2⟩ := hin
      rcases abs_cases (n : ℝ) with ⟨h, _⟩ | ⟨h, _⟩
      · rw [h] at hn1; linarith
      · rw [h] at hn1; linarith
    have : psiFn χ J f ξ n = 0 := by
      unfold psiFn multJ freqProfile
      simp [hχ.eq_zero _ hout]
    rw [this]; simp

/-- **The wave-packet expansion** ([O+] L978-L1019): for every `ξ`,
`∑_{|I| = 1/(2|J|)} ⟨f, φ_{I×J}⟩ φ̂_{I×J}(ξ) = f̂(ξ) φ_J(ξ)` (here `φ_J(ξ) = χ((ξ - c(J))/|J|)`,
the sum over `m ∈ ℤ` of the intervals `I = [L m, L(m+1))`, `L = 1/(2|J|)`), the series converging
absolutely. -/
theorem hasSum_expansion (hχ : IsProfile χ) (f : 𝓢(ℝ, ℂ)) (J : Dyadic) (ξ : ℝ) :
    HasSum (fun m : ℤ => pairing f (wavePacketOf χ (J.dual m) J) *
        𝓕 (wavePacketOf χ (J.dual m) J) ξ)
      (((χ ((ξ - J.center) / J.length) : ℝ) : ℂ) * 𝓕 (⇑f) ξ) := by
  have hP := hasSum_fourier_psiFn hχ f J ξ (1 / 2)
  have h1 : HasSum (fun m : ℤ => (J.dualL : ℂ) * freqProfile χ J ξ *
      𝓕 (psiFn χ J f ξ) (1 / 2 + m))
      ((J.dualL : ℂ) * freqProfile χ J ξ * ∑' n : ℤ, psiFn χ J f ξ n *
        e (-((n : ℝ) * (1 / 2)))) := hP.mul_left _
  simp_rw [← coeff_mul_fourier hχ f J] at h1
  by_cases hξ : freqProfile χ J ξ = 0
  · have hχ0 : χ ((ξ - J.center) / J.length) = 0 := by
      have : √(χ ((ξ - J.center) / J.length)) = 0 := by
        have h' := hξ
        unfold freqProfile at h'
        exact_mod_cast h'
      rw [Real.sqrt_eq_zero (hχ.nonneg _)] at this
      exact this
    rw [hχ0]
    convert h1 using 1
    simp [hξ]
  · rw [tsum_psiFn_eq hχ f J hξ] at h1
    convert h1 using 1
    unfold psiFn multJ
    simp only [mul_zero, sub_zero]
    have hLs := J.dualL_mul
    have hsq : (freqProfile χ J ξ) * freqProfile χ J ξ =
        ((χ ((ξ - J.center) / J.length) : ℝ) : ℂ) := by
      unfold freqProfile
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hχ.nonneg _)]
    have hLs' : (J.dualL : ℂ) * ((2 * J.length : ℝ) : ℂ) = 1 := by exact_mod_cast hLs
    rw [← hsq]
    calc freqProfile χ J ξ * freqProfile χ J ξ * 𝓕 (⇑f) ξ
        = ((J.dualL : ℂ) * ((2 * J.length : ℝ) : ℂ)) * (freqProfile χ J ξ *
            freqProfile χ J ξ * 𝓕 (⇑f) ξ) := by rw [hLs', one_mul]
      _ = _ := by ring

/-- The coefficients `⟨f, φ_{I×J}⟩` of the expansion are absolutely summable over the intervals
`I` of length `1/(2|J|)` (they are the Fourier coefficients of the smooth `√χ_J f̂`). -/
theorem summable_pairing_dual (hχ : IsProfile χ) (f : 𝓢(ℝ, ℂ)) (J : Dyadic) :
    Summable (fun m : ℤ => pairing f (wavePacketOf χ (J.dual m) J)) := by
  have h0 := (summable_fourier_add_int_of_contDiff_two (contDiff_two_psiFn hχ J f 0)
    (hasCompactSupport_psiFn hχ J f 0) (1 / 2)).mul_left (((√J.dualL : ℝ)) : ℂ)
  refine h0.congr fun m => ?_
  rw [pairing_wavePacketOf_eq hχ, fourier_psiFn]
  have hlen : (J.dual m).length = J.dualL := rfl
  rw [hlen, Dyadic.center_dual]
  congr 2
  funext u
  simp only [zero_add]
  congr 2
  ring

/-- The series of wave packets, termwise inverse Fourier transform of the expansion:
`∑_{|I| = 1/(2|J|)} ⟨f, φ_{I×J}⟩ φ_{I×J}(x) = ∫ φ_J(η) f̂(η) e(ηx) dη`. -/
theorem hasSum_wavePacket_series (hχ : IsProfile χ) (f : 𝓢(ℝ, ℂ)) (J : Dyadic) (x : ℝ) :
    HasSum (fun m : ℤ => pairing f (wavePacketOf χ (J.dual m) J) *
        wavePacketOf χ (J.dual m) J x)
      (∫ η, ((χ ((η - J.center) / J.length) : ℝ) : ℂ) * 𝓕 (⇑f) η * e (η * x)) := by
  set pk : ℤ → ℝ → ℂ := fun m => wavePacketOf χ (J.dual m) J with hpk
  set c : ℤ → ℂ := fun m => pairing f (pk m) with hc
  set F : ℤ → ℝ → ℂ := fun m η => c m * 𝓕 (pk m) η * e (η * x) with hF
  have hg : ∀ m, (⇑(hχ.wavePacketSchwartz (J.dual m) J) : ℝ → ℂ) = pk m := fun m =>
    funext (hχ.wavePacketSchwartz_apply (J.dual m) J)
  have hFint : ∀ m, Integrable (F m) := by
    intro m
    have := integrable_fourier_mul_e (hχ.wavePacketSchwartz (J.dual m) J) x
    rw [hg m] at this
    have := this.const_mul (c m)
    refine this.congr (Filter.Eventually.of_forall fun η => ?_)
    simp only [hF]; ring
  have hnorm : ∀ m η, ‖F m η‖ = ‖c m‖ * (√J.dualL * ‖freqProfile χ J η‖) := by
    intro m η
    simp only [hF, hpk, norm_mul, norm_e, mul_one]
    rw [fourier_wavePacketOf hχ, norm_mul, norm_mul, norm_e, mul_one]
    have : ‖((√(J.dual m).length : ℝ) : ℂ)‖ = √J.dualL := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]; rfl
    rw [this]
  have hsum : Summable fun m => ∫ η, ‖F m η‖ := by
    simp_rw [hnorm]
    simp_rw [integral_const_mul]
    exact (summable_pairing_dual hχ f J).norm.mul_right _
  have hmain := hasSum_integral_of_summable_integral_norm hFint hsum
  have h1 : ∀ m, ∫ η, F m η = c m * pk m x := by
    intro m
    have hinv := fourier_inversion_schwartz (hχ.wavePacketSchwartz (J.dual m) J) x
    rw [hg m] at hinv
    simp only [hF]
    simp_rw [mul_assoc]
    rw [integral_const_mul, ← hinv]
  have h2 : ∀ η, ∑' m, F m η =
      ((χ ((η - J.center) / J.length) : ℝ) : ℂ) * 𝓕 (⇑f) η * e (η * x) := by
    intro η
    have h3 := (hasSum_expansion hχ f J η).tsum_eq
    simp only [hF]
    rw [tsum_mul_right]
    exact congrArg (· * e (η * x)) h3
  simp_rw [h1, h2] at hmain
  exact hmain

end PrimeCarleson.Proof.Oplus
