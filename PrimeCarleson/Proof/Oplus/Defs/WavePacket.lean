module

public import PrimeCarleson.Proof.Oplus.Defs.Cutoff
public import PrimeCarleson.Proof.Common.FourierR
public import PrimeCarleson.Proof.Goal0.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Wave packets of tiles ([O+] L972-L987)

[O+] L975-L976: "For every tile `P = I × J`, define
`φ_P(x) = |I|^{1/2} 𝓕^{-1}[√φ_J](x - c(I))` where `c(I)` is the center of `I` and `𝓕^{-1}` denotes
the inverse Fourier transform"; L984-L985: `φ̂_P(ξ) = √|I| √φ_J(ξ) e^{-2πi c(I) ξ}`. Source: [O+],
L930–L976 (the dyadic intervals and tiles are in `Defs/Dyadic.lean`). The
Fourier conventions are those of `Common/FourierR.lean`: `e(t) = exp(2πit)`, Mathlib's `𝓕`, `𝓕⁻`.

* `wavePacketOf χ I J`: the packet `|I|^{1/2} 𝓕⁻[√(χ((· - c(J))/|J|))](· - c(I))` for a frequency
  profile `χ`;
* `wavePacket i I J`: the paper's `φ_P` for the tile `I × J` and the neighbour index `i = i(J) ∈
  {-1,0,1}` (L964; the packet is not a function of `J` alone), i.e. the profile `χ = ν_i` with
  the explicit `ν` of `Defs/Cutoff.lean`, whose `√χ((ξ - c(J))/|J|) = √φ_{J,i}(ξ)`
  (`phiDyadic_eq_nuFamily`); the reflected packet (profile `ν_i(-·)`, L1119-L1121) is
  `wavePacketOf (fun η => nuFamily i (-η)) I J`;
* for a profile (`IsProfile χ`): `wavePacketSchwartz` (the packet is a Schwartz function),
  `fourier_wavePacketOf` (`φ̂_P(ξ) = √|I| √χ((ξ - c(J))/|J|) e(-c(I)ξ)`),
  `support_fourier_wavePacketOf` and `tsupport_fourier_wavePacketOf_subset_dilate`
  (the Fourier transform is supported in `[c(J) - 13/25 |J|, c(J) + 13/25 |J|] ⊆ (26/25) J`).
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped FourierTransform SchwartzMap ContDiff

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

open PrimeCarleson PrimeCarleson.Proof.Common PrimeCarleson.Proof.Goal0

/-! ### Definitions -/

/-- The frequency profile `ξ ↦ √χ((ξ - c(J))/|J|)` of a frequency interval `J`, complex valued:
for `χ = ν_i` this is `√φ_{J,i}`. -/
def freqProfile (χ : ℝ → ℝ) (J : Dyadic) (ξ : ℝ) : ℂ :=
  ((√(χ ((ξ - J.center) / J.length)) : ℝ) : ℂ)

/-- The wave packet of the tile `I × J` for the frequency profile `χ`:
`|I|^{1/2} 𝓕⁻[√χ((· - c(J))/|J|)](x - c(I))` ([O+] L975-L976). -/
def wavePacketOf (χ : ℝ → ℝ) (I J : Dyadic) (x : ℝ) : ℂ :=
  ((√I.length : ℝ) : ℂ) * 𝓕⁻ (freqProfile χ J) (x - I.center)

/-- The wave packet `φ_P` of the tile `P = I × J` ([O+] L975-L976), for the index `i = i(J) ∈
{-1, 0, 1}` of L964: `|I|^{1/2} 𝓕⁻[√φ_{J,i}](x - c(I))`, with the explicit cutoff `ν`. -/
def wavePacket (i : ℤ) (I J : Dyadic) : ℝ → ℂ := wavePacketOf (nuFamily i) I J

/-- The wave packet of a tile `P` for the index `i`. -/
def Tile.wavePacket (i : ℤ) (P : Tile) : ℝ → ℂ := PrimeCarleson.Proof.Oplus.wavePacket i P.I P.J

/-! ### The packet is a Schwartz function -/

variable {χ : ℝ → ℝ}

/-- The frequency profile of a profile is `C^∞`. -/
theorem IsProfile.contDiff_freqProfile (hχ : IsProfile χ) (J : Dyadic) :
    ContDiff ℝ ∞ (freqProfile χ J) :=
  Complex.ofRealCLM.contDiff.comp
    (hχ.contDiff_sqrt.comp ((contDiff_id.sub contDiff_const).div_const J.length))

/-- The frequency profile has compact support. -/
theorem IsProfile.hasCompactSupport_freqProfile (hχ : IsProfile χ) (J : Dyadic) :
    HasCompactSupport (freqProfile χ J) := by
  refine HasCompactSupport.intro
    (isCompact_Icc (a := J.center - 13 / 25 * J.length) (b := J.center + 13 / 25 * J.length))
    fun ξ hξ => ?_
  have hL := J.length_pos
  have : (ξ - J.center) / J.length ∉ Icc (-13 / 25 : ℝ) (13 / 25) := by
    intro h
    apply hξ
    rw [mem_Icc, le_div_iff₀ hL, div_le_iff₀ hL] at h
    constructor <;> nlinarith [h.1, h.2]
  simp [freqProfile, hχ.eq_zero _ this]

/-- The frequency profile as a Schwartz function. -/
def IsProfile.freqSchwartz (hχ : IsProfile χ) (J : Dyadic) : 𝓢(ℝ, ℂ) :=
  (hχ.hasCompactSupport_freqProfile J).toSchwartzMap (hχ.contDiff_freqProfile J)

/-- The wave packet of a profile is a Schwartz function (its Fourier transform is smooth with
compact support). -/
def IsProfile.wavePacketSchwartz (hχ : IsProfile χ) (I J : Dyadic) : 𝓢(ℝ, ℂ) :=
  ((√I.length : ℝ) : ℂ) • (𝓕⁻ (hχ.freqSchwartz J)).compSubConstCLM ℂ I.center

/-- Evaluation of `wavePacketSchwartz`. -/
theorem IsProfile.wavePacketSchwartz_apply (hχ : IsProfile χ) (I J : Dyadic) (x : ℝ) :
    hχ.wavePacketSchwartz I J x = wavePacketOf χ I J x := by
  simp only [IsProfile.wavePacketSchwartz, smul_apply, SchwartzMap.compSubConstCLM_apply,
    smul_eq_mul, wavePacketOf]
  rw [SchwartzMap.fourierInv_coe]
  rfl

/-- A wave packet is continuous. -/
theorem IsProfile.continuous_wavePacketOf (hχ : IsProfile χ) (I J : Dyadic) :
    Continuous (wavePacketOf χ I J) := by
  have : wavePacketOf χ I J = ⇑(hχ.wavePacketSchwartz I J) :=
    funext fun x => (hχ.wavePacketSchwartz_apply I J x).symm
  rw [this]; exact (hχ.wavePacketSchwartz I J).continuous

/-- A wave packet is integrable. -/
theorem IsProfile.integrable_wavePacketOf (hχ : IsProfile χ) (I J : Dyadic) :
    Integrable (wavePacketOf χ I J) := by
  have : wavePacketOf χ I J = ⇑(hχ.wavePacketSchwartz I J) :=
    funext fun x => (hχ.wavePacketSchwartz_apply I J x).symm
  rw [this]; exact (hχ.wavePacketSchwartz I J).integrable

/-- A wave packet is in `L²`. -/
theorem IsProfile.memLp_wavePacketOf (hχ : IsProfile χ) (I J : Dyadic) :
    MemLp (wavePacketOf χ I J) 2 volume := by
  have : wavePacketOf χ I J = ⇑(hχ.wavePacketSchwartz I J) :=
    funext fun x => (hχ.wavePacketSchwartz_apply I J x).symm
  rw [this]; exact (hχ.wavePacketSchwartz I J).memLp 2 volume

/-! ### The Fourier transform of a wave packet -/

/-- Translation: `(G(· - c))^ (ξ) = e(-cξ) Ĝ(ξ)`. -/
theorem fourier_comp_sub_const (G : ℝ → ℂ) (c ξ : ℝ) :
    𝓕 (fun x => G (x - c)) ξ = e (-(c * ξ)) * 𝓕 G ξ := by
  rw [fourier_eq_integral_e, fourier_eq_integral_e, ← integral_const_mul]
  rw [← integral_add_right_eq_self (fun x => e (-(x * ξ)) * G (x - c)) c]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [add_sub_cancel_right]
  rw [show -((x + c) * ξ) = -(c * ξ) + -(x * ξ) by ring, e_add]
  ring

/-- Scalars: `(a G)^ = a Ĝ`. -/
theorem fourier_const_mul (a : ℂ) (G : ℝ → ℂ) (ξ : ℝ) :
    𝓕 (fun x => a * G x) ξ = a * 𝓕 G ξ := by
  rw [fourier_eq_integral_e, fourier_eq_integral_e, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  ring

/-- `𝓕 𝓕⁻ g = g` for the frequency profile `g`. -/
theorem fourier_fourierInv_freqSchwartz (hχ : IsProfile χ) (J : Dyadic) (ξ : ℝ) :
    𝓕 (𝓕⁻ (freqProfile χ J)) ξ = freqProfile χ J ξ := by
  have h : (𝓕 (𝓕⁻ (hχ.freqSchwartz J)) : 𝓢(ℝ, ℂ)) = hχ.freqSchwartz J :=
    FourierInvPair.fourier_fourierInv_eq (hχ.freqSchwartz J)
  have h2 := congrArg (fun F : 𝓢(ℝ, ℂ) => F ξ) h
  rw [SchwartzMap.fourier_coe, SchwartzMap.fourierInv_coe] at h2
  exact h2

/-- **`φ̂_P(ξ) = √|I| √χ((ξ - c(J))/|J|) e(-c(I) ξ)`** ([O+] L984-L985; for `χ = ν_i`,
`√χ((ξ - c(J))/|J|) = √φ_J(ξ)`). -/
theorem fourier_wavePacketOf (hχ : IsProfile χ) (I J : Dyadic) (ξ : ℝ) :
    𝓕 (wavePacketOf χ I J) ξ =
      ((√I.length : ℝ) : ℂ) * freqProfile χ J ξ * e (-(I.center * ξ)) := by
  unfold wavePacketOf
  rw [fourier_const_mul, fourier_comp_sub_const (𝓕⁻ (freqProfile χ J)) I.center ξ,
    fourier_fourierInv_freqSchwartz hχ J ξ]
  ring

/-- The Fourier transform of a wave packet is supported in
`[c(J) - (13/25)|J|, c(J) + (13/25)|J|]`, inside the `26/25`-dilate of `J`. -/
theorem support_fourier_wavePacketOf (hχ : IsProfile χ) (I J : Dyadic) :
    Function.support (𝓕 (wavePacketOf χ I J)) ⊆
      Icc (J.center - 13 / 25 * J.length) (J.center + 13 / 25 * J.length) := by
  intro ξ hξ
  rw [Function.mem_support, fourier_wavePacketOf hχ] at hξ
  have hL := J.length_pos
  by_contra hmem
  apply hξ
  have : (ξ - J.center) / J.length ∉ Icc (-13 / 25 : ℝ) (13 / 25) := by
    intro h
    apply hmem
    rw [mem_Icc, le_div_iff₀ hL, div_le_iff₀ hL] at h
    constructor <;> nlinarith [h.1, h.2]
  simp [freqProfile, hχ.eq_zero _ this]

/-- The closed support (`supp` of [O+] L1170-L1171) of `φ̂_P` lies in `C J` for every
`C > 26/25`; in particular in `C₃ J` for `C₃ = 11/10`. -/
theorem tsupport_fourier_wavePacketOf_subset_dilate (hχ : IsProfile χ) (I J : Dyadic) {C : ℝ}
    (hC : 26 / 25 < C) : tsupport (𝓕 (wavePacketOf χ I J)) ⊆ J.dilate C := by
  refine closure_minimal (support_fourier_wavePacketOf hχ I J) ?_ |>.trans fun ξ hξ => ?_
  · exact isClosed_Icc
  · have hL := J.length_pos
    unfold Dyadic.dilate
    constructor <;> nlinarith [hξ.1, hξ.2]

/-! ### Choice of the profile and the coefficients `⟨f, φ_P⟩` -/

/-- Which of the two profiles `√ν_i` (`plain`) and `√ν_i(-·)` (`reflected`, L1119-L1121 of [O+])
is used. -/
inductive Orientation where
  | plain
  | reflected
  deriving DecidableEq

/-- A choice of wave-packet profile: the index `i ∈ {-1, 0, 1}` and one of `ν_i`, `ν_i(-·)`. All
later sections of [O+] are valid for every such choice (the reflection of L1113-L1118 produces the
`reflected` ones). -/
structure ProfileChoice where
  /-- The neighbour index `i ∈ {-1, 0, 1}`. -/
  i : ℤ
  neg_one_le : -1 ≤ i
  le_one : i ≤ 1
  /-- `ν_i` or `ν_i(-·)`. -/
  orientation : Orientation

namespace ProfileChoice

/-- The frequency profile `χ` of the choice: `ν_i` or `η ↦ ν_i(-η)`. -/
def fn (c : ProfileChoice) : ℝ → ℝ :=
  match c.orientation with
  | Orientation.plain => nuFamily c.i
  | Orientation.reflected => fun η => nuFamily c.i (-η)

/-- Every choice is a profile in the sense of `IsProfile`. -/
theorem isProfile (c : ProfileChoice) : IsProfile c.fn := by
  unfold fn
  cases h : c.orientation
  · exact isProfile_nuFamily c.neg_one_le c.le_one
  · exact isProfile_nuFamily_neg c.neg_one_le c.le_one

end ProfileChoice

/-- The coefficient `⟨f, φ⟩ = ∫ f φ̄` ([O+] L976: `⟨f, φ_P⟩`; the inner product is linear in
`f`). -/
def pairing (f φ : ℝ → ℂ) : ℂ := ∫ x, f x * (starRingEnd ℂ) (φ x)

end PrimeCarleson.Proof.Oplus
