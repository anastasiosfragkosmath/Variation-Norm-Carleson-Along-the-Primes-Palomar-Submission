module

public import PrimeCarleson.Proof.Oplus.TreeSmall.TreeSum
public import PrimeCarleson.Proof.Oplus.SquareFunction.Main
public import PrimeCarleson.Proof.Oplus.TreeLarge.Scales
public import Mathlib.Analysis.Fourier.Convolution

/-!
# Fourier analysis for the multiplier representation of a tree sum ([O+] L2295-L2370)

Source: [O+] `schwartzchoice`, L2295–L2310; [O+] `schwartzchoice`, L2311–L2316; [O+]
`treeestimatelargeintervals`, L2350–L2370 (L2295-L2335 and L2350-L2370). The tree sum of an
`l`-overlapping tree `T` with top frequency `ξ_T` is `G = ∑_{P ∈ T} ⟨f, φ_P⟩ φ_P`; the
Fourier-analytic facts about it are phrased for the *demodulated* function
`g = e_T^{-1} G = ∑_P ⟨f, φ_P⟩ φ_P e(-· ξ_T)` (`modTreeFn`), and the Schwartz averages
`A_ℓ g = ψ_ℓ * g` of `SquareFunction/Convolution.lean` (`schwartzAvg`), since
`|(e_T ψ_ℓ) * G| = |ψ_ℓ * g|`.

* `FNice h`: continuous, integrable, with integrable Fourier transform: the class in which
  Fourier inversion holds (`FNice.eq_of_fourier_eq`); closed under finite combinations, modulation
  and convolution with `ψ_k` (`fnice_schwartzAvg`: `𝓕(ψ_k * h) = ψ̂(2^k ·) ĥ`);
* `fourier_schwartzScale`: `𝓕(ψ_k)(ζ) = ψ̂(2^k ζ)`;
* `modPacket ch ξ P = φ_P e(-· ξ)`: `𝓕(φ_P e(-· ξ))(ζ) = φ̂_P(ζ + ξ)` is supported where
  `ζ + ξ ∈ C₃ ω_u`;
* `schwartzAvg_modTreeFn` (**frequency localization**, [O+] L2311-L2316):
  for an `l`-overlapping tree, `ψ_ℓ * g = ∑_{P : |I| ≥ 2^ℓ} ⟨f, φ_P⟩ φ_P e_T^{-1}` for every `ℓ`
  with
  `2^ℓ ≤ |I|` or `2^ℓ ≥ (2C₁/(C₂ - C₃)) |I|` for each tile. The cutoff is `ψ̂ = 1` on
  `|ξ| ≤ (C₁ + C₃)/4` and `ψ̂ = 0` for `|ξ| ≥ C₁/2` (`IsPsiCutoff (C₁/4) (C₃/4) ψ`) instead of the
  printed `ψ̂ = 1` on `|ξ| ≤ C₁ + C₃`, `ψ̂ = 0` for `|ξ| ≥ 2C₁`: with the printed support the
  smaller scale `|I'| ≤ |I|/32` of a tree with `m = 1` can have `ξ_T` at distance only
  `≈ 7.7/|I|` from `supp φ̂_{P'}`, so `ψ̂_ℓ(· - ξ_T) = 1` there and the identity fails;
* `schwartzAvg_reproduce` (**local constancy**, [O+] L2353-L2359): for
  `c + 1 ≤ k₁ ≤ k₂`, `ψ_{k₁} * g - ψ_{k₂} * g = ψ_c * (ψ_{k₁} * g - ψ_{k₂} * g)`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal SchwartzMap FourierTransform Convolution

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

open PrimeCarleson PrimeCarleson.Proof.Common PrimeCarleson.Proof.Goal0

/-- Regularity class for Fourier inversion. -/
structure FNice (h : ℝ → ℂ) : Prop where
  continuous : Continuous h
  integrable : Integrable h
  integrable_fourier : Integrable (𝓕 h)

/-- `e(-xξ) h(x)` is integrable when `h` is. -/
theorem integrable_e_neg_mul {h : ℝ → ℂ} (hh : Integrable h) (ξ : ℝ) :
    Integrable (fun x => e (-(x * ξ)) * h x) :=
  hh.bdd_mul (c := 1)
    (continuous_e.comp (continuous_id.mul continuous_const).neg).aestronglyMeasurable
    (Eventually.of_forall fun x => by rw [norm_e])

/-- The Fourier transform is additive on integrable functions. -/
theorem fourier_add' {h₁ h₂ : ℝ → ℂ} (i₁ : Integrable h₁) (i₂ : Integrable h₂) (ξ : ℝ) :
    𝓕 (fun x => h₁ x + h₂ x) ξ = 𝓕 h₁ ξ + 𝓕 h₂ ξ := by
  simp only [fourier_eq_integral_e, mul_add]
  exact integral_add (integrable_e_neg_mul i₁ ξ) (integrable_e_neg_mul i₂ ξ)

/-- The Fourier transform commutes with multiplication by a constant. -/
theorem fourier_smul' {h : ℝ → ℂ} (c : ℂ) (ξ : ℝ) :
    𝓕 (fun x => c * h x) ξ = c * 𝓕 h ξ := by
  simp only [fourier_eq_integral_e]
  rw [← integral_const_mul]
  congr 1
  ext x
  ring

/-- The Fourier transform is subtractive on integrable functions. -/
theorem fourier_sub' {h₁ h₂ : ℝ → ℂ} (i₁ : Integrable h₁) (i₂ : Integrable h₂) (ξ : ℝ) :
    𝓕 (fun x => h₁ x - h₂ x) ξ = 𝓕 h₁ ξ - 𝓕 h₂ ξ := by
  simp only [fourier_eq_integral_e, mul_sub]
  exact integral_sub (integrable_e_neg_mul i₁ ξ) (integrable_e_neg_mul i₂ ξ)

/-- `FNice` is closed under subtraction. -/
theorem FNice.sub {h₁ h₂ : ℝ → ℂ} (a : FNice h₁) (b : FNice h₂) : FNice (fun x => h₁ x - h₂ x) where
  continuous := a.continuous.sub b.continuous
  integrable := a.integrable.sub b.integrable
  integrable_fourier := by
    have : 𝓕 (fun x => h₁ x - h₂ x) = fun ξ => 𝓕 h₁ ξ - 𝓕 h₂ ξ :=
      funext (fourier_sub' a.integrable b.integrable)
    rw [this]
    exact a.integrable_fourier.sub b.integrable_fourier

/-- `FNice` is closed under multiplication by a constant. -/
theorem FNice.const_mul {h : ℝ → ℂ} (a : FNice h) (c : ℂ) : FNice (fun x => c * h x) where
  continuous := continuous_const.mul a.continuous
  integrable := a.integrable.const_mul c
  integrable_fourier := by
    have : 𝓕 (fun x => c * h x) = fun ξ => c * 𝓕 h ξ := funext (fourier_smul' c)
    rw [this]
    exact a.integrable_fourier.const_mul c

/-- The Fourier transform of a finite sum of integrable functions. -/
theorem fourier_finset_sum {ι : Type*} (s : Finset ι) (h : ι → ℝ → ℂ)
    (hi : ∀ i ∈ s, Integrable (h i)) (ξ : ℝ) :
    𝓕 (fun x => ∑ i ∈ s, h i x) ξ = ∑ i ∈ s, 𝓕 (h i) ξ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [fourier_eq_integral_e]
  | insert a s ha ih =>
    have e1 : (fun x => ∑ i ∈ insert a s, h i x) = fun x => h a x + ∑ i ∈ s, h i x := by
      funext x; rw [Finset.sum_insert ha]
    rw [e1, fourier_add' (hi a (Finset.mem_insert_self a s))
      (integrable_finsetSum _ fun i hi' => hi i (Finset.mem_insert_of_mem hi')),
      Finset.sum_insert ha,
      ih fun i hi' => hi i (Finset.mem_insert_of_mem hi')]

/-- `FNice` is closed under finite sums. -/
theorem FNice.finset_sum {ι : Type*} (s : Finset ι) (h : ι → ℝ → ℂ) (hi : ∀ i ∈ s, FNice (h i)) :
    FNice (fun x => ∑ i ∈ s, h i x) where
  continuous := continuous_finsetSum _ fun i hi' => (hi i hi').continuous
  integrable := integrable_finsetSum _ fun i hi' => (hi i hi').integrable
  integrable_fourier := by
    have : 𝓕 (fun x => ∑ i ∈ s, h i x) = fun ξ => ∑ i ∈ s, 𝓕 (h i) ξ :=
      funext (fourier_finset_sum s h fun i hi' => (hi i hi').integrable)
    rw [this]
    exact integrable_finsetSum _ fun i hi' => (hi i hi').integrable_fourier

/-- Fourier uniqueness in the class `FNice`. -/
theorem FNice.eq_of_fourier_eq {h₁ h₂ : ℝ → ℂ} (a : FNice h₁) (b : FNice h₂)
    (h : ∀ ζ, 𝓕 h₁ ζ = 𝓕 h₂ ζ) : h₁ = h₂ := by
  have e : 𝓕 h₁ = 𝓕 h₂ := funext h
  rw [← a.continuous.fourierInv_fourier_eq a.integrable a.integrable_fourier,
    ← b.continuous.fourierInv_fourier_eq b.integrable b.integrable_fourier, e]

/-- A Schwartz function is `FNice`. -/
theorem FNice.of_schwartz (h : 𝓢(ℝ, ℂ)) : FNice h where
  continuous := h.continuous
  integrable := h.integrable
  integrable_fourier := (𝓕 h).integrable


/-! ### Scaling and convolution -/

theorem fourier_schwartzScale (ψ : ℝ → ℂ) (k : ℤ) (ζ : ℝ) :
    𝓕 (schwartzScale ψ k) ζ = 𝓕 ψ ((2 : ℝ) ^ k * ζ) := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (-k) := by positivity
  have hk : (2 : ℝ) ^ (-k) * (2 : ℝ) ^ k = 1 := by
    rw [← zpow_add₀ (by norm_num)]; simp
  rw [fourier_eq_integral_e, fourier_eq_integral_e]
  set a : ℝ := (2 : ℝ) ^ (-k) with ha
  have key : ∀ x : ℝ, e (-(x * ζ)) * schwartzScale ψ k x =
      (a : ℂ) * (fun u : ℝ => e (-(u * ((2 : ℝ) ^ k * ζ))) * ψ u) (a * x) := by
    intro x
    have hx : a * x * ((2 : ℝ) ^ k * ζ) = x * ζ := by
      calc a * x * ((2 : ℝ) ^ k * ζ) = (a * (2 : ℝ) ^ k) * (x * ζ) := by ring
        _ = x * ζ := by rw [hk, one_mul]
    simp only [schwartzScale]
    rw [hx]
    ring
  simp_rw [key]
  rw [integral_const_mul, Measure.integral_comp_mul_left
    (fun u : ℝ => e (-(u * ((2 : ℝ) ^ k * ζ))) * ψ u) a, abs_of_pos (inv_pos.2 h2),
    Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ h2.ne']
  simp

/-- `ψ_k` is integrable for a Schwartz function `ψ`. -/
theorem integrable_schwartzScale (ψ : 𝓢(ℝ, ℂ)) (k : ℤ) : Integrable (schwartzScale ψ k) :=
  ⟨(continuous_schwartzScale ψ k).aestronglyMeasurable, lintegral_enorm_schwartzScale_lt_top ψ k⟩

/-- `A_k B = B ⋆ ψ_k`: the Schwartz average is a convolution (Mathlib `⋆`). -/
theorem schwartzAvg_eq_convolution (ψ : ℝ → ℂ) (k : ℤ) (B : ℝ → ℂ) :
    schwartzAvg ψ k B = B ⋆[ContinuousLinearMap.mul ℂ ℂ] schwartzScale ψ k := by
  funext x
  simp only [schwartzAvg, MeasureTheory.convolution_def, ContinuousLinearMap.mul_apply']
  congr 1
  ext y
  ring

/-- The Fourier transform of a Schwartz function is bounded. -/
theorem bounded_fourier_schwartz (ψ : 𝓢(ℝ, ℂ)) : ∃ M : ℝ, 0 ≤ M ∧ ∀ ζ, ‖𝓕 (⇑ψ) ζ‖ ≤ M := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_schwartz (𝓕 ψ)
  exact ⟨M, hM0, fun ζ => by simpa [SchwartzMap.fourier_coe] using hM ζ⟩

/-- `ψ_k * B` is `FNice`, with Fourier transform `ψ̂(2^k ·) B̂`, if `B` is. -/
theorem fnice_schwartzAvg (ψ : 𝓢(ℝ, ℂ)) (k : ℤ) {B : ℝ → ℂ} (hB : FNice B) :
    FNice (schwartzAvg ψ k B) ∧
      ∀ ζ, 𝓕 (schwartzAvg ψ k B) ζ = 𝓕 (⇑ψ) ((2 : ℝ) ^ k * ζ) * 𝓕 B ζ := by
  have hψk : Integrable (schwartzScale ψ k) := integrable_schwartzScale ψ k
  have hform : ∀ ζ, 𝓕 (schwartzAvg ψ k B) ζ = 𝓕 (⇑ψ) ((2 : ℝ) ^ k * ζ) * 𝓕 B ζ := by
    intro ζ
    rw [schwartzAvg_eq_convolution, Real.fourier_mul_convolution_eq hB.integrable hψk,
      fourier_schwartzScale, mul_comm]
  refine ⟨⟨?_, ?_, ?_⟩, hform⟩
  · rw [schwartzAvg_eq_convolution]
    refine BddAbove.continuous_convolution_right_of_integrable (ContinuousLinearMap.mul ℂ ℂ) ?_
      hB.integrable (continuous_schwartzScale ψ k)
    obtain ⟨M, -, hM⟩ := exists_bound_schwartz ψ
    refine ⟨(2 : ℝ) ^ (-k) * M, ?_⟩
    rintro _ ⟨x, rfl⟩
    have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ (-k) := by positivity
    simp only [schwartzScale, norm_mul, Complex.norm_real, Real.norm_of_nonneg h2]
    exact mul_le_mul_of_nonneg_left (hM _) h2
  · rw [schwartzAvg_eq_convolution]
    exact hB.integrable.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hψk
  · have : 𝓕 (schwartzAvg ψ k B) = fun ζ => 𝓕 (⇑ψ) ((2 : ℝ) ^ k * ζ) * 𝓕 B ζ := funext hform
    rw [this]
    obtain ⟨M, -, hM⟩ := bounded_fourier_schwartz ψ
    refine Integrable.bdd_mul hB.integrable_fourier ?_ (c := M) (Eventually.of_forall fun ζ => hM _)
    exact ((SchwartzMap.continuous (𝓕 ψ)).comp
      (continuous_const.mul continuous_id)).aestronglyMeasurable


/-! ### Modulated wave packets -/

theorem FNice.mul_e_neg {h : ℝ → ℂ} (a : FNice h) (β : ℝ) :
    FNice (fun x => h x * e (-(x * β))) where
  continuous := a.continuous.mul (continuous_e.comp (continuous_id.mul continuous_const).neg)
  integrable := by
    refine a.integrable.norm.mono'
      (a.continuous.mul (continuous_e.comp
        (continuous_id.mul continuous_const).neg)).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [norm_mul, norm_e, mul_one]
  integrable_fourier := by
    have : 𝓕 (fun x => h x * e (-(x * β))) = fun ξ => 𝓕 h (ξ + β) :=
      funext fun ξ => fourier_mul_e_neg h β ξ
    rw [this]
    exact a.integrable_fourier.comp_add_right β

/-- The wave packet of a multitile is `FNice` (it is a Schwartz function). -/
theorem fnice_wavePacket {ρ : Idx} (ch : ProfileChoice) (P : Multitile ρ) :
    FNice (P.wavePacket ch) := by
  have h := FNice.of_schwartz (ch.isProfile.wavePacketSchwartz P.I P.ωu)
  have e : (⇑(ch.isProfile.wavePacketSchwartz P.I P.ωu) : ℝ → ℂ) = P.wavePacket ch :=
    funext (ch.isProfile.wavePacketSchwartz_apply P.I P.ωu)
  rwa [e] at h

/-- The wave packet modulated by `e(-xβ)`: `φ_P e_β^{-1}`. -/
def modPacket {ρ : Idx} (ch : ProfileChoice) (β : ℝ) (P : Multitile ρ) (x : ℝ) : ℂ :=
  P.wavePacket ch x * e (-(x * β))

/-- The modulated wave packet `φ_P e(-· β)` is `FNice`. -/
theorem fnice_modPacket {ρ : Idx} (ch : ProfileChoice) (β : ℝ) (P : Multitile ρ) :
    FNice (modPacket ch β P) :=
  (fnice_wavePacket ch P).mul_e_neg β

/-- `𝓕(φ_P e(-· β))(ζ) = φ̂_P(ζ + β)`. -/
theorem fourier_modPacket {ρ : Idx} (ch : ProfileChoice) (β : ℝ) (P : Multitile ρ) (ζ : ℝ) :
    𝓕 (modPacket ch β P) ζ = 𝓕 (P.wavePacket ch) (ζ + β) :=
  fourier_mul_e_neg _ β ζ

section Localization

variable {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ C₃ : ℝ}

omit [Fact ρ.IsOneOrTwo] in
/-- The Fourier transform of `φ_P e(-· β)` at `ζ` is nonzero only if `ζ + β ∈ C₃ ω_u`. -/
theorem mem_dilate_of_fourier_modPacket_ne (hC : AdmissibleConstants C₁ C₂ C₃)
    (ch : ProfileChoice) (β ζ : ℝ) (P : Multitile ρ) (h : 𝓕 (modPacket ch β P) ζ ≠ 0) :
    ζ + β ∈ P.ωu.dilate C₃ := by
  rw [fourier_modPacket] at h
  by_contra hn
  have hts := hC.packet_support ch P.I P.ωu
  have : ζ + β ∉ tsupport (𝓕 (wavePacketOf ch.fn P.I P.ωu)) := fun hh => hn (hts hh)
  exact h (image_eq_zero_of_notMem_tsupport this)

/-- `|ζ + ξ_T - c| ≤ C₃ L/2` and `ξ_T ∈ C₂ ω_l ⊂ C₁ ω_u` give `|ζ| < (C₁ + C₃) L / 2`. -/
theorem abs_lt_of_overlapping (hC : AdmissibleConstants C₁ C₂ C₃) (hρ : ρ.IsStd)
    {P : Multitile ρ} {ξ ζ : ℝ} (hξ : ξ ∈ P.ωlDil C₂) (hζ : ζ + ξ ∈ P.ωu.dilate C₃) :
    |ζ| < (C₁ + C₃) * P.ωu.length / 2 := by
  have h1 : ξ ∈ P.ωu.dilate C₁ := (hC.geometry ρ hρ Fact.out P.ωu).2.2.1 hξ
  rw [Dyadic.mem_dilate] at h1 hζ
  rw [abs_lt]
  constructor <;> linarith [h1.1, h1.2, hζ.1, hζ.2]

/-- `ζ + ξ_T ∈ C₃ ω_u` and `ξ_T ∈ C₂ ω_l` give `ζ > (C₂ - C₃)|ω_u|/2` (using `C₂ ≤ m + 1`). -/
theorem lt_of_overlapping (hC : AdmissibleConstants C₁ C₂ C₃) (hρ : ρ.IsStd)
    {P : Multitile ρ} {ξ ζ : ℝ} (hξ : ξ ∈ P.ωlDil C₂) (hζ : ζ + ξ ∈ P.ωu.dilate C₃) :
    (C₂ - C₃) * P.ωu.length / 2 < ζ := by
  have hm := hC.le_m_add_one hρ
  have hL := P.ωu.length_pos
  rw [Multitile.ωlDil_eq] at hξ
  rw [Dyadic.mem_dilate] at hζ
  have : C₂ * P.ωu.length ≤ ((ρ.m : ℝ) + 1) * P.ωu.length := mul_le_mul_of_nonneg_right hm hL.le
  linarith [hξ.2, hζ.1]

variable {ψ : 𝓢(ℝ, ℂ)}

/-- `ψ̂(2^ℓ ζ) · 𝓕(φ_P e_T^{-1})(ζ) = 𝓕(φ_P e_T^{-1})(ζ)` when `2^ℓ ≤ |I|`. -/
theorem fourier_psi_mul_eq_self (hC : AdmissibleConstants C₁ C₂ C₃) (hρ : ρ.IsStd)
    (hψ : IsPsiCutoff (C₁ / 4) (C₃ / 4) ψ) (ch : ProfileChoice) {P : Multitile ρ} {ξ : ℝ}
    (hξ : ξ ∈ P.ωlDil C₂) {ℓ : ℤ} (hℓ : ℓ ≤ P.I.k) (ζ : ℝ) :
    𝓕 (⇑ψ) ((2 : ℝ) ^ ℓ * ζ) * 𝓕 (modPacket ch ξ P) ζ = 𝓕 (modPacket ch ξ P) ζ := by
  by_cases h0 : 𝓕 (modPacket ch ξ P) ζ = 0
  · rw [h0, mul_zero]
  have hmem := mem_dilate_of_fourier_modPacket_ne hC ch ξ ζ P h0
  have hlt := abs_lt_of_overlapping hC hρ hξ hmem
  have hone : 𝓕 (⇑ψ) ((2 : ℝ) ^ ℓ * ζ) = 1 := by
    have := hψ.fourier_eq_one ((2 : ℝ) ^ ℓ * ζ) ?_
    · simpa [SchwartzMap.fourier_coe] using this
    · rw [abs_mul, abs_of_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) ℓ)]
      have hL := Multitile.length_ωu_eq P
      have h2 : (2 : ℝ) ^ ℓ * (2 : ℝ) ^ (-1 - P.I.k) ≤ 1 / 2 := by
        rw [← zpow_add₀ (by norm_num)]
        calc (2 : ℝ) ^ (ℓ + (-1 - P.I.k)) ≤ (2 : ℝ) ^ (-1 : ℤ) :=
              zpow_le_zpow_right₀ (by norm_num) (by omega)
          _ = 1 / 2 := by norm_num
      have hpos : (0 : ℝ) < (2 : ℝ) ^ ℓ := zpow_pos (by norm_num) _
      have hC13 : 0 ≤ C₁ + C₃ := by linarith [hC.one_le, hC.lt₁, hC.lt₂]
      calc (2 : ℝ) ^ ℓ * |ζ| ≤ (2 : ℝ) ^ ℓ * ((C₁ + C₃) * P.ωu.length / 2) :=
            mul_le_mul_of_nonneg_left hlt.le hpos.le
        _ = (C₁ + C₃) / 2 * ((2 : ℝ) ^ ℓ * (2 : ℝ) ^ (-1 - P.I.k)) := by rw [hL]; ring
        _ ≤ (C₁ + C₃) / 2 * (1 / 2) := mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = C₁ / 4 + C₃ / 4 := by ring
  rw [hone, one_mul]

/-- `ψ̂(2^ℓ ζ) · 𝓕(φ_P e_T^{-1})(ζ) = 0` when `2^ℓ ≥ (2C₁/(C₂ - C₃))|I|`. -/
theorem fourier_psi_mul_eq_zero (hC : AdmissibleConstants C₁ C₂ C₃) (hρ : ρ.IsStd)
    (hψ : IsPsiCutoff (C₁ / 4) (C₃ / 4) ψ) (ch : ProfileChoice) {P : Multitile ρ} {ξ : ℝ}
    (hξ : ξ ∈ P.ωlDil C₂) {ℓ : ℤ} (hℓ : 2 * C₁ / (C₂ - C₃) ≤ (2 : ℝ) ^ (ℓ - P.I.k)) (ζ : ℝ) :
    𝓕 (⇑ψ) ((2 : ℝ) ^ ℓ * ζ) * 𝓕 (modPacket ch ξ P) ζ = 0 := by
  by_cases h0 : 𝓕 (modPacket ch ξ P) ζ = 0
  · rw [h0, mul_zero]
  have hmem := mem_dilate_of_fourier_modPacket_ne hC ch ξ ζ P h0
  have hlt := lt_of_overlapping hC hρ hξ hmem
  have hzero : 𝓕 (⇑ψ) ((2 : ℝ) ^ ℓ * ζ) = 0 := by
    have hC23 : 0 < C₂ - C₃ := by linarith [hC.lt₁]
    have := hψ.fourier_eq_zero ((2 : ℝ) ^ ℓ * ζ) ?_
    · simpa [SchwartzMap.fourier_coe] using this
    · have hpos : (0 : ℝ) < (2 : ℝ) ^ ℓ := zpow_pos (by norm_num) _
      have hζpos : 0 < ζ :=
        lt_of_le_of_lt (div_nonneg (mul_nonneg hC23.le P.ωu.length_pos.le) (by norm_num)) hlt
      rw [abs_mul, abs_of_pos hpos, abs_of_pos hζpos]
      have hL := Multitile.length_ωu_eq P
      have e1 : (2 : ℝ) ^ ℓ * (2 : ℝ) ^ (-1 - P.I.k) = (2 : ℝ) ^ (ℓ - P.I.k) / 2 := by
        rw [← zpow_add₀ (by norm_num)]
        rw [show ℓ + (-1 - P.I.k) = (ℓ - P.I.k) - 1 by ring, zpow_sub₀ (by norm_num)]
        norm_num
      have h3 : 2 * C₁ ≤ (C₂ - C₃) * (2 : ℝ) ^ (ℓ - P.I.k) := by
        have := (div_le_iff₀ hC23).1 hℓ
        linarith [mul_comm (C₂ - C₃) ((2 : ℝ) ^ (ℓ - P.I.k))]
      calc 2 * (C₁ / 4) = (2 * C₁) / 4 := by ring
        _ ≤ ((C₂ - C₃) * (2 : ℝ) ^ (ℓ - P.I.k)) / 4 := by linarith
        _ = (2 : ℝ) ^ ℓ * ((C₂ - C₃) * P.ωu.length / 2) := by
            rw [hL]
            calc (C₂ - C₃) * (2 : ℝ) ^ (ℓ - P.I.k) / 4
                = (C₂ - C₃) / 2 * ((2 : ℝ) ^ (ℓ - P.I.k) / 2) := by ring
              _ = (C₂ - C₃) / 2 * ((2 : ℝ) ^ ℓ * (2 : ℝ) ^ (-1 - P.I.k)) := by rw [e1]
              _ = _ := by ring
        _ ≤ (2 : ℝ) ^ ℓ * ζ := mul_le_mul_of_nonneg_left hlt.le hpos.le
  rw [hzero, zero_mul]

end Localization


/-! ### The tree function `g = ∑ ⟨f, φ_P⟩ φ_P e_T^{-1}` and its Fourier localization -/

/-- `g(x) = ∑_{P ∈ T} ⟨f, φ_P⟩ φ_P(x) e(-x ξ_T) = e_T^{-1}(x) ∑_P ⟨f, φ_P⟩ φ_P(x)`. -/
def modTreeFn {ρ : Idx} (ch : ProfileChoice) (f : ℝ → ℂ) (ξ : ℝ)
    (T : Finset (Multitile ρ)) (x : ℝ) : ℂ :=
  ∑ P ∈ T, P.coeff ch f * modPacket ch ξ P x

/-- The demodulated tree function `g = e_T^{-1} ∑_P ⟨f, φ_P⟩ φ_P` is `FNice`. -/
theorem fnice_modTreeFn {ρ : Idx} (ch : ProfileChoice) (f : ℝ → ℂ) (ξ : ℝ)
    (T : Finset (Multitile ρ)) : FNice (modTreeFn ch f ξ T) :=
  FNice.finset_sum T _ fun P _ => (fnice_modPacket ch ξ P).const_mul (P.coeff ch f)

/-- `ĝ = ∑_P ⟨f, φ_P⟩ 𝓕(φ_P e_T^{-1})`. -/
theorem fourier_modTreeFn {ρ : Idx} (ch : ProfileChoice) (f : ℝ → ℂ) (ξ : ℝ)
    (T : Finset (Multitile ρ)) (ζ : ℝ) :
    𝓕 (modTreeFn ch f ξ T) ζ = ∑ P ∈ T, P.coeff ch f * 𝓕 (modPacket ch ξ P) ζ := by
  unfold modTreeFn
  rw [fourier_finset_sum T (fun P x => P.coeff ch f * modPacket ch ξ P x)
    (fun P _ => (fnice_modPacket ch ξ P).integrable.const_mul _) ζ]
  exact Finset.sum_congr rfl fun P _ => fourier_smul' _ _

section Reproduce

variable {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ C₃ : ℝ} {ψ : 𝓢(ℝ, ℂ)}

open Classical in
/-- **Frequency localization** ([O+] L2311-L2316): for
`ℓ` such that every tile of `T` has `|I| ≥ 2^ℓ` or a scale at least `2C₁/(C₂-C₃)` below `2^ℓ`,
`ψ_ℓ * g = ∑_{P ∈ T, |I| ≥ 2^ℓ} ⟨f, φ_P⟩ φ_P e_T^{-1}`. -/
theorem schwartzAvg_modTreeFn (hC : AdmissibleConstants C₁ C₂ C₃) (hρ : ρ.IsStd)
    (hψ : IsPsiCutoff (C₁ / 4) (C₃ / 4) ψ) (ch : ProfileChoice) (f : ℝ → ℂ) (ξ : ℝ)
    (T : Finset (Multitile ρ)) (hov : ∀ P ∈ T, ξ ∈ P.ωlDil C₂) {ℓ : ℤ}
    (hℓ : ∀ P ∈ T, ℓ ≤ P.I.k ∨ 2 * C₁ / (C₂ - C₃) ≤ (2 : ℝ) ^ (ℓ - P.I.k)) :
    schwartzAvg ψ ℓ (modTreeFn ch f ξ T) = modTreeFn ch f ξ (T.filter fun P => ℓ ≤ P.I.k) := by
  have hg := fnice_modTreeFn ch f ξ T
  obtain ⟨h1, h2⟩ := fnice_schwartzAvg ψ ℓ hg
  refine FNice.eq_of_fourier_eq h1 (fnice_modTreeFn ch f ξ _) fun ζ => ?_
  rw [h2, fourier_modTreeFn, fourier_modTreeFn, Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun P hP => ?_
  by_cases hle : ℓ ≤ P.I.k
  · simp only [hle, ↓reduceIte]
    rw [mul_left_comm, fourier_psi_mul_eq_self hC hρ hψ ch (hov P hP) hle ζ]
  · simp only [hle, ↓reduceIte]
    rw [mul_left_comm]
    have : 2 * C₁ / (C₂ - C₃) ≤ (2 : ℝ) ^ (ℓ - P.I.k) := (hℓ P hP).resolve_left hle
    rw [fourier_psi_mul_eq_zero hC hρ hψ ch (hov P hP) this ζ, mul_zero]

end Reproduce

/-- **Local constancy** ([O+] L2353-L2359):
for `c + 1 ≤ k₁ ≤ k₂`, the difference `ψ_{k₁} * g - ψ_{k₂} * g` is reproduced by `ψ_c`. -/
theorem schwartzAvg_reproduce {C₁ C₃ : ℝ} (hC₃ : 0 ≤ C₃) {ψ : 𝓢(ℝ, ℂ)}
    (hψ : IsPsiCutoff (C₁ / 4) (C₃ / 4) ψ) {g : ℝ → ℂ} (hg : FNice g) {c k₁ k₂ : ℤ}
    (hck : c + 1 ≤ k₁) (hk : k₁ ≤ k₂) :
    (fun x => schwartzAvg ψ k₁ g x - schwartzAvg ψ k₂ g x) =
      schwartzAvg ψ c (fun x => schwartzAvg ψ k₁ g x - schwartzAvg ψ k₂ g x) := by
  obtain ⟨hA₁, hf₁⟩ := fnice_schwartzAvg ψ k₁ hg
  obtain ⟨hA₂, hf₂⟩ := fnice_schwartzAvg ψ k₂ hg
  have hD := hA₁.sub hA₂
  obtain ⟨hDc, hfc⟩ := fnice_schwartzAvg ψ c hD
  refine FNice.eq_of_fourier_eq hD hDc fun ζ => ?_
  rw [hfc, fourier_sub' hA₁.integrable hA₂.integrable, hf₁, hf₂]
  by_cases h0 : 𝓕 (⇑ψ) ((2 : ℝ) ^ k₁ * ζ) * 𝓕 g ζ - 𝓕 (⇑ψ) ((2 : ℝ) ^ k₂ * ζ) * 𝓕 g ζ = 0
  · rw [h0, mul_zero]
  have hne : 𝓕 (⇑ψ) ((2 : ℝ) ^ k₁ * ζ) ≠ 0 ∨ 𝓕 (⇑ψ) ((2 : ℝ) ^ k₂ * ζ) ≠ 0 := by
    by_contra hcon
    rw [not_or, not_not, not_not] at hcon
    exact h0 (by rw [hcon.1, hcon.2]; ring)
  -- `|ζ| < (C₁/2) 2^{-k₁}`
  have hsmall : ∀ k : ℤ, k₁ ≤ k → 𝓕 (⇑ψ) ((2 : ℝ) ^ k * ζ) ≠ 0 →
      |(2 : ℝ) ^ c * ζ| ≤ C₁ / 4 + C₃ / 4 := by
    intro k hk1 hne'
    have hlt : |(2 : ℝ) ^ k * ζ| < 2 * (C₁ / 4) := by
      by_contra hcon
      rw [not_lt] at hcon
      apply hne'
      have := hψ.fourier_eq_zero _ hcon
      simpa [SchwartzMap.fourier_coe] using this
    have hpk : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos (by norm_num) _
    have hpc : (0 : ℝ) < (2 : ℝ) ^ c := zpow_pos (by norm_num) _
    rw [abs_mul, abs_of_pos hpk] at hlt
    rw [abs_mul, abs_of_pos hpc]
    have hcmp : (2 : ℝ) ^ c * 2 ≤ (2 : ℝ) ^ k := by
      calc (2 : ℝ) ^ c * 2 = (2 : ℝ) ^ (c + 1) := by rw [zpow_add_one₀ (by norm_num)]
        _ ≤ (2 : ℝ) ^ k := zpow_le_zpow_right₀ (by norm_num) (by omega)
    have : (2 : ℝ) ^ c * 2 * |ζ| ≤ (2 : ℝ) ^ k * |ζ| :=
      mul_le_mul_of_nonneg_right hcmp (abs_nonneg _)
    nlinarith [abs_nonneg ζ]
  have hone : 𝓕 (⇑ψ) ((2 : ℝ) ^ c * ζ) = 1 := by
    have hb : |(2 : ℝ) ^ c * ζ| ≤ C₁ / 4 + C₃ / 4 := by
      rcases hne with h | h
      · exact hsmall k₁ le_rfl h
      · exact hsmall k₂ hk h
    have := hψ.fourier_eq_one _ hb
    simpa [SchwartzMap.fourier_coe] using this
  rw [hone, one_mul]

end PrimeCarleson.Proof.Oplus
