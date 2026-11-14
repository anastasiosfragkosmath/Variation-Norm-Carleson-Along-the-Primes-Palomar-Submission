module

public import PrimeCarleson.Proof.Oplus.Defs.Multitile
public import Carleson.ToMathlib.RealInterpolation.Misc
public import Carleson.ToMathlib.MeasureTheory.Function.LorentzSeminorm.Basic
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# The model operator `𝒮^ρ` of a finite family is a finite sum of bounded functionals
([O+] L1085-L1090)

Source: [O+], L1085–L1090: for a finite set `S` of
`ρ`-multitiles, a profile choice `ch` and linearizing data `L`, the model operator
`𝒮^ρ[f](x) = ∑_{P ∈ S} ⟨f, φ_P⟩ φ_P(x) a_P(x)` (`modelOp`) is

* (i) defined on the class `𝒞 = {f : ∫ |f(x)| (1 + |x|)^{-2} dx < ∞}` (`ModelClass`), which is
  closed under both truncations `f 1_{|f| ≤ s}`, `f 1_{|f| > s}` (`ModelClass.trunc`,
  `.truncCompl`, for the vendored `MeasureTheory.trunc`, `truncCompl`, as the hypotheses `hPt`,
  `hPc` of `Common/MarcinkiewiczRestricted.eLpNorm_le_interpolation_of_restricted` read), and
  contains `L^q` for `1 ≤ q ≤ ∞` (`ModelClass.of_memLp`);
* (ii) for `f ∈ 𝒞` every `⟨f, φ_P⟩` is an absolutely convergent integral
  (`integrable_mul_conj_wavePacket`), `f ↦ 𝒮^ρ[f]` is additive (`modelOp_add`) on `𝒞`, and
  `𝒮^ρ[f]` is measurable for every `f` (`measurable_modelOp`);
* (iii) `𝒮^ρ[f] = ∑_{P ∈ S} (∫ f k_P) ψ_P` with `k_P = conj φ_P ∈ L^q` for every
  `1 ≤ q ≤ ∞` (`memLp_conj_wavePacket`) and `ψ_P = φ_P a_P` measurable (`measurable_psi`)
  (`modelOp_eq_sum`): this is `Common/LorentzSuperposition.finSumOp volume S k ψ`, the form
  consumed by `wnorm_finSumOp_le`.

The exponent `2` of the weight is arbitrary (any exponent `> 1` works): a Schwartz packet
decays faster than every power.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped FourierTransform SchwartzMap ContDiff ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

/-- The weight `(1 + |x|)^{-2}` of the class `𝒞`. -/
def modelWeight (x : ℝ) : ℝ := ((1 + |x|) ^ 2)⁻¹

theorem modelWeight_pos (x : ℝ) : 0 < modelWeight x := by unfold modelWeight; positivity

theorem modelWeight_le_one (x : ℝ) : modelWeight x ≤ 1 := by
  have : (1 : ℝ) ≤ (1 + |x|) ^ 2 := by nlinarith [abs_nonneg x]
  exact inv_le_one_of_one_le₀ this

theorem measurable_modelWeight : Measurable modelWeight := by unfold modelWeight; fun_prop

theorem integrable_modelWeight : Integrable modelWeight := by
  have h := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by simp)
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [Real.norm_eq_abs, modelWeight]
  rw [Real.rpow_neg (by positivity), Real.rpow_two]

/-- The class `𝒞 = {f : ℝ → ℂ measurable : ∫ |f(x)| (1 + |x|)^{-2} dx < ∞}` of
the model operator of a finite family ([O+] L1085–L1090). -/
def ModelClass (f : ℝ → ℂ) : Prop :=
  AEStronglyMeasurable f volume ∧ Integrable (fun x => ‖f x‖ * modelWeight x) volume

namespace ModelClass

/-- Domination by a function of the class. -/
theorem of_norm_le {f g : ℝ → ℂ} (hf : ModelClass f) (hg : AEStronglyMeasurable g volume)
    (h : ∀ x, ‖g x‖ ≤ ‖f x‖) : ModelClass g :=
  ⟨hg, hf.2.mono' (hg.norm.mul measurable_modelWeight.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => by
      rw [norm_mul, norm_norm, Real.norm_of_nonneg (modelWeight_pos x).le]
      exact mul_le_mul_of_nonneg_right (h x) (modelWeight_pos x).le)⟩

/-- Closure under the truncation `f 1_{|f| ≤ s}`. -/
theorem trunc {f : ℝ → ℂ} (hf : ModelClass f) (s : ℝ≥0∞) : ModelClass (MeasureTheory.trunc f s) :=
  hf.of_norm_le hf.1.trunc fun x => by
    unfold MeasureTheory.trunc
    split_ifs
    · exact le_rfl
    · simp

/-- Closure under the truncation `f 1_{|f| > s}`. -/
theorem truncCompl {f : ℝ → ℂ} (hf : ModelClass f) (s : ℝ≥0∞) :
    ModelClass (MeasureTheory.truncCompl f s) :=
  hf.of_norm_le hf.1.truncCompl fun x => by
    unfold MeasureTheory.truncCompl
    split_ifs
    · simp
    · exact le_rfl

/-- `L^q ⊆ 𝒞` for `1 ≤ q ≤ ∞`. -/
theorem of_memLp {f : ℝ → ℂ} {q : ℝ≥0∞} (hq : 1 ≤ q) (hf : MemLp f q volume) : ModelClass f := by
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  by_cases hqt : q = ⊤
  · subst hqt
    have hE : eLpNormEssSup f volume < ⊤ := by
      have := hf.eLpNorm_lt_top
      rwa [eLpNorm_exponent_top hf.aestronglyMeasurable] at this
    have hC : ∀ᵐ x, ‖f x‖ ≤ (eLpNormEssSup f volume).toReal := by
      filter_upwards [ae_le_eLpNormEssSup (f := f) (μ := volume)] with x hx
      exact (ENNReal.ofReal_le_iff_le_toReal hE.ne).1 (by rwa [ofReal_norm])
    refine (integrable_modelWeight.const_mul (eLpNormEssSup f volume).toReal).mono'
      ((hf.aestronglyMeasurable.norm.mul measurable_modelWeight.aestronglyMeasurable)) ?_
    filter_upwards [hC] with x hx
    rw [norm_mul, norm_norm, Real.norm_of_nonneg (modelWeight_pos x).le]
    exact mul_le_mul_of_nonneg_right hx (modelWeight_pos x).le
  · have hq0 : q ≠ 0 := by intro h; rw [h] at hq; simp at hq
    have hs : (1 : ℝ) ≤ q.toReal := by
      have := ENNReal.toReal_mono hqt hq
      simpa using this
    have h1 := hf.integrable_norm_rpow hq0 hqt
    refine (integrable_modelWeight.add h1).mono' ((hf.aestronglyMeasurable.norm.mul
      measurable_modelWeight.aestronglyMeasurable)) (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul, norm_norm, Real.norm_of_nonneg (modelWeight_pos x).le, Pi.add_apply]
    have hw := modelWeight_le_one x
    have hw0 := modelWeight_pos x
    by_cases hx : ‖f x‖ ≤ 1
    · nlinarith [norm_nonneg (f x), Real.rpow_nonneg (norm_nonneg (f x)) q.toReal]
    · push Not at hx
      have : ‖f x‖ ≤ ‖f x‖ ^ q.toReal := by
        simpa using Real.rpow_le_rpow_of_exponent_le hx.le hs
      nlinarith [norm_nonneg (f x), Real.rpow_nonneg (norm_nonneg (f x)) q.toReal]

end ModelClass

open scoped ComplexConjugate

section Model

variable {ρ : Idx} {r : ℝ}

/-- The decay of a Schwartz function against the weight of `𝒞`. -/
theorem exists_norm_schwartz_le_weight (g : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, ∀ y, ‖g y‖ ≤ C * modelWeight y := by
  refine ⟨2 * SchwartzMap.seminorm ℝ 0 0 g + 2 * SchwartzMap.seminorm ℝ 2 0 g, fun y => ?_⟩
  have h0 := SchwartzMap.norm_le_seminorm ℝ g y
  have h2 := SchwartzMap.norm_pow_mul_le_seminorm ℝ g 2 y
  rw [Real.norm_eq_abs] at h2
  have hpos : (0 : ℝ) < (1 + |y|) ^ 2 := by positivity
  unfold modelWeight
  rw [← div_eq_mul_inv, le_div_iff₀ hpos]
  have : (1 + |y|) ^ 2 ≤ 2 + 2 * |y| ^ 2 := by nlinarith [abs_nonneg y, sq_nonneg (1 - |y|)]
  calc ‖g y‖ * (1 + |y|) ^ 2 ≤ ‖g y‖ * (2 + 2 * |y| ^ 2) :=
        mul_le_mul_of_nonneg_left this (norm_nonneg _)
    _ = 2 * ‖g y‖ + 2 * (|y| ^ 2 * ‖g y‖) := by ring
    _ ≤ _ := by nlinarith [norm_nonneg (g y)]

/-- For `f ∈ 𝒞` the coefficient `⟨f, φ_P⟩` is an absolutely convergent integral. -/
theorem integrable_mul_conj_wavePacket (P : Multitile ρ) (ch : ProfileChoice) {f : ℝ → ℂ}
    (hf : ModelClass f) : Integrable (fun y => f y * conj (P.wavePacket ch y)) := by
  set g := ch.isProfile.wavePacketSchwartz P.I P.ωu with hg
  have hgf : (⇑g : ℝ → ℂ) = P.wavePacket ch :=
    funext fun y => ch.isProfile.wavePacketSchwartz_apply P.I P.ωu y
  obtain ⟨C, hC⟩ := exists_norm_schwartz_le_weight g
  rw [← hgf]
  refine (hf.2.mul_const C).mono'
    (hf.1.mul (continuous_star.comp g.continuous).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun y => ?_)
  rw [norm_mul, Complex.norm_conj]
  calc ‖f y‖ * ‖g y‖ ≤ ‖f y‖ * (C * modelWeight y) :=
        mul_le_mul_of_nonneg_left (hC y) (norm_nonneg _)
    _ = ‖f y‖ * modelWeight y * C := by ring

/-- **The model operator** `𝒮^ρ[f](x) = ∑_{P ∈ 𝒫_ρ} ⟨f, φ_P⟩ φ_P(x) a_P(x)` of a finite set `S` of
`ρ`-multitiles ([O+] L1085-L1090), for the profile choice `ch` (`ν_i` or `ν_i(-·)`). -/
def modelOp (ch : ProfileChoice) (L : Linearization r) (S : Finset (Multitile ρ)) (f : ℝ → ℂ)
    (x : ℝ) : ℂ :=
  ∑ P ∈ S, P.coeff ch f * P.wavePacket ch x * P.aP L x

theorem coeff_add (P : Multitile ρ) (ch : ProfileChoice) {f g : ℝ → ℂ} (hf : ModelClass f)
    (hg : ModelClass g) : P.coeff ch (f + g) = P.coeff ch f + P.coeff ch g := by
  unfold Multitile.coeff pairing
  simp_rw [Pi.add_apply, add_mul]
  exact integral_add (integrable_mul_conj_wavePacket P ch hf)
    (integrable_mul_conj_wavePacket P ch hg)

/-- **(ii) Linearity on `𝒞`**: `f ↦ 𝒮^ρ[f]` is additive on the class `𝒞`. -/
theorem modelOp_add (ch : ProfileChoice) (L : Linearization r) (S : Finset (Multitile ρ))
    {f g : ℝ → ℂ} (hf : ModelClass f) (hg : ModelClass g) (x : ℝ) :
    modelOp ch L S (f + g) x = modelOp ch L S f x + modelOp ch L S g x := by
  unfold modelOp
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [coeff_add P ch hf hg]
  ring

/-- The wave packet of a multitile is continuous, hence measurable. -/
theorem continuous_wavePacket (P : Multitile ρ) (ch : ProfileChoice) :
    Continuous (P.wavePacket ch) := ch.isProfile.continuous_wavePacketOf P.I P.ωu

/-- **(ii) Measurability**: `𝒮^ρ[f]` is measurable, for every `f`. -/
theorem measurable_modelOp (ch : ProfileChoice) (L : Linearization r) (S : Finset (Multitile ρ))
    (f : ℝ → ℂ) : Measurable (modelOp ch L S f) := by
  unfold modelOp
  refine Finset.measurable_sum _ fun P _ => ?_
  exact ((measurable_const.mul (continuous_wavePacket P ch).measurable).mul (P.measurable_aP L))

/-- **(iii) The finite-sum form**: `𝒮^ρ[f] = ∑_P (∫ f k_P) ψ_P` with `k_P = conj φ_P` and
`ψ_P = φ_P a_P`. -/
theorem modelOp_eq_sum (ch : ProfileChoice) (L : Linearization r) (S : Finset (Multitile ρ))
    (f : ℝ → ℂ) (x : ℝ) :
    modelOp ch L S f x = ∑ P ∈ S, (∫ y, f y * conj (P.wavePacket ch y)) *
      (P.wavePacket ch x * P.aP L x) := by
  unfold modelOp
  refine Finset.sum_congr rfl fun P _ => ?_
  unfold Multitile.coeff pairing
  ring

/-- **(iii) The kernels `k_P = conj φ_P` lie in every `L^q`, `1 ≤ q ≤ ∞`.** -/
theorem memLp_conj_wavePacket (P : Multitile ρ) (ch : ProfileChoice) (q : ℝ≥0∞) :
    MemLp (fun y => conj (P.wavePacket ch y)) q volume := by
  set g := ch.isProfile.wavePacketSchwartz P.I P.ωu with hg
  have hgf : (⇑g : ℝ → ℂ) = P.wavePacket ch :=
    funext fun y => ch.isProfile.wavePacketSchwartz_apply P.I P.ωu y
  rw [← hgf]
  exact (g.memLp q volume).star

/-- **(iii) The functions `ψ_P = φ_P a_P` are measurable.** -/
theorem measurable_psi (P : Multitile ρ) (ch : ProfileChoice) (L : Linearization r) :
    Measurable (fun x => P.wavePacket ch x * P.aP L x) :=
  (continuous_wavePacket P ch).measurable.mul (P.measurable_aP L)

end Model

end PrimeCarleson.Proof.Oplus
