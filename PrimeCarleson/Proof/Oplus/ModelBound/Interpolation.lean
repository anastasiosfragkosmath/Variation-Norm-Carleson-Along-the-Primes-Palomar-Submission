module

public import PrimeCarleson.Proof.Oplus.ModelBound.Weak
public import PrimeCarleson.Proof.Common.MarcinkiewiczRestricted

/-!
# The strong `L^p` bound for the model operators

Source: [O+] `csrhobound`, L1092–L1096 and L879-L880 (in the amended form used here): for `r > 2`,
`r' < p < 2r/(r-2)` and every index `ρ` with `m, n ∈ {1, …, 4}`, every profile choice, every finite
family of `ρ`-multitiles and every linearizing data with `Ξ` free of dyadic end points,

`‖𝒮^ρ[f]‖_{L^p} ≤ C ‖f‖_{L^p}` for every `f ∈ L^p`, with `C = C(p, r)` independent of all of them.

The interpolation is applied to the finite linear operator `f ↦ 𝒮^ρ[f]` on the truncation-closed
class `𝒞` of the model operator of a finite family (`ModelClass`, Decomposition/ModelOperator.lean;
closed under `trunc`, `truncCompl`, contains `L^q`, `q ≥ 1`) by
`Common.eLpNorm_le_interpolation_of_restricted`, between `p₀ = r'` and
`p₁ = (p + 2r/(r-2))/2` (both in `[r', 2r/(r-2))`, so that `csrhobound` applies), with `θ`
determined by `1/p = (1-θ)/p₀ + θ/p₁`. The hypotheses are: `modelOp_add` (subadditivity, from
linearity on `𝒞`), `measurable_modelOp` and `csrhobound` for `p₀` and `p₁`. A function in `L^p`,
`p ≥ 1`, lies in `𝒞` (`ModelClass.of_memLp`), so no separate assumption on `f` is needed.

For the ten indices of `R` this is the form consumed by [O+] `linearizedtheorem` (by Minkowski over
`ρ ∈ R` and `Multitile.ofTiles`, `waveOp_eq_sum_modelOp`).
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

open PrimeCarleson.Proof.Common

/-- **Strong type from two restricted weak type bounds for the model operator**: interpolation
between `p₀ < p₁` for the linear operator `modelOp ch L 𝔓` on `𝒞`. -/
theorem eLpNorm_modelOp_le_of_weak {ρ : Idx} {r : ℝ} (ch : ProfileChoice) (L : Linearization r)
    (𝔓 : Finset (Multitile ρ)) {p₀ p₁ p θ : ℝ} (hp₀ : 0 < p₀) (hp₀₁ : p₀ < p₁) (hθ₀ : 0 < θ)
    (hθ₁ : θ < 1) (hp : 1 / p = (1 - θ) / p₀ + θ / p₁) {M₀ M₁ : ℝ≥0} (hM₀ : 0 < M₀)
    (hM₁ : 0 < M₁)
    (h₀ : ∀ f : ℝ → ℂ, ModelClass f → MemLorentz f (ENNReal.ofReal p₀) 1 volume →
      wnorm (modelOp ch L 𝔓 f) (ENNReal.ofReal p₀) volume ≤
        M₀ * eLorentzNorm f (ENNReal.ofReal p₀) 1 volume)
    (h₁ : ∀ f : ℝ → ℂ, ModelClass f → MemLorentz f (ENNReal.ofReal p₁) 1 volume →
      wnorm (modelOp ch L 𝔓 f) (ENNReal.ofReal p₁) volume ≤
        M₁ * eLorentzNorm f (ENNReal.ofReal p₁) 1 volume)
    {f : ℝ → ℂ} (hf : ModelClass f) (hfp : MemLp f (ENNReal.ofReal p) volume) :
    eLpNorm (modelOp ch L 𝔓 f) (ENNReal.ofReal p) volume ≤
      restrictedInterpConst p₀ p₁ p θ * (M₀ : ℝ≥0∞) ^ (1 - θ) * (M₁ : ℝ≥0∞) ^ θ *
        eLpNorm f (ENNReal.ofReal p) volume :=
  eLpNorm_le_interpolation_of_restricted ModelClass (fun f s hf => hf.trunc s)
    (fun f s hf => hf.truncCompl s) hp₀ hp₀₁ hθ₀ hθ₁ hp hM₀ hM₁ (fun g => modelOp ch L 𝔓 g)
    (fun g _ => (measurable_modelOp ch L 𝔓 g).aestronglyMeasurable)
    (fun g g' hg hg' => Filter.Eventually.of_forall fun x => by
      rw [modelOp_add ch L 𝔓 hg hg' x]
      exact enorm_add_le _ _)
    h₀ h₁ hf hfp

/-- The exponents `p₀ < p < p₁` and the parameter `θ ∈ (0, 1)` with `1/p = (1-θ)/p₀ + θ/p₁`. -/
theorem exists_interpolation_parameter {p₀ p p₁ : ℝ} (hp₀ : 0 < p₀) (h₀ : p₀ < p) (h₁ : p < p₁) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ 1 / p = (1 - θ) / p₀ + θ / p₁ := by
  have hp : 0 < p := hp₀.trans h₀
  have hp₁ : 0 < p₁ := hp.trans h₁
  have h1 : 1 / p < 1 / p₀ := one_div_lt_one_div_of_lt hp₀ h₀
  have h2 : 1 / p₁ < 1 / p := one_div_lt_one_div_of_lt hp h₁
  have hd : 0 < 1 / p₀ - 1 / p₁ := by linarith
  refine ⟨(1 / p₀ - 1 / p) / (1 / p₀ - 1 / p₁), div_pos (by linarith) hd, ?_, ?_⟩
  · rw [div_lt_one hd]; linarith
  · have key : ∀ a₀ a a₁ : ℝ, a₀ - a₁ ≠ 0 →
        (1 - (a₀ - a) / (a₀ - a₁)) * a₀ + (a₀ - a) / (a₀ - a₁) * a₁ = a := by
      intro a₀ a a₁ h
      field_simp
      ring
    have := key (1 / p₀) (1 / p) (1 / p₁) hd.ne'
    exact this.symm.trans (by rw [mul_one_div, mul_one_div])

/-- **`model_strong_type`**: the strong `L^p` bound for the model operators of every finite family,
for `r > 2`, `r' < p < 2r/(r-2)`: `‖𝒮^ρ[f]‖_{L^p} ≤ C ‖f‖_{L^p}` for every `f ∈ L^p`, every index
`ρ` with `m, n ∈ {1, …, 4}` (types `1, 2, 3`, in particular the ten indices of `R`), profile choice,
finite family of `ρ`-multitiles and linearizing data with `Ξ` free of dyadic end points.
`C = C(p, r)` (and the admissible constants `C₁, C₂ = 2, C₃`, which do not influence the operator).
-/
theorem model_strong_type {r p : ℝ} (hr : 2 < r) (hp1 : Real.conjExponent r < p)
    (hp2 : p < 2 * r / (r - 2)) {C₁ C₂ C₃ : ℝ} (hC : AdmissibleConstants C₁ C₂ C₃)
    (hC₂ : C₂ = 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ρ : Idx}, ρ.IsStd → ∀ (ch : ProfileChoice) (L : Linearization r),
      AvoidsDyadicEndpoints (L.Ξ : Set ℝ) → ∀ (𝔓 : Finset (Multitile ρ)) {f : ℝ → ℂ},
      MemLp f (ENNReal.ofReal p) volume →
      eLpNorm (modelOp ch L 𝔓 f) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) volume := by
  have hr1 : 1 < r := by linarith
  have hq1 : 1 < Real.conjExponent r := one_lt_conjExponent hr1
  have hp0 : 0 < p := by linarith
  set p₀ := Real.conjExponent r with hp₀def
  set p₁ := (p + 2 * r / (r - 2)) / 2 with hp₁def
  have hp₀p : p₀ < p := hp1
  have hpp₁ : p < p₁ := by rw [hp₁def]; linarith
  have hp₁2 : p₁ < 2 * r / (r - 2) := by rw [hp₁def]; linarith
  obtain ⟨M₀, hM₀, hw₀⟩ := csrhobound hr (le_refl p₀) (hp₀p.trans hp2) hC hC₂
  obtain ⟨M₁, hM₁, hw₁⟩ := csrhobound hr (hp₀p.le.trans hpp₁.le) hp₁2 hC hC₂
  obtain ⟨θ, hθ₀, hθ₁, hθ⟩ := exists_interpolation_parameter (by linarith : 0 < p₀) hp₀p hpp₁
  set K : ℝ≥0∞ := restrictedInterpConst p₀ p₁ p θ * (M₀ : ℝ≥0∞) ^ (1 - θ) * (M₁ : ℝ≥0∞) ^ θ
    with hK
  have hKt : K ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (restrictedInterpConst_ne_top (by linarith)
      (hp₀p.trans hpp₁) hθ₀ hθ₁ hθ) ?_) ?_
    · exact ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.coe_ne_top
    · exact ENNReal.rpow_ne_top_of_nonneg hθ₀.le ENNReal.coe_ne_top
  refine ⟨K.toReal + 1, by positivity, ?_⟩
  intro ρ hρ ch L hΞ 𝔓 f hfp
  have hf : ModelClass f := ModelClass.of_memLp (q := ENNReal.ofReal p)
    (ENNReal.one_le_ofReal.2 (by linarith)) hfp
  refine (eLpNorm_modelOp_le_of_weak ch L 𝔓 (by linarith) (hp₀p.trans hpp₁) hθ₀ hθ₁ hθ hM₀ hM₁
    (fun g _ hg => hw₀ hρ ch L hΞ 𝔓 hg) (fun g _ hg => hw₁ hρ ch L hΞ 𝔓 hg) hf hfp).trans ?_
  gcongr
  exact (ENNReal.ofReal_toReal hKt).symm.le.trans (ENNReal.ofReal_le_ofReal (by linarith))

end PrimeCarleson.Proof.Oplus
