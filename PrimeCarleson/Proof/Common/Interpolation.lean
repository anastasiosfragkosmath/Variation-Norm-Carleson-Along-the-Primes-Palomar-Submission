module

public import Carleson.ToMathlib.RealInterpolation.Main

/-!
# Marcinkiewicz interpolation for subadditive operators on discrete spaces

Difference from the printed route: the paper interpolates scalar subadditive operators (variational
and maximal blocks, residual pieces) between an `ℓ²` and an `ℓ^s` bound and points to [Kold, §7] for
this (`sources/Variational_Carleson.tex` L1374-L1375, L1456-L1457, L1504-L1507, L1525-L1528, L1717,
L1731-L1732). We use instead the Marcinkiewicz real interpolation theorem of the vendored Lean
Carleson project (`exists_hasStrongType_real_interpolation` in
`Carleson.ToMathlib.RealInterpolation.Main`). This file proves the interpolation statement used at
those places.

* `eLpNorm_le_interpolation_of_truncClosed`: the (possibly off-diagonal) Marcinkiewicz bound
  for an operator that is only controlled on a class `P` of functions closed under the
  truncations `trunc f t`, `truncCompl f t` (e.g. finitely supported functions); the constant is
  `realInterpConst p₀ p₁ q₀ q₁ q t * M₀ ^ (1 - t) * M₁ ^ t`.
* With counting measure, the target a countable type with measurable singletons (e.g. `ℤ`), where
  every function is strongly measurable (`StronglyMeasurable.of_discrete`; this matters because
  `eLpNorm` is `∞` for a function that is not a.e. strongly measurable):
  `exists_eLpNorm_count_le_interpolation_of_finite` (operators controlled on finitely supported
  functions) and `exists_eLpNorm_count_le_interpolation_finsupp_of_wnorm`,
  `exists_eLpNorm_count_le_interpolation_finsupp`,
  `exists_eLpNorm_count_le_interpolation_finsupp_ofReal` (operators on `α →₀ E`, the form of the
  operators `multiplierOpDis`, `primeVariation`, `carlesonMax`).

In each discrete statement the constant `C` depends only on the exponents, and the bound is
`‖T f‖_{ℓ^p} ≤ C M₀^{1-θ} M₁^θ ‖f‖_{ℓ^p}` for `1/p = (1-θ)/p₀ + θ/p₁`, `0 < θ < 1`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Common

/-! ### The core statement on general measure spaces -/

section Core

variable {α α' E₁ E₂ : Type*} [MeasurableSpace α] [MeasurableSpace α'] {μ : Measure α}
  {ν : Measure α'} [TopologicalSpace E₁] [ESeminormedAddMonoid E₁] [TopologicalSpace E₂]
  [ESeminormedAddMonoid E₂]

/-- The exponent-dependent factor of the constant in the Marcinkiewicz interpolation theorem of
the vendored Carleson project (subadditivity constant `A = 1`, endpoint constants `1`). -/
def realInterpConst (p₀ p₁ q₀ q₁ q t : ℝ≥0∞) : ℝ≥0∞ :=
  C_realInterpolation_ENNReal p₀ p₁ q₀ q₁ q 1 1 1 t

/-- The constant of the vendored interpolation theorem factors as
`realInterpConst * M₀ ^ (1 - t) * M₁ ^ t`. -/
theorem C_realInterpolation_ENNReal_eq_realInterpConst_mul (p₀ p₁ q₀ q₁ q t : ℝ≥0∞)
    (M₀ M₁ : ℝ≥0) :
    C_realInterpolation_ENNReal p₀ p₁ q₀ q₁ q M₀ M₁ 1 t =
      realInterpConst p₀ p₁ q₀ q₁ q t * (M₀ : ℝ≥0∞) ^ (1 - t).toReal *
        (M₁ : ℝ≥0∞) ^ t.toReal := by
  simp only [realInterpConst, C_realInterpolation_ENNReal, ENNReal.coe_one, ENNReal.one_rpow,
    mul_one]

/-- The exponent factor `realInterpConst` is finite. -/
theorem realInterpConst_ne_top {p₀ p₁ q₀ q₁ q t : ℝ≥0∞} (hp₀ : p₀ ∈ Ioc 0 q₀)
    (hp₁ : p₁ ∈ Ioc 0 q₁) (hq₀q₁ : q₀ ≠ q₁) (ht : t ∈ Ioo 0 1)
    (hq : q⁻¹ = (1 - t) / q₀ + t / q₁) : realInterpConst p₀ p₁ q₀ q₁ q t ≠ ⊤ :=
  C_realInterpolation_ENNReal_ne_top (A := 1) hp₀ hp₁ hq₀q₁ ht one_pos one_pos hq

/-- The exponent factor `realInterpConst` is positive. -/
theorem realInterpConst_pos {p₀ p₁ q₀ q₁ q t : ℝ≥0∞} (hp₀ : p₀ ∈ Ioc 0 q₀)
    (hp₁ : p₁ ∈ Ioc 0 q₁) (hq₀q₁ : q₀ ≠ q₁) (ht : t ∈ Ioo 0 1)
    (hq : q⁻¹ = (1 - t) / q₀ + t / q₁) : 0 < realInterpConst p₀ p₁ q₀ q₁ q t :=
  C_realInterpolation_ENNReal_pos (A := 1) one_pos hp₀ hp₁ hq₀q₁ ht one_pos one_pos hq

/-- **Marcinkiewicz interpolation on a class of functions closed under truncation.** Let `P` be
a class of functions closed under `trunc f t` and `truncCompl f t`, and let `T` be subadditive
on `P` and of weak types `(p₀, q₀)` and `(p₁, q₁)` on `P` with constants `M₀, M₁ > 0`, where
`p₀ ≤ q₀`, `p₁ ≤ q₁`, `q₀ ≠ q₁`. Then for `f ∈ P ∩ L^p`,
`‖T f‖_{L^q} ≤ realInterpConst · M₀^{1-t} M₁^t ‖f‖_{L^p}` with
`1/p = (1-t)/p₀ + t/p₁`, `1/q = (1-t)/q₀ + t/q₁`, `0 < t < 1`. -/
theorem eLpNorm_le_interpolation_of_truncClosed (P : (α → E₁) → Prop)
    (hPt : ∀ f (s : ℝ≥0∞), P f → P (trunc f s))
    (hPc : ∀ f (s : ℝ≥0∞), P f → P (truncCompl f s))
    {p₀ p₁ q₀ q₁ p q t : ℝ≥0∞} (hp₀ : p₀ ∈ Ioc 0 q₀) (hp₁ : p₁ ∈ Ioc 0 q₁) (hq₀q₁ : q₀ ≠ q₁)
    (ht : t ∈ Ioo 0 1) (hp : p⁻¹ = (1 - t) / p₀ + t / p₁) (hq : q⁻¹ = (1 - t) / q₀ + t / q₁)
    {M₀ M₁ : ℝ≥0} (hM₀ : 0 < M₀) (hM₁ : 0 < M₁) (T : (α → E₁) → α' → E₂)
    (hmeas : ∀ f, P f → AEStronglyMeasurable (T f) ν)
    (hsub : ∀ f g, P f → P g → ∀ᵐ x ∂ν, ‖T (f + g) x‖ₑ ≤ ‖T f x‖ₑ + ‖T g x‖ₑ)
    (h₀ : ∀ f, P f → MemLp f p₀ μ → wnorm (T f) q₀ ν ≤ M₀ * eLpNorm f p₀ μ)
    (h₁ : ∀ f, P f → MemLp f p₁ μ → wnorm (T f) q₁ ν ≤ M₁ * eLpNorm f p₁ μ)
    {f : α → E₁} (hf : P f) (hfp : MemLp f p μ) :
    eLpNorm (T f) q ν ≤ realInterpConst p₀ p₁ q₀ q₁ q t * (M₀ : ℝ≥0∞) ^ (1 - t).toReal *
      (M₁ : ℝ≥0∞) ^ t.toReal * eLpNorm f p μ := by
  classical
  let T' : (α → E₁) → α' → E₂ := fun g => if P g then T g else 0
  have hT'f : T' f = T f := by simp [T', hf]
  have hweak : ∀ {p' q' : ℝ≥0∞} {M : ℝ≥0}, 0 < q' →
      (∀ g, P g → MemLp g p' μ → wnorm (T g) q' ν ≤ M * eLpNorm g p' μ) →
      HasWeakType T' p' q' μ ν M := by
    intro p' q' M hq' h g hg
    by_cases hPg : P g
    · simp only [T', hPg, ↓reduceIte]
      exact ⟨hmeas g hPg, h g hPg hg⟩
    · simp only [T', hPg, ↓reduceIte]
      refine ⟨aestronglyMeasurable_const, ?_⟩
      calc wnorm (0 : α' → E₂) q' ν ≤ eLpNorm (0 : α' → E₂) q' ν :=
            wnorm_le_eLpNorm aestronglyMeasurable_const hq'
        _ = 0 := eLpNorm_zero
        _ ≤ _ := zero_le
  have hsubT : SubadditiveTrunc T' ((1 : ℝ≥0) : ℝ≥0∞) f ν := by
    intro a _
    have h1 := hsub (trunc f a) (truncCompl f a) (hPt f a hf) (hPc f a hf)
    simp only [T', hPt f a hf, hPc f a hf, trunc_add_truncCompl, hf, ↓reduceIte,
      ENNReal.coe_one, one_mul]
    filter_upwards [h1] with x hx
    simpa [trunc_add_truncCompl] using hx
  have hmT : PreservesAEStrongMeasurability (μ := μ) (ν := ν) T' p := by
    intro g _
    by_cases hPg : P g
    · simp only [T', hPg, ↓reduceIte]; exact hmeas g hPg
    · simp only [T', hPg, ↓reduceIte]; exact aestronglyMeasurable_const
  have key := exists_hasStrongType_real_interpolation_aux₄ (T := T') (f := f) (A := 1) one_pos
    hp₀ hp₁ hq₀q₁ ht hM₀ hM₁ hp hq hsubT (hweak (hp₀.1.trans_le hp₀.2) h₀)
    (hweak (hp₁.1.trans_le hp₁.2) h₁) hmT hfp
  rw [hT'f] at key
  rw [← C_realInterpolation_ENNReal_eq_realInterpConst_mul]
  exact key

end Core

/-! ### Exponent bookkeeping for a real interpolation parameter -/

section Exponents

/-- For `0 < θ < 1`, the parameter `ENNReal.ofReal θ` lies in `(0, 1)`. -/
theorem ofReal_mem_Ioo_zero_one {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1) :
    ENNReal.ofReal θ ∈ Ioo (0 : ℝ≥0∞) 1 :=
  ⟨ENNReal.ofReal_pos.2 hθ₀, ENNReal.ofReal_lt_one.2 hθ₁⟩

/-- `1 - ENNReal.ofReal θ = ENNReal.ofReal (1 - θ)` for `0 ≤ θ`. -/
theorem one_sub_ofReal_eq {θ : ℝ} (hθ₀ : 0 ≤ θ) :
    1 - ENNReal.ofReal θ = ENNReal.ofReal (1 - θ) := by
  rw [ENNReal.ofReal_sub _ hθ₀, ENNReal.ofReal_one]

/-- `(1 - ENNReal.ofReal θ).toReal = 1 - θ` for `0 ≤ θ ≤ 1`. -/
theorem toReal_one_sub_ofReal {θ : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    (1 - ENNReal.ofReal θ).toReal = 1 - θ := by
  rw [one_sub_ofReal_eq hθ₀, ENNReal.toReal_ofReal (by linarith)]

end Exponents

/-! ### Countable discrete spaces with counting measure -/

section Discrete

variable {α β E ε : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass β]
  [Countable β]
  [TopologicalSpace E] [ESeminormedAddMonoid E] [TopologicalSpace ε] [ESeminormedAddMonoid ε]

/-- On a countable type with measurable singletons every function is a.e. strongly measurable. -/
theorem aestronglyMeasurable_of_discrete {γ G : Type*} [MeasurableSpace γ]
    [MeasurableSingletonClass γ] [Countable γ] [TopologicalSpace G] (g : γ → G)
    (m : Measure γ) : AEStronglyMeasurable g m :=
  StronglyMeasurable.of_discrete.aestronglyMeasurable

/-- A function that is not in `L^p` has infinite `L^p` norm. -/
theorem eLpNorm_eq_top_of_not_memLp {γ G : Type*} [MeasurableSpace γ] [TopologicalSpace G]
    [ContinuousENorm G] {g : γ → G} {p : ℝ≥0∞} {m : Measure γ} (hg : ¬ MemLp g p m) :
    eLpNorm g p m = ⊤ :=
  not_lt_top_iff.1 hg

/-- **Marcinkiewicz interpolation for operators controlled on finitely supported functions**.
Subadditivity and the two weak-type endpoint bounds are only assumed for finitely supported
functions, and the conclusion is for finitely supported `f` (truncations of a finitely supported
function are finitely supported). -/
theorem exists_eLpNorm_count_le_interpolation_of_finite {p₀ p₁ p : ℝ≥0∞} {θ : ℝ}
    (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (hp₀₁ : p₀ ≠ p₁) (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) / p₀ + ENNReal.ofReal θ / p₁) :
    ∃ C : ℝ≥0, ∀ (T : (α → E) → β → ε) (M₀ M₁ : ℝ≥0), 0 < M₀ → 0 < M₁ →
      (∀ f g : α → E, f.support.Finite → g.support.Finite →
        ∀ x, ‖T (f + g) x‖ₑ ≤ ‖T f x‖ₑ + ‖T g x‖ₑ) →
      (∀ f : α → E, f.support.Finite →
        wnorm (T f) p₀ Measure.count ≤ M₀ * eLpNorm f p₀ Measure.count) →
      (∀ f : α → E, f.support.Finite →
        wnorm (T f) p₁ Measure.count ≤ M₁ * eLpNorm f p₁ Measure.count) →
      ∀ f : α → E, f.support.Finite →
        eLpNorm (T f) p Measure.count ≤
          C * (M₀ : ℝ≥0∞) ^ (1 - θ) * (M₁ : ℝ≥0∞) ^ θ * eLpNorm f p Measure.count := by
  set t := ENNReal.ofReal θ with ht_def
  have ht := ofReal_mem_Ioo_zero_one hθ₀ hθ₁
  have hp' : p⁻¹ = (1 - t) / p₀ + t / p₁ := by rw [one_sub_ofReal_eq hθ₀.le]; exact hp
  have hP₀ : p₀ ∈ Ioc 0 p₀ := ⟨hp₀, le_rfl⟩
  have hP₁ : p₁ ∈ Ioc 0 p₁ := ⟨hp₁, le_rfl⟩
  have hK := realInterpConst_ne_top hP₀ hP₁ hp₀₁ ht hp'
  refine ⟨(realInterpConst p₀ p₁ p₀ p₁ p t).toNNReal, ?_⟩
  intro T M₀ M₁ hM₀ hM₁ hsub h₀ h₁ f hf
  rw [ENNReal.coe_toNNReal hK]
  by_cases hfp : MemLp f p Measure.count
  · have key := eLpNorm_le_interpolation_of_truncClosed (μ := Measure.count)
      (ν := Measure.count) (fun g : α → E => g.support.Finite)
      (fun g s hg => hg.subset fun x hx => by
        by_contra h0
        exact hx (by simp [trunc, Function.notMem_support.1 h0]))
      (fun g s hg => hg.subset fun x hx => by
        by_contra h0
        exact hx (by simp [truncCompl, Function.notMem_support.1 h0]))
      hP₀ hP₁ hp₀₁ ht hp' hp' hM₀ hM₁ T (fun g _ => aestronglyMeasurable_of_discrete _ _)
      (fun g g' hg hg' => Filter.Eventually.of_forall (hsub g g' hg hg'))
      (fun g hg _ => h₀ g hg) (fun g hg _ => h₁ g hg) hf hfp
    rwa [toReal_one_sub_ofReal hθ₀.le hθ₁.le, ENNReal.toReal_ofReal hθ₀.le] at key
  · rw [eLpNorm_eq_top_of_not_memLp hfp, ENNReal.mul_top]
    · exact le_top
    · refine mul_ne_zero (mul_ne_zero (realInterpConst_pos hP₀ hP₁ hp₀₁ ht hp').ne' ?_) ?_
      · exact (ENNReal.rpow_pos (by exact_mod_cast hM₀) ENNReal.coe_ne_top).ne'
      · exact (ENNReal.rpow_pos (by exact_mod_cast hM₁) ENNReal.coe_ne_top).ne'

/-- **Marcinkiewicz interpolation for operators on finitely supported sequences**, weak-type
form: for `T : (α →₀ E) → β → ε` subadditive and of weak types `(p₀, p₀)`, `(p₁, p₁)` with constants
`M₀, M₁ > 0`, `‖T f‖_{ℓ^p} ≤ C M₀^{1-θ} M₁^θ ‖f‖_{ℓ^p}` with `C` depending only on the
exponents. -/
theorem exists_eLpNorm_count_le_interpolation_finsupp_of_wnorm {p₀ p₁ p : ℝ≥0∞} {θ : ℝ}
    (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (hp₀₁ : p₀ ≠ p₁) (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) / p₀ + ENNReal.ofReal θ / p₁) :
    ∃ C : ℝ≥0, ∀ (T : (α →₀ E) → β → ε) (M₀ M₁ : ℝ≥0), 0 < M₀ → 0 < M₁ →
      (∀ f g : α →₀ E, ∀ x, ‖T (f + g) x‖ₑ ≤ ‖T f x‖ₑ + ‖T g x‖ₑ) →
      (∀ f : α →₀ E, wnorm (T f) p₀ Measure.count ≤ M₀ * eLpNorm (⇑f) p₀ Measure.count) →
      (∀ f : α →₀ E, wnorm (T f) p₁ Measure.count ≤ M₁ * eLpNorm (⇑f) p₁ Measure.count) →
      ∀ f : α →₀ E, eLpNorm (T f) p Measure.count ≤
        C * (M₀ : ℝ≥0∞) ^ (1 - θ) * (M₁ : ℝ≥0∞) ^ θ * eLpNorm (⇑f) p Measure.count := by
  classical
  obtain ⟨C, hC⟩ := exists_eLpNorm_count_le_interpolation_of_finite (α := α) (β := β) (E := E)
    (ε := ε) hp₀ hp₁ hp₀₁ hθ₀ hθ₁ hp
  refine ⟨C, fun T M₀ M₁ hM₀ hM₁ hsub h₀ h₁ f => ?_⟩
  let T₁ : (α → E) → β → ε := fun g =>
    if h : g.support.Finite then T (Finsupp.ofSupportFinite g h) else 0
  have hT₁ : ∀ (g : α → E) (h : g.support.Finite), T₁ g = T (Finsupp.ofSupportFinite g h) :=
    fun g h => by simp [T₁, h]
  have hf : (Function.support (⇑f)).Finite := f.fun_support_eq ▸ f.support.finite_toSet
  have key := hC T₁ M₀ M₁ hM₀ hM₁
    (fun g g' hg hg' x => by
      rw [hT₁ g hg, hT₁ g' hg', hT₁ (g + g') (hg.union hg' |>.subset (Function.support_add _ _))]
      have : Finsupp.ofSupportFinite (g + g') (hg.union hg' |>.subset (Function.support_add _ _))
          = Finsupp.ofSupportFinite g hg + Finsupp.ofSupportFinite g' hg' := by
        ext y; simp
      rw [this]
      exact hsub _ _ x)
    (fun g hg => by simpa [hT₁ g hg] using h₀ (Finsupp.ofSupportFinite g hg))
    (fun g hg => by simpa [hT₁ g hg] using h₁ (Finsupp.ofSupportFinite g hg))
    (⇑f) hf
  rwa [hT₁ (⇑f) hf, show Finsupp.ofSupportFinite (⇑f) hf = f from Finsupp.ext fun _ => rfl]
    at key

/-- **Marcinkiewicz interpolation for operators on finitely supported sequences**, in the form of
the operators (`multiplierOpDis`, `primeVariation`, `carlesonMax` act on `ℤ →₀ ℂ`): for
`T : (α →₀ E) → β → ε` subadditive, with `‖T f‖_{ℓ^{p₀}} ≤ M₀ ‖f‖_{ℓ^{p₀}}` and
`‖T f‖_{ℓ^{p₁}} ≤ M₁ ‖f‖_{ℓ^{p₁}}`, one has `‖T f‖_{ℓ^p} ≤ C M₀^{1-θ} M₁^θ ‖f‖_{ℓ^p}` with `C`
depending only on the exponents. -/
theorem exists_eLpNorm_count_le_interpolation_finsupp {p₀ p₁ p : ℝ≥0∞} {θ : ℝ}
    (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (hp₀₁ : p₀ ≠ p₁) (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) / p₀ + ENNReal.ofReal θ / p₁) :
    ∃ C : ℝ≥0, ∀ (T : (α →₀ E) → β → ε) (M₀ M₁ : ℝ≥0), 0 < M₀ → 0 < M₁ →
      (∀ f g : α →₀ E, ∀ x, ‖T (f + g) x‖ₑ ≤ ‖T f x‖ₑ + ‖T g x‖ₑ) →
      (∀ f : α →₀ E, eLpNorm (T f) p₀ Measure.count ≤ M₀ * eLpNorm (⇑f) p₀ Measure.count) →
      (∀ f : α →₀ E, eLpNorm (T f) p₁ Measure.count ≤ M₁ * eLpNorm (⇑f) p₁ Measure.count) →
      ∀ f : α →₀ E, eLpNorm (T f) p Measure.count ≤
        C * (M₀ : ℝ≥0∞) ^ (1 - θ) * (M₁ : ℝ≥0∞) ^ θ * eLpNorm (⇑f) p Measure.count := by
  obtain ⟨C, hC⟩ := exists_eLpNorm_count_le_interpolation_finsupp_of_wnorm (α := α) (β := β)
    (E := E) (ε := ε) hp₀ hp₁ hp₀₁ hθ₀ hθ₁ hp
  exact ⟨C, fun T M₀ M₁ hM₀ hM₁ hsub h₀ h₁ => hC T M₀ M₁ hM₀ hM₁ hsub
    (fun f => (wnorm_le_eLpNorm (aestronglyMeasurable_of_discrete _ _) hp₀).trans (h₀ f))
    (fun f => (wnorm_le_eLpNorm (aestronglyMeasurable_of_discrete _ _) hp₁).trans (h₁ f))⟩

/-- `exists_eLpNorm_count_le_interpolation_finsupp` with real exponents `0 < p₀ ≠ p₁`,
`1/p = (1-θ)/p₀ + θ/p₁` (the norms are `eLpNorm · (ENNReal.ofReal p) Measure.count`, as in the
statements). -/
theorem exists_eLpNorm_count_le_interpolation_finsupp_ofReal {p₀ p₁ p θ : ℝ} (hp₀ : 0 < p₀)
    (hp₁ : 0 < p₁) (hp₀₁ : p₀ ≠ p₁) (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (hp : 1 / p = (1 - θ) / p₀ + θ / p₁) :
    ∃ C : ℝ≥0, ∀ (T : (α →₀ E) → β → ε) (M₀ M₁ : ℝ≥0), 0 < M₀ → 0 < M₁ →
      (∀ f g : α →₀ E, ∀ x, ‖T (f + g) x‖ₑ ≤ ‖T f x‖ₑ + ‖T g x‖ₑ) →
      (∀ f : α →₀ E, eLpNorm (T f) (ENNReal.ofReal p₀) Measure.count ≤
        M₀ * eLpNorm (⇑f) (ENNReal.ofReal p₀) Measure.count) →
      (∀ f : α →₀ E, eLpNorm (T f) (ENNReal.ofReal p₁) Measure.count ≤
        M₁ * eLpNorm (⇑f) (ENNReal.ofReal p₁) Measure.count) →
      ∀ f : α →₀ E, eLpNorm (T f) (ENNReal.ofReal p) Measure.count ≤
        C * (M₀ : ℝ≥0∞) ^ (1 - θ) * (M₁ : ℝ≥0∞) ^ θ *
          eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
  have h1 : 0 ≤ (1 - θ) / p₀ := div_nonneg (by linarith) hp₀.le
  have h2 : 0 ≤ θ / p₁ := div_nonneg hθ₀.le hp₁.le
  have hpos : 0 < 1 / p := by
    rw [hp]; exact add_pos_of_nonneg_of_pos h1 (div_pos hθ₀ hp₁)
  have hp_pos : 0 < p := one_div_pos.1 hpos
  refine exists_eLpNorm_count_le_interpolation_finsupp (ENNReal.ofReal_pos.2 hp₀)
    (ENNReal.ofReal_pos.2 hp₁)
    (fun h => hp₀₁ ((ENNReal.ofReal_eq_ofReal_iff hp₀.le hp₁.le).1 h)) hθ₀ hθ₁ ?_
  rw [← ENNReal.ofReal_inv_of_pos hp_pos, ← one_div, hp, ENNReal.ofReal_add h1 h2,
    ENNReal.ofReal_div_of_pos hp₀, ENNReal.ofReal_div_of_pos hp₁]

end Discrete

end PrimeCarleson.Proof.Common
