module

public import PrimeCarleson.Frozen.MswTransferenceVariation
public import PrimeCarleson.Proof.Common.FourierR
public import PrimeCarleson.Proof.Paper.P7.VarcarBV
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# The discrete half-line variation bound from the Euclidean estimate and MSW transference

Source: main paper `l:varcarZ`, L1813–L1816; main paper `p:disc`, L2983–L2987 (with its Euclidean
hypothesis, L2983–L2986), here for the half-line family.

For a chart `(c - 1/2, c + 1/2]` and a finitely supported `f : ℤ →₀ ℂ` the *chart density* is
`ĝ_{c,f,n}(β) = 1_{(c - 1/2, c + 1/2]}(β) f̂(β) e(nβ)`, and its partial integral
`Φ(λ) = ∫_{β ≤ λ} ĝ_{c,f,n}(β) dβ` is the discrete half-line projection `S_dis(λ) f(n)` onto the
frequencies `(c - 1/2, λ]` of the chart. Under `hO : OplusVariationBound` (the Euclidean variational
Carleson theorem) we prove (`halfLine_variation`):

`‖ n ↦ V^r(Φ_{c,f,n} : λ ∈ ℝ) ‖_{ℓ^p(ℤ)} ≤ C_{p,r} ‖f‖_{ℓ^p}`  for `r > 2`, `r' < p < ∞`.

The multiplier family of the transference is `m_λ = 1_{(-1/2, 1/2] ∩ (-∞, λ]}`: its Euclidean
variation is the one of the half-line projections `𝒮[F](κ λ, x) - 𝒮[F](-1/2, x)` with the monotone
clamp `κ`, hence at most `V^r(𝒮[F](·, x))` (`rVariationOn_comp_monotone_le`); this is the
Euclidean hypothesis of `msw_transference_variation`. The chart `c ≠ 0` is reduced to
`c = 0` by modulating `f` by `e(-c ·)`, and `T` finite to `T` arbitrary by
`eLpNorm_count_iSup_le`.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal SchwartzMap FourierTransform

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Common PrimeCarleson.Proof.MswTransference
  PrimeCarleson.Proof.Goal0

/-! ### Partial integrals -/

/-- `Φ_g(b) - Φ_g(a) = ∫_{(a, b]} g` for integrable `g`, `a ≤ b`. -/
theorem partialInt_sub_eq {g : ℝ → ℂ} (hg : Integrable g) {a b : ℝ} (hab : a ≤ b) :
    partialInt g b - partialInt g a = ∫ ξ in Set.Ioc a b, g ξ := by
  have := intervalIntegral.integral_Iic_sub_Iic hg.integrableOn hg.integrableOn (a := a) (b := b)
  unfold partialInt
  rw [this, intervalIntegral.integral_of_le hab]

/-- `Φ_g(λ)` as the integral of an indicator. -/
theorem partialInt_eq_integral_indicator (g : ℝ → ℂ) (lam : ℝ) :
    partialInt g lam = ∫ ξ, (Set.Iic lam).indicator g ξ :=
  (integral_indicator measurableSet_Iic).symm

/-- Constants cancel in the `r`-variation. -/
theorem rVariationOn_sub_const (r : ℝ) (S : Set ℝ) (a : ℝ → ℂ) (c : ℂ) :
    rVariationOn r S (fun t => a t - c) = rVariationOn r S a := by
  unfold rVariationOn
  refine iSup_congr fun J => iSup_congr fun t => iSup_congr fun _ => iSup_congr fun _ => ?_
  simp only [sub_sub_sub_cancel_right]

/-! ### The Euclidean side: `𝒮[F](ξ, x)` as a partial integral -/

/-- `ĝ(η) e(ηx)` for a Schwartz function `F`: the integrand of `𝒮[F](·, x)`. -/
def schwartzDensity (F : 𝓢(ℝ, ℂ)) (x : ℝ) (η : ℝ) : ℂ := (∫ y, F y * e (-(y * η))) * e (η * x)

/-- `F̂` is integrable for a Schwartz function `F`. -/
theorem integrable_schwartzHat (F : 𝓢(ℝ, ℂ)) : Integrable fun η : ℝ => ∫ y, F y * e (-(y * η)) := by
  have h1 : Integrable (⇑(𝓕 F : 𝓢(ℝ, ℂ))) := (𝓕 F : 𝓢(ℝ, ℂ)).integrable
  have h2 : (⇑(𝓕 F : 𝓢(ℝ, ℂ))) = 𝓕 (⇑F) := SchwartzMap.fourier_coe F
  rw [h2] at h1
  have h3 : (fun η : ℝ => ∫ y, F y * e (-(y * η))) = 𝓕 (⇑F) := by
    funext η
    rw [fourier_eq_integral_e]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    ring
  rw [h3]
  exact h1

/-- `F̂ e(·x)` is integrable for a Schwartz function `F`. -/
theorem integrable_schwartzDensity (F : 𝓢(ℝ, ℂ)) (x : ℝ) : Integrable (schwartzDensity F x) := by
  have h1 := integrable_schwartzHat F
  unfold schwartzDensity
  refine h1.norm.mono' (h1.aestronglyMeasurable.mul ?_) (Filter.Eventually.of_forall fun η => ?_)
  · exact (continuous_e.comp (continuous_id.mul continuous_const)).aestronglyMeasurable
  · rw [norm_mul, norm_e, mul_one]

/-- `ξ ↦ 𝒮[F](ξ, x)` is continuous. -/
theorem continuous_partialFourierIntegral (F : 𝓢(ℝ, ℂ)) (x : ℝ) :
    Continuous fun ξ => partialFourierIntegral F ξ x :=
  continuous_partialInt (integrable_schwartzDensity F x)

/-- `x ↦ 𝒮[F](ξ, x)` is continuous (dominated convergence). -/
theorem continuous_partialFourierIntegral_right (F : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    Continuous fun x => partialFourierIntegral F ξ x := by
  have h1 := integrable_schwartzHat F
  refine continuous_of_dominated (bound := fun η => ‖∫ y, F y * e (-(y * η))‖) (fun x => ?_)
    (fun x => ?_) ?_ ?_
  · exact (integrable_schwartzDensity F x).aestronglyMeasurable.restrict
  · refine Filter.Eventually.of_forall fun η => ?_
    rw [norm_mul, norm_e, mul_one]
  · exact h1.norm.restrict
  · refine Filter.Eventually.of_forall fun η => ?_
    exact continuous_const.mul (continuous_e.comp (continuous_const.mul continuous_id))

/-! ### Charts -/

/-- The chart `(c - 1/2, c + 1/2]`. -/
def chartSet (c : ℝ) : Set ℝ := Set.Ioc (c - 1 / 2) (c + 1 / 2)

/-- The chart is measurable. -/
theorem measurableSet_chartSet (c : ℝ) : MeasurableSet (chartSet c) := measurableSet_Ioc

/-- The chart `0` is `(-1/2, 1/2]`. -/
theorem chartSet_zero : chartSet 0 = Set.Ioc (-1 / 2 : ℝ) (1 / 2) := by
  ext β
  simp only [chartSet, Set.mem_Ioc]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

/-- The chart density `ĝ_{c,f,n}(β) = 1_{(c - 1/2, c + 1/2]}(β) f̂(β) e(nβ)`. -/
def chartDensity (c : ℝ) (f : ℤ →₀ ℂ) (n : ℤ) : ℝ → ℂ :=
  (chartSet c).indicator fun β => fourierZ f β * e ((n : ℝ) * β)

/-- The chart density is integrable. -/
theorem integrable_chartDensity (c : ℝ) (f : ℤ →₀ ℂ) (n : ℤ) : Integrable (chartDensity c f n) := by
  unfold chartDensity
  rw [integrable_indicator_iff (measurableSet_chartSet c)]
  exact (((continuous_fourierZ f).mul
    (continuous_e.comp (continuous_const.mul continuous_id))).integrableOn_Ioc)

/-- The modulated sequence `k ↦ f(k) e(-ck)`: `(modulate c f)^(β) = f̂(β + c)`. -/
def modulate (c : ℝ) (f : ℤ →₀ ℂ) : ℤ →₀ ℂ :=
  Finsupp.onFinset f.support (fun k => f k * e (-(c * k))) fun k hk => by
    by_contra h
    exact hk (by simp [Finsupp.notMem_support_iff.1 h])

/-- `(f_c)(k) = f(k) e(-ck)`. -/
theorem modulate_apply (c : ℝ) (f : ℤ →₀ ℂ) (k : ℤ) : modulate c f k = f k * e (-(c * k)) := rfl

/-- `(f_c)^(β) = f̂(β + c)`. -/
theorem fourierZ_modulate (c : ℝ) (f : ℤ →₀ ℂ) (β : ℝ) :
    fourierZ (modulate c f) β = fourierZ f (β + c) := by
  have hS : (modulate c f).support ⊆ f.support := fun k hk => by
    by_contra h
    exact (Finsupp.mem_support_iff.1 hk) (by simp [modulate_apply, Finsupp.notMem_support_iff.1 h])
  rw [fourierZ_eq_sum_of_support_subset _ hS]
  unfold fourierZ Finsupp.sum
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [modulate_apply, mul_assoc, ← e_add]
  congr 2
  ring

/-- `‖e(t)‖ₑ = 1`. -/
theorem enorm_e (t : ℝ) : ‖e t‖ₑ = 1 := by
  rw [← ofReal_norm, norm_e]
  simp

/-- Modulation preserves the `ℓ^p(ℤ)` norm. -/
theorem eLpNorm_modulate {p : ℝ} (hp : 0 < p) (c : ℝ) (f : ℤ →₀ ℂ) :
    eLpNorm (⇑(modulate c f)) (ENNReal.ofReal p) Measure.count =
      eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
  rw [eLpNorm_count_eq_tsum _ hp, eLpNorm_count_eq_tsum _ hp]
  simp_rw [modulate_apply, enorm_mul, enorm_e, mul_one]

/-- The chart density of `f` on the chart `c` is the modulated chart density on the chart `0`:
`ĝ_{c,f,n}(β) = e(nc) ĝ_{0,f_c,n}(β - c)`. -/
theorem chartDensity_shift (c : ℝ) (f : ℤ →₀ ℂ) (n : ℤ) (β : ℝ) :
    chartDensity c f n β = e ((n : ℝ) * c) * chartDensity 0 (modulate c f) n (β - c) := by
  unfold chartDensity
  by_cases hβ : β ∈ chartSet c
  · have hβ' : β - c ∈ chartSet 0 := by
      simp only [chartSet, Set.mem_Ioc] at hβ ⊢
      constructor <;> linarith [hβ.1, hβ.2]
    rw [Set.indicator_of_mem hβ, Set.indicator_of_mem hβ', fourierZ_modulate, sub_add_cancel,
      ← mul_assoc, mul_comm (e _), mul_assoc, ← e_add]
    congr 2
    ring
  · have hβ' : β - c ∉ chartSet 0 := by
      simp only [chartSet, Set.mem_Ioc, not_and_or, not_lt, not_le] at hβ ⊢
      rcases hβ with h | h
      · left; linarith
      · right; linarith
    rw [Set.indicator_of_notMem hβ, Set.indicator_of_notMem hβ', mul_zero]

/-- The chart partial integral on the chart `c` is the modulated one on the chart `0`:
`Φ_{c,f,n}(λ) = e(nc) Φ_{0,f_c,n}(λ - c)`. -/
theorem partialInt_chartDensity_shift (c : ℝ) (f : ℤ →₀ ℂ) (n : ℤ) (lam : ℝ) :
    partialInt (chartDensity c f n) lam =
      e ((n : ℝ) * c) * partialInt (chartDensity 0 (modulate c f) n) (lam - c) := by
  rw [partialInt_eq_integral_indicator, partialInt_eq_integral_indicator]
  have h1 : ∀ ξ : ℝ, (Set.Iic lam).indicator (chartDensity c f n) ξ =
      e ((n : ℝ) * c) *
        (Set.Iic (lam - c)).indicator (chartDensity 0 (modulate c f) n) (ξ - c) := by
    intro ξ
    by_cases hξ : ξ ≤ lam
    · have hξ' : ξ - c ≤ lam - c := by linarith
      rw [Set.indicator_of_mem (Set.mem_Iic.2 hξ), Set.indicator_of_mem (Set.mem_Iic.2 hξ'),
        chartDensity_shift]
    · have hξ' : ¬ ξ - c ≤ lam - c := by intro h; apply hξ; linarith
      rw [Set.indicator_of_notMem (by simpa using hξ), Set.indicator_of_notMem (by simpa using hξ'),
        mul_zero]
  simp_rw [h1]
  rw [integral_const_mul, integral_sub_right_eq_self
    (fun ξ => (Set.Iic (lam - c)).indicator (chartDensity 0 (modulate c f) n) ξ) c]

/-! ### The half-line family and the Euclidean hypothesis -/

/-- The half-line multiplier `1_{(-1/2, 1/2] ∩ (-∞, λ]}`, supported in `(-1/2, 1/2]`. -/
def halfLineMult (lam : ℝ) : ℝ → ℂ :=
  (Set.Ioc (-1 / 2 : ℝ) (1 / 2) ∩ Set.Iic lam).indicator fun _ => (1 : ℂ)

/-- The half-line multiplier is measurable. -/
theorem measurable_halfLineMult (lam : ℝ) : Measurable (halfLineMult lam) :=
  measurable_const.indicator (measurableSet_Ioc.inter measurableSet_Iic)

/-- The half-line multiplier is bounded by `1`. -/
theorem norm_halfLineMult_le (lam ξ : ℝ) : ‖halfLineMult lam ξ‖ ≤ 1 := by
  unfold halfLineMult
  by_cases h : ξ ∈ Set.Ioc (-1 / 2 : ℝ) (1 / 2) ∩ Set.Iic lam
  · rw [Set.indicator_of_mem h]
    simp
  · rw [Set.indicator_of_notMem h]
    simp

/-- The half-line multiplier is `1` on its set. -/
theorem halfLineMult_of_mem {lam ξ : ℝ} (h : ξ ∈ Set.Ioc (-1 / 2 : ℝ) (1 / 2) ∩ Set.Iic lam) :
    halfLineMult lam ξ = 1 := by
  unfold halfLineMult
  exact Set.indicator_of_mem h _

/-- The half-line multiplier is `0` off its set. -/
theorem halfLineMult_of_notMem {lam ξ : ℝ}
    (h : ξ ∉ Set.Ioc (-1 / 2 : ℝ) (1 / 2) ∩ Set.Iic lam) : halfLineMult lam ξ = 0 := by
  unfold halfLineMult
  exact Set.indicator_of_notMem h _

/-- The half-line multiplier is supported in `(-1/2, 1/2]`. -/
theorem support_halfLineMult_subset (lam : ℝ) :
    Function.support (halfLineMult lam) ⊆ Set.Ioc (-1 / 2 : ℝ) (1 / 2) := by
  intro ξ hξ
  by_contra h
  exact hξ (halfLineMult_of_notMem fun hh => h hh.1)

/-- The clamp `κ(λ) = max(-1/2, min(λ, 1/2))`. -/
def clampHalf (lam : ℝ) : ℝ := max (-1 / 2) (min lam (1 / 2))

/-- The clamp `κ` is monotone. -/
theorem monotone_clampHalf : Monotone clampHalf := fun _ _ hab =>
  max_le_max le_rfl (min_le_min hab le_rfl)

/-- The Euclidean multiplier output of the half-line family is a clamped difference of
half-line projections: `T_{m_λ} F(x) = 𝒮[F](κ λ, x) - 𝒮[F](-1/2, x)`. -/
theorem multiplierOp_halfLineMult (F : 𝓢(ℝ, ℂ)) (x lam : ℝ) :
    multiplierOp (halfLineMult lam) F x =
      partialFourierIntegral F (clampHalf lam) x - partialFourierIntegral F (-1 / 2) x := by
  have hset : Set.Ioc (-1 / 2 : ℝ) (1 / 2) ∩ Set.Iic lam = Set.Ioc (-1 / 2) (clampHalf lam) := by
    ext ξ
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Iic, clampHalf]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, le_max_of_le_right (le_min h3 h2)⟩
    · rintro ⟨h1, h2⟩
      rcases le_max_iff.1 h2 with h | h
      · exact absurd h (not_le.2 h1)
      · exact ⟨⟨h1, (le_min_iff.1 h).2⟩, (le_min_iff.1 h).1⟩
  unfold multiplierOp
  have h1 : ∀ ξ : ℝ, halfLineMult lam ξ * (∫ y, F y * e (-(y * ξ))) * e (ξ * x) =
      (Set.Ioc (-1 / 2 : ℝ) (1 / 2) ∩ Set.Iic lam).indicator (schwartzDensity F x) ξ := by
    intro ξ
    by_cases hξ : ξ ∈ Set.Ioc (-1 / 2 : ℝ) (1 / 2) ∩ Set.Iic lam
    · rw [halfLineMult_of_mem hξ, Set.indicator_of_mem hξ]
      unfold schwartzDensity
      ring
    · rw [halfLineMult_of_notMem hξ, Set.indicator_of_notMem hξ]
      ring
  simp_rw [h1]
  rw [integral_indicator (measurableSet_Ioc.inter measurableSet_Iic), hset]
  exact (partialInt_sub_eq (integrable_schwartzDensity F x) (le_max_left _ _)).symm

/-- The discrete multiplier output of the half-line family is the chart partial integral:
`T_{dis, m_λ} f(n) = Φ_{0,f,n}(λ)`. -/
theorem multiplierOpDis_halfLineMult (f : ℤ →₀ ℂ) (n : ℤ) (lam : ℝ) :
    multiplierOpDis (halfLineMult lam) f n = partialInt (chartDensity 0 f n) lam := by
  rw [multiplierOpDis_eq_integral (measurable_halfLineMult lam) ⟨1, norm_halfLineMult_le lam⟩
    (support_halfLineMult_subset lam), intervalIntegral.integral_of_le (by norm_num),
    partialInt_eq_integral_indicator, ← integral_indicator measurableSet_Ioc]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  have hcd : chartDensity 0 f n = (Set.Ioc (-1 / 2 : ℝ) (1 / 2)).indicator
      fun β => fourierZ f β * e ((n : ℝ) * β) := by
    unfold chartDensity
    rw [chartSet_zero]
  rw [hcd]
  by_cases h1 : ξ ∈ Set.Ioc (-1 / 2 : ℝ) (1 / 2)
  · by_cases h2 : ξ ≤ lam
    · have h3 : ξ ∈ Set.Ioc (-1 / 2 : ℝ) (1 / 2) ∩ Set.Iic lam := ⟨h1, h2⟩
      rw [Set.indicator_of_mem h1, Set.indicator_of_mem (Set.mem_Iic.2 h2),
        Set.indicator_of_mem h1, halfLineMult_of_mem h3, one_mul]
    · have h3 : ξ ∉ Set.Ioc (-1 / 2 : ℝ) (1 / 2) ∩ Set.Iic lam := fun h => h2 h.2
      rw [Set.indicator_of_mem h1, Set.indicator_of_notMem (s := Set.Iic lam) (a := ξ) h2,
        halfLineMult_of_notMem h3]
      ring
  · rw [Set.indicator_of_notMem h1]
    by_cases h2 : ξ ≤ lam
    · rw [Set.indicator_of_mem (Set.mem_Iic.2 h2), Set.indicator_of_notMem h1]
    · rw [Set.indicator_of_notMem (s := Set.Iic lam) (a := ξ) h2]

/-- `x ↦ T_{m_λ} F(x)` is continuous for the half-line family. -/
theorem continuous_multiplierOp_halfLineMult (F : 𝓢(ℝ, ℂ)) (lam : ℝ) :
    Continuous fun x => multiplierOp (halfLineMult lam) F x := by
  simp_rw [multiplierOp_halfLineMult]
  exact (continuous_partialFourierIntegral_right F _).sub
    (continuous_partialFourierIntegral_right F _)

/-! ### Finite `T`, chart `0` -/

theorem one_le_of_gt_conj {r p : ℝ} (hr : 2 < r) (hp : r / (r - 1) < p) : 1 ≤ p := by
  have h1 : 1 < r / (r - 1) := by
    rw [one_lt_div (by linarith)]
    linarith
  linarith

/-- **Half-line variation bound for finite `T`, chart `0`** (conditional on `hO`): the transference
of the Euclidean variational Carleson estimate to `ℓ^p(ℤ)`. -/
theorem halfLine_finite_zero (hO : OplusVariationBound) {r p : ℝ} (hr : 2 < r)
    (hp : r / (r - 1) < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : Finset ℝ) (f : ℤ →₀ ℂ),
      eLpNorm (fun n => rVariationOn r (T : Set ℝ) (partialInt (chartDensity 0 f n)))
          (ENNReal.ofReal p) Measure.count ≤
        ENNReal.ofReal C * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
  obtain ⟨CO, hCO⟩ := hO r hr p hp
  obtain ⟨CM, hCM⟩ := msw_transference_variation
  have hp1 : 1 ≤ p := one_le_of_gt_conj hr hp
  have hr1 : 1 ≤ r := by linarith
  refine ⟨max (CM * max CO 0) 0, le_max_right _ _, fun T f => ?_⟩
  have heuclid : ∀ F : 𝓢(ℝ, ℂ),
      eLpNorm (fun x => rVariationOn r (T : Set ℝ)
          (fun lam => multiplierOp (halfLineMult lam) F x)) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (max CO 0) * eLpNorm (⇑F) (ENNReal.ofReal p) volume := by
    intro F
    calc eLpNorm (fun x => rVariationOn r (T : Set ℝ)
            (fun lam => multiplierOp (halfLineMult lam) F x)) (ENNReal.ofReal p) volume
        ≤ eLpNorm (fun x => rVariationOn r Set.univ (fun ξ => partialFourierIntegral F ξ x))
            (ENNReal.ofReal p) volume := by
          refine eLpNorm_mono_enorm (measurable_rVariationOn (by linarith)
            (a := fun lam x => multiplierOp (halfLineMult lam) F x) (S := (T : Set ℝ))
            (fun lam _ => continuous_multiplierOp_halfLineMult F lam)).aestronglyMeasurable
            fun x => ?_
          simp only [enorm_eq_self]
          simp_rw [multiplierOp_halfLineMult]
          rw [rVariationOn_sub_const]
          exact rVariationOn_comp_monotone_le (continuous_partialFourierIntegral F x)
            monotone_clampHalf _
      _ ≤ ENNReal.ofReal CO * eLpNorm (⇑F) (ENNReal.ofReal p) volume := hCO F
      _ ≤ ENNReal.ofReal (max CO 0) * eLpNorm (⇑F) (ENNReal.ofReal p) volume := by
          gcongr
          exact le_max_left _ _
  have hmsw := hCM p hp1 r hr1 T (fun lam => halfLineMult lam) (max CO 0)
    (fun lam _ => measurable_halfLineMult lam) (fun lam _ => ⟨1, norm_halfLineMult_le lam⟩)
    (fun lam _ => support_halfLineMult_subset lam) heuclid f
  simp_rw [multiplierOpDis_halfLineMult] at hmsw
  refine hmsw.trans ?_
  gcongr
  exact le_max_left _ _

/-! ### Chart `c`, finite `T` -/

theorem rVariationOn_chart_le (r : ℝ) (T : Finset ℝ) (c : ℝ) (f : ℤ →₀ ℂ) (n : ℤ) :
    rVariationOn r (T : Set ℝ) (partialInt (chartDensity c f n)) ≤
      rVariationOn r ((T.image fun t => t - c : Finset ℝ) : Set ℝ)
        (partialInt (chartDensity 0 (modulate c f) n)) := by
  classical
  refine rVariationOn_le fun J t hm hS => ?_
  have hm' : StrictMono fun i => t i - c := fun i j hij => by
    have := hm hij
    simp only
    linarith
  have hS' : ∀ i, (fun i => t i - c) i ∈ ((T.image fun t => t - c : Finset ℝ) : Set ℝ) :=
    fun i => by
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
      exact ⟨t i, hS i, rfl⟩
  have h := le_rVariationOn (r := r) (a := partialInt (chartDensity 0 (modulate c f) n)) hm' hS'
  refine le_trans (le_of_eq ?_) h
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [partialInt_chartDensity_shift c f n, partialInt_chartDensity_shift c f n, ← mul_sub,
    enorm_mul, enorm_e, one_mul]

/-- **Half-line variation bound for finite `T`, chart `c`** (conditional on `hO`). -/
theorem halfLine_finite (hO : OplusVariationBound) {r p : ℝ} (hr : 2 < r) (hp : r / (r - 1) < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : ℝ) (T : Finset ℝ) (f : ℤ →₀ ℂ),
      eLpNorm (fun n => rVariationOn r (T : Set ℝ) (partialInt (chartDensity c f n)))
          (ENNReal.ofReal p) Measure.count ≤
        ENNReal.ofReal C * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
  classical
  obtain ⟨C, hC0, hC⟩ := halfLine_finite_zero hO hr hp
  have hp0 : 0 < p := by linarith [one_le_of_gt_conj hr hp]
  refine ⟨C, hC0, fun c T f => ?_⟩
  calc eLpNorm (fun n => rVariationOn r (T : Set ℝ) (partialInt (chartDensity c f n)))
        (ENNReal.ofReal p) Measure.count
      ≤ eLpNorm (fun n => rVariationOn r ((T.image fun t => t - c : Finset ℝ) : Set ℝ)
          (partialInt (chartDensity 0 (modulate c f) n))) (ENNReal.ofReal p) Measure.count :=
        eLpNorm_count_mono_enn (fun n => rVariationOn_chart_le r T c f n) _
    _ ≤ ENNReal.ofReal C * eLpNorm (⇑(modulate c f)) (ENNReal.ofReal p) Measure.count :=
        hC _ _
    _ = ENNReal.ofReal C * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
        rw [eLpNorm_modulate hp0]

/-! ### Arbitrary `T` -/

/-- **The discrete half-line variation bound** (conditional on `hO`; Source: main paper `l:varcarZ`,
L1813–L1816; main paper `p:disc`, L2983–L2986, with its Euclidean hypothesis for the half-line
family): for `r > 2`, `r' < p < ∞` there is `C` such that for every chart centre `c` and every
finitely supported `f`,
`‖ n ↦ V^r(λ ↦ ∫_{(c - 1/2, c + 1/2], β ≤ λ} f̂(β) e(nβ) dβ : λ ∈ ℝ) ‖_{ℓ^p} ≤ C ‖f‖_{ℓ^p}`. -/
theorem halfLine_variation (hO : OplusVariationBound) {r p : ℝ} (hr : 2 < r)
    (hp : r / (r - 1) < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : ℝ) (f : ℤ →₀ ℂ),
      eLpNorm (fun n => rVariationOn r Set.univ (partialInt (chartDensity c f n)))
          (ENNReal.ofReal p) Measure.count ≤
        ENNReal.ofReal C * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
  obtain ⟨C, hC0, hC⟩ := halfLine_finite hO hr hp
  have hp0 : 0 < p := by linarith [one_le_of_gt_conj hr hp]
  refine ⟨C, hC0, fun c f => ?_⟩
  have hu : ∀ n : ℤ, rVariationOn r Set.univ (partialInt (chartDensity c f n)) =
      ⨆ T : Finset ℝ, rVariationOn r (T : Set ℝ) (partialInt (chartDensity c f n)) := by
    intro n
    rw [rVariationOn_eq_iSup_finset]
    simp
  have hfun : (fun n : ℤ => rVariationOn r Set.univ (partialInt (chartDensity c f n))) =
      fun n => ⨆ T : Finset ℝ, rVariationOn r (T : Set ℝ) (partialInt (chartDensity c f n)) :=
    funext hu
  rw [hfun]
  refine (eLpNorm_count_iSup_le hp0 ?_).trans (iSup_le fun T => hC c T f)
  intro T₁ T₂
  exact ⟨T₁ ∪ T₂, fun n => ⟨rVariationOn_mono_set (by simp) _, rVariationOn_mono_set (by simp) _⟩⟩

/-- The multiplier output on the chart `c`: `λ ↦ ∫ h(β - λ) 1_{chart}(β) f̂(β) e(nβ) dβ`. -/
def chartMult (c : ℝ) (h : ℝ → ℂ) (f : ℤ →₀ ℂ) (n : ℤ) : ℝ → ℂ := mulInt h (chartDensity c f n)

/-- **Variation of the maximally modulated bounded-variation multipliers on `ℤ`** (conditional on
`hO`; the core of `l:varcarZ`, `p:disc`, `c:disc`): for `r > 2`, `r' < p < ∞` there is `C` such that
for every chart centre `c`, every `h` of variation `≤ B` vanishing off a compact interval, every set
`S ⊆ ℝ` of frequencies and every finitely supported `f`,
`‖ n ↦ V^r(λ ↦ ∫_{(c - 1/2, c + 1/2]} h(β - λ) f̂(β) e(nβ) dβ : λ ∈ S) ‖_{ℓ^p} ≤ C B ‖f‖_{ℓ^p}`. -/
theorem chart_variation (hO : OplusVariationBound) {r p : ℝ} (hr : 2 < r) (hp : r / (r - 1) < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : ℝ) (h : ℝ → ℂ) (u w : ℝ), (∀ s, s ∉ Set.Icc u w → h s = 0) →
      ∀ B : ℝ, 0 ≤ B → eVariationOn h Set.univ ≤ ENNReal.ofReal B →
      ∀ (f : ℤ →₀ ℂ) (S : Set ℝ),
        eLpNorm (fun n => rVariationOn r S (chartMult c h f n)) (ENNReal.ofReal p)
            Measure.count ≤
          ENNReal.ofReal (C * B) * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
  obtain ⟨C, hC0, hC⟩ := halfLine_variation hO hr hp
  have hp0 : 0 < p := by linarith [one_le_of_gt_conj hr hp]
  refine ⟨C, hC0, fun c h u w hsupp B hB0 hB f S => ?_⟩
  calc eLpNorm (fun n => rVariationOn r S (chartMult c h f n)) (ENNReal.ofReal p) Measure.count
      ≤ eLpNorm (fun n => ENNReal.ofReal B *
          rVariationOn r Set.univ (partialInt (chartDensity c f n))) (ENNReal.ofReal p)
          Measure.count :=
        eLpNorm_count_mono_enn (fun n => varcar_bv (by linarith) (integrable_chartDensity c f n)
          hsupp hB0 hB S) _
    _ = ENNReal.ofReal B * eLpNorm (fun n => rVariationOn r Set.univ
          (partialInt (chartDensity c f n))) (ENNReal.ofReal p) Measure.count :=
        eLpNorm_count_const_mul _ _ hp0
    _ ≤ ENNReal.ofReal B * (ENNReal.ofReal C * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count) := by
        gcongr
        exact hC c f
    _ = ENNReal.ofReal (C * B) * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hB0, mul_comm B C]

end PrimeCarleson.Proof.Paper
