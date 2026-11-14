module

public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Layer-cake and Tonelli toolbox for the Lépingle track

The layer cake formula, a standard result (used in Zorin-Kranich's notes, 01-BDG.tex L92-L96,
L331-L334, L388-L399): for `X ≥ 0` measurable, `p > 0`, `t ≥ 0`
* `∫ X^p dμ = ∫_0^∞ p λ^{p-1} μ(X > λ) dλ` (Mathlib: `lintegral_comp_eq_lintegral_meas_lt_mul`,
  here `lintegral_eq_lintegral_meas_lt_ennreal` for `ℝ≥0∞`-valued `X`);
* `t^p = p (p-1) ∫_0^t (t - λ) λ^{p-2} dλ` for `p > 1` (`lintegral_Ioo_sub_mul_rpow`).

Also the elementary integrals `∫_0^x t^s dt` and `∫_a^∞ t^{-2} dt` in `ℝ≥0∞` and the Tonelli swap
`lintegral_lintegral_Ioo_swap` used by Doob, Garsia-Neveu and Davis.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Lepingle

section Calculus

/-- `∫_0^x t^s dt = x^{s+1}/(s+1)` for `s > -1`, in `ℝ≥0∞`. -/
theorem lintegral_Ioo_rpow {s : ℝ} (hs : -1 < s) {x : ℝ} (hx : 0 ≤ x) :
    ∫⁻ t in Ioo 0 x, ENNReal.ofReal (t ^ s) = ENNReal.ofReal (x ^ (s + 1) / (s + 1)) := by
  have hint : IntervalIntegrable (fun t : ℝ => t ^ s) volume 0 x :=
    intervalIntegral.intervalIntegrable_rpow' hs
  have h1 : ∫⁻ t in Ioo 0 x, ENNReal.ofReal (t ^ s) =
      ENNReal.ofReal (∫ t in Ioo 0 x, t ^ s) := by
    rw [ofReal_integral_eq_lintegral_ofReal]
    · exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hx).1 hint
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht using
        Real.rpow_nonneg ht.1.le s
  rw [h1, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hx,
    integral_rpow (Or.inl hs)]
  simp [Real.zero_rpow (by linarith : s + 1 ≠ 0)]

/-- `p(p-1) ∫_0^x (x - t) t^{p-2} dt = x^p` for `p > 1` (`t^p = p(p-1) ∫_0^t (t-λ) λ^{p-2} dλ`
of Zorin-Kranich's notes, L390, with the sign misprint corrected), written as
`∫_0^x (x - t) t^{p-2} dt = x^p / (p (p-1))` in `ℝ≥0∞`. -/
theorem lintegral_Ioo_sub_mul_rpow {p : ℝ} (hp : 1 < p) {x : ℝ} (hx : 0 ≤ x) :
    ∫⁻ t in Ioo 0 x, ENNReal.ofReal ((x - t) * t ^ (p - 2)) =
      ENNReal.ofReal (x ^ p / (p * (p - 1))) := by
  have hs : -1 < p - 2 := by linarith
  have hint : IntervalIntegrable (fun t : ℝ => t ^ (p - 2)) volume 0 x :=
    intervalIntegral.intervalIntegrable_rpow' hs
  have hint2 : IntervalIntegrable (fun t : ℝ => t ^ (p - 1)) volume 0 x :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hnn : ∀ t ∈ Ioo 0 x, 0 ≤ (x - t) * t ^ (p - 2) := fun t ht =>
    mul_nonneg (by linarith [ht.2]) (Real.rpow_nonneg ht.1.le _)
  have hfun : (fun t : ℝ => (x - t) * t ^ (p - 2)) = fun t => x * t ^ (p - 2) - t ^ (p - 1) := by
    funext t
    rcases eq_or_ne t 0 with rfl | ht
    · simp [Real.zero_rpow (by linarith : p - 1 ≠ 0)]
    · rw [sub_mul, show p - 1 = (p - 2) + 1 by ring, Real.rpow_add_one ht]
      ring
  have hII : IntervalIntegrable (fun t : ℝ => (x - t) * t ^ (p - 2)) volume 0 x := by
    rw [hfun]
    exact (hint.const_mul x).sub hint2
  have h1 : ∫⁻ t in Ioo 0 x, ENNReal.ofReal ((x - t) * t ^ (p - 2)) =
      ENNReal.ofReal (∫ t in Ioo 0 x, (x - t) * t ^ (p - 2)) := by
    rw [ofReal_integral_eq_lintegral_ofReal]
    · exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hx).1 hII
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht using hnn t ht
  rw [h1, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hx]
  congr 1
  rw [hfun, intervalIntegral.integral_sub (hint.const_mul x) hint2,
    intervalIntegral.integral_const_mul, integral_rpow (Or.inl hs),
    integral_rpow (Or.inl (by linarith))]
  have h0 : (0 : ℝ) ^ (p - 2 + 1) = 0 := Real.zero_rpow (by linarith)
  have h0' : (0 : ℝ) ^ (p - 1 + 1) = 0 := Real.zero_rpow (by linarith)
  have hx1 : x * x ^ (p - 2 + 1) = x ^ p := by
    rw [← Real.rpow_one_add' hx (by linarith)]
    congr 1
    ring
  have hx2 : x ^ (p - 1 + 1) = x ^ p := by
    congr 1
    ring
  rw [h0, h0', sub_zero, sub_zero, mul_div_assoc', hx1, hx2]
  have h1p : p - 2 + 1 = p - 1 := by ring
  have h2p : p - 1 + 1 = p := by ring
  rw [h1p, h2p]
  field_simp
  ring

/-- `∫_a^∞ t^{-2} dt = 1/a` for `a > 0`, in `ℝ≥0∞`. -/
theorem lintegral_Ioi_rpow_neg_two {a : ℝ} (ha : 0 < a) :
    ∫⁻ t in Ioi a, ENNReal.ofReal (t ^ (-2 : ℝ)) = ENNReal.ofReal a⁻¹ := by
  have hint : IntegrableOn (fun t : ℝ => t ^ (-2 : ℝ)) (Ioi a) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) ha
  rw [← ofReal_integral_eq_lintegral_ofReal hint]
  · congr 1
    rw [integral_Ioi_rpow_of_lt (by norm_num) ha]
    norm_num
    rw [Real.rpow_neg_one]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht using
      Real.rpow_nonneg (ha.trans ht).le _

end Calculus

section Tonelli

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [SFinite μ]

/-- Tonelli swap for the region under a real-valued function:
`∫_Ω ∫_{0}^{X ω} H t ω dt dμ = ∫_{t > 0} ∫_{X > t} H t ω dμ dt`. -/
theorem lintegral_lintegral_Ioo_swap {X : Ω → ℝ} (hX : Measurable X) {H : ℝ → Ω → ℝ≥0∞}
    (hH : Measurable (Function.uncurry H)) :
    ∫⁻ ω, (∫⁻ t in Ioo 0 (X ω), H t ω) ∂μ =
      ∫⁻ t in Ioi 0, (∫⁻ ω in {ω | t < X ω}, H t ω ∂μ) := by
  have h1 : ∀ ω, ∫⁻ t in Ioo 0 (X ω), H t ω =
      ∫⁻ t in Ioi 0, if t < X ω then H t ω else 0 := by
    intro ω
    have : (fun t => if t < X ω then H t ω else 0) =
        (Iio (X ω)).indicator (fun t => H t ω) := by
      funext t
      simp [Set.indicator_apply]
    rw [this, lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
      Set.Iio_inter_Ioi]
  simp_rw [h1]
  rw [lintegral_lintegral_swap]
  · refine lintegral_congr fun t => ?_
    rw [← lintegral_indicator (measurableSet_lt measurable_const hX)]
    congr 1
  · refine Measurable.aemeasurable ?_
    refine Measurable.ite (measurableSet_lt measurable_snd (hX.comp measurable_fst)) ?_
      measurable_const
    exact hH.comp (measurable_snd.prodMk measurable_fst)

/-- The measure of the region under `x`: `∫_{t > 0} 1_{t < x} dt = x` in `ℝ≥0∞`. -/
theorem lintegral_Ioi_indicator_lt (x : ℝ≥0∞) :
    ∫⁻ t in Ioi (0 : ℝ), {t : ℝ | ENNReal.ofReal t < x}.indicator (fun _ => (1 : ℝ≥0∞)) t = x := by
  rcases eq_or_ne x ∞ with rfl | hx
  · have : {t : ℝ | ENNReal.ofReal t < ∞} = univ := by
      ext t
      simp
    rw [this]
    simp
  · have hset : {t : ℝ | ENNReal.ofReal t < x} ∩ Ioi 0 = Ioo 0 x.toReal := by
      ext t
      simp only [mem_inter_iff, mem_ofPred_eq, mem_Ioi, mem_Ioo]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h2, (ENNReal.ofReal_lt_iff_lt_toReal h2.le hx).1 h1⟩
      · rintro ⟨h2, h1⟩
        exact ⟨(ENNReal.ofReal_lt_iff_lt_toReal h2.le hx).2 h1, h2⟩
    have hms : MeasurableSet {t : ℝ | ENNReal.ofReal t < x} :=
      measurableSet_lt (by fun_prop) measurable_const
    rw [lintegral_indicator_const hms, Measure.restrict_apply hms, hset, Real.volume_Ioo]
    simp [ENNReal.ofReal_toReal hx]

/-- Layer cake formula for `ℝ≥0∞`-valued functions: `∫ X dμ = ∫_0^∞ μ(X > t) dt`. -/
theorem lintegral_eq_lintegral_meas_lt_ennreal {X : Ω → ℝ≥0∞} (hX : Measurable X) :
    ∫⁻ ω, X ω ∂μ = ∫⁻ t in Ioi (0 : ℝ), μ {ω | ENNReal.ofReal t < X ω} := by
  have h1 : ∀ ω, X ω = ∫⁻ t in Ioi (0 : ℝ),
      {t : ℝ | ENNReal.ofReal t < X ω}.indicator (fun _ => (1 : ℝ≥0∞)) t := fun ω =>
    (lintegral_Ioi_indicator_lt (X ω)).symm
  have hmeas : Measurable (Function.uncurry fun (ω : Ω) (t : ℝ) =>
      {t : ℝ | ENNReal.ofReal t < X ω}.indicator (fun _ => (1 : ℝ≥0∞)) t) := by
    have : MeasurableSet {q : Ω × ℝ | ENNReal.ofReal q.2 < X q.1} :=
      measurableSet_lt (by fun_prop) (hX.comp measurable_fst)
    have heq : Function.uncurry (fun (ω : Ω) (t : ℝ) =>
        {t : ℝ | ENNReal.ofReal t < X ω}.indicator (fun _ => (1 : ℝ≥0∞)) t) =
        {q : Ω × ℝ | ENNReal.ofReal q.2 < X q.1}.indicator (fun _ => (1 : ℝ≥0∞)) := by
      funext q
      simp [Set.indicator_apply, Function.uncurry]
    rw [heq]
    exact measurable_const.indicator this
  calc ∫⁻ ω, X ω ∂μ
      = ∫⁻ ω, (∫⁻ t in Ioi (0 : ℝ),
          {t : ℝ | ENNReal.ofReal t < X ω}.indicator (fun _ => (1 : ℝ≥0∞)) t) ∂μ :=
        lintegral_congr h1
    _ = ∫⁻ t in Ioi (0 : ℝ), (∫⁻ ω,
          {t : ℝ | ENNReal.ofReal t < X ω}.indicator (fun _ => (1 : ℝ≥0∞)) t ∂μ) :=
        lintegral_lintegral_swap hmeas.aemeasurable
    _ = ∫⁻ t in Ioi (0 : ℝ), μ {ω | ENNReal.ofReal t < X ω} := by
        refine lintegral_congr fun t => ?_
        have hms : MeasurableSet {ω | ENNReal.ofReal t < X ω} :=
          measurableSet_lt measurable_const hX
        have : (fun ω => {t : ℝ | ENNReal.ofReal t < X ω}.indicator (fun _ => (1 : ℝ≥0∞)) t) =
            {ω | ENNReal.ofReal t < X ω}.indicator (fun _ => (1 : ℝ≥0∞)) := by
          funext ω
          simp [Set.indicator_apply]
        rw [this, lintegral_indicator_const hms, one_mul]

end Tonelli

end PrimeCarleson.Proof.Lepingle
