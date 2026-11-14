module

public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# A Schur test for nonnegative kernels

For a kernel `K : X → Y → ℝ≥0∞` whose row integrals are bounded by `a` and whose column integrals
are bounded by `b`, the operator `G ↦ ∫⁻ y, K x y * G y ∂ν` is bounded on `Lᵖ` with constant
`a ^ (1 - 1 / p) * b ^ (1 / p)` (Schur's test). The proof applies Hölder's inequality
for the measure `K x · ν` in each row, and then Tonelli's theorem.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.MswTransference

/-- Jensen's inequality for the measure `k ν`: `(∫ k G)^p ≤ (∫ k)^(p-1) ∫ k G^p`
for `p ≥ 1`. -/
theorem lintegral_mul_rpow_le_rpow_mul_lintegral {Y : Type*} [MeasurableSpace Y]
    {ν : Measure Y} {k G : Y → ℝ≥0∞} (hk : Measurable k) (hG : Measurable G) {p : ℝ}
    (hp : 1 ≤ p) :
    (∫⁻ y, k y * G y ∂ν) ^ p ≤ (∫⁻ y, k y ∂ν) ^ (p - 1) * ∫⁻ y, k y * G y ^ p ∂ν := by
  rcases hp.eq_or_lt with rfl | hp1
  · simp
  · have hpq : p.HolderConjugate (Real.conjExponent p) := Real.HolderConjugate.conjExponent hp1
    set q := Real.conjExponent p with hq
    have hp0 : 0 ≤ p := hpq.nonneg
    have h1 : ∀ y, k y * G y = (k y ^ (1 / p) * G y) * k y ^ (1 / q) := by
      intro y
      have : k y = k y ^ (1 / p) * k y ^ (1 / q) := by
        rw [← ENNReal.rpow_add_of_nonneg _ _ hpq.one_div_nonneg hpq.symm.one_div_nonneg,
          hpq.one_div_add_one_div, one_div_one, ENNReal.rpow_one]
      conv_lhs => rw [this]
      ring
    have h2 : ∀ y, (k y ^ (1 / p) * G y) ^ p = k y * G y ^ p := by
      intro y
      rw [ENNReal.mul_rpow_of_nonneg _ _ hp0, ← ENNReal.rpow_mul, one_div,
        inv_mul_cancel₀ hpq.ne_zero, ENNReal.rpow_one]
    have h3 : ∀ y, (k y ^ (1 / q)) ^ q = k y := by
      intro y
      rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hpq.symm.ne_zero, ENNReal.rpow_one]
    have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq ν hpq (f := fun y => k y ^ (1 / p) * G y)
      (g := fun y => k y ^ (1 / q)) (by fun_prop) (by fun_prop)
    simp only [Pi.mul_apply, h2, h3, ← h1] at hH
    calc (∫⁻ y, k y * G y ∂ν) ^ p
        ≤ ((∫⁻ y, k y * G y ^ p ∂ν) ^ (1 / p) * (∫⁻ y, k y ∂ν) ^ (1 / q)) ^ p :=
          ENNReal.rpow_le_rpow hH hp0
      _ = (∫⁻ y, k y ∂ν) ^ (p - 1) * ∫⁻ y, k y * G y ^ p ∂ν := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp0, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, one_div,
          inv_mul_cancel₀ hpq.ne_zero, ENNReal.rpow_one, mul_comm, one_div, inv_mul_eq_div,
          hpq.div_conj_eq_sub_one]

/-- **Schur's test**, in the form `∫ (∫ K G)^p ≤ a^(p-1) b ∫ G^p`. -/
theorem lintegral_rpow_lintegral_mul_le {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
    {K : X → Y → ℝ≥0∞} (hK : Measurable (Function.uncurry K)) {G : Y → ℝ≥0∞}
    (hG : Measurable G) {a b : ℝ≥0∞} (ha : ∀ x, ∫⁻ y, K x y ∂ν ≤ a)
    (hb : ∀ y, ∫⁻ x, K x y ∂μ ≤ b) {p : ℝ} (hp : 1 ≤ p) :
    ∫⁻ x, (∫⁻ y, K x y * G y ∂ν) ^ p ∂μ ≤ a ^ (p - 1) * b * ∫⁻ y, G y ^ p ∂ν := by
  have hp1 : 0 ≤ p - 1 := sub_nonneg.2 hp
  have hKx : ∀ x, Measurable (K x) := fun x => hK.of_uncurry_left
  have hKy : ∀ y, Measurable (fun x => K x y) := fun y => hK.of_uncurry_right
  have hGp : Measurable (fun y => G y ^ p) := hG.pow_const p
  have hprod : Measurable (Function.uncurry fun x y => K x y * G y ^ p) := by
    have : Measurable (fun z : X × Y => G z.2 ^ p) := hGp.comp measurable_snd
    exact hK.mul this
  have hrow : Measurable (fun x => ∫⁻ y, K x y * G y ^ p ∂ν) :=
    hprod.lintegral_prod_right'
  calc ∫⁻ x, (∫⁻ y, K x y * G y ∂ν) ^ p ∂μ
      ≤ ∫⁻ x, a ^ (p - 1) * ∫⁻ y, K x y * G y ^ p ∂ν ∂μ := by
        refine lintegral_mono fun x => ?_
        refine (lintegral_mul_rpow_le_rpow_mul_lintegral (hKx x) hG hp).trans ?_
        exact mul_le_mul_left (ENNReal.rpow_le_rpow (ha x) hp1) _
    _ = a ^ (p - 1) * ∫⁻ x, ∫⁻ y, K x y * G y ^ p ∂ν ∂μ := lintegral_const_mul _ hrow
    _ = a ^ (p - 1) * ∫⁻ y, ∫⁻ x, K x y * G y ^ p ∂μ ∂ν := by
        rw [lintegral_lintegral_swap hprod.aemeasurable]
    _ = a ^ (p - 1) * ∫⁻ y, (∫⁻ x, K x y ∂μ) * G y ^ p ∂ν := by
        congr 1
        refine lintegral_congr fun y => ?_
        exact lintegral_mul_const _ (hKy y)
    _ ≤ a ^ (p - 1) * ∫⁻ y, b * G y ^ p ∂ν := by
        refine mul_le_mul_right (lintegral_mono fun y => ?_) _
        exact mul_le_mul_left (hb y) _
    _ = a ^ (p - 1) * b * ∫⁻ y, G y ^ p ∂ν := by
        rw [lintegral_const_mul _ hGp, mul_assoc]

/-- Schur's test with a common constant `c`, in `∫⁻` form: if `F ≤ ∫⁻ K G` pointwise, then
`∫⁻ F^p ≤ c^p ∫⁻ G^p`. No measurability of `F` is needed. -/
theorem lintegral_rpow_le_of_le_lintegral_kernel {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
    {K : X → Y → ℝ≥0∞} (hK : Measurable (Function.uncurry K)) {G : Y → ℝ≥0∞}
    (hG : Measurable G) {c : ℝ≥0∞} (ha : ∀ x, ∫⁻ y, K x y ∂ν ≤ c)
    (hb : ∀ y, ∫⁻ x, K x y ∂μ ≤ c) {F : X → ℝ≥0∞} (hF : ∀ x, F x ≤ ∫⁻ y, K x y * G y ∂ν)
    {p : ℝ} (hp : 1 ≤ p) :
    ∫⁻ x, F x ^ p ∂μ ≤ c ^ p * ∫⁻ y, G y ^ p ∂ν := by
  have hp0 : 0 ≤ p := by linarith
  have hp1 : 0 ≤ p - 1 := sub_nonneg.2 hp
  have hc : c ^ (p - 1) * c = c ^ p := by
    have h := ENNReal.rpow_add_of_nonneg (x := c) (p - 1) 1 hp1 zero_le_one
    rw [ENNReal.rpow_one, sub_add_cancel] at h
    exact h.symm
  calc ∫⁻ x, F x ^ p ∂μ ≤ ∫⁻ x, (∫⁻ y, K x y * G y ∂ν) ^ p ∂μ :=
        lintegral_mono fun x => ENNReal.rpow_le_rpow (hF x) hp0
    _ ≤ c ^ (p - 1) * c * ∫⁻ y, G y ^ p ∂ν := lintegral_rpow_lintegral_mul_le hK hG ha hb hp
    _ = c ^ p * ∫⁻ y, G y ^ p ∂ν := by rw [hc]

/-- Schur's test with a common constant `c`, in the form of `eLpNorm'`. No measurability of `F`
is needed. -/
theorem eLpNorm'_le_of_le_lintegral_kernel {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
    {K : X → Y → ℝ≥0∞} (hK : Measurable (Function.uncurry K)) {G : Y → ℝ≥0∞}
    (hG : Measurable G) {c : ℝ≥0∞} (ha : ∀ x, ∫⁻ y, K x y ∂ν ≤ c)
    (hb : ∀ y, ∫⁻ x, K x y ∂μ ≤ c) {F : X → ℝ≥0∞} (hF : ∀ x, F x ≤ ∫⁻ y, K x y * G y ∂ν)
    {p : ℝ} (hp : 1 ≤ p) :
    eLpNorm' F p μ ≤ c * eLpNorm' G p ν := by
  have hp0 : 0 < p := by linarith
  unfold eLpNorm'
  simp only [enorm_eq_self]
  calc (∫⁻ x, F x ^ p ∂μ) ^ (1 / p)
      ≤ (c ^ p * ∫⁻ y, G y ^ p ∂ν) ^ (1 / p) :=
        ENNReal.rpow_le_rpow (lintegral_rpow_le_of_le_lintegral_kernel hK hG ha hb hF hp)
          (by positivity)
    _ = c * (∫⁻ y, G y ^ p ∂ν) ^ (1 / p) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
          mul_one_div_cancel hp0.ne', ENNReal.rpow_one]

/-- Schur's test with a common constant `c`, in `eLpNorm` form, for an a.e. measurable `F`.

The a.e. measurability of `F` cannot be dropped: `eLpNorm` of a function that is not a.e.
strongly measurable is `⊤`, while `F` can be any function below `∫⁻ K G`. -/
theorem eLpNorm_le_of_le_lintegral_kernel_of_aemeasurable {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
    {K : X → Y → ℝ≥0∞} (hK : Measurable (Function.uncurry K)) {G : Y → ℝ≥0∞}
    (hG : Measurable G) {c : ℝ≥0∞} (ha : ∀ x, ∫⁻ y, K x y ∂ν ≤ c)
    (hb : ∀ y, ∫⁻ x, K x y ∂μ ≤ c) {F : X → ℝ≥0∞} (hFm : AEMeasurable F μ)
    (hF : ∀ x, F x ≤ ∫⁻ y, K x y * G y ∂ν) {p : ℝ} (hp : 1 ≤ p) :
    eLpNorm F (ENNReal.ofReal p) μ ≤ c * eLpNorm G (ENNReal.ofReal p) ν := by
  have hp0 : 0 < p := by linarith
  have h0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.2 hp0).ne'
  rw [eLpNorm_eq_eLpNorm' h0 ENNReal.ofReal_ne_top (aestronglyMeasurable_iff_aemeasurable.2 hFm),
    eLpNorm_eq_eLpNorm' h0 ENNReal.ofReal_ne_top hG.stronglyMeasurable.aestronglyMeasurable,
    ENNReal.toReal_ofReal hp0.le]
  exact eLpNorm'_le_of_le_lintegral_kernel hK hG ha hb hF hp

end PrimeCarleson.Proof.MswTransference
