module

public import PrimeCarleson.Proof.MswTransference.Variation
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Minkowski's integral inequality for the `r`-variation

Minkowski's integral inequality for the variation norm, a standard result, used in the proof of
`treeestimatelargeintervals` ([O+] L2361-L2370, where
`(e_T ψ_k) * G (x) = ∫ (e_T ψ_{C + log₂|J|})(x - y) ((e_T ψ_k) * G')(y) dy` is a mollification of
a family and its `V^r_k` norm is bounded by the integral of the `V^r_k` norms against
`|ψ_{C + log₂ |J|}|`).

The statement uses the `PrimeCarleson.rVariationOn r S` (`S ⊆ ℝ` the index set, any set, in
particular the image of `ℤ`, `ℕ` or a finite set) of a family `t ↦ a t y` of complex numbers:

`V^r_{t ∈ S}(∫ a_t(y) w(y) dy) ≤ ∫ V^r_{t ∈ S}(a_t(y)) ‖w(y)‖ dy`  for `1 ≤ r`,

proved in `PrimeCarleson.Proof.MswTransference.rVariationOn_integral_le` (Minkowski's inequality
in `ℓ^r` applied to chains, then the supremum over chains).  Here it is restated in the form the
applications need: the families `a_t` are a.e. strongly measurable and bounded for `t ∈ S`, and
`w` is integrable (`rVariationOn_integral_le_of_bounded`); for a convolution kernel
`w(y) = ψ(x - y)` with `ψ` integrable (`rVariationOn_integral_sub_le`).  The right-hand side is a
lower Lebesgue integral in `ℝ≥0∞`
(no measurability of `y ↦ V^r(a · y)` is needed).
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Common

open PrimeCarleson

/-- **Minkowski's integral inequality for the `r`-variation**: for `1 ≤ r`, an index set `S ⊆ ℝ`,
families `a_t` (`t ∈ S`) a.e. strongly measurable and bounded, and `w` integrable,
`V^r_{t ∈ S}(∫ a_t w) ≤ ∫ V^r_{t ∈ S}(a_t(y)) ‖w(y)‖ₑ dy`. -/
theorem rVariationOn_integral_le_of_bounded {r : ℝ} (hr : 1 ≤ r) {S : Set ℝ} {α : Type*}
    [MeasurableSpace α] {μ : Measure α} (a : ℝ → α → ℂ) (w : α → ℂ)
    (ha : ∀ t ∈ S, AEStronglyMeasurable (a t) μ) (hb : ∀ t ∈ S, ∃ C : ℝ, ∀ y, ‖a t y‖ ≤ C)
    (hw : Integrable w μ) :
    PrimeCarleson.rVariationOn r S (fun t => ∫ y, a t y * w y ∂μ) ≤
      ∫⁻ y, PrimeCarleson.rVariationOn r S (fun t => a t y) * ‖w y‖ₑ ∂μ := by
  refine PrimeCarleson.Proof.MswTransference.rVariationOn_integral_le hr a w fun t ht => ?_
  obtain ⟨C, hC⟩ := hb t ht
  exact hw.bdd_mul (ha t ht) (Filter.Eventually.of_forall hC)

/-- Minkowski's integral inequality for the `r`-variation of a mollified family, with the
convolution kernel `w(y) = ψ(x - y)` on `ℝ` (the form of L2361-L2370 of `osttw0710.tex`):
`V^r_{t ∈ S}(∫ a_t(y) ψ(x - y) dy) ≤ ∫ V^r_{t ∈ S}(a_t(y)) ‖ψ(x - y)‖ₑ dy`. -/
theorem rVariationOn_integral_sub_le {r : ℝ} (hr : 1 ≤ r) {S : Set ℝ} (a : ℝ → ℝ → ℂ)
    (ψ : ℝ → ℂ) (x : ℝ) (ha : ∀ t ∈ S, AEStronglyMeasurable (a t) volume)
    (hb : ∀ t ∈ S, ∃ C : ℝ, ∀ y, ‖a t y‖ ≤ C) (hψ : Integrable ψ volume) :
    PrimeCarleson.rVariationOn r S (fun t => ∫ y, a t y * ψ (x - y)) ≤
      ∫⁻ y, PrimeCarleson.rVariationOn r S (fun t => a t y) * ‖ψ (x - y)‖ₑ := by
  have hw : Integrable (fun y => ψ (x - y)) volume := hψ.comp_sub_left x
  exact rVariationOn_integral_le_of_bounded hr a (fun y => ψ (x - y)) ha hb hw

end PrimeCarleson.Proof.Common
