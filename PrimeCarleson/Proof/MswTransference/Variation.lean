module

public import PrimeCarleson.Frozen.RVariationOn
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Elementary properties of the `r`-variation

Three facts about `PrimeCarleson.rVariationOn` used by the Magyar–Stein–Wainger transference:

* `rVariationOn_congr`: the `r`-variation over `S` only depends on the values on `S`;
* `rVariationOn_integral_le`: Minkowski's integral inequality for the `r`-variation, i.e. the
  `r`-variation of a weighted integral of a family is at most the integral of the `r`-variations;
* `measurable_rVariationOn`: for a family of continuous functions, the `r`-variation is a
  measurable function of the variable (it is lower semicontinuous).
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.MswTransference

/-- The `r`-variation is bounded by `B` once every admissible chain gives a value at most `B`. -/
theorem rVariationOn_le {r : ℝ} {S : Set ℝ} {a : ℝ → ℂ} {B : ℝ≥0∞}
    (h : ∀ (J : ℕ) (t : Fin (J + 1) → ℝ), StrictMono t → (∀ i, t i ∈ S) →
      (∑ i : Fin J, ‖a (t i.castSucc) - a (t i.succ)‖ₑ ^ r) ^ (1 / r) ≤ B) :
    rVariationOn r S a ≤ B :=
  iSup_le fun J => iSup_le fun t => iSup_le fun hm => iSup_le fun hS => h J t hm hS

/-- Every admissible chain gives a value at most the `r`-variation. -/
theorem le_rVariationOn {r : ℝ} {S : Set ℝ} {a : ℝ → ℂ} {J : ℕ} {t : Fin (J + 1) → ℝ}
    (hm : StrictMono t) (hS : ∀ i, t i ∈ S) :
    (∑ i : Fin J, ‖a (t i.castSucc) - a (t i.succ)‖ₑ ^ r) ^ (1 / r) ≤ rVariationOn r S a :=
  le_iSup₂_of_le J t <| le_iSup₂_of_le hm hS le_rfl

/-- The `r`-variation over `S` only depends on the values on `S`. -/
theorem rVariationOn_congr {r : ℝ} {S : Set ℝ} {a b : ℝ → ℂ} (h : ∀ t ∈ S, a t = b t) :
    rVariationOn r S a = rVariationOn r S b := by
  unfold rVariationOn
  refine iSup_congr fun J => iSup_congr fun t => iSup_congr fun _ => iSup_congr fun ht => ?_
  refine congrArg (· ^ (1 / r)) (Finset.sum_congr rfl fun i _ => ?_)
  rw [h _ (ht _), h _ (ht _)]

/-- For a family of continuous functions, the `r`-variation is a measurable function of the
variable: it is a supremum of continuous functions, hence lower semicontinuous. -/
theorem measurable_rVariationOn {r : ℝ} (hr : 1 ≤ r) {S : Set ℝ} {a : ℝ → ℝ → ℂ}
    (ha : ∀ t ∈ S, Continuous (a t)) :
    Measurable (fun y => rVariationOn r S (fun t => a t y)) := by
  have hr0 : 0 ≤ 1 / r := by positivity
  refine LowerSemicontinuous.measurable ?_
  unfold rVariationOn
  refine lowerSemicontinuous_iSup fun J => lowerSemicontinuous_iSup fun t =>
    lowerSemicontinuous_iSup fun _ => lowerSemicontinuous_iSup fun hS => ?_
  refine Continuous.lowerSemicontinuous ?_
  refine ENNReal.continuous_rpow_const.comp (continuous_finsetSum _ fun i _ => ?_)
  exact ENNReal.continuous_rpow_const.comp
    (((ha _ (hS _)).sub (ha _ (hS _))).enorm)

/-- **Minkowski's integral inequality** for the `r`-variation. -/
theorem rVariationOn_integral_le {r : ℝ} (hr : 1 ≤ r) {S : Set ℝ} {α : Type*}
    [MeasurableSpace α] {μ : Measure α} (a : ℝ → α → ℂ) (w : α → ℂ)
    (ha : ∀ t ∈ S, Integrable (fun y => a t y * w y) μ) :
    rVariationOn r S (fun t => ∫ y, a t y * w y ∂μ) ≤
      ∫⁻ y, rVariationOn r S (fun t => a t y) * ‖w y‖ₑ ∂μ := by
  have hr0 : 0 < r := by linarith
  have : Fact (1 ≤ ENNReal.ofReal r) := ⟨ENNReal.one_le_ofReal.2 hr⟩
  have hp : 0 < (ENNReal.ofReal r).toReal := by
    rw [ENNReal.toReal_ofReal hr0.le]
    exact hr0
  refine rVariationOn_le fun J t hm hS => ?_
  -- the vector-valued integrand
  let v : α → PiLp (ENNReal.ofReal r) (fun _ : Fin J => ℂ) := fun y =>
    WithLp.toLp _ fun i => (a (t i.castSucc) y - a (t i.succ) y) * w y
  have hvi : ∀ i, (fun y => v y i) = fun y =>
      a (t i.castSucc) y * w y - a (t i.succ) y * w y := by
    intro i
    funext y
    simp only [v, sub_mul]
  have hint : ∀ i, Integrable (fun y => v y i) μ := fun i => by
    rw [hvi i]
    exact (ha _ (hS _)).sub (ha _ (hS _))
  have hv : Integrable v μ := Integrable.of_eval_piLp hint
  have hcomp : ∀ i, (∫ y, v y ∂μ) i =
      ∫ y, a (t i.castSucc) y * w y ∂μ - ∫ y, a (t i.succ) y * w y ∂μ := by
    intro i
    rw [eval_integral_piLp hint i, hvi i, integral_sub (ha _ (hS _)) (ha _ (hS _))]
  have hnorm : ∀ x : PiLp (ENNReal.ofReal r) (fun _ : Fin J => ℂ),
      ‖x‖ₑ = (∑ i, ‖x i‖ₑ ^ r) ^ (1 / r) := by
    intro x
    rw [← edist_zero_right, PiLp.edist_eq_sum hp, ENNReal.toReal_ofReal hr0.le]
    simp only [edist_zero_right, PiLp.zero_apply]
  calc (∑ i : Fin J, ‖(∫ y, a (t i.castSucc) y * w y ∂μ) - ∫ y, a (t i.succ) y * w y ∂μ‖ₑ ^ r)
        ^ (1 / r)
      = ‖∫ y, v y ∂μ‖ₑ := by
        rw [hnorm]
        simp only [hcomp]
    _ ≤ ∫⁻ y, ‖v y‖ₑ ∂μ := enorm_integral_le_lintegral_enorm v
    _ ≤ ∫⁻ y, rVariationOn r S (fun t => a t y) * ‖w y‖ₑ ∂μ := by
        refine lintegral_mono fun y => ?_
        have hy : ‖v y‖ₑ = (∑ i : Fin J, ‖a (t i.castSucc) y - a (t i.succ) y‖ₑ ^ r) ^ (1 / r) *
            ‖w y‖ₑ := by
          rw [hnorm]
          simp only [v, enorm_mul]
          simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hr0.le]
          rw [← Finset.sum_mul, ENNReal.mul_rpow_of_nonneg _ _ (by positivity : 0 ≤ 1 / r),
            ← ENNReal.rpow_mul, mul_one_div_cancel hr0.ne', ENNReal.rpow_one]
        rw [hy]
        exact mul_le_mul_left (le_rVariationOn (a := fun t => a t y) hm hS) _

end PrimeCarleson.Proof.MswTransference
