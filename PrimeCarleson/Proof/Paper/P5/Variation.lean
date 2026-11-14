module

public import Mathlib.Analysis.BoundedVariation
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Total variation of `C¹` functions on `ℝ`

Tools for the uniform bounded variation of the multiplier of `K_Q` (main paper `s:red`, L1694–L1695,
and `p:global-shell-var`, L2028–L2029) and for the error multiplier of the `K_Q`-replacement
(`p:red-var`, L1476–L1483):

* `eVariationOn_le_integral`: a `C¹` function `f : ℝ → ℂ` with integrable derivative has total
  variation `eVariationOn f univ ≤ ∫ ‖f'‖` (fundamental theorem of calculus on each interval of
  a monotone partition);
* `eVariationOn_le_setIntegral`: the same on any interval `s` (closed, or a half-line);
* `norm_le_half_integral`: if moreover `f → 0` at `±∞` then `‖f(β)‖ ≤ ½ ∫ ‖f'‖` for every `β`;
* `eVariationOn_le_of_forall`: the total variation of a pointwise limit is at most the limit of
  the total variations (lower semicontinuity, `eVariationOn.lowerSemicontinuous_aux`).
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper.P5

/-- The total variation of a `C¹` function on a set `s = [a, b]`-type monotone partition is at
most the integral of `‖f'‖` over the set (`s` an interval `Set.OrdConnected`). -/
theorem eVariationOn_le_setIntegral {f f' : ℝ → ℂ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hc : Continuous f') {s : Set ℝ} (hs : s.OrdConnected) (hint : IntegrableOn f' s) :
    eVariationOn f s ≤ ENNReal.ofReal (∫ x in s, ‖f' x‖) := by
  unfold eVariationOn
  refine iSup_le fun p => ?_
  obtain ⟨n, ⟨u, um, us⟩⟩ := p
  have h1 : ∀ i, edist (f (u (i + 1))) (f (u i)) ≤
      ENNReal.ofReal (∫ x in u i..u (i + 1), ‖f' x‖) := by
    intro i
    have hle := um (Nat.le_succ i)
    rw [edist_dist, dist_eq_norm]
    apply ENNReal.ofReal_le_ofReal
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := f) (f' := f') (a := u i)
      (b := u (i + 1)) (fun x _ => hf x) (hc.intervalIntegrable _ _)
    rw [← this]
    exact intervalIntegral.norm_integral_le_integral_norm hle
  calc ∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))
      ≤ ∑ i ∈ Finset.range n, ENNReal.ofReal (∫ x in u i..u (i + 1), ‖f' x‖) :=
        Finset.sum_le_sum fun i _ => h1 i
    _ = ENNReal.ofReal (∑ i ∈ Finset.range n, ∫ x in u i..u (i + 1), ‖f' x‖) :=
        (ENNReal.ofReal_sum_of_nonneg fun i _ =>
          intervalIntegral.integral_nonneg (um (Nat.le_succ i)) fun x _ => norm_nonneg _).symm
    _ = ENNReal.ofReal (∫ x in u 0..u n, ‖f' x‖) := by
        rw [intervalIntegral.sum_integral_adjacent_intervals
          (fun k _ => hc.norm.intervalIntegrable _ _)]
    _ ≤ ENNReal.ofReal (∫ x in s, ‖f' x‖) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [intervalIntegral.integral_of_le (um (Nat.zero_le n))]
        refine setIntegral_mono_set hint.norm (Eventually.of_forall fun _ => norm_nonneg _) ?_
        have h0 := us 0
        have hn := us n
        have : Set.Ioc (u 0) (u n) ⊆ Set.Icc (u 0) (u n) := Set.Ioc_subset_Icc_self
        exact (this.trans (hs.out h0 hn)).eventuallyLE

/-- The total variation of a `C¹` function on `ℝ`: `V(f) ≤ ∫ ‖f'‖`. -/
theorem eVariationOn_le_integral {f f' : ℝ → ℂ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hc : Continuous f') (hint : Integrable f') :
    eVariationOn f Set.univ ≤ ENNReal.ofReal (∫ x, ‖f' x‖) := by
  have := eVariationOn_le_setIntegral hf hc (Set.ordConnected_univ) hint.integrableOn
  simpa using this

/-- If `f → 0` at `±∞` and `f'` is integrable, `‖f(β)‖ ≤ ½ ∫ ‖f'‖`. -/
theorem norm_le_half_integral {f f' : ℝ → ℂ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (_hc : Continuous f') (hint : Integrable f')
    (h1 : Tendsto f atTop (𝓝 0)) (h2 : Tendsto f atBot (𝓝 0)) (β : ℝ) :
    ‖f β‖ ≤ (∫ x, ‖f' x‖) / 2 := by
  have hcf : Continuous f := continuous_iff_continuousAt.2 fun x => (hf x).continuousAt
  have hR := integral_Ioi_of_hasDerivAt_of_tendsto (a := β) hcf.continuousWithinAt
    (fun x _ => hf x) hint.integrableOn h1
  have hL := integral_Iic_of_hasDerivAt_of_tendsto (a := β) hcf.continuousWithinAt
    (fun x _ => hf x) hint.integrableOn h2
  have bR : ‖f β‖ ≤ ∫ x in Set.Ioi β, ‖f' x‖ := by
    have := norm_integral_le_integral_norm (μ := volume.restrict (Set.Ioi β)) f'
    rw [hR, zero_sub, norm_neg] at this
    exact this
  have bL : ‖f β‖ ≤ ∫ x in Set.Iic β, ‖f' x‖ := by
    have := norm_integral_le_integral_norm (μ := volume.restrict (Set.Iic β)) f'
    rw [hL, sub_zero] at this
    exact this
  have hsum := intervalIntegral.integral_Iic_add_Ioi (b := β)
    hint.norm.integrableOn hint.norm.integrableOn
  linarith

/-- Lower semicontinuity: if `F n → f` pointwise and `V(F n) ≤ C` for all `n`, then `V(f) ≤ C`. -/
theorem eVariationOn_le_of_forall {F : ℕ → ℝ → ℂ} {f : ℝ → ℂ} {C : ℝ≥0∞}
    (hF : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (f x)))
    (hC : ∀ n, eVariationOn (F n) Set.univ ≤ C) : eVariationOn f Set.univ ≤ C := by
  by_contra h
  rw [not_le] at h
  have := eVariationOn.lowerSemicontinuous_aux (p := atTop) (s := Set.univ) (F := F) (f := f)
    (fun x _ => hF x) h
  obtain ⟨n, hn⟩ := this.exists
  exact absurd (hC n) (not_le.2 hn)

end PrimeCarleson.Proof.Paper.P5
