module

public import PrimeCarleson.Frozen.CarlesonMax
public import PrimeCarleson.Frozen.SineWeight
import PrimeCarleson.Proof.AdmissibleSineWeight.UnboundedSum
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# Unboundedness of the sine-weighted maximal operator on `ℓ^p`

Second half of the Appendix A.1 lemma
(`PrimeCarleson.admissible_sineWeight_carleson_unbounded`): for `0 < α < 1` and `q₀ ≥ 3`, the
maximally modulated operator `𝒞_v` with `v(n) = 1 + α sin(2π n / q₀)` is unbounded on `ℓ^p(ℤ)`
for every `p ∈ [1, ∞]`.

Proof (Appendix A.1). On the test function `1_{[-4K, 4K]}` the
operator is at least `α log (3K + 1) - C` on `[-K, K]` (`exists_carlesonMax_lower`). Hence
`(α log (3K + 1) - C) · (2K + 1)^{1/p} ≤ ‖𝒞_v 1_{[-4K, 4K]}‖_p`, while
`‖1_{[-4K, 4K]}‖_p = (8K + 1)^{1/p} ≤ 4 (2K + 1)^{1/p}`; a bound `‖𝒞_v f‖_p ≤ κ ‖f‖_p`
would force `α log (3K + 1) - C ≤ 4 κ` for all `K`.
-/

public section

open MeasureTheory Filter Topology
open scoped ENNReal ComplexConjugate

set_option autoImplicit false

namespace PrimeCarleson.Proof

/-- `𝒞_v` is unbounded on `ℓ^p(ℤ)` for every `p ∈ [1, ∞]`, for the weight
`v(n) = 1 + α sin(2π n / q₀)` with `0 < α < 1` and `q₀ ≥ 3`. -/
theorem carlesonMax_sineWeight_unbounded (α : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1) (q₀ : ℕ)
    (hq₀ : 3 ≤ q₀) :
    ∀ p : ℝ≥0∞, 1 ≤ p → ¬ ∃ K : ℝ, ∀ f : ℤ →₀ ℂ,
      eLpNorm (carlesonMax (sineWeight α q₀) f) p Measure.count ≤
        ENNReal.ofReal K * eLpNorm (⇑f) p Measure.count := by
  intro p hp ⟨κ, hκ⟩
  obtain ⟨C, hC⟩ := exists_carlesonMax_lower α hα₀ hα₁ q₀ hq₀
  have hp0 : p ≠ 0 := fun h => by simp [h] at hp
  -- the exponent `1 / p.toReal` lies in `[0, 1]`
  have hr0 : 0 ≤ 1 / p.toReal := by positivity
  have hr1 : 1 / p.toReal ≤ 1 := by
    by_cases hpt : p = ∞
    · simp [hpt]
    · have : (1 : ℝ) ≤ p.toReal := by
        have := ENNReal.toReal_mono hpt hp
        simpa using this
      rw [div_le_one (by linarith)]
      exact this
  have key : ∀ K : ℕ, 1 ≤ K →
      ENNReal.ofReal (α * Real.log (3 * K + 1) - C) ≤ 4 * ENNReal.ofReal κ := by
    intro K hK
    set s : Finset ℤ := Finset.Icc (-(K : ℤ)) K with hs
    set s' : Finset ℤ := Finset.Icc (-((4 * K : ℕ) : ℤ)) ((4 * K : ℕ) : ℤ) with hs'
    set c : ℝ≥0∞ := ENNReal.ofReal (α * Real.log (3 * K + 1) - C) with hc
    have hcount : Measure.count (s : Set ℤ) = (2 * K + 1 : ℕ) := by
      rw [Measure.count_apply_finset, hs, Int.card_Icc]
      congr 1
      omega
    have hcount' : Measure.count (s' : Set ℤ) = (8 * K + 1 : ℕ) := by
      rw [Measure.count_apply_finset, hs', Int.card_Icc]
      congr 1
      push_cast
      omega
    have hs0 : Measure.count (s : Set ℤ) ≠ 0 := by
      rw [hcount]; simp
    have hs'0 : Measure.count (s' : Set ℤ) ≠ 0 := by
      rw [hcount']; simp
    -- lower bound for `‖𝒞_v f‖_p`
    have hlow : c * ((2 * K + 1 : ℕ) : ℝ≥0∞) ^ (1 / p.toReal) ≤
        eLpNorm (carlesonMax (sineWeight α q₀) (unboundedTest (4 * K))) p Measure.count := by
      have h1 := eLpNorm_indicator_const' (μ := Measure.count) (p := p) (c := c)
        (s := (s : Set ℤ)) s.measurableSet.nullMeasurableSet hs0 hp0
      rw [hcount, enorm_eq_self] at h1
      rw [← h1]
      refine eLpNorm_mono_enorm (AEStronglyMeasurable.of_discrete) fun x => ?_
      by_cases hx : x ∈ (s : Set ℤ)
      · rw [Set.indicator_of_mem hx, enorm_eq_self, enorm_eq_self]
        have := hx
        simp only [hs, Finset.coe_Icc, Set.mem_Icc] at this
        exact hC K hK x this.1 this.2
      · rw [Set.indicator_of_notMem hx]
        simp
    -- upper bound for `‖f‖_p`
    have hup : eLpNorm (⇑(unboundedTest (4 * K))) p Measure.count =
        ((8 * K + 1 : ℕ) : ℝ≥0∞) ^ (1 / p.toReal) := by
      have hfun : ⇑(unboundedTest (4 * K)) = (s' : Set ℤ).indicator (fun _ => (1 : ℂ)) := by
        funext n
        rw [unboundedTest_apply, Set.indicator_apply]
        simp [hs']
      rw [hfun, eLpNorm_indicator_const' s'.measurableSet.nullMeasurableSet hs'0 hp0, hcount']
      simp
    have hmain := hκ (unboundedTest (4 * K))
    rw [hup] at hmain
    have hrpow : ((8 * K + 1 : ℕ) : ℝ≥0∞) ^ (1 / p.toReal) ≤
        4 * ((2 * K + 1 : ℕ) : ℝ≥0∞) ^ (1 / p.toReal) := by
      have h4 : ((8 * K + 1 : ℕ) : ℝ≥0∞) ≤ 4 * ((2 * K + 1 : ℕ) : ℝ≥0∞) := by
        have : (8 * K + 1 : ℕ) ≤ 4 * (2 * K + 1) := by omega
        exact_mod_cast this
      calc ((8 * K + 1 : ℕ) : ℝ≥0∞) ^ (1 / p.toReal)
          ≤ (4 * ((2 * K + 1 : ℕ) : ℝ≥0∞)) ^ (1 / p.toReal) := ENNReal.rpow_le_rpow h4 hr0
        _ = 4 ^ (1 / p.toReal) * ((2 * K + 1 : ℕ) : ℝ≥0∞) ^ (1 / p.toReal) :=
            ENNReal.mul_rpow_of_nonneg _ _ hr0
        _ ≤ 4 * ((2 * K + 1 : ℕ) : ℝ≥0∞) ^ (1 / p.toReal) := by
            gcongr
            calc (4 : ℝ≥0∞) ^ (1 / p.toReal) ≤ 4 ^ (1 : ℝ) :=
                  ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) hr1
              _ = 4 := ENNReal.rpow_one 4
    have hpos : ((2 * K + 1 : ℕ) : ℝ≥0∞) ^ (1 / p.toReal) ≠ 0 :=
      (ENNReal.rpow_pos (Nat.cast_pos.2 (by omega)) (ENNReal.natCast_ne_top _)).ne'
    have hfin : ((2 * K + 1 : ℕ) : ℝ≥0∞) ^ (1 / p.toReal) ≠ ∞ :=
      ENNReal.rpow_ne_top_of_nonneg hr0 (ENNReal.natCast_ne_top _)
    have : c * ((2 * K + 1 : ℕ) : ℝ≥0∞) ^ (1 / p.toReal) ≤
        (4 * ENNReal.ofReal κ) * ((2 * K + 1 : ℕ) : ℝ≥0∞) ^ (1 / p.toReal) := by
      calc _ ≤ _ := hlow
        _ ≤ ENNReal.ofReal κ * ((8 * K + 1 : ℕ) : ℝ≥0∞) ^ (1 / p.toReal) := hmain
        _ ≤ ENNReal.ofReal κ * (4 * ((2 * K + 1 : ℕ) : ℝ≥0∞) ^ (1 / p.toReal)) := by gcongr
        _ = _ := by ring
    exact (ENNReal.mul_le_mul_iff_left hpos hfin).1 this
  -- choose `K` large enough that the logarithmic lower bound exceeds `4 |κ|`
  set R : ℝ := (C + 4 * |κ|) / α with hR
  set K : ℕ := ⌈Real.exp R⌉₊ + 1 with hK
  have hK1 : 1 ≤ K := by omega
  have hlog : R < Real.log (3 * K + 1) := by
    have hKe : Real.exp R ≤ K := by
      have := Nat.le_ceil (Real.exp R)
      rw [hK]; push_cast; linarith
    have hK0 : (0 : ℝ) ≤ K := by positivity
    rw [Real.lt_log_iff_exp_lt (by positivity)]
    linarith
  have hlt : C + 4 * |κ| < α * Real.log (3 * K + 1) := by
    rw [hR, div_lt_iff₀ hα₀] at hlog
    linarith
  have h4 := key K hK1
  have h4' : 4 * ENNReal.ofReal κ = ENNReal.ofReal (4 * κ) := by
    rw [ENNReal.ofReal_mul (by norm_num)]
    simp
  rw [h4', ENNReal.ofReal_le_ofReal_iff'] at h4
  rcases h4 with h | h
  · linarith [le_abs_self κ]
  · linarith [abs_nonneg κ]

end PrimeCarleson.Proof
