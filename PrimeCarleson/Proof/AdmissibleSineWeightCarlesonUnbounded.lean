module

public import PrimeCarleson.Frozen.Admissible
public import PrimeCarleson.Frozen.SineWeight
public import PrimeCarleson.Frozen.CarlesonMax
import PrimeCarleson.Proof.AdmissibleSineWeight.Admissible
import PrimeCarleson.Proof.AdmissibleSineWeight.Unbounded

/-!
# Provider for `PrimeCarleson.admissible_sineWeight_carleson_unbounded`

Proves the statement under the separate name
`PrimeCarleson.Proof.admissible_sineWeight_carleson_unbounded`, from the two halves
`sineWeight_admissible` and `carlesonMax_sineWeight_unbounded`.
Only `PrimeCarleson.Frozen.AdmissibleSineWeightCarlesonUnbounded` imports this module.

The theorem binds `α hα₀ hα₁ q₀ hq₀` before its colon, and its proof must be the
bare assembly `by exact PrimeCarleson.Proof.admissible_sineWeight_carleson_unbounded`. So
`α` and `q₀` are implicit here and the hypotheses are filled by `by assumption` from the
theorem's context.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace PrimeCarleson.Proof

/-- The Appendix A.1 lemma: `v(n) = 1 + α sin(2πn/q₀)` is admissible, but `𝒞_v` is unbounded
on `ℓ^p` for each `1 ≤ p ≤ ∞`. -/
theorem admissible_sineWeight_carleson_unbounded {α : ℝ} {q₀ : ℕ}
    (hα₀ : 0 < α := by assumption) (hα₁ : α < 1 := by assumption)
    (hq₀ : 3 ≤ q₀ := by assumption) :
    Admissible (sineWeight α q₀) ∧
      ∀ p : ℝ≥0∞, 1 ≤ p → ¬ ∃ K : ℝ, ∀ f : ℤ →₀ ℂ,
        eLpNorm (carlesonMax (sineWeight α q₀) f) p Measure.count ≤
          ENNReal.ofReal K * eLpNorm (⇑f) p Measure.count :=
  ⟨sineWeight_admissible α hα₀ hα₁ q₀ hq₀, carlesonMax_sineWeight_unbounded α hα₀ hα₁ q₀ hq₀⟩

end PrimeCarleson.Proof
