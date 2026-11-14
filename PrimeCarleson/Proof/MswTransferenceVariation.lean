module

public import PrimeCarleson.Frozen.RVariationOn
public import PrimeCarleson.Frozen.MultiplierOp
public import PrimeCarleson.Frozen.MultiplierOpDis
public import PrimeCarleson.Proof.MswTransference.Extension
public import PrimeCarleson.Proof.MswTransference.Bounds

/-!
# Provider for `PrimeCarleson.msw_transference_variation`

Proves the statement under the separate name
`PrimeCarleson.Proof.msw_transference_variation`.
Only `PrimeCarleson.Frozen.MswTransferenceVariation` imports this module.

Route: extend `f` by the Schwartz cutoff `Φ` (`MswTransference.extend`). Then `T(f_ext)` restricted
to `ℤ` is `T_dis f`, so
`‖V^r T_dis f‖_{ℓ^p} ≤ A₁ ‖V^r T(f_ext)‖_{L^p} ≤ A₁ A ‖f_ext‖_{L^p} ≤ A₁² A ‖f‖_{ℓ^p}`
with `A₁ = cutoffConst`, independent of `p`, `r`, `T`, `m`, `A` and `f`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal SchwartzMap

namespace PrimeCarleson.Proof

open MswTransference

/-- [MSW] Proposition 2.1 for `r`-variation norms, with the constant `A₁²`. -/
theorem msw_transference_variation :
    ∃ C : ℝ, ∀ p : ℝ, 1 ≤ p → ∀ r : ℝ, 1 ≤ r →
      ∀ (T : Finset ℝ) (m : ℝ → ℝ → ℂ) (A : ℝ),
        (∀ lam ∈ T, Measurable (m lam)) →
        (∀ lam ∈ T, ∃ M : ℝ, ∀ ξ, ‖m lam ξ‖ ≤ M) →
        (∀ lam ∈ T, Function.support (m lam) ⊆ Set.Ioc (-1 / 2) (1 / 2)) →
        (∀ F : 𝓢(ℝ, ℂ),
          eLpNorm (fun x => rVariationOn r T (fun lam => multiplierOp (m lam) F x))
              (ENNReal.ofReal p) volume ≤
            ENNReal.ofReal A * eLpNorm (⇑F) (ENNReal.ofReal p) volume) →
        ∀ f : ℤ →₀ ℂ,
          eLpNorm (fun n => rVariationOn r T (fun lam => multiplierOpDis (m lam) f n))
              (ENNReal.ofReal p) Measure.count ≤
            ENNReal.ofReal (C * A) * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
  refine ⟨cutoffConst.toReal ^ 2, ?_⟩
  intro p hp r hr T m A hmeas hbdd hsupp hA f
  set H : ℝ → ℝ → ℂ := fun lam => multiplierOp (m lam) (extend f) with hH
  have hdis : (fun n : ℤ => rVariationOn r T (fun lam => multiplierOpDis (m lam) f n)) =
      fun n : ℤ => rVariationOn r T (fun lam => H lam n) := by
    funext n
    exact rVariationOn_congr fun lam hlam =>
      (multiplierOp_extend_intCast (hmeas lam hlam) (hbdd lam hlam) (hsupp lam hlam) f n).symm
  have hsample := eLpNorm_rVariationOn_sample_le hr hp T H
    (fun lam hlam =>
      continuous_multiplierOp_extend (hmeas lam hlam) (hbdd lam hlam) (hsupp lam hlam) f)
    (fun lam hlam x =>
      integrable_multiplierOp_extend_mul (hmeas lam hlam) (hbdd lam hlam) (hsupp lam hlam) f x)
    (fun lam hlam n =>
      multiplierOp_extend_eq_integral (hmeas lam hlam) (hbdd lam hlam) (hsupp lam hlam) f n)
  have hC : ENNReal.ofReal (cutoffConst.toReal ^ 2 * A) =
      cutoffConst * cutoffConst * ENNReal.ofReal A := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal cutoffConst_lt_top.ne, pow_two]
  rw [hdis, hC]
  calc _ ≤ cutoffConst *
        eLpNorm (fun x => rVariationOn r T (fun t => H t x)) (ENNReal.ofReal p) volume :=
        hsample
    _ ≤ cutoffConst * (ENNReal.ofReal A * eLpNorm (⇑(extend f)) (ENNReal.ofReal p) volume) := by
        gcongr
        exact hA (extend f)
    _ ≤ cutoffConst * (ENNReal.ofReal A *
          (cutoffConst * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count)) := by
        gcongr
        exact eLpNorm_extend_le hp f
    _ = cutoffConst * cutoffConst * ENNReal.ofReal A *
          eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by ring

end PrimeCarleson.Proof
