module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.Data.Nat.Totient
public import Mathlib.Algebra.Ring.Periodic
public import PrimeCarleson.Frozen.Exp
public import PrimeCarleson.Frozen.GowersNormInterval
public import PrimeCarleson.Frozen.RVariationOn
public import PrimeCarleson.Frozen.MultiplierOp
public import PrimeCarleson.Frozen.MultiplierOpDis
import PrimeCarleson.Proof.MswTransferenceVariation

/-!
# Frozen: `PrimeCarleson.msw_transference_variation`

The statement as the author approved it before any proof was written; it is the only
declaration in this file.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal SchwartzMap

set_option autoImplicit false

namespace PrimeCarleson

/-- **[MSW] Proposition 2.1, for `r`-variation norms** (`d = 1`, `B₁ = ℂ`, `B₂ = ℂ^T` modulo
constants with the `V^r` norm, `1 ≤ p < ∞`). There is an absolute constant `C` such that
for every finite `T ⊂ ℝ` and every family of bounded measurable multipliers `m_λ`
(`λ ∈ T`) supported in `(-1/2, 1/2]`: if `‖V^r(T_{m_λ} F : λ ∈ T)‖_{L^p(ℝ)} ≤ A ‖F‖_{L^p(ℝ)}`
for all Schwartz `F`, then `‖V^r(T_{dis, m_λ} f : λ ∈ T)‖_{ℓ^p(ℤ)} ≤ C A ‖f‖_{ℓ^p(ℤ)}` for all
finitely supported `f`. -/
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
            ENNReal.ofReal (C * A) * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count :=
  by exact PrimeCarleson.Proof.msw_transference_variation

end PrimeCarleson
