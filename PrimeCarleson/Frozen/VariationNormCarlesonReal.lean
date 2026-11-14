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
public import PrimeCarleson.Frozen.PartialFourierIntegral
import PrimeCarleson.Proof.VariationNormCarlesonReal

/-!
# Frozen: `PrimeCarleson.variation_norm_carleson_real`

The statement as the author approved it before any proof was written; it is the only
declaration in this file.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal SchwartzMap

set_option autoImplicit false

namespace PrimeCarleson

/-- **[O+] Theorem 1.2.** For `r > 2` and `r' < p < ∞`, `𝒮` extends to a bounded operator
`L^p(ℝ) → L^p(V^r)`: there is `C_{p,r}` with
`‖ ‖𝒮[f](·, x)‖_{V^r_ξ(ℝ)} ‖_{L^p(dx)} ≤ C_{p,r} ‖f‖_{L^p}` for every Schwartz function `f`. -/
theorem variation_norm_carleson_real :
    ∀ r : ℝ, 2 < r → ∀ p : ℝ, r / (r - 1) < p → ∃ C : ℝ, ∀ f : 𝓢(ℝ, ℂ),
      eLpNorm (fun x => rVariationOn r Set.univ (fun ξ => partialFourierIntegral f ξ x))
          (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C * eLpNorm (⇑f) (ENNReal.ofReal p) volume :=
  by exact PrimeCarleson.Proof.variation_norm_carleson_real

end PrimeCarleson
