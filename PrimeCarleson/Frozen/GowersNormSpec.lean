module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.MeasureTheory.MeasurableSpace.Instances
public import Mathlib.Data.Finsupp.Indicator
public import Mathlib.Data.PNat.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Order.LiminfLimsup
public import PrimeCarleson.Frozen.MultDiff
public import PrimeCarleson.Frozen.GowersNorm
import PrimeCarleson.Proof.GowersNormSpec

/-!
# Frozen: `PrimeCarleson.gowersNorm_spec`

The statement as the author approved it before any proof was written; it is the only
declaration in this file.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal ComplexConjugate

set_option autoImplicit false

namespace PrimeCarleson

/-- The Gowers norm is the source object: the defining sum has finitely many nonzero terms
(so the `tsum` is the genuine sum), the norm is nonnegative, and its `2^s`-th power is the
sum `∑_{x, h₁, …, h_s} Δ_{h₁,…,h_s} f(x)` of (e;GowersDef). -/
theorem gowersNorm_spec (s : ℕ+) (f : ℤ →₀ ℂ) :
    (Function.support fun p : ℤ × (Fin s → ℤ) => multDiff s p.2 f p.1).Finite ∧
      0 ≤ gowersNorm s f ∧
      ((gowersNorm s f : ℝ) : ℂ) ^ (2 ^ (s : ℕ)) =
        ∑' p : ℤ × (Fin s → ℤ), multDiff s p.2 f p.1 :=
  by exact PrimeCarleson.Proof.gowersNorm_spec

end PrimeCarleson
