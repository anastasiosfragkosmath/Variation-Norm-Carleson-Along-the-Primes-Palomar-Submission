/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/NativeEqualDimension.lean
Changes: Lean module/public-import conversion only.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Nilpotent.IdealInvariantNiltestBudget
@[expose] public section

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d k : ℕ}

def castDimension (D : RationalFilteredNilmanifold L s d) (h : d = k) :
    RationalFilteredNilmanifold L s k := h ▸ D

theorem castDimension_geometry (D : RationalFilteredNilmanifold L s d) (h : d = k) (p : ℝ) :
    (D.castDimension h).GeometryComplexityLE p ↔ D.GeometryComplexityLE p := by
  cases h
  rfl

namespace Niltest

variable {σ : Type*} {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

noncomputable def castDimension (T : D.Niltest w) (h : d = k) : (D.castDimension h).Niltest w := by
  cases h
  exact T

theorem castDimension_normBound (T : D.Niltest w) (h : d = k) :
    (T.castDimension h).normBound = T.normBound := by
  cases h
  rfl

theorem castDimension_eval (T : D.Niltest w) (h : d = k) (x : σ → ℤ) :
    (T.castDimension h).eval x = T.eval x := by
  cases h
  rfl

theorem castDimension_complexity (T : D.Niltest w) (h : d = k) (p : ℝ) :
    (T.castDimension h).ComplexityLE p ↔ T.ComplexityLE p := by
  cases h
  rfl

theorem castDimension_unit_interval (T : D.Niltest w) (h : d = k) :
    (T.castDimension h).UnitIntervalValued ↔ T.UnitIntervalValued := by
  cases h
  rfl

end Niltest
end Erdos3.RationalFilteredNilmanifold

end

end OAI
