/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Linear/RealReducedFastKernel.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.ReducedNativeFactorization
@[expose] public section

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)
  (W : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))

theorem reducedSquareRealFastRelative_action_mem (hw : ∀ i, 0 < w i)
    {u : ℝ ⊗[ℚ] F.quotientTop.PolynomialSymbol w}
    (hu : u ∈ realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra w W))
    {v : ℝ ⊗[ℚ] F.squareFiltration.quotientTop.PolynomialSymbol w}
    (hv : v ∈ (F.reducedSquareFastRelativeSubmodule w W).baseChange ℝ) :
    ⁅(F.reducedSquareDiagonalSymbolMap w).toLinearMap.baseChange ℝ u, v⁆ ∈
      (F.reducedSquareFastRelativeSubmodule w W).baseChange ℝ := by
  let P := (F.reducedSquareFastDiagonalSubalgebra w W).toSubmodule
  let K := F.reducedSquareFastRelativeSubmodule w W
  let d := (F.reducedSquareDiagonalSymbolMap w).toLinearMap
  have hu' : d.baseChange ℝ u ∈ (P.map d).baseChange ℝ := by
    rw [realification_map]
    exact ⟨u, hu, rfl⟩
  have hclosed : ∀ x ∈ P.map d, ∀ y ∈ K, ⁅x, y⁆ ∈ K := by
    rintro x ⟨y, hy, rfl⟩ z hz
    exact F.reducedSquareFastRelative_action_mem w W hw hy hz
  exact lie_mem_real_baseChange (P.map d) K K hclosed hu' hv

end Erdos3.NilpotentLieFiltration

end

end OAI
