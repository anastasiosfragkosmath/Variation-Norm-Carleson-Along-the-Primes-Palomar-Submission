/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Fourier/DilationFrequencyPhase.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.NativeDilationObservable
@[expose] public section

namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

theorem NilpotentLieFiltration.realDilationPair_frequency_phase
    {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (q : ℤ) (η : L →ₗ[ℚ] ℚ)
    (g : (F.dilationPairFiltration (q : ℚ)).realification.Group)
    (hg : g ∈ (F.dilationPairFiltration (q : ℚ)).realification.subgroup s) :
    (realifyFunctional η (F.realDilationPairProjection (q : ℚ) 0 g).coord : CircleFourier.Circle) =
      (q ^ s) • (realifyFunctional η
        (F.realDilationPairProjection (q : ℚ) 1 g).coord : CircleFourier.Circle) := by
  rw [F.realDilationPair_top_group_relation q g hg, NilpotentLieBCHGroup.coord_zpow,
    map_zsmul, AddCircle.coe_zsmul]

end Erdos3

end

end OAI
