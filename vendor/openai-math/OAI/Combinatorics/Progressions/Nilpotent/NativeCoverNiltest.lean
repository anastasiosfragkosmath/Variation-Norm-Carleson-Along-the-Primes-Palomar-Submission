/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Nilpotent/NativeCoverNiltest.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Linear.SplitCoverProjection
@[expose] public section

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}
  (T : D.Niltest w) (Λ : Subgroup D.filtration.Group) (m : ℕ) (hm : 0 < m)
  (hin : scaledIntegerGrid m ⊆ bchSubgroupCoordinates D.basis Λ)
  (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid m) (hΛ : Λ ≤ D.lattice)

noncomputable def onSublattice : (D.withLattice Λ m hm hin hout).Niltest w where
  orbit := T.orbit
  observable := T.observable ∘ sublatticeProjection D (D.withLattice Λ m hm hin hout) hΛ
  normBound := T.normBound
  lipBound := T.lipBound
  norm_le _ := T.norm_le _
  lipschitz := sublattice_pullback_lipschitz D (D.withLattice Λ m hm hin hout) hΛ rfl
    T.observable T.lipschitz

theorem onSublattice_complexity {p : ℝ} (hT : T.ComplexityLE p)
    (hD : (D.withLattice Λ m hm hin hout).GeometryComplexityLE p) :
    (T.onSublattice Λ m hm hin hout hΛ).ComplexityLE p := ⟨hD, hT.2⟩

theorem onSublattice_unit_interval (hT : T.UnitIntervalValued) :
    (T.onSublattice Λ m hm hin hout hΛ).UnitIntervalValued := fun _ => hT _

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open NilpotentLieFiltration
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}
    (T : D.Niltest w) (E : RationalFilteredNilmanifold L s d)
    (hfil : E.filtration = D.filtration) (hb : E.basis = D.basis)
    (hΛ : E.lattice ≤ D.lattice)

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI
