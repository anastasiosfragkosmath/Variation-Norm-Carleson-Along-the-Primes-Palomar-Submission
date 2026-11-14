/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Lattices/FiniteLatticeBasis.lean
Changes: Lean module/public-import conversion only.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import Mathlib.Algebra.Module.ZLattice.Basic
@[expose] public section

namespace OAI

section

namespace Erdos3

noncomputable def finiteLatticeBasis {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    Module.Basis (Fin (Module.finrank ℝ E)) ℤ Λ :=
  (Module.Free.chooseBasis ℤ Λ).reindex (Fintype.equivOfCardEq
    (by rw [← Module.finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ, Fintype.card_fin]))

end Erdos3

end

end OAI
