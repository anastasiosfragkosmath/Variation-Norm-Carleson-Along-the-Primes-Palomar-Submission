/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/SubmoduleSupRestriction.lean
Changes: Lean module/public-import conversion only.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import Mathlib.LinearAlgebra.Span.Basic
@[expose] public section

namespace OAI

section

namespace Erdos3

theorem submodule_comap_iSup_of_le_range {R M N : Type*} [Ring R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {I : Sort*} (f : M →ₗ[R] N) (hf : Function.Injective f)
    (P : I → Submodule R N) (hP : ∀ i, P i ≤ LinearMap.range f) :
    (⨆ i, P i).comap f = ⨆ i, (P i).comap f := by
  apply Submodule.map_injective_of_injective hf
  rw [Submodule.map_comap_eq_of_le (iSup_le hP), Submodule.map_iSup]
  exact iSup_congr (fun i => (Submodule.map_comap_eq_of_le (hP i)).symm)

end Erdos3

end

end OAI
