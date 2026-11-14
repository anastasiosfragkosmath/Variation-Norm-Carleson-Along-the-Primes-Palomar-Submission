/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Lattices/RationalLatticeFunctional.lean
Changes: Lean module/public-import conversion only.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.NativeCentralSeed
@[expose] public section

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d)

theorem realLattice_functional_integral (η : L →ₗ[ℚ] ℚ)
    (hη : ∀ g : D.filtration.Group, g ∈ D.lattice → ∃ n : ℤ, η g.coord = n)
    (z : D.RealGroup) (hz : z ∈ D.realLattice) :
    ∃ n : ℤ, realifyFunctional η z.coord = n := by
  obtain ⟨g, hg, rfl⟩ := hz
  obtain ⟨n, hn⟩ := hη g hg
  refine ⟨n, ?_⟩
  change realifyFunctional η ((1 : ℝ) ⊗ₜ[ℚ] g.coord) = _
  rw [realifyFunctional_tmul, one_mul, hn, Rat.cast_intCast]

end Erdos3.RationalFilteredNilmanifold

end

end OAI
