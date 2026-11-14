/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Polynomial/ProductPolynomialMaps.lean
Changes: Lean module/public-import conversion; unneeded declarations and imports were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Linear.NativeRankQuotientOrbit
@[expose] public section

namespace OAI

section

namespace Erdos3

open Module VectorPolynomial NilpotentLieFiltration NilpotentLieBCHGroup
open scoped TensorProduct

namespace NilpotentLieFiltration

theorem piRealOrbit_projection_log {ι σ : Type*} [Fintype ι]
    {L : ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ}
    (F : ∀ i, NilpotentLieFiltration (L i) s) {w : σ → ℕ}
    (g : ∀ i, (F i).realification.PolynomialOrbit w) (a : ι) :
    VectorPolynomial.map ((realificationLieHom (liePiEval a)).toLinearMap.restrictScalars ℚ)
      (piRealOrbit F g).log = (g a).log := by
  classical
  apply coefficients.injective
  ext α
  simp only [coefficients_map, piRealOrbit, polynomialOrbitOfLog_log, map_sum,
    Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single a]
  · exact realProductSingle_projection a _
  · intro j _ hja
    exact realProductSingle_projection_ne (Ne.symm hja) _
  · simp

end NilpotentLieFiltration

namespace RationalFilteredNilmanifold

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)) (f : κ → ι)

end RationalFilteredNilmanifold
end Erdos3

end

end OAI
