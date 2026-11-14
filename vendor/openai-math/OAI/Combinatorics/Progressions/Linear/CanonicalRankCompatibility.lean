/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Linear/CanonicalRankCompatibility.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Nilpotent.DegreeRankBCH
public import OAI.Combinatorics.Progressions.Polynomial.AdaptedPolynomialSubstitution
@[expose] public section

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

theorem eq_of_layer_eq {F G : NilpotentLieFiltration L s} (h : F.layer = G.layer) : F = G := by
  cases F
  cases G
  cases h
  rfl

variable (F : NilpotentLieFiltration L s)

theorem canonicalDegreeRank_associatedDegree_eq : F.canonicalDegreeRank.associatedDegree = F :=
  eq_of_layer_eq (funext F.canonicalDegreeRank_associatedDegree_layer)

noncomputable def orbitEquivOfEq {G : NilpotentLieFiltration L s} (h : F = G)
    {σ : Type*} (w : σ → ℕ) : F.PolynomialOrbit w ≃* G.PolynomialOrbit w := by
  subst G
  exact MulEquiv.refl _

theorem orbitEquivOfEq_eval {G : NilpotentLieFiltration L s} (h : F = G)
    {σ : Type*} (w : σ → ℕ) (g : F.PolynomialOrbit w) (x : σ → ℤ) :
    G.polynomialOrbitEval w x (F.orbitEquivOfEq h w g) = F.polynomialOrbitEval w x g := by
  subst G
  rfl

end Erdos3.NilpotentLieFiltration

end

end OAI
