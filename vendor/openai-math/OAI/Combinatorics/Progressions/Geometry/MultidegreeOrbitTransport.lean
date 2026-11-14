/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Geometry/MultidegreeOrbitTransport.lean
Changes: Lean module/public-import conversion only.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Polynomial.WeightedPolynomialRestriction
@[expose] public section

namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)
  {G : MultidegreeLieFiltration σ L s bound}

noncomputable def orbitEquivOfEq (h : F = G) : F.PolynomialOrbit ≃* G.PolynomialOrbit := by
  subst G
  exact MulEquiv.refl _

theorem orbitEquivOfEq_eval (h : F = G) (p : F.PolynomialOrbit) (x : σ → ℤ) :
    G.polynomialOrbitEval x (F.orbitEquivOfEq h p) = F.polynomialOrbitEval x p := by
  subst G
  rfl

end Erdos3.MultidegreeLieFiltration

end

end OAI
