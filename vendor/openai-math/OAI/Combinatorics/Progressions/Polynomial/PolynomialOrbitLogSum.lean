/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Polynomial/PolynomialOrbitLogSum.lean
Changes: Lean module/public-import conversion only.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.NativeCoveredCommonFactorization
@[expose] public section

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {F : NilpotentLieFiltration L s} {w : σ → ℕ}

noncomputable def PolynomialOrbit.logSum (g h : F.PolynomialOrbit w) : F.PolynomialOrbit w :=
  ⟨⟨g.log + h.log⟩, (F.adaptedLieSubalgebra w).add_mem g.property h.property⟩

@[simp] theorem PolynomialOrbit.logSum_log (g h : F.PolynomialOrbit w) :
    (g.logSum h).log = g.log + h.log := rfl

theorem PolynomialOrbit.logSum_normalized (g h : F.PolynomialOrbit w)
    (hg : F.polynomialOrbitEval w 0 g = 1) (hh : F.polynomialOrbitEval w 0 h = 1) :
    F.polynomialOrbitEval w 0 (g.logSum h) = 1 := by
  rw [F.polynomialOrbitEval_zero_iff_coefficient_zero] at hg hh ⊢
  simp only [logSum_log, map_add, Finsupp.add_apply, hg, hh, add_zero]

end Erdos3.NilpotentLieFiltration

end

end OAI
