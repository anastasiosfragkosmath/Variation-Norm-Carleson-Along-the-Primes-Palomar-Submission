/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Lattices/RealSymbolAffine.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.SymbolFastMembership
@[expose] public section

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem realSymbolOfPolynomial_translate (hw : ∀ i, 0 < w i) (h : σ → ℚ)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (hp : F.realification.Adapted w p) :
    F.realSymbolOfPolynomial b ω hF w (translate h p) = F.realSymbolOfPolynomial b ω hF w p := by
  let q : F.realification.adaptedLieSubalgebra w :=
    ⟨p, (F.realification.mem_adaptedSubmodule w p).mpr hp⟩
  let q' : F.realification.adaptedLieSubalgebra w :=
    ⟨translate h p, (F.realification.mem_adaptedSubmodule w _).mpr
      (F.realification.adapted_translate w hw h hp)⟩
  exact (F.realSymbolOfPolynomial_eq_iff_symbolMap_eq b ω hF w q' q).mpr
    (F.realification.polynomialSymbolMap_translate w hw h q)

theorem realSymbolOfPolynomial_affine (hw : ∀ i, 0 < w i) (h : σ → ℚ) (r : ℚ)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (hp : F.realification.Adapted w p) :
    F.realSymbolOfPolynomial b ω hF w (weightedDilation w r (translate h p)) =
      F.realPolynomialSymbolDilation w r (F.realSymbolOfPolynomial b ω hF w p) := by
  rw [F.realSymbolOfPolynomial_dilation, F.realSymbolOfPolynomial_translate b ω hF w hw h p hp]

end Erdos3.NilpotentLieFiltration

end

end OAI
