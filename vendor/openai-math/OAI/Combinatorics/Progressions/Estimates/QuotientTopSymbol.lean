/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/QuotientTopSymbol.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Polynomial.RealAdaptedPolynomialGroup
@[expose] public section

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)

noncomputable def quotientTopPolynomialMap : F.adaptedLieSubalgebra w →ₗ⁅ℚ⁆
    F.quotientTop.adaptedLieSubalgebra w :=
  F.filteredPolynomialMap F.quotientTop (lieQuotientMap (F.layerIdeal (s + 1)))
    (fun _ _ hx => F.quotientLie_mem _ le_rfl hx) w

noncomputable def quotientTopSymbolMap : F.PolynomialSymbol w →ₗ⁅ℚ⁆
    F.quotientTop.PolynomialSymbol w :=
  F.filteredPolynomialSymbolMap F.quotientTop (lieQuotientMap (F.layerIdeal (s + 1)))
    (fun _ _ hx => F.quotientLie_mem _ le_rfl hx) w

@[simp] theorem quotientTopSymbolMap_symbol (p : F.adaptedLieSubalgebra w) :
    F.quotientTopSymbolMap w (F.polynomialSymbolMap w p) =
      F.quotientTop.polynomialSymbolMap w (F.quotientTopPolynomialMap w p) := rfl

theorem quotientTopSymbolMap_surjective : Function.Surjective (F.quotientTopSymbolMap w) :=
  F.filteredPolynomialSymbolMap_surjective _ _ _ w (fun _ _ hy => hy)

end Erdos3.NilpotentLieFiltration

end

end OAI
