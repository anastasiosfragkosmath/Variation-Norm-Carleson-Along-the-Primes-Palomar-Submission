/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/SquareSymbolRelative.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.SplitGroupRelative
public import OAI.Combinatorics.Progressions.Polynomial.SquarePolynomialCoordinates
@[expose] public section

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ) (hw : ∀ i, 0 < w i)

theorem relativeSquareSymbol_lie_eq_zero (p q : F.normalizedRelativeSubmodule w) :
    ⁅F.relativeSquareSymbolMap w hw p, F.relativeSquareSymbolMap w hw q⁆ = 0 := by
  have hpq : ⁅p.val, q.val⁆ ∈ F.shiftedPolynomialIdeal w 2 :=
    F.shiftedPolynomialIdeal_lie_mem w (i := 1) (j := 1) p.property.1 q.property.1
  have hpq0 : coefficients ⁅p.val, q.val⁆.val 0 ∈ F.layer 2 := by
    have hh := hpq 0
    change coefficients ⁅p.val, q.val⁆.val 0 ∈ F.layer (Finsupp.weight w 0 + 2) at hh
    rw [map_zero, Nat.zero_add] at hh
    exact hh
  let r : F.normalizedRelativeSubmodule w :=
    ⟨⁅p.val, q.val⁆, F.shiftedPolynomialIdeal_antitone w (by decide : 1 ≤ 2) hpq, hpq0⟩
  have he : ⁅F.relativeSquareLift w hw p, F.relativeSquareLift w hw q⁆ =
      F.relativeSquareLift w hw r := by
    apply F.square_polynomial_ext w
    · rw [LieHom.map_lie, F.squareFstPolynomialMap_relative, F.squareFstPolynomialMap_relative,
        F.squareFstPolynomialMap_relative]
    · rw [LieHom.map_lie, F.squareSndPolynomialMap_relative, F.squareSndPolynomialMap_relative,
        F.squareSndPolynomialMap_relative, lie_zero]
  change ⁅F.squareFiltration.polynomialSymbolMap w (F.relativeSquareLift w hw p),
    F.squareFiltration.polynomialSymbolMap w (F.relativeSquareLift w hw q)⁆ = 0
  rw [← LieHom.map_lie, he]
  exact (F.relativeSquareSymbolMap_eq_zero_iff w hw r).mpr hpq

include hw in
theorem squareSndSymbolKernel_lie_eq_zero {x y : F.squareFiltration.PolynomialSymbol w}
    (hx : F.squareSndSymbolMap w x = 0) (hy : F.squareSndSymbolMap w y = 0) : ⁅x, y⁆ = 0 := by
  have hx' : x ∈ LinearMap.range (F.relativeSquareSymbolMap w hw) := by
    rw [F.relativeSquareSymbolMap_range w hw]
    exact hx
  have hy' : y ∈ LinearMap.range (F.relativeSquareSymbolMap w hw) := by
    rw [F.relativeSquareSymbolMap_range w hw]
    exact hy
  obtain ⟨p, rfl⟩ := hx'
  obtain ⟨q, rfl⟩ := hy'
  exact F.relativeSquareSymbol_lie_eq_zero w hw p q

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

@[simp] theorem squareSndSymbolMap_symbol (r : F.squareFiltration.adaptedLieSubalgebra w) :
    F.squareSndSymbolMap w (F.squareFiltration.polynomialSymbolMap w r) =
      F.polynomialSymbolMap w (F.squareSndPolynomialMap w r) := rfl

@[simp] theorem squareSndSymbolMap_diagonal (x : F.PolynomialSymbol w) :
    F.squareSndSymbolMap w (F.squareDiagonalSymbolMap w x) = x := by
  obtain ⟨p, rfl⟩ := F.polynomialSymbolMap_surjective w x
  rw [F.squareDiagonalSymbolMap_symbol, F.squareSndSymbolMap_symbol, F.squareSndPolynomialMap_diagonal]

variable (hw : ∀ i, 0 < w i)

end Erdos3.NilpotentLieFiltration

end

end OAI
