/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Linear/SquareSymbolProjection.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import Mathlib.LinearAlgebra.Isomorphisms
public import OAI.Combinatorics.Progressions.Polynomial.RelativeSquarePolynomial
@[expose] public section

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

variable (hw : ∀ i, 0 < w i)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

noncomputable def squareSndSymbolMap : F.squareFiltration.PolynomialSymbol w →ₗ⁅ℚ⁆ F.PolynomialSymbol w :=
  F.squareFiltration.filteredPolynomialSymbolMap F F.squareSnd (fun _ _ hx => hx.2.1) w

theorem squareSndSymbolMap_map_eq_zero_iff (r : F.squareFiltration.adaptedLieSubalgebra w) :
    F.squareSndSymbolMap w (F.squareFiltration.polynomialSymbolMap w r) = 0 ↔
      ∀ α, (coefficients r.val α).val.2 ∈ F.layer (Finsupp.weight w α + 1) := by
  change F.polynomialSymbolMap w
    (F.squareFiltration.filteredPolynomialMap F F.squareSnd (fun _ _ hx => hx.2.1) w r) = 0 ↔ _
  rw [F.polynomialSymbolMap_eq_zero_iff]
  change (∀ α, coefficients (VectorPolynomial.map F.squareSnd.toLinearMap r.val) α ∈
    F.layer (Finsupp.weight w α + 1)) ↔ _
  simp only [coefficients_map]
  rfl

variable (hw : ∀ i, 0 < w i)

theorem squareSndSymbolMap_relative (p : F.normalizedRelativeSubmodule w) :
    F.squareSndSymbolMap w (F.relativeSquareSymbolMap w hw p) = 0 := by
  apply (F.squareSndSymbolMap_map_eq_zero_iff w (F.relativeSquareLift w hw p)).mpr
  intro α
  change (coefficients (F.relativeSquarePolynomial w hw p) α).val.2 ∈ _
  rw [F.relativeSquarePolynomial_coefficient]
  exact (F.layer _).zero_mem

theorem relativeSquareSymbolMap_range :
    LinearMap.range (F.relativeSquareSymbolMap w hw) = (F.squareSndSymbolMap w).ker.toSubmodule := by
  apply le_antisymm
  · rintro x ⟨p, rfl⟩
    exact F.squareSndSymbolMap_relative w hw p
  · intro x hx
    obtain ⟨r, rfl⟩ := F.squareFiltration.polynomialSymbolMap_surjective w x
    have hs : ∀ α, (coefficients r.val α).val.2 ∈ F.layer (Finsupp.weight w α + 1) :=
      (F.squareSndSymbolMap_map_eq_zero_iff w r).mp hx
    let p : VectorPolynomial σ ℚ L :=
      VectorPolynomial.map F.squareFst.toLinearMap r.val - VectorPolynomial.map F.squareSnd.toLinearMap r.val
    have hc (α : σ →₀ ℕ) : coefficients p α =
        (coefficients r.val α).val.1 - (coefficients r.val α).val.2 := by
      simp only [p, map_sub, Finsupp.sub_apply, coefficients_map]
      rfl
    have hp : ∀ α, coefficients p α ∈ F.layer (Finsupp.weight w α + 1) := by
      intro α
      rw [hc]
      exact (r.property α).2.2
    have hpa : p ∈ F.adaptedLieSubalgebra w :=
      fun α => F.antitone (Nat.le_succ _) (hp α)
    have hp0 : coefficients p 0 ∈ F.layer 2 := by
      rw [hc]
      exact (F.mem_squareLieSubalgebra _).mp (coefficients r.val 0).property
    let q : F.normalizedRelativeSubmodule w := ⟨⟨p, hpa⟩, hp, hp0⟩
    refine ⟨q, ?_⟩
    apply (F.squareFiltration.polynomialSymbolMap_eq_iff w (F.relativeSquareLift w hw q) r).mpr
    intro α
    rw [map_sub, Finsupp.sub_apply]
    change (coefficients (F.relativeSquarePolynomial w hw q) α).val - (coefficients r.val α).val ∈
      F.squareLayer (Finsupp.weight w α + 1)
    rw [F.relativeSquarePolynomial_coefficient]
    change (coefficients p α, (0 : L)) - (coefficients r.val α).val ∈ _
    rw [hc]
    have he : ((coefficients r.val α).val.1 - (coefficients r.val α).val.2, (0 : L)) -
        (coefficients r.val α).val = (-(coefficients r.val α).val.2, -(coefficients r.val α).val.2) := by
      apply Prod.ext <;> dsimp <;> abel
    rw [he]
    exact ⟨(F.layer _).neg_mem (hs α), (F.layer _).neg_mem (hs α), by simp⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
