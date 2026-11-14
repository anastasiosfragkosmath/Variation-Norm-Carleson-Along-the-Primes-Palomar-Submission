/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/FastCoefficientBlocks.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Geometry.ReducedSquareCoefficientCoordinates
@[expose] public section

namespace OAI

section

namespace Erdos3

open Module

variable {K V ι δ ε : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem basisCoordinateProjection_coarser_block (b : Basis ι K V) (c : ι → δ)
    (f : δ → ε) (d : δ) (e : ε) [Decidable (f d = e)] (x : V) :
    basisCoordinateProjection b {i | f (c i) = e}
      (basisCoordinateProjection b {i | c i = d} x) =
      if f d = e then basisCoordinateProjection b {i | c i = d} x else 0 := by
  classical
  apply b.repr.injective
  ext i
  by_cases hi : c i = d <;> by_cases hd : f d = e <;>
    simp_all [basisCoordinateProjection_repr]

theorem BasisBlockInvariant.coarser [Fintype ι]
    (b : Basis ι K V) (c : ι → δ) (U : Submodule K V)
    (hU : BasisBlockInvariant b c U) (f : δ → ε) :
    BasisBlockInvariant b (fun i => f (c i)) U := by
  classical
  intro e x hx
  rw [← sum_basisBlockProjection b c x, map_sum]
  apply U.sum_mem
  intro d _
  rw [basisCoordinateProjection_coarser_block]
  split_ifs
  · exact hU d x hx
  · exact U.zero_mem

theorem BasisBlockInvariant.graded [Fintype ι]
    (b : Basis ι K V) (c : ι → δ) (U : Submodule K V)
    (hU : BasisBlockInvariant b c U) (f : δ → ℕ) :
    BasisGradedSubmodule b (fun i => f (c i)) U :=
  hU.coarser b c U f

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem reducedSquareSnd_kernel_monomial_blocks :
    BasisBlockInvariant (F.reducedSquareSymbolBasis e ω hF w) (fun z => z.val.1)
      (F.reducedSquareSndSymbolMap w).ker.toSubmodule :=
  basisBlockInvariant_ker (F.reducedSquareSymbolBasis e ω hF w)
    (F.quotientTopSymbolBasis e ω hF w) (fun z => z.val.1) (fun z => z.val.1)
    (F.reducedSquareSndSymbolMap w).toLinearMap (F.reducedSquareSndSymbolMap_monomial_blocks e ω hF w)

theorem firstCoefficientFastSubmodule_monomial_blocks (hw : ∀ i, 0 < w i)
    (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (hU : BasisBlockInvariant (F.reducedSquareSymbolBasis e ω hF w) (fun z => z.val.1) U) :
    BasisBlockInvariant (F.firstCoefficientBasis e ω hF w) (fun z => z.val.1)
      (F.firstCoefficientFastSubmodule w hw U) := by
  rw [F.firstCoefficientFastSubmodule_eq_image]
  apply BasisBlockInvariant.map (F.reducedSquareSymbolBasis e ω hF w)
    (F.firstCoefficientBasis e ω hF w) (fun z => z.val.1) (fun z => z.val.1)
    (F.reducedSquareCoefficientMap w) (F.reducedSquareCoefficientMap_monomial_blocks e ω hF w)
  exact hU.inf _ _ _ _ (F.reducedSquareSnd_kernel_monomial_blocks e ω hF w)

end Erdos3.NilpotentLieFiltration

end

end OAI
