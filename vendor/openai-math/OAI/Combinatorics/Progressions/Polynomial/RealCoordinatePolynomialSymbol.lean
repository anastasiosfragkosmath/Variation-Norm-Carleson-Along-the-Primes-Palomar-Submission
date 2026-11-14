/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Polynomial/RealCoordinatePolynomialSymbol.lean
Changes: Lean module/public-import conversion; unneeded declarations and imports were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Nilpotent.IdealInvariantNiltestBudget
public import OAI.Combinatorics.Progressions.Sampling.IntegralGridBudget
@[expose] public section

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct

variable {σ τ R S V : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup V] [Module R V] [Module S V] [IsScalarTower R S V]

end Erdos3.VectorPolynomial

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ τ L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] {s : ℕ} (F : NilpotentLieFiltration L s)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {d s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis (Fin d) ℚ L) (omega : Fin d → ℕ)
  (hlayer : ∀ k, F.layer k = Submodule.span ℚ (e '' {j | k ≤ omega j}))

include hlayer

theorem real_scaled_adapted_basis_mem (B : ℝ) (j : Fin d) :
    B • (e.baseChange ℝ) j ∈ F.realification.layer (omega j) := by
  change B • (e.baseChange ℝ) j ∈ (F.realLayer (omega j)).toSubmodule
  rw [F.realLayer_eq_span_basis e _ _ (hlayer _)]
  exact Submodule.smul_mem _ B (Submodule.subset_span ⟨j, by simp, rfl⟩)

noncomputable def orderedSlotFactor (B : ℝ) (i j : Fin d) :
    F.realification.PolynomialOrbit (patchVariableWeight (σ := σ) omega i) := by
  classical
  exact if h : j.val < i.val then
    polynomialOrbitOfLog
      (monomial (Finsupp.single (Sum.inr (⟨j.val, h⟩ : Fin i.val)) 1)
        (B • (e.baseChange ℝ) j)) (by
      apply (F.realification.mem_adaptedSubmodule _ _).mp
      apply F.realification.monomial_mem_adaptedSubmodule
      simpa only [Finsupp.weight_single, one_smul, patchVariableWeight,
        Sum.elim_inr, earlierSlot, Fin.eta] using
        F.real_scaled_adapted_basis_mem e omega hlayer B j)
  else 1

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hlayers : ∀ k, F.layer k = Submodule.span ℚ (b '' {i | k ≤ ω i}))
    (v : σ → ℕ) (P : ι → MvPolynomial σ ℝ)
    (hP : ∀ i, P i ∈ weightedSupportLE v (ω i))

include hlayers hP

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {d s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis (Fin d) ℚ L) (omega : Fin d → ℕ)
  (hlayer : ∀ k, F.layer k = Submodule.span ℚ (e '' {j | k ≤ omega j}))

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

noncomputable def realExtendedSymbolMap :
    (ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) →ₗ⁅ℚ⁆ F.RealPolynomialSymbol w :=
  LieAlgebra.ExtendScalars.map (AlgHom.id ℚ ℝ) (F.polynomialSymbolMap w)

theorem realSymbolOfPolynomial_realAdaptedPolynomialMap
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :
    F.realSymbolOfPolynomial b ω hlayers w (F.realAdaptedPolynomialMap w x) =
      F.realExtendedSymbolMap w x := by
  induction x using TensorProduct.inductionOn with
  | tmul a p =>
    apply ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr.injective
    ext z
    rw [F.realSymbolOfPolynomial_coordinate, F.realAdaptedPolynomialMap_coefficient_tmul]
    change (b.baseChange ℝ).repr (a ⊗ₜ[ℚ] coefficients (p : VectorPolynomial σ ℚ L) z.val.1) z.val.2 =
      ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr
        (a ⊗ₜ[ℚ] F.polynomialSymbolMap w p) z
    rw [Basis.baseChange_repr_tmul, Basis.baseChange_repr_tmul, F.polynomialSymbolBasis_repr_map]
  | add x y hx hy => simp only [map_add, hx, hy]

noncomputable def realPolynomialSymbolMap :
    F.realification.adaptedLieSubalgebra w →ₗ⁅ℚ⁆ F.RealPolynomialSymbol w where
  toLinearMap := (F.realSymbolOfPolynomial b ω hlayers w).comp
    (F.realification.adaptedLieSubalgebra w).incl.toLinearMap
  map_lie' {p q} := by
    change F.realSymbolOfPolynomial b ω hlayers w (↑⁅p, q⁆) =
      ⁅F.realSymbolOfPolynomial b ω hlayers w p, F.realSymbolOfPolynomial b ω hlayers w q⁆
    obtain ⟨x, rfl⟩ := F.realAdaptedPolynomialTensor_surjective w b ω hlayers p
    obtain ⟨y, rfl⟩ := F.realAdaptedPolynomialTensor_surjective w b ω hlayers q
    rw [← (F.realAdaptedPolynomialTensor w).map_lie x y]
    simp only [F.realAdaptedPolynomialTensor_coe, F.realSymbolOfPolynomial_realAdaptedPolynomialMap]
    exact (F.realExtendedSymbolMap w).map_lie x y

@[simp] theorem realPolynomialSymbolMap_apply (p : F.realification.adaptedLieSubalgebra w) :
    F.realPolynomialSymbolMap b ω hlayers w p = F.realSymbolOfPolynomial b ω hlayers w p := rfl

@[simp] theorem realPolynomialSymbolMap_representative (x : F.RealPolynomialSymbol w) :
    F.realPolynomialSymbolMap b ω hlayers w (F.realAdaptedSymbolRepresentative b ω hlayers w x) = x := by
  rw [F.realPolynomialSymbolMap_apply, F.realAdaptedSymbolRepresentative_coe,
    F.realSymbolOfPolynomial_representative]

theorem realPolynomialSymbolMap_surjective :
    Function.Surjective (F.realPolynomialSymbolMap b ω hlayers w) :=
  fun x => ⟨F.realAdaptedSymbolRepresentative b ω hlayers w x,
    F.realPolynomialSymbolMap_representative b ω hlayers w x⟩

theorem realPolynomialSymbolMap_eq_zero_iff (p : F.realification.adaptedLieSubalgebra w) :
    F.realPolynomialSymbolMap b ω hlayers w p = 0 ↔
      F.realification.polynomialSymbolMap w p = 0 := by
  rw [F.realPolynomialSymbolMap_apply, F.realSymbolOfPolynomial_eq_zero_iff,
    F.realification.polynomialSymbolMap_eq_zero_iff]

noncomputable def realPolynomialSymbolHom :
    (F.realification.adaptedPolynomialFiltration w).Group →* F.RealPolynomialSymbolGroup w :=
  NilpotentLieBCHGroup.map (F.realPolynomialSymbolMap b ω hlayers w)

@[simp] theorem realPolynomialSymbolHom_coord
    (g : (F.realification.adaptedPolynomialFiltration w).Group) :
    (F.realPolynomialSymbolHom b ω hlayers w g).coord =
      F.realPolynomialSymbolMap b ω hlayers w g.coord := rfl

noncomputable def realPolynomialSymbolLift (g : F.RealPolynomialSymbolGroup w) :
    (F.realification.adaptedPolynomialFiltration w).Group :=
  ⟨F.realAdaptedSymbolRepresentative b ω hlayers w g.coord⟩

@[simp] theorem realPolynomialSymbolHom_lift (g : F.RealPolynomialSymbolGroup w) :
    F.realPolynomialSymbolHom b ω hlayers w (F.realPolynomialSymbolLift b ω hlayers w g) = g := by
  apply NilpotentLieBCHGroup.ext
  simp only [F.realPolynomialSymbolHom_coord, realPolynomialSymbolLift,
    F.realPolynomialSymbolMap_representative]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {d s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis (Fin d) ℚ L) (omega : Fin d → ℕ)
  (hlayer : ∀ k, F.layer k = Submodule.span ℚ (e '' {j | k ≤ omega j}))
  (Λ : Subgroup F.Group) [MetricSpace (F.realification.Group ⧸ Λ.map realificationHom)]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open MvPolynomial

namespace NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hlayers : ∀ k, F.layer k = Submodule.span ℚ (b '' {i | k ≤ ω i}))
    (v : σ → ℕ) (P : ι → MvPolynomial σ ℝ)

variable (hP : ∀ i, P i ∈ weightedSupportLE v (ω i))

end NilpotentLieFiltration

end Erdos3

end

end OAI
