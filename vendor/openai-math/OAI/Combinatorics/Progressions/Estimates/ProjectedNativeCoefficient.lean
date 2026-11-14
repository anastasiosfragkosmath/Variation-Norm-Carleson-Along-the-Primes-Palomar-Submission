/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/ProjectedNativeCoefficient.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.BoundedRealifiedSquareOrbit
public import OAI.Combinatorics.Progressions.Estimates.RealProjectedCoefficientLift
public import OAI.Combinatorics.Progressions.Linear.RealRankHorizontalSymbol
public import OAI.Combinatorics.Progressions.Nilpotent.RealifiedBCHProductEquiv
@[expose] public section

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

noncomputable def adaptedTranslateLinear (w : σ → ℕ) (hw : ∀ i, 0 < w i) (h : σ → ℚ) :
    F.adaptedLieSubalgebra w →ₗ[ℚ] F.adaptedLieSubalgebra w :=
  ((VectorPolynomial.translate h).comp (F.adaptedLieSubalgebra w).incl.toLinearMap).codRestrict
    (F.adaptedLieSubalgebra w).toSubmodule (by
      intro p
      exact (F.mem_adaptedSubmodule w _).mpr
        (F.adapted_translate w hw h ((F.mem_adaptedSubmodule w _).mp p.property)))

@[simp] theorem adaptedTranslateLinear_coe (w : σ → ℕ) (hw : ∀ i, 0 < w i) (h : σ → ℚ)
    (p : F.adaptedLieSubalgebra w) :
    (F.adaptedTranslateLinear w hw h p : VectorPolynomial σ ℚ L) = translate h p.val := rfl

theorem polynomialSymbolMap_adaptedTranslateLinear (w : σ → ℕ) (hw : ∀ i, 0 < w i) (h : σ → ℚ)
    (p : F.adaptedLieSubalgebra w) :
    F.polynomialSymbolMap w (F.adaptedTranslateLinear w hw h p) = F.polynomialSymbolMap w p := by
  exact F.polynomialSymbolMap_translate w hw h p

theorem realPolynomialSymbolMap_translate (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (hw : ∀ i, 0 < w i) (h : σ → ℚ)
    (p : F.realification.adaptedLieSubalgebra w) :
    F.realPolynomialSymbolMap b ω hF w (F.realification.adaptedTranslateLinear w hw h p) =
      F.realPolynomialSymbolMap b ω hF w p := by
  apply sub_eq_zero.mp
  rw [← map_sub, F.realPolynomialSymbolMap_eq_zero_iff, map_sub, sub_eq_zero]
  exact F.realification.polynomialSymbolMap_adaptedTranslateLinear w hw h p

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t : ℕ} (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

theorem realFilteredPolynomialSymbolMap_extended (w : σ → ℕ)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :
    (F.filteredPolynomialSymbolMap G φ hφ w).toLinearMap.baseChange ℝ (F.realExtendedSymbolMap w x) =
      G.realExtendedSymbolMap w ((F.filteredPolynomialMap G φ hφ w).toLinearMap.baseChange ℝ x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a p => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem realFilteredPolynomialSymbolMap_polynomial
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ M) (τ : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (w : σ → ℕ) (p : F.realification.adaptedLieSubalgebra w) :
    (F.filteredPolynomialSymbolMap G φ hφ w).toLinearMap.baseChange ℝ
        (F.realPolynomialSymbolMap b ω hF w p) =
      G.realSymbolOfPolynomial c τ hG w
        (VectorPolynomial.map ((realificationLieHom φ).toLinearMap.restrictScalars ℚ) p.val) := by
  obtain ⟨x, rfl⟩ := F.realAdaptedPolynomialTensor_surjective w b ω hF p
  change (F.filteredPolynomialSymbolMap G φ hφ w).toLinearMap.baseChange ℝ
    (F.realSymbolOfPolynomial b ω hF w (F.realAdaptedPolynomialMap w x)) = _
  rw [F.realSymbolOfPolynomial_realAdaptedPolynomialMap,
    F.realFilteredPolynomialSymbolMap_extended,
    ← G.realSymbolOfPolynomial_realAdaptedPolynomialMap c τ hG,
    F.realFilteredPolynomialMap_polynomial]
  rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {F : NilpotentLieFiltration L s} {w : σ → ℕ}

noncomputable def PolynomialOrbit.translate (g : F.PolynomialOrbit w)
    (hw : ∀ i, 0 < w i) (h : σ → ℤ) : F.PolynomialOrbit w :=
  polynomialOrbitOfLog (VectorPolynomial.translate (fun i => (h i : ℚ)) g.log)
    (F.adapted_translate w hw _ g.adapted)

end Erdos3.NilpotentLieFiltration

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d)

noncomputable def integerOrbitPoint
    (g : D.filtration.realification.PolynomialOrbit (fun _ : Unit => 1)) (n : ℤ) : D.Space :=
  QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval
    (fun _ : Unit => 1) (fun _ => n) g)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.DegreeRankLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

noncomputable def nativeHorizontalCoefficientHom (hs : 1 ≤ s)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (α : σ →₀ ℕ) :
    F.associatedDegree.realification.PolynomialOrbit w →*
      Multiplicative (ℝ ⊗[ℚ] F.HigherHorizontal (Finsupp.weight w α)) :=
  (F.realHorizontalPolynomialHom hs b ω hF w α).comp
    (F.associatedDegree.realification.polynomialOrbitCoordinates w).toMonoidHom

@[simp] theorem nativeHorizontalCoefficientHom_apply (hs : 1 ≤ s)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (α : σ →₀ ℕ)
    (g : F.associatedDegree.realification.PolynomialOrbit w) :
    Multiplicative.toAdd (F.nativeHorizontalCoefficientHom hs b ω hF w α g) =
      (F.higherHorizontalSymbolCoefficient w α).baseChange ℝ
        (F.associatedDegree.realSymbolOfPolynomial b ω hF w g.log) := rfl

theorem nativeHorizontalCoefficientHom_tensor (hs : 1 ≤ s)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (α : σ →₀ ℕ)
    (g : F.associatedDegree.realification.PolynomialOrbit w)
    (x : ℝ ⊗[ℚ] F.associatedDegree.adaptedLieSubalgebra w)
    (hx : g.log = F.associatedDegree.realAdaptedPolynomialMap w x) :
    Multiplicative.toAdd (F.nativeHorizontalCoefficientHom hs b ω hF w α g) =
      (F.higherHorizontalCoefficient w α).baseChange ℝ x := by
  rw [F.nativeHorizontalCoefficientHom_apply, hx,
    F.associatedDegree.realSymbolOfPolynomial_realAdaptedPolynomialMap]
  exact F.realHorizontalSymbolCoefficient_extended w α x

theorem nativeHorizontalCoefficientHom_translate (hs : 1 ≤ s)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (hw : ∀ i, 0 < w i) (α : σ →₀ ℕ)
    (g : F.associatedDegree.realification.PolynomialOrbit w) (h : σ → ℤ) :
    F.nativeHorizontalCoefficientHom hs b ω hF w α (g.translate hw h) =
      F.nativeHorizontalCoefficientHom hs b ω hF w α g := by
  change Multiplicative.ofAdd ((F.higherHorizontalSymbolCoefficient w α).baseChange ℝ
    (F.associatedDegree.realPolynomialSymbolMap b ω hF w
      (F.associatedDegree.realification.adaptedTranslateLinear w hw (fun i => (h i : ℚ))
        ⟨g.log, g.property⟩))) = _
  rw [F.associatedDegree.realPolynomialSymbolMap_translate]
  rfl

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

end Erdos3.NilpotentLieFiltration

namespace Erdos3

open scoped TensorProduct

end Erdos3

end

section

namespace Erdos3.DegreeRankLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t r : ℕ} (G : DegreeRankLieFiltration L s r) (F : NilpotentLieFiltration M t)
  (φ : M →ₗ⁅ℚ⁆ (Fin 4 → L))
  (hφ : ∀ d x, x ∈ F.layer d → ∀ k, φ x k ∈ G.layer d 1)

theorem projectedHorizontalSymbolCoefficient_native (hs : 1 ≤ s)
    (b : Basis ι ℚ M) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ L) (τ : κ → ℕ)
    (hG : ∀ j, G.associatedDegree.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (w : σ → ℕ) (α : σ →₀ ℕ) (p : F.realification.adaptedLieSubalgebra w)
    (g : G.associatedDegree.realification.PolynomialOrbit w) (k : Fin 4)
    (hg : VectorPolynomial.map
      ((realificationLieHom ((liePiEval k).comp φ)).toLinearMap.restrictScalars ℚ) p.val = g.log) :
    (LinearMap.proj k).baseChange ℝ
        ((G.projectedHorizontalSymbolCoefficient F φ hφ w α).baseChange ℝ
          (F.realPolynomialSymbolMap b ω hF w p)) =
      Multiplicative.toAdd (G.nativeHorizontalCoefficientHom hs c τ hG w α g) := by
  rw [G.real_projectedHorizontalSymbolCoefficient_component,
    G.nativeHorizontalCoefficientHom_apply]
  change (G.higherHorizontalSymbolCoefficient w α).baseChange ℝ
    ((F.filteredPolynomialSymbolMap G.associatedDegree ((liePiEval k).comp φ)
      (G.projectedComponent_mem_layer F φ hφ k) w).toLinearMap.baseChange ℝ
        (F.realPolynomialSymbolMap b ω hF w p)) = _
  rw [F.realFilteredPolynomialSymbolMap_polynomial G.associatedDegree ((liePiEval k).comp φ)
    (G.projectedComponent_mem_layer F φ hφ k) b ω hF c τ hG w p, hg]

end Erdos3.DegreeRankLieFiltration

end

end OAI
