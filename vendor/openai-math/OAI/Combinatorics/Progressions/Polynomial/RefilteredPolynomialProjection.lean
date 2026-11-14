/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Polynomial/RefilteredPolynomialProjection.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.ProductOrbitCongruence
public import OAI.Combinatorics.Progressions.Estimates.UniformControlledNativeExternalNetsOfRecovery
@[expose] public section

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (W : LieSubalgebra ℚ F.AssociatedGraded)

theorem mem_native_refiltration_layer (j : ℕ)
    (x : ℝ ⊗[ℚ] F.gradedRefiltrationSubalgebra W) :
    x ∈ (F.gradedRefiltration W).realification.layer j ↔
      realificationLieHom (F.gradedRefiltrationSubalgebra W).incl x ∈
        F.realGradedRefiltrationLayer W j := by
  change x ∈ ((F.gradedRefiltrationLayer W j).comap
    (F.gradedRefiltrationSubalgebra W).incl.toLinearMap).baseChange ℝ ↔ _
  rw [realification_comap]
  rfl

theorem exists_native_refiltered_orbit (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hp : ∀ α, coefficients p α ∈ F.realGradedRefiltrationLayer W (Finsupp.weight w α))
    (hzero : coefficients p 0 = 0) :
    ∃ q : (F.gradedRefiltration W).realification.PolynomialOrbit w,
      VectorPolynomial.map
        (realLieHomToRat (realificationLieHom (F.gradedRefiltrationSubalgebra W).incl)).toLinearMap
        q.log = p ∧ coefficients q.log 0 = 0 := by
  obtain ⟨q₀, _, hq₀, hz₀⟩ := F.exists_refiltered_polynomial_of_coefficients w W hw p hp hzero
  let H := F.gradedRefiltrationSubalgebra W
  let inc := (realLieHomToRat (realificationLieHom H.incl)).toLinearMap
  let lift : F.realGradedRefiltrationSubalgebra W →ₗ[ℚ] (ℝ ⊗[ℚ] H) :=
    (realificationSubmoduleEquiv H.toSubmodule).symm.toLinearMap.restrictScalars ℚ
  have hcomp : inc.comp lift = (F.realGradedRefiltrationSubalgebra W).incl.toLinearMap := by
    ext x
    exact congrArg Subtype.val ((realificationSubmoduleEquiv H.toSubmodule).apply_symm_apply x)
  let q := VectorPolynomial.map lift q₀
  have hmap : VectorPolynomial.map inc q = p := by
    apply coefficients.injective
    ext α
    dsimp only [q]
    rw [coefficients_map, coefficients_map]
    change (inc.comp lift) (coefficients q₀ α) = coefficients p α
    rw [hcomp]
    simpa only [coefficients_map] using congrArg (fun r => coefficients r α) hq₀
  have hadapted : (F.gradedRefiltration W).realification.Adapted w q := by
    apply ((F.gradedRefiltration W).realification.adapted_iff_coefficients w q).mpr
    intro α
    rw [F.mem_native_refiltration_layer]
    have h := congrArg (fun r => coefficients r α) hmap
    rw [coefficients_map] at h
    change inc (coefficients q α) ∈ F.realGradedRefiltrationLayer W (Finsupp.weight w α)
    rw [h]
    exact hp α
  refine ⟨polynomialOrbitOfLog q hadapted, hmap, ?_⟩
  change coefficients (VectorPolynomial.map lift q₀) 0 = 0
  rw [coefficients_map, hz₀, map_zero]

theorem native_refiltered_orbit_real_value (w : σ → ℕ)
    (q : (F.gradedRefiltration W).realification.PolynomialOrbit w)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hmap : VectorPolynomial.map
      (realLieHomToRat (realificationLieHom (F.gradedRefiltrationSubalgebra W).incl)).toLinearMap
      q.log = p) (t : σ → ℝ) :
    NilpotentLieBCHGroup.realificationMap
      (hnil := (F.gradedRefiltration W).lowerCentralSeries_eq_bot)
      (hM := F.lowerCentralSeries_eq_bot) (F.gradedRefiltrationSubalgebra W).incl
      ((F.gradedRefiltration W).realification.polynomialOrbitRealEval w t q) =
        (⟨eval₂ t p⟩ : F.realification.Group) := by
  apply NilpotentLieBCHGroup.ext
  change realificationLieHom (F.gradedRefiltrationSubalgebra W).incl (eval₂ t q.log) = eval₂ t p
  rw [← hmap]
  exact (eval₂_map (realificationLieHom (F.gradedRefiltrationSubalgebra W).incl).toLinearMap t q.log).symm

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t : ℕ} (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j) (w : σ → ℕ)

include hφ in
theorem realificationLieHom_mem_layer (j : ℕ) (x : ℝ ⊗[ℚ] L)
    (hx : x ∈ F.realification.layer j) :
    realificationLieHom φ x ∈ G.realification.layer j :=
  baseChange_mem_of_mapsTo (F.layer j) (G.layer j) φ.toLinearMap (hφ j) hx

noncomputable def realPolynomialGroupMap :
    (F.realification.adaptedPolynomialFiltration w).Group →*
      (G.realification.adaptedPolynomialFiltration w).Group :=
  mapOfSteps (hL := (F.realification.adaptedPolynomialFiltration w).lowerCentralSeries_eq_bot)
    (hM := (G.realification.adaptedPolynomialFiltration w).lowerCentralSeries_eq_bot)
    (F.realification.filteredPolynomialMap G.realification
      (realLieHomToRat (realificationLieHom φ)) (F.realificationLieHom_mem_layer G φ hφ) w)

theorem realPolynomialGroupMap_value
    (g : (F.realification.adaptedPolynomialFiltration w).Group) (x : σ → ℝ) :
    G.adaptedPolynomialRealValueHom w x (F.realPolynomialGroupMap G φ hφ w g) =
      realificationMap (hnil := F.lowerCentralSeries_eq_bot) (hM := G.lowerCentralSeries_eq_bot) φ
        (F.adaptedPolynomialRealValueHom w x g) := by
  apply NilpotentLieBCHGroup.ext
  exact eval₂_map (realificationLieHom φ).toLinearMap x
    (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))

theorem realPolynomialGroupMap_constant (c : F.realification.Group) :
    F.realPolynomialGroupMap G φ hφ w (F.realification.adaptedConstantGroupHom w c) =
      G.realification.adaptedConstantGroupHom w
        (realificationMap (hnil := F.lowerCentralSeries_eq_bot)
          (hM := G.lowerCentralSeries_eq_bot) φ c) := by
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  change VectorPolynomial.map ((realificationLieHom φ).toLinearMap.restrictScalars ℚ)
    (monomial 0 c.coord) = monomial 0 (realificationLieHom φ c.coord)
  exact map_monomial _ _ _

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (W : LieSubalgebra ℚ F.AssociatedGraded)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

variable {ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  (b : Basis ι ℚ L) (e : Basis κ ℚ M) (φ : L →ₗ⁅ℚ⁆ M) (ν : κ → ι)
  (hν : ∀ x k, e.repr (φ x) k = b.repr x (ν k))

namespace NilpotentLieFiltration

variable {σ : Type*} {s t : ℕ} (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
  (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j) (w : σ → ℕ)

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (w : σ → ℕ)

variable (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t e : ℕ} (F : NilpotentLieFiltration L s)
  (W : LieSubalgebra ℚ F.AssociatedGraded)
  (E : RationalFilteredNilmanifold (F.gradedRefiltrationSubalgebra W) s e)
  (hEF : E.filtration = F.gradedRefiltration W) (w : σ → ℕ)

include hEF in
theorem exists_model_refiltered_polynomial (hw : ∀ i, 0 < w i)
    (b : (F.realification.adaptedPolynomialFiltration w).Group)
    (hb : ∀ α, coefficients (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α ∈
      F.realGradedRefiltrationLayer W (Finsupp.weight w α))
    (hb0 : coefficients (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0) :
    ∃ g : E.filtration.realification.PolynomialOrbit w,
      ∀ x : σ → ℤ,
        realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
          (hM := F.lowerCentralSeries_eq_bot) (F.gradedRefiltrationSubalgebra W).incl
          (E.filtration.realification.polynomialOrbitEval w x g) =
            F.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) b := by
  rw [hEF]
  obtain ⟨g, hg, _⟩ := F.exists_native_refiltered_orbit W w hw
    (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) hb hb0
  refine ⟨g, ?_⟩
  intro x
  rw [← polynomialOrbitRealEval_integer]
  exact F.native_refiltered_orbit_real_value W w g _ hg _

end Erdos3.NilpotentLieFiltration

end

end OAI
