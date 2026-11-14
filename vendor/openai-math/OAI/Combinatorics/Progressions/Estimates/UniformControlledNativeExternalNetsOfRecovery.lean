/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/UniformControlledNativeExternalNetsOfRecovery.lean
Changes: Lean module/public-import conversion; unneeded declarations and imports were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.FixedObservableCorrelation
public import OAI.Combinatorics.Progressions.Estimates.McShaneEnvelope
public import OAI.Combinatorics.Progressions.Estimates.PositiveReconstruction
public import OAI.Combinatorics.Progressions.Nilpotent.LocalMajorDenseSliceNiltest
@[expose] public section

namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {X Y : Type*} [Nonempty X] [PseudoMetricSpace Y]
  (φ : X → Y) (L : ℝ≥0)

noncomputable def positiveImageExtension (f : X → ℂ) (y : Y) : ℂ :=
  positiveClip (mcShaneEnvelope φ L (fun x => (f x).re) y)

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {X Y Z : Type*} [Nonempty X] [PseudoMetricSpace Y] [PseudoMetricSpace Z]
  (φ : X → Y × Z) (L : ℝ≥0)

noncomputable def positiveImageSlice (f : X → ℂ) (z : Z) (y : Y) : ℂ :=
  positiveImageExtension φ L f (y, z)

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {X Y Z : Type*} [Nonempty X] [PseudoMetricSpace Y] [PseudoMetricSpace Z]
  (φ : X → Y × Z) (K : ℝ≥0) (f : X → ℂ)
  (hf : ∀ x, 0 ≤ (f x).re)
  (hrecovery : ∀ x, positiveImageSlice φ K f (φ x).2 (φ x).1 = f x)

include hf hrecovery

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial
open scoped TensorProduct

namespace NilpotentLieFiltration

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

noncomputable def adaptedPolynomialRealValueHom (t : σ → ℝ) :
    (F.realification.adaptedPolynomialFiltration w).Group →* F.realification.Group :=
  (F.realification.polynomialOrbitRealEval w t).comp (F.realification.adaptedBCHToOrbit w)

theorem adaptedPolynomialRealValueHom_coord (t : σ → ℝ)
    (g : (F.realification.adaptedPolynomialFiltration w).Group) :
    (F.adaptedPolynomialRealValueHom w t g).coord =
      eval₂ t (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) := rfl

theorem adaptedPolynomialRealValueHom_constant (t : σ → ℝ) (κ : F.realification.Group) :
    F.adaptedPolynomialRealValueHom w t (F.realification.adaptedConstantGroupHom w κ) = κ := by
  apply NilpotentLieBCHGroup.ext
  rw [adaptedPolynomialRealValueHom_coord, F.realification.adaptedConstantGroupHom_log,
    eval₂_monomial, Finsupp.prod_zero_index, one_smul]

end NilpotentLieFiltration

namespace RationalFilteredNilmanifold

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d) (w : σ → ℕ)

theorem lattice_factorization_quotient
    (g E b R : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
    (κ : D.RealGroup) (hκ : κ ∈ D.realLattice)
    (hprod : E * b * R * D.filtration.realification.adaptedConstantGroupHom w κ = g)
    (t : σ → ℝ) :
    (QuotientGroup.mk (D.filtration.adaptedPolynomialRealValueHom w t g) : D.Space) =
      QuotientGroup.mk (D.filtration.adaptedPolynomialRealValueHom w t E *
        D.filtration.adaptedPolynomialRealValueHom w t b *
        D.filtration.adaptedPolynomialRealValueHom w t R) := by
  have h := congrArg (D.filtration.adaptedPolynomialRealValueHom w t) hprod
  simp only [map_mul, NilpotentLieFiltration.adaptedPolynomialRealValueHom_constant] at h
  rw [← h]
  exact QuotientGroup.mk_mul_of_mem _ hκ

namespace Niltest

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem evalReal_of_lattice_factorization (T : D.Niltest w)
    (E b R : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
    (κ : D.RealGroup) (hκ : κ ∈ D.realLattice)
    (hprod : E * b * R * D.filtration.realification.adaptedConstantGroupHom w κ =
      ⟨⟨T.orbit.log, T.orbit.property⟩⟩) (t : σ → ℝ) :
    T.evalReal t = T.observable (QuotientGroup.mk
      (D.filtration.adaptedPolynomialRealValueHom w t E *
        D.filtration.adaptedPolynomialRealValueHom w t b *
        D.filtration.adaptedPolynomialRealValueHom w t R)) := by
  exact congrArg T.observable (lattice_factorization_quotient D w _ E b R κ hκ hprod t)

theorem eval_of_lattice_factorization (T : D.Niltest w)
    (E b R : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
    (κ : D.RealGroup) (hκ : κ ∈ D.realLattice)
    (hprod : E * b * R * D.filtration.realification.adaptedConstantGroupHom w κ =
      ⟨⟨T.orbit.log, T.orbit.property⟩⟩) (x : σ → ℤ) :
    T.eval x = T.observable (QuotientGroup.mk
      (D.filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) E *
        D.filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) b *
        D.filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) R)) := by
  rw [← T.evalReal_integer]
  exact evalReal_of_lattice_factorization D w T E b R κ hκ hprod _

end Niltest
end RationalFilteredNilmanifold
end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

theorem observable_change_left (T : D.Niltest w) (a a₀ : D.RealGroup) (x : D.Space) :
    letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
    ‖T.observable (a • x) - T.observable (a₀ • x)‖ ≤ (T.lipBound : ℝ) * dist a a₀ := by
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  let := D.metricSpace
  have hpoint : dist (a • x) (a₀ • x) ≤ dist a a₀ := by
    have hLip : LipschitzWith 1 (fun a : D.RealGroup => a • x) :=
      quotientMetricSpace_lipschitz_orbit (D.basis.baseChange ℝ) D.realLattice
        D.realLattice_closed_discrete.1 x
    simpa only [NNReal.coe_one, one_mul] using hLip.dist_le_mul a a₀
  calc
    _ ≤ (T.lipBound : ℝ) * dist (a • x) (a₀ • x) := by
      simpa only [dist_eq_norm] using T.lipschitz.dist_le_mul (a • x) (a₀ • x)
    _ ≤ _ := mul_le_mul_of_nonneg_left hpoint T.lipBound.coe_nonneg

theorem observable_freeze_factors (T : D.Niltest w) (a a₀ b r r₀ : D.RealGroup)
    (hr : (QuotientGroup.mk r : D.Space) = QuotientGroup.mk r₀) :
    letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
    ‖T.observable (QuotientGroup.mk (a * b * r)) -
      T.observable (QuotientGroup.mk (a₀ * b * r₀))‖ ≤ (T.lipBound : ℝ) * dist a a₀ := by
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  have heq : T.observable (QuotientGroup.mk (a * b * r)) =
      T.observable (QuotientGroup.mk (a * b * r₀)) :=
    congrArg (fun x : D.Space => T.observable ((a * b) • x)) hr
  rw [heq, mul_assoc a b r₀, mul_assoc a₀ b r₀]
  exact T.observable_change_left a a₀ (QuotientGroup.mk (b * r₀))

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (D : RationalFilteredNilmanifold L s d)

theorem frozen_observable_change_left (S : D.Space → ℂ) {ℓ : ℝ≥0}
    (hS : letI := D.metricSpace; LipschitzWith ℓ S) (a a' b r : D.RealGroup) :
    letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
      (D.basis.baseChange ℝ)
    ‖S (QuotientGroup.mk (a * b * r)) - S (QuotientGroup.mk (a' * b * r))‖ ≤
      (ℓ : ℝ) * dist a a' := by
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  let := D.metricSpace
  let x : D.Space := QuotientGroup.mk (b * r)
  have hLip : LipschitzWith 1 (fun a : D.RealGroup => a • x) :=
    quotientMetricSpace_lipschitz_orbit (D.basis.baseChange ℝ) D.realLattice
      D.realLattice_closed_discrete.1 x
  have hpoint : dist (a • x) (a' • x) ≤ dist a a' := by
    simpa only [NNReal.coe_one, one_mul] using hLip.dist_le_mul a a'
  have h := (hS.dist_le_mul (a • x) (a' • x)).trans
    (mul_le_mul_of_nonneg_left hpoint ℓ.coe_nonneg)
  simpa only [x, MulAction.Quotient.smul_mk, smul_eq_mul, mul_assoc, dist_eq_norm] using h

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

end Erdos3.RationalFilteredNilmanifold

end

end OAI
