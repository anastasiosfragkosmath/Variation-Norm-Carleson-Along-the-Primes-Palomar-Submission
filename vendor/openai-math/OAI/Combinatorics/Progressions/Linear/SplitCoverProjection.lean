/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Linear/SplitCoverProjection.lean
Changes: Lean module/public-import conversion; unneeded declarations and imports were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Geometry.NativeProductOrbitMetric
public import OAI.Combinatorics.Progressions.Geometry.SquarefreeActionMetric
public import OAI.Combinatorics.Progressions.Lattices.SourceLatticeCover
@[expose] public section

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D E : RationalFilteredNilmanifold L s d)

noncomputable def sublatticeProjection (h : E.lattice ≤ D.lattice) : E.Space → D.Space :=
  cosetMap E.realLattice D.realLattice (MonoidHom.id _) (Subgroup.map_mono h)

@[simp] theorem sublatticeProjection_mk (h : E.lattice ≤ D.lattice) (x : E.RealGroup) :
    sublatticeProjection D E h (QuotientGroup.mk x) = QuotientGroup.mk x := rfl

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem sublatticeProjection_lipschitz (h : E.lattice ≤ D.lattice) (hb : E.basis = D.basis) :
    letI := E.metricSpace
    letI := D.metricSpace
    LipschitzWith 1 (sublatticeProjection D E h) := by
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] L) := (D.basis.baseChange ℝ).finiteDimensional_of_finite
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  let := rightMetricSpace_isIsometricSMul (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  have hLip : LipschitzWith 1 (MonoidHom.id D.RealGroup) := LipschitzWith.id
  have hc := lipschitz_cosetMap E.realLattice D.realLattice E.realLattice_closed_discrete.1
    D.realLattice_closed_discrete.1 (MonoidHom.id _) (Subgroup.map_mono h) hLip
  change @LipschitzWith E.Space D.Space
    (quotientMetricSpace (E.basis.baseChange ℝ) E.realLattice
      E.realLattice_closed_discrete.1).toEMetricSpace.toPseudoEMetricSpace
    (quotientMetricSpace (D.basis.baseChange ℝ) D.realLattice
      D.realLattice_closed_discrete.1).toEMetricSpace.toPseudoEMetricSpace
    1 (sublatticeProjection D E h)
  rw [hb]
  exact hc

theorem sublattice_pullback_lipschitz (h : E.lattice ≤ D.lattice) (hb : E.basis = D.basis)
    (u : D.Space → ℂ) {K : ℝ≥0} (hu : letI := D.metricSpace; LipschitzWith K u) :
    letI := E.metricSpace
    LipschitzWith K (u ∘ sublatticeProjection D E h) := by
  let := E.metricSpace
  let := D.metricSpace
  simpa only [mul_one] using hu.comp (sublatticeProjection_lipschitz D E h hb)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {L : Option ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
  {s : ℕ} {d : Option ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
  (V : RationalFilteredNilmanifold (∀ i, L i) s (Fintype.card (Σ i, Fin (d i))))
  (hsub : (pi D).lattice ≤ V.lattice)

variable [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L (some i)))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L (some i)))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L (some i)))]
  [T2Space (ℝ ⊗[ℚ] (∀ i, L (some i)))]

end Erdos3.RationalFilteredNilmanifold

end

end OAI
