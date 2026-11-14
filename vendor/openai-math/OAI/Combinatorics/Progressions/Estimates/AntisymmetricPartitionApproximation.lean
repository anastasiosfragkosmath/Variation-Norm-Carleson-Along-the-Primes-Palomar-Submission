/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/AntisymmetricPartitionApproximation.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Polynomial.AntisymmetricBoxPolynomial
@[expose] public section

namespace OAI

section

namespace Erdos3

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

structure NativeAntisymmetricOrbitFactors {p : ℝ}
    (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p) (N : ℕ) (q : ℝ) where
  leftIndex : Fin W.outputDim
  rightIndex : Fin W.outputDim
  basis : Basis (Fin (finrank ℚ (Fin 8 → W.L))) ℚ (Fin 8 → W.L)
  weight : Fin (finrank ℚ (Fin 8 → W.L)) → ℕ
  adapted : ∀ k, (pi (fun _ : Fin 8 => W.model)).filtration.layer k =
    Submodule.span ℚ (basis '' {i | k ≤ weight i})
  basis_height : ∀ i j,
    rationalLogHeight ((pi (fun _ : Fin 8 => W.model)).basis.repr (basis i) j) ≤ q
  subalgebra : LieSubalgebra ℚ (pi (fun _ : Fin 8 => W.model)).filtration.AssociatedGraded
  generator : Fin (finrank ℚ (Fin 8 → W.L)) →
    (pi (fun _ : Fin 8 => W.model)).filtration.AssociatedGraded
  spanning : Submodule.span ℚ (Set.range generator) = subalgebra.toSubmodule
  graded : BasisGradedSubmodule
    ((pi (fun _ : Fin 8 => W.model)).filtration.associatedGradedBasis basis weight adapted)
    weight subalgebra.toSubmodule
  generator_height : ∀ i j, rationalLogHeight
    (((pi (fun _ : Fin 8 => W.model)).filtration.associatedGradedBasis basis weight adapted).repr
      (generator i) j) ≤ q
  kills_top : ∀ z ∈ (pi (fun _ : Fin 8 => W.model)).filtration.realGradedRefiltrationLayer
      subalgebra (∑ k, mixedCorrelationDegree 1 k),
    realifyFunctional (piFrequency W.antisymmetricBoxFrequencies) z = 0
  denominator : ℕ
  denominator_pos : 0 < denominator
  denominator_bound : (denominator : ℝ) ≤ Real.exp q
  latticeConstant : (pi (fun _ : Fin 8 => W.model)).RealGroup
  latticeConstant_mem : latticeConstant ∈ (pi (fun _ : Fin 8 => W.model)).realLattice
  slow :
    ((pi (fun _ : Fin 8 => W.model)).filtration.realification.adaptedPolynomialFiltration
      (fun _ : Fin 4 => 1)).Group
  middle :
    ((pi (fun _ : Fin 8 => W.model)).filtration.realification.adaptedPolynomialFiltration
      (fun _ : Fin 4 => 1)).Group
  rational :
    ((pi (fun _ : Fin 8 => W.model)).filtration.realification.adaptedPolynomialFiltration
      (fun _ : Fin 4 => 1)).Group
  product : slow * middle * rational *
    (pi (fun _ : Fin 8 => W.model)).filtration.realification.adaptedConstantGroupHom
      (fun _ : Fin 4 => 1) latticeConstant = W.antisymmetricBoxPolynomial leftIndex rightIndex
  slow_bound : ∀ α i, |(basis.baseChange ℝ).repr
    (coefficients (slow.coord : VectorPolynomial (Fin 4) ℚ (ℝ ⊗[ℚ] (Fin 8 → W.L))) α) i| ≤
      Real.exp q / monomialScale (fun _ : Fin 4 => (N : ℝ)) α
  rational_grid : (fun z : ((Fin 4) →₀ ℕ) × Fin (finrank ℚ (Fin 8 → W.L)) =>
    (basis.baseChange ℝ).repr
      (coefficients (rational.coord : VectorPolynomial (Fin 4) ℚ (ℝ ⊗[ℚ] (Fin 8 → W.L))) z.1) z.2) ∈
        realDenominatorGrid denominator
  middle_zero : coefficients
    (middle.coord : VectorPolynomial (Fin 4) ℚ (ℝ ⊗[ℚ] (Fin 8 → W.L))) 0 = 0
  rational_zero : coefficients
    (rational.coord : VectorPolynomial (Fin 4) ℚ (ℝ ⊗[ℚ] (Fin 8 → W.L))) 0 = 0
  middle_coefficients : ∀ α, coefficients
    (middle.coord : VectorPolynomial (Fin 4) ℚ (ℝ ⊗[ℚ] (Fin 8 → W.L))) α ∈
      (pi (fun _ : Fin 8 => W.model)).filtration.realGradedRefiltrationLayer subalgebra
        (Finsupp.weight (fun _ => 1) α)

namespace NativeAntisymmetricOrbitFactors

variable {p q : ℝ} {N : ℕ}
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p}
  (V : NativeAntisymmetricOrbitFactors W N q)

end NativeAntisymmetricOrbitFactors

end Erdos3

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra

end Erdos3

end

section

namespace Erdos3.NativeAntisymmetricOrbitFactors

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

variable {p q : ℝ} {N : ℕ}
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p}
  (V : NativeAntisymmetricOrbitFactors W N q)
  [TopologicalSpace (ℝ ⊗[ℚ] (Fin 8 → W.L))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (Fin 8 → W.L))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (Fin 8 → W.L))] [T2Space (ℝ ⊗[ℚ] (Fin 8 → W.L))]

end Erdos3.NativeAntisymmetricOrbitFactors

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

end Erdos3

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold NilpotentLieBCHGroup
open scoped TensorProduct

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

structure NativeAntisymmetricFrozenDescent {p : ℝ}
    {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {N : ℕ}
    (V : NativeAntisymmetricOrbitFactors W N p) (q : ℝ) where
  nonnegative : 0 ≤ p
  [productTopology : TopologicalSpace (ℝ ⊗[ℚ] (Fin 8 → W.L))]
  [productTopologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] (Fin 8 → W.L))]
  [productContinuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] (Fin 8 → W.L))]
  [productHausdorff : T2Space (ℝ ⊗[ℚ] (Fin 8 → W.L))]
  outerBudget : ℝ
  outer_nonnegative : 0 ≤ outerBudget
  outer_bound : outerBudget ≤ q
  denominator : ℕ
  denominator_pos : 0 < denominator
  denominator_bound : (denominator : ℝ) ≤ Real.exp outerBudget
  rational_values : ∀ x : Fin 4 → ℤ,
    ((pi (fun _ : Fin 8 => W.model)).basis.baseChange ℝ).equivFun
      ((pi (fun _ : Fin 8 => W.model)).filtration.adaptedPolynomialRealValueHom
        (fun _ : Fin 4 => 1) (fun i => (x i : ℝ)) V.rational).coord ∈
      realDenominatorGrid denominator
  slow_values : ∀ x : Fin 4 → ℤ, (∀ i, |(x i : ℝ)| ≤ (N : ℝ)) → ∀ i,
    |((pi (fun _ : Fin 8 => W.model)).basis.baseChange ℝ).repr
      ((pi (fun _ : Fin 8 => W.model)).filtration.adaptedPolynomialRealValueHom
        (fun _ : Fin 4 => 1) (fun j => (x j : ℝ)) V.slow).coord i| ≤ Real.exp outerBudget
  L : Type
  [lie : LieRing L]
  [algebra : LieAlgebra ℚ L]
  dim : ℕ
  [topology : TopologicalSpace (ℝ ⊗[ℚ] L)]
  [topologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
  [hausdorff : T2Space (ℝ ⊗[ℚ] L)]
  model : RationalFilteredNilmanifold L 1 dim
  model_complexity : model.GeometryComplexityLE q
  orbit : model.filtration.realification.PolynomialOrbit (fun _ : Fin 4 => 1)
  descend : ∀ a r : (pi (fun _ : Fin 8 => W.model)).RealGroup,
    (∀ i, |((pi (fun _ : Fin 8 => W.model)).basis.baseChange ℝ).repr a.coord i| ≤
      Real.exp outerBudget) →
    ((pi (fun _ : Fin 8 => W.model)).basis.baseChange ℝ).equivFun r.coord ∈
      realDenominatorGrid denominator →
    ∃ S : model.Niltest (fun _ : Fin 4 => 1), S.orbit = orbit ∧
      S.normBound = (W.antisymmetricBoxNiltest nonnegative V.leftIndex V.rightIndex).normBound ∧
      S.ComplexityLE q ∧ ∀ x : Fin 4 → ℤ,
        S.eval x = (W.antisymmetricBoxNiltest nonnegative V.leftIndex V.rightIndex).observable
          (QuotientGroup.mk (a *
            (pi (fun _ : Fin 8 => W.model)).filtration.adaptedPolynomialRealValueHom
              (fun _ : Fin 4 => 1) (fun i => (x i : ℝ)) V.middle * r))

attribute [local instance] NativeAntisymmetricFrozenDescent.lie NativeAntisymmetricFrozenDescent.algebra
  NativeAntisymmetricFrozenDescent.topology NativeAntisymmetricFrozenDescent.topologicalAdd
  NativeAntisymmetricFrozenDescent.continuousSMul NativeAntisymmetricFrozenDescent.hausdorff

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold NilpotentLieBCHGroup
open scoped TensorProduct

theorem RationalFilteredNilmanifold.observable_frozen_right_eq
    {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    (D : RationalFilteredNilmanifold L s d) (u : D.Space → ℂ)
    (a b r r' : D.RealGroup)
    (h : (QuotientGroup.mk r : D.Space) = QuotientGroup.mk r') :
    u (QuotientGroup.mk (a * b * r)) = u (QuotientGroup.mk (a * b * r')) :=
  congrArg (fun x : D.Space => u ((a * b) • x)) h

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeAntisymmetricFrozenDescent.lie NativeAntisymmetricFrozenDescent.algebra
  NativeAntisymmetricFrozenDescent.topology NativeAntisymmetricFrozenDescent.topologicalAdd
  NativeAntisymmetricFrozenDescent.continuousSMul NativeAntisymmetricFrozenDescent.hausdorff

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeAntisymmetricFrozenDescent.lie NativeAntisymmetricFrozenDescent.algebra
  NativeAntisymmetricFrozenDescent.topology NativeAntisymmetricFrozenDescent.topologicalAdd
  NativeAntisymmetricFrozenDescent.continuousSMul NativeAntisymmetricFrozenDescent.hausdorff

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeAntisymmetricFrozenDescent.lie NativeAntisymmetricFrozenDescent.algebra
  NativeAntisymmetricFrozenDescent.topology NativeAntisymmetricFrozenDescent.topologicalAdd
  NativeAntisymmetricFrozenDescent.continuousSMul NativeAntisymmetricFrozenDescent.hausdorff

end Erdos3

end

end OAI
