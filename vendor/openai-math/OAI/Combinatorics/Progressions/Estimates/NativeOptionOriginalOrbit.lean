/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/NativeOptionOriginalOrbit.lean
Changes: Lean module/public-import conversion; unneeded declarations and imports were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Nilpotent.CyclicNiltestApproximation
public import OAI.Combinatorics.Progressions.Nilpotent.RealifiedBCHProductEquiv
public import OAI.Combinatorics.Progressions.Polynomial.RefilteredPolynomialProjection
@[expose] public section

namespace OAI

section

universe u v

namespace Erdos3

open scoped TensorProduct

variable {ι : Type v} {L₀ : Type u} {L : ι → Type u}
  [LieRing L₀] [∀ i, LieRing (L i)] [LieAlgebra ℚ L₀] [∀ i, LieAlgebra ℚ (L i)]

instance optionRealificationTopology
    [TopologicalSpace (ℝ ⊗[ℚ] L₀)] [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] (i : Option ι) :
    TopologicalSpace (ℝ ⊗[ℚ] optionLieSpace L₀ L i) := by
  cases i with
  | none => exact (inferInstance : TopologicalSpace (ℝ ⊗[ℚ] L₀))
  | some i => exact (inferInstance : TopologicalSpace (ℝ ⊗[ℚ] L i))

instance optionRealificationTopologicalAddGroup
    [TopologicalSpace (ℝ ⊗[ℚ] L₀)] [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] L₀)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
    (i : Option ι) : IsTopologicalAddGroup (ℝ ⊗[ℚ] optionLieSpace L₀ L i) := by
  cases i with
  | none => exact (inferInstance : IsTopologicalAddGroup (ℝ ⊗[ℚ] L₀))
  | some i => exact (inferInstance : IsTopologicalAddGroup (ℝ ⊗[ℚ] L i))

instance optionRealificationContinuousSMul
    [TopologicalSpace (ℝ ⊗[ℚ] L₀)] [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L₀)] [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)]
    (i : Option ι) : ContinuousSMul ℝ (ℝ ⊗[ℚ] optionLieSpace L₀ L i) := by
  cases i with
  | none => exact (inferInstance : ContinuousSMul ℝ (ℝ ⊗[ℚ] L₀))
  | some i => exact (inferInstance : ContinuousSMul ℝ (ℝ ⊗[ℚ] L i))

instance optionRealificationT2Space
    [TopologicalSpace (ℝ ⊗[ℚ] L₀)] [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)]
    [T2Space (ℝ ⊗[ℚ] L₀)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
    (i : Option ι) : T2Space (ℝ ⊗[ℚ] optionLieSpace L₀ L i) := by
  cases i with
  | none => exact (inferInstance : T2Space (ℝ ⊗[ℚ] L₀))
  | some i => exact (inferInstance : T2Space (ℝ ⊗[ℚ] L i))

end Erdos3

end

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieFiltration
open scoped TensorProduct BigOperators

variable {ι : Type v} [Fintype ι] {L₀ : Type u} {L : ι → Type u}
  [LieRing L₀] [∀ i, LieRing (L i)] [LieAlgebra ℚ L₀] [∀ i, LieAlgebra ℚ (L i)]
  {s d₀ : ℕ} {d : ι → ℕ}
  (D₀ : RationalFilteredNilmanifold L₀ s d₀)
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

section Metric

variable [TopologicalSpace (ℝ ⊗[ℚ] L₀)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L₀)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L₀)] [T2Space (ℝ ⊗[ℚ] L₀)]
  [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i : Option ι, optionLieSpace L₀ L i))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i : Option ι, optionLieSpace L₀ L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i : Option ι, optionLieSpace L₀ L i))]
  [T2Space (ℝ ⊗[ℚ] (∀ i : Option ι, optionLieSpace L₀ L i))]

end Metric

end Erdos3.RationalFilteredNilmanifold

end

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

open VectorPolynomial NilpotentLieFiltration NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

variable {ι : Type v} [Fintype ι] {L₀ : Type u} {L : ι → Type u}
  [LieRing L₀] [∀ i, LieRing (L i)] [LieAlgebra ℚ L₀] [∀ i, LieAlgebra ℚ (L i)]
  {s d₀ : ℕ} {d : ι → ℕ}
  (D₀ : RationalFilteredNilmanifold L₀ s d₀)
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

attribute [local irreducible] realPolynomialGroupMap

end Erdos3.RationalFilteredNilmanifold

end

end OAI
