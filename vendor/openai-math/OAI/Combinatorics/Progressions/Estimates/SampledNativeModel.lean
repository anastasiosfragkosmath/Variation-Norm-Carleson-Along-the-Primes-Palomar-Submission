/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/SampledNativeModel.lean
Changes: Lean module/public-import conversion; unneeded declarations and imports were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import Mathlib.Analysis.LocallyConvex.BalancedCoreHull
public import Mathlib.Analysis.Normed.Module.Seminorm.Basic
public import OAI.Combinatorics.Progressions.Nilpotent.LocalMajorDenseSliceNiltest
public import OAI.Combinatorics.Progressions.Nilpotent.NiltestVerticalBounds
public import OAI.Combinatorics.Progressions.Lattices.NativeIntegerAffinePullbackHom
@[expose] public section

namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

structure NativeSampleCorrelation {σ X : Type*} (w : σ → ℕ)
    (degree : ℕ) (p : ℝ) (S : Finset X) (sample : X → σ → ℤ) (f : X → ℂ) where
  L : Type
  [lie : LieRing L]
  [algebra : LieAlgebra ℚ L]
  dim : ℕ
  [topology : TopologicalSpace (ℝ ⊗[ℚ] L)]
  [topologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
  [hausdorff : T2Space (ℝ ⊗[ℚ] L)]
  model : RationalFilteredNilmanifold L degree dim
  test : model.Niltest w
  complexity : test.ComplexityLE p
  correlation : Real.exp (-p) ≤ ‖𝔼 x ∈ S, f x * star (test.eval (sample x))‖

attribute [local instance] NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

namespace NativeSampleCorrelation

variable {σ X : Type*} {w : σ → ℕ} {s : ℕ} {p q : ℝ}
  {S : Finset X} {sample : X → σ → ℤ} {f : X → ℂ}

noncomputable def mono (V : NativeSampleCorrelation w s p S sample f) (hpq : p ≤ q) :
    NativeSampleCorrelation w s q S sample f :=
  { V with
    complexity := V.complexity.mono hpq
    correlation := (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans V.correlation }

theorem exists_of_expansion {eta : (σ → ℤ) → ℂ}
    (E : NativeIntegerExpansion w s p eta) (hq : 0 ≤ q)
    (hcorr : Real.exp (-q) ≤ ‖𝔼 x ∈ S, f x * star (eta (sample x))‖) :
    Nonempty (NativeSampleCorrelation w s (q + p) S sample f) := by
  obtain ⟨i, hi⟩ := E.select_sample_correlation S sample f hcorr
  exact ⟨{
    L := E.L i
    dim := E.dim i
    model := E.model i
    test := E.test i
    complexity := (E.complexity i).mono (le_add_of_nonneg_left hq)
    correlation := hi }⟩

end NativeSampleCorrelation

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct Pointwise BigOperators

structure NativeSampleModel {σ X : Type*} (w : σ → ℕ) (degree : ℕ) (p : ℝ)
    (sample : X → σ → ℤ) (f : X → ℂ) where
  L : Type
  [lie : LieRing L]
  [algebra : LieAlgebra ℚ L]
  dim : ℕ
  [topology : TopologicalSpace (ℝ ⊗[ℚ] L)]
  [topologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
  [hausdorff : T2Space (ℝ ⊗[ℚ] L)]
  model : RationalFilteredNilmanifold L degree dim
  test : model.Niltest w
  norm : test.normBound ≤ 1
  complexity : test.ComplexityLE p
  eval : ∀ x, f x = test.eval (sample x)

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

variable {σ X : Type*} {w : σ → ℕ} {degree : ℕ} {p : ℝ}
  {sample : X → σ → ℤ} {f : X → ℂ}

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

attribute [local instance] NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

namespace RationalFilteredNilmanifold.Niltest

variable {I L : Type*} [Fintype I] [DecidableEq I] [LieRing L] [LieAlgebra ℚ L]
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {degree dim : ℕ}
  {D : RationalFilteredNilmanifold L degree dim}

end RationalFilteredNilmanifold.Niltest

namespace RationalFilteredNilmanifold.Niltest

variable {I Ω : Type*} {L : Type} [Fintype I] [DecidableEq I]
  [LieRing L] [LieAlgebra ℚ L]
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {degree dim : ℕ}
  {D : RationalFilteredNilmanifold L degree dim} {p : ℝ}

end RationalFilteredNilmanifold.Niltest

end Erdos3

end

section

namespace Erdos3.NativeSampleModel

open CircleFourier
open scoped TensorProduct BigOperators

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

variable {σ X : Type*} {w : σ → ℕ} {degree : ℕ} {p : ℝ}
  {sample : X → σ → ℤ} {f : X → ℂ}

structure VerticalExpansion (native : NativeSampleModel w degree p sample f)
    (q rho : ℝ) where
  I : Type
  [finite : Fintype I]
  frequency : I → native.L →ₗ[ℚ] ℚ
  component : I → native.model.Niltest w
  card_le : (Fintype.card I : ℝ) ≤ Real.exp (verticalDecompositionBudget q)
  height_le : ∀ i j, rationalLogHeight (frequency i (native.model.basis j)) ≤
    verticalDecompositionBudget q
  orbit_eq : ∀ i, (component i).orbit = native.test.orbit
  norm_eq : ∀ i, (component i).normBound = native.test.normBound
  lip_eq : ∀ i, (component i).lipBound = native.test.lipBound
  vertical : ∀ i (z : native.model.RealGroup),
    z ∈ native.model.filtration.realification.subgroup degree → ∀ x,
      (component i).observable (z • x) =
        character ((realifyFunctional (frequency i) z.coord : ℝ) : CircleFourier.Circle) *
          (component i).observable x
  integral : ∀ i, (∃ x, (component i).observable x ≠ 0) →
    ∀ z : native.model.RealGroup,
      z ∈ native.model.filtration.realification.subgroup degree →
      z ∈ native.model.realLattice → ∃ n : ℤ, realifyFunctional (frequency i) z.coord = n
  preserves_character : ∀ (z : native.model.RealGroup) (c : ℂ),
    (∀ x, native.test.observable (z • x) = c * native.test.observable x) →
      ∀ i x, (component i).observable (z • x) = c * (component i).observable x
  observable_error : ∀ x,
    ‖(∑ i, (component i).observable x) - native.test.observable x‖ ≤ rho

attribute [instance] VerticalExpansion.finite

namespace VerticalExpansion

variable {native : NativeSampleModel w degree p sample f} {q rho : ℝ}
  (E : native.VerticalExpansion q rho)

end VerticalExpansion
end Erdos3.NativeSampleModel

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI
