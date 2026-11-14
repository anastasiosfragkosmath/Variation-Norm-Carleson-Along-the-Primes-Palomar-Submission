/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/CommonPositivePartitionRefinement.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Lattices.NativeIntervalResiduePartition
@[expose] public section

namespace OAI

section

universe u

namespace Erdos3

open scoped TensorProduct

structure PositiveCyclicModel (degree N : ℕ) [NeZero N] (p : ℝ) (f : ZMod N → ℝ) where
  L : Type u
  [lie : LieRing L]
  [algebra : LieAlgebra ℚ L]
  dim : ℕ
  [topology : TopologicalSpace (ℝ ⊗[ℚ] L)]
  [topologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
  [hausdorff : T2Space (ℝ ⊗[ℚ] L)]
  model : RationalFilteredNilmanifold L degree dim
  test : model.Niltest (fun _ : Unit => 1)
  positive : test.UnitIntervalValued
  complexity : test.ComplexityLE p
  eval : ∀ x, f x = (test.evalCyclic N (fun _ => x)).re

theorem PositiveCyclicNiltest.model_nonempty {degree N : ℕ} [NeZero N] {p : ℝ}
    {f : ZMod N → ℝ} (hf : PositiveCyclicNiltest.{u} degree N p f) (hp : 0 ≤ p) :
    Nonempty (PositiveCyclicModel.{u} degree N (raisedNiltestBudget p) f) := by
  rcases hf with @⟨L, lie, algebra, s, dim, topology, topologicalAdd, continuousSMul,
    hausdorff, D, hdegree, T, hpositive, hcomplexity, heval⟩
  refine ⟨{
    L := L
    lie := lie
    algebra := algebra
    dim := dim
    topology := topology
    topologicalAdd := topologicalAdd
    continuousSMul := continuousSMul
    hausdorff := hausdorff
    model := D.raiseStep hdegree
    test := T.raiseStep hdegree
    positive := T.raiseStep_unit_interval hdegree hpositive
    complexity := T.raiseStep_complexity hdegree hp hcomplexity
    eval := ?_ }⟩
  intro x
  rw [RationalFilteredNilmanifold.Niltest.raiseStep_evalCyclic]
  exact heval x

end Erdos3

end

section

universe u

namespace Erdos3.PositiveCyclicNiltest

open scoped TensorProduct

end Erdos3.PositiveCyclicNiltest

end

section

universe u

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI
