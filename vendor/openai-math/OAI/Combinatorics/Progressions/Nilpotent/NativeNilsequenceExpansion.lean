/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Nilpotent/NativeNilsequenceExpansion.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Nilpotent.NiltestBasepointNormalization
@[expose] public section

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

noncomputable def conjugate (T : D.Niltest w) : D.Niltest w where
  orbit := T.orbit
  observable := fun x => star (T.observable x)
  normBound := T.normBound
  lipBound := T.lipBound
  norm_le x := by simpa only [norm_star] using T.norm_le x
  lipschitz := by
    let := D.metricSpace
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_eq_norm, ← star_sub, norm_star] using T.lipschitz.dist_le_mul x y

@[simp] theorem eval_conjugate (T : D.Niltest w) (x : σ → ℤ) :
    T.conjugate.eval x = star (T.eval x) := rfl

@[simp] theorem conjugate_complexityLE (T : D.Niltest w) (p : ℝ) :
    T.conjugate.ComplexityLE p ↔ T.ComplexityLE p := Iff.rfl

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

structure NativeNilsequenceExpansion (s N : ℕ) [NeZero N] (p : ℝ) (f : ZMod N → ℂ) where
  count : ℕ
  count_bound : (count : ℝ) ≤ Real.exp p
  L : Fin count → Type
  [lie : ∀ i, LieRing (L i)]
  [algebra : ∀ i, LieAlgebra ℚ (L i)]
  dim : Fin count → ℕ
  [topology : ∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)]
  [topologicalAdd : ∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [continuousSMul : ∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)]
  [hausdorff : ∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  model : ∀ i, RationalFilteredNilmanifold (L i) s (dim i)
  test : ∀ i, (model i).Niltest (fun _ : Unit => 1)
  complexity : ∀ i, (test i).ComplexityLE p
  coefficient : Fin count → ℂ
  cost : (∑ i, ‖coefficient i‖) ≤ Real.exp p
  eval : ∀ x, f x = ∑ i, coefficient i * (test i).evalCyclic N (fun _ => x)

attribute [local instance] NativeNilsequenceExpansion.lie NativeNilsequenceExpansion.algebra
  NativeNilsequenceExpansion.topology NativeNilsequenceExpansion.topologicalAdd
  NativeNilsequenceExpansion.continuousSMul NativeNilsequenceExpansion.hausdorff

namespace NativeNilsequenceExpansion

variable {s N : ℕ} [NeZero N] {p q : ℝ} {f : ZMod N → ℂ}

noncomputable def mono (E : NativeNilsequenceExpansion s N p f) (hpq : p ≤ q) :
    NativeNilsequenceExpansion s N q f :=
  { E with
    count_bound := E.count_bound.trans (Real.exp_le_exp.mpr hpq)
    complexity := fun i => (E.complexity i).mono hpq
    cost := E.cost.trans (Real.exp_le_exp.mpr hpq) }

end NativeNilsequenceExpansion

structure NativeVectorEquivalence {J K : Type*} [Fintype J] [Fintype K]
    (s N : ℕ) [NeZero N] (p : ℝ) (chi : J → ZMod N → ℂ) (chi' : K → ZMod N → ℂ) : Prop where
  left_dimension : (Fintype.card J : ℝ) ≤ Real.exp p
  right_dimension : (Fintype.card K : ℝ) ≤ Real.exp p
  expansion : ∀ j k, Nonempty (NativeNilsequenceExpansion s N p
    (fun x => chi j x * star (chi' k x)))

end Erdos3

end

end OAI
