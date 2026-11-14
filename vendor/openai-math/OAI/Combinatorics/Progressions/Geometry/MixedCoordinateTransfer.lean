/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Geometry/MixedCoordinateTransfer.lean
Changes: Lean module/public-import conversion; unneeded declarations and imports were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Fourier.NiltestConjugateFrequency
public import OAI.Combinatorics.Progressions.Lattices.NativeFrozenAffineExpansion
public import OAI.Combinatorics.Progressions.Lattices.NativeIntegerSelfEquivalence
public import OAI.Combinatorics.Progressions.Nilpotent.NativeMultidegreeNiltest
@[expose] public section

namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)

noncomputable def boxComponent (out : Fin W.outputDim) (a b : Fin 4) :
    W.model.Niltest (fun _ : Fin 4 => 1) :=
  (W.component out).linearPullbackHom
    ![{ toFun := fun n => n a, map_zero' := rfl, map_add' := fun _ _ => rfl },
      { toFun := fun n => n b, map_zero' := rfl, map_add' := fun _ _ => rfl }]

noncomputable def antisymmetricBoxValue (i j : Fin W.outputDim) (n : Fin 4 → ℤ) : ℂ :=
  let K := fun x y => star (W.eval i (correlationInput x y)) * W.eval j (correlationInput y x)
  K (n 0) (n 2) * star (K (n 1) (n 2)) * star (K (n 0) (n 3)) * K (n 1) (n 3)

noncomputable def antisymmetricBoxFactors (i j : Fin W.outputDim) :
    Fin 8 → W.model.Niltest (fun _ : Fin 4 => 1) :=
  ![(W.boxComponent i 0 2).conjugate, W.boxComponent j 2 0,
    W.boxComponent i 1 2, (W.boxComponent j 2 1).conjugate,
    W.boxComponent i 0 3, (W.boxComponent j 3 0).conjugate,
    (W.boxComponent i 1 3).conjugate, W.boxComponent j 3 1]

noncomputable def antisymmetricBoxFrequencies : Fin 8 → (W.L →ₗ[ℚ] ℚ) :=
  ![-W.vertical.frequency, W.vertical.frequency, W.vertical.frequency, -W.vertical.frequency,
    W.vertical.frequency, -W.vertical.frequency, -W.vertical.frequency, W.vertical.frequency]

theorem antisymmetricBoxFactors_complexity (i j : Fin W.outputDim) (k : Fin 8) :
    (W.antisymmetricBoxFactors i j k).ComplexityLE (p + 8) := by
  have hi := (W.component_complexity i).mono (by linarith : p + 4 ≤ p + 8)
  have hj := (W.component_complexity j).mono (by linarith : p + 4 ≤ p + 8)
  fin_cases k
  · exact hi
  · exact hj
  · exact hi
  · exact hj
  · exact hi
  · exact hj
  · exact hi
  · exact hj

variable [TopologicalSpace (ℝ ⊗[ℚ] (Fin 8 → W.L))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (Fin 8 → W.L))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (Fin 8 → W.L))] [T2Space (ℝ ⊗[ℚ] (Fin 8 → W.L))]

noncomputable def antisymmetricBoxNiltest (hp : 0 ≤ p) (i j : Fin W.outputDim) :
    (pi (fun _ : Fin 8 => W.model)).Niltest (fun _ : Fin 4 => 1) :=
  piNiltest (fun _ : Fin 8 => W.model) (W.antisymmetricBoxFactors i j)
    (by linarith) (by simpa using hp) (W.antisymmetricBoxFactors_complexity i j)

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)

variable [TopologicalSpace (ℝ ⊗[ℚ] (Fin 8 → W.L))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (Fin 8 → W.L))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (Fin 8 → W.L))] [T2Space (ℝ ⊗[ℚ] (Fin 8 → W.L))]

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

noncomputable def antisymmetricKernel {p : ℝ}
    (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)
    (i j : Fin W.outputDim) (x y : ℤ) : ℂ :=
  star (W.eval i (correlationInput x y)) * W.eval j (correlationInput y x)

theorem antisymmetricKernel_norm {p : ℝ}
    (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)
    (i j : Fin W.outputDim) (x y : ℤ) : ‖W.antisymmetricKernel i j x y‖ ≤ 1 := by
  rw [antisymmetricKernel, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (W.norm_eval i _)).trans
    (W.norm_eval j _)

theorem antisymmetricKernel_cyclic {p : ℝ}
    (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)
    (N : ℕ) [NeZero N] (i j : Fin W.outputDim) (x y : ZMod N) :
    W.antisymmetricKernel i j (x.val : ℤ) (y.val : ℤ) =
      star (W.evalCyclic N i (correlationInput x y)) * W.evalCyclic N j (correlationInput y x) := by
  have he (k : Fin W.outputDim) (x y : ZMod N) :
      W.eval k (correlationInput (x.val : ℤ) (y.val : ℤ)) =
        W.evalCyclic N k (correlationInput x y) := by
    apply congrArg (W.eval k)
    funext l
    fin_cases l <;> rfl
  simp only [antisymmetricKernel, he]

theorem exists_mixed_coordinate_slice :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)
      (d : Fin 2) (c : ℤ) (k : Fin W.outputDim),
      Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) 1 ((p + C) ^ C)
        (fun x => W.eval k (Function.update (fun _ => c) d (x ())))) := by
  obtain ⟨C, hC, hfreeze⟩ := exists_frozen_affine_expansion (mixedCorrelationDegree 1)
  refine ⟨C, hC, ?_⟩
  intro p W d c k
  classical
  let A : Fin 2 → ℤ := fun j => if j = d then 1 else 0
  let b : Fin 2 → ℤ := fun j => if j = d then 0 else c
  obtain ⟨E, _⟩ := hfreeze W {d} A b k (by
    intro j hj
    simp only [Finset.mem_singleton] at hj
    simp [A, hj])
  have hdegree : (∑ j ∈ ({d} : Finset (Fin 2)), mixedCorrelationDegree 1 j) = 1 := by
    simp only [Finset.sum_singleton]
    fin_cases d <;> rfl
  have heq : (fun x : Unit → ℤ => W.eval k (fun j => b j + A j * x ())) =
      (fun x => W.eval k (Function.update (fun _ => c) d (x ()))) := by
    funext x
    apply congrArg (W.eval k)
    funext j
    by_cases hj : j = d
    · subst j
      simp [A, b]
    · simp [A, b, hj]
  exact ⟨by simpa only [hdegree, heq] using E⟩

theorem exists_antisymmetric_coordinate_slice :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)
      (i j : Fin W.outputDim) (d : Fin 2) (c : ℤ),
      Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) 1 ((p + C) ^ C)
        (fun x => let z := Function.update (fun _ => c) d (x ())
          W.antisymmetricKernel i j (z 0) (z 1))) := by
  obtain ⟨A, _, hslice⟩ := exists_mixed_coordinate_slice
  obtain ⟨B, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (((X + Polynomial.C A) ^ A + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p W i j d c
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  obtain ⟨E⟩ := hslice W d c i
  obtain ⟨F⟩ := hslice W d.rev c j
  obtain ⟨G⟩ := hmul (by positivity : 0 ≤ (p + A) ^ A) E.conjugate F
  have hcost : ((p + A) ^ A + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have heq : (fun x : Unit → ℤ => star (W.eval i (Function.update (fun _ => c) d (x ()))) *
      W.eval j (Function.update (fun _ => c) d.rev (x ()))) =
      (fun x => let z := Function.update (fun _ => c) d (x ())
        W.antisymmetricKernel i j (z 0) (z 1)) := by
    funext x
    unfold antisymmetricKernel
    congr 1
    · congr 1
      apply congrArg (W.eval i)
      funext l
      fin_cases l <;> rfl
    · apply congrArg (W.eval j)
      funext l
      fin_cases d <;> fin_cases l <;> rfl
  exact ⟨by simpa only [heq] using G.mono hcost⟩

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
