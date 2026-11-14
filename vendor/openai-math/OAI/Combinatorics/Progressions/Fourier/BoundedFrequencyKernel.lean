/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Fourier/BoundedFrequencyKernel.lean
Changes: Lean module/public-import conversion; unneeded declarations and imports were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.BoundedSubmoduleIntersection
public import OAI.Combinatorics.Progressions.Estimates.LinearCoefficientSplitting
public import OAI.Combinatorics.Progressions.Estimates.StrongRefiltrationReconstruction
public import OAI.Combinatorics.Progressions.Nilpotent.NiltestVerticalBounds
@[expose] public section

namespace OAI

section

namespace Erdos3

open Module CircleFourier
open scoped TensorProduct

theorem realifyFunctional_zero {V : Type*} [AddCommGroup V] [Module ℚ V]
    (x : ℝ ⊗[ℚ] V) : realifyFunctional (0 : V →ₗ[ℚ] ℚ) x = 0 := by
  apply (mem_realified_frequency_kernel_iff (0 : V →ₗ[ℚ] ℚ) x).mp
  rw [LinearMap.ker_zero, Submodule.baseChange_top]
  trivial

theorem exists_linear_frequency_splitting
    {σ ι V : Type*} [Fintype σ] [DecidableEq σ] [AddCommGroup V] [Module ℚ V]
    (b : Basis ι ℚ V) (η : V →ₗ[ℚ] ℚ)
    {H : ℕ} (hH : 1 ≤ H) (hheight : ∀ i, RationalHeightLE (η (b i)) H)
    (T : σ → ℕ) (hT : ∀ i, 0 < T i) (a : σ → ℝ ⊗[ℚ] V)
    {δ : ℝ} (hδ : 0 < δ)
    (hbias : δ ≤ ‖linearPhaseMean T (fun i => (realifyFunctional η (a i) : CircleFourier.Circle))‖) :
    ∃ (m : ℕ) (e p r : σ → ℝ ⊗[ℚ] V),
      0 < m ∧ m ≤ H ∧ (∀ i, e i + p i + r i = a i) ∧
      (∀ i, realifyFunctional η (p i) = 0) ∧
      (∀ i j, |(b.baseChange ℝ).repr (e i) j| ≤ (H : ℝ) / (2 * T i * δ)) ∧
      (fun z : σ × ι => (b.baseChange ℝ).repr (r z.1) z.2) ∈ realDenominatorGrid m := by
  by_cases hη : η = 0
  · subst η
    refine ⟨1, 0, a, 0, Nat.zero_lt_one, hH, ?_, ?_, ?_, ?_⟩
    · intro i
      simp
    · intro i
      exact realifyFunctional_zero (a i)
    · intro i j
      simp only [Pi.zero_apply, map_zero, Finsupp.zero_apply, abs_zero]
      positivity
    · refine ⟨0, ?_⟩
      ext z
      simp
  · exact exists_biased_linear_coefficient_splitting b η hη hH hheight T hT a hδ hbias

theorem exists_bounded_frequency_kernel_spanning {ι V : Type*} [AddCommGroup V] [Module ℚ V]
    (b : Basis ι ℚ V) (η : V →ₗ[ℚ] ℚ)
    {H : ℕ} (hH : 1 ≤ H) (hheight : ∀ i, RationalHeightLE (η (b i)) H) :
    ∃ v : ι → V, Submodule.span ℚ (Set.range v) = LinearMap.ker η ∧
      ∀ i j, RationalHeightLE (b.repr (v i) j) (2 * H ^ 2) := by
  classical
  by_cases hη : η = 0
  · subst η
    refine ⟨b, ?_, ?_⟩
    · rw [LinearMap.ker_zero]
      exact b.span_eq
    · intro i j
      have hh : 1 ≤ 2 * H ^ 2 := (one_le_pow₀ hH).trans (Nat.le_mul_of_pos_left _ (by decide : 0 < 2))
      rw [Basis.repr_self, Finsupp.single_apply]
      split_ifs
      · exact rationalHeightLE_one hh
      · exact rationalHeightLE_zero hh
  · obtain ⟨u, _, _, _, hu, huheight, _⟩ := exists_bounded_frequency_direction b η hη hH hheight
    exact ⟨fun i => b i - η (b i) • u, frequencyKernel_spanning b η u hu,
      frequencyKernel_spanning_height b η u hheight huheight⟩

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Classical

end Erdos3

end

end OAI
