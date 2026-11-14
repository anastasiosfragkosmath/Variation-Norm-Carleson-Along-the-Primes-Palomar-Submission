/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Linear/RealFourAnnihilatorKernel.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import OAI.Combinatorics.Progressions.Estimates.CommonCoefficientFourAnnihilators
@[expose] public section

namespace OAI

section

namespace Erdos3

open scoped TensorProduct

theorem mem_realified_coordinate_kernel_iff
    {V J : Type*} [AddCommGroup V] [Module ℚ V] [Fintype J]
    (ℓ : V →ₗ[ℚ] (J → ℚ)) (x : ℝ ⊗[ℚ] V) :
    x ∈ (LinearMap.ker ℓ).baseChange ℝ ↔
      ∀ j, realifyFunctional ((LinearMap.proj j).comp ℓ) x = 0 := by
  have hker : LinearMap.ker ℓ = ⨅ j, LinearMap.ker ((LinearMap.proj j).comp ℓ) := by
    ext v
    simp only [LinearMap.mem_ker, Submodule.mem_iInf, LinearMap.comp_apply, LinearMap.proj_apply]
    exact funext_iff
  rw [hker, real_baseChange_iInf]
  simp only [Submodule.mem_iInf, mem_realified_frequency_kernel_iff]

theorem mem_real_petal_annihilator_iff
    {V J : Type*} [AddCommGroup V] [Module ℚ V] [Fintype J]
    (D : Submodule ℚ V) (K : Submodule ℚ (Fin 4 → V))
    (ℓ : (Fin 4 → V) →ₗ[ℚ] (J → ℚ)) (hker : LinearMap.ker ℓ = K)
    (v : ℝ ⊗[ℚ] V) :
    v ∈ (fourPetalSpace D K).baseChange ℝ ↔
      v ∈ D.baseChange ℝ ∧ ∀ j, realifyFunctional
        (((LinearMap.proj j).comp ℓ).comp (LinearMap.single ℚ (fun _ : Fin 4 => V) 0)) v = 0 := by
  rw [fourPetalSpace_eq_inf_ker D K ℓ hker, realification_inf, Submodule.mem_inf,
    mem_realified_coordinate_kernel_iff]
  rfl

end Erdos3

end

end OAI
