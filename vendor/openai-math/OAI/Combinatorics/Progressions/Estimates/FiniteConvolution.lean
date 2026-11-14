/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/FiniteConvolution.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Fourier.FiniteFourierSmoothing
@[expose] public section

namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H]

noncomputable def finiteConvolution (f g : H → ℂ) (x : H) : ℂ :=
  𝔼 y, f y * g (x - y)

theorem finiteConvolution_fourier_mass_sq (f g : H → ℂ) :
    (∑ χ : AddChar H ℂ, ‖finiteFourierCoeff f χ * finiteFourierCoeff g χ‖) ^ 2 ≤
      (𝔼 x, ‖f x‖ ^ 2) * (𝔼 x, ‖g x‖ ^ 2) := by
  simp only [norm_mul]
  rw [← finiteFourier_parseval, ← finiteFourier_parseval]
  exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _

end Erdos3

end

end OAI
