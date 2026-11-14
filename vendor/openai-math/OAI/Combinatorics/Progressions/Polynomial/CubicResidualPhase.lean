/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Polynomial/CubicResidualPhase.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.HigherResidualRowDifferences
@[expose] public section

namespace OAI

section

namespace Erdos3

open scoped BigOperators TensorProduct

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

namespace NativeMixedCorrelation

theorem exists_fixed_residual_coordinate {s N : ℕ} [NeZero N] {p : ℝ}
    {f : ZMod N → ℂ} (W : NativeMixedCorrelation s N p f) :
    ∃ i : Fin W.mixed.outputDim, ∃ H ⊆ W.shifts, H.Nonempty ∧
      Real.exp (-(2 * p)) * N ≤ (H.card : ℝ) ∧
      ∀ h ∈ H, Nonempty (NativeVectorCorrelation (s - 1) N p
        (fun _ : Unit => nativeMixedResidual f W.mixed h i)) := by
  obtain ⟨i, H, hsub, hH, hdense, hcorr⟩ := NativeVectorCorrelation.exists_fixed_coordinate
    W.shifts W.nonempty (nativeMixedResidual f W.mixed)
    (by simpa only [Fintype.card_fin] using W.mixed.output_bound) W.correlation
  refine ⟨i, H, hsub, hH, ?_, hcorr⟩
  have hW : Real.exp (-p) * N ≤ (W.shifts.card : ℝ) := by
    simpa only [ZMod.card] using W.density
  calc
    Real.exp (-(2 * p)) * N = Real.exp (-p) * (Real.exp (-p) * N) := by
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ Real.exp (-p) * W.shifts.card := mul_le_mul_of_nonneg_left hW (Real.exp_nonneg _)
    _ ≤ H.card := hdense

end NativeMixedCorrelation

end Erdos3

end

end OAI
