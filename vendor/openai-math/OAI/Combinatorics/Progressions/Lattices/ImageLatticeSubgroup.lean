/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Lattices/ImageLatticeSubgroup.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.ControlledSurjectiveReconstruction
@[expose] public section

namespace OAI

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped Matrix TensorProduct

theorem matrix_mulVec_fine_grid {ι κ : Type*} [Fintype ι] [Fintype κ]
    (S : Matrix ι κ ℚ) (l : ℕ) :
    scaledIntegerGrid (l * matrixDenominator S) ⊆ S.mulVec ⁻¹' scaledIntegerGrid l := by
  classical
  rintro y ⟨z, rfl⟩
  obtain ⟨w, hw⟩ := integralVector_denominator_mulVec S (fun j => (z j : ℚ)) ⟨z, fun _ => rfl⟩
  refine ⟨w, ?_⟩
  rw [Matrix.mulVec_smul]
  ext i
  have hi := hw i
  change (matrixDenominator S : ℚ) * (S *ᵥ fun j => (z j : ℚ)) i = (w i : ℚ) at hi
  simp only [Pi.smul_apply, smul_eq_mul, Nat.cast_mul]
  rw [mul_assoc, hi]

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s : ℕ} {hL : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M s = ⊥}

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s : ℕ} {hL : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M s = ⊥}

namespace NilpotentLieFiltration

end NilpotentLieFiltration
end Erdos3

end

end OAI
