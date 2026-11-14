/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Nilpotent/CurrentBracketInductionStep.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.CurrentLayerPreservation
@[expose] public section

namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

section General

variable {R L ι : Type*} [Field R] [LieRing L] [LieAlgebra R L]

def BasisHomogeneousBrackets (b : Basis ι R L) (w : ι → ℕ) : Prop :=
  ∀ i j k, w k ≠ w i + w j → b.repr ⁅b i, b j⁆ k = 0

theorem BasisHomogeneousBrackets.lie_mem_span (b : Basis ι R L) (w : ι → ℕ)
    (hb : BasisHomogeneousBrackets b w) {i j : ℕ} {x y : L}
    (hx : x ∈ Submodule.span R (b '' {k | w k = i}))
    (hy : y ∈ Submodule.span R (b '' {k | w k = j})) :
    ⁅x, y⁆ ∈ Submodule.span R (b '' {k | w k = i + j}) := by
  induction hx, hy using Submodule.span_induction₂ with
  | mem_mem x y hx hy =>
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨c, hc, rfl⟩ := hy
    change w a = i at ha
    change w c = j at hc
    apply (basis_mem_span_image_iff b _ _).mpr
    intro k hk
    change w k ≠ i + j at hk
    exact hb a c k (by simpa only [ha, hc] using hk)
  | zero_left y _ => rw [zero_lie]; exact Submodule.zero_mem _
  | zero_right x _ => rw [lie_zero]; exact Submodule.zero_mem _
  | add_left x y z _ _ _ hx hy => rw [add_lie]; exact Submodule.add_mem _ hx hy
  | add_right x y z _ _ _ hx hy => rw [lie_add]; exact Submodule.add_mem _ hx hy
  | smul_left r x y _ _ h => rw [smul_lie]; exact Submodule.smul_mem _ r h
  | smul_right r x y _ _ h => rw [lie_smul]; exact Submodule.smul_mem _ r h

theorem BasisHomogeneousBrackets.projection_lie (b : Basis ι R L) (w : ι → ℕ)
    (hb : BasisHomogeneousBrackets b w) {i j : ℕ} {x y : L}
    (hx : basisGradeProjection b w i x = x) (hy : basisGradeProjection b w j y = y) :
    basisGradeProjection b w (i + j) ⁅x, y⁆ = ⁅x, y⁆ := by
  apply basisCoordinateProjection_eq_self
  apply hb.lie_mem_span b w
  · rw [← hx]
    exact basisCoordinateProjection_mem_span b _ _
  · rw [← hy]
    exact basisCoordinateProjection_mem_span b _ _

end General

theorem BasisHomogeneousBrackets.baseChange {L ι : Type*} [LieRing L] [LieAlgebra ℚ L]
    (b : Basis ι ℚ L) (w : ι → ℕ) (hb : BasisHomogeneousBrackets b w) :
    BasisHomogeneousBrackets (b.baseChange ℝ) w := by
  intro i j k hk
  rw [Basis.baseChange_apply, Basis.baseChange_apply,
    LieAlgebra.ExtendScalars.bracket_tmul, one_mul, Basis.baseChange_repr_tmul, hb i j k hk]
  exact zero_smul ℚ (1 : ℝ)

namespace NilpotentLieFiltration

variable {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))

theorem associatedGradedBasis_homogeneous_brackets :
    BasisHomogeneousBrackets (F.associatedGradedBasis b w hlayers) w := by
  intro i j k hk
  rw [F.associatedGradedBasis_bracket b w hlayers, ite_eq_right (Ne.symm hk)]

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.PolynomialTranslationLie

open MvPolynomial Module

variable {σ : Type*} [Fintype σ]

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))

end Erdos3.NilpotentLieFiltration

end

end OAI
