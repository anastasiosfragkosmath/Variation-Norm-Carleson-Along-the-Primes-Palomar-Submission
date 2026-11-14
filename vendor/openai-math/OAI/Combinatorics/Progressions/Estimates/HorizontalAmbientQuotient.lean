/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/HorizontalAmbientQuotient.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.RealSubquotientEquiv
public import OAI.Combinatorics.Progressions.Polynomial.DegreeRankSunflower
@[expose] public section

namespace OAI

section

namespace Erdos3.DegreeRankLieFiltration

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

def higherHorizontalAmbient (d : ℕ) : F.HigherHorizontal d →ₗ[ℚ] L ⧸ F.layer d 2 :=
  (F.higherHorizontalKernel d).liftQ
    ((F.layer d 2).mkQ.comp (F.layer d 1).subtype) (by
      intro x hx
      exact (Submodule.Quotient.mk_eq_zero (F.layer d 2)).mpr hx)

@[simp] theorem higherHorizontalAmbient_mk (d : ℕ) (x : F.layer d 1) :
    F.higherHorizontalAmbient d (F.higherHorizontalMk d x) = (F.layer d 2).mkQ x.val := rfl

theorem higherHorizontalAmbient_injective (d : ℕ) :
    Function.Injective (F.higherHorizontalAmbient d) := by
  intro x y h
  obtain ⟨x, rfl⟩ := F.higherHorizontalMk_surjective d x
  obtain ⟨y, rfl⟩ := F.higherHorizontalMk_surjective d y
  apply (F.higherHorizontalMk_eq d x y).mpr
  exact (Submodule.Quotient.eq (F.layer d 2)).mp h

theorem real_higherHorizontalAmbient_injective (d : ℕ) :
    Function.Injective ((F.higherHorizontalAmbient d).baseChange ℝ) := by
  let : Module.Free ℚ ℝ := Module.Free.of_divisionRing ℚ ℝ
  exact Module.Flat.lTensor_preserves_injective_linearMap (M := ℝ)
    (F.higherHorizontalAmbient d) (F.higherHorizontalAmbient_injective d)

end Erdos3.DegreeRankLieFiltration

end

end OAI
