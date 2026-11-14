/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/NumberTheory/SiegelZeros/Estimates/GlobalConstants.lean
Changes: Lean module/public-import conversion only.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.FieldTheory.IsAlgClosed.Basic
@[expose] public section

namespace OAI

namespace SiegelZeros

section

open CategoryTheory AlgebraicGeometry

namespace SiegelZerosAwei.Workers.W15

universe u

variable {K : Type u} [Field K] [IsAlgClosed K]
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K))

noncomputable def constantSectionMap : K →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appTop).hom

theorem constantSectionMap_bijective [IsIntegral X] [UniversallyClosed f] :
    Function.Bijective (constantSectionMap f) := by
  apply IsAlgClosed.ringHom_bijective_of_isIntegral
  change (((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appTop).hom).IsIntegral
  apply RingHom.isIntegral_respectsIso.2
    (e := (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv)
  exact isIntegral_appTop_of_universallyClosed f

theorem globalSection_existsUnique_constant [IsIntegral X] [UniversallyClosed f]
    (s : Γ(X, ⊤)) : ∃! c : K, constantSectionMap f c = s := by
  obtain ⟨c, hc⟩ := (constantSectionMap_bijective f).2 s
  exact ⟨c, hc, fun d hd => (constantSectionMap_bijective f).1 (hd.trans hc.symm)⟩

local instance integral_top_nonempty [IsIntegral X] : Nonempty (⊤ : X.Opens) :=
  ⟨⟨Classical.choice (inferInstance : Nonempty X), trivial⟩⟩

theorem rationalFunction_constant_of_global [IsIntegral X] [UniversallyClosed f]
    (r : X.functionField)
    (h : ∃ s : Γ(X, ⊤), X.germToFunctionField ⊤ s = r) :
    ∃ c : K, X.germToFunctionField ⊤ (constantSectionMap f c) = r := by
  obtain ⟨s, hs⟩ := h
  obtain ⟨c, hc⟩ := (constantSectionMap_bijective f).2 s
  exact ⟨c, by rw [hc, hs]⟩

end SiegelZerosAwei.Workers.W15

end

end SiegelZeros

end OAI
