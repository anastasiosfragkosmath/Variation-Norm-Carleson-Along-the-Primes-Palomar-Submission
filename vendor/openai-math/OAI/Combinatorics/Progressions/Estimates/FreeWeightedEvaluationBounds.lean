/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/FreeWeightedEvaluationBounds.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Nilpotent.FreeWeightedNilpotentLieAlgebra
@[expose] public section

namespace OAI

section

namespace Erdos3

variable {X L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : X → ℕ) (f : X → L)
  (hf : ∀ x, f x ∈ F.layer (w x))

include hf in
theorem FreeNilpotentLieAlgebra.lift_weightedLayer {d : ℕ} {x : FreeNilpotentLieAlgebra X s}
    (hx : x ∈ FreeNilpotentLieAlgebra.weightedLayer X s w d) :
    FreeNilpotentLieAlgebra.lift f F.lowerCentralSeries_eq_bot x ∈ F.layer d :=
  weightedLieUpperSpan_le_comap F (FreeNilpotentLieAlgebra.lift f F.lowerCentralSeries_eq_bot)
    (FreeNilpotentLieAlgebra.of X s) w
    (fun i => by rw [FreeNilpotentLieAlgebra.lift_of]; exact hf i) d hx

namespace FreeWeightedNilpotentLieAlgebra

noncomputable def lift : FreeWeightedNilpotentLieAlgebra X s w →ₗ⁅ℚ⁆ L :=
  lieQuotientDescend (FreeNilpotentLieAlgebra.weightedLayerIdeal X s w (s + 1))
    (FreeNilpotentLieAlgebra.lift f F.lowerCentralSeries_eq_bot)
    (fun x hx => by
      have h := FreeNilpotentLieAlgebra.lift_weightedLayer F w f hf hx
      simpa only [F.terminal, Submodule.mem_bot] using h)

@[simp] theorem lift_of (x : X) : lift F w f hf (of X s w x) = f x :=
  FreeNilpotentLieAlgebra.lift_of f F.lowerCentralSeries_eq_bot x

theorem lift_mem_layer (hw : ∀ i, 0 < w i) {d : ℕ} {x : FreeWeightedNilpotentLieAlgebra X s w}
    (hx : x ∈ (filtration X s w hw).layer d) : lift F w f hf x ∈ F.layer d := by
  obtain ⟨a, ha, rfl⟩ := hx
  exact FreeNilpotentLieAlgebra.lift_weightedLayer F w f hf ha

theorem hom_ext {φ ψ : FreeWeightedNilpotentLieAlgebra X s w →ₗ⁅ℚ⁆ L}
    (h : ∀ x, φ (of X s w x) = ψ (of X s w x)) : φ = ψ := by
  have heq : φ.comp (mk X s w) = ψ.comp (mk X s w) := FreeNilpotentLieAlgebra.hom_ext h
  apply LieHom.ext
  intro x
  obtain ⟨a, rfl⟩ := mk_surjective X s w x
  exact LieHom.congr_fun heq a

end FreeWeightedNilpotentLieAlgebra

end Erdos3

end

section

namespace Erdos3.FreeWeightedNilpotentLieAlgebra

open Module
open scoped Matrix

variable {X ι κ L : Type*} [Fintype X] [Fintype ι] [Fintype κ] [DecidableEq κ]
  [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

end Erdos3.FreeWeightedNilpotentLieAlgebra

end

end OAI
