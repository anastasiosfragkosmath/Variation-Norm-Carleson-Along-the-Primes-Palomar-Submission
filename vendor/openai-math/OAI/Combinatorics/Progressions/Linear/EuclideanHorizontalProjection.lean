/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Linear/EuclideanHorizontalProjection.lean
Changes: Lean module/public-import conversion only.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Geometry.ProductEuclideanCoordinates
@[expose] public section

namespace OAI

section

namespace Erdos3

def euclideanHorizontalProjection {σ : Type*} {m : ℕ} (a : ℕ) (ha : a ≤ m) :
    EuclideanSpace ℝ (σ ⊕ Fin m) →ₗ[ℝ] (Fin a → ℝ) where
  toFun x i := x (Sum.inr (Fin.castLE ha i))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem euclideanHorizontalProjection_apply {σ : Type*} {m : ℕ}
    (a : ℕ) (ha : a ≤ m) (x : EuclideanSpace ℝ (σ ⊕ Fin m)) (i : Fin a) :
    euclideanHorizontalProjection a ha x i = x (Sum.inr (Fin.castLE ha i)) := rfl

end Erdos3

end

end OAI
