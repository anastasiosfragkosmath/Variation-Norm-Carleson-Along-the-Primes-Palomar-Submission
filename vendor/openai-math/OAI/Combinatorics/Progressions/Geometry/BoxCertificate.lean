/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Geometry/BoxCertificate.lean
Changes: Lean module/public-import conversion only.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import Mathlib
@[expose] public section

namespace OAI

section

namespace Erdos3.BohrLattice.BoxCertificate

open scoped BigOperators

def realBox {n : ℕ} (r : Fin n → ℝ) : Set (Fin n → ℝ) :=
  Set.Icc (-r) r

structure SuccessiveProductCertificate {n : ℕ} (Λ : AddSubgroup (Fin n → ℝ))
    (r : Fin n → ℝ) (B : ℝ) where
  scale : Fin n → ℝ
  point : Fin n → Fin n → ℝ
  scale_nonneg : ∀ i, 0 ≤ scale i
  point_mem : ∀ i, point i ∈ Λ
  independent : LinearIndependent ℝ point
  mem_scaledBox : ∀ i, point i ∈ realBox (scale i • r)
  product_le : ∏ i, scale i ≤ B

end Erdos3.BohrLattice.BoxCertificate

end

end OAI
