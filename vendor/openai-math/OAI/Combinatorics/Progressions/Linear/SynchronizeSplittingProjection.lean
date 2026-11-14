/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Linear/SynchronizeSplittingProjection.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.SplitGroupRelative
@[expose] public section

namespace OAI

section

namespace Erdos3

variable {G Q : Type*} [Group G] [Group Q]

theorem synchronize_splitting_projection (q : G →* Q) (H : Subgroup G)
    (E P R a d : G) (A D : Q) (hP : P ∈ H) (ha : a ∈ H) (hd : d ∈ H)
    (haq : q a = A⁻¹ * q E) (hdq : q d = q R * D⁻¹) :
    (E * a⁻¹) * (a * P * d) * (d⁻¹ * R) = E * P * R ∧
      a * P * d ∈ H ∧ q (E * a⁻¹) = A ∧ q (d⁻¹ * R) = D ∧
      q (a * P * d) = A⁻¹ * q (E * P * R) * D⁻¹ := by
  refine ⟨?_, H.mul_mem (H.mul_mem ha hP) hd, ?_, ?_, ?_⟩
  · group
  · rw [map_mul, map_inv, haq]
    group
  · rw [map_mul, map_inv, hdq]
    group
  · simp only [map_mul, haq, hdq]
    group

end Erdos3

end

end OAI
