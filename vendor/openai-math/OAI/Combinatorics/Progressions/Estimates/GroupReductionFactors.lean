/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/GroupReductionFactors.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import Mathlib.Tactic
public import Mathlib.Topology.Algebra.Group.Pointwise
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Compactness.Compact
@[expose] public section

namespace OAI

section

namespace Erdos3

open scoped Pointwise

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

end Erdos3

end

section

namespace Erdos3

variable {G : Type*} [Group G]

theorem exists_representative_factors_of_reductions (Γ : Subgroup G)
    (H : ℕ → Subgroup G) (s : ℕ) (P : G → Prop)
    (hzero : H 0 = ⊤) (hterminal : H s = ⊥)
    (hstep : ∀ i < s, ∀ g ∈ H i,
      ∃ r, P r ∧ ∃ w ∈ Γ, r⁻¹ * g * w⁻¹ ∈ H (i + 1)) :
    ∀ g : G, ∃ rs : List G, rs.length = s ∧ (∀ r ∈ rs, P r) ∧
      ∃ γ ∈ Γ, g = rs.prod * γ := by
  have haux (n : ℕ) : ∀ i, i + n = s → ∀ g ∈ H i,
      ∃ rs : List G, rs.length = n ∧ (∀ r ∈ rs, P r) ∧
        ∃ γ ∈ Γ, g = rs.prod * γ := by
    induction n with
    | zero =>
      intro i hi g hg
      have his : i = s := by omega
      subst i
      have hg1 : g = 1 := by simpa only [hterminal, Subgroup.mem_bot] using hg
      exact ⟨[], rfl, by simp, 1, Γ.one_mem, by simpa using hg1⟩
    | succ n ih =>
      intro i hi g hg
      obtain ⟨r, hr, w, hw, hrem⟩ := hstep i (by omega) g hg
      obtain ⟨rs, hlen, hP, γ, hγ, heq⟩ := ih (i + 1) (by omega) _ hrem
      refine ⟨r :: rs, by simp [hlen], ?_, γ * w, Γ.mul_mem hγ hw, ?_⟩
      · intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hr
        · exact hP a ha
      · calc
          g = r * (r⁻¹ * g * w⁻¹) * w := by group
          _ = (r :: rs).prod * (γ * w) := by rw [heq, List.prod_cons]; group
  intro g
  exact haux s 0 (by omega) g (by simp [hzero])

end Erdos3

end

end OAI
