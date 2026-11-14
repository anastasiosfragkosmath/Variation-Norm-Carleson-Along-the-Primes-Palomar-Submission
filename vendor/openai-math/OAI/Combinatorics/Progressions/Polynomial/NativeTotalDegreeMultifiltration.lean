/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Polynomial/NativeTotalDegreeMultifiltration.lean
Changes: Lean module/public-import conversion only.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.RationalPowerHeight
@[expose] public section

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped BigOperators

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d)

theorem exists_totalDegree_layer_basis (n : ℕ) {p : ℝ} (hD : D.GeometryComplexityLE p) :
    ∃ b : Basis (Fin (finrank ℚ (D.filtration.layer n))) ℚ (D.filtration.layer n),
      ∀ j k, rationalLogHeight (D.basis.repr (b j : L) k) ≤ p := by
  by_cases hn : n = 0
  · subst n
    have hzero : D.filtration.layer 0 = D.filtration.layer 1 :=
      D.filtration.totalDegree_zero_layer.trans D.filtration.one_eq_top.symm
    rw [hzero]
    exact D.exists_positive_layer_basis 1 le_rfl hD
  · exact D.exists_positive_layer_basis n (by omega) hD

noncomputable def totalDegreeMultidegree (σ : Type*) [Fintype σ] [Nonempty σ]
    {p : ℝ} (hD : D.GeometryComplexityLE p) : D.MultidegreeStructure (fun _ : σ => s) where
  filtration := D.filtration.totalDegreeMultifiltration σ
  ordinary := rfl
  basis a := Classical.choose (D.exists_totalDegree_layer_basis (∑ i, (a i).val) hD)

theorem totalDegreeMultidegree_complexity (σ : Type*) [Fintype σ] [Nonempty σ]
    {p : ℝ} (hD : D.GeometryComplexityLE p) :
    (D.totalDegreeMultidegree σ hD).ComplexityLE p :=
  ⟨hD, fun a => Classical.choose_spec (D.exists_totalDegree_layer_basis (∑ i, (a i).val) hD)⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI
