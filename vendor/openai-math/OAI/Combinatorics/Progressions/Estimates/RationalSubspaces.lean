/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/RationalSubspaces.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Linear.SpanKernelGenerators
@[expose] public section

namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

section Intersection

variable {η κ : Type*} [Fintype η] [Fintype κ] [DecidableEq κ]
variable {ρ : η → Type*} [∀ i, Fintype (ρ i)]

def jointMatrix (A : ∀ i, Matrix (ρ i) κ ℚ) : Matrix (Σ i, ρ i) κ ℚ :=
  fun ij k => A ij.1 ij.2 k

omit [Fintype η] [∀ i, Fintype (ρ i)] [DecidableEq κ] in
theorem jointMatrix_ker (A : ∀ i, Matrix (ρ i) κ ℚ) :
    LinearMap.ker (jointMatrix A).mulVecLin = ⨅ i, LinearMap.ker (A i).mulVecLin := by
  ext x
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, Matrix.mulVecLin_apply,
    funext_iff, Pi.zero_apply]
  exact ⟨fun h i j => h ⟨i, j⟩, fun h ij => h ij.1 ij.2⟩

theorem exists_bounded_rational_intersection_basis (A : ∀ i, Matrix (ρ i) κ ℚ)
    {H : ℕ} (hH : 1 ≤ H) (hA : ∀ i j k, RationalHeightLE (A i j k) H) :
    ∃ r : ℕ, r ≤ ∑ i, Fintype.card (ρ i) ∧
      ∃ b : Module.Basis (Fin (Module.finrank ℚ
        (⨅ i, LinearMap.ker (A i).mulVecLin : Submodule ℚ (κ → ℚ))))
        ℚ (⨅ i, LinearMap.ker (A i).mulVecLin : Submodule ℚ (κ → ℚ)),
        ∀ i j, RationalHeightLE ((b i : κ → ℚ) j) (rationalKernelHeight r H) := by
  have h := exists_bounded_rational_kernel_basis (jointMatrix A) hH
    (fun ij k => hA ij.1 ij.2 k)
  rw [← jointMatrix_ker A]
  simpa only [Fintype.card_sigma] using h

end Intersection

end Erdos3

end

end OAI
