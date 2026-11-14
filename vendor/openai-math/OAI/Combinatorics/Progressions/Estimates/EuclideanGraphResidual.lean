/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/EuclideanGraphResidual.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Lattices.ScaledLatticeCovolume
public import OAI.Combinatorics.Progressions.Linear.EuclideanDerivativeProjection
@[expose] public section

namespace OAI

section

namespace Erdos3

variable {σ κ : Type*} [Fintype σ] [Fintype κ]

noncomputable def euclideanDerivativeShiftMap (T : σ → ℝ) (hT : ∀ i, T i ≠ 0) :
    EuclideanSpace ℝ (σ ⊕ κ) →ₗ[ℝ] (σ → ℝ) :=
  (coordinateScaleEquiv T hT).toLinearMap.comp
    ((LinearMap.fst ℝ (σ → ℝ) (κ → ℝ)).comp productEuclideanEquiv.symm.toLinearMap)

omit [Fintype σ] [Fintype κ] in
theorem euclideanDerivativeShiftMap_apply (T : σ → ℝ) (hT : ∀ i, T i ≠ 0)
    (v : EuclideanSpace ℝ (σ ⊕ κ)) (i : σ) :
    euclideanDerivativeShiftMap T hT v i = T i * v (Sum.inl i) := rfl

omit [Fintype σ] [Fintype κ] in
theorem euclideanDerivativeShiftMap_eq_zero_iff (T : σ → ℝ) (hT : ∀ i, T i ≠ 0)
    (v : EuclideanSpace ℝ (σ ⊕ κ)) :
    euclideanDerivativeShiftMap T hT v = 0 ↔ ∀ i : σ, v (Sum.inl i) = 0 := by
  simp only [funext_iff, euclideanDerivativeShiftMap_apply, Pi.zero_apply,
    mul_eq_zero, hT, false_or]

variable (T : σ → ℝ) (hT : ∀ i, T i ≠ 0) (scale : κ → ℝ) (hscale : ∀ j, scale j ≠ 0)
  (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (A : (κ → ℝ) ≃ₗ[ℝ] (κ → ℝ)) (l : ℕ) (hl : 0 < l)

theorem euclideanDerivativeShiftMap_integer (v : EuclideanSpace ℝ (σ ⊕ κ))
    (hv : v ∈ euclideanDerivativeLattice T hT scale hscale Y A l hl) :
    euclideanDerivativeShiftMap T hT v ∈ realIntegerGrid := by
  have hv' := (euclideanDerivativeLattice_mem_iff T hT scale hscale Y A l hl v).mp hv
  obtain ⟨h, z, hz⟩ := (derivativeLattice_mem_iff T hT scale hscale Y A l hl _).mp hv'
  refine ⟨h, ?_⟩
  funext i
  change (h i : ℝ) = T i * (productEuclideanEquiv.symm v).1 i
  rw [hz, derivativeLatticeEquiv_apply]
  exact (mul_div_cancel₀ (h i : ℝ) (hT i)).symm

theorem euclideanDerivative_vertical_lattice_full (R : ℝ) :
    let Λ := euclideanDerivativeLattice T hT scale hscale Y A l hl
    let Z := shortVectorSpan Λ R
    IsZLattice ℝ (latticeKernel (shortVectorLattice Λ R)
      ((euclideanDerivativeShiftMap T hT).comp Z.subtype)) := by
  apply latticeKernel_full
  intro x hx
  exact euclideanDerivativeShiftMap_integer T hT scale hscale Y A l hl x.val hx

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

theorem euclidean_graph_residual_mem_kernel
    {σ κ : Type*} [Fintype σ] [Fintype κ]
    (T : σ → ℝ) (hT : ∀ i, T i ≠ 0)
    (Z : Submodule ℝ (EuclideanSpace ℝ (σ ⊕ κ)))
    (G : (σ → ℝ) →ₗ[ℝ] Z) (hG : ∀ y i, (G y).val (Sum.inl i) = y i) (x : Z) :
    x - G (fun i => x.val (Sum.inl i)) ∈
      LinearMap.ker ((euclideanDerivativeShiftMap T hT).comp Z.subtype) := by
  change euclideanDerivativeShiftMap T hT
    ((x - G (fun i => x.val (Sum.inl i))).val) = 0
  apply (euclideanDerivativeShiftMap_eq_zero_iff T hT _).mpr
  intro i
  change x.val (Sum.inl i) - (G (fun j => x.val (Sum.inl j))).val (Sum.inl i) = 0
  rw [hG, sub_self]

end Erdos3

end

end OAI
