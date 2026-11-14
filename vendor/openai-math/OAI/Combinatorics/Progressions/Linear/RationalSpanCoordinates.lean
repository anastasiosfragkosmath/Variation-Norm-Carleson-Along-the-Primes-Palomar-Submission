/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Linear/RationalSpanCoordinates.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.RealifiedMultidegree
@[expose] public section

namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem span_submodule_basis (P : Submodule ℚ L) (b : Basis κ ℚ P) :
    Submodule.span ℚ (Set.range (fun j => (b j : L))) = P := by
  change Submodule.span ℚ (Set.range (P.subtype ∘ b)) = P
  rw [Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]

theorem real_span_rational_family (P : Submodule ℚ L) (v : κ → L)
    (hspan : Submodule.span ℚ (Set.range v) = P) :
    Submodule.span ℝ (Set.range (fun j => rationalLieInclusion (v j))) = P.baseChange ℝ := by
  rw [← hspan, Submodule.baseChange_span, ← Set.range_comp]
  rfl

theorem realification_layer_eq_span (n : ℕ) (v : κ → L)
    (hspan : Submodule.span ℚ (Set.range v) = (LieModule.lowerCentralSeries ℚ L L n).toSubmodule) :
    (LieModule.lowerCentralSeries ℚ (ℝ ⊗[ℚ] L) (ℝ ⊗[ℚ] L) n : Set (ℝ ⊗[ℚ] L)) =
      (Submodule.span ℝ (Set.range (fun j => rationalLieInclusion (v j))) : Set (ℝ ⊗[ℚ] L)) := by
  calc
    _ = (LieModule.lowerCentralSeries ℝ (ℝ ⊗[ℚ] L) (ℝ ⊗[ℚ] L) n : Set (ℝ ⊗[ℚ] L)) := by
      rw [LieModule.coe_lowerCentralSeries_eq_int ℚ,
        LieModule.coe_lowerCentralSeries_eq_int ℝ]
    _ = ((LieModule.lowerCentralSeries ℚ L L n).baseChange ℝ : Set (ℝ ⊗[ℚ] L)) := by
      rw [LieSubmodule.lowerCentralSeries_tensor_eq_baseChange]
    _ = ((LieModule.lowerCentralSeries ℚ L L n).toSubmodule.baseChange ℝ : Set (ℝ ⊗[ℚ] L)) := rfl
    _ = _ := congrArg (fun P : Submodule ℝ (ℝ ⊗[ℚ] L) => (P : Set (ℝ ⊗[ℚ] L)))
      (real_span_rational_family _ v hspan).symm

theorem rationalLieInclusion_integer_combination [Fintype κ] (v : κ → L) (z : κ → ℤ) (m : ℕ) :
    rationalLieInclusion (∑ j, ((z j : ℚ) * (m : ℚ)) • v j) =
      ∑ j, ((z j : ℝ) * (m : ℝ)) • rationalLieInclusion (v j) := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul]
  rw [← algebraMap_smul ℝ ((z j : ℚ) * (m : ℚ))]
  simp only [map_mul, map_intCast, map_natCast]

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι κ η L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]

theorem real_span_family_coordinates (e : Basis ι ℚ L) (v : κ → L) :
    (Submodule.span ℝ (Set.range (fun j => rationalLieInclusion (v j)))).map
        (e.baseChange ℝ).equivFun.toLinearMap =
      Submodule.span ℝ (Set.range (fun j i => (e.repr (v j) i : ℝ))) := by
  rw [Submodule.map_span, ← Set.range_comp]
  congr 2
  funext j i
  exact rationalLieInclusion_coordinates e (v j) i

theorem real_span_family_mem_iff_coordinates (e : Basis ι ℚ L) (v : κ → L)
    (x : ℝ ⊗[ℚ] L) :
    x ∈ Submodule.span ℝ (Set.range (fun j => rationalLieInclusion (v j))) ↔
      (e.baseChange ℝ).equivFun x ∈
        Submodule.span ℝ (Set.range (fun j i => (e.repr (v j) i : ℝ))) := by
  rw [← real_span_family_coordinates e v, Submodule.mem_map_equiv,
    LinearEquiv.symm_apply_apply]

theorem real_span_sum_family (v : κ → L) (w : η → L) :
    Submodule.span ℝ (Set.range (fun j => rationalLieInclusion (Sum.elim v w j))) =
      Submodule.span ℝ (Set.range (fun j => rationalLieInclusion (v j))) ⊔
        Submodule.span ℝ (Set.range (fun j => rationalLieInclusion (w j))) := by
  have heq : (fun j => rationalLieInclusion (Sum.elim v w j)) =
      Sum.elim (fun j => rationalLieInclusion (v j)) (fun j => rationalLieInclusion (w j)) := by
    funext j
    cases j <;> rfl
  rw [heq, Set.Sum.elim_range, Submodule.span_union]

omit [Fintype ι] in
theorem span_conditional_basis (e : Basis ι ℚ L) (S : Set ι) [DecidablePred (· ∈ S)] :
    Submodule.span ℚ (Set.range (fun i => if i ∈ S then e i else 0)) =
      Submodule.span ℚ (e '' S) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change (if i ∈ S then e i else 0) ∈ _
    split_ifs with h
    · exact Submodule.subset_span ⟨i, h, rfl⟩
    · exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    apply Submodule.subset_span
    exact ⟨i, by simp only [hi, ↓reduceIte]⟩

end Erdos3

end

end OAI
