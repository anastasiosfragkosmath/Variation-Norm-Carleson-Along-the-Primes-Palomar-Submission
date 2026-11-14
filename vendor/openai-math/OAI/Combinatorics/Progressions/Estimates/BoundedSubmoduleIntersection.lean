/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/BoundedSubmoduleIntersection.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Linear.RankQuotientHeightBudget
@[expose] public section

namespace OAI

section

namespace Erdos3

open Module

variable {ι L : Type*} [Fintype ι] [AddCommGroup L] [Module ℚ L]
  (b : Basis ι ℚ L)

noncomputable def coordinateArraySpan (m : ℕ) (c : Fin m × ι → ℚ) : Submodule ℚ L :=
  Submodule.span ℚ (Set.range fun a : Fin m => b.equivFun.symm (fun i => c (a, i)))

noncomputable def heightBoundedSubspaces (m H : ℕ) : Set (Submodule ℚ L) :=
  coordinateArraySpan b m '' {c : Fin m × ι → ℚ | ∀ z, RationalHeightLE (c z) H}

theorem mem_heightBoundedSubspaces (m H : ℕ) (U : Submodule ℚ L) :
    U ∈ heightBoundedSubspaces b m H ↔
      ∃ v : Fin m → L, Submodule.span ℚ (Set.range v) = U ∧
        ∀ a i, RationalHeightLE (b.repr (v a) i) H := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨fun a => b.equivFun.symm (fun i => c (a, i)), rfl, ?_⟩
    intro a i
    simpa only [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply] using hc (a, i)
  · rintro ⟨v, hv, hh⟩
    refine ⟨fun z => b.repr (v z.1) z.2, (fun z => hh z.1 z.2), ?_⟩
    have he : (fun a : Fin m => b.equivFun.symm (fun i => b.repr (v a) i)) = v := by
      funext a
      apply b.equivFun.injective
      simp only [LinearEquiv.apply_symm_apply, Basis.equivFun_apply]
    change Submodule.span ℚ (Set.range (fun a : Fin m => b.equivFun.symm (fun i => b.repr (v a) i))) = U
    rw [he, hv]

theorem finite_card_heightBoundedSubspaces (m H : ℕ) :
    (heightBoundedSubspaces b m H).Finite ∧
      (heightBoundedSubspaces b m H).ncard ≤ ((2 * H + 1) * (H + 1)) ^ (m * Fintype.card ι) := by
  let S : Set (Fin m × ι → ℚ) := {c | ∀ z, RationalHeightLE (c z) H}
  obtain ⟨hfin, hcard⟩ := finite_card_bounded_height_arrays S H (fun _ hc => hc)
  refine ⟨hfin.image (coordinateArraySpan b m), ?_⟩
  have hh := (Set.ncard_image_le (f := coordinateArraySpan b m) hfin).trans hcard
  rw [Fintype.card_prod, Fintype.card_fin] at hh
  exact hh

section Lie

variable {A : Type*} [LieRing A] [LieAlgebra ℚ A] (e : Basis ι ℚ A)

noncomputable def heightBoundedLieSubalgebras (m H : ℕ) : Set (LieSubalgebra ℚ A) :=
  {K | K.toSubmodule ∈ heightBoundedSubspaces e m H}

theorem finite_card_heightBoundedLieSubalgebras (m H : ℕ) :
    (heightBoundedLieSubalgebras e m H).Finite ∧
      (heightBoundedLieSubalgebras e m H).ncard ≤
        ((2 * H + 1) * (H + 1)) ^ (m * Fintype.card ι) := by
  classical
  obtain ⟨hfin, hcard⟩ := finite_card_heightBoundedSubspaces e m H
  let f : heightBoundedLieSubalgebras e m H → heightBoundedSubspaces e m H :=
    fun K => ⟨K.val.toSubmodule, K.property⟩
  have hf : Function.Injective f := by
    intro K J h
    exact Subtype.ext (LieSubalgebra.toSubmodule_injective (congrArg Subtype.val h))
  let : Fintype (heightBoundedSubspaces e m H) := hfin.fintype
  let : Finite (heightBoundedLieSubalgebras e m H) := Finite.of_injective f hf
  have hc := Nat.card_le_card_of_injective f hf
  refine ⟨Set.toFinite _, ?_⟩
  exact (show (heightBoundedLieSubalgebras e m H).ncard ≤ (heightBoundedSubspaces e m H).ncard by
    simpa only [Nat.card_coe_set_eq] using hc).trans hcard

end Lie
end Erdos3

end

section

namespace Erdos3

open Module

variable {ι η L : Type*} [Fintype ι] [AddCommGroup L] [Module ℚ L]
  (e : Basis ι ℚ L) (K : Submodule ℚ L)

theorem exists_bounded_submodule_ambient_spanning (v : η → L)
    (hspan : Submodule.span ℚ (Set.range v) = K) {H : ℕ} (hH : 1 ≤ H)
    (hv : ∀ a i, RationalHeightLE (e.repr (v a) i) H) :
    ∃ w : Fin (Fintype.card ι) → L,
      Submodule.span ℚ (Set.range w) = K ∧
        ∀ a i, RationalHeightLE (e.repr (w a) i) H := by
  classical
  let : FiniteDimensional ℚ L := e.finiteDimensional_of_finite
  obtain ⟨b, hb⟩ := exists_bounded_submodule_basis_from_spanning e K v hspan hv
  have hr : finrank ℚ K ≤ Fintype.card ι := by
    simpa only [finrank_eq_card_basis e] using K.finrank_le
  let w : Fin (Fintype.card ι) → L := fun a =>
    if ha : a.val < finrank ℚ K then (b ⟨a.val, ha⟩ : L) else 0
  have hw (i : Fin (finrank ℚ K)) :
      w ⟨i.val, lt_of_lt_of_le i.isLt hr⟩ = (b i : L) := by
    simp only [w, dite_eq_left i.isLt]
  refine ⟨w, ?_, ?_⟩
  · apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro x ⟨a, rfl⟩
      dsimp only [w]
      split_ifs with ha
      · exact (b ⟨a.val, ha⟩).property
      · exact K.zero_mem
    · have htop : (⊤ : Submodule ℚ K) ≤
          (Submodule.span ℚ (Set.range w)).comap K.subtype := by
        rw [← b.span_eq]
        apply Submodule.span_le.mpr
        rintro y ⟨i, rfl⟩
        change (b i : L) ∈ Submodule.span ℚ (Set.range w)
        rw [← hw i]
        exact Submodule.subset_span ⟨_, rfl⟩
      intro x hx
      exact htop (show (⟨x, hx⟩ : K) ∈ (⊤ : Submodule ℚ K) by trivial)
  · intro a i
    dsimp only [w]
    split_ifs with ha
    · exact hb ⟨a.val, ha⟩ i
    · simpa only [map_zero, Finsupp.zero_apply] using rationalHeightLE_zero hH

theorem bounded_submodule_spanning_mem_candidates (v : η → L)
    (hspan : Submodule.span ℚ (Set.range v) = K) {H : ℕ} (hH : 1 ≤ H)
    (hv : ∀ a i, RationalHeightLE (e.repr (v a) i) H) :
    K ∈ heightBoundedSubspaces e (Fintype.card ι) H := by
  obtain ⟨w, hw, hh⟩ := exists_bounded_submodule_ambient_spanning e K v hspan hH hv
  exact (mem_heightBoundedSubspaces e (Fintype.card ι) H K).mpr ⟨w, hw, hh⟩

end Erdos3

end

section

namespace Erdos3

open Module
open scoped BigOperators

end Erdos3

end

end OAI
