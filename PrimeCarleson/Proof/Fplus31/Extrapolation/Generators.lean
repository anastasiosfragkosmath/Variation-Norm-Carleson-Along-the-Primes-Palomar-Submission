module

public import PrimeCarleson.Proof.Fplus31.Extrapolation.Datum
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Prod

/-!
# Generators of `K = W + D` (the extrapolation step)

Part of the abstract extrapolation (the extrapolation step of the iteration of `C2/CMain.lean`,
proof of [F+] Proposition 3.1). The subalgebra `K = W + D` produced by the extrapolation step is
spanned by at most `d = dim g` vectors of coordinate log-height at most `p`, "chosen from the
generators of `W` and the structure-constant vectors (a maximal independent subfamily)":

* `exists_fin_family`: a finite family spans the same space as a family of exactly `dim V` vectors
  that are zero or members of the original family (a maximal independent subfamily, padded by
  zeros);
* `derived_eq_span`: `D = β(g₁, g₁)` is spanned by the structure-constant vectors;
* `GradedSubalg.gen_plusDerived`: `W.Gen p` and the height bound on the structure constants give
  `(W + D).Gen p`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

/-- A family spans the same space as a maximal independent subfamily, padded by zeros to length
`d = dim V`. -/
theorem exists_fin_family {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    {N : Type*} (g : N → V) (d : ℕ) (hd : Module.finrank ℚ V = d) :
    ∃ v : Fin d → V, Submodule.span ℚ (Set.range v) = Submodule.span ℚ (Set.range g) ∧
      ∀ r, v r = 0 ∨ ∃ n, v r = g n := by
  classical
  obtain ⟨b, hbT, hbspan, hbli⟩ := exists_linearIndependent ℚ (Set.range g)
  have : Finite b := hbli.finite
  have : Fintype b := Fintype.ofFinite b
  have hcard : Fintype.card b ≤ d := hd ▸ hbli.fintype_card_le_finrank
  let e : b ≃ Fin (Fintype.card b) := Fintype.equivFin b
  let v : Fin d → V := fun r =>
    if h : r.val < Fintype.card b then ((e.symm ⟨r.val, h⟩ : b) : V) else 0
  have hv_pos : ∀ (r : Fin d) (h : r.val < Fintype.card b),
      v r = ((e.symm ⟨r.val, h⟩ : b) : V) := by
    intro r h
    simp only [v]
    split_ifs
    rfl
  have hv_neg : ∀ r : Fin d, ¬r.val < Fintype.card b → v r = 0 := by
    intro r h
    simp only [v]
    split_ifs
    rfl
  refine ⟨v, ?_, ?_⟩
  · apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨r, rfl⟩
      by_cases h : r.val < Fintype.card b
      · rw [hv_pos r h, SetLike.mem_coe, ← hbspan]
        exact Submodule.subset_span (e.symm ⟨r.val, h⟩).2
      · rw [hv_neg r h]
        exact Submodule.zero_mem _
    · rw [← hbspan]
      apply Submodule.span_mono
      intro x hx
      have hlt : (e ⟨x, hx⟩).val < Fintype.card b := (e ⟨x, hx⟩).2
      refine ⟨⟨(e ⟨x, hx⟩).val, lt_of_lt_of_le hlt hcard⟩, ?_⟩
      rw [hv_pos _ hlt]
      simp
  · intro r
    by_cases h : r.val < Fintype.card b
    · right
      obtain ⟨n, hn⟩ := hbT (e.symm ⟨r.val, h⟩).2
      exact ⟨n, by rw [hv_pos r h, ← hn]⟩
    · left
      exact hv_neg r h

variable {ι₁ ι₂ : Type*} [Fintype ι₁] {a : Step2Algebra ι₁ ι₂}

/-- `D = β(g₁, g₁)` is spanned by the vectors `β(b_i, b_j)` of structure constants. -/
theorem derived_eq_span (a : Step2Algebra ι₁ ι₂) :
    derived a = Submodule.span ℚ (Set.range fun ij : ι₁ × ι₁ => fun k => a.c ij.1 ij.2 k) := by
  classical
  apply le_antisymm
  · rw [derived, Submodule.span_le]
    rintro _ ⟨x, y, rfl⟩
    have : a.br x y = ∑ ij : ι₁ × ι₁, (x ij.1 * y ij.2) • (fun k => a.c ij.1 ij.2 k) := by
      ext k
      simp [Step2Algebra.br_apply, Fintype.sum_prod_type]
    rw [SetLike.mem_coe, this]
    exact Submodule.sum_mem _ fun ij _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨ij, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨ij, rfl⟩
    have : (fun k => a.c ij.1 ij.2 k) = a.br (Pi.single ij.1 1) (Pi.single ij.2 1) := by
      ext k
      simp [Step2Algebra.br_apply, Pi.single_apply]
    change (fun k => a.c ij.1 ij.2 k) ∈ derived a
    rw [this]
    exact br_mem_derived _ _

variable [Fintype ι₂]

/-- **Generators of `K = W + D`.**  If `W` is spanned by `d` vectors of coordinate log-height at
most `p` and the structure constants have log-height at most `p` (`p ≥ 0`), then so is
`W + D`: choose a maximal independent subfamily among the generators of `W` and the vectors
`(0, β(b_i, b_j))`. -/
theorem GradedSubalg.gen_plusDerived {p : ℝ} (hp : 0 ≤ p) (W : GradedSubalg a) (hW : W.Gen p)
    (hc : ∀ i j k, ratLogHeight (a.c i j k) ≤ p) : W.plusDerived.Gen p := by
  obtain ⟨v, hv, hh⟩ := hW
  let g : Fin (Fintype.card ι₁ + Fintype.card ι₂) ⊕ (ι₁ × ι₁) → (ι₁ → ℚ) × (ι₂ → ℚ) :=
    Sum.elim v fun ij => ((0 : ι₁ → ℚ), fun k => a.c ij.1 ij.2 k)
  have hd : Module.finrank ℚ ((ι₁ → ℚ) × (ι₂ → ℚ)) = Fintype.card ι₁ + Fintype.card ι₂ := by
    rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card]
  obtain ⟨v', hv', hmem⟩ := exists_fin_family g _ hd
  refine ⟨v', ?_, ?_⟩
  · rw [hv']
    have hrange : Set.range g = Set.range v ∪ Set.range fun ij : ι₁ × ι₁ =>
        (((0 : ι₁ → ℚ), fun k => a.c ij.1 ij.2 k) : (ι₁ → ℚ) × (ι₂ → ℚ)) := by
      ext x
      simp only [g, Set.mem_range, Set.mem_union, Sum.exists, Sum.elim_inl, Sum.elim_inr]
    rw [hrange, Submodule.span_union, hv]
    unfold GradedSubalg.plusDerived
    congr 1
    rw [derived_eq_span, ← Submodule.map_inr, Submodule.map_span, ← Set.range_comp]
    rfl
  · intro r
    rcases hmem r with h0 | ⟨n, hn⟩
    · rw [h0]
      simp [ratLogHeight_zero, hp]
    · rw [hn]
      rcases n with n | ij
      · exact hh n
      · refine ⟨fun i => ?_, fun k => hc _ _ k⟩
        simp [g, ratLogHeight_zero, hp]

end PrimeCarleson.Proof.Fplus31
