module

public import PrimeCarleson.Proof.Oplus.TreeLarge.LargeIntervals

/-!
# Reduction of the tree estimate to special trees ([O+] L2054-L2076)

Source: [O+] `treeestimate`, L2054–L2076: "Every tree can be split into an
`l`-lacunary tree and an `l`-overlapping tree [...]
By breaking up `T` into a bounded number of subtrees we may assume that for each `P ∈ T`
`ξ_T ∈ ω_l + j|ω_l|` for some integer `j` with `|j| ≤ C₂` [...] either `ξ_T ≤ inf ω_l` for every `P`
(`l^-`-overlapping) or `ξ_T > inf ω_l` for every `P` (`l^+`-overlapping)."

`exists_special_decomposition`: for a tree `𝒯` the multitiles are labelled by
`lab P = none` if `ξ_T ∉ C₂ ω_l(P)` and `lab P = some (j, b)` with `j = ⌊(ξ_T - inf ω_l)/|ω_l|⌋` and
`b = (ξ_T ≤ inf ω_l)` otherwise; there are at most `1 + 2(2⌈C₂⌉ + 1)` labels, and the multitiles of
one label form a tree with the same top data which is `l`-lacunary (`none`), or `l`-overlapping with
(jconsolidation) for the integer `j` and `l^±` (the source's "one `j` per subtree" reading, L2059).
The index `|j| ≤ C₂` is automatic from `ξ_T ∈ C₂ ω_l`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

section Reduction

variable {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ C₃ : ℝ} {M : ℤ}

/-- The subtree of the multitiles of `𝒯` satisfying a predicate, with the same top data. -/
def MultitileTree.restrict (𝒯 : MultitileTree ρ) (p : Multitile ρ → Prop) [DecidablePred p] :
    MultitileTree ρ :=
  ⟨𝒯.T.filter p, 𝒯.I, 𝒯.ξ⟩

omit [Fact ρ.IsOneOrTwo] in
/-- The multitiles of a restricted tree. -/
@[simp] theorem MultitileTree.restrict_T (𝒯 : MultitileTree ρ) (p : Multitile ρ → Prop)
    [DecidablePred p] : (𝒯.restrict p).T = 𝒯.T.filter p := rfl

omit [Fact ρ.IsOneOrTwo] in
/-- The top interval of a restricted tree. -/
@[simp] theorem MultitileTree.restrict_I (𝒯 : MultitileTree ρ) (p : Multitile ρ → Prop)
    [DecidablePred p] : (𝒯.restrict p).I = 𝒯.I := rfl

omit [Fact ρ.IsOneOrTwo] in
/-- The top frequency of a restricted tree. -/
@[simp] theorem MultitileTree.restrict_ξ (𝒯 : MultitileTree ρ) (p : Multitile ρ → Prop)
    [DecidablePred p] : (𝒯.restrict p).ξ = 𝒯.ξ := rfl

/-- A sub-collection of the multitiles of a tree (with the same top data) is a tree. -/
theorem MultitileTree.IsTree.restrict {𝒯 : MultitileTree ρ} (h : 𝒯.IsTree C₁ C₂ M)
    (p : Multitile ρ → Prop) [DecidablePred p] : (𝒯.restrict p).IsTree C₁ C₂ M :=
  ⟨h.top_subset, h.ξ_mem, fun P hP => h.time P (Finset.mem_filter.1 hP).1,
    fun P hP => h.freq P (Finset.mem_filter.1 hP).1⟩

open Classical in
/-- The label of a multitile (L2054-L2071). -/
def treeLabel (C₂ : ℝ) (ξ : ℝ) (P : Multitile ρ) : Option (ℤ × Bool) :=
  if ξ ∈ P.ωlDil C₂ then
    some (⌊(ξ - (ρ.ωlDyadic P.ωu).left) / P.ωu.length⌋, decide (ξ ≤ (ρ.ωlDyadic P.ωu).left))
  else none

/-- **The reduction to special trees** ([O+] L2054-L2076): the multitiles of a tree split into at
most `1 + 2(2⌈C₂⌉ + 1)` classes, each of which is a special tree with the same top data. -/
theorem exists_special_decomposition (hC : AdmissibleConstants C₁ C₂ C₃) {𝒯 : MultitileTree ρ} :
    ∃ Λ : Finset (Option (ℤ × Bool)), Λ.card ≤ 1 + 2 * (2 * ⌈C₂⌉₊ + 1) ∧
      (∀ P ∈ 𝒯.T, treeLabel C₂ 𝒯.ξ P ∈ Λ) ∧
      ∀ l ∈ Λ, (𝒯.restrict fun P => treeLabel C₂ 𝒯.ξ P = l).IsSpecialJ C₂ := by
  classical
  have hC2 : 1 ≤ C₂ := by linarith [hC.one_le, hC.lt₁]
  set N₂ : ℕ := ⌈C₂⌉₊ with hN₂
  have hN₂C : C₂ ≤ N₂ := Nat.le_ceil _
  refine ⟨insert none ((Finset.Icc (-(N₂ : ℤ)) N₂ ×ˢ (Finset.univ : Finset Bool)).image some),
    ?_, ?_, ?_⟩
  · refine (Finset.card_insert_le _ _).trans ?_
    have := Finset.card_image_le (s := Finset.Icc (-(N₂ : ℤ)) N₂ ×ˢ (Finset.univ : Finset Bool))
      (f := Option.some)
    rw [Finset.card_product, Int.card_Icc] at this
    simp only [Finset.card_univ, Fintype.card_bool] at this
    have h2 : (N₂ : ℤ) + 1 - -(N₂ : ℤ) = 2 * N₂ + 1 := by ring
    rw [h2] at this
    have h3 : (2 * (N₂ : ℤ) + 1).toNat = 2 * N₂ + 1 := by omega
    rw [h3] at this
    omega
  · intro P hP
    unfold treeLabel
    split_ifs with h
    · refine Finset.mem_insert_of_mem (Finset.mem_image.2
        ⟨_, Finset.mem_product.2 ⟨?_, Finset.mem_univ _⟩, rfl⟩)
      have hL := P.ωu.length_pos
      rw [Multitile.ωlDil_eq] at h
      have e1 := Idx.left_ωlDyadic ρ P.ωu
      have hc := P.ωu.center_eq
      obtain ⟨h1, h2⟩ := h
      rw [Finset.mem_Icc]
      constructor
      · have : (1 - C₂) / 2 ≤ (𝒯.ξ - (ρ.ωlDyadic P.ωu).left) / P.ωu.length := by
          rw [le_div_iff₀ hL]
          nlinarith
        have h4 := Int.sub_one_lt_floor ((𝒯.ξ - (ρ.ωlDyadic P.ωu).left) / P.ωu.length)
        have : (-(N₂ : ℝ)) ≤ (⌊(𝒯.ξ - (ρ.ωlDyadic P.ωu).left) / P.ωu.length⌋ : ℝ) := by
          linarith
        exact_mod_cast this
      · have : (𝒯.ξ - (ρ.ωlDyadic P.ωu).left) / P.ωu.length < (C₂ + 1) / 2 := by
          rw [div_lt_iff₀ hL]
          nlinarith
        have h4 := Int.floor_le ((𝒯.ξ - (ρ.ωlDyadic P.ωu).left) / P.ωu.length)
        have : (⌊(𝒯.ξ - (ρ.ωlDyadic P.ωu).left) / P.ωu.length⌋ : ℝ) ≤ N₂ := by linarith
        exact_mod_cast this
    · exact Finset.mem_insert_self _ _
  · intro l _
    unfold MultitileTree.IsSpecialJ
    have hmem : ∀ P ∈ (𝒯.restrict fun P => treeLabel C₂ 𝒯.ξ P = l).T,
        treeLabel C₂ 𝒯.ξ P = l := fun P hP => (Finset.mem_filter.1 hP).2
    rcases l with _ | ⟨j, b⟩
    · left
      intro P hP h
      have h' : 𝒯.ξ ∈ P.ωlDil C₂ := h
      have := hmem P hP
      unfold treeLabel at this
      simp [h'] at this
    · right
      have key : ∀ P ∈ (𝒯.restrict fun P => treeLabel C₂ 𝒯.ξ P = some (j, b)).T,
          𝒯.ξ ∈ P.ωlDil C₂ ∧ ⌊(𝒯.ξ - (ρ.ωlDyadic P.ωu).left) / P.ωu.length⌋ = j ∧
            decide (𝒯.ξ ≤ (ρ.ωlDyadic P.ωu).left) = b := by
        intro P hP
        have hlab := hmem P hP
        unfold treeLabel at hlab
        split_ifs at hlab with h
        · simp only [Option.some.injEq, Prod.mk.injEq] at hlab
          exact ⟨h, hlab.1, hlab.2⟩
      refine ⟨fun P hP => by simpa using (key P hP).1, ?_, j, fun P hP => ?_⟩
      · rcases b with _ | _
        · left
          intro P hP
          have := (key P hP).2.2
          simp only [decide_eq_false_iff_not, not_le] at this
          exact this
        · right
          intro P hP
          have := (key P hP).2.2
          simpa using this
      · obtain ⟨-, hj, -⟩ := key P hP
        have hL := P.ωu.length_pos
        have h1 := Int.floor_le ((𝒯.ξ - (ρ.ωlDyadic P.ωu).left) / P.ωu.length)
        have h2 := Int.lt_floor_add_one ((𝒯.ξ - (ρ.ωlDyadic P.ωu).left) / P.ωu.length)
        rw [hj] at h1 h2
        rw [le_div_iff₀ hL] at h1
        rw [div_lt_iff₀ hL] at h2
        rw [P.ωl_eq_toSet_ωlDyadic Fact.out, Dyadic.mem_toSet, Dyadic.right_eq]
        have hlen : (ρ.ωlDyadic P.ωu).length = P.ωu.length := rfl
        rw [hlen]
        simp only [MultitileTree.restrict_ξ]
        constructor <;> nlinarith

end Reduction

end PrimeCarleson.Proof.Oplus
