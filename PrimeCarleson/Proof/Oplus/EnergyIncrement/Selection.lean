module

public import PrimeCarleson.Proof.Oplus.EnergyIncrement.Basic

/-!
# The selection algorithm of the energy increment ([O+] L1449-L1500)

Source: [O+] `energyincrementprop`, L1451–L1498 (L1449-L1500): "If `energy(𝔓) ≤ e/2` no tree is
chosen. If `energy(𝔓) ≥ e/2` there is an `l`-overlapping tree `S ⊂ 𝔓` with
`(1/|I_S|) ∑_{P ∈ S} |⟨f, φ_P⟩|² ≥ e²/4` (shaslargeenergy). There is only a finite number of such
trees and as `S₁` we choose one for which the top datum `ξ_S` is maximal. Let `T₁` be the tree in
`𝔓` with top data `(ξ_{S₁}, I_{S₁})` which is maximal with respect to inclusion. Suppose `S_k, T_k`
have been chosen for `k ≤ j`. Set `𝔓_j = 𝔓 ∖ ⋃_{k ≤ j} T_k`. If `energy(𝔓_j) ≤ e/2` we terminate.
Otherwise we choose an `l`-overlapping tree `S ⊂ 𝔓_j` with (shaslargeenergy) of maximal top
frequency (in `𝒳_top`) and label it `S_{j+1}`; `T_{j+1}` is the maximal tree in `𝔓_j` with top data
`(ξ_{S_{j+1}}, I_{S_{j+1}})`. This process stops since each `T_j` is nonempty and `𝔓` is finite."

The recursion is on the cardinality of the finite family `Q`. The algorithm is recorded by
`IsSelection`: sequences `S, T : ℕ → MultitileTree ρ` (indices `< n` are meaningful), where
`remainingFamily 𝔓 T j = 𝔓 ∖ ⋃_{k < j} T_k` (so `𝔓_j` of the text is `remainingFamily 𝔓 T (j+1)`)
and the four clauses are: `S_j` is a large `l`-overlapping tree in the remaining family; its top
frequency is maximal among such trees (the finite set `𝒳_top` makes the maximum exist,
`finite_Xtop`); `T_j` is the maximal tree with the top data of `S_j`; the process has stopped at
`n`. `exists_selection` is the existence statement. Consequences used later (the properties of the
output that the source leaves implicit, L1614-L1621, L1827-L1830, L1851-L1852): `S_j ⊂ T_j`,
`I_{T_j} = I_{S_j}`, the `T_j` are pairwise disjoint and `S_k` is disjoint from `T_j` for `j < k`,
the top frequencies are non-increasing, and the maximality of the trees `T_j`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

section Remaining

variable {ρ : Idx}

open Classical in
/-- The collection `𝔓 ∖ ⋃_{k < j} T_k` of multitiles not yet used by the first `j` trees. -/
def remainingFamily (𝔓 : Finset (Multitile ρ)) (T : ℕ → MultitileTree ρ) (j : ℕ) :
    Finset (Multitile ρ) :=
  𝔓.filter fun P => ∀ k < j, P ∉ (T k).T

/-- Membership in `remainingFamily`. -/
theorem mem_remainingFamily {𝔓 : Finset (Multitile ρ)} {T : ℕ → MultitileTree ρ} {j : ℕ}
    {P : Multitile ρ} : P ∈ remainingFamily 𝔓 T j ↔ P ∈ 𝔓 ∧ ∀ k < j, P ∉ (T k).T := by
  classical
  simp [remainingFamily]

/-- The remaining family shrinks. -/
theorem remainingFamily_anti {𝔓 : Finset (Multitile ρ)} {T : ℕ → MultitileTree ρ} {j k : ℕ}
    (h : j ≤ k) : remainingFamily 𝔓 T k ⊆ remainingFamily 𝔓 T j := fun _ hP => by
  obtain ⟨h1, h2⟩ := mem_remainingFamily.1 hP
  exact mem_remainingFamily.2 ⟨h1, fun i hi => h2 i (lt_of_lt_of_le hi h)⟩

/-- `remainingFamily 𝔓 T 0 = 𝔓`. -/
theorem remainingFamily_zero (𝔓 : Finset (Multitile ρ)) (T : ℕ → MultitileTree ρ) :
    remainingFamily 𝔓 T 0 = 𝔓 := by
  ext P
  simp [mem_remainingFamily]

/-- The tail of `ℕ`-indexed sequences. -/
theorem forall_lt_succ_iff {p : ℕ → Prop} {j : ℕ} : (∀ k < j + 1, p k) ↔ p 0 ∧ ∀ k < j, p (k + 1) :=
  ⟨fun h => ⟨h 0 (Nat.succ_pos _), fun k hk => h (k + 1) (Nat.succ_lt_succ hk)⟩,
    fun ⟨h0, h⟩ k hk => by
      cases k with
      | zero => exact h0
      | succ k => exact h k (Nat.lt_of_succ_lt_succ hk)⟩

/-- Prepending an element to a sequence. -/
def consSeq {α : Type*} (a : α) (g : ℕ → α) : ℕ → α
  | 0 => a
  | i + 1 => g i

@[simp] theorem consSeq_zero {α : Type*} (a : α) (g : ℕ → α) : consSeq a g 0 = a := rfl

@[simp] theorem consSeq_succ {α : Type*} (a : α) (g : ℕ → α) (i : ℕ) :
    consSeq a g (i + 1) = g i := rfl

/-- Prepending a step to a sequence of steps. -/
theorem remainingFamily_cons (Q : Finset (Multitile ρ)) (T₁ : MultitileTree ρ)
    (T' : ℕ → MultitileTree ρ) (j : ℕ) :
    remainingFamily Q (consSeq T₁ T') (j + 1) = remainingFamily (Q \ T₁.T) T' j := by
  ext P
  simp only [mem_remainingFamily, Finset.mem_sdiff]
  rw [forall_lt_succ_iff (p := fun k => P ∉ (consSeq T₁ T' k).T)]
  simp only [consSeq_zero, consSeq_succ]
  tauto

/-- A multitile of the family remaining after `k` steps is not in `T_j` for `j < k`. -/
theorem not_mem_of_mem_remainingFamily {𝔓 : Finset (Multitile ρ)} {T : ℕ → MultitileTree ρ}
    {j k : ℕ} (hjk : j < k) {P : Multitile ρ} (hP : P ∈ remainingFamily 𝔓 T k) :
    P ∉ (T j).T :=
  (mem_remainingFamily.1 hP).2 j hjk

/-- The family left after `n` steps is `𝔓 ∖ ⋃_{j < n} T_j`. -/
theorem coe_remainingFamily {𝔓 : Finset (Multitile ρ)} {T : ℕ → MultitileTree ρ} {n : ℕ} :
    (remainingFamily 𝔓 T n : Set (Multitile ρ)) = (𝔓 : Set (Multitile ρ)) \
      ⋃ j ∈ Finset.range n, ((T j).T : Set (Multitile ρ)) := by
  ext P
  simp only [Finset.mem_coe, mem_remainingFamily, mem_sdiff, mem_iUnion, Finset.mem_range,
    exists_prop, not_exists, not_and]

end Remaining

section Selection

variable {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ : ℝ} {M : ℤ} {ch : ProfileChoice} {f : ℝ → ℂ}
  {e : ℝ}

open Classical in
/-- The maximal tree in `Q` with the top data of `S`: all `P ∈ Q` with `I ⊂ I_S` and
`ω_S ⊂ ω_m(P)` (the union of all trees in `Q` with these top data, L1255-L1259). -/
def maximalTree (C₂ : ℝ) (Q : Finset (Multitile ρ)) (S : MultitileTree ρ) : MultitileTree ρ :=
  ⟨Q.filter fun P => P.I.toSet ⊆ S.I.toSet ∧ S.ωT C₂ ⊆ P.ωm C₂, S.I, S.ξ⟩

/-- Membership in the maximal tree. -/
theorem mem_maximalTree {Q : Finset (Multitile ρ)} {S : MultitileTree ρ} {P : Multitile ρ} :
    P ∈ (maximalTree C₂ Q S).T ↔ P ∈ Q ∧ P.I.toSet ⊆ S.I.toSet ∧ S.ωT C₂ ⊆ P.ωm C₂ := by
  classical
  simp [maximalTree]

/-- The maximal tree with the top data of a tree `S` is a tree. -/
theorem maximalTree_isTree {Q : Finset (Multitile ρ)} {S : MultitileTree ρ}
    (hS : S.IsTree C₁ C₂ M) : (maximalTree C₂ Q S).IsTree C₁ C₂ M := by
  refine ⟨hS.top_subset, hS.ξ_mem, fun P hP => (mem_maximalTree.1 hP).2.1, fun P hP => ?_⟩
  exact (mem_maximalTree.1 hP).2.2

/-- A tree `S ⊂ Q` is contained in the maximal tree with its top data. -/
theorem subset_maximalTree {Q : Finset (Multitile ρ)} {S : MultitileTree ρ}
    (hS : S.IsTree C₁ C₂ M) (hQ : (S.T : Set (Multitile ρ)) ⊆ Q) :
    S.T ⊆ (maximalTree C₂ Q S).T := fun P hP =>
  mem_maximalTree.2 ⟨hQ hP, hS.time P hP, hS.freq P hP⟩

/-- The maximal tree has the top data of `S`. -/
@[simp] theorem maximalTree_I (Q : Finset (Multitile ρ)) (S : MultitileTree ρ) :
    (maximalTree C₂ Q S).I = S.I := rfl

/-- The maximal tree has the top data of `S`. -/
@[simp] theorem maximalTree_ξ (Q : Finset (Multitile ρ)) (S : MultitileTree ρ) :
    (maximalTree C₂ Q S).ξ = S.ξ := rfl

/-- `S` is an `l`-overlapping tree in `Q` satisfying (shaslargeenergy):
`(1/|I_S|) ∑_{P ∈ S} |⟨f, φ_P⟩|² ≥ e²/4` (L1456-L1459). -/
structure IsLargeTree (C₁ C₂ : ℝ) (M : ℤ) (ch : ProfileChoice) (f : ℝ → ℂ) (e : ℝ)
    (Q : Set (Multitile ρ)) (S : MultitileTree ρ) : Prop where
  isTree : S.IsTree C₁ C₂ M
  overlapping : S.IsOverlapping C₂
  subset : (S.T : Set (Multitile ρ)) ⊆ Q
  large : e ^ 2 / 4 * S.I.length ≤ ∑ P ∈ S.T, ‖P.coeff ch f‖ ^ 2

/-- Being a large tree in `Q` is monotone in `Q`. -/
theorem IsLargeTree.mono {Q Q' : Set (Multitile ρ)} {S : MultitileTree ρ}
    (h : IsLargeTree C₁ C₂ M ch f e Q S) (hQ : Q ⊆ Q') : IsLargeTree C₁ C₂ M ch f e Q' S :=
  ⟨h.isTree, h.overlapping, h.subset.trans hQ, h.large⟩

/-- A large tree is nonempty (for `e > 0`). -/
theorem IsLargeTree.nonempty {Q : Set (Multitile ρ)} {S : MultitileTree ρ}
    (h : IsLargeTree C₁ C₂ M ch f e Q S) (he : 0 < e) : S.T.Nonempty := by
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  have := h.large
  rw [hne, Finset.sum_empty] at this
  have hI := S.I.length_pos
  nlinarith [sq_nonneg e, mul_pos (by positivity : 0 < e ^ 2 / 4) hI]

/-- **The output of the selection algorithm** (L1449-L1500): `n` steps with the trees `S_j, T_j`
(`j < n`) chosen successively in `𝔓`; `remainingFamily 𝔓 T j` is `𝔓 ∖ ⋃_{k < j} T_k`. -/
structure IsSelection (C₁ C₂ : ℝ) (M : ℤ) (ch : ProfileChoice) (f : ℝ → ℂ) (e : ℝ)
    (𝔓 : Finset (Multitile ρ)) (n : ℕ) (S T : ℕ → MultitileTree ρ) : Prop where
  /-- `S_j` is an `l`-overlapping tree in the remaining family with (shaslargeenergy). -/
  large : ∀ j < n, IsLargeTree C₁ C₂ M ch f e (remainingFamily 𝔓 T j : Set (Multitile ρ)) (S j)
  /-- The top frequency of `S_j` is maximal among all such trees. -/
  xi_max : ∀ j < n, ∀ S' : MultitileTree ρ,
    IsLargeTree C₁ C₂ M ch f e (remainingFamily 𝔓 T j : Set (Multitile ρ)) S' → S'.ξ ≤ (S j).ξ
  /-- `T_j` is the inclusion-maximal tree in the remaining family with the top data of `S_j`. -/
  tree_eq : ∀ j < n, T j = maximalTree C₂ (remainingFamily 𝔓 T j) (S j)
  /-- The process stops: `energy(𝔓 ∖ ⋃_{k < n} T_k) ≤ e/2`. -/
  stop : energy C₁ C₂ M ch f (remainingFamily 𝔓 T n : Set (Multitile ρ)) ≤
    ENNReal.ofReal (e / 2)

/-- **Existence of the selection** (L1449-L1500): for every finite family `Q` and `e > 0` the
algorithm terminates. The maximal top frequency exists because `𝒳_top` is finite. -/
theorem exists_selection (he : 0 < e) (Q : Finset (Multitile ρ)) :
    ∃ (n : ℕ) (S T : ℕ → MultitileTree ρ), IsSelection C₁ C₂ M ch f e Q n S T := by
  classical
  induction Q using Finset.strongInduction with
  | H Q ih =>
    by_cases hQ : energy C₁ C₂ M ch f (Q : Set (Multitile ρ)) ≤ ENNReal.ofReal (e / 2)
    · refine ⟨0, fun _ => ⟨∅, ⟨0, 0⟩, 0⟩, fun _ => ⟨∅, ⟨0, 0⟩, 0⟩, ?_⟩
      refine ⟨fun j hj => absurd hj (Nat.not_lt_zero _), fun j hj => absurd hj (Nat.not_lt_zero _),
        fun j hj => absurd hj (Nat.not_lt_zero _), ?_⟩
      rw [remainingFamily_zero]; exact hQ
    · rw [not_le] at hQ
      obtain ⟨S₀, hS₀⟩ := exists_large_tree he hQ
      have h𝔏 : IsLargeTree C₁ C₂ M ch f e (Q : Set (Multitile ρ)) S₀ :=
        ⟨hS₀.1, hS₀.2.1, hS₀.2.2.1, hS₀.2.2.2⟩
      -- the maximal top frequency
      set Ξ : Set ℝ := (fun S : MultitileTree ρ => S.ξ) ''
        {S | IsLargeTree C₁ C₂ M ch f e (Q : Set (Multitile ρ)) S} with hΞ
      have hΞfin : Ξ.Finite := (finite_Xtop C₁ M).subset (by
        rintro _ ⟨S, hS, rfl⟩
        exact hS.isTree.ξ_mem)
      obtain ⟨_, ⟨S₁, hS₁, rfl⟩, hmax⟩ := Set.exists_max_image Ξ id hΞfin ⟨_, ⟨S₀, h𝔏, rfl⟩⟩
      have hS₁max : ∀ S' : MultitileTree ρ,
          IsLargeTree C₁ C₂ M ch f e (Q : Set (Multitile ρ)) S' → S'.ξ ≤ S₁.ξ :=
        fun S' hS' => hmax S'.ξ ⟨S', hS', rfl⟩
      set T₁ : MultitileTree ρ := maximalTree C₂ Q S₁ with hT₁
      have hST : S₁.T ⊆ T₁.T := subset_maximalTree hS₁.isTree hS₁.subset
      have hne : S₁.T.Nonempty := hS₁.nonempty he
      have hlt : Q \ T₁.T ⊂ Q := by
        refine Finset.sdiff_ssubset (fun P hP => (mem_maximalTree.1 hP).1) ?_
        obtain ⟨P, hP⟩ := hne
        exact ⟨P, hST hP⟩
      obtain ⟨n', S', T', hsel⟩ := ih (Q \ T₁.T) hlt
      refine ⟨n' + 1, consSeq S₁ S', consSeq T₁ T', ?_⟩
      refine ⟨fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, ?_⟩
      · cases j with
        | zero =>
          rw [remainingFamily_zero]; exact hS₁
        | succ j =>
          have := hsel.large j (Nat.lt_of_succ_lt_succ hj)
          rw [remainingFamily_cons, consSeq_succ]; exact this
      · cases j with
        | zero =>
          rw [remainingFamily_zero]; exact hS₁max
        | succ j =>
          have := hsel.xi_max j (Nat.lt_of_succ_lt_succ hj)
          rw [remainingFamily_cons, consSeq_succ]; exact this
      · cases j with
        | zero =>
          rw [remainingFamily_zero]; rfl
        | succ j =>
          have := hsel.tree_eq j (Nat.lt_of_succ_lt_succ hj)
          rw [remainingFamily_cons, consSeq_succ, consSeq_succ]; exact this
      · rw [remainingFamily_cons]; exact hsel.stop

/-! ### Consequences of the selection -/

namespace IsSelection

variable {𝔓 : Finset (Multitile ρ)} {n : ℕ} {S T : ℕ → MultitileTree ρ}
  (sel : IsSelection C₁ C₂ M ch f e 𝔓 n S T)
include sel

/-- `S_j` is a tree. -/
theorem S_isTree {j : ℕ} (hj : j < n) : (S j).IsTree C₁ C₂ M := (sel.large j hj).isTree

/-- `S_j` is `l`-overlapping. -/
theorem S_overlapping {j : ℕ} (hj : j < n) : (S j).IsOverlapping C₂ := (sel.large j hj).overlapping

/-- `S_j ⊂ 𝔓 ∖ ⋃_{k < j} T_k`. -/
theorem S_subset_rem {j : ℕ} (hj : j < n) {P : Multitile ρ} (hP : P ∈ (S j).T) :
    P ∈ remainingFamily 𝔓 T j := (sel.large j hj).subset hP

/-- `T_j ⊂ 𝔓 ∖ ⋃_{k < j} T_k`. -/
theorem T_subset_rem {j : ℕ} (hj : j < n) {P : Multitile ρ} (hP : P ∈ (T j).T) :
    P ∈ remainingFamily 𝔓 T j := by
  rw [sel.tree_eq j hj] at hP
  exact (mem_maximalTree.1 hP).1

/-- `S_j ⊂ T_j`. -/
theorem S_subset_T {j : ℕ} (hj : j < n) : (S j).T ⊆ (T j).T := by
  rw [sel.tree_eq j hj]
  exact subset_maximalTree (sel.S_isTree hj) (sel.large j hj).subset

/-- `I_{T_j} = I_{S_j}`. -/
theorem T_I {j : ℕ} (hj : j < n) : (T j).I = (S j).I := by
  rw [sel.tree_eq j hj]; rfl

/-- `T_j` is a tree. -/
theorem T_isTree {j : ℕ} (hj : j < n) : (T j).IsTree C₁ C₂ M := by
  rw [sel.tree_eq j hj]
  exact maximalTree_isTree (sel.S_isTree hj)

/-- `T_j` and `S_k` are disjoint for `j < k`. -/
theorem disjoint_T_S {j k : ℕ} (hjk : j < k) (hk : k < n) : Disjoint (T j).T (S k).T :=
  Finset.disjoint_left.2 fun _ hPj hPk =>
    not_mem_of_mem_remainingFamily hjk (sel.S_subset_rem hk hPk) hPj

/-- The trees `S_j` are pairwise disjoint (`S_j ⊂ T_j`). -/
theorem disjoint_S_S {j k : ℕ} (hj : j < n) (hk : k < n) (hjk : j ≠ k) :
    Disjoint (S j).T (S k).T := by
  rcases lt_or_gt_of_ne hjk with h | h
  · exact (sel.disjoint_T_S h hk).mono_left (sel.S_subset_T hj)
  · exact ((sel.disjoint_T_S h hj).mono_left (sel.S_subset_T hk)).symm

/-- The top frequencies are non-increasing: `ξ_{S_k} ≤ ξ_{S_j}` for `j ≤ k` (L1829-L1830). -/
theorem xi_le {j k : ℕ} (hjk : j ≤ k) (hk : k < n) : (S k).ξ ≤ (S j).ξ :=
  sel.xi_max j (lt_of_le_of_lt hjk hk) (S k)
    ((sel.large k hk).mono (fun _ hP => remainingFamily_anti hjk hP))

/-- **Maximality of `T_j`**: a multitile of the remaining family with `I ⊂ I_{S_j}` and
`ω_{S_j} ⊂ ω_m(P)` belongs to `T_j`. -/
theorem mem_T_of_mem_rem {j : ℕ} (hj : j < n) {P : Multitile ρ}
    (hP : P ∈ remainingFamily 𝔓 T j) (hI : P.I.toSet ⊆ (S j).I.toSet)
    (hω : (S j).ωT C₂ ⊆ P.ωm C₂) : P ∈ (T j).T := by
  rw [sel.tree_eq j hj]
  exact mem_maximalTree.2 ⟨hP, hI, hω⟩

/-- Each `S_j` is nonempty. -/
theorem S_nonempty (he : 0 < e) {j : ℕ} (hj : j < n) : (S j).T.Nonempty :=
  (sel.large j hj).nonempty he

/-- The trees `T_j` are pairwise distinct. -/
theorem T_injOn (he : 0 < e) : Set.InjOn T (Set.Iio n) := by
  intro j hj k hk hjk
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · obtain ⟨P, hP⟩ := sel.S_nonempty he (show k < n from hk)
    have h1 : P ∈ (T k).T := sel.S_subset_T hk hP
    have h2 : P ∈ (T j).T := by rw [hjk]; exact h1
    exact Finset.disjoint_left.1 (sel.disjoint_T_S h hk) h2 hP
  · obtain ⟨P, hP⟩ := sel.S_nonempty he (show j < n from hj)
    have h1 : P ∈ (T j).T := sel.S_subset_T hj hP
    have h2 : P ∈ (T k).T := by rw [← hjk]; exact h1
    exact Finset.disjoint_left.1 (sel.disjoint_T_S h hj) h2 hP

end IsSelection

end Selection

end PrimeCarleson.Proof.Oplus
