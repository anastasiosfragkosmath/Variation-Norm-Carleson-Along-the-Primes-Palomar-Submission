module

public import PrimeCarleson.Proof.Oplus.DensityIncrement.Basic

/-!
# The selection algorithm of the density increment ([O+] L1913-L1929)

Source: [O+] `densityincrementprop`, L1913–L1929: "Suppose that trees `T_j, T_j^+, T_j^-` have
been chosen for `j = 1, …, k`. Let `𝔓_k = 𝔓 ∖ ⋃_{j ≤ k} T_j ∪ T_j^+ ∪ T_j^-`. If
`density(𝔓_k) ≤ den/2` we terminate. Otherwise we may find a nonempty tree `T ⊂ 𝔓_k` such that
(treehaslargedensity).
Choose `T_{k+1} ⊂ 𝔓_k` so that `|I_{T_{k+1}}|` is maximal among all nonempty trees contained in
`𝔓_k` which satisfy (treehaslargedensity), and so that `T_{k+1}` is the maximal, with respect to
inclusion, tree contained in `𝔓_k` with top data `(I_{T_{k+1}}, ξ_{T_{k+1}})`. Let `T^+_{k+1}`
be the maximal tree contained in `𝔓_k` with top data `(I_{T_{k+1}}, ξ_{T_{k+1}} + (C₂ -
1)/(2|I_{T_{k+1}}|))` and `T^-_{k+1}` the one with `ξ_{T_{k+1}} - (C₂ - 1)/(2|I_{T_{k+1}}|)`.
Since each `T_j` is nonempty and `𝔓` is finite, this process will eventually stop."

The recursion is on the cardinality of the finite family `Q` (as for the energy increment,
`EnergyIncrement/Selection.lean`). The algorithm is recorded by `IsDensitySelection`: sequences
`S, T, Tp, Tm : ℕ → MultitileTree ρ` (`Tp`, `Tm` are `T^+`, `T^-`; indices `< n` are
meaningful), `densityRemaining 𝔓 T Tp Tm j = 𝔓 ∖ ⋃_{k < j} (T_k ∪ T_k^+ ∪ T_k^-)` (so `𝔓_k` of the
text is `densityRemaining … (k + 1)` when the text counts from `1`), and the clauses: `S_j` is a
dense tree in the remaining family; `|I_{S_j}|` is maximal among such trees; `T_j`, `T_j^±` are the
maximal trees in the remaining family with the (shifted) top data of `S_j`; the process has
stopped at `n`. `exists_density_selection` is the existence statement. The tree `T_j` is itself a
dense tree (the density integral depends on the top data only), `S_j ⊂ T_j`, so `T_j` is nonempty.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

section Remaining

variable {ρ : Idx}

open Classical in
/-- The collection `𝔓 ∖ ⋃_{k < j} (T_k ∪ T_k^+ ∪ T_k^-)` of multitiles not yet used by the first `j`
steps. -/
def densityRemaining (𝔓 : Finset (Multitile ρ)) (T Tp Tm : ℕ → MultitileTree ρ) (j : ℕ) :
    Finset (Multitile ρ) :=
  𝔓.filter fun P => ∀ k < j, P ∉ (T k).T ∧ P ∉ (Tp k).T ∧ P ∉ (Tm k).T

/-- Membership in `densityRemaining`. -/
theorem mem_densityRemaining {𝔓 : Finset (Multitile ρ)} {T Tp Tm : ℕ → MultitileTree ρ} {j : ℕ}
    {P : Multitile ρ} :
    P ∈ densityRemaining 𝔓 T Tp Tm j ↔
      P ∈ 𝔓 ∧ ∀ k < j, P ∉ (T k).T ∧ P ∉ (Tp k).T ∧ P ∉ (Tm k).T := by
  classical
  simp [densityRemaining]

/-- The remaining family is contained in `𝔓`. -/
theorem densityRemaining_subset (𝔓 : Finset (Multitile ρ)) (T Tp Tm : ℕ → MultitileTree ρ)
    (j : ℕ) : densityRemaining 𝔓 T Tp Tm j ⊆ 𝔓 := fun _ hP => (mem_densityRemaining.1 hP).1

/-- The remaining family shrinks. -/
theorem densityRemaining_anti {𝔓 : Finset (Multitile ρ)} {T Tp Tm : ℕ → MultitileTree ρ}
    {j k : ℕ} (h : j ≤ k) :
    densityRemaining 𝔓 T Tp Tm k ⊆ densityRemaining 𝔓 T Tp Tm j := fun _ hP => by
  obtain ⟨h1, h2⟩ := mem_densityRemaining.1 hP
  exact mem_densityRemaining.2 ⟨h1, fun i hi => h2 i (lt_of_lt_of_le hi h)⟩

/-- `densityRemaining 𝔓 T Tp Tm 0 = 𝔓`. -/
theorem densityRemaining_zero (𝔓 : Finset (Multitile ρ)) (T Tp Tm : ℕ → MultitileTree ρ) :
    densityRemaining 𝔓 T Tp Tm 0 = 𝔓 := by
  ext P
  simp [mem_densityRemaining]

/-- Prepending a step to the sequences of steps. -/
theorem densityRemaining_cons (Q : Finset (Multitile ρ)) (T₁ T₁p T₁m : MultitileTree ρ)
    (T Tp Tm : ℕ → MultitileTree ρ) (j : ℕ) :
    densityRemaining Q (consSeq T₁ T) (consSeq T₁p Tp) (consSeq T₁m Tm) (j + 1) =
      densityRemaining (Q \ (T₁.T ∪ T₁p.T ∪ T₁m.T)) T Tp Tm j := by
  ext P
  simp only [mem_densityRemaining, Finset.mem_sdiff, Finset.mem_union]
  rw [forall_lt_succ_iff (p := fun k => P ∉ (consSeq T₁ T k).T ∧ P ∉ (consSeq T₁p Tp k).T ∧
    P ∉ (consSeq T₁m Tm k).T)]
  simp only [consSeq_zero, consSeq_succ]
  tauto

/-- A multitile of the family remaining after `k` steps is not in the trees of step `j < k`. -/
theorem not_mem_of_mem_densityRemaining {𝔓 : Finset (Multitile ρ)}
    {T Tp Tm : ℕ → MultitileTree ρ} {j k : ℕ} (hjk : j < k) {P : Multitile ρ}
    (hP : P ∈ densityRemaining 𝔓 T Tp Tm k) :
    P ∉ (T j).T ∧ P ∉ (Tp j).T ∧ P ∉ (Tm j).T :=
  (mem_densityRemaining.1 hP).2 j hjk

/-- The family left after `n` steps is `𝔓 ∖ ⋃_{j < n} (T_j ∪ T_j^+ ∪ T_j^-)`. -/
theorem coe_densityRemaining {𝔓 : Finset (Multitile ρ)} {T Tp Tm : ℕ → MultitileTree ρ}
    {n : ℕ} :
    (densityRemaining 𝔓 T Tp Tm n : Set (Multitile ρ)) = (𝔓 : Set (Multitile ρ)) \
      ⋃ j ∈ Finset.range n, (((T j).T : Set (Multitile ρ)) ∪ (Tp j).T ∪ (Tm j).T) := by
  ext P
  simp only [Finset.mem_coe, mem_densityRemaining, mem_sdiff, mem_iUnion, Finset.mem_range,
    exists_prop, not_exists, not_and, mem_union]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun k hk h => ?_⟩
    obtain ⟨a, b, c⟩ := h2 k hk
    tauto
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun k hk => ?_⟩
    refine ⟨fun h => h2 k hk (Or.inl (Or.inl h)), fun h => h2 k hk (Or.inl (Or.inr h)),
      fun h => h2 k hk (Or.inr h)⟩

end Remaining

section Selection

variable {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ C₃ : ℝ} {M : ℤ} {r : ℝ} {L : Linearization r}
  {E : Set ℝ} {den : ℝ}

/-- **The output of the selection algorithm** (L1913-L1929): `n` steps with the trees `S_j`
(a dense tree of maximal `|I|`), `T_j`, `T_j^+ = Tp_j`, `T_j^- = Tm_j` (`j < n`) chosen
successively in `𝔓`; `densityRemaining 𝔓 T Tp Tm j` is `𝔓 ∖ ⋃_{k < j} (T_k ∪ T_k^+ ∪ T_k^-)`. -/
structure IsDensitySelection (C₁ C₂ : ℝ) (M : ℤ) (L : Linearization r) (E : Set ℝ) (den : ℝ)
    (𝔓 : Finset (Multitile ρ)) (n : ℕ) (S T Tp Tm : ℕ → MultitileTree ρ) : Prop where
  /-- `S_j` is a nonempty tree in the remaining family with (treehaslargedensity). -/
  dense : ∀ j < n, IsDenseTree C₁ C₂ M L E den
    (densityRemaining 𝔓 T Tp Tm j : Set (Multitile ρ)) (S j)
  /-- `|I_{S_j}|` is maximal among all such trees. -/
  I_max : ∀ j < n, ∀ S' : MultitileTree ρ, IsDenseTree C₁ C₂ M L E den
    (densityRemaining 𝔓 T Tp Tm j : Set (Multitile ρ)) S' → S'.I.length ≤ (S j).I.length
  /-- `T_j` is the inclusion-maximal tree in the remaining family with the top data of `S_j`. -/
  T_eq : ∀ j < n, T j = maximalTree C₂ (densityRemaining 𝔓 T Tp Tm j) (S j)
  /-- `T_j^+` is the maximal tree with top data `(I_{S_j}, ξ_{S_j} + (C₂ - 1)/(2|I_{S_j}|))`. -/
  Tp_eq : ∀ j < n, Tp j = maximalTree C₂ (densityRemaining 𝔓 T Tp Tm j) (shiftTree C₂ 1 (S j))
  /-- `T_j^-` is the maximal tree with top data `(I_{S_j}, ξ_{S_j} - (C₂ - 1)/(2|I_{S_j}|))`. -/
  Tm_eq : ∀ j < n, Tm j = maximalTree C₂ (densityRemaining 𝔓 T Tp Tm j) (shiftTree C₂ (-1) (S j))
  /-- The process stops: `density(𝔓 ∖ ⋃_{k < n} (T_k ∪ T_k^+ ∪ T_k^-)) ≤ den/2`. -/
  stop : density C₁ C₂ M L E (densityRemaining 𝔓 T Tp Tm n : Set (Multitile ρ)) ≤
    ENNReal.ofReal (den / 2)

/-- Among the dense trees in `Q` there is one with `|I|` maximal (the scales are bounded above by
`M + 1`, since `I_T ⊂ [-2^M, 2^M)`). -/
theorem exists_dense_tree_max_length {Q : Set (Multitile ρ)} {S₀ : MultitileTree ρ}
    (h₀ : IsDenseTree C₁ C₂ M L E den Q S₀) :
    ∃ S : MultitileTree ρ, IsDenseTree C₁ C₂ M L E den Q S ∧
      ∀ S' : MultitileTree ρ, IsDenseTree C₁ C₂ M L E den Q S' → S'.I.length ≤ S.I.length := by
  have hbdd : ∃ b : ℤ, ∀ z : ℤ, (∃ S : MultitileTree ρ, IsDenseTree C₁ C₂ M L E den Q S ∧
      S.I.k = z) → z ≤ b := by
    refine ⟨M + 1, ?_⟩
    rintro z ⟨S, hS, rfl⟩
    exact Dyadic.k_le_of_subset_Icc fun x hx => by
      have := hS.isTree.top_subset hx
      exact ⟨this.1, this.2.le⟩
  obtain ⟨z, ⟨S, hS, rfl⟩, hz⟩ := Int.exists_greatest_of_bdd hbdd ⟨S₀.I.k, S₀, h₀, rfl⟩
  refine ⟨S, hS, fun S' hS' => ?_⟩
  exact Dyadic.length_le_iff.2 (hz _ ⟨S', hS', rfl⟩)

/-- **Existence of the selection** (L1913-L1929): for every finite family `Q` the algorithm
terminates. -/
theorem exists_density_selection (hr : 1 < r) (Q : Finset (Multitile ρ)) :
    ∃ (n : ℕ) (S T Tp Tm : ℕ → MultitileTree ρ),
      IsDensitySelection C₁ C₂ M L E den Q n S T Tp Tm := by
  classical
  induction Q using Finset.strongInduction with
  | H Q ih =>
    by_cases hQ : density C₁ C₂ M L E (Q : Set (Multitile ρ)) ≤ ENNReal.ofReal (den / 2)
    · refine ⟨0, fun _ => ⟨∅, ⟨0, 0⟩, 0⟩, fun _ => ⟨∅, ⟨0, 0⟩, 0⟩, fun _ => ⟨∅, ⟨0, 0⟩, 0⟩,
        fun _ => ⟨∅, ⟨0, 0⟩, 0⟩, ?_⟩
      refine ⟨fun j hj => absurd hj (Nat.not_lt_zero _), fun j hj => absurd hj (Nat.not_lt_zero _),
        fun j hj => absurd hj (Nat.not_lt_zero _), fun j hj => absurd hj (Nat.not_lt_zero _),
        fun j hj => absurd hj (Nat.not_lt_zero _), ?_⟩
      rw [densityRemaining_zero]; exact hQ
    · rw [not_le] at hQ
      obtain ⟨S₀, hS₀⟩ := exists_dense_tree hr hQ
      obtain ⟨S₁, hS₁, hmax⟩ := exists_dense_tree_max_length hS₀
      set T₁ : MultitileTree ρ := maximalTree C₂ Q S₁ with hT₁
      set T₁p : MultitileTree ρ := maximalTree C₂ Q (shiftTree C₂ 1 S₁) with hT₁p
      set T₁m : MultitileTree ρ := maximalTree C₂ Q (shiftTree C₂ (-1) S₁) with hT₁m
      have hST : S₁.T ⊆ T₁.T := subset_maximalTree hS₁.isTree hS₁.subset
      have hne : S₁.T.Nonempty := hS₁.nonempty
      have hlt : Q \ (T₁.T ∪ T₁p.T ∪ T₁m.T) ⊂ Q := by
        refine Finset.sdiff_ssubset (fun P hP => ?_) ?_
        · rcases Finset.mem_union.1 hP with hP | hP
          · rcases Finset.mem_union.1 hP with hP | hP
            · exact (mem_maximalTree.1 hP).1
            · exact (mem_maximalTree.1 hP).1
          · exact (mem_maximalTree.1 hP).1
        · obtain ⟨P, hP⟩ := hne
          exact ⟨P, Finset.mem_union_left _ (Finset.mem_union_left _ (hST hP))⟩
      obtain ⟨n', S', T', Tp', Tm', hsel⟩ := ih _ hlt
      refine ⟨n' + 1, consSeq S₁ S', consSeq T₁ T', consSeq T₁p Tp', consSeq T₁m Tm', ?_⟩
      refine ⟨fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, ?_⟩
      · cases j with
        | zero => rw [densityRemaining_zero]; exact hS₁
        | succ j =>
          have := hsel.dense j (Nat.lt_of_succ_lt_succ hj)
          rw [densityRemaining_cons, consSeq_succ]; exact this
      · cases j with
        | zero => rw [densityRemaining_zero]; exact hmax
        | succ j =>
          have := hsel.I_max j (Nat.lt_of_succ_lt_succ hj)
          rw [densityRemaining_cons, consSeq_succ]; exact this
      · cases j with
        | zero => rw [densityRemaining_zero]; rfl
        | succ j =>
          have := hsel.T_eq j (Nat.lt_of_succ_lt_succ hj)
          rw [densityRemaining_cons, consSeq_succ, consSeq_succ]; exact this
      · cases j with
        | zero => rw [densityRemaining_zero]; rfl
        | succ j =>
          have := hsel.Tp_eq j (Nat.lt_of_succ_lt_succ hj)
          rw [densityRemaining_cons, consSeq_succ, consSeq_succ]; exact this
      · cases j with
        | zero => rw [densityRemaining_zero]; rfl
        | succ j =>
          have := hsel.Tm_eq j (Nat.lt_of_succ_lt_succ hj)
          rw [densityRemaining_cons, consSeq_succ, consSeq_succ]; exact this
      · rw [densityRemaining_cons]; exact hsel.stop

/-! ### Consequences of the selection -/

namespace IsDensitySelection

variable {𝔓 : Finset (Multitile ρ)} {n : ℕ} {S T Tp Tm : ℕ → MultitileTree ρ}
  (sel : IsDensitySelection C₁ C₂ M L E den 𝔓 n S T Tp Tm)
include sel

/-- `S_j` is a tree. -/
theorem S_isTree {j : ℕ} (hj : j < n) : (S j).IsTree C₁ C₂ M := (sel.dense j hj).isTree

/-- `S_j` is nonempty. -/
theorem S_nonempty {j : ℕ} (hj : j < n) : (S j).T.Nonempty := (sel.dense j hj).nonempty

/-- `T_j ⊂ 𝔓 ∖ ⋃_{k < j} (T_k ∪ T_k^+ ∪ T_k^-)`. -/
theorem T_subset_rem {j : ℕ} (hj : j < n) {P : Multitile ρ} (hP : P ∈ (T j).T) :
    P ∈ densityRemaining 𝔓 T Tp Tm j := by
  rw [sel.T_eq j hj] at hP
  exact (mem_maximalTree.1 hP).1

/-- `T_j^+ ⊂ 𝔓 ∖ ⋃_{k < j} (T_k ∪ T_k^+ ∪ T_k^-)`. -/
theorem Tp_subset_rem {j : ℕ} (hj : j < n) {P : Multitile ρ} (hP : P ∈ (Tp j).T) :
    P ∈ densityRemaining 𝔓 T Tp Tm j := by
  rw [sel.Tp_eq j hj] at hP
  exact (mem_maximalTree.1 hP).1

/-- `T_j^- ⊂ 𝔓 ∖ ⋃_{k < j} (T_k ∪ T_k^+ ∪ T_k^-)`. -/
theorem Tm_subset_rem {j : ℕ} (hj : j < n) {P : Multitile ρ} (hP : P ∈ (Tm j).T) :
    P ∈ densityRemaining 𝔓 T Tp Tm j := by
  rw [sel.Tm_eq j hj] at hP
  exact (mem_maximalTree.1 hP).1

/-- `S_j ⊂ T_j`. -/
theorem S_subset_T {j : ℕ} (hj : j < n) : (S j).T ⊆ (T j).T := by
  rw [sel.T_eq j hj]
  exact subset_maximalTree (sel.S_isTree hj) (sel.dense j hj).subset

/-- `T_j` is nonempty. -/
theorem T_nonempty {j : ℕ} (hj : j < n) : (T j).T.Nonempty :=
  (sel.S_nonempty hj).mono (sel.S_subset_T hj)

/-- `I_{T_j} = I_{S_j}`. -/
theorem T_I {j : ℕ} (hj : j < n) : (T j).I = (S j).I := by
  rw [sel.T_eq j hj]; rfl

/-- `ξ_{T_j} = ξ_{S_j}`. -/
theorem T_ξ {j : ℕ} (hj : j < n) : (T j).ξ = (S j).ξ := by
  rw [sel.T_eq j hj]; rfl

/-- `I_{T_j^+} = I_{S_j}`. -/
theorem Tp_I {j : ℕ} (hj : j < n) : (Tp j).I = (S j).I := by
  rw [sel.Tp_eq j hj]; rfl

/-- `I_{T_j^-} = I_{S_j}`. -/
theorem Tm_I {j : ℕ} (hj : j < n) : (Tm j).I = (S j).I := by
  rw [sel.Tm_eq j hj]; rfl

/-- `T_j` is a tree. -/
theorem T_isTree {j : ℕ} (hj : j < n) : (T j).IsTree C₁ C₂ M := by
  rw [sel.T_eq j hj]
  exact maximalTree_isTree (sel.S_isTree hj)

/-- `T_j^+`, if nonempty, is a tree (for multitiles in the square `[-2^M, 2^M]²`). -/
theorem Tp_isTree (hC : AdmissibleConstants C₁ C₂ C₃) (hρ : ρ.IsStd)
    (hsq : ∀ P ∈ 𝔓, P.InSquare M) {j : ℕ} (hj : j < n) (hne : (Tp j).T.Nonempty) :
    (Tp j).IsTree C₁ C₂ M := by
  rw [sel.Tp_eq j hj] at hne ⊢
  exact maximalTree_shiftTree_isTree hC hρ (sel.S_isTree hj) 1
    (fun P hP => hsq P (densityRemaining_subset _ _ _ _ _ hP)) hne

/-- `T_j^-`, if nonempty, is a tree (for multitiles in the square `[-2^M, 2^M]²`). -/
theorem Tm_isTree (hC : AdmissibleConstants C₁ C₂ C₃) (hρ : ρ.IsStd)
    (hsq : ∀ P ∈ 𝔓, P.InSquare M) {j : ℕ} (hj : j < n) (hne : (Tm j).T.Nonempty) :
    (Tm j).IsTree C₁ C₂ M := by
  rw [sel.Tm_eq j hj] at hne ⊢
  exact maximalTree_shiftTree_isTree hC hρ (sel.S_isTree hj) (-1)
    (fun P hP => hsq P (densityRemaining_subset _ _ _ _ _ hP)) hne

/-- `T_j` itself satisfies (treehaslargedensity): the density integral depends on the top data
only. -/
theorem T_dense {j : ℕ} (hj : j < n) :
    IsDenseTree C₁ C₂ M L E den (densityRemaining 𝔓 T Tp Tm j : Set (Multitile ρ)) (T j) :=
  (sel.dense j hj).of_top_data (sel.T_I hj) (sel.T_ξ hj) (sel.T_isTree hj) (sel.T_nonempty hj)
    (fun _ hP => Finset.mem_coe.2 (sel.T_subset_rem hj hP))

end IsDensitySelection

end Selection

end PrimeCarleson.Proof.Oplus
