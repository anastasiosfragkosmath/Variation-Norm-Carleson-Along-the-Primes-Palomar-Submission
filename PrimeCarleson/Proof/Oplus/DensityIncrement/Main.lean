module

public import PrimeCarleson.Proof.Oplus.DensityIncrement.Summation

/-!
# The density increment proposition ([O+] L1895-L1967)

Source: [O+] `densityincrementprop`, L1900–L1910:
"Let `𝔓` be a collection of multitiles and `den > 0`. Then there is a collection of trees `𝒯`
such that `∑_{T ∈ 𝒯} |I_T| ≲ den^{-r'} |E|` (dtreeintervalbound) and such that
`density(𝔓 ∖ ⋃_{T ∈ 𝒯} T) ≤ den/2`."

`density_increment` is this proposition for a *finite* family `𝔓` of `ρ`-multitiles (`ρ` any `1`- or
`2`-index with `m, n ∈ {1, …, 4}`, any profile choice: the proof does not use the wave packets),
with one implicit constant `K` depending only on `r` (through `r'`; independent of `ρ`, the
admissible constants, `M`, the linearizing data `L`, `E`, `den` and `𝔓`). The collection `𝒯` is a
`Finset` of nonempty trees inside `𝔓`, pairwise disjoint as sets of multitiles: the nonempty ones
among `T_j`, `T_j^+ ∖ T_j`, `T_j^- ∖ (T_j ∪ T_j^+)` of the selection algorithm
(`IsDensitySelection`, `trimmedTree`). The source's `T_j, T_j^+, T_j^-` may overlap (the paper does
not say how this is handled where the trees are used, L2583); the trimmed trees have the same top
data and the same union. As in `EnergyIncrement/Main.lean`, `𝔓` lies in the square `[-2^M, 2^M]²`
(`M = M_o + 3` of the ambient family); this is used only for the top frequencies of `T_j^±` to lie
in `𝒳_top`. The separation assumptions (separationofscales), (separationprop2) of the source are not
needed, `r > 1` suffices, and `E` need not be measurable (`volume` is the outer measure). -/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

/-- The sum of a function over the image of a finite set is at most the sum over the set. -/
theorem sum_image_le_sum_comp_ennreal {ι α : Type*} [DecidableEq α] (s : Finset ι) (f : ι → α)
    (g : α → ℝ≥0∞) : ∑ x ∈ s.image f, g x ≤ ∑ i ∈ s, g (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.image_insert, Finset.sum_insert ha]
    by_cases hmem : f a ∈ s.image f
    · rw [Finset.insert_eq_of_mem hmem]
      exact ih.trans le_add_self
    · rw [Finset.sum_insert hmem]
      exact add_le_add le_rfl ih

/-- The sum over a union is at most the sum of the sums. -/
theorem sum_union_le_add_ennreal {α : Type*} [DecidableEq α] (s t : Finset α) (g : α → ℝ≥0∞) :
    ∑ x ∈ s ∪ t, g x ≤ ∑ x ∈ s, g x + ∑ x ∈ t, g x := by
  rw [← Finset.sum_union_inter]
  exact le_self_add

section Trim

variable {ρ : Idx}

/-- A tree with the multitiles of `A` removed (same top data). -/
def MultitileTree.without (𝒯 : MultitileTree ρ) (A : Finset (Multitile ρ)) : MultitileTree ρ :=
  ⟨𝒯.T \ A, 𝒯.I, 𝒯.ξ⟩

/-- Removing multitiles from a tree gives a tree. -/
theorem MultitileTree.IsTree.without [Fact ρ.IsOneOrTwo] {C₁ C₂ : ℝ} {M : ℤ}
    {𝒯 : MultitileTree ρ} (h : 𝒯.IsTree C₁ C₂ M) (A : Finset (Multitile ρ)) :
    (𝒯.without A).IsTree C₁ C₂ M :=
  ⟨h.top_subset, h.ξ_mem, fun P hP => h.time P (Finset.sdiff_subset hP),
    fun P hP => h.freq P (Finset.sdiff_subset hP)⟩

/-- The three trees `T_j`, `T_j^+ ∖ T_j`, `T_j^- ∖ (T_j ∪ T_j^+)` of step `j`: they have the top
data of `T_j`, `T_j^+`, `T_j^-` and are pairwise disjoint, with the same union. -/
def trimmedTree (T Tp Tm : ℕ → MultitileTree ρ) (j : ℕ) : Fin 3 → MultitileTree ρ
  | 0 => T j
  | 1 => (Tp j).without (T j).T
  | 2 => (Tm j).without ((T j).T ∪ (Tp j).T)

/-- A multitile of a trimmed tree is in `T_j ∪ T_j^+ ∪ T_j^-`. -/
theorem mem_used_of_mem_trimmed {T Tp Tm : ℕ → MultitileTree ρ} {j : ℕ} (a : Fin 3)
    {P : Multitile ρ} (hP : P ∈ (trimmedTree T Tp Tm j a).T) :
    P ∈ (T j).T ∨ P ∈ (Tp j).T ∨ P ∈ (Tm j).T := by
  fin_cases a
  · exact Or.inl hP
  · exact Or.inr (Or.inl (Finset.sdiff_subset hP))
  · exact Or.inr (Or.inr (Finset.sdiff_subset hP))

variable [Fact ρ.IsOneOrTwo] {C₁ C₂ C₃ : ℝ} {M : ℤ} {r : ℝ} {L : Linearization r} {E : Set ℝ}
  {den : ℝ} {𝔓 : Finset (Multitile ρ)} {n : ℕ} {S T Tp Tm : ℕ → MultitileTree ρ}

namespace IsDensitySelection

variable (sel : IsDensitySelection C₁ C₂ M L E den 𝔓 n S T Tp Tm)
include sel

/-- The trimmed trees have the top interval `I_{S_j}`. -/
theorem trimmed_I {j : ℕ} (hj : j < n) (a : Fin 3) : (trimmedTree T Tp Tm j a).I = (T j).I := by
  fin_cases a
  · rfl
  · exact (sel.Tp_I hj).trans (sel.T_I hj).symm
  · exact (sel.Tm_I hj).trans (sel.T_I hj).symm

/-- A multitile of a trimmed tree lies in the family remaining before step `j`. -/
theorem mem_rem_of_mem_trimmed {j : ℕ} (hj : j < n) (a : Fin 3) {P : Multitile ρ}
    (hP : P ∈ (trimmedTree T Tp Tm j a).T) : P ∈ densityRemaining 𝔓 T Tp Tm j := by
  rcases mem_used_of_mem_trimmed a hP with h | h | h
  · exact sel.T_subset_rem hj h
  · exact sel.Tp_subset_rem hj h
  · exact sel.Tm_subset_rem hj h

/-- The trimmed trees of all steps are pairwise disjoint. -/
theorem trimmed_disjoint {j j' : ℕ} (hj : j < n) (hj' : j' < n) {a b : Fin 3}
    (hne : (j, a) ≠ (j', b)) :
    Disjoint (trimmedTree T Tp Tm j a).T (trimmedTree T Tp Tm j' b).T := by
  rcases lt_trichotomy j j' with h | rfl | h
  · refine Finset.disjoint_left.2 fun P hP hP' => ?_
    have h1 := sel.mem_rem_of_mem_trimmed hj' b hP'
    obtain ⟨x1, x2, x3⟩ := not_mem_of_mem_densityRemaining h h1
    rcases mem_used_of_mem_trimmed a hP with h | h | h
    exacts [x1 h, x2 h, x3 h]
  · have hab : a ≠ b := fun h => hne (by rw [h])
    fin_cases a <;> fin_cases b <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      trimmedTree, MultitileTree.without] at hab ⊢ <;>
    first
    | exact absurd rfl hab
    | (refine Finset.disjoint_left.2 fun P hP hP' => ?_
       simp only [Finset.mem_sdiff, Finset.mem_union] at hP hP'
       tauto)
  · refine Finset.disjoint_left.2 fun P hP hP' => ?_
    have h1 := sel.mem_rem_of_mem_trimmed hj a hP
    obtain ⟨x1, x2, x3⟩ := not_mem_of_mem_densityRemaining h h1
    rcases mem_used_of_mem_trimmed b hP' with h | h | h
    exacts [x1 h, x2 h, x3 h]

end IsDensitySelection

end Trim

section Main

variable {r : ℝ}

/-- **`densityincrementprop`** ([O+] L1900-L1967): the density increment. For every `den > 0`
and every finite family `𝔓` of multitiles in the square `[-2^M, 2^M]²` there is a finite
collection `𝒯` of nonempty trees in `𝔓` with `∑_{T ∈ 𝒯} |I_T| ≤ K den^{-r'} |E|` and
`density(𝔓 ∖ ⋃_{T ∈ 𝒯} T) ≤ den/2`. The trees are pairwise disjoint (as sets of multitiles): the
trees `T_j^+, T_j^-` of the source, which may overlap `T_j` and each other, are replaced by the
subtrees of the multitiles not yet in `T_j`, `T_j^+`; this changes neither the top intervals nor
the union. -/
theorem density_increment (hr : 1 < r) : ∃ K : ℝ, 0 < K ∧ ∀ {ρ : Idx} [Fact ρ.IsOneOrTwo]
    {C₁ C₂ C₃ : ℝ} {M : ℤ}, AdmissibleConstants C₁ C₂ C₃ → ρ.IsStd →
    ∀ (L : Linearization r) (E : Set ℝ) {den : ℝ}, 0 < den →
    ∀ {𝔓 : Finset (Multitile ρ)}, (∀ P ∈ 𝔓, P.InSquare M) →
    ∃ 𝒯 : Finset (MultitileTree ρ),
      (∀ T ∈ 𝒯, T.IsTree C₁ C₂ M ∧ (T.T : Set (Multitile ρ)) ⊆ 𝔓 ∧ T.T.Nonempty) ∧
      ∑ T ∈ 𝒯, ENNReal.ofReal T.I.length ≤
        ENNReal.ofReal (K / den ^ Real.conjExponent r) * volume E ∧
      density C₁ C₂ M L E ((𝔓 : Set (Multitile ρ)) \ ⋃ T ∈ 𝒯, (T.T : Set (Multitile ρ))) ≤
        ENNReal.ofReal (den / 2) ∧
      (∀ T ∈ 𝒯, ∀ T' ∈ 𝒯, T ≠ T' → Disjoint T.T T'.T) := by
  classical
  have hp0 : 0 < Real.conjExponent r := by
    unfold Real.conjExponent
    exact div_pos (by linarith) (by linarith)
  refine ⟨48 * 2 ^ (8 + Real.conjExponent r), by positivity, ?_⟩
  intro ρ _ C₁ C₂ C₃ M hC hρ L E den hden 𝔓 hsq
  obtain ⟨n, S, T, Tp, Tm, sel⟩ := exists_density_selection (C₁ := C₁) (C₂ := C₂) (M := M)
    (L := L) (E := E) (den := den) hr 𝔓
  set 𝒯 : Finset (MultitileTree ρ) :=
    ((Finset.range n ×ˢ (Finset.univ : Finset (Fin 3))).image
      (fun x => trimmedTree T Tp Tm x.1 x.2)).filter (fun T' => T'.T.Nonempty) with h𝒯
  have hslot : ∀ T' ∈ 𝒯, ∃ j a, j < n ∧ T' = trimmedTree T Tp Tm j a ∧ T'.T.Nonempty := by
    intro T' hT'
    obtain ⟨hmem, hne⟩ := Finset.mem_filter.1 hT'
    obtain ⟨⟨j, a⟩, hja, rfl⟩ := Finset.mem_image.1 hmem
    exact ⟨j, a, Finset.mem_range.1 (Finset.mem_product.1 hja).1, rfl, hne⟩
  refine ⟨𝒯, ?_, ?_, ?_, ?_⟩
  · -- every member is a nonempty tree in `𝔓`
    intro T' hT'
    obtain ⟨j, a, hj, rfl, hne⟩ := hslot T' hT'
    refine ⟨?_, fun P hP => Finset.mem_coe.2 (densityRemaining_subset _ _ _ _ _
      (sel.mem_rem_of_mem_trimmed hj a hP)), hne⟩
    fin_cases a
    · exact sel.T_isTree hj
    · exact (sel.Tp_isTree hC hρ hsq hj (hne.mono Finset.sdiff_subset)).without _
    · exact (sel.Tm_isTree hC hρ hsq hj (hne.mono Finset.sdiff_subset)).without _
  · -- (dtreeintervalbound), from (thirddtreeintervalbound) by a factor 3
    have h3 : ∑ T' ∈ 𝒯, ENNReal.ofReal T'.I.length ≤
        3 * ∑ j ∈ Finset.range n, ENNReal.ofReal (T j).I.length := by
      calc ∑ T' ∈ 𝒯, ENNReal.ofReal T'.I.length
          ≤ ∑ T' ∈ (Finset.range n ×ˢ (Finset.univ : Finset (Fin 3))).image
              (fun x => trimmedTree T Tp Tm x.1 x.2), ENNReal.ofReal T'.I.length :=
            Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
        _ ≤ ∑ x ∈ Finset.range n ×ˢ (Finset.univ : Finset (Fin 3)),
              ENNReal.ofReal (trimmedTree T Tp Tm x.1 x.2).I.length :=
            sum_image_le_sum_comp_ennreal _ _
              (fun T' : MultitileTree ρ => ENNReal.ofReal T'.I.length)
        _ = ∑ j ∈ Finset.range n, 3 * ENNReal.ofReal (T j).I.length := by
            rw [Finset.sum_product]
            refine Finset.sum_congr rfl fun j hj => ?_
            have := fun a => sel.trimmed_I (Finset.mem_range.1 hj) a
            simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            norm_num
        _ = 3 * ∑ j ∈ Finset.range n, ENNReal.ofReal (T j).I.length := by rw [Finset.mul_sum]
    have h4 := sel.thirddtreeintervalbound hr hden hC hρ
    have hDd0 : ENNReal.ofReal (den ^ Real.conjExponent r) ≠ 0 :=
      (ENNReal.ofReal_pos.2 (by positivity)).ne'
    have hDdt : ENNReal.ofReal (den ^ Real.conjExponent r) ≠ ∞ := ENNReal.ofReal_ne_top
    have h5 : ENNReal.ofReal (den ^ Real.conjExponent r) * ∑ T' ∈ 𝒯, ENNReal.ofReal T'.I.length ≤
        ENNReal.ofReal (48 * 2 ^ (8 + Real.conjExponent r)) * volume E := by
      calc ENNReal.ofReal (den ^ Real.conjExponent r) * ∑ T' ∈ 𝒯, ENNReal.ofReal T'.I.length
          ≤ ENNReal.ofReal (den ^ Real.conjExponent r) *
            (3 * ∑ j ∈ Finset.range n, ENNReal.ofReal (T j).I.length) := mul_le_mul' le_rfl h3
        _ = 3 * (ENNReal.ofReal (den ^ Real.conjExponent r) *
            ∑ j ∈ Finset.range n, ENNReal.ofReal (T j).I.length) := by ring
        _ ≤ 3 * (ENNReal.ofReal (16 * 2 ^ (8 + Real.conjExponent r)) * volume E) :=
            mul_le_mul' le_rfl h4
        _ = ENNReal.ofReal (48 * 2 ^ (8 + Real.conjExponent r)) * volume E := by
            rw [← mul_assoc]
            congr 1
            rw [show (3 : ℝ≥0∞) = ENNReal.ofReal 3 by simp, ← ENNReal.ofReal_mul (by norm_num)]
            congr 1; ring
    refine ((ENNReal.mul_le_iff_le_inv hDd0 hDdt).1 h5).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_div_of_pos (by positivity), div_eq_mul_inv]
    ring
  · -- the remaining family has density at most `den/2`
    have hset : (𝔓 : Set (Multitile ρ)) \ ⋃ T' ∈ 𝒯, (T'.T : Set (Multitile ρ)) =
        (densityRemaining 𝔓 T Tp Tm n : Set (Multitile ρ)) := by
      rw [coe_densityRemaining]
      congr 1
      ext P
      simp only [mem_iUnion, Finset.mem_range, exists_prop, mem_union, Finset.mem_coe]
      constructor
      · rintro ⟨T', hT', hP⟩
        obtain ⟨j, a, hj, rfl, -⟩ := hslot T' hT'
        have := mem_used_of_mem_trimmed (T := T) (Tp := Tp) (Tm := Tm) a hP
        exact ⟨j, hj, by tauto⟩
      · rintro ⟨j, hj, hP⟩
        have hmem : ∀ a : Fin 3, P ∈ (trimmedTree T Tp Tm j a).T →
            trimmedTree T Tp Tm j a ∈ 𝒯 := fun a hPa =>
          Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨(j, a), Finset.mem_product.2
            ⟨Finset.mem_range.2 hj, Finset.mem_univ _⟩, rfl⟩, ⟨P, hPa⟩⟩
        by_cases h1 : P ∈ (T j).T
        · exact ⟨_, hmem 0 h1, h1⟩
        · by_cases h2 : P ∈ (Tp j).T
          · exact ⟨_, hmem 1 (Finset.mem_sdiff.2 ⟨h2, h1⟩), Finset.mem_sdiff.2 ⟨h2, h1⟩⟩
          · have h3 : P ∈ (Tm j).T := by tauto
            have h4 : P ∈ (trimmedTree T Tp Tm j 2).T := by
              change P ∈ (Tm j).T \ ((T j).T ∪ (Tp j).T)
              simp [h3, h1, h2]
            exact ⟨_, hmem 2 h4, h4⟩
    rw [hset]
    exact sel.stop
  · -- the trees are pairwise disjoint
    intro T' hT' T'' hT'' hne
    obtain ⟨j, a, hj, rfl, -⟩ := hslot T' hT'
    obtain ⟨j', b, hj', rfl, -⟩ := hslot T'' hT''
    exact sel.trimmed_disjoint hj hj' fun h => hne (by rw [Prod.mk.injEq] at h; rw [h.1, h.2])

end Main

end PrimeCarleson.Proof.Oplus
