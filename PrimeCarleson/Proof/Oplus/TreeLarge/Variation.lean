module

public import PrimeCarleson.Proof.MswTransference.Variation
public import PrimeCarleson.Proof.Common.Variation

/-!
# The `r`-variation of a family and sums over disjoint windows ([O+] L2337-L2349)

Source: [O+] `treeestimatelargeintervals`, L2337–L2349: the `ℓ^r` sum over `k` of the blocks
`∑_{P : ξ_{k-1}(x) ∈ ω_l, ξ_k(x) ∈ ω_h} ⟨f, φ_P⟩ φ_P(x)` is dominated by the `r`-variation of
`ℓ ↦ (e_T ψ_ℓ) * G(x)` (the source does not state that the scale windows of different
`k` are non-overlapping). This file proves the combinatorial core, independent of trees:

* `sum_window_le_rVariationOn`: for finitely many pairwise non-overlapping windows `p_i < q_i` with
  endpoints in the index set `S`, `∑_i ‖a(p_i) - a(q_i)‖^r ≤ V^r_S(a)^r` (the `r`-variation is the
  supremum of the chain sums over strictly increasing chains in `S`; the chain is built by
  inserting the windows from the right, `exists_chain_snoc`);
* `sum_blocks_le_rVariationOn`: if `S ⊆ ℤ` is a finite set of scales and
  `H_ℓ = ∑_{s ∈ S, s ≥ ℓ} G_s`
  for `ℓ ∈ S ∪ {top}`, the blocks `Q_i ⊆ S` are pairwise disjoint and convex in `S`, then
  `∑_i |∑_{s ∈ Q_i} G_s|^r ≤ V^r_{ℓ ∈ S ∪ {top}}(H_ℓ)^r`: each block is `H_{ℓ₁} - H_{ℓ₂}` for the
  window `[min Q_i, successor of max Q_i)`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

open PrimeCarleson PrimeCarleson.Proof.Common PrimeCarleson.Proof.MswTransference

/-- The `r`-th power of the chain sum `∑ ‖a(t_j) - a(t_{j+1})‖^r`. -/
def chainSum (r : ℝ) (a : ℝ → ℂ) {J : ℕ} (t : Fin (J + 1) → ℝ) : ℝ≥0∞ :=
  ∑ j : Fin J, ‖a (t j.castSucc) - a (t j.succ)‖ₑ ^ r

/-- A chain sum is at most `V^r_S(a)^r`. -/
theorem chainSum_le_rVariationOn_rpow {r : ℝ} (hr : 0 < r) {S : Set ℝ} (a : ℝ → ℂ) {J : ℕ}
    {t : Fin (J + 1) → ℝ} (ht : StrictMono t) (hS : ∀ j, t j ∈ S) :
    chainSum r a t ≤ rVariationOn r S a ^ r := by
  have h := le_rVariationOn (r := r) (a := a) ht hS
  have h2 := ENNReal.rpow_le_rpow h hr.le
  rwa [← ENNReal.rpow_mul, one_div_mul_cancel hr.ne', ENNReal.rpow_one] at h2

/-- Appending a larger point to a chain adds one term. -/
theorem exists_chain_snoc {r : ℝ} (a : ℝ → ℂ) {J : ℕ} {t : Fin (J + 1) → ℝ} (ht : StrictMono t)
    {y : ℝ} (hy : t (Fin.last J) < y) :
    ∃ t' : Fin (J + 1 + 1) → ℝ, StrictMono t' ∧ t' (Fin.last (J + 1)) = y ∧
      (∀ j, t' j = y ∨ ∃ i, t' j = t i) ∧
      chainSum r a t' = chainSum r a t + ‖a (t (Fin.last J)) - a y‖ₑ ^ r := by
  refine ⟨Fin.snoc (α := fun _ => ℝ) t y, ?_, ?_, ?_, ?_⟩
  · rw [Fin.strictMono_iff_lt_succ]
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hy
    · have : j.castSucc.succ = j.succ.castSucc := Fin.succ_castSucc j
      rw [this]
      simp only [Fin.snoc_castSucc]
      exact ht (Fin.castSucc_lt_succ)
  · simp
  · intro j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · left; simp
    · right; exact ⟨i, by simp⟩
  · unfold chainSum
    rw [Fin.sum_univ_castSucc]
    congr 1
    · refine Finset.sum_congr rfl fun j _ => ?_
      have : j.castSucc.succ = j.succ.castSucc := Fin.succ_castSucc j
      simp only [this, Fin.snoc_castSucc]
    · simp only [Fin.succ_last, Fin.snoc_last, Fin.snoc_castSucc]


/-- **Disjoint windows**: for finitely many pairwise non-overlapping windows `p_i < q_i` with
endpoints in `S`, `∑_i ‖a(p_i) - a(q_i)‖^r ≤ V^r_S(a)^r`. -/
theorem sum_window_le_rVariationOn {r : ℝ} (hr : 0 < r) {S : Set ℝ} (a : ℝ → ℂ) {ι : Type*}
    (𝒦 : Finset ι) (p q : ι → ℝ) (hpS : ∀ i ∈ 𝒦, p i ∈ S)
    (hqS : ∀ i ∈ 𝒦, q i ∈ S) (hpq : ∀ i ∈ 𝒦, p i < q i)
    (hdisj : ∀ i ∈ 𝒦, ∀ i' ∈ 𝒦, i ≠ i' → q i ≤ p i' ∨ q i' ≤ p i) :
    ∑ i ∈ 𝒦, ‖a (p i) - a (q i)‖ₑ ^ r ≤ rVariationOn r S a ^ r := by
  classical
  have key : ∀ 𝒦 : Finset ι, (∀ i ∈ 𝒦, p i ∈ S) → (∀ i ∈ 𝒦, q i ∈ S) → (∀ i ∈ 𝒦, p i < q i) →
      (∀ i ∈ 𝒦, ∀ i' ∈ 𝒦, i ≠ i' → q i ≤ p i' ∨ q i' ≤ p i) → ∀ B : ℝ, (∀ i ∈ 𝒦, q i ≤ B) →
      𝒦 = ∅ ∨ ∃ (J : ℕ) (t : Fin (J + 1) → ℝ), StrictMono t ∧ (∀ j, t j ∈ S) ∧
        t (Fin.last J) ≤ B ∧ ∑ i ∈ 𝒦, ‖a (p i) - a (q i)‖ₑ ^ r ≤ chainSum r a t := by
    intro 𝒦
    refine Finset.induction_on_max_value p 𝒦 (fun _ _ _ _ _ _ => Or.inl rfl) ?_
    intro i₀ s hi₀ hmax ih hpS hqS hpq hdisj B hB
    have hsub : ∀ i ∈ s, i ∈ insert i₀ s := fun i hi => Finset.mem_insert_of_mem hi
    have hq_le : ∀ i ∈ s, q i ≤ p i₀ := by
      intro i hi
      have hne : i ≠ i₀ := fun h => hi₀ (h ▸ hi)
      rcases hdisj i (hsub i hi) i₀ (Finset.mem_insert_self _ _) hne with h | h
      · exact h
      · exfalso
        have h1 := hpq i₀ (Finset.mem_insert_self _ _)
        have h2 := hmax i hi
        linarith
    have hS := ih (fun i hi => hpS i (hsub i hi)) (fun i hi => hqS i (hsub i hi))
      (fun i hi => hpq i (hsub i hi))
      (fun i hi i' hi' h => hdisj i (hsub i hi) i' (hsub i' hi') h) (p i₀) hq_le
    right
    have hp0 := hpS i₀ (Finset.mem_insert_self _ _)
    have hq0 := hqS i₀ (Finset.mem_insert_self _ _)
    have hlt0 := hpq i₀ (Finset.mem_insert_self _ _)
    have hB0 := hB i₀ (Finset.mem_insert_self _ _)
    rw [Finset.sum_insert hi₀]
    rcases hS with hs | ⟨J, t, ht, htS, htl, hsum⟩
    · subst hs
      obtain ⟨t', ht', hl', hmem, hcs⟩ := exists_chain_snoc (r := r) a
        (t := fun _ : Fin (0 + 1) => p i₀) (J := 0) (fun i j h => absurd h (by omega)) hlt0
      refine ⟨0 + 1, t', ht', ?_, by rw [hl']; exact hB0, ?_⟩
      · intro j
        rcases hmem j with h | ⟨i, h⟩
        · rw [h]; exact hq0
        · rw [h]; exact hp0
      · rw [hcs]
        simp [chainSum]
    · rcases htl.lt_or_eq with hlt | heq
      · obtain ⟨t', ht', hl', hmem, hcs⟩ := exists_chain_snoc (r := r) a ht hlt
        obtain ⟨t'', ht'', hl'', hmem'', hcs'⟩ := exists_chain_snoc (r := r) a ht'
          (y := q i₀) (by rw [hl']; exact hlt0)
        refine ⟨J + 1 + 1, t'', ht'', ?_, by rw [hl'']; exact hB0, ?_⟩
        · intro j
          rcases hmem'' j with h | ⟨i, h⟩
          · rw [h]; exact hq0
          · rw [h]
            rcases hmem i with h' | ⟨i', h'⟩
            · rw [h']; exact hp0
            · rw [h']; exact htS i'
        · rw [hcs', hl', hcs]
          calc ‖a (p i₀) - a (q i₀)‖ₑ ^ r + ∑ i ∈ s, ‖a (p i) - a (q i)‖ₑ ^ r
              ≤ ‖a (p i₀) - a (q i₀)‖ₑ ^ r + chainSum r a t := by gcongr
            _ = chainSum r a t + ‖a (p i₀) - a (q i₀)‖ₑ ^ r := add_comm _ _
            _ ≤ _ := by gcongr; exact le_self_add
      · obtain ⟨t', ht', hl', hmem, hcs⟩ := exists_chain_snoc (r := r) a ht
          (y := q i₀) (by rw [heq]; exact hlt0)
        refine ⟨J + 1, t', ht', ?_, by rw [hl']; exact hB0, ?_⟩
        · intro j
          rcases hmem j with h | ⟨i, h⟩
          · rw [h]; exact hq0
          · rw [h]; exact htS i
        · rw [hcs, heq]
          calc ‖a (p i₀) - a (q i₀)‖ₑ ^ r + ∑ i ∈ s, ‖a (p i) - a (q i)‖ₑ ^ r
              ≤ ‖a (p i₀) - a (q i₀)‖ₑ ^ r + chainSum r a t := by gcongr
            _ = _ := add_comm _ _
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ i ∈ 𝒦, q i ≤ B := by
    obtain ⟨B, hB⟩ := (𝒦.image q).bddAbove
    exact ⟨B, fun i hi => hB (Finset.mem_image_of_mem q hi)⟩
  rcases key 𝒦 hpS hqS hpq hdisj B hB with h | ⟨J, t, ht, htS, -, hsum⟩
  · subst h; simp
  · exact hsum.trans (chainSum_le_rVariationOn_rpow hr a ht htS)


/-- **The block sums over convex disjoint runs of scales** (abstract form of the variation in the
scale parameter, [O+] `treeestimatelargeintervals`): `S` is a finite set of scales,
`H_ℓ = ∑_{s ≥ ℓ, s ∈ S} G_s` for `ℓ ∈ S ∪ {top}`, the blocks `Q_i ⊆ S` are pairwise disjoint and
convex in `S`; then `∑_i |∑_{s ∈ Q_i} G_s|^r ≤ V^r_{ℓ ∈ S ∪ {top}}(H_ℓ)^r`. -/
theorem sum_blocks_le_rVariationOn {r : ℝ} (hr : 0 < r) {ι : Type*} (𝒦 : Finset ι)
    (S : Finset ℤ) (top : ℤ) (htop : ∀ s ∈ S, s < top) (G H : ℤ → ℂ)
    (hH : ∀ ℓ ∈ insert top S, H ℓ = ∑ s ∈ S.filter (fun s => ℓ ≤ s), G s)
    (Q : ι → Finset ℤ) (hQS : ∀ i ∈ 𝒦, Q i ⊆ S) (hne : ∀ i ∈ 𝒦, (Q i).Nonempty)
    (hdisj : ∀ i ∈ 𝒦, ∀ i' ∈ 𝒦, i ≠ i' → Disjoint (Q i) (Q i'))
    (hconv : ∀ i ∈ 𝒦, ∀ s ∈ S, ∀ s₁ ∈ Q i, ∀ s₂ ∈ Q i, s₁ ≤ s → s ≤ s₂ → s ∈ Q i) :
    ∑ i ∈ 𝒦, ‖∑ s ∈ Q i, G s‖ₑ ^ r ≤
      rVariationOn r ((↑) '' (↑(insert top S) : Set ℤ) : Set ℝ) (fun t => H ⌊t⌋) ^ r := by
  classical
  have hex : ∀ i ∈ 𝒦, ∃ l1 l2 : ℤ, l1 ∈ S ∧ l2 ∈ insert top S ∧ l1 < l2 ∧
      ∀ s ∈ S, (s ∈ Q i ↔ l1 ≤ s ∧ s < l2) := by
    intro i hi
    have hn := hne i hi
    set lo := (Q i).min' hn with hlo
    set hi' := (Q i).max' hn with hhi
    have hlomem : lo ∈ Q i := Finset.min'_mem _ _
    have hhimem : hi' ∈ Q i := Finset.max'_mem _ _
    have hnn : (insert top (S.filter fun s => hi' < s)).Nonempty := Finset.insert_nonempty _ _
    set l2 := (insert top (S.filter fun s => hi' < s)).min' hnn with hl2
    have hl2mem : l2 ∈ insert top (S.filter fun s => hi' < s) := Finset.min'_mem _ _
    have hgt : ∀ y ∈ insert top (S.filter fun s => hi' < s), hi' < y := by
      intro y hy
      rcases Finset.mem_insert.1 hy with rfl | hy
      · exact htop _ (hQS i hi hhimem)
      · exact (Finset.mem_filter.1 hy).2
    refine ⟨lo, l2, hQS i hi hlomem, ?_, ?_, ?_⟩
    · rcases Finset.mem_insert.1 hl2mem with h | h
      · rw [h]; exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_filter.1 h).1
    · exact lt_of_le_of_lt (Finset.min'_le _ _ hhimem) (hgt _ hl2mem)
    · intro s hs
      constructor
      · intro hsQ
        refine ⟨Finset.min'_le _ _ hsQ, ?_⟩
        exact lt_of_le_of_lt (Finset.le_max' _ _ hsQ) (hgt _ hl2mem)
      · rintro ⟨h1, h2⟩
        have hsle : s ≤ hi' := by
          by_contra hcon
          rw [not_le] at hcon
          have : l2 ≤ s := Finset.min'_le _ _
            (Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨hs, hcon⟩))
          omega
        exact hconv i hi s hs lo hlomem hi' hhimem h1 hsle
  choose! l1 l2 hl using hex
  set a : ℝ → ℂ := fun t => H ⌊t⌋ with ha
  have hae : ∀ l : ℤ, a (l : ℝ) = H l := fun l => by simp [ha]
  have hsum : ∀ i ∈ 𝒦, ∑ s ∈ Q i, G s = H (l1 i) - H (l2 i) := by
    intro i hi
    obtain ⟨h1S, h2S, hlt, hQ⟩ := hl i hi
    rw [hH _ (Finset.mem_insert_of_mem h1S), hH _ h2S]
    have hsub : S.filter (fun s => l2 i ≤ s) ⊆ S.filter (fun s => l1 i ≤ s) := by
      intro s hs
      have := Finset.mem_filter.1 hs
      exact Finset.mem_filter.2 ⟨this.1, by omega⟩
    rw [← Finset.sum_sdiff hsub, add_sub_cancel_right]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext s
    simp only [Finset.mem_sdiff, Finset.mem_filter]
    constructor
    · intro hs
      have hsS := hQS i hi hs
      have := (hQ s hsS).1 hs
      exact ⟨⟨hsS, this.1⟩, fun h => by omega⟩
    · rintro ⟨⟨hsS, hs1⟩, hs2⟩
      exact (hQ s hsS).2 ⟨hs1, by
        by_contra hcon
        exact hs2 ⟨hsS, by omega⟩⟩
  have hwin := sum_window_le_rVariationOn hr a 𝒦 (fun i => (l1 i : ℝ)) (fun i => (l2 i : ℝ))
    (S := (↑) '' (↑(insert top S) : Set ℤ))
    (fun i hi => ⟨l1 i, by exact_mod_cast Finset.mem_insert_of_mem (hl i hi).1, rfl⟩)
    (fun i hi => ⟨l2 i, by exact_mod_cast (hl i hi).2.1, rfl⟩)
    (fun i hi => by exact_mod_cast (hl i hi).2.2.1)
    (fun i hi i' hi' hne' => by
      by_contra hcon
      simp only [not_or, not_le] at hcon
      obtain ⟨hc1, hc2⟩ := hcon
      have hc1' : l1 i' < l2 i := by exact_mod_cast hc1
      have hc2' : l1 i < l2 i' := by exact_mod_cast hc2
      obtain ⟨h1S, -, -, hQ⟩ := hl i hi
      obtain ⟨h1S', -, -, hQ'⟩ := hl i' hi'
      have hmS : max (l1 i) (l1 i') ∈ S := by
        rcases le_total (l1 i) (l1 i') with h | h
        · rw [max_eq_right h]; exact h1S'
        · rw [max_eq_left h]; exact h1S
      have m1 : max (l1 i) (l1 i') ∈ Q i :=
        (hQ _ hmS).2 ⟨le_max_left _ _, max_lt (hl i hi).2.2.1 hc1'⟩
      have m2 : max (l1 i) (l1 i') ∈ Q i' :=
        (hQ' _ hmS).2 ⟨le_max_right _ _, max_lt hc2' (hl i' hi').2.2.1⟩
      exact Finset.disjoint_left.1 (hdisj i hi i' hi' hne') m1 m2)
  calc ∑ i ∈ 𝒦, ‖∑ s ∈ Q i, G s‖ₑ ^ r
      = ∑ i ∈ 𝒦, ‖a (l1 i : ℝ) - a (l2 i : ℝ)‖ₑ ^ r := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [hae, hae, hsum i hi]
    _ ≤ _ := hwin

/-- The `r`-variation over `S` depends only on the increments `a s - a t`, `s ≤ t` in `S`. -/
theorem rVariationOn_congr_sub {r : ℝ} {S : Set ℝ} {a b : ℝ → ℂ}
    (h : ∀ s ∈ S, ∀ t ∈ S, s ≤ t → a s - a t = b s - b t) :
    rVariationOn r S a = rVariationOn r S b := by
  unfold rVariationOn
  refine iSup_congr fun J => iSup_congr fun t => iSup_congr fun ht => iSup_congr fun hS => ?_
  refine congrArg (· ^ (1 / r)) (Finset.sum_congr rfl fun i _ => ?_)
  rw [h _ (hS _) _ (hS _) (ht.monotone (Fin.castSucc_lt_succ).le)]

end PrimeCarleson.Proof.Oplus
