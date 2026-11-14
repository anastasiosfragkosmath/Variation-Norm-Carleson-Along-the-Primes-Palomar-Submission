module

public import PrimeCarleson.Proof.Paper.P5.Blocks

/-!
# Existence of the block partition (`e:kappa`)

`sources/Variational_Carleson.tex` L2083-L2086: "partitioning the square-free integers inside
`(Q/2, Q]` into disjoint subsets `{B}` with `|B| ≈ Q^κ`". The paper tacitly uses that there are
at least about `Q^κ` squarefree integers there. `exists_chunks` partitions any finite set `S` into
blocks of size in `[m, 2m)` (a single smaller block if `|S| < m`), and
`exists_blockPartition` turns this into a `BlockPartition j κ A` for every `A ≥ 4` provided the
squarefree integers in `(Q/2, Q]` number at least `Q^κ / A`
(`hS`, which holds for `A = 24`, `κ ≤ 1`, by the density of squarefree integers).
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

/-- A finite set of naturals is partitioned into blocks of size `< 2m`, each of size `≥ m`
unless there is a single block. -/
theorem exists_chunks (m : ℕ) (hm : 1 ≤ m) : ∀ (n : ℕ) (S : Finset ℕ), S.card = n →
    ∃ blocks : Finset (Finset ℕ), (blocks : Set (Finset ℕ)).PairwiseDisjoint id ∧
      blocks.biUnion id = S ∧ ∀ B ∈ blocks, B.Nonempty ∧ B.card < 2 * m ∧
        (m ≤ B.card ∨ blocks = {B}) := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S hS
    by_cases hlt : S.card < 2 * m
    · by_cases hne : S.Nonempty
      · refine ⟨{S}, by simp, by simp, fun B hB => ?_⟩
        rw [Finset.mem_singleton] at hB
        subst hB
        exact ⟨hne, hlt, Or.inr rfl⟩
      · rw [Finset.not_nonempty_iff_eq_empty] at hne
        subst hne
        exact ⟨∅, by simp, by simp, by simp⟩
    · push Not at hlt
      obtain ⟨T, hTS, hTc⟩ := Finset.exists_subset_card_eq (s := S) (n := m) (by omega)
      have hS'c : (S \ T).card = n - m := by
        rw [Finset.card_sdiff_of_subset hTS, hS, hTc]
      obtain ⟨blocks', hd', hu', hp'⟩ := ih (n - m) (by omega) (S \ T) hS'c
      have hTne : T.Nonempty := by
        rw [← Finset.card_pos, hTc]
        omega
      have hTnot : T ∉ blocks' := by
        intro hT
        have hsub : T ⊆ S \ T := by
          have := Finset.subset_biUnion_of_mem id hT
          rw [hu'] at this
          exact this
        obtain ⟨x, hx⟩ := hTne
        exact (Finset.mem_sdiff.1 (hsub hx)).2 hx
      refine ⟨insert T blocks', ?_, ?_, ?_⟩
      · rw [Finset.coe_insert]
        refine Set.PairwiseDisjoint.insert hd' fun B hB _ => ?_
        have hBsub : B ⊆ S \ T := by
          rw [← hu']
          exact Finset.subset_biUnion_of_mem id hB
        exact Finset.disjoint_of_subset_right hBsub Finset.disjoint_sdiff
      · rw [Finset.biUnion_insert, hu']
        simp [Finset.union_sdiff_of_subset hTS]
      · intro B hB
        rw [Finset.mem_insert] at hB
        rcases hB with rfl | hB
        · exact ⟨hTne, by omega, Or.inl (by omega)⟩
        · obtain ⟨hBne, hBlt, hBor⟩ := hp' B hB
          refine ⟨hBne, hBlt, Or.inl ?_⟩
          rcases hBor with h | h
          · exact h
          · have : B = S \ T := by
              rw [← hu', h]
              simp
            rw [this]
            have : (S \ T).card = n - m := hS'c
            omega

/-- **The block partition `e:kappa`**: a block partition exists for every `A ≥ 4`, provided there
are at least `Q^κ / A` squarefree integers in `(Q/2, Q]`. -/
theorem exists_blockPartition {j : ℕ} {κ A : ℝ} (hκ : 0 ≤ κ) (hA : 4 ≤ A)
    (hS : ((2 : ℝ) ^ j) ^ κ ≤ A * (sqfreeSet j).card) : Nonempty (BlockPartition j κ A) := by
  have hQ1 : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
  have hQκ : (1 : ℝ) ≤ ((2 : ℝ) ^ j) ^ κ := Real.one_le_rpow hQ1 hκ
  set m : ℕ := ⌈((2 : ℝ) ^ j) ^ κ⌉₊ with hm
  have hm1 : 1 ≤ m := by
    rw [hm]
    exact Nat.one_le_iff_ne_zero.2 (by rw [Ne, Nat.ceil_eq_zero, not_le]; linarith)
  have hmle : (m : ℝ) ≤ ((2 : ℝ) ^ j) ^ κ + 1 := (Nat.ceil_lt_add_one (by linarith)).le
  have hmge : ((2 : ℝ) ^ j) ^ κ ≤ m := Nat.le_ceil _
  obtain ⟨blocks, hd, hu, hp⟩ := exists_chunks m hm1 _ (sqfreeSet j) rfl
  refine ⟨⟨blocks, hd, hu, fun B hB => ?_, fun B hB => ?_⟩⟩
  · obtain ⟨hBne, hBlt, hBor⟩ := hp B hB
    rcases hBor with h | h
    · have : (m : ℝ) ≤ B.card := by exact_mod_cast h
      nlinarith
    · have : B = sqfreeSet j := by
        rw [← hu, h]
        simp
      rw [this]
      exact hS
  · obtain ⟨hBne, hBlt, hBor⟩ := hp B hB
    have h1 : (B.card : ℝ) < 2 * m := by exact_mod_cast hBlt
    nlinarith
end PrimeCarleson.Proof.Paper
