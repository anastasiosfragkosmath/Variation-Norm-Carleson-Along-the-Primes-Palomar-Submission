module

public import PrimeCarleson.Proof.Oplus.EnergyIncrement.All
public import PrimeCarleson.Proof.Oplus.DensityIncrement.All
public import PrimeCarleson.Proof.Oplus.TreeLarge.All

/-!
# Iterating the energy and density increments ([O+] L2582-L2602, L2666-L2676)

Source: [O+] `L1except`, L2582–L2602; [O+] `L1except`, L2666–L2676 (the source says only
"repeatedly applying Propositions energyincrementprop and densityincrementprop" and does not
carry this out).

This file holds the abstract, increment-independent part of the bookkeeping:

* `exists_iteration`: if a step lemma takes a family satisfying an invariant `Inv j` to a finite
  set of trees contained in it whose complement satisfies `Inv (j + 1)`, then there is an infinite
  sequence of such steps starting from a given family; if moreover the invariant at some stage `J`
  forces every remaining multitile into a set `Z`, then every multitile of the starting family lies
  in `Z` or in one of the trees extracted before stage `J`;
* `exists_J_coeff_zero`: the multitiles with a nonzero coefficient `⟨f, φ_P⟩` all disappear from a
  family whose energy is at most `e₀ ν^J` once `J` is large (a single multitile is an
  `l`-overlapping tree, so its coefficient is at most the energy times `|I_P|^{1/2}`). This is the
  termination argument that the source omits: the multitiles with zero coefficient may never be
  selected, and they do not contribute to the model operator;
* `exists_assignment`: a cover of a finite family by finitely many sets of multitiles can be made
  disjoint by assigning each multitile to one set containing it; sums over the family become sums
  over the sets (this is the reduction to the disjoint union of the source, L2583);
* `MultitileTree.IsTree.of_subset`: a subset of the multitiles of a tree, with the same top data,
  is a tree.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

section Iteration

/-- **Iteration of a step** (the bookkeeping behind "repeatedly applying" the increment
propositions). If `step` takes each family `Q` with `Inv j Q` to finitely many trees with
`cov T ⊆ Q` whose complement satisfies `Inv (j + 1)`, there are sequences `𝒯 j`, `Q j` with
`Q 0 = Q₀`, `Q (j + 1) = Q j ∖ ⋃ 𝒯 j`. If every multitile of a family satisfying `Inv J` lies in
`Z`, then every multitile of `Q₀` lies in `Z` or in a tree of a stage before `J`. -/
theorem exists_iteration {X Tr : Type*} [DecidableEq X] (cov : Tr → Finset X)
    (Inv : ℕ → Finset X → Prop) (Out : ℕ → Finset X → Finset Tr → Prop)
    (step : ∀ j (Q : Finset X), Inv j Q → ∃ 𝒯 : Finset Tr, Out j Q 𝒯 ∧
      (∀ T ∈ 𝒯, cov T ⊆ Q) ∧ Inv (j + 1) (Q \ 𝒯.biUnion cov))
    (Q₀ : Finset X) (h0 : Inv 0 Q₀) (Z : Set X) (J : ℕ)
    (hJ : ∀ Q : Finset X, Q ⊆ Q₀ → Inv J Q → ∀ P ∈ Q, P ∈ Z) :
    ∃ (𝒯 : ℕ → Finset Tr) (Q : ℕ → Finset X), Q 0 = Q₀ ∧
      (∀ j, Inv j (Q j) ∧ Out j (Q j) (𝒯 j) ∧ (∀ T ∈ 𝒯 j, cov T ⊆ Q j) ∧
        Q (j + 1) = Q j \ (𝒯 j).biUnion cov) ∧
      ∀ P ∈ Q₀, P ∈ Z ∨ ∃ j < J, ∃ T ∈ 𝒯 j, P ∈ cov T := by
  classical
  let seq : (j : ℕ) → {Q : Finset X // Inv j Q} := fun j =>
    Nat.rec (motive := fun j => {Q : Finset X // Inv j Q}) ⟨Q₀, h0⟩
      (fun j s => ⟨s.1 \ (Classical.choose (step j s.1 s.2)).biUnion cov,
        (Classical.choose_spec (step j s.1 s.2)).2.2⟩) j
  let 𝒯 : ℕ → Finset Tr := fun j => Classical.choose (step j (seq j).1 (seq j).2)
  have hspec : ∀ j, Out j (seq j).1 (𝒯 j) ∧ (∀ T ∈ 𝒯 j, cov T ⊆ (seq j).1) :=
    fun j => ⟨(Classical.choose_spec (step j (seq j).1 (seq j).2)).1,
      (Classical.choose_spec (step j (seq j).1 (seq j).2)).2.1⟩
  have hsucc : ∀ j, (seq (j + 1)).1 = (seq j).1 \ (𝒯 j).biUnion cov := fun j => rfl
  have hsub : ∀ n, (seq n).1 ⊆ Q₀ := by
    intro n
    induction n with
    | zero => exact subset_rfl
    | succ n ih => rw [hsucc]; exact Finset.sdiff_subset.trans ih
  refine ⟨𝒯, fun j => (seq j).1, rfl, fun j => ⟨(seq j).2, (hspec j).1, (hspec j).2, hsucc j⟩, ?_⟩
  have key : ∀ n, ∀ P ∈ Q₀, P ∈ (seq n).1 ∨ ∃ j < n, ∃ T ∈ 𝒯 j, P ∈ cov T := by
    intro n
    induction n with
    | zero => exact fun P hP => Or.inl hP
    | succ n ih =>
      intro P hP
      rcases ih P hP with h | ⟨j, hj, T, hT, hPT⟩
      · by_cases hex : ∃ T ∈ 𝒯 n, P ∈ cov T
        · obtain ⟨T, hT, hPT⟩ := hex
          exact Or.inr ⟨n, Nat.lt_succ_self n, T, hT, hPT⟩
        · left
          rw [hsucc]
          refine Finset.mem_sdiff.2 ⟨h, fun hmem => hex ?_⟩
          obtain ⟨T, hT, hPT⟩ := Finset.mem_biUnion.1 hmem
          exact ⟨T, hT, hPT⟩
      · exact Or.inr ⟨j, Nat.lt_succ_of_lt hj, T, hT, hPT⟩
  intro P hP
  rcases key J P hP with h | h
  · exact Or.inl (hJ (seq J).1 (hsub J) (seq J).2 P h)
  · exact Or.inr h

end Iteration

section Coefficients

variable {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ C₃ : ℝ} {M : ℤ}

/-- **Termination of the iteration.** For a finite family `𝔓` of multitiles in the square
`[-2^M, 2^M]²` and `ν < 1` there is `J` such that every subfamily of energy at most `e₀ ν^J`
consists of multitiles with zero coefficient `⟨f, φ_P⟩` (a single multitile is an
`l`-overlapping tree: `|⟨f, φ_P⟩|² ≤ energy² |I_P|`). -/
theorem exists_J_coeff_zero (hC : AdmissibleConstants C₁ C₂ C₃) (hρ : ρ.IsStd)
    (ch : ProfileChoice) (f : ℝ → ℂ) (𝔓 : Finset (Multitile ρ)) (hsq : ∀ P ∈ 𝔓, P.InSquare M)
    {e₀ ν : ℝ} (he₀ : 0 < e₀) (hν0 : 0 < ν) (hν1 : ν < 1) :
    ∃ J : ℕ, ∀ Q : Finset (Multitile ρ), Q ⊆ 𝔓 →
      energy C₁ C₂ M ch f (Q : Set (Multitile ρ)) ≤ ENNReal.ofReal (e₀ * ν ^ J) →
      ∀ P ∈ Q, P.coeff ch f = 0 := by
  classical
  have hJP : ∀ P : Multitile ρ, ∃ J : ℕ, P.coeff ch f ≠ 0 →
      (e₀ * ν ^ J) ^ 2 * P.I.length < ‖P.coeff ch f‖ ^ 2 := by
    intro P
    by_cases h : P.coeff ch f = 0
    · exact ⟨0, fun h' => absurd h h'⟩
    · have hc : 0 < ‖P.coeff ch f‖ ^ 2 := by positivity
      have hl := P.I.length_pos
      have ht : Filter.Tendsto (fun n : ℕ => (e₀ * ν ^ n) ^ 2 * P.I.length) Filter.atTop
          (nhds 0) := by
        have h1 := (tendsto_pow_atTop_nhds_zero_of_lt_one hν0.le hν1).const_mul e₀
        have h2 := (h1.pow 2).mul_const P.I.length
        simpa using h2
      obtain ⟨J, hJ⟩ := (ht.eventually (gt_mem_nhds hc)).exists
      exact ⟨J, fun _ => hJ⟩
  choose Jf hJf using hJP
  refine ⟨𝔓.sup Jf, fun Q hQ hen P hP => ?_⟩
  by_contra hne
  have hP𝔓 := hQ hP
  have hmono : ν ^ (𝔓.sup Jf) ≤ ν ^ (Jf P) :=
    pow_le_pow_of_le_one hν0.le hν1.le (Finset.le_sup hP𝔓)
  have hpos : 0 < e₀ * ν ^ (𝔓.sup Jf) := by positivity
  have h1 := norm_sq_coeff_le_of_energy_le hC hρ hpos.le hen (Finset.mem_coe.2 hP) (hsq P hP𝔓)
  have h2 := hJf P hne
  have h3 : (e₀ * ν ^ (𝔓.sup Jf)) ^ 2 * P.I.length ≤ (e₀ * ν ^ (Jf P)) ^ 2 * P.I.length := by
    have hl := P.I.length_pos
    gcongr
  linarith

end Coefficients

section Assignment

/-- **Disjointification of a finite cover.** If `Q` is covered by the sets `V i`, `i ∈ s`, there are
`R i ⊆ V i ∩ Q` such that every sum over `Q` is the sum over `i ∈ s` of the sums over `R i`
(assign each element of `Q` to one index). -/
theorem exists_assignment {X ι : Type*} [Nonempty ι] (s : Finset ι)
    (V : ι → Finset X) (Q : Finset X) (hcov : ∀ P ∈ Q, ∃ i ∈ s, P ∈ V i) :
    ∃ R : ι → Finset X, (∀ i, R i ⊆ V i) ∧ (∀ i, R i ⊆ Q) ∧
      ∀ {A : Type*} [AddCommMonoid A] (g : X → A), ∑ P ∈ Q, g P = ∑ i ∈ s, ∑ P ∈ R i, g P := by
  classical
  choose! c hc using hcov
  refine ⟨fun i => Q.filter fun P => c P = i, ?_, ?_, ?_⟩
  · intro i P hP
    obtain ⟨hPQ, hPi⟩ := Finset.mem_filter.1 hP
    rw [← hPi]
    exact (hc P hPQ).2
  · intro i P hP
    exact (Finset.mem_filter.1 hP).1
  · intro A _ g
    exact (Finset.sum_fiberwise_of_maps_to (s := Q) (t := s) (g := c)
      (fun P hP => (hc P hP).1) g).symm

end Assignment

section TreeSubset

variable {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ : ℝ} {M : ℤ}

/-- A subset of the multitiles of a tree, with the same top data, is a tree. -/
theorem MultitileTree.IsTree.of_subset {𝒯 : MultitileTree ρ} (h : 𝒯.IsTree C₁ C₂ M)
    (R : Finset (Multitile ρ)) (hR : R ⊆ 𝒯.T) : (MultitileTree.mk R 𝒯.I 𝒯.ξ).IsTree C₁ C₂ M :=
  ⟨h.top_subset, h.ξ_mem, fun P hP => h.time P (hR hP), fun P hP => h.freq P (hR hP)⟩

end TreeSubset

end PrimeCarleson.Proof.Oplus
