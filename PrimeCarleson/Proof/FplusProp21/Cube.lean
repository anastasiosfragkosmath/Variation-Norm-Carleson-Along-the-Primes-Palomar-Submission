module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Fin

/-!
# The cube `{0,1}³`, its faces and the propagation algorithm

Finite combinatorics of the proof of [F+] Proposition 2.1
([F+] TeX, the marking argument L828-L839 and the
postponed counting argument L914–L1044). The steps, with their sources:

* [F+] L836 (`exists_card_filter_eq_one`): every set of one, two or three vertices of the cube meets
  some face `{ω : ω i = j}` in exactly one vertex;
* [F+] L914–L932, the propagation algorithm (`propStep`, `propClosure`): a marked vertex `ω ∈ S` is
  coloured green once some face through `ω` has all its other marked vertices green;
  `propClosure S T` runs four rounds of this rule from the green set `T`;
* [F+] L1041 (`subset_propClosure_empty`): `|S| ≤ 3` is coloured from `∅`;
* [F+] L1043 (`exists_subset_propClosure_singleton`): a five-element `S` is coloured from one of its
  vertices;
* [F+] L1039–L1040 (`insert_propClosure_subset`): adding a vertex to both `S` and `T` keeps the run;
* [F+] `l:algorithm`, L935–L944 (`exists_subset_propClosure`): every `S` with `|S| ≥ 4` is coloured
  from some `T ⊆ S` with `|T| ≤ 1` if `|S| = 4` and `|T| ≤ |S| - 4` if `|S| ≥ 5`.

The three finite facts are checked by `decide +kernel` over the `2⁸` subsets of the cube; the
algorithm's rounds colour all qualifying vertices at once, so four rounds suffice in the decided
cases, and the induction of the step adding a green vertex keeps the number of rounds.
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PrimeCarleson.Proof.FplusProp21

/-- The cube `{0,1}³`. -/
abbrev Cube : Type := Fin 3 → Fin 2

/-- The weight `|ω| = ω₁ + ω₂ + ω₃` of a vertex. -/
def cubeWt (ω : Cube) : ℕ := ∑ i, ((ω i : ℕ))

/-- The sign `(-1)^{|ω|}` of a vertex. -/
def cubeSign (ω : Cube) : ℤ := (-1) ^ cubeWt ω

/-- One round of the propagation algorithm: a marked vertex `ω ∈ S` turns green when, on some
face `{ν : ν i = ω i}` through `ω`, every other marked vertex is already green. -/
def propStep (S G : Finset Cube) : Finset Cube :=
  G ∪ S.filter (fun ω => ∃ i : Fin 3, (S.filter (fun ν => ν i = ω i)).erase ω ⊆ G)

/-- Four rounds of the propagation algorithm on the marked set `S`, from the green set `T`. -/
def propClosure (S T : Finset Cube) : Finset Cube := (propStep S)^[4] T

/-- The eight vertices of the cube. -/
theorem univ_cube : (Finset.univ : Finset Cube) =
    {![0, 0, 0], ![1, 0, 0], ![0, 1, 0], ![1, 1, 0], ![0, 0, 1], ![1, 0, 1], ![0, 1, 1],
      ![1, 1, 1]} := by
  decide

/-- A product over the cube, written out. -/
theorem prod_cube {M : Type*} [CommMonoid M] (f : Cube → M) :
    ∏ ω, f ω = f ![0, 0, 0] * f ![1, 0, 0] * f ![0, 1, 0] * f ![1, 1, 0] * f ![0, 0, 1] *
      f ![1, 0, 1] * f ![0, 1, 1] * f ![1, 1, 1] := by
  rw [univ_cube, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton]
  simp only [mul_assoc]

/-- The sign of a vertex is `±1`. -/
theorem cubeSign_eq_one_or (ω : Cube) : cubeSign ω = 1 ∨ cubeSign ω = -1 := by
  unfold cubeSign
  rcases Nat.even_or_odd (cubeWt ω) with h | h
  · exact Or.inl h.neg_one_pow
  · exact Or.inr h.neg_one_pow

/-- **Cube fact** (Source: [F+] L836): every set of one, two or three vertices of `{0,1}³` meets
some face `{ω : ω i = j}` in exactly one vertex. -/
theorem exists_card_filter_eq_one :
    ∀ S : Finset Cube, 1 ≤ S.card → S.card ≤ 3 →
      ∃ i : Fin 3, ∃ j : Fin 2, (S.filter (fun ω => ω i = j)).card = 1 := by
  decide +kernel

/-- **Small sets** (Source: [F+] L1041): a marked set of at most three vertices is coloured by the
algorithm from no green vertex. -/
theorem subset_propClosure_empty :
    ∀ S : Finset Cube, S.card ≤ 3 → S ⊆ propClosure S ∅ := by
  decide +kernel

/-- **Five vertices** (Source: [F+] L1043 and Figure fig2): every five-element marked set is
coloured from a single green vertex. -/
theorem exists_subset_propClosure_singleton :
    ∀ S : Finset Cube, S.card = 5 → ∃ v ∈ S, S ⊆ propClosure S {v} := by
  decide +kernel

/-- A round of the algorithm is monotone in the green set. -/
theorem propStep_mono (S : Finset Cube) {G G' : Finset Cube} (h : G ⊆ G') :
    propStep S G ⊆ propStep S G' := by
  intro ω hω
  simp only [propStep, Finset.mem_union, Finset.mem_filter] at hω ⊢
  rcases hω with hω | ⟨hωS, i, hi⟩
  · exact Or.inl (h hω)
  · exact Or.inr ⟨hωS, i, hi.trans h⟩

/-- Adding a vertex to both the marked and the green set: one round. -/
theorem insert_propStep_subset (S G : Finset Cube) (v : Cube) :
    insert v (propStep S G) ⊆ propStep (insert v S) (insert v G) := by
  classical
  intro ω hω
  rw [Finset.mem_insert] at hω
  simp only [propStep, Finset.mem_union, Finset.mem_filter, Finset.mem_insert] at hω ⊢
  rcases hω with rfl | hω | ⟨hωS, i, hi⟩
  · exact Or.inl (Or.inl rfl)
  · exact Or.inl (Or.inr hω)
  · refine Or.inr ⟨Or.inr hωS, i, fun ν hν => ?_⟩
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_insert] at hν
    obtain ⟨hνω, hνS, hνi⟩ := hν
    rcases hνS with rfl | hνS
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem
        (hi (Finset.mem_erase.2 ⟨hνω, Finset.mem_filter.2 ⟨hνS, hνi⟩⟩))

/-- Adding a vertex to both the marked and the green set: any number of rounds. -/
theorem insert_iterate_propStep_subset (S T : Finset Cube) (v : Cube) (n : ℕ) :
    insert v ((propStep S)^[n] T) ⊆ (propStep (insert v S))^[n] (insert v T) := by
  induction n with
  | zero => exact subset_rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact (insert_propStep_subset S _ v).trans (propStep_mono _ ih)

/-- **Adding a green vertex** (Source: [F+] L1039–L1040): if the algorithm colours `S` from `T`, it
colours `S ∪ {v}` from `T ∪ {v}`. -/
theorem insert_propClosure_subset (S T : Finset Cube) (v : Cube) :
    insert v (propClosure S T) ⊆ propClosure (insert v S) (insert v T) :=
  insert_iterate_propStep_subset S T v 4

/-- The bound `f(|S|)` of Lemma `l:algorithm`: `0` for `|S| ≤ 3`, `1` for `|S| = 4` and
`|S| - 4` for `|S| ≥ 5`. -/
def algBound (n : ℕ) : ℕ := if n ≤ 3 then 0 else if n = 4 then 1 else n - 4

/-- `f(4) = 1`. -/
theorem algBound_four : algBound 4 = 1 := by
  simp [algBound]

/-- `f(n) = n - 4` for `n ≥ 5`. -/
theorem algBound_of_five_le {n : ℕ} (h : 5 ≤ n) : algBound n = n - 4 := by
  unfold algBound
  split_ifs <;> omega

/-- **Lemma `l:algorithm`**, for every marked set: there is `T ⊆ S` with `|T| ≤ f(|S|)` from
which the algorithm colours all of `S`. -/
theorem exists_subset_propClosure_algBound (S : Finset Cube) :
    ∃ T ⊆ S, T.card ≤ algBound S.card ∧ S ⊆ propClosure S T := by
  classical
  induction h : S.card generalizing S with
  | zero =>
    exact ⟨∅, Finset.empty_subset _, by simp, subset_propClosure_empty S (by omega)⟩
  | succ n ih =>
    rcases Nat.lt_or_ge n 3 with hn | hn
    · exact ⟨∅, Finset.empty_subset _, by simp, subset_propClosure_empty S (by omega)⟩
    rcases Nat.lt_or_ge n 4 with hn4 | hn4
    · -- `|S| = 4`
      obtain ⟨v, hv⟩ : S.Nonempty := Finset.card_pos.1 (by omega)
      have hS' : (S.erase v).card = 3 := by rw [Finset.card_erase_of_mem hv, h]; omega
      have hn4' : n + 1 = 4 := by omega
      refine ⟨{v}, Finset.singleton_subset_iff.2 hv, by rw [hn4', algBound_four]; simp, ?_⟩
      have h1 := insert_propClosure_subset (S.erase v) ∅ v
      rw [Finset.insert_erase hv] at h1
      calc S = insert v (S.erase v) := (Finset.insert_erase hv).symm
        _ ⊆ insert v (propClosure (S.erase v) ∅) :=
            Finset.insert_subset_insert _ (subset_propClosure_empty _ (by omega))
        _ ⊆ propClosure S {v} := by simpa using h1
    rcases Nat.lt_or_ge n 5 with hn5 | hn5
    · -- `|S| = 5`
      obtain ⟨v, hv, hS⟩ := exists_subset_propClosure_singleton S (by omega)
      refine ⟨{v}, Finset.singleton_subset_iff.2 hv, ?_, hS⟩
      rw [algBound_of_five_le (by omega)]
      simp only [Finset.card_singleton]
      omega
    · -- `|S| ≥ 6`: remove a vertex
      obtain ⟨v, hv⟩ : S.Nonempty := Finset.card_pos.1 (by omega)
      have hS' : (S.erase v).card = n := by rw [Finset.card_erase_of_mem hv, h]; omega
      obtain ⟨T, hTS, hTc, hST⟩ := ih (S.erase v) hS'
      refine ⟨insert v T, Finset.insert_subset hv (hTS.trans (Finset.erase_subset _ _)), ?_, ?_⟩
      · rw [algBound_of_five_le (by omega)]
        rw [algBound_of_five_le (by omega)] at hTc
        calc (insert v T).card ≤ T.card + 1 := Finset.card_insert_le _ _
          _ ≤ n + 1 - 4 := by omega
      · have h1 := insert_propClosure_subset (S.erase v) T v
        rw [Finset.insert_erase hv] at h1
        calc S = insert v (S.erase v) := (Finset.insert_erase hv).symm
          _ ⊆ insert v (propClosure (S.erase v) T) := Finset.insert_subset_insert _ hST
          _ ⊆ propClosure S (insert v T) := h1

/-- **Lemma `l:algorithm`** ([F+] L935-L944), as stated: for `|S| ≥ 4` there is `T ⊆ S` with
`|T| ≤ 1` if `|S| = 4` and `|T| ≤ |S| - 4` if `5 ≤ |S| ≤ 8`, such that the propagation
algorithm started from `T` colours every vertex of `S`. -/
theorem exists_subset_propClosure (S : Finset Cube) (hS : 4 ≤ S.card) :
    ∃ T ⊆ S, T.card ≤ (if S.card = 4 then 1 else S.card - 4) ∧ S ⊆ propClosure S T := by
  obtain ⟨T, hTS, hTc, hST⟩ := exists_subset_propClosure_algBound S
  refine ⟨T, hTS, ?_, hST⟩
  have : algBound S.card = if S.card = 4 then 1 else S.card - 4 := by
    unfold algBound
    split_ifs <;> omega
  rwa [← this]

end PrimeCarleson.Proof.FplusProp21
