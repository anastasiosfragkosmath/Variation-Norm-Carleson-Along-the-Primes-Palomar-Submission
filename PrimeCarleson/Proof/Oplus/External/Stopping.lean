module

public import PrimeCarleson.Proof.Oplus.Defs.Dyadic

/-!
# Maximal dyadic intervals with a property of bounded scale

The stopping-time device behind the two external inputs of [O+] Section 7 ([O+], L2603–L2609:
the maximal intervals `{I : g_I > λ}` in the interpolation between `L¹` and dyadic BMO) and the
tile-energy bound (the maximal dyadic intervals `J ⊂ Ω_λ`, the Calderón–Zygmund intervals of
Grafakos–Tao–Terwilleger).

* `Dyadic.ancestor J k`: the dyadic interval of scale `k` containing `J.left`; it contains `J`
  for `k ≥ J.k`;
* `Dyadic.IsMaxFor p I`: `I` satisfies `p` and every `p`-interval containing `I` is `I`;
* `Dyadic.exists_isMaxFor_superset`: if the scale of the `p`-intervals is bounded above, every
  `p`-interval lies in a maximal one;
* `Dyadic.IsMaxFor.disjoint`: distinct maximal intervals are disjoint.
-/

@[expose] public noncomputable section

open MeasureTheory Set

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

namespace Dyadic

/-- The dyadic interval of scale `k` containing the left end point of `J`. -/
def ancestor (J : Dyadic) (k : ℤ) : Dyadic := ofPoint k J.left

/-- The ancestor of `J` at scale `k` has scale `k`. -/
@[simp] theorem ancestor_k (J : Dyadic) (k : ℤ) : (J.ancestor k).k = k := rfl

/-- The ancestor of `J` at its own scale is `J`. -/
theorem ancestor_self (J : Dyadic) : J.ancestor J.k = J :=
  (eq_ofPoint_of_mem J.left_mem_toSet).symm

/-- A dyadic interval lies in its ancestors of larger scale. -/
theorem subset_ancestor {J : Dyadic} {k : ℤ} (hk : J.k ≤ k) :
    J.toSet ⊆ (J.ancestor k).toSet := by
  have hmem : J.left ∈ (J.ancestor k).toSet := mem_toSet_ofPoint k J.left
  rcases J.toSet_subset_or_disjoint_of_k_le (J.ancestor k) hk with h | h
  · exact h
  · exact absurd hmem (fun hm => Set.disjoint_left.1 h J.left_mem_toSet hm)

/-- A dyadic interval containing `J` is the ancestor of `J` at its own scale. -/
theorem eq_ancestor_of_subset {J J' : Dyadic} (h : J.toSet ⊆ J'.toSet) :
    J' = J.ancestor J'.k := eq_ofPoint_of_mem (h J.left_mem_toSet)

/-- `I` is maximal for the property `p`: it satisfies `p` and every `p`-interval containing it
equals it. -/
def IsMaxFor (p : Dyadic → Prop) (I : Dyadic) : Prop :=
  p I ∧ ∀ J, p J → I.toSet ⊆ J.toSet → J = I

/-- **Every `p`-interval lies in a maximal one**, provided the scales of `p`-intervals are
bounded above. -/
theorem exists_isMaxFor_superset (p : Dyadic → Prop) (K : ℤ) (hK : ∀ J, p J → J.k ≤ K)
    {J : Dyadic} (hJ : p J) : ∃ I, IsMaxFor p I ∧ J.toSet ⊆ I.toSet := by
  classical
  obtain ⟨ub, ⟨hub1, hub2⟩, hgr⟩ := Int.exists_greatest_of_bdd
    (P := fun k : ℤ => J.k ≤ k ∧ p (J.ancestor k))
    ⟨K, fun z hz => by simpa using hK _ hz.2⟩ ⟨J.k, le_rfl, by rwa [ancestor_self]⟩
  refine ⟨J.ancestor ub, ⟨hub2, fun J' hJ' hsub => ?_⟩, subset_ancestor hub1⟩
  have hJJ' : J.toSet ⊆ J'.toSet := (subset_ancestor hub1).trans hsub
  have hk1 : J.k ≤ J'.k := k_le_of_toSet_subset hJJ'
  have hk2 : J'.k ≤ ub := by
    refine hgr J'.k ⟨hk1, ?_⟩
    rw [← eq_ancestor_of_subset hJJ']
    exact hJ'
  have hk3 : (J.ancestor ub).k ≤ J'.k := k_le_of_toSet_subset hsub
  have hk4 : J'.k = (J.ancestor ub).k := by simpa using le_antisymm hk2 hk3
  exact (eq_of_toSet_subset_of_k_eq hk4.symm hsub).symm

/-- Distinct maximal intervals are disjoint. -/
theorem IsMaxFor.disjoint {p : Dyadic → Prop} {I₁ I₂ : Dyadic} (h₁ : IsMaxFor p I₁)
    (h₂ : IsMaxFor p I₂) (hne : I₁ ≠ I₂) : Disjoint I₁.toSet I₂.toSet := by
  rcases I₁.nested_or_disjoint I₂ with h | h | h
  · exact absurd (h₁.2 I₂ h₂.1 h).symm hne
  · exact absurd (h₂.2 I₁ h₁.1 h) hne
  · exact h

/-- The maximal intervals of `p` are pairwise disjoint (as a family of sets). -/
theorem pairwiseDisjoint_isMaxFor (p : Dyadic → Prop) :
    {I | IsMaxFor p I}.PairwiseDisjoint Dyadic.toSet :=
  fun _ h₁ _ h₂ hne => IsMaxFor.disjoint h₁ h₂ hne

end Dyadic

end PrimeCarleson.Proof.Oplus
