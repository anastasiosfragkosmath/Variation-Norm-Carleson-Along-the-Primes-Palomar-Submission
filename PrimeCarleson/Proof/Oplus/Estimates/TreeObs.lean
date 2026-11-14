module

public import PrimeCarleson.Proof.Oplus.Defs.All

/-!
# The Observation on trees with separated scales ([O+] L1286-L1309)

[O+] L1286-L1309: "Let `T` be a tree satisfying the
separation properties (separationofscales) and (separationprop2). Then (i) if `T` is
`l`-overlapping, `P, P' ∈ T` and `|ω_u'| < |ω_u|` then `C₃ ω_u ∩ C₂ ω_u' = ∅`; (ii) if `T` is
`l`-lacunary, `P, P' ∈ T` and `|ω_u'| < |ω_u|` then `C₃ ω_l ∩ C₃ ω_l' = ∅`; (iii) if `P, P' ∈ T`,
`P ≠ P'` and `|ω_u| = |ω_u'|` then `I ∩ I' = ∅`." Source: [O+] `treeobs`, L1286–L1309
(stated as "immediate" without proof).

The proofs are elementary interval geometry with the abstract constants `C₁ > C₂ > C₃ ≥ 1`
(`AdmissibleConstants`) and the multitile indices `ρ` with `m, n ∈ {1, …, 4}` and `ρ` a `1`- or
`2`-index (all of them, not only the indices of `R`):

* (i) `ξ_𝒯 ∈ C₂ ω_l ∩ C₂ ω_l'`; `C₂ ω_u ∩ C₂ ω_l = ∅` puts `ξ_𝒯` at distance `≥ (C₂ - C₃)|ω_u|/2`
  from `C₃ ω_u`, while `C₂ ω_l' ⊂ C₁ ω_u'` and `C₂ ω_u' ⊂ C₁ ω_u'` put `ξ_𝒯` and `C₂ ω_u'` within
  `C₁|ω_u'| ≤ (C₂ - C₃)|ω_u|/2`;
* (ii) `ξ_𝒯 ∈ ω_𝒯 ⊂ ω_m(P)` and `ξ_𝒯 ∉ C₂ ω_l` give `ξ_𝒯 ≥ sup C₂ ω_l`, while `ω_m(P') ⊂ C₁ ω_l'`
  bounds `ξ_𝒯` from above by `sup C₁ ω_l'`;
* (iii) `ω_𝒯 ⊂ ω_m ⊂ C₁ ω_u` for both multitiles, so `C₁ ω_u ∩ C₁ ω_u' ≠ ∅` and
  (separationprop2) gives `ω_u = ω_u'`; then `I ≠ I'` have the same length, hence are disjoint.

`Separated.mono` restricts the separation assumptions to a subfamily (a tree inside a separated
collection).
-/

@[expose] public noncomputable section

open Set

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

/-! ### Geometry of the dilates -/

/-- Membership in the dilate `C J` of a dyadic interval. -/
theorem Dyadic.mem_dilate {u : Dyadic} {C x : ℝ} :
    x ∈ u.dilate C ↔
      u.center - C * u.length / 2 ≤ x ∧ x < u.center + C * u.length / 2 := Iff.rfl

/-- The centre of `ω_l = ω_u - (m+1)|ω_u|` is `c(ω_u) - (m+1)|ω_u|`. -/
theorem Idx.center_ωlDyadic (ρ : Idx) (u : Dyadic) :
    (ρ.ωlDyadic u).center = u.center - ((ρ.m : ℝ) + 1) * u.length := by
  unfold Idx.ωlDyadic; rw [Dyadic.center_shift]; push_cast; ring

/-- `|ω_l| = |ω_u|`. -/
theorem Idx.length_ωlDyadic (ρ : Idx) (u : Dyadic) : (ρ.ωlDyadic u).length = u.length := rfl

/-- Lengths of dyadic intervals agree iff the scales agree. -/
theorem Dyadic.length_eq_iff {I J : Dyadic} : I.length = J.length ↔ I.k = J.k := by
  constructor
  · intro h
    exact zpow_right_injective₀ (by norm_num) (by norm_num) h
  · intro h; unfold Dyadic.length; rw [h]

/-- Two distinct dyadic intervals of the same scale are disjoint. -/
theorem Dyadic.disjoint_of_k_eq_of_ne {I J : Dyadic} (hk : I.k = J.k) (hne : I ≠ J) :
    Disjoint I.toSet J.toSet := by
  rcases I.nested_or_disjoint J with h | h | h
  · exact absurd (Dyadic.eq_of_toSet_subset_of_k_eq hk h) hne
  · exact absurd (Dyadic.eq_of_toSet_subset_of_k_eq hk.symm h).symm hne
  · exact h

/-- The separation assumptions restrict to subfamilies. -/
theorem Separated.mono {ρ : Idx} {C₁ C₂ C₃ : ℝ} {S S' : Set (Multitile ρ)}
    (h : Separated C₁ C₂ C₃ S) (hS : S' ⊆ S) : Separated C₁ C₂ C₃ S' :=
  ⟨fun P hP P' hP' => h.scales P (hS hP) P' (hS hP'),
    fun P hP P' hP' => h.prop2 P (hS hP) P' (hS hP')⟩

variable {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ C₃ : ℝ}

omit [Fact ρ.IsOneOrTwo] in
/-- `ω_𝒯` contains the top frequency `ξ_𝒯` for `C₂ > 1`. -/
theorem MultitileTree.mem_ωT_self (𝒯 : MultitileTree ρ) {C₂ : ℝ} (hC₂ : 1 < C₂) :
    𝒯.ξ ∈ 𝒯.ωT C₂ := by
  have hI := 𝒯.I.length_pos
  have : 0 < (C₂ - 1) / (4 * 𝒯.I.length) := by
    apply div_pos <;> linarith
  constructor <;> linarith

/-- `ω_m = hull(C₂ ω_u ∪ C₂ ω_l) ⊆ C₁ ω_u` (using `C₂ ω_l ⊆ C₁ ω_u`). -/
theorem Multitile.ωm_subset_ωuDil (hC : AdmissibleConstants C₁ C₂ C₃) (hρ : ρ.IsStd)
    (P : Multitile ρ) : P.ωm C₂ ⊆ P.ωuDil C₁ := by
  obtain ⟨-, -, hsub1, -⟩ := hC.geometry ρ hρ Fact.out P.ωu
  unfold Multitile.ωm
  refine convexHull_min (Set.union_subset ?_ ?_) (convex_Ico _ _)
  · exact Dyadic.dilate_mono P.ωu hC.lt₂.le
  · exact hsub1

/-- `ω_m ⊆ [c(ω_l) - C₂|ω_u|/2, c(ω_u) + C₂|ω_u|/2)`. -/
theorem Multitile.ωm_subset_Ico (C₂ : ℝ) (P : Multitile ρ) :
    P.ωm C₂ ⊆ Ico (P.ωu.center - ((ρ.m : ℝ) + 1) * P.ωu.length - C₂ * P.ωu.length / 2)
      (P.ωu.center + C₂ * P.ωu.length / 2) := by
  have hL := P.ωu.length_pos
  have hm : (0 : ℝ) ≤ ρ.m := Nat.cast_nonneg _
  unfold Multitile.ωm
  refine convexHull_min (Set.union_subset ?_ ?_) (convex_Ico _ _)
  · intro x hx
    have hx' : x ∈ P.ωu.dilate C₂ := hx
    obtain ⟨h1, h2⟩ := Dyadic.mem_dilate.1 hx'
    constructor
    · nlinarith
    · linarith
  · intro x hx
    have hx' : x ∈ (ρ.ωlDyadic P.ωu).dilate C₂ := hx
    obtain ⟨h1, h2⟩ := Dyadic.mem_dilate.1 hx'
    rw [Idx.center_ωlDyadic, Idx.length_ωlDyadic] at h1 h2
    constructor
    · linarith
    · nlinarith

/-- A point outside the dilate `C J` is at distance `≥ C|J|/2` from the centre of `J`. -/
theorem Dyadic.half_le_abs_of_not_mem_dilate {u : Dyadic} {C ξ : ℝ} (h : ξ ∉ u.dilate C) :
    C * u.length / 2 ≤ |ξ - u.center| := by
  by_contra h'
  rw [not_le, abs_lt] at h'
  exact h (Dyadic.mem_dilate.2 ⟨by linarith [h'.1], by linarith [h'.2]⟩)

/-- A point of the dilate `C J` is at distance `≤ C|J|/2` from the centre of `J`. -/
theorem Dyadic.abs_sub_center_le_of_mem_dilate {u : Dyadic} {C x : ℝ} (h : x ∈ u.dilate C) :
    |x - u.center| ≤ C * u.length / 2 := by
  obtain ⟨h1, h2⟩ := Dyadic.mem_dilate.1 h
  rw [abs_le]
  constructor <;> linarith

/-- Two points of the dilate `C J` are at distance `< C|J|`. -/
theorem Dyadic.abs_sub_lt_of_mem_dilate {u : Dyadic} {C x y : ℝ} (hx : x ∈ u.dilate C)
    (hy : y ∈ u.dilate C) : |x - y| < C * u.length := by
  obtain ⟨h1, h2⟩ := Dyadic.mem_dilate.1 hx
  obtain ⟨h3, h4⟩ := Dyadic.mem_dilate.1 hy
  rw [abs_lt]
  constructor <;> linarith

/-! ### The three parts of the Observation -/

/-- **(i), without the tree**: if `ξ ∈ C₂ ω_l ∩ C₂ ω_l'` and `|ω_u'| ≤ ((C₂ - C₃)/(2C₁))|ω_u|`
then `C₃ ω_u ∩ C₂ ω_u' = ∅`. -/
theorem treeobs_overlapping_aux (hC : AdmissibleConstants C₁ C₂ C₃) (hρ : ρ.IsStd)
    {P P' : Multitile ρ} {ξ : ℝ} (hξ : ξ ∈ P.ωlDil C₂) (hξ' : ξ ∈ P'.ωlDil C₂)
    (hsc : P'.ωu.length ≤ (C₂ - C₃) / (2 * C₁) * P.ωu.length) :
    Disjoint (P.ωuDil C₃) (P'.ωuDil C₂) := by
  have hL := P.ωu.length_pos
  have hL' := P'.ωu.length_pos
  have hC1 : 0 < C₁ := by linarith [hC.one_le, hC.lt₁, hC.lt₂]
  obtain ⟨hdisj, -, -, -⟩ := hC.geometry ρ hρ Fact.out P.ωu
  obtain ⟨-, -, hsub1', -⟩ := hC.geometry ρ hρ Fact.out P'.ωu
  rw [Set.disjoint_left]
  intro x hx hx'
  have hξnot : ξ ∉ P.ωu.dilate C₂ := fun h => Set.disjoint_left.1 hdisj h hξ
  have h1 := Dyadic.half_le_abs_of_not_mem_dilate hξnot
  have h2 := Dyadic.abs_sub_center_le_of_mem_dilate (show x ∈ P.ωu.dilate C₃ from hx)
  have h3 : (C₂ - C₃) * P.ωu.length / 2 ≤ |ξ - x| := by
    have : |ξ - P.ωu.center| ≤ |ξ - x| + |x - P.ωu.center| := by
      have := abs_add_le (ξ - x) (x - P.ωu.center)
      simpa using this
    nlinarith
  have h4 : x ∈ P'.ωu.dilate C₁ :=
    Dyadic.dilate_mono P'.ωu hC.lt₂.le (show x ∈ P'.ωu.dilate C₂ from hx')
  have h5 : ξ ∈ P'.ωu.dilate C₁ := hsub1' hξ'
  have h6 := Dyadic.abs_sub_lt_of_mem_dilate h5 h4
  rw [abs_sub_comm] at h3
  have h7 : C₁ * P'.ωu.length ≤ (C₂ - C₃) * P.ωu.length / 2 := by
    calc C₁ * P'.ωu.length ≤ C₁ * ((C₂ - C₃) / (2 * C₁) * P.ωu.length) :=
          mul_le_mul_of_nonneg_left hsc hC1.le
      _ = (C₂ - C₃) * P.ωu.length / 2 := by field_simp
  have h8 : |x - ξ| < C₁ * P'.ωu.length := by rw [abs_sub_comm]; exact h6
  linarith

/-- **(i)**: in an `l`-overlapping tree satisfying (separationofscales), `|ω_u'| < |ω_u|` implies
`C₃ ω_u ∩ C₂ ω_u' = ∅` (L1291-L1292). -/
theorem treeobs_overlapping (hC : AdmissibleConstants C₁ C₂ C₃) (hρ : ρ.IsStd)
    (𝒯 : MultitileTree ρ) (hov : 𝒯.IsOverlapping C₂)
    (hsc : SeparationOfScales C₁ C₂ C₃ (𝒯.T : Set (Multitile ρ))) {P P' : Multitile ρ}
    (hP : P ∈ 𝒯.T) (hP' : P' ∈ 𝒯.T) (hlt : P'.ωu.length < P.ωu.length) :
    Disjoint (P.ωuDil C₃) (P'.ωuDil C₂) :=
  treeobs_overlapping_aux hC hρ (hov P hP) (hov P' hP') (hsc P hP P' hP' hlt)

/-- **(iii)**: in a tree satisfying (separationprop2), distinct multitiles `P ≠ P'` with
`|ω_u| = |ω_u'|` have disjoint time intervals (L1301-L1304). -/
theorem treeobs_disjoint_time (hC : AdmissibleConstants C₁ C₂ C₃) (hρ : ρ.IsStd) {M : ℤ}
    (𝒯 : MultitileTree ρ) (hT : 𝒯.IsTree C₁ C₂ M)
    (hp2 : SeparationProp2 C₁ (𝒯.T : Set (Multitile ρ))) {P P' : Multitile ρ}
    (hP : P ∈ 𝒯.T) (hP' : P' ∈ 𝒯.T) (hne : P ≠ P') (hlen : P.ωu.length = P'.ωu.length) :
    Disjoint P.I.toSet P'.I.toSet := by
  have hC2 : 1 < C₂ := lt_of_le_of_lt hC.one_le hC.lt₁
  have hξ := 𝒯.mem_ωT_self hC2
  have h1 : 𝒯.ξ ∈ P.ωuDil C₁ := Multitile.ωm_subset_ωuDil hC hρ P (hT.freq P hP hξ)
  have h2 : 𝒯.ξ ∈ P'.ωuDil C₁ := Multitile.ωm_subset_ωuDil hC hρ P' (hT.freq P' hP' hξ)
  have hωu : P.ωu = P'.ωu := hp2 P hP P' hP' ⟨𝒯.ξ, h1, h2⟩ hlen
  have hIne : P.I ≠ P'.I := fun h => hne (Multitile.ext h hωu)
  have hk : P.I.k = P'.I.k := by
    have e1 := P.area
    have e2 := P'.area
    rw [hωu] at e1
    omega
  exact Dyadic.disjoint_of_k_eq_of_ne hk hIne

/-- **Packets of different scales in an `l`-overlapping tree have disjoint `C₃`-dilated frequency
supports**: `C₃ ω_u ∩ C₃ ω_u' = ∅` whenever `|ω_u| ≠ |ω_u'|` (the consequence of (i) used for the
orthogonality of different scales, L1373-L1374). -/
theorem treeobs_disjoint_dilate (hC : AdmissibleConstants C₁ C₂ C₃) (hρ : ρ.IsStd)
    (𝒯 : MultitileTree ρ) (hov : 𝒯.IsOverlapping C₂)
    (hsc : SeparationOfScales C₁ C₂ C₃ (𝒯.T : Set (Multitile ρ))) {P P' : Multitile ρ}
    (hP : P ∈ 𝒯.T) (hP' : P' ∈ 𝒯.T) (hne : P.ωu.length ≠ P'.ωu.length) :
    Disjoint (P.ωu.dilate C₃) (P'.ωu.dilate C₃) := by
  rcases lt_or_gt_of_ne hne with h | h
  · -- `|ω_u| < |ω_u'|`: apply (i) with the roles exchanged
    have := treeobs_overlapping hC hρ 𝒯 hov hsc hP' hP h
    exact (this.mono_right (Dyadic.dilate_mono P.ωu hC.lt₁.le)).symm
  · have := treeobs_overlapping hC hρ 𝒯 hov hsc hP hP' h
    exact this.mono_right (Dyadic.dilate_mono P'.ωu hC.lt₁.le)

end PrimeCarleson.Proof.Oplus
