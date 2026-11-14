module

public import PrimeCarleson.Proof.Oplus.TreeSmall.Lacunary

/-!
# The scale structure of an `l`-overlapping tree ([O+] L2317-L2334)

Source: [O+] `intervalofscales2`, L2322–L2324; [O+] `intervalofscales`, L2317–L2321
(L2317-L2334): for an `l`-overlapping tree with
(jconsolidation) `ξ_T ∈ ω_l + j|ω_l|` the multitiles `P ∈ T` with `ξ_{k-1}(x) ∈ ω_l` (and
`ξ_k(x) ∈ ω_h`) have the time lengths `|I|` in an interval of scales (L2321-L2334). The proof of the
source is a sketch ("from the fact that ..."); here:

* `mem_middle_of_jconsolidation` (**`intervalofscales2`**): if `A, B, C` are dyadic intervals
  (the sets `ω_l` of three multitiles of scales `|A| ≥ |B| ≥ |C|`) containing the points
  `ξ - j|A|`, `ξ - j|B|`, `ξ - j|C|` and `y ∈ A ∩ C`, then `y ∈ B`. The cases are `|j| ≥ 2`
  (`A ∩ C = ∅`), `j = 0` (nested), `j = ±1` (the three-interval nesting): all by endpoint
  arithmetic from the nested-or-disjoint property of dyadic intervals;
* `mem_ωh_middle` (**the `ω_h` part of `intervalofscales`**, L2321-L2322): `ω_h` of the middle
  scale contains `y'` when it is in `ω_h` of the outer ones (for `1`- and `2`-indices), given that
  `y` is in the three `ω_l`; this needs only `m, n ≥ 0` and the factor `2` between scales;
* `scale_gap_of_separation`: the separation of scales as a gap `2^{k'-k} ≥ 2C₁/(C₂ - C₃)` between
  the time
  scales of two multitiles of the collection.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

namespace Dyadic

/-- `I ⊆ J` forces `left J ≤ left I`. -/
theorem left_le_of_toSet_subset {I J : Dyadic} (h : I.toSet ⊆ J.toSet) : J.left ≤ I.left :=
  (h I.left_mem_toSet).1

/-- `I ⊆ J` forces `right I ≤ right J`. -/
theorem right_le_of_toSet_subset {I J : Dyadic} (h : I.toSet ⊆ J.toSet) : I.right ≤ J.right := by
  by_contra hlt
  rw [not_le] at hlt
  have h1 : J.right ∈ I.toSet := ⟨(h I.left_mem_toSet).2.le, hlt⟩
  exact lt_irrefl _ (h h1).2

/-- A dyadic interval of smaller length through a point of a larger one lies inside it. -/
theorem toSet_subset_of_k_le_of_mem {I J : Dyadic} (hk : I.k ≤ J.k) {x : ℝ} (hI : x ∈ I.toSet)
    (hJ : x ∈ J.toSet) : I.toSet ⊆ J.toSet := by
  rcases I.toSet_subset_or_disjoint_of_k_le J hk with h | h
  · exact h
  · exact absurd hJ (Set.disjoint_left.1 h hI)

/-- The length is monotone in the scale. -/
theorem length_le_of_k_le {I J : Dyadic} (h : I.k ≤ J.k) : I.length ≤ J.length :=
  zpow_le_zpow_right₀ (by norm_num) h

/-- A strictly larger scale at least doubles the length. -/
theorem two_mul_length_le_of_k_lt {I J : Dyadic} (h : I.k < J.k) : 2 * I.length ≤ J.length := by
  unfold Dyadic.length
  calc 2 * (2 : ℝ) ^ I.k = (2 : ℝ) ^ (I.k + 1) := by rw [zpow_add_one₀ (by norm_num)]; ring
    _ ≤ (2 : ℝ) ^ J.k := zpow_le_zpow_right₀ (by norm_num) (by omega)

end Dyadic

/-- **The middle dyadic interval of a `j`-consolidated chain** ([O+] `intervalofscales2`, the
three facts of L2325-L2332): let `A ⊇ ... ` be dyadic intervals with `C.k ≤ B.k ≤ A.k` containing
the points `ξ - j|A|`, `ξ - j|B|`, `ξ - j|C|` respectively; if a point `y` lies in `A` and in `C`
then it lies in `B`. -/
theorem mem_middle_of_jconsolidation {A B C : Dyadic} (hAB : B.k ≤ A.k) (hBC : C.k ≤ B.k)
    {ξ y : ℝ} {j : ℤ} (hA : ξ - j * A.length ∈ A.toSet) (hB : ξ - j * B.length ∈ B.toSet)
    (hC : ξ - j * C.length ∈ C.toSet) (hyA : y ∈ A.toSet) (hyC : y ∈ C.toSet) :
    y ∈ B.toSet := by
  rcases hAB.eq_or_lt with hAB' | hAB'
  · have hl : A.length = B.length := Dyadic.length_eq_iff.2 hAB'.symm
    have : A = B := Dyadic.eq_of_k_eq_of_mem hAB'.symm hA (by rwa [hl])
    exact this ▸ hyA
  rcases hBC.eq_or_lt with hBC' | hBC'
  · have hl : B.length = C.length := Dyadic.length_eq_iff.2 hBC'.symm
    have : B = C := Dyadic.eq_of_k_eq_of_mem hBC'.symm hB (by rwa [hl])
    exact this ▸ hyC
  have hCA : C.toSet ⊆ A.toSet := Dyadic.toSet_subset_of_k_le_of_mem (by omega) hyC hyA
  have hca : 2 * C.length ≤ A.length := Dyadic.two_mul_length_le_of_k_lt (by omega)
  have hcb : C.length ≤ B.length := Dyadic.length_le_of_k_le hBC
  have hC0 := C.length_pos
  have hB0 := B.length_pos
  have hA0 := A.length_pos
  -- the shifted intervals all contain `ξ`
  have hA' : ξ ∈ (A.shift j).toSet := (Dyadic.mem_shift_toSet A j).2 hA
  have hB' : ξ ∈ (B.shift j).toSet := (Dyadic.mem_shift_toSet B j).2 hB
  have hC' : ξ ∈ (C.shift j).toSet := (Dyadic.mem_shift_toSet C j).2 hC
  have hBA : (B.shift j).toSet ⊆ (A.shift j).toSet :=
    Dyadic.toSet_subset_of_k_le_of_mem hAB hB' hA'
  have hCB : (C.shift j).toSet ⊆ (B.shift j).toSet :=
    Dyadic.toSet_subset_of_k_le_of_mem hBC hC' hB'
  have e1 := Dyadic.left_le_of_toSet_subset hBA
  have e2 := Dyadic.right_le_of_toSet_subset hBA
  have e3 := Dyadic.left_le_of_toSet_subset hCB
  have e4 := Dyadic.right_le_of_toSet_subset hCB
  have e5 := Dyadic.left_le_of_toSet_subset hCA
  have e6 := Dyadic.right_le_of_toSet_subset hCA
  simp only [Dyadic.left_shift, Dyadic.right_eq, Dyadic.length_shift] at e1 e2 e3 e4
  rw [Dyadic.right_eq, Dyadic.right_eq] at e6
  obtain ⟨hy1, hy2⟩ := hyC
  rw [Dyadic.right_eq] at hy2
  rw [Dyadic.mem_toSet, Dyadic.right_eq]
  rcases (show j ≤ -2 ∨ j = -1 ∨ j = 0 ∨ j = 1 ∨ 2 ≤ j by omega) with h | h | h | h | h
  · exfalso
    -- both `ξ - j|A|` and `ξ - j|C|` lie in `A`
    have hCm : ξ - j * C.length ∈ A.toSet := hCA hC
    obtain ⟨a1, a2⟩ := hA
    obtain ⟨c1, c2⟩ := hCm
    rw [Dyadic.right_eq] at a2 c2
    have hj : (j : ℝ) ≤ -2 := by exact_mod_cast h
    nlinarith
  · subst h
    push_cast at *
    constructor <;> linarith
  · subst h
    push_cast at *
    constructor <;> linarith
  · subst h
    push_cast at *
    constructor <;> linarith
  · exfalso
    have hCm : ξ - j * C.length ∈ A.toSet := hCA hC
    obtain ⟨a1, a2⟩ := hA
    obtain ⟨c1, c2⟩ := hCm
    rw [Dyadic.right_eq] at a2 c2
    have hj : (2 : ℝ) ≤ j := by exact_mod_cast h
    nlinarith


section TreeScales

variable {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ C₃ : ℝ} {M : ℤ}

omit [Fact ρ.IsOneOrTwo] in
/-- `y ∈ ω_h` for a `1`-index. -/
theorem Multitile.mem_ωh_iff_one (P : Multitile ρ) (h : ρ.typ = IdxType.one) (y : ℝ) :
    y ∈ P.ωh ↔ P.ωu.left + ((ρ.n : ℝ) + 1) * P.ωu.length ≤ y ∧
      y < P.ωu.left + ((ρ.n : ℝ) + 2) * P.ωu.length := by
  unfold Multitile.ωh Idx.ωh
  rw [h]
  simp only [Dyadic.mem_toSet, Dyadic.left_shift, Dyadic.right_eq, Dyadic.length_shift]
  push_cast
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩

omit [Fact ρ.IsOneOrTwo] in
/-- `y ∈ ω_h` for a `2`-index. -/
theorem Multitile.mem_ωh_iff_two (P : Multitile ρ) (h : ρ.typ = IdxType.two) (y : ℝ) :
    y ∈ P.ωh ↔ P.ωu.left + ((ρ.n : ℝ) + 1) * P.ωu.length ≤ y := by
  unfold Multitile.ωh Idx.ωh
  rw [h]
  simp only [Set.mem_Ici]

/-- **`ω_h` is an interval of scales** (the passage from `intervalofscales2` to
`intervalofscales`, L2321-L2322): if `y ∈ ω_l` of three multitiles `P₁, P, P₂` with scales
`|ω_u(P₁)| ≥ 2|ω_u(P)| ≥ 4|ω_u(P₂)|` and `y' ∈ ω_h` of `P₁` and `P₂` then `y' ∈ ω_h(P)`. -/
theorem mem_ωh_middle {P₁ P P₂ : Multitile ρ} {y y' : ℝ}
    (h₁ : 2 * P.ωu.length ≤ P₁.ωu.length) (h₂ : 2 * P₂.ωu.length ≤ P.ωu.length)
    (hl₁ : y ∈ P₁.ωl) (hl : y ∈ P.ωl) (hl₂ : y ∈ P₂.ωl) (hh₁ : y' ∈ P₁.ωh)
    (hh₂ : y' ∈ P₂.ωh) : y' ∈ P.ωh := by
  rw [Multitile.mem_ωl_iff] at hl₁ hl hl₂
  have hL := P.ωu.length_pos
  have hL₂ := P₂.ωu.length_pos
  have hm : (0 : ℝ) ≤ ρ.m := Nat.cast_nonneg _
  have hn : (0 : ℝ) ≤ ρ.n := Nat.cast_nonneg _
  have c1 := P₁.ωu.center_eq
  have c2 := P.ωu.center_eq
  have c3 := P₂.ωu.center_eq
  have h12 : ρ.typ ≠ IdxType.three := (Fact.out : ρ.IsOneOrTwo)
  have p1 := mul_nonneg (by positivity : (0 : ℝ) ≤ (ρ.m : ℝ) + ρ.n + 1) (sub_nonneg.2 h₁)
  have p2 := mul_nonneg (add_nonneg hm hn) hL.le
  have p3 := mul_nonneg (by positivity : (0 : ℝ) ≤ (ρ.m : ℝ) + ρ.n + 3) (sub_nonneg.2 h₂)
  have p4 := mul_nonneg (by positivity : (0 : ℝ) ≤ (ρ.m : ℝ) + ρ.n + 1) hL.le
  rcases h : ρ.typ with _ | _ | _
  · rw [Multitile.mem_ωh_iff_one _ h] at hh₁ hh₂ ⊢
    constructor
    · linarith only [hh₁.1, hl₁.2, hl.1, c1, c2, p1, p2]
    · linarith only [hh₂.2, hl.2, hl₂.1, c2, c3, p3, p4]
  · rw [Multitile.mem_ωh_iff_two _ h] at hh₁ ⊢
    linarith only [hh₁, hl₁.2, hl.1, c1, c2, p1, p2]
  · exact absurd h h12

omit [Fact ρ.IsOneOrTwo] in
/-- Multitiles of one scale in a tree have the same `ω_u`. -/
theorem Multitile.ωu_eq_of_k_eq_of_tree (hC : AdmissibleConstants C₁ C₂ C₃) (hρ : ρ.IsStd)
    [Fact ρ.IsOneOrTwo] {𝒯 : MultitileTree ρ} (hT : 𝒯.IsTree C₁ C₂ M)
    (hp2 : SeparationProp2 C₁ (𝒯.T : Set (Multitile ρ))) {P P' : Multitile ρ} (hP : P ∈ 𝒯.T)
    (hP' : P' ∈ 𝒯.T) (hk : P.I.k = P'.I.k) : P.ωu = P'.ωu :=
  ωu_eq_of_I_length_eq_of_tree hC hρ hT hp2 hP hP' (Dyadic.length_eq_iff.2 hk)

omit [Fact ρ.IsOneOrTwo] in
/-- `|ω_u|` and the scale: `|ω_u| = 2^{-1-k}`. -/
theorem Multitile.length_ωu_eq (P : Multitile ρ) : P.ωu.length = (2 : ℝ) ^ (-1 - P.I.k) := by
  unfold Dyadic.length
  congr 1
  have := P.area
  omega

omit [Fact ρ.IsOneOrTwo] in
/-- **Separation of scales** as a gap: if `k < k'` then `2^{k'-k} ≥ 2C₁/(C₂-C₃)`. -/
theorem scale_gap_of_separation (hC : AdmissibleConstants C₁ C₂ C₃)
    {S : Set (Multitile ρ)} (hsc : SeparationOfScales C₁ C₂ C₃ S) {P P' : Multitile ρ}
    (hP : P ∈ S) (hP' : P' ∈ S) (hk : P.I.k < P'.I.k) :
    2 * C₁ / (C₂ - C₃) ≤ (2 : ℝ) ^ (P'.I.k - P.I.k) := by
  have hC1 : 0 < C₁ := by linarith [hC.one_le, hC.lt₁, hC.lt₂]
  have hC23 : 0 < C₂ - C₃ := by linarith [hC.lt₁]
  have hlt : P'.ωu.length < P.ωu.length := by
    rw [Multitile.length_ωu_eq, Multitile.length_ωu_eq]
    exact zpow_lt_zpow_right₀ (by norm_num) (by omega)
  have h := hsc P hP P' hP' hlt
  rw [Multitile.length_ωu_eq, Multitile.length_ωu_eq] at h
  have e : (2 : ℝ) ^ (-1 - P.I.k) = (2 : ℝ) ^ (-1 - P'.I.k) * (2 : ℝ) ^ (P'.I.k - P.I.k) := by
    rw [← zpow_add₀ (by norm_num)]
    congr 1; ring
  rw [e] at h
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (-1 - P'.I.k) := zpow_pos (by norm_num) _
  have h1 : 1 ≤ (C₂ - C₃) / (2 * C₁) * (2 : ℝ) ^ (P'.I.k - P.I.k) := by
    have := h
    nlinarith
  rw [div_le_iff₀ hC23]
  have : 2 * C₁ ≤ (C₂ - C₃) * (2 : ℝ) ^ (P'.I.k - P.I.k) := by
    have h2 : 1 ≤ (C₂ - C₃) * (2 : ℝ) ^ (P'.I.k - P.I.k) / (2 * C₁) := by
      rwa [div_mul_eq_mul_div] at h1
    rwa [le_div_iff₀ (by positivity), one_mul] at h2
  linarith

end TreeScales

end PrimeCarleson.Proof.Oplus
