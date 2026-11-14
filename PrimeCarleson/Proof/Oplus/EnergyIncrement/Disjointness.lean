module

public import PrimeCarleson.Proof.Oplus.EnergyIncrement.Geometry

/-!
# The disjointness claim ([O+] L1583-L1622)

Source: [O+], L1583–L1590 (L1583-L1622):
"Consider two multitiles `P¹ = (I¹, ω_u¹) ∈ S_{κ₁}` and `P² = (I², ω_u²) ∈ S_{κ₂}`, `P¹ ≠ P²`, so
that `|I²| ≤ |I¹|` and `C₃ ω_u¹ ∩ C₃ ω_u² ≠ ∅`. [...] Then `I¹ ∩ I² = ∅`, and if in addition
`|I²| < |I¹|` then `I²` does not belong to the top interval of the tree `S_{κ₁}`."

* `claim_pair` is this statement, in the form `|c(ω_u¹) - c(ω_u²)| ≤ C₃(|ω_u¹| + |ω_u²|)/2` (the two
  closed `C₃`-dilates meet; a point `sup C₃ ω_u ∈ C₃ ω_u'` gives this too), for every pair of
  multitiles of the selected trees `S_j`, `S_k` of `IsSelection`. The proof follows the source:
  equal sizes by (separationprop2); `|I²| < |I¹|`: in one tree `S` it contradicts the `l`-overlap
  (`ωuDil_right_le_left`, the Observation (i)); in two trees, (separationofscales) gives
  `inf C₂ ω_l¹ > sup C₂ ω_l²` hence `ξ_{S_{κ₂}} < ξ_{S_{κ₁}}`, so `κ₁ < κ₂`, so `P²` is not in
  `T_{κ₁}`,
  and `ω_{S_{κ₁}} ⊂ ω_m(P¹) ⊂ ω_m(P²)` (`ωm_subset_ωm_of_near`) forces `I² ∩ I_{S_{κ₁}} = ∅`
  by the maximality of `T_{κ₁}`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

section Near

variable {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ C₃ : ℝ}

/-- The closed `C₃`-dilates of `ω_u` and `ω_u'` meet or touch: `|c - c'| ≤ C₃(|ω_u| + |ω_u'|)/2`. -/
def Multitile.Near (C₃ : ℝ) (P P' : Multitile ρ) : Prop :=
  |P.ωu.center - P'.ωu.center| ≤ C₃ * (P.ωu.length + P'.ωu.length) / 2

omit [Fact ρ.IsOneOrTwo] in
/-- `Near` is symmetric. -/
theorem Multitile.Near.symm {C₃ : ℝ} {P P' : Multitile ρ} (h : Multitile.Near C₃ P P') :
    Multitile.Near C₃ P' P := by
  unfold Multitile.Near at *
  rw [abs_sub_comm]
  linarith

omit [Fact ρ.IsOneOrTwo] in
/-- Intersecting `C₃`-dilates are near. -/
theorem Multitile.Near.of_inter {C₃ : ℝ} {P P' : Multitile ρ}
    (h : (P.ωuDil C₃ ∩ P'.ωuDil C₃).Nonempty) : Multitile.Near C₃ P P' := by
  obtain ⟨x, hx, hx'⟩ := h
  obtain ⟨h1, h2⟩ := hx
  obtain ⟨h3, h4⟩ := hx'
  unfold Multitile.Near
  rw [abs_le]
  constructor <;> linarith

omit [Fact ρ.IsOneOrTwo] in
/-- If `sup C₃ ω_u ∈ C₃ ω_u'` then `P, P'` are near. -/
theorem Multitile.Near.of_right_mem {C₃ : ℝ} (hC : 0 ≤ C₃) {P P' : Multitile ρ}
    (h : P.ωu.center + C₃ * P.ωu.length / 2 ∈ P'.ωuDil C₃) : Multitile.Near C₃ P P' := by
  obtain ⟨h1, h2⟩ := h
  have := P.ωu.length_pos
  unfold Multitile.Near
  rw [abs_le]
  constructor <;> nlinarith

omit [Fact ρ.IsOneOrTwo] in
/-- If `inf C₃ ω_u ∈ C₃ ω_u'` then `P, P'` are near. -/
theorem Multitile.Near.of_left_mem {C₃ : ℝ} (hC : 0 ≤ C₃) {P P' : Multitile ρ}
    (h : P.ωu.center - C₃ * P.ωu.length / 2 ∈ P'.ωuDil C₃) : Multitile.Near C₃ P P' := by
  obtain ⟨h1, h2⟩ := h
  have := P.ωu.length_pos
  unfold Multitile.Near
  rw [abs_le]
  constructor <;> nlinarith

omit [Fact ρ.IsOneOrTwo] in
/-- If the `C₃`-dilates of `P` and `P'` intersect and `|ω_u| < |ω_u'|`, then `inf C₃ ω_u` or
`sup C₃ ω_u` lies in `C₃ ω_u'` (L1209-L1210: "`sup C₃ ω_u ∈ C₃ ω_u'` or `inf C₃ ω_u ∈ C₃ ω_u'`"). -/
theorem Multitile.mem_dilate_of_inter_of_length_lt {C₃ : ℝ} {P P' : Multitile ρ}
    (h : (P.ωuDil C₃ ∩ P'.ωuDil C₃).Nonempty) (hlt : P.ωu.length < P'.ωu.length) :
    P.ωu.center + C₃ * P.ωu.length / 2 ∈ P'.ωuDil C₃ ∨
      P.ωu.center - C₃ * P.ωu.length / 2 ∈ P'.ωuDil C₃ := by
  obtain ⟨x, hx, hx'⟩ := h
  obtain ⟨h1, h2⟩ := hx
  obtain ⟨h3, h4⟩ := hx'
  have hC : 0 ≤ C₃ := by
    by_contra hneg
    rw [not_le] at hneg
    have := P.ωu.length_pos
    nlinarith
  by_cases hc : P'.ωu.center - C₃ * P'.ωu.length / 2 ≤ P.ωu.center - C₃ * P.ωu.length / 2
  · right
    constructor
    · exact hc
    · nlinarith
  · left
    rw [not_le] at hc
    constructor
    · nlinarith
    · nlinarith

/-- `ω_m(P) ⊂ ω_m(P')` when the `C₃`-dilates are near and `|ω_u| ≤ ((C₂ - C₃)/(2C₁))|ω_u'|`. -/
theorem ωm_subset_ωm_of_near (hC : AdmissibleConstants C₁ C₂ C₃) (hρ : ρ.IsStd)
    {P P' : Multitile ρ} (hnear : Multitile.Near C₃ P P')
    (hsc : P.ωu.length ≤ (C₂ - C₃) / (2 * C₁) * P'.ωu.length) : P.ωm C₂ ⊆ P'.ωm C₂ := by
  have hL := P.ωu.length_pos
  have hL' := P'.ωu.length_pos
  have hC1 : 0 < C₁ := by linarith [hC.one_le, hC.lt₁, hC.lt₂]
  have hC₂ : 0 < C₂ := by linarith [hC.one_le, hC.lt₁]
  have h1 := hC.le_m_add_one hρ
  have h2 := hC.two_m_add_one_add_le hρ
  have h7 : 2 * C₁ * P.ωu.length ≤ (C₂ - C₃) * P'.ωu.length := by
    calc 2 * C₁ * P.ωu.length = 2 * (C₁ * P.ωu.length) := by ring
      _ ≤ 2 * (C₁ * ((C₂ - C₃) / (2 * C₁) * P'.ωu.length)) := by gcongr
      _ = (C₂ - C₃) * P'.ωu.length := by field_simp
  unfold Multitile.Near at hnear
  rw [abs_le] at hnear
  rw [Multitile.ωm_eq_Ico hC₂, Multitile.ωm_eq_Ico hC₂]
  have hsL : ((ρ.m : ℝ) + 1) * P.ωu.length ≤ (C₁ - C₂) / 2 * P.ωu.length :=
    mul_le_mul_of_nonneg_right (by linarith) hL.le
  have hsL' : C₂ * P'.ωu.length ≤ ((ρ.m : ℝ) + 1) * P'.ωu.length :=
    mul_le_mul_of_nonneg_right h1 hL'.le
  have h3L : C₃ * P.ωu.length ≤ C₁ * P.ωu.length :=
    mul_le_mul_of_nonneg_right (by linarith [hC.lt₁, hC.lt₂]) hL.le
  have h2L : C₂ * P.ωu.length ≤ C₁ * P.ωu.length :=
    mul_le_mul_of_nonneg_right hC.lt₂.le hL.le
  have hsL0 : 0 ≤ ((ρ.m : ℝ) + 1) * P.ωu.length := by positivity
  apply Ico_subset_Ico
  · nlinarith
  · nlinarith

/-- **`ξ' < ξ`**: for near multitiles with `|ω_u| ≤ ((C₂ - C₃)/(2C₁))|ω_u'|`, any point of
`C₂ ω_l(P')` lies below any point of `C₂ ω_l(P)` (`inf C₂ ω_l(P) > sup C₂ ω_l(P')`, L1608-L1613). -/
theorem xi_lt_of_near (hC : AdmissibleConstants C₁ C₂ C₃) (hρ : ρ.IsStd) {P P' : Multitile ρ}
    (hnear : Multitile.Near C₃ P P') (hsc : P.ωu.length ≤ (C₂ - C₃) / (2 * C₁) * P'.ωu.length)
    {ξ ξ' : ℝ} (hξ : ξ ∈ P.ωlDil C₂) (hξ' : ξ' ∈ P'.ωlDil C₂) : ξ' < ξ := by
  have hL := P.ωu.length_pos
  have hL' := P'.ωu.length_pos
  have hC1 : 0 < C₁ := by linarith [hC.one_le, hC.lt₁, hC.lt₂]
  have h1 := hC.le_m_add_one hρ
  have h2 := hC.two_m_add_one_add_le hρ
  have h7 : 2 * C₁ * P.ωu.length ≤ (C₂ - C₃) * P'.ωu.length := by
    calc 2 * C₁ * P.ωu.length = 2 * (C₁ * P.ωu.length) := by ring
      _ ≤ 2 * (C₁ * ((C₂ - C₃) / (2 * C₁) * P'.ωu.length)) := by gcongr
      _ = (C₂ - C₃) * P'.ωu.length := by field_simp
  unfold Multitile.Near at hnear
  rw [abs_le] at hnear
  rw [P.ωlDil_eq] at hξ
  rw [P'.ωlDil_eq] at hξ'
  obtain ⟨hξ1, -⟩ := hξ
  obtain ⟨-, hξ2'⟩ := hξ'
  have hsL : ((ρ.m : ℝ) + 1) * P.ωu.length ≤ (C₁ - C₂) / 2 * P.ωu.length :=
    mul_le_mul_of_nonneg_right (by linarith) hL.le
  have hsL' : C₂ * P'.ωu.length ≤ ((ρ.m : ℝ) + 1) * P'.ωu.length :=
    mul_le_mul_of_nonneg_right h1 hL'.le
  have h3L : C₃ * P.ωu.length ≤ C₁ * P.ωu.length :=
    mul_le_mul_of_nonneg_right (by linarith [hC.lt₁, hC.lt₂]) hL.le
  nlinarith

end Near

section Claim

variable {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ C₃ : ℝ} {M : ℤ} {ch : ProfileChoice} {f : ℝ → ℂ}
  {e : ℝ} {𝔓 : Finset (Multitile ρ)} {n : ℕ} {S T : ℕ → MultitileTree ρ}

omit [Fact ρ.IsOneOrTwo] in
/-- Equal time lengths give equal frequency lengths (the area condition). -/
theorem Multitile.ωu_length_eq_of_I_length_eq {P P' : Multitile ρ}
    (h : P.I.length = P'.I.length) : P.ωu.length = P'.ωu.length := by
  have h1 := Dyadic.length_eq_iff.1 h
  rw [Dyadic.length_eq_iff]
  have := P.area
  have := P'.area
  omega

omit [Fact ρ.IsOneOrTwo] in
/-- A smaller time length is a larger frequency length. -/
theorem Multitile.ωu_length_lt_of_I_length_lt {P P' : Multitile ρ}
    (h : P'.I.length < P.I.length) : P.ωu.length < P'.ωu.length := by
  have h1 := Dyadic.length_lt_iff.1 h
  rw [Dyadic.length_lt_iff]
  have := P.area
  have := P'.area
  omega

omit [Fact ρ.IsOneOrTwo] in
/-- **(separationprop2) for near multitiles of one time length**: if `P, P' ∈ 𝔓` have
`|I| = |I'|` and their closed `C₃`-dilates meet, then `ω_u = ω_u'` (L1280-L1282, L1549, L1599). -/
theorem ωu_eq_of_near_of_I_length_eq (hC : AdmissibleConstants C₁ C₂ C₃)
    {𝔓 : Finset (Multitile ρ)} (hsep : Separated C₁ C₂ C₃ (𝔓 : Set (Multitile ρ)))
    {P P' : Multitile ρ} (hP : P ∈ 𝔓) (hP' : P' ∈ 𝔓) (hlen : P.I.length = P'.I.length)
    (hnear : Multitile.Near C₃ P P') : P.ωu = P'.ωu := by
  have hL := P.ωu.length_pos
  have hlen' := Multitile.ωu_length_eq_of_I_length_eq hlen
  have hd : C₃ * P.ωu.length < C₁ * P.ωu.length :=
    mul_lt_mul_of_pos_right (lt_trans hC.lt₁ hC.lt₂) hL
  refine hsep.prop2 P hP P' hP' ⟨(P.ωu.center + P'.ωu.center) / 2, ?_, ?_⟩ hlen'
  · rw [Multitile.ωuDil_eq]
    unfold Multitile.Near at hnear
    rw [abs_le] at hnear
    rw [← hlen'] at hnear
    constructor <;> linarith [hnear.1, hnear.2]
  · rw [Multitile.ωuDil_eq]
    unfold Multitile.Near at hnear
    rw [abs_le] at hnear
    rw [← hlen'] at hnear
    rw [← hlen']
    constructor <;> linarith [hnear.1, hnear.2]

/-- **`claimofdisjointness`** ([O+] L1583-L1622). Let `P ∈ S_j`, `P' ∈ S_k` be multitiles with
`|I'| ≤ |I|` whose closed `C₃`-dilates meet (`Near`), `P ≠ P'`. Then `I ∩ I' = ∅`, and if
`|I'| < |I|` then `I'` is disjoint from the top interval `I_{S_j}`. -/
theorem claim_pair (hC : AdmissibleConstants C₁ C₂ C₃) (hρ : ρ.IsStd)
    (hsep : Separated C₁ C₂ C₃ (𝔓 : Set (Multitile ρ)))
    (sel : IsSelection C₁ C₂ M ch f e 𝔓 n S T) {j k : ℕ} (hj : j < n) (hk : k < n)
    {P P' : Multitile ρ} (hP : P ∈ (S j).T) (hP' : P' ∈ (S k).T) (hne : P ≠ P')
    (hle : P'.I.length ≤ P.I.length) (hnear : Multitile.Near C₃ P P') :
    Disjoint P.I.toSet P'.I.toSet ∧
      (P'.I.length < P.I.length → Disjoint P'.I.toSet (S j).I.toSet) := by
  have hPm : P ∈ 𝔓 := (mem_remainingFamily.1 (sel.S_subset_rem hj hP)).1
  have hPm' : P' ∈ 𝔓 := (mem_remainingFamily.1 (sel.S_subset_rem hk hP')).1
  have hC₂ : 0 < C₂ := by linarith [hC.one_le, hC.lt₁]
  have hC1 : 0 < C₁ := by linarith [hC.one_le, hC.lt₁, hC.lt₂]
  have hL := P.ωu.length_pos
  have hL' := P'.ωu.length_pos
  rcases eq_or_lt_of_le hle with heq | hlt
  · -- equal sizes: (separationprop2)
    have hω : P.ωu = P'.ωu :=
      ωu_eq_of_near_of_I_length_eq hC hsep hPm hPm' heq.symm hnear
    have hIne : P.I ≠ P'.I := fun h => hne (Multitile.ext h hω)
    have hk' : P.I.k = P'.I.k := Dyadic.length_eq_iff.1 heq.symm
    exact ⟨Dyadic.disjoint_of_k_eq_of_ne hk' hIne, fun h => absurd h (not_lt.2 heq.symm.le)⟩
  · -- `|I'| < |I|`
    have hlt' : P.ωu.length < P'.ωu.length := Multitile.ωu_length_lt_of_I_length_lt hlt
    have hsc : P.ωu.length ≤ (C₂ - C₃) / (2 * C₁) * P'.ωu.length :=
      hsep.scales P' hPm' P hPm hlt'
    by_cases hjk : j = k
    · -- the same `l`-overlapping tree: impossible
      subst hjk
      exfalso
      have hov := sel.S_overlapping hj
      have h1 := ωuDil_right_le_left hC hρ (hov P' hP') (hov P hP) le_rfl hsc
      unfold Multitile.Near at hnear
      rw [abs_le] at hnear
      have h2 : C₃ * P'.ωu.length / 2 + C₂ * P.ωu.length / 2 ≤ P'.ωu.center - P.ωu.center := by
        linarith
      nlinarith [hC.lt₁]
    · -- two different trees
      have hξ : (S k).ξ < (S j).ξ :=
        xi_lt_of_near hC hρ hnear hsc ((sel.S_overlapping hj) P hP) ((sel.S_overlapping hk) P' hP')
      have hjk' : j < k := by
        rcases lt_or_gt_of_ne hjk with h | h
        · exact h
        · exact absurd (sel.xi_le h.le hj) (not_le.2 hξ)
      have hPrem : P' ∈ remainingFamily 𝔓 T j :=
        remainingFamily_anti hjk'.le (sel.S_subset_rem hk hP')
      have hnotT : P' ∉ (T j).T :=
        not_mem_of_mem_remainingFamily hjk' (sel.S_subset_rem hk hP')
      have hdisj : Disjoint P'.I.toSet (S j).I.toSet := by
        by_contra hnd
        have hsub : P'.I.toSet ⊆ (S j).I.toSet := by
          refine Dyadic.toSet_subset_of_length_le_of_not_disjoint ?_ hnd
          have h1 : P.I.toSet ⊆ (S j).I.toSet := (sel.S_isTree hj).time P hP
          have h2 := Dyadic.k_le_of_toSet_subset h1
          exact (hlt.le).trans (Dyadic.length_le_iff.2 h2)
        refine hnotT (sel.mem_T_of_mem_rem hj hPrem hsub ?_)
        have hfreq := (sel.S_isTree hj).freq P hP
        exact hfreq.trans (ωm_subset_ωm_of_near hC hρ hnear hsc)
      refine ⟨?_, fun _ => hdisj⟩
      exact hdisj.symm.mono_left ((sel.S_isTree hj).time P hP)

end Claim

end PrimeCarleson.Proof.Oplus
