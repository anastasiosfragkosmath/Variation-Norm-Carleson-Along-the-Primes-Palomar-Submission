module

public import PrimeCarleson.Proof.Oplus.EnergyIncrement.PisaTerms

/-!
# The third term of `pisatree` ([O+] L1855-L1894)

Source: [O+] `pisatree`, L1855–L1894:
"Suppose `P ∈ T' ∩ S`, `Pt ∈ T' ∩ S̃` where `ξ_{T'} ∈ [sup C₂ ω_l, inf C₃ ω_u) ∩ [sup C₂ ω̃_l,
inf C₃ ω̃_u)`, and `I ⊂ Ĩ`, `P ≠ Pt`. From (separationprop2) we have `I ⊊ Ĩ`. We also have `inf C₂
ω̃_l < sup C₂ ω_l` since otherwise it would follow that `S̃` was selected prior to `S` and hence
`P ∈ T̃` which is impossible. From (separationofscales), we have `inf C₂ ω̃_l ≥ sup C₃ ω_l` and so
`P` is in the maximal `l`-overlapping tree contained in `T'` with top data `(Ĩ, inf C₂ ω̃_l)`. For
each `T'` let `T''` be the collection of `P ∈ T' ∩ ⋃ S` with `ξ_{T'} ∈ [sup C₂ ω_l, inf C₃ ω_u)`
and `I`
maximal among such multitiles. Then the sum is at most `∑_{T'} ∑_{P'' ∈ T''} 2 e² |I''|`".

* `gTree T' Pt`: the maximal `l`-overlapping tree in `T'` with top data `(Ĩ, inf C₂ ω̃_l)`
  (`inf C₂ ω̃_l = c(ω̃_l) - |ω̃_u|` for `C₂ = 2`), a tree because `inf C₂ ω̃_l ∈ 𝒳_top`
  (`Multitile.inf_ωl_mem_Xtop`); `sum_gTree_le`: its energy sum is `≤ e² |Ĩ|`;
* `case3_mem_gTree`: the preliminary observation of the source: `P ∈ gTree T' Pt`;
* `pisatree_third_term`: the packet `P''` of maximal `I` itself contributes `≤ e² |I''|` (it is
  *not* in `gTree T' P''`: `ω_𝒯 ⊄ ω_m(P'')`), the others `≤ e² |I''|`; the maximal `I''` are
  pairwise
  disjoint (Observation (iii)): total `≤ 2 e² |I_{T'}|`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

section Third

variable {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ C₃ : ℝ} {M : ℤ} {ch : ProfileChoice} {f : ℝ → ℂ}
  {e : ℝ} {𝔓 : Finset (Multitile ρ)} {n : ℕ} {S T : ℕ → MultitileTree ρ}

/-- The top frequency `inf C₂ ω̃_l = c(ω̃_l) - |ω̃_u|` for `C₂ = 2`. -/
def Multitile.topXi (P : Multitile ρ) : ℝ := (ρ.ωlDyadic P.ωu).center - P.ωu.length

omit [Fact ρ.IsOneOrTwo] in
/-- `inf C₂ ω_l = c - (m+1)|ω_u| - |ω_u|`. -/
theorem Multitile.topXi_eq (P : Multitile ρ) :
    P.topXi = P.ωu.center - ((ρ.m : ℝ) + 1) * P.ωu.length - P.ωu.length := by
  unfold Multitile.topXi; rw [Idx.center_ωlDyadic]

open Classical in
/-- The maximal `l`-overlapping tree in `T'` with top data `(Ĩ, inf C₂ ω̃_l)`. -/
def gTree (C₂ : ℝ) (T' : MultitileTree ρ) (Pt : Multitile ρ) : MultitileTree ρ :=
  ⟨T'.T.filter (fun Q => Q.I.toSet ⊆ Pt.I.toSet ∧
      (⟨∅, Pt.I, Pt.topXi⟩ : MultitileTree ρ).ωT C₂ ⊆ Q.ωm C₂ ∧ Pt.topXi ∈ Q.ωlDil C₂),
    Pt.I, Pt.topXi⟩

/-- `gTree T' Pt` is an `l`-overlapping tree. -/
theorem gTree_isTree (hC : AdmissibleConstants C₁ C₂ C₃) (hρ : ρ.IsStd) (hC₂ : C₂ = 2)
    {T' : MultitileTree ρ} (hT' : T'.IsTree C₁ C₂ M) {Pt : Multitile ρ} (hPt : Pt.InSquare M) :
    (gTree C₂ T' Pt).IsTree C₁ C₂ M ∧ (gTree C₂ T' Pt).IsOverlapping C₂ := by
  classical
  refine ⟨⟨Dyadic.toSet_subset_Ico_of_subset_Icc hPt.1, ?_, fun Q hQ => ?_, fun Q hQ => ?_⟩,
    fun Q hQ => ?_⟩
  · subst hC₂
    exact Multitile.inf_ωl_mem_Xtop hρ (by linarith [hC.one_le, hC.lt₁, hC.lt₂]) hPt
  · exact (Finset.mem_filter.1 hQ).2.1
  · exact (Finset.mem_filter.1 hQ).2.2.1
  · exact (Finset.mem_filter.1 hQ).2.2.2

/-- **The energy of `gTree T' Pt`**: `∑_{Q ∈ gTree T' Pt} |⟨f, φ_Q⟩|² ≤ e² |Ĩ|`. -/
theorem sum_gTree_le (hC : AdmissibleConstants C₁ C₂ C₃) (hρ : ρ.IsStd) (hC₂ : C₂ = 2)
    (he : 0 ≤ e) (hen : energy C₁ C₂ M ch f (𝔓 : Set (Multitile ρ)) ≤ ENNReal.ofReal e)
    {T' : MultitileTree ρ} (hT' : T'.IsTree C₁ C₂ M) (hsub : (T'.T : Set (Multitile ρ)) ⊆ 𝔓)
    {Pt : Multitile ρ} (hPt : Pt.InSquare M) :
    ∑ Q ∈ (gTree C₂ T' Pt).T, ‖Q.coeff ch f‖ ^ 2 ≤ e ^ 2 * Pt.I.length := by
  classical
  obtain ⟨h1, h2⟩ := gTree_isTree hC hρ hC₂ hT' hPt
  exact sum_norm_sq_coeff_le_of_energy_le he hen h1 h2 (fun Q hQ =>
    hsub (Finset.mem_coe.2 (Finset.mem_filter.1 (Finset.mem_coe.1 hQ)).1))

/-- **The preliminary observation of the third term** (L1857-L1871): `P ∈ gTree T' Pt`. -/
theorem case3_mem_gTree (hC : AdmissibleConstants C₁ C₂ C₃) (hC₂ : C₂ = 2) (hρ : ρ.IsStd)
    (hsep : Separated C₁ C₂ C₃ (𝔓 : Set (Multitile ρ)))
    (sel : IsSelection C₁ C₂ M ch f e 𝔓 n S T) {T' : MultitileTree ρ} (hT' : T'.IsTree C₁ C₂ M)
    (hsub : (T'.T : Set (Multitile ρ)) ⊆ 𝔓) {a b : ℕ} (ha : a < n) (hb : b < n)
    {P Pt : Multitile ρ} (hP : P ∈ (S a).T) (hPt : Pt ∈ (S b).T) (hPT : P ∈ T'.T)
    (hPtT : Pt ∈ T'.T) (h3 : Multitile.Case3 C₂ C₃ T'.ξ P) (h3' : Multitile.Case3 C₂ C₃ T'.ξ Pt)
    (hI : P.I.toSet ⊆ Pt.I.toSet) (hne : P ≠ Pt) : P ∈ (gTree C₂ T' Pt).T := by
  classical
  subst hC₂
  have hC1 : 0 < C₁ := by linarith [hC.one_le, hC.lt₁, hC.lt₂]
  have hC₂1 : (1 : ℝ) < 2 := by norm_num
  have hC₃2 : C₃ < 2 := hC.lt₁
  have hPm : P ∈ 𝔓 := sel.mem_of_mem_S ha hP
  have hPtm : Pt ∈ 𝔓 := sel.mem_of_mem_S hb hPt
  have hp2 : SeparationProp2 C₁ (T'.T : Set (Multitile ρ)) := (hsep.mono hsub).prop2
  have hL := P.ωu.length_pos
  have hL' := Pt.ωu.length_pos
  -- `|Ĩ| > |I|`
  have hlen : P.I.length < Pt.I.length := by
    have hle : P.I.length ≤ Pt.I.length := Dyadic.length_le_iff.2 (Dyadic.k_le_of_toSet_subset hI)
    rcases eq_or_lt_of_le hle with heq | hlt
    · exfalso
      have hd := treeobs_disjoint_time hC hρ T' hT' hp2 hPT hPtT hne
        (Multitile.ωu_length_eq_of_I_length_eq heq)
      obtain ⟨x, hx⟩ := Dyadic.toSet_nonempty P.I
      exact Set.disjoint_left.1 hd hx (hI hx)
    · exact hlt
  have hlt' : Pt.ωu.length < P.ωu.length := Multitile.ωu_length_lt_of_I_length_lt hlen
  have hsc : Pt.ωu.length ≤ (2 - C₃) / (2 * C₁) * P.ωu.length := hsep.scales P hPm Pt hPtm hlt'
  have h7 := two_mul_le_of_ratio hC1 hsc
  unfold Multitile.Case3 at h3 h3'
  obtain ⟨h3a, h3b⟩ := h3
  obtain ⟨h3a', h3b'⟩ := h3'
  have hm := hC.le_m_add_one hρ
  have hm2 := hC.two_m_add_one_add_le hρ
  have hsL' : ((ρ.m : ℝ) + 1) * Pt.ωu.length ≤ (C₁ - 2) / 2 * Pt.ωu.length :=
    mul_le_mul_of_nonneg_right (by linarith) hL'.le
  have hsL : 2 * P.ωu.length ≤ ((ρ.m : ℝ) + 1) * P.ωu.length :=
    mul_le_mul_of_nonneg_right hm hL.le
  have hC3L' : 1 * Pt.ωu.length ≤ C₃ * Pt.ωu.length :=
    mul_le_mul_of_nonneg_right hC.one_le hL'.le
  have hC3L : 1 * P.ωu.length ≤ C₃ * P.ωu.length :=
    mul_le_mul_of_nonneg_right hC.one_le hL.le
  have h2C3L : 0 ≤ (2 - C₃) * P.ωu.length := mul_nonneg (by linarith) hL.le
  have hC₃L : C₃ * P.ωu.length ≤ 2 * P.ωu.length :=
    mul_le_mul_of_nonneg_right hC₃2.le hL.le
  -- from (separationofscales): `inf C₂ ω̃_l ≥ sup C₃ ω_l`
  have hF3 : P.ωu.center - ((ρ.m : ℝ) + 1) * P.ωu.length + C₃ * P.ωu.length / 2 ≤ Pt.topXi := by
    rw [Pt.topXi_eq]
    linarith
  -- from the selection: `inf C₂ ω̃_l < sup C₂ ω_l`
  have hF2 : Pt.topXi < P.ωu.center - ((ρ.m : ℝ) + 1) * P.ωu.length +
      2 * P.ωu.length / 2 := by
    by_contra hcon
    rw [not_lt] at hcon
    have hξa := (sel.S_overlapping ha) P hP
    have hξb := (sel.S_overlapping hb) Pt hPt
    rw [P.ωlDil_eq] at hξa
    rw [Pt.ωlDil_eq] at hξb
    have hξb1 : Pt.topXi ≤ (S b).ξ := by rw [Multitile.topXi_eq]; linarith [hξb.1]
    by_cases hab : a = b
    · subst hab
      linarith [hξa.2, hξb1, hcon]
    · have hlt_ξ : (S a).ξ < (S b).ξ := by linarith [hξa.2, hξb1, hcon]
      have hba : b < a := by
        rcases lt_or_gt_of_ne hab with h | h
        · exact absurd (sel.xi_le h.le hb) (not_le.2 hlt_ξ)
        · exact h
      have hPrem : P ∈ remainingFamily 𝔓 T b :=
        remainingFamily_anti hba.le (sel.S_subset_rem ha hP)
      refine not_mem_of_mem_remainingFamily hba (sel.S_subset_rem ha hP)
        (sel.mem_T_of_mem_rem hb hPrem (hI.trans ((sel.S_isTree hb).time Pt hPt)) ?_)
      rw [MultitileTree.ωT_subset_ωm_iff hC₂1]
      have hrad := ωT_radius_le hC₂1 ((sel.S_isTree hb).time Pt hPt)
      generalize ((2 : ℝ) - 1) / (4 * (S b).I.length) = r at hrad ⊢
      constructor
      · linarith [hξb1, hcon, hrad]
      · linarith [hξb.2, h3a', h3b, hrad]
  -- the membership
  have hξmem : Pt.topXi ∈ P.ωlDil 2 := by
    rw [P.ωlDil_eq]
    constructor
    · linarith
    · exact hF2
  have hωsub : (⟨∅, Pt.I, Pt.topXi⟩ : MultitileTree ρ).ωT 2 ⊆ P.ωm 2 := by
    rw [MultitileTree.ωT_subset_ωm_iff hC₂1]
    have hrad := ωT_radius_le hC₂1 (P := Pt) (I' := Pt.I) subset_rfl
    dsimp only
    generalize ((2 : ℝ) - 1) / (4 * Pt.I.length) = r at hrad ⊢
    constructor
    · linarith
    · linarith
  exact Finset.mem_filter.2 ⟨hPT, hI, hωsub, hξmem⟩

/-- `∑_{insert a s} f ≤ f a + ∑_s f` for `f ≥ 0`. -/
theorem sum_insert_le_add {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι) (g : ι → ℝ)
    (hg : ∀ i, 0 ≤ g i) : ∑ i ∈ insert a s, g i ≤ g a + ∑ i ∈ s, g i := by
  by_cases h : a ∈ s
  · rw [Finset.insert_eq_of_mem h]
    have := hg a
    linarith
  · rw [Finset.sum_insert h]

open Classical in
/-- **The third term of `pisatree`** ([O+] L1855-L1894): for a tree `T' ⊂ 𝔓`,
`∑_{P ∈ T' ∩ U : sup C₂ ω_l ≤ ξ_{T'} < inf C₃ ω_u} |⟨f, φ_P⟩|² ≤ 2 e² |I_{T'}|`
(`C₂ = 2`; the multitiles lie in the square `[-2^M, 2^M]²`). -/
theorem pisatree_third_term (hC : AdmissibleConstants C₁ C₂ C₃) (hC₂ : C₂ = 2) (hρ : ρ.IsStd)
    (hsep : Separated C₁ C₂ C₃ (𝔓 : Set (Multitile ρ))) (hsq : ∀ P ∈ 𝔓, P.InSquare M)
    (he : 0 ≤ e) (hen : energy C₁ C₂ M ch f (𝔓 : Set (Multitile ρ)) ≤ ENNReal.ofReal e)
    (sel : IsSelection C₁ C₂ M ch f e 𝔓 n S T) {T' : MultitileTree ρ} (hT' : T'.IsTree C₁ C₂ M)
    (hsub : (T'.T : Set (Multitile ρ)) ⊆ 𝔓) :
    ∑ P ∈ T'.T.filter (fun P => P ∈ (Finset.range n).biUnion (fun j => (S j).T) ∧
        Multitile.Case3 C₂ C₃ T'.ξ P), ‖P.coeff ch f‖ ^ 2 ≤ 2 * (e ^ 2 * T'.I.length) := by
  set A := T'.T.filter (fun P => P ∈ (Finset.range n).biUnion (fun j => (S j).T) ∧
    Multitile.Case3 C₂ C₃ T'.ξ P) with hA
  have hmem : ∀ P ∈ A, P ∈ T'.T ∧ (∃ a, a < n ∧ P ∈ (S a).T) ∧
      Multitile.Case3 C₂ C₃ T'.ξ P := by
    intro P hP
    obtain ⟨h1, h2, h3⟩ := Finset.mem_filter.1 hP
    obtain ⟨a, ha, hPa⟩ := Finset.mem_biUnion.1 h2
    exact ⟨h1, ⟨a, Finset.mem_range.1 ha, hPa⟩, h3⟩
  have hp2 : SeparationProp2 C₁ (T'.T : Set (Multitile ρ)) := (hsep.mono hsub).prop2
  set Mx := A.filter (fun P'' => ∀ Pt ∈ A, P''.I.toSet ⊆ Pt.I.toSet →
    Pt.I.length ≤ P''.I.length) with hMx
  have hdom : ∀ P ∈ A, ∃ P'' ∈ Mx, P.I.toSet ⊆ P''.I.toSet := by
    intro P hP
    obtain ⟨P'', hP''mem, hP''max⟩ := Finset.exists_max_image
      (A.filter (fun Pt => P.I.toSet ⊆ Pt.I.toSet)) (fun Pt => Pt.I.length)
      ⟨P, Finset.mem_filter.2 ⟨hP, subset_rfl⟩⟩
    obtain ⟨hP''A, hPsub⟩ := Finset.mem_filter.1 hP''mem
    refine ⟨P'', Finset.mem_filter.2 ⟨hP''A, fun Pt hPt hsub' => ?_⟩, hPsub⟩
    exact hP''max Pt (Finset.mem_filter.2 ⟨hPt, hPsub.trans hsub'⟩)
  have hMxdisj : (Mx : Set (Multitile ρ)).PairwiseDisjoint (fun P => P.I.toSet) := by
    intro P hP P' hP' hne
    have h1 := Finset.mem_filter.1 (Finset.mem_coe.1 hP)
    have h2 := Finset.mem_filter.1 (Finset.mem_coe.1 hP')
    by_contra hnd
    rcases le_total P'.I.length P.I.length with hle | hle
    · have hsubI : P'.I.toSet ⊆ P.I.toSet :=
        Dyadic.toSet_subset_of_length_le_of_not_disjoint hle (fun h => hnd h.symm)
      have heq : P.I.length = P'.I.length := le_antisymm (h2.2 P h1.1 hsubI) hle
      exact hnd (treeobs_disjoint_time hC hρ T' hT' hp2 (hmem P h1.1).1 (hmem P' h2.1).1 hne
        (Multitile.ωu_length_eq_of_I_length_eq heq))
    · have hsubI : P.I.toSet ⊆ P'.I.toSet :=
        Dyadic.toSet_subset_of_length_le_of_not_disjoint hle hnd
      have heq : P'.I.length = P.I.length := le_antisymm (h1.2 P' h2.1 hsubI) hle
      exact hnd (treeobs_disjoint_time hC hρ T' hT' hp2 (hmem P h1.1).1 (hmem P' h2.1).1 hne
        (Multitile.ωu_length_eq_of_I_length_eq heq.symm))
  -- the bound for one maximal multitile
  have hB : ∀ P'' ∈ Mx, ∑ P ∈ insert P'' (gTree C₂ T' P'').T, ‖P.coeff ch f‖ ^ 2 ≤
      2 * (e ^ 2 * P''.I.length) := by
    intro P'' hP''
    obtain ⟨hP''T, ⟨a, ha, hP''a⟩, -⟩ := hmem P'' (Finset.mem_filter.1 hP'').1
    have hP''m := sel.mem_of_mem_S ha hP''a
    have h1 := norm_sq_coeff_le_of_energy_le hC hρ he hen (Finset.mem_coe.2 hP''m) (hsq P'' hP''m)
    have h2 := sum_gTree_le hC hρ hC₂ he hen hT' hsub (hsq P'' hP''m)
    calc ∑ P ∈ insert P'' (gTree C₂ T' P'').T, ‖P.coeff ch f‖ ^ 2
        ≤ ‖P''.coeff ch f‖ ^ 2 + ∑ Q ∈ (gTree C₂ T' P'').T, ‖Q.coeff ch f‖ ^ 2 :=
          sum_insert_le_add _ _ (fun P : Multitile ρ => ‖P.coeff ch f‖ ^ 2) (fun P => by positivity)
      _ ≤ e ^ 2 * P''.I.length + e ^ 2 * P''.I.length := add_le_add h1 h2
      _ = 2 * (e ^ 2 * P''.I.length) := by ring
  -- the covering
  have hcover : ∀ P ∈ A, ∃ P'' ∈ Mx, P ∈ insert P'' (gTree C₂ T' P'').T := by
    intro P hP
    obtain ⟨P'', hP''Mx, hsubI⟩ := hdom P hP
    refine ⟨P'', hP''Mx, ?_⟩
    by_cases hPP : P = P''
    · rw [hPP]; exact Finset.mem_insert_self _ _
    · obtain ⟨hPT, ⟨a, ha, hPa⟩, h3⟩ := hmem P hP
      obtain ⟨hP''T, ⟨b, hb, hP''b⟩, h3'⟩ := hmem P'' (Finset.mem_filter.1 hP''Mx).1
      exact Finset.mem_insert_of_mem (case3_mem_gTree hC hC₂ hρ hsep sel hT' hsub ha hb hPa hP''b
        hPT hP''T h3 h3' hsubI hPP)
  calc ∑ P ∈ A, ‖P.coeff ch f‖ ^ 2
      ≤ ∑ P ∈ A, ∑ P'' ∈ Mx, (if P ∈ insert P'' (gTree C₂ T' P'').T
          then ‖(P : Multitile ρ).coeff ch f‖ ^ 2 else 0) := by
        refine Finset.sum_le_sum fun P hP => ?_
        obtain ⟨P'', hP''Mx, hmemB⟩ := hcover P hP
        have := Finset.single_le_sum (f := fun P'' : Multitile ρ =>
          if P ∈ insert P'' (gTree C₂ T' P'').T then ‖P.coeff ch f‖ ^ 2 else 0) (s := Mx)
          (fun P'' _ => by split_ifs <;> positivity) hP''Mx
        simpa [hmemB] using this
    _ = ∑ P'' ∈ Mx, ∑ P ∈ A, (if P ∈ insert P'' (gTree C₂ T' P'').T
          then ‖(P : Multitile ρ).coeff ch f‖ ^ 2 else 0) := Finset.sum_comm
    _ ≤ ∑ P'' ∈ Mx, ∑ P ∈ insert P'' (gTree C₂ T' P'').T, ‖P.coeff ch f‖ ^ 2 := by
        refine Finset.sum_le_sum fun P'' _ => ?_
        rw [← Finset.sum_filter]
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun P _ _ => by positivity
        intro P hP
        exact (Finset.mem_filter.1 hP).2
    _ ≤ ∑ P'' ∈ Mx, 2 * (e ^ 2 * P''.I.length) := Finset.sum_le_sum hB
    _ = 2 * (e ^ 2 * ∑ P'' ∈ Mx, P''.I.length) := by
        rw [Finset.mul_sum, Finset.mul_sum]
    _ ≤ 2 * (e ^ 2 * T'.I.length) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)) (by norm_num)
        exact sum_length_le_of_disjoint Mx Multitile.I T'.I hMxdisj fun P hP =>
          hT'.time P (hmem P (Finset.mem_filter.1 hP).1).1

end Third

end PrimeCarleson.Proof.Oplus
