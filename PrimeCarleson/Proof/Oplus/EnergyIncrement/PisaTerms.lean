module

public import PrimeCarleson.Proof.Oplus.EnergyIncrement.PisaGeometry

/-!
# The first and second terms of `pisatree` ([O+] L1810-L1853)

Source: [O+] `pisatree`, L1810–L1817; [O+] `pisatree`, L1820–L1844 (L1810-L1853): for a tree `T'` of
the cover and the multitiles `U = ⋃_j S_j` of the selected trees,

* first term: `∑_{P ∈ T' ∩ U : ξ_{T'} ∈ C₂ ω_l} |⟨f, φ_P⟩|² ≤ e² |I_{T'}|` ("by definition an
  `l`-overlapping tree");
* second term: `∑_{P ∈ T' ∩ U : ξ_{T'} ≥ inf C₃ ω_u} |⟨f, φ_P⟩|² ≤ e² |I_{T'}|`: "we use the energy
  bound for fixed tiles" and the rectangles `I × [inf C₃ ω_u, sup C₂ ω_u)` are pairwise disjoint;
  all
  these rectangles contain the frequency `ξ_{T'}`, so the time intervals `I` are pairwise disjoint
  subintervals of `I_{T'}`. The disjointness (`case2_disjoint_aux`) is proved as in the source: two
  multitiles of one `l`-overlapping tree by the Observation (i) (`ωuDil_right_le_left`); of two
  trees `S_a, S_b`, `a < b`, by the maximality of `T_a`, using that `sup C₂ ω_u' ≥ inf C₂ ω_u - ...`
  (the lattice step `lattice_le`, which is where `C₂ = 2` is used).
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

section Terms

variable {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ C₃ : ℝ} {M : ℤ} {ch : ProfileChoice} {f : ℝ → ℂ}
  {e : ℝ} {𝔓 : Finset (Multitile ρ)} {n : ℕ} {S T : ℕ → MultitileTree ρ}

omit [Fact ρ.IsOneOrTwo] in
/-- `(C₂ - 1)/(4 |I'|) ≤ (C₂ - 1)|ω_u|/2` if `I ⊂ I'` (`|I||ω_u| = 1/2`). -/
theorem ωT_radius_le {C₂ : ℝ} (hC₂ : 1 < C₂) {I' : Dyadic} {P : Multitile ρ}
    (h : P.I.toSet ⊆ I'.toSet) : (C₂ - 1) / (4 * I'.length) ≤ (C₂ - 1) * P.ωu.length / 2 := by
  have hI := P.I.length_pos
  have hL := P.ωu.length_pos
  have hI' : P.I.length ≤ I'.length := Dyadic.length_le_iff.2 (Dyadic.k_le_of_toSet_subset h)
  have harea := P.length_I_mul_length_ωu
  calc (C₂ - 1) / (4 * I'.length) ≤ (C₂ - 1) / (4 * P.I.length) :=
        div_le_div_of_nonneg_left (by linarith) (by positivity) (by linarith)
    _ = (C₂ - 1) * P.ωu.length / 2 := by
        field_simp
        nlinarith

omit [Fact ρ.IsOneOrTwo] in
/-- `|ω_u| ≤ ((C₂ - C₃)/(2C₁)) |ω_u'|` gives `2 C₁ |ω_u| ≤ (C₂ - C₃) |ω_u'|`. -/
theorem two_mul_le_of_ratio {C₁ C₂ C₃ L L' : ℝ} (hC1 : 0 < C₁)
    (hsc : L ≤ (C₂ - C₃) / (2 * C₁) * L') : 2 * C₁ * L ≤ (C₂ - C₃) * L' := by
  calc 2 * C₁ * L = 2 * (C₁ * L) := by ring
    _ ≤ 2 * (C₁ * ((C₂ - C₃) / (2 * C₁) * L')) := by gcongr
    _ = (C₂ - C₃) * L' := by field_simp

/-- **The sum of the lengths of pairwise disjoint dyadic intervals inside `I'`** is at most
`|I'|`. -/
theorem sum_length_le_of_disjoint {ι : Type*} (A : Finset ι) (I : ι → Dyadic) (I' : Dyadic)
    (hdisj : (A : Set ι).PairwiseDisjoint (fun i => (I i).toSet))
    (hsub : ∀ i ∈ A, (I i).toSet ⊆ I'.toSet) : ∑ i ∈ A, (I i).length ≤ I'.length := by
  have h1 := measureReal_biUnion_finset (μ := volume) hdisj (fun i _ => (I i).measurableSet_toSet)
    (fun i _ => by simp [Dyadic.volume_toSet])
  have h2 : volume.real (⋃ i ∈ A, (I i).toSet) ≤ volume.real I'.toSet :=
    measureReal_mono (Set.iUnion₂_subset hsub) (by simp [Dyadic.volume_toSet])
  rw [h1] at h2
  simpa only [Dyadic.volume_real_toSet] using h2

open Classical in
/-- **The first term of `pisatree`** ([O+] L1810-L1817): the multitiles of a tree `T' ⊂ 𝔓` with
`ξ_{T'} ∈ C₂ ω_l` form an `l`-overlapping tree with the top data of `T'`, so by `energy(𝔓) ≤ e`
their `∑ |⟨f, φ_P⟩|² ≤ e² |I_{T'}|`. -/
theorem pisatree_first_term {U : Finset (Multitile ρ)} (he : 0 ≤ e)
    (hen : energy C₁ C₂ M ch f (𝔓 : Set (Multitile ρ)) ≤ ENNReal.ofReal e)
    {T' : MultitileTree ρ} (hT' : T'.IsTree C₁ C₂ M) (hsub : (T'.T : Set (Multitile ρ)) ⊆ 𝔓) :
    ∑ P ∈ T'.T.filter (fun P => P ∈ U ∧ Multitile.Case1 C₂ T'.ξ P), ‖P.coeff ch f‖ ^ 2 ≤
      e ^ 2 * T'.I.length := by
  classical
  set G : MultitileTree ρ := ⟨T'.T.filter (fun P => P ∈ U ∧ Multitile.Case1 C₂ T'.ξ P), T'.I, T'.ξ⟩
    with hG
  have hGtree : G.IsTree C₁ C₂ M :=
    ⟨hT'.top_subset, hT'.ξ_mem, fun P hP => hT'.time P (Finset.mem_filter.1 hP).1,
      fun P hP => hT'.freq P (Finset.mem_filter.1 hP).1⟩
  have hGov : G.IsOverlapping C₂ := fun P hP => (Finset.mem_filter.1 hP).2.2
  exact sum_norm_sq_coeff_le_of_energy_le he hen hGtree hGov (fun P hP =>
    hsub (Finset.mem_coe.2 (Finset.mem_filter.1 (Finset.mem_coe.1 hP)).1))

/-- **The time intervals of `T' ∩ U` in the second case are pairwise disjoint** (L1823-L1832): for
`P ∈ S_a`, `P' ∈ S_b`, `P ≠ P'`, both in a tree `T'` with `ξ_{T'} ≥ inf C₃ ω_u`,
`ξ_{T'} ≥ inf C₃ ω_{u'}`,
and `|I'| ≤ |I|`, the intervals `I`, `I'` are disjoint. -/
theorem case2_disjoint_aux (hC : AdmissibleConstants C₁ C₂ C₃) (hC₂ : C₂ = 2) (hρ : ρ.IsStd)
    (hsep : Separated C₁ C₂ C₃ (𝔓 : Set (Multitile ρ)))
    (sel : IsSelection C₁ C₂ M ch f e 𝔓 n S T) {T' : MultitileTree ρ} (hT' : T'.IsTree C₁ C₂ M)
    (hsub : (T'.T : Set (Multitile ρ)) ⊆ 𝔓) {a b : ℕ} (ha : a < n) (hb : b < n)
    {P P' : Multitile ρ} (hP : P ∈ (S a).T) (hP' : P' ∈ (S b).T) (hPT : P ∈ T'.T)
    (hPT' : P' ∈ T'.T) (hne : P ≠ P') (hle : P'.I.length ≤ P.I.length)
    (h2 : Multitile.Case2 C₃ T'.ξ P) (h2' : Multitile.Case2 C₃ T'.ξ P') :
    Disjoint P.I.toSet P'.I.toSet := by
  subst hC₂
  have hC1 : 0 < C₁ := by linarith [hC.one_le, hC.lt₁, hC.lt₂]
  have hC₂1 : (1 : ℝ) < 2 := by norm_num
  have hC₃2 : C₃ < 2 := hC.lt₁
  have hPm : P ∈ 𝔓 := sel.mem_of_mem_S ha hP
  have hPm' : P' ∈ 𝔓 := sel.mem_of_mem_S hb hP'
  have hp2 : SeparationProp2 C₁ (T'.T : Set (Multitile ρ)) :=
    (hsep.mono hsub).prop2
  rcases eq_or_lt_of_le hle with heq | hlt
  · exact treeobs_disjoint_time hC hρ T' hT' hp2 hPT hPT' hne
      (Multitile.ωu_length_eq_of_I_length_eq heq.symm)
  by_contra hnd
  have hsubI : P'.I.toSet ⊆ P.I.toSet :=
    Dyadic.toSet_subset_of_length_le_of_not_disjoint hle (fun h => hnd h.symm)
  have hlt' : P.ωu.length < P'.ωu.length := Multitile.ωu_length_lt_of_I_length_lt hlt
  have hsc : P.ωu.length ≤ (2 - C₃) / (2 * C₁) * P'.ωu.length :=
    hsep.scales P' hPm' P hPm hlt'
  have hL := P.ωu.length_pos
  have hL' := P'.ωu.length_pos
  have hξm := hT'.freq P hPT (T'.mem_ωT_self hC₂1)
  have hξm' := hT'.freq P' hPT' (T'.mem_ωT_self hC₂1)
  rw [Multitile.ωm_eq_Ico (by norm_num)] at hξm hξm'
  unfold Multitile.Case2 at h2 h2'
  have hcase : ¬ ((S a).ξ ≤ (S b).ξ) := by
    intro hle'
    have := ωuDil_right_le_left hC hρ ((sel.S_overlapping hb) P' hP')
      ((sel.S_overlapping ha) P hP) hle' hsc
    linarith [hξm.2, hξm'.2]
  have hab : a < b := by
    rcases lt_trichotomy a b with h | h | h
    · exact h
    · subst h; exact absurd le_rfl hcase
    · exact absurd (sel.xi_le h.le ha) hcase
  -- `P' ∉ T_a`, but the maximality of `T_a` puts it there
  have hP'rem : P' ∈ remainingFamily 𝔓 T a :=
    remainingFamily_anti hab.le (sel.S_subset_rem hb hP')
  have hnotT : P' ∉ (T a).T := not_mem_of_mem_remainingFamily hab (sel.S_subset_rem hb hP')
  refine hnotT (sel.mem_T_of_mem_rem ha hP'rem
    (hsubI.trans ((sel.S_isTree ha).time P hP)) ?_)
  rw [MultitileTree.ωT_subset_ωm_iff hC₂1]
  have hrad := ωT_radius_le hC₂1 ((sel.S_isTree ha).time P hP)
  obtain ⟨hξa1, hξa2⟩ := mem_ωlDil_bounds hC hρ ((sel.S_overlapping ha) P hP)
  have hmult := hC.le_m_add_one hρ
  have h7 := two_mul_le_of_ratio hC1 hsc
  have hlat := lattice_le (hC₃2.trans (by norm_num)) hlt' (by linarith [hξm'.2])
  have hs1 : 2 * P'.ωu.length ≤ ((ρ.m : ℝ) + 1) * P'.ωu.length :=
    mul_le_mul_of_nonneg_right hmult hL'.le
  have h2L : (2 : ℝ) * P.ωu.length ≤ C₁ * P.ωu.length :=
    mul_le_mul_of_nonneg_right (by linarith [hC.lt₂]) hL.le
  have h3a : C₃ * P'.ωu.length ≤ 2 * P'.ωu.length :=
    mul_le_mul_of_nonneg_right hC₃2.le hL'.le
  have h3b : 1 * P'.ωu.length ≤ C₃ * P'.ωu.length :=
    mul_le_mul_of_nonneg_right hC.one_le hL'.le
  generalize ((2 : ℝ) - 1) / (4 * (S a).I.length) = r at hrad ⊢
  constructor
  · nlinarith [hξm.2, hξm'.1, hrad]
  · nlinarith [hξa2, hrad, hlat]

open Classical in
/-- **The second term of `pisatree`** ([O+] L1820-L1845): for a tree `T' ⊂ 𝔓`,
`∑_{P ∈ T' ∩ U : ξ_{T'} ≥ inf C₃ ω_u} |⟨f, φ_P⟩|² ≤ e² |I_{T'}|`, `U = ⋃_j S_j`
(`C₂ = 2`; the multitiles lie in the square `[-2^M, 2^M]²`). -/
theorem pisatree_second_term (hC : AdmissibleConstants C₁ C₂ C₃) (hC₂ : C₂ = 2) (hρ : ρ.IsStd)
    (hsep : Separated C₁ C₂ C₃ (𝔓 : Set (Multitile ρ))) (hsq : ∀ P ∈ 𝔓, P.InSquare M)
    (he : 0 ≤ e) (hen : energy C₁ C₂ M ch f (𝔓 : Set (Multitile ρ)) ≤ ENNReal.ofReal e)
    (sel : IsSelection C₁ C₂ M ch f e 𝔓 n S T) {T' : MultitileTree ρ} (hT' : T'.IsTree C₁ C₂ M)
    (hsub : (T'.T : Set (Multitile ρ)) ⊆ 𝔓) :
    ∑ P ∈ T'.T.filter (fun P => P ∈ (Finset.range n).biUnion (fun j => (S j).T) ∧
        Multitile.Case2 C₃ T'.ξ P), ‖P.coeff ch f‖ ^ 2 ≤ e ^ 2 * T'.I.length := by
  set A := T'.T.filter (fun P => P ∈ (Finset.range n).biUnion (fun j => (S j).T) ∧
    Multitile.Case2 C₃ T'.ξ P) with hA
  have hmem : ∀ P ∈ A, P ∈ T'.T ∧ (∃ a, a < n ∧ P ∈ (S a).T) ∧ Multitile.Case2 C₃ T'.ξ P := by
    intro P hP
    obtain ⟨h1, h2, h3⟩ := Finset.mem_filter.1 hP
    obtain ⟨a, ha, hPa⟩ := Finset.mem_biUnion.1 h2
    exact ⟨h1, ⟨a, Finset.mem_range.1 ha, hPa⟩, h3⟩
  have hdisj : (A : Set (Multitile ρ)).PairwiseDisjoint (fun P => P.I.toSet) := by
    intro P hP P' hP' hne
    obtain ⟨hPT, ⟨a, ha, hPa⟩, h2⟩ := hmem P (Finset.mem_coe.1 hP)
    obtain ⟨hPT', ⟨b, hb, hPb⟩, h2'⟩ := hmem P' (Finset.mem_coe.1 hP')
    rcases le_total P'.I.length P.I.length with h | h
    · exact case2_disjoint_aux hC hC₂ hρ hsep sel hT' hsub ha hb hPa hPb hPT hPT' hne h h2 h2'
    · exact (case2_disjoint_aux hC hC₂ hρ hsep sel hT' hsub hb ha hPb hPa hPT' hPT hne.symm h
        h2' h2).symm
  calc ∑ P ∈ A, ‖P.coeff ch f‖ ^ 2 ≤ ∑ P ∈ A, e ^ 2 * P.I.length :=
        Finset.sum_le_sum fun P hP => by
          obtain ⟨hPT, ⟨a, ha, hPa⟩, -⟩ := hmem P hP
          have hPm : P ∈ 𝔓 := sel.mem_of_mem_S ha hPa
          exact norm_sq_coeff_le_of_energy_le hC hρ he hen (Finset.mem_coe.2 hPm) (hsq P hPm)
    _ = e ^ 2 * ∑ P ∈ A, P.I.length := by rw [Finset.mul_sum]
    _ ≤ e ^ 2 * T'.I.length := mul_le_mul_of_nonneg_left
        (sum_length_le_of_disjoint A Multitile.I T'.I hdisj fun P hP =>
          hT'.time P (hmem P hP).1) (sq_nonneg _)

end Terms

end PrimeCarleson.Proof.Oplus
