module

public import PrimeCarleson.Proof.Oplus.DensityIncrement.Selection

/-!
# The tiles of the selected trees are pairwise disjoint ([O+] L1935)

Source: [O+] `densityincrementprop`, L1935: "we first observe that the tiles `I_{T_j} ×
ω_{T_j}` are pairwise disjoint. Indeed, suppose that `(I_{T_j} × ω_{T_j}) ∩ (I_{T_{j'}} ×
ω_{T_{j'}}) ≠ ∅` and `j < j'`. Then, by the first maximality condition, we have `|I_{T_j}| ≥
|I_{T_{j'}}|` and so `I_{T_{j'}} ⊂ I_{T_j}` and `|ω_{T_j}| ≤ |ω_{T_{j'}}|`. From the latter
inequality, it follows that for every `P ∈ T_{j'}`, either `ω_{T_j} ⊂ ω_m`, `ω_{T_j^+} ⊂ ω_m`, or
`ω_{T_j^-} ⊂ ω_m`. Thus `T_{j'} ⊂ T_j ∪ T_j^+ ∪ T_j^-` which contradicts the selection
algorithm."

The step "from the latter inequality it follows" is the elementary fact
`density_exists_shift_subset`: an interval `[lo, hi)` meeting `ω_T = [ξ - r, ξ + r)` and of length
at least `4r` contains one of `ω_{T^-} = [ξ - 3r, ξ - r)`, `ω_T`,
`ω_{T^+} = [ξ + r, ξ + 3r)`. It applies to `ω_m(P)`, an
interval of length `(m + 1 + C₂)|ω_u| ≥ 2 C₂ |ω_u| = C₂/|I_P| ≥ C₂/|I_{T_j}| > 4r` since
`C₂ ≤ m + 1` (`AdmissibleConstants.le_m_add_one`) and `|I_P| ≤ |I_{T_j}|`. (The separation
assumptions are not used.)
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

/-- An interval `[lo, hi)` of length at least `4r` which meets `[ξ - r, ξ + r)` contains one of the
three adjacent intervals `[ξ - 3r, ξ - r)`, `[ξ - r, ξ + r)`, `[ξ + r, ξ + 3r)` (in the form of the
inequalities of `MultitileTree.ωT_subset_ωm_iff`). -/
theorem density_exists_shift_subset {lo hi ξ r x : ℝ} (hlo : lo ≤ x) (hxhi : x < hi)
    (hx1 : ξ - r ≤ x) (hx2 : x < ξ + r) (hlen : 4 * r ≤ hi - lo) :
    (lo ≤ ξ - 3 * r ∧ ξ - r ≤ hi) ∨ (lo ≤ ξ - r ∧ ξ + r ≤ hi) ∨
      (lo ≤ ξ + r ∧ ξ + 3 * r ≤ hi) := by
  by_cases h1 : lo ≤ ξ - 3 * r
  · exact Or.inl ⟨h1, by linarith⟩
  · by_cases h2 : lo ≤ ξ - r
    · exact Or.inr (Or.inl ⟨h2, by linarith⟩)
    · exact Or.inr (Or.inr ⟨by linarith, by linarith⟩)

section Disjoint

variable {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ C₃ : ℝ} {M : ℤ} {r : ℝ} {L : Linearization r}
  {E : Set ℝ} {den : ℝ}

/-- `ω_m(P)` has length at least `(C₂ - 1)/|J|` when `|I_P| ≤ |J|`: it is the interval
`[c - (m+1)|ω_u| - C₂|ω_u|/2, c + C₂|ω_u|/2)` of length `(m + 1 + C₂)|ω_u| ≥ 2 C₂ |ω_u|`. -/
theorem ωm_length_ge (hC : AdmissibleConstants C₁ C₂ C₃) (hρ : ρ.IsStd) {P : Multitile ρ}
    {J : Dyadic} (hPJ : P.I.length ≤ J.length) :
    (C₂ - 1) / J.length ≤
      (P.ωu.center + C₂ * P.ωu.length / 2) -
        (P.ωu.center - ((ρ.m : ℝ) + 1) * P.ωu.length - C₂ * P.ωu.length / 2) := by
  have hC₂ : 1 < C₂ := lt_of_le_of_lt hC.one_le hC.lt₁
  have hLpos := P.ωu.length_pos
  have hJ := J.length_pos
  have harea := P.length_I_mul_length_ωu
  have hm := hC.le_m_add_one hρ
  have h1 : 1 / 2 ≤ J.length * P.ωu.length := by
    rw [← harea]; exact mul_le_mul_of_nonneg_right hPJ hLpos.le
  rw [div_le_iff₀ hJ]
  have h2 : C₂ * (2 * (J.length * P.ωu.length)) ≥ C₂ := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hm hLpos.le]

namespace IsDensitySelection

variable {𝔓 : Finset (Multitile ρ)} {n : ℕ} {S T Tp Tm : ℕ → MultitileTree ρ}
  (sel : IsDensitySelection C₁ C₂ M L E den 𝔓 n S T Tp Tm)
include sel

/-- **The covering step of `tiles_disjoint`**: let `P` be a multitile of the family remaining
before step `j` with `P.I ⊂ I_{S_j}`, and suppose `ω_m(P)` meets `ω_{S_j}` and has length at least
`(C₂ - 1)/|I_{S_j}|`. Then one of `ω_{T_j^-}`, `ω_{T_j}`, `ω_{T_j^+}` lies in `ω_m(P)` (the interval
`ω_m(P)` of length `≥ 4r` meeting `ω_{S_j} = [ξ - r, ξ + r)` contains one of the three adjacent
intervals, `density_exists_shift_subset`), so `P ∈ T_j ∪ T_j^+ ∪ T_j^-` by maximality. -/
theorem mem_union_of_overlap (hC : AdmissibleConstants C₁ C₂ C₃) {j : ℕ} (hj : j < n)
    {P : Multitile ρ} (hP : P ∈ densityRemaining 𝔓 T Tp Tm j)
    (hI : P.I.toSet ⊆ (S j).I.toSet) {η : ℝ} (hη : η ∈ (S j).ωT C₂) (hηm : η ∈ P.ωm C₂)
    (hlen : (C₂ - 1) / (S j).I.length ≤
      (P.ωu.center + C₂ * P.ωu.length / 2) -
        (P.ωu.center - ((ρ.m : ℝ) + 1) * P.ωu.length - C₂ * P.ωu.length / 2)) :
    P ∈ (T j).T ∨ P ∈ (Tp j).T ∨ P ∈ (Tm j).T := by
  have hC₂ : 1 < C₂ := lt_of_le_of_lt hC.one_le hC.lt₁
  have hIpos := (S j).I.length_pos
  have hr : 0 < (C₂ - 1) / (4 * (S j).I.length) := by apply div_pos <;> linarith
  have h4r : 4 * ((C₂ - 1) / (4 * (S j).I.length)) = (C₂ - 1) / (S j).I.length := by
    field_simp
  rw [Multitile.ωm_eq_Ico (by linarith)] at hηm
  obtain ⟨hlo, hhi⟩ := hηm
  obtain ⟨hx1, hx2⟩ := hη
  have hshift : topShift C₂ (S j) = 2 * ((C₂ - 1) / (4 * (S j).I.length)) := by
    unfold topShift; field_simp; ring
  rcases density_exists_shift_subset hlo hhi hx1 hx2 (by rw [h4r]; exact hlen) with h | h | h
  · -- `ω_{T^-} ⊂ ω_m(P)`
    right; right
    rw [sel.Tm_eq j hj]
    refine mem_maximalTree.2 ⟨hP, hI, ?_⟩
    rw [MultitileTree.ωT_subset_ωm_iff hC₂]
    simp only [shiftTree_I, shiftTree_ξ, hshift]
    constructor <;> push_cast <;> linarith [h.1, h.2]
  · left
    rw [sel.T_eq j hj]
    refine mem_maximalTree.2 ⟨hP, hI, ?_⟩
    rw [MultitileTree.ωT_subset_ωm_iff hC₂]
    exact ⟨h.1, h.2⟩
  · right; left
    rw [sel.Tp_eq j hj]
    refine mem_maximalTree.2 ⟨hP, hI, ?_⟩
    rw [MultitileTree.ωT_subset_ωm_iff hC₂]
    simp only [shiftTree_I, shiftTree_ξ, hshift]
    constructor <;> push_cast <;> linarith [h.1, h.2]

/-- **The selected tiles are disjoint** ([O+] L1935): the tiles `I_{T_j} × ω_{T_j}` of the
selected trees are pairwise disjoint (for `j < j'`; see `tiles_disjoint` for all `j ≠ j'`). -/
theorem tiles_disjoint_lt (hC : AdmissibleConstants C₁ C₂ C₃) (hρ : ρ.IsStd) {j j' : ℕ}
    (hjj' : j < j') (hj' : j' < n) :
    Disjoint ((T j).I.toSet ×ˢ (T j).ωT C₂) ((T j').I.toSet ×ˢ (T j').ωT C₂) := by
  have hj : j < n := lt_trans hjj' hj'
  refine Set.disjoint_left.2 fun ⟨x, η⟩ h1 h2 => ?_
  obtain ⟨hx1, hη1⟩ := h1
  obtain ⟨hx2, hη2⟩ := h2
  -- the first maximality condition: `|I_{T_{j'}}| ≤ |I_{T_j}|`
  have hlen : (T j').I.length ≤ (T j).I.length := by
    have := sel.I_max j hj (T j')
      ((sel.T_dense hj').mono (fun P hP => densityRemaining_anti hjj'.le hP))
    rwa [sel.T_I hj]
  have hnest : (T j').I.toSet ⊆ (T j).I.toSet :=
    Dyadic.toSet_subset_of_length_le_of_not_disjoint hlen
      (Set.not_disjoint_iff.2 ⟨x, hx2, hx1⟩)
  obtain ⟨P, hP⟩ := sel.T_nonempty hj'
  have hPrem' := sel.T_subset_rem hj' hP
  have hPrem : P ∈ densityRemaining 𝔓 T Tp Tm j := densityRemaining_anti hjj'.le hPrem'
  have hT' := sel.T_isTree hj'
  have hPI : P.I.toSet ⊆ (T j).I.toSet := (hT'.time P hP).trans hnest
  have hPm : η ∈ P.ωm C₂ := hT'.freq P hP hη2
  have hlenP : P.I.length ≤ (T j).I.length :=
    Dyadic.length_le_iff.2 (Dyadic.k_le_of_toSet_subset hPI)
  have hge := ωm_length_ge hC hρ hlenP
  rw [sel.T_I hj] at hPI hge hlenP
  have hωT : (T j).ωT C₂ = (S j).ωT C₂ := by
    unfold MultitileTree.ωT; rw [sel.T_I hj, sel.T_ξ hj]
  have hη1' : η ∈ (S j).ωT C₂ := hωT ▸ hη1
  have hmem := sel.mem_union_of_overlap hC hj hPrem hPI hη1' hPm hge
  obtain ⟨a, b, c⟩ := not_mem_of_mem_densityRemaining hjj' hPrem'
  rcases hmem with h | h | h
  · exact a h
  · exact b h
  · exact c h

/-- **The selected tiles are disjoint** ([O+] L1935): the tiles `I_{T_j} × ω_{T_j}` of the
selected trees are pairwise disjoint. -/
theorem tiles_disjoint (hC : AdmissibleConstants C₁ C₂ C₃) (hρ : ρ.IsStd) {j j' : ℕ} (hj : j < n)
    (hj' : j' < n) (hne : j ≠ j') :
    Disjoint ((T j).I.toSet ×ˢ (T j).ωT C₂) ((T j').I.toSet ×ˢ (T j').ωT C₂) := by
  rcases lt_or_gt_of_ne hne with h | h
  · exact sel.tiles_disjoint_lt hC hρ h hj'
  · exact (sel.tiles_disjoint_lt hC hρ h hj).symm

end IsDensitySelection

end Disjoint

end PrimeCarleson.Proof.Oplus
