module

public import PrimeCarleson.Proof.Oplus.EnergyIncrement.Selection

/-!
# Interval geometry of multitiles for the energy increment ([O+] L1583-L1622, L1855-L1876)

The geometric content of the source arguments for `claimofdisjointness` and
`pisatree`, in coordinates. For a `ρ`-multitile `P` write `c = c(ω_u)`, `L = |ω_u|`,
`s = m + 1`; then (`Multitile.ωuDil_eq`, `ωlDil_eq`, `ωm_eq_Ico`)

* `C ω_u = [c - C L/2, c + C L/2)`, `C ω_l = [c - s L - C L/2, c - s L + C L/2)`;
* `ω_m = hull(C₂ ω_u ∪ C₂ ω_l) = [c - s L - C₂ L/2, c + C₂ L/2)`;
* `ω_𝒯 ⊂ ω_m(P)` iff `c - s L - C₂ L/2 ≤ ξ_𝒯 - r` and `ξ_𝒯 + r ≤ c + C₂ L/2`
  (`ωT_subset_ωm_iff`, `r = (C₂ - 1)/(4|I_𝒯|)`).

From `C₂ ≤ s` and `2 s + C₂ ≤ C₁` (`Basic.lean`): a point `ξ ∈ C₂ ω_l` satisfies
`c - C₁ L/2 ≤ ξ < c - C₂ L/2` (`mem_ωlDil_bounds`), which gives the **ordering lemma**
`sup C₂ ω_u' ≤ inf C₃ ω_u` (`ωuDil_right_le_left`) for two multitiles whose `l`-overlapping top
frequencies satisfy `ξ' ≤ ξ` and `|ω_u'| ≤ ((C₂ - C₃)/(2C₁)) |ω_u|`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

/-! ### Lengths of dyadic intervals -/

/-- `|I| < |J|` iff `k_I < k_J`. -/
theorem Dyadic.length_lt_iff {I J : Dyadic} : I.length < J.length ↔ I.k < J.k := by
  unfold Dyadic.length
  exact zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)

/-- `|I| ≤ |J|` iff `k_I ≤ k_J`. -/
theorem Dyadic.length_le_iff {I J : Dyadic} : I.length ≤ J.length ↔ I.k ≤ J.k := by
  unfold Dyadic.length
  exact zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)

/-- Two dyadic intervals with intersecting sets and `|I| ≤ |J|` are nested. -/
theorem Dyadic.toSet_subset_of_length_le_of_not_disjoint {I J : Dyadic} (h : I.length ≤ J.length)
    (hd : ¬ Disjoint I.toSet J.toSet) : I.toSet ⊆ J.toSet := by
  rcases I.toSet_subset_or_disjoint_of_k_le J (Dyadic.length_le_iff.1 h) with h1 | h1
  · exact h1
  · exact absurd h1 hd

/-! ### Multitiles in coordinates -/

section Coordinates

variable {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ C₃ : ℝ}

omit [Fact ρ.IsOneOrTwo] in
/-- `C ω_u = [c - C L/2, c + C L/2)`. -/
theorem Multitile.ωuDil_eq (P : Multitile ρ) (C : ℝ) :
    P.ωuDil C = Ico (P.ωu.center - C * P.ωu.length / 2) (P.ωu.center + C * P.ωu.length / 2) := rfl

/-- `C ω_l = [c - s L - C L/2, c - s L + C L/2)`, `s = m + 1`. -/
theorem Multitile.ωlDil_eq (P : Multitile ρ) (C : ℝ) :
    P.ωlDil C = Ico (P.ωu.center - ((ρ.m : ℝ) + 1) * P.ωu.length - C * P.ωu.length / 2)
      (P.ωu.center - ((ρ.m : ℝ) + 1) * P.ωu.length + C * P.ωu.length / 2) := by
  unfold Multitile.ωlDil Dyadic.dilate
  rw [Idx.center_ωlDyadic, Idx.length_ωlDyadic]

/-- **`ω_m = [c - s L - C₂ L/2, c + C₂ L/2)`**: the convex hull of `C₂ ω_u ∪ C₂ ω_l` (L1228-L1230)
is the half-open interval from `inf C₂ ω_l` to `sup C₂ ω_u`. -/
theorem Multitile.ωm_eq_Ico (hC₂ : 0 < C₂) (P : Multitile ρ) :
    P.ωm C₂ = Ico (P.ωu.center - ((ρ.m : ℝ) + 1) * P.ωu.length - C₂ * P.ωu.length / 2)
      (P.ωu.center + C₂ * P.ωu.length / 2) := by
  have hL := P.ωu.length_pos
  have hm : (0 : ℝ) ≤ ρ.m := Nat.cast_nonneg _
  refine Set.Subset.antisymm (Multitile.ωm_subset_Ico C₂ P) ?_
  rintro x ⟨h1, h2⟩
  by_cases hx : P.ωu.center - C₂ * P.ωu.length / 2 ≤ x
  · exact subset_convexHull ℝ _ (Or.inl (show x ∈ P.ωuDil C₂ from ⟨hx, h2⟩))
  · rw [not_le] at hx
    have hseg := segment_subset_convexHull (𝕜 := ℝ)
      (s := P.ωuDil C₂ ∪ P.ωlDil C₂)
      (show P.ωu.center - ((ρ.m : ℝ) + 1) * P.ωu.length - C₂ * P.ωu.length / 2 ∈ _ from by
        refine Or.inr ?_
        rw [P.ωlDil_eq C₂]
        constructor
        · exact le_rfl
        · nlinarith)
      (show P.ωu.center - C₂ * P.ωu.length / 2 ∈ _ from by
        refine Or.inl ?_
        rw [P.ωuDil_eq C₂]
        constructor
        · exact le_rfl
        · nlinarith)
    refine hseg ?_
    rw [segment_eq_Icc (by nlinarith)]
    exact ⟨h1, hx.le⟩

/-- The top interval `ω_𝒯` lies in `ω_m(P)` iff both end points do. -/
theorem MultitileTree.ωT_subset_ωm_iff (hC₂ : 1 < C₂) (𝒯 : MultitileTree ρ) (P : Multitile ρ) :
    𝒯.ωT C₂ ⊆ P.ωm C₂ ↔
      P.ωu.center - ((ρ.m : ℝ) + 1) * P.ωu.length - C₂ * P.ωu.length / 2 ≤
          𝒯.ξ - (C₂ - 1) / (4 * 𝒯.I.length) ∧
        𝒯.ξ + (C₂ - 1) / (4 * 𝒯.I.length) ≤ P.ωu.center + C₂ * P.ωu.length / 2 := by
  have hI := 𝒯.I.length_pos
  have hr : 0 < (C₂ - 1) / (4 * 𝒯.I.length) := by
    apply div_pos <;> linarith
  rw [Multitile.ωm_eq_Ico (by linarith)]
  unfold MultitileTree.ωT
  exact Ico_subset_Ico_iff (by linarith)

/-- A point of `C₂ ω_l` satisfies `c - C₁ L/2 ≤ ξ < c - C₂ L/2` (it lies to the left of `C₂ ω_u`
and inside `C₁ ω_u`). -/
theorem mem_ωlDil_bounds (hC : AdmissibleConstants C₁ C₂ C₃) (hρ : ρ.IsStd) {P : Multitile ρ}
    {ξ : ℝ} (hξ : ξ ∈ P.ωlDil C₂) :
    P.ωu.center - C₁ * P.ωu.length / 2 ≤ ξ ∧ ξ < P.ωu.center - C₂ * P.ωu.length / 2 := by
  have hL := P.ωu.length_pos
  have h1 := hC.le_m_add_one hρ
  have h2 := hC.two_m_add_one_add_le hρ
  rw [P.ωlDil_eq] at hξ
  obtain ⟨hξ1, hξ2⟩ := hξ
  constructor
  · nlinarith
  · nlinarith

/-- **The ordering lemma**: if `ξ ∈ C₂ ω_l(P)`, `ξ' ∈ C₂ ω_l(P')`, `ξ' ≤ ξ` and
`|ω_u'| ≤ ((C₂ - C₃)/(2 C₁)) |ω_u|` then `sup C₂ ω_u' ≤ inf C₃ ω_u`. -/
theorem ωuDil_right_le_left (hC : AdmissibleConstants C₁ C₂ C₃) (hρ : ρ.IsStd)
    {P P' : Multitile ρ} {ξ ξ' : ℝ} (hξ : ξ ∈ P.ωlDil C₂) (hξ' : ξ' ∈ P'.ωlDil C₂)
    (hle : ξ' ≤ ξ) (hsc : P'.ωu.length ≤ (C₂ - C₃) / (2 * C₁) * P.ωu.length) :
    P'.ωu.center + C₂ * P'.ωu.length / 2 ≤ P.ωu.center - C₃ * P.ωu.length / 2 := by
  have hL := P.ωu.length_pos
  have hL' := P'.ωu.length_pos
  have hC1 : 0 < C₁ := by linarith [hC.one_le, hC.lt₁, hC.lt₂]
  obtain ⟨-, hξ2⟩ := mem_ωlDil_bounds hC hρ hξ
  obtain ⟨hξ1', -⟩ := mem_ωlDil_bounds hC hρ hξ'
  have h7 : 2 * C₁ * P'.ωu.length ≤ (C₂ - C₃) * P.ωu.length := by
    calc 2 * C₁ * P'.ωu.length = 2 * (C₁ * P'.ωu.length) := by ring
      _ ≤ 2 * (C₁ * ((C₂ - C₃) / (2 * C₁) * P.ωu.length)) := by gcongr
      _ = (C₂ - C₃) * P.ωu.length := by field_simp
  have h8 : C₂ * P'.ωu.length ≤ C₁ * P'.ωu.length := by
    apply mul_le_mul_of_nonneg_right hC.lt₂.le hL'.le
  nlinarith

end Coordinates

end PrimeCarleson.Proof.Oplus
