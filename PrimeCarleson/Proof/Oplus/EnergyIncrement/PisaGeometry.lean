module

public import PrimeCarleson.Proof.Oplus.EnergyIncrement.IntervalBound

/-!
# Geometry for `pisatree` ([O+] L1801-L1894)

[O+] L1801-L1894 (`threeterms` and the three terms of `pisatree`). The arguments of the source use
`C₂ = 2`
(L1875: "with the choice `C₂ = 2` the number `inf C₂ ω̃_l` belongs to `𝒳_top`") and a lattice
argument for the dyadic end points; the hypothesis `C₂ = 2` is explicit below.

* `Multitile.inf_ωl_mem_Xtop`: for a multitile in the square `[-2^M, 2^M]²` and `C₂ = 2`, the point
  `inf C₂ ω_l = c(ω_l) - |ω_u|` lies in `𝒳_top`, so that it is an admissible top frequency;
* `lattice_le`: if `|ω_u| < |ω_u'|` and `c - C₃|ω_u|/2 < c' + |ω_u'|` (`C₃ < 3`) then
  `c - |ω_u|/2 ≤ c' + |ω_u'|` (both sides are integer multiples of `|ω_u|`);
* the three position cases of `ξ_{T'}` relative to a multitile `P ∈ T'`: `C₂ ω_l`
  (`Case1`), `ξ_{T'} ≥ inf C₃ ω_u` (`Case2`), the rest (`Case3`), `case_cover`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

section Lattice

variable {ρ : Idx}

/-- For `C₂ = 2` the point `inf C₂ ω_l = c(ω_l) - |ω_u|` of a multitile in the square is in
`𝒳_top` (it is a multiple of `|ω_u|/2` of modulus at most `13 · 2^M`). -/
theorem Multitile.inf_ωl_mem_Xtop (hρ : ρ.IsStd) {C₁ : ℝ} (hC₁ : 1 ≤ C₁) {M : ℤ}
    {P : Multitile ρ} (hP : P.InSquare M) :
    (ρ.ωlDyadic P.ωu).center - P.ωu.length ∈ Xtop C₁ M := by
  have hL := P.ωu.length_pos
  have h2M : (0 : ℝ) < (2 : ℝ) ^ M := zpow_pos (by norm_num) _
  obtain ⟨-, hm4, -, -⟩ := hρ
  have hm4' : (ρ.m : ℝ) ≤ 4 := by exact_mod_cast hm4
  have hm0 : (0 : ℝ) ≤ ρ.m := Nat.cast_nonneg _
  refine ⟨?_, ?_⟩
  · have h1 := Dyadic.abs_center_le_of_subset_Icc hP.2
    have h2 := Dyadic.length_le_of_subset_Icc hP.2
    rw [Idx.center_ωlDyadic]
    have h3 : (2 : ℝ) ^ (M + 10) = (2 : ℝ) ^ M * 1024 := by
      rw [zpow_add₀ (by norm_num)]; norm_num
    rw [h3]
    have h4 : ((ρ.m : ℝ) + 1) * P.ωu.length ≤ 5 * (2 * (2 : ℝ) ^ M) := by
      apply mul_le_mul (by linarith) h2 hL.le (by norm_num)
    rw [abs_le] at h1 ⊢
    constructor <;> nlinarith [h1.1, h1.2]
  · have hk : P.I.k ≤ M + 1 := by
      have h := Dyadic.length_le_of_subset_Icc hP.1
      have : (2 : ℝ) ^ P.I.k ≤ (2 : ℝ) ^ (M + 1) := by
        have e1 : P.I.length = (2 : ℝ) ^ P.I.k := rfl
        rw [zpow_add_one₀ (by norm_num)]
        linarith
      exact (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 this
    have harea := P.area
    set m' : ℤ := P.ωu.m - ((ρ.m : ℤ) + 1) with hm'
    have hcen : (ρ.ωlDyadic P.ωu).center - P.ωu.length =
        (2 : ℝ) ^ P.ωu.k * ((m' : ℝ) - 1 / 2) := by
      unfold Idx.ωlDyadic Dyadic.center Dyadic.shift Dyadic.length
      simp only [hm']
      push_cast
      ring
    refine ⟨(2 * m' - 1) * (2 : ℤ) ^ (P.ωu.k + M + 9).toNat, ?_⟩
    have hk' : 0 ≤ P.ωu.k + M + 9 := by omega
    have e1 : (2 : ℝ) ^ P.ωu.k = (2 : ℝ) ^ (P.ωu.k + M + 9) * (2 : ℝ) ^ (-M - 9) := by
      rw [← zpow_add₀ (by norm_num)]; congr 1; ring
    have e2 : (2 : ℝ) ^ (-M - 10) = (2 : ℝ) ^ (-M - 9) / 2 := by
      rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
      field_simp
    have e3 : (2 : ℝ) ^ (P.ωu.k + M + 9) = (2 : ℝ) ^ (P.ωu.k + M + 9).toNat := by
      rw [← zpow_natCast, Int.toNat_of_nonneg hk']
    rw [hcen, e1, e2]
    push_cast
    rw [← e3]
    ring

/-- **The lattice step**: if `|ω_u| < |ω_u'|` and `c - C₃|ω_u|/2 < c' + |ω_u'|` with `C₃ < 3`, then
`c - |ω_u|/2 ≤ c' + |ω_u'|`: both end points are integer multiples of `|ω_u|` (`|ω_u'| ≥ 2|ω_u|`),
and the difference exceeds `-|ω_u|`. -/
theorem lattice_le {C₃ : ℝ} (hC₃ : C₃ < 3) {P P' : Multitile ρ}
    (hlt : P.ωu.length < P'.ωu.length)
    (h : P.ωu.center - C₃ * P.ωu.length / 2 < P'.ωu.center + P'.ωu.length) :
    P.ωu.center - P.ωu.length / 2 ≤ P'.ωu.center + P'.ωu.length := by
  have hL := P.ωu.length_pos
  have hk : P.ωu.k < P'.ωu.k := Dyadic.length_lt_iff.1 hlt
  obtain ⟨t, ht⟩ : ∃ t : ℕ, P'.ωu.k = P.ωu.k + 1 + t := ⟨(P'.ωu.k - P.ωu.k - 1).toNat, by omega⟩
  have h2k : (2 : ℝ) ^ P'.ωu.k = 2 ^ P.ωu.k * 2 * 2 ^ t := by
    rw [ht, zpow_add₀ (by norm_num), zpow_add_one₀ (by norm_num), zpow_natCast]
  have hc : P.ωu.center - P.ωu.length / 2 = P.ωu.length * (P.ωu.m : ℝ) := by
    unfold Dyadic.center Dyadic.length; ring
  have hc' : P'.ωu.center + P'.ωu.length =
      P.ωu.length * (((2 : ℤ) ^ t * (2 * P'.ωu.m + 3) : ℤ) : ℝ) := by
    unfold Dyadic.center Dyadic.length
    rw [h2k]
    push_cast
    ring
  set q : ℤ := (2 : ℤ) ^ t * (2 * P'.ωu.m + 3) - P.ωu.m with hq
  have hdiff : P'.ωu.center + P'.ωu.length - (P.ωu.center - P.ωu.length / 2) =
      P.ωu.length * (q : ℝ) := by
    rw [hc', hc, hq]; push_cast; ring
  have h3 : 0 < (3 - C₃) * P.ωu.length := mul_pos (by linarith) hL
  have hqpos : (-1 : ℝ) < q := by
    have h1 : -P.ωu.length < P.ωu.length * (q : ℝ) := by
      rw [← hdiff]; nlinarith
    by_contra hcon
    rw [not_lt] at hcon
    nlinarith
  have hq0 : 0 ≤ q := by
    have : (-1 : ℤ) < q := by exact_mod_cast hqpos
    omega
  have : (0 : ℝ) ≤ P.ωu.length * (q : ℝ) := by
    have : (0 : ℝ) ≤ q := by exact_mod_cast hq0
    positivity
  linarith

end Lattice

section Cases

variable {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ C₃ : ℝ}

/-- Case 1 of `threeterms`: `ξ ∈ C₂ ω_l`. -/
def Multitile.Case1 (C₂ ξ : ℝ) (P : Multitile ρ) : Prop := ξ ∈ P.ωlDil C₂

/-- Case 2 of `threeterms`: `ξ ∉ C₂ ω_l` is not required: `ξ ≥ inf C₃ ω_u`. -/
def Multitile.Case2 (C₃ ξ : ℝ) (P : Multitile ρ) : Prop :=
  P.ωu.center - C₃ * P.ωu.length / 2 ≤ ξ

/-- Case 3 of `threeterms`: `sup C₂ ω_l ≤ ξ < inf C₃ ω_u`. -/
def Multitile.Case3 (C₂ C₃ ξ : ℝ) (P : Multitile ρ) : Prop :=
  P.ωu.center - ((ρ.m : ℝ) + 1) * P.ωu.length + C₂ * P.ωu.length / 2 ≤ ξ ∧
    ξ < P.ωu.center - C₃ * P.ωu.length / 2

/-- **`threeterms`, the covering step** ([O+] L1807-L1809): if `ξ ∈ ω_m(P)` then `ξ ∈ C₂ ω_l`, or
`ξ ≥ inf C₃ ω_u`, or `sup C₂ ω_l ≤ ξ < inf C₃ ω_u`. -/
theorem case_cover (hC₂ : 0 < C₂) {P : Multitile ρ} {ξ : ℝ} (hξ : ξ ∈ P.ωm C₂) :
    Multitile.Case1 C₂ ξ P ∨ Multitile.Case2 C₃ ξ P ∨ Multitile.Case3 C₂ C₃ ξ P := by
  rw [Multitile.ωm_eq_Ico hC₂] at hξ
  obtain ⟨h1, h2⟩ := hξ
  by_cases hA : ξ < P.ωu.center - ((ρ.m : ℝ) + 1) * P.ωu.length + C₂ * P.ωu.length / 2
  · left
    rw [Multitile.Case1, Multitile.ωlDil_eq]
    exact ⟨h1, hA⟩
  · rw [not_lt] at hA
    by_cases hB : P.ωu.center - C₃ * P.ωu.length / 2 ≤ ξ
    · right; left; exact hB
    · right; right; exact ⟨hA, not_le.1 hB⟩

end Cases

end PrimeCarleson.Proof.Oplus
