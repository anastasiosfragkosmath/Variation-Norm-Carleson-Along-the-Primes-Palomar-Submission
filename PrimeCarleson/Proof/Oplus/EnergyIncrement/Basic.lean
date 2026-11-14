module

public import PrimeCarleson.Proof.Oplus.Estimates.All

/-!
# Energy and top-data utilities for the energy increment ([O+] L1420-L1500)

Source: [O+] L1313-L1345 (energy), L1449-L1500 (the selection of the trees), [O+]
`energyincrementprop`, L1420–L1447 and its steps. Utilities used by every file of
`EnergyIncrement/`:

* `Dyadic.toSet_subset_Ico_of_subset_Icc`: a dyadic interval inside `[-A, A]` lies in `[-A, A)`;
* `AdmissibleConstants.le_m_add_one`, `AdmissibleConstants.two_m_add_one_add_le`: the numerical
  content `C₂ ≤ m + 1`, `2(m+1) + C₂ ≤ C₁` of the geometric properties of `L1172-L1177`;
* `sum_norm_sq_coeff_le_of_energy_le`: `energy(𝔓) ≤ e` bounds `∑_{P ∈ T} |⟨f, φ_P⟩|² ≤ e² |I_T|` for
  every `l`-overlapping tree `T ⊂ 𝔓`; `exists_large_tree` is the converse, which starts the
  selection (`shaslargeenergy`, L1456-L1459);
* `exists_singleton_tree`, `norm_sq_coeff_le_of_energy_le`: a single multitile of a family inside
  `[-2^M, 2^M]²` is an `l`-overlapping tree ("any fixed multitile forms an `l`-overlapping tree",
  L1822-L1823), hence `|⟨f, φ_P⟩|² ≤ e² |I_P|`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

/-! ### Dyadic intervals in a square -/

/-- A dyadic interval inside `[-A, A]` has its right end point at most `A`. -/
theorem Dyadic.right_le_of_subset_Icc {I : Dyadic} {A : ℝ} (h : I.toSet ⊆ Icc (-A) A) :
    I.right ≤ A := by
  by_contra hcon
  rw [not_le] at hcon
  have hl : I.left ≤ A := (h I.left_mem_toSet).2
  have hlr := I.left_lt_right
  have hx : (A + I.right) / 2 ∈ I.toSet := ⟨by linarith, by linarith⟩
  have := (h hx).2
  linarith

/-- A dyadic interval inside `[-A, A]` lies in `[-A, A)`. -/
theorem Dyadic.toSet_subset_Ico_of_subset_Icc {I : Dyadic} {A : ℝ} (h : I.toSet ⊆ Icc (-A) A) :
    I.toSet ⊆ Ico (-A) A :=
  fun _ hx => ⟨(h hx).1, lt_of_lt_of_le hx.2 (Dyadic.right_le_of_subset_Icc h)⟩

/-- A dyadic interval inside `[-A, A]` has length at most `2A`. -/
theorem Dyadic.length_le_of_subset_Icc {I : Dyadic} {A : ℝ} (h : I.toSet ⊆ Icc (-A) A) :
    I.length ≤ 2 * A := by
  have h1 := Dyadic.right_le_of_subset_Icc h
  have h2 : -A ≤ I.left := (h I.left_mem_toSet).1
  have := I.right_eq
  linarith

/-- The centre of a dyadic interval inside `[-A, A]` has absolute value at most `A`. -/
theorem Dyadic.abs_center_le_of_subset_Icc {I : Dyadic} {A : ℝ} (h : I.toSet ⊆ Icc (-A) A) :
    |I.center| ≤ A := by
  have := h I.center_mem_toSet
  exact abs_le.2 this

/-! ### Numerical content of the geometric properties -/

section Geometry

variable {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ C₃ : ℝ}

/-- `C₂ ≤ m + 1`: from `C₂ ω_u ∩ C₂ ω_l = ∅` (L1172-L1173). -/
theorem AdmissibleConstants.le_m_add_one (hC : AdmissibleConstants C₁ C₂ C₃) (hρ : ρ.IsStd) :
    C₂ ≤ (ρ.m : ℝ) + 1 := by
  obtain ⟨hdisj, -, -, -⟩ := hC.geometry ρ hρ Fact.out (⟨0, 0⟩ : Dyadic)
  have hC₂ : 0 < C₂ := by linarith [hC.one_le, hC.lt₁]
  have hL : (⟨0, 0⟩ : Dyadic).length = 1 := by simp [Dyadic.length]
  have hc : (⟨0, 0⟩ : Dyadic).center = 1 / 2 := by simp [Dyadic.center]
  have hlc := Idx.center_ωlDyadic ρ (⟨0, 0⟩ : Dyadic)
  have hll := Idx.length_ωlDyadic ρ (⟨0, 0⟩ : Dyadic)
  rw [hL, hc] at hlc
  rw [hL] at hll
  by_contra hcon
  rw [not_le] at hcon
  have hx1 : (1 / 2 : ℝ) - C₂ / 2 ∈ (⟨0, 0⟩ : Dyadic).dilate C₂ := by
    simp only [Dyadic.dilate, hL, hc, mem_Ico]
    constructor <;> linarith
  have hx2 : (1 / 2 : ℝ) - C₂ / 2 ∈ (ρ.ωlDyadic (⟨0, 0⟩ : Dyadic)).dilate C₂ := by
    simp only [Dyadic.dilate, hll, hlc, mem_Ico]
    constructor <;> nlinarith [(Nat.cast_nonneg ρ.m : (0 : ℝ) ≤ ρ.m)]
  exact Set.disjoint_left.1 hdisj hx1 hx2

/-- `2(m + 1) + C₂ ≤ C₁`: from `C₂ ω_l ⊂ C₁ ω_u` (L1175). -/
theorem AdmissibleConstants.two_m_add_one_add_le (hC : AdmissibleConstants C₁ C₂ C₃)
    (hρ : ρ.IsStd) : 2 * ((ρ.m : ℝ) + 1) + C₂ ≤ C₁ := by
  obtain ⟨-, -, hsub, -⟩ := hC.geometry ρ hρ Fact.out (⟨0, 0⟩ : Dyadic)
  have hC₂ : 0 < C₂ := by linarith [hC.one_le, hC.lt₁]
  have hL : (⟨0, 0⟩ : Dyadic).length = 1 := by simp [Dyadic.length]
  have hc : (⟨0, 0⟩ : Dyadic).center = 1 / 2 := by simp [Dyadic.center]
  have hlc := Idx.center_ωlDyadic ρ (⟨0, 0⟩ : Dyadic)
  have hll := Idx.length_ωlDyadic ρ (⟨0, 0⟩ : Dyadic)
  rw [hL, hc] at hlc
  rw [hL] at hll
  have hx : (1 / 2 : ℝ) - ((ρ.m : ℝ) + 1) - C₂ / 2 ∈
      (ρ.ωlDyadic (⟨0, 0⟩ : Dyadic)).dilate C₂ := by
    simp only [Dyadic.dilate, hll, hlc, mem_Ico]
    constructor <;> linarith
  have := (hsub hx).1
  simp only [hL, hc] at this
  linarith

end Geometry

/-! ### Energy -/

section Energy

variable {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ C₃ : ℝ} {M : ℤ} {ch : ProfileChoice} {f : ℝ → ℂ}

/-- The extended norms of finitely many numbers sum to the `ofReal` of the real sum. -/
theorem sum_enorm_sq_eq_ofReal {ι : Type*} (T : Finset ι) (c : ι → ℂ) :
    ∑ P ∈ T, ‖c P‖ₑ ^ 2 = ENNReal.ofReal (∑ P ∈ T, ‖c P‖ ^ 2) := by
  rw [ENNReal.ofReal_sum_of_nonneg (fun P _ => by positivity)]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- **`energy(𝔓) ≤ e` bounds every `l`-overlapping tree**: `∑_{P ∈ T} |⟨f, φ_P⟩|² ≤ e² |I_T|`
for every `l`-overlapping tree `T ⊂ 𝔓`. -/
theorem sum_norm_sq_coeff_le_of_energy_le {S : Set (Multitile ρ)} {e : ℝ} (he : 0 ≤ e)
    (h : energy C₁ C₂ M ch f S ≤ ENNReal.ofReal e) {𝒯 : MultitileTree ρ}
    (hT : 𝒯.IsTree C₁ C₂ M) (hov : 𝒯.IsOverlapping C₂) (hsub : (𝒯.T : Set (Multitile ρ)) ⊆ S) :
    ∑ P ∈ 𝒯.T, ‖P.coeff ch f‖ ^ 2 ≤ e ^ 2 * 𝒯.I.length := by
  have hI := 𝒯.I.length_pos
  have h1 : ((ENNReal.ofReal 𝒯.I.length)⁻¹ * ∑ P ∈ 𝒯.T, ‖P.coeff ch f‖ₑ ^ 2) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal e := by
    refine le_trans ?_ h
    unfold energy energyOf
    exact le_iSup₂_of_le 𝒯 hT (le_iSup₂_of_le hov hsub le_rfl)
  rw [one_div, ENNReal.rpow_inv_le_iff (by norm_num : (0 : ℝ) < 2)] at h1
  rw [ENNReal.inv_mul_le_iff (by simpa using hI) ENNReal.ofReal_ne_top] at h1
  rw [sum_enorm_sq_eq_ofReal] at h1
  have h2 : ENNReal.ofReal e ^ (2 : ℝ) = ENNReal.ofReal (e ^ 2) := by
    rw [ENNReal.ofReal_rpow_of_nonneg he (by norm_num)]
    norm_num
  rw [h2, ← ENNReal.ofReal_mul hI.le,
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at h1
  linarith

/-- **The start of the selection** (L1456-L1459): if `energy(𝔓) > e/2` there is an `l`-overlapping
tree `S ⊂ 𝔓` with `(1/|I_S|) ∑_{P ∈ S} |⟨f, φ_P⟩|² ≥ e²/4` (`shaslargeenergy`). -/
theorem exists_large_tree {S : Set (Multitile ρ)} {e : ℝ} (he : 0 < e)
    (h : ENNReal.ofReal (e / 2) < energy C₁ C₂ M ch f S) :
    ∃ 𝒯 : MultitileTree ρ, 𝒯.IsTree C₁ C₂ M ∧ 𝒯.IsOverlapping C₂ ∧
      (𝒯.T : Set (Multitile ρ)) ⊆ S ∧ e ^ 2 / 4 * 𝒯.I.length ≤ ∑ P ∈ 𝒯.T, ‖P.coeff ch f‖ ^ 2 := by
  unfold energy energyOf at h
  obtain ⟨𝒯, h⟩ := lt_iSup_iff.1 h
  obtain ⟨hT, h⟩ := lt_iSup_iff.1 h
  obtain ⟨hov, h⟩ := lt_iSup_iff.1 h
  obtain ⟨hsub, h⟩ := lt_iSup_iff.1 h
  refine ⟨𝒯, hT, hov, hsub, ?_⟩
  have hI := 𝒯.I.length_pos
  rw [one_div, ENNReal.lt_rpow_inv_iff (by norm_num : (0 : ℝ) < 2)] at h
  have h2 : ENNReal.ofReal (e / 2) ^ (2 : ℝ) = ENNReal.ofReal ((e / 2) ^ 2) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
    norm_num
  rw [h2, ← ENNReal.ofReal_inv_of_pos hI, sum_enorm_sq_eq_ofReal,
    ← ENNReal.ofReal_mul (inv_pos.2 hI).le] at h
  have h3 := (ENNReal.ofReal_lt_ofReal_iff'.1 h).1
  have h4 := (le_inv_mul_iff₀ hI).1 h3.le
  linarith

/-! ### A single multitile is an `l`-overlapping tree -/

/-- The top frequency `c(ω_l)` of the singleton tree of `P` lies in `𝒳_top` when `P` lies in the
square `[-2^M, 2^M]²` (`m ≤ 4`, `C₁ ≥ 1`): it is a multiple of `|ω_u|/2 ≥ 2^{-M-3}` of modulus
at most `11 · 2^M`. -/
theorem Multitile.center_ωlDyadic_mem_Xtop {ρ : Idx} (hρ : ρ.IsStd) {C₁ : ℝ} (hC₁ : 1 ≤ C₁)
    {M : ℤ} {P : Multitile ρ} (hP : P.InSquare M) :
    (ρ.ωlDyadic P.ωu).center ∈ Xtop C₁ M := by
  have hL := P.ωu.length_pos
  have h2M : (0 : ℝ) < (2 : ℝ) ^ M := zpow_pos (by norm_num) _
  obtain ⟨-, hm4, -, -⟩ := hρ
  have hm4' : (ρ.m : ℝ) ≤ 4 := by exact_mod_cast hm4
  have hm0 : (0 : ℝ) ≤ ρ.m := Nat.cast_nonneg _
  refine ⟨?_, ?_⟩
  · -- the size
    have h1 := Dyadic.abs_center_le_of_subset_Icc hP.2
    have h2 := Dyadic.length_le_of_subset_Icc hP.2
    rw [Idx.center_ωlDyadic]
    have h3 : (2 : ℝ) ^ (M + 10) = (2 : ℝ) ^ M * 1024 := by
      rw [zpow_add₀ (by norm_num)]; norm_num
    rw [h3]
    have h4 : ((ρ.m : ℝ) + 1) * P.ωu.length ≤ 5 * (2 * (2 : ℝ) ^ M) := by
      apply mul_le_mul (by linarith) h2 hL.le (by norm_num)
    rw [abs_le] at h1 ⊢
    constructor <;> nlinarith [h1.1, h1.2]
  · -- the lattice
    have hk : P.I.k ≤ M + 1 := by
      have h := Dyadic.length_le_of_subset_Icc hP.1
      have : (2 : ℝ) ^ P.I.k ≤ (2 : ℝ) ^ (M + 1) := by
        have e1 : P.I.length = (2 : ℝ) ^ P.I.k := rfl
        rw [zpow_add_one₀ (by norm_num)]
        linarith
      exact (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 this
    have harea := P.area
    set m' : ℤ := P.ωu.m - ((ρ.m : ℤ) + 1) with hm'
    have hcen : (ρ.ωlDyadic P.ωu).center = (2 : ℝ) ^ P.ωu.k * ((m' : ℝ) + 1 / 2) := by
      unfold Idx.ωlDyadic Dyadic.center Dyadic.shift
      simp only [hm']
      push_cast
      ring
    refine ⟨(2 * m' + 1) * (2 : ℤ) ^ (P.ωu.k + M + 9).toNat, ?_⟩
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

/-- A multitile in the square `[-2^M, 2^M]²` is an `l`-overlapping tree with top interval `I` and
top frequency `c(ω_l)` ("any fixed multitile forms an `l`-overlapping tree", L1822-L1823). -/
theorem exists_singleton_tree {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ C₃ : ℝ}
    (hC : AdmissibleConstants C₁ C₂ C₃) (hρ : ρ.IsStd) {M : ℤ} {P : Multitile ρ}
    (hP : P.InSquare M) :
    ∃ 𝒯 : MultitileTree ρ, 𝒯.T = {P} ∧ 𝒯.I = P.I ∧ 𝒯.IsTree C₁ C₂ M ∧ 𝒯.IsOverlapping C₂ := by
  have hC₂ : 0 < C₂ := by linarith [hC.one_le, hC.lt₁]
  have hC₂1 : 1 < C₂ := lt_of_le_of_lt hC.one_le hC.lt₁
  have hL := P.ωu.length_pos
  have hI := P.I.length_pos
  have harea := P.length_I_mul_length_ωu
  set ξ : ℝ := (ρ.ωlDyadic P.ωu).center with hξ
  have hdil : P.ωlDil C₂ = Ico (ξ - C₂ * P.ωu.length / 2) (ξ + C₂ * P.ωu.length / 2) := by
    unfold Multitile.ωlDil Dyadic.dilate
    rw [Idx.length_ωlDyadic]
  refine ⟨⟨{P}, P.I, ξ⟩, rfl, rfl, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · exact Dyadic.toSet_subset_Ico_of_subset_Icc hP.1
  · exact Multitile.center_ωlDyadic_mem_Xtop hρ (by linarith [hC.one_le, hC.lt₁, hC.lt₂]) hP
  · intro Q hQ
    rw [Finset.mem_singleton] at hQ
    rw [hQ]
  · intro Q hQ
    rw [Finset.mem_singleton] at hQ
    subst hQ
    have hsub : Q.ωlDil C₂ ⊆ Q.ωm C₂ := fun x hx =>
      subset_convexHull ℝ _ (Or.inr hx)
    refine Set.Subset.trans ?_ hsub
    rw [hdil]
    have h1 : (C₂ - 1) / (4 * Q.I.length) = (C₂ - 1) * Q.ωu.length / 2 := by
      field_simp
      linarith
    refine Ico_subset_Ico ?_ ?_
    · change ξ - C₂ * Q.ωu.length / 2 ≤ ξ - (C₂ - 1) / (4 * Q.I.length)
      rw [h1]; nlinarith
    · change ξ + (C₂ - 1) / (4 * Q.I.length) ≤ ξ + C₂ * Q.ωu.length / 2
      rw [h1]; nlinarith
  · intro Q hQ
    rw [Finset.mem_singleton] at hQ
    subst hQ
    change ξ ∈ Q.ωlDil C₂
    rw [hdil]
    constructor <;> nlinarith

/-- **A single multitile of the family has `|⟨f, φ_P⟩|² ≤ e² |I_P|`** when `energy(𝔓) ≤ e`
(L1822-L1823: "we use the energy bound for fixed tiles"). -/
theorem norm_sq_coeff_le_of_energy_le {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ C₃ : ℝ} {M : ℤ}
    {ch : ProfileChoice} {f : ℝ → ℂ} (hC : AdmissibleConstants C₁ C₂ C₃) (hρ : ρ.IsStd)
    {S : Set (Multitile ρ)} {e : ℝ} (he : 0 ≤ e)
    (h : energy C₁ C₂ M ch f S ≤ ENNReal.ofReal e) {P : Multitile ρ} (hPS : P ∈ S)
    (hP : P.InSquare M) : ‖P.coeff ch f‖ ^ 2 ≤ e ^ 2 * P.I.length := by
  obtain ⟨𝒯, hT, hI, htree, hov⟩ := exists_singleton_tree hC hρ hP
  have := sum_norm_sq_coeff_le_of_energy_le he h htree hov (by simpa [hT] using hPS)
  rwa [hT, Finset.sum_singleton, hI] at this

end Energy

end PrimeCarleson.Proof.Oplus
