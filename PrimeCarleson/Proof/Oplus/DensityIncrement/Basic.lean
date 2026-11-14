module

public import PrimeCarleson.Proof.Oplus.EnergyIncrement.Selection
public import PrimeCarleson.Proof.Oplus.TreeSmall.DensityBound

/-!
# Density and the shifted top data for the density increment ([O+] L1895-L1930)

Source: [O+] L1336-L1345 (the density); [O+] `densityincrementprop`, L1900–L1910 and L1913–L1929
(the selection of the trees `T_j`, `T_j^+`, `T_j^-`).

* `treeWeight`, `densityExpr`: the quantity
  `(1/|I_T|) ∫_E (1 + |x - c(I_T)|/|I_T|)^{-4} ∑_{k : ξ_{k-1}(x) ∈ ω_T} |a_k(x)|^{r'} dx` of
  (treehaslargedensity) (`ℝ≥0∞`-valued); it depends on the top data `(I_T, ξ_T)` only, and
  `density` is the supremum of its `1/r'`-th power over the nonempty trees (`density_eq`).
* `IsDenseTree`: a nonempty tree in a family satisfying (treehaslargedensity); `exists_dense_tree`
  starts the selection (`density(𝔓) > den/2`).
* `topShift`, `shiftTree`: the top data `(I_T, ξ_T ± (C₂ - 1)/(2|I_T|))` of `T_j^±` (L1927-L1928).
  A maximal tree with these top data is a tree as soon as it is nonempty
  (`maximalTree_shiftTree_isTree`): the shifted frequency lies in `ω_m(P)` of any of its
  multitiles `P` (hence in `𝒳_top`, `abs_le_of_mem_ωm`) and in the lattice `2^{-M-10} ℤ`
  (`exists_int_eq_shift`, using `C₂ ∈ ℕ`).
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

/-! ### The density integral of a tree -/

section DensityExpr

variable {ρ : Idx} {r : ℝ}

/-- The weight `(1 + |x - c(I_T)|/|I_T|)^{-4}` of (treehaslargedensity) (L1336-L1345). -/
def treeWeight (𝒯 : MultitileTree ρ) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((1 + |x - 𝒯.I.center| / 𝒯.I.length) ^ (-4 : ℤ))

/-- The density integral of a tree (L1336-L1345, L1921-L1927):
`(1/|I_T|) ∫_E (1 + |x - c(I_T)|/|I_T|)^{-4} ∑_{k : ξ_{k-1}(x) ∈ ω_T} |a_k(x)|^{r'} dx`. -/
def densityExpr (L : Linearization r) (E : Set ℝ) (C₂ : ℝ) (𝒯 : MultitileTree ρ) : ℝ≥0∞ :=
  (ENNReal.ofReal 𝒯.I.length)⁻¹ * ∫⁻ x in E, treeWeight 𝒯 x * L.tailSum (𝒯.ωT C₂) x

/-- The density integral depends on the top data `(I_𝒯, ξ_𝒯)` only. -/
theorem densityExpr_congr (L : Linearization r) (E : Set ℝ) (C₂ : ℝ) {𝒯 𝒯' : MultitileTree ρ}
    (hI : 𝒯.I = 𝒯'.I) (hξ : 𝒯.ξ = 𝒯'.ξ) : densityExpr L E C₂ 𝒯 = densityExpr L E C₂ 𝒯' := by
  simp only [densityExpr, treeWeight, MultitileTree.ωT, hI, hξ]

variable [Fact ρ.IsOneOrTwo] {C₁ C₂ : ℝ} {M : ℤ}

/-- `density(S)` is the supremum of `densityExpr^{1/r'}` over the nonempty trees `T ⊂ S`. -/
theorem density_eq (L : Linearization r) (E : Set ℝ) (S : Set (Multitile ρ)) :
    density C₁ C₂ M L E S =
      ⨆ (𝒯 : MultitileTree ρ) (_ : 𝒯.IsTree C₁ C₂ M) (_ : 𝒯.T.Nonempty)
        (_ : (𝒯.T : Set (Multitile ρ)) ⊆ S),
        densityExpr L E C₂ 𝒯 ^ (1 / Real.conjExponent r) := rfl

/-- A nonempty tree `T ⊂ Q` satisfying (treehaslargedensity):
`(1/|I_T|) ∫_E (1 + |x - c(I_T)|/|I_T|)^{-4} ∑_{k : ξ_{k-1}(x) ∈ ω_T} |a_k(x)|^{r'} dx >
(den/2)^{r'}` (L1919-L1927). -/
structure IsDenseTree (C₁ C₂ : ℝ) (M : ℤ) (L : Linearization r) (E : Set ℝ) (den : ℝ)
    (Q : Set (Multitile ρ)) (S : MultitileTree ρ) : Prop where
  isTree : S.IsTree C₁ C₂ M
  nonempty : S.T.Nonempty
  subset : (S.T : Set (Multitile ρ)) ⊆ Q
  large : ENNReal.ofReal (den / 2) ^ Real.conjExponent r < densityExpr L E C₂ S

/-- Being a dense tree in `Q` is monotone in `Q`. -/
theorem IsDenseTree.mono {L : Linearization r} {E : Set ℝ} {den : ℝ} {Q Q' : Set (Multitile ρ)}
    {S : MultitileTree ρ} (h : IsDenseTree C₁ C₂ M L E den Q S) (hQ : Q ⊆ Q') :
    IsDenseTree C₁ C₂ M L E den Q' S :=
  ⟨h.isTree, h.nonempty, h.subset.trans hQ, h.large⟩

/-- A tree with the same top data as a dense tree, with the same support condition, is dense. -/
theorem IsDenseTree.of_top_data {L : Linearization r} {E : Set ℝ} {den : ℝ}
    {Q : Set (Multitile ρ)} {S S' : MultitileTree ρ} (h : IsDenseTree C₁ C₂ M L E den Q S)
    (hI : S'.I = S.I) (hξ : S'.ξ = S.ξ) (hT : S'.IsTree C₁ C₂ M) (hne : S'.T.Nonempty)
    (hsub : (S'.T : Set (Multitile ρ)) ⊆ Q) : IsDenseTree C₁ C₂ M L E den Q S' :=
  ⟨hT, hne, hsub, by rw [densityExpr_congr L E C₂ hI hξ]; exact h.large⟩

/-- **The start of the selection** (L1919-L1927): if `density(Q) > den/2` there is a nonempty tree
`T ⊂ Q` with (treehaslargedensity). -/
theorem exists_dense_tree {L : Linearization r} {E : Set ℝ} {den : ℝ} {Q : Set (Multitile ρ)}
    (hr : 1 < r) (h : ENNReal.ofReal (den / 2) < density C₁ C₂ M L E Q) :
    ∃ 𝒯 : MultitileTree ρ, IsDenseTree C₁ C₂ M L E den Q 𝒯 := by
  have hpos : 0 < Real.conjExponent r := by
    unfold Real.conjExponent
    exact div_pos (by linarith) (by linarith)
  rw [density_eq] at h
  obtain ⟨𝒯, h⟩ := lt_iSup_iff.1 h
  obtain ⟨hT, h⟩ := lt_iSup_iff.1 h
  obtain ⟨hne, h⟩ := lt_iSup_iff.1 h
  obtain ⟨hsub, h⟩ := lt_iSup_iff.1 h
  refine ⟨𝒯, hT, hne, hsub, ?_⟩
  rw [one_div, ENNReal.lt_rpow_inv_iff hpos] at h
  exact h

end DensityExpr

/-! ### Shifted top data -/

section Shift

variable {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ C₃ : ℝ} {M : ℤ}

/-- The shift `(C₂ - 1)/(2|I_T|)` of the top frequency of `T_j^±` (L1927-L1928): the length of
`ω_T`. -/
def topShift (C₂ : ℝ) (𝒯 : MultitileTree ρ) : ℝ := (C₂ - 1) / (2 * 𝒯.I.length)

/-- The top data `(I_T, ξ_T + j (C₂ - 1)/(2|I_T|))` of the shifted trees (`j = ±1`); the
multitile set is that of `𝒯` and plays no role. -/
def shiftTree (C₂ : ℝ) (j : ℤ) (𝒯 : MultitileTree ρ) : MultitileTree ρ :=
  ⟨𝒯.T, 𝒯.I, 𝒯.ξ + j * topShift C₂ 𝒯⟩

omit [Fact ρ.IsOneOrTwo] in
/-- The shifted tree has the same top interval. -/
@[simp] theorem shiftTree_I (C₂ : ℝ) (j : ℤ) (𝒯 : MultitileTree ρ) : (shiftTree C₂ j 𝒯).I = 𝒯.I :=
  rfl

omit [Fact ρ.IsOneOrTwo] in
/-- The shifted top frequency. -/
@[simp] theorem shiftTree_ξ (C₂ : ℝ) (j : ℤ) (𝒯 : MultitileTree ρ) :
    (shiftTree C₂ j 𝒯).ξ = 𝒯.ξ + j * topShift C₂ 𝒯 := rfl

/-- A dyadic interval inside `[-2^M, 2^M)` has `k ≤ M + 1`. -/
theorem Dyadic.k_le_of_subset_Icc {I : Dyadic} {M : ℤ}
    (h : I.toSet ⊆ Icc (-(2 : ℝ) ^ M) ((2 : ℝ) ^ M)) : I.k ≤ M + 1 := by
  have hl := Dyadic.length_le_of_subset_Icc h
  have : (2 : ℝ) ^ I.k ≤ (2 : ℝ) ^ (M + 1) := by
    have e1 : I.length = (2 : ℝ) ^ I.k := rfl
    rw [zpow_add_one₀ (by norm_num)]
    linarith
  exact (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 this

/-- **The shifted top frequencies lie in the lattice `2^{-M-10} ℤ`** (uses `C₂ ∈ ℕ` and
`|I_T| ≤ 2^{M+1}`): `ξ_T + j (C₂ - 1)/(2|I_T|) = n 2^{-M-10}` for an integer `n`. -/
theorem exists_int_eq_shift (hC : AdmissibleConstants C₁ C₂ C₃) {𝒯 : MultitileTree ρ}
    (h𝒯 : 𝒯.IsTree C₁ C₂ M) (j : ℤ) :
    ∃ n : ℤ, 𝒯.ξ + j * topShift C₂ 𝒯 = n * (2 : ℝ) ^ (-M - 10) := by
  obtain ⟨N, hN⟩ := hC.nat_C₂
  obtain ⟨-, n, hn⟩ := h𝒯.ξ_mem
  have hk : 𝒯.I.k ≤ M + 1 :=
    Dyadic.k_le_of_subset_Icc (fun x hx => by
      have := h𝒯.top_subset hx
      exact ⟨this.1, this.2.le⟩)
  have hk' : 0 ≤ M + 9 - 𝒯.I.k := by omega
  have e1 : (2 * 𝒯.I.length)⁻¹ = (2 : ℝ) ^ (M + 9 - 𝒯.I.k) * (2 : ℝ) ^ (-M - 10) := by
    rw [← zpow_add₀ (by norm_num)]
    have : (M + 9 - 𝒯.I.k) + (-M - 10) = -(𝒯.I.k + 1) := by ring
    rw [this, zpow_neg, zpow_add_one₀ (by norm_num)]
    simp only [Dyadic.length]
    rw [mul_comm]
  have e2 : (2 : ℝ) ^ (M + 9 - 𝒯.I.k) = (2 : ℝ) ^ (M + 9 - 𝒯.I.k).toNat := by
    rw [← zpow_natCast, Int.toNat_of_nonneg hk']
  refine ⟨n + j * ((N : ℤ) - 1) * 2 ^ (M + 9 - 𝒯.I.k).toNat, ?_⟩
  unfold topShift
  rw [hn, hN, div_eq_mul_inv, e1, e2]
  push_cast
  ring

/-- A point of `ω_m(P)` for a multitile `P` in the square `[-2^M, 2^M]²` lies in `[-C₁ 2^{M+10},
C₁ 2^{M+10}]`. -/
theorem abs_le_of_mem_ωm (hC : AdmissibleConstants C₁ C₂ C₃) (hρ : ρ.IsStd) {P : Multitile ρ}
    (hP : P.InSquare M) {ξ : ℝ} (hξ : ξ ∈ P.ωm C₂) : |ξ| ≤ C₁ * (2 : ℝ) ^ (M + 10) := by
  have hC₂ : 0 < C₂ := by linarith [hC.one_le, hC.lt₁]
  have hC₁ : 1 ≤ C₁ := by linarith [hC.one_le, hC.lt₁, hC.lt₂]
  rw [Multitile.ωm_eq_Ico hC₂] at hξ
  obtain ⟨h1, h2⟩ := hξ
  have hc := Dyadic.abs_center_le_of_subset_Icc hP.2
  have hL := Dyadic.length_le_of_subset_Icc hP.2
  have hL0 := P.ωu.length_pos
  have hm : (ρ.m : ℝ) ≤ 4 := by exact_mod_cast hρ.2.1
  have hm0 : (0 : ℝ) ≤ ρ.m := Nat.cast_nonneg _
  have hC2m := hC.le_m_add_one hρ
  have h2M : (0 : ℝ) < (2 : ℝ) ^ M := zpow_pos (by norm_num) _
  have h3 : (2 : ℝ) ^ (M + 10) = (2 : ℝ) ^ M * 1024 := by
    rw [zpow_add₀ (by norm_num)]; norm_num
  have h4 : ((ρ.m : ℝ) + 1) * P.ωu.length ≤ 5 * (2 * (2 : ℝ) ^ M) :=
    mul_le_mul (by linarith) hL hL0.le (by norm_num)
  have h5 : C₂ * P.ωu.length ≤ 5 * (2 * (2 : ℝ) ^ M) :=
    mul_le_mul (by linarith) hL hL0.le (by norm_num)
  have h6 : (2 : ℝ) ^ M * 1024 ≤ C₁ * ((2 : ℝ) ^ M * 1024) := by nlinarith
  rw [abs_le] at hc ⊢
  rw [h3]
  constructor <;> nlinarith [hc.1, hc.2]

/-- **A nonempty maximal tree with shifted top data is a tree.** Let `S` be a tree, `Q` a family
of multitiles in the square `[-2^M, 2^M]²`, and suppose the maximal tree in `Q` with top data
`(I_S, ξ_S + j (C₂ - 1)/(2|I_S|))` is nonempty. Then it is a tree: the top frequency lies in
`ω_m(P)` of one of its multitiles, hence in `[-C₁ 2^{M+10}, C₁ 2^{M+10}]`, and in the lattice
`2^{-M-10} ℤ` (`exists_int_eq_shift`). -/
theorem maximalTree_shiftTree_isTree (hC : AdmissibleConstants C₁ C₂ C₃) (hρ : ρ.IsStd)
    {S : MultitileTree ρ} (hS : S.IsTree C₁ C₂ M) (j : ℤ) {Q : Finset (Multitile ρ)}
    (hQ : ∀ P ∈ Q, P.InSquare M)
    (hne : (maximalTree C₂ Q (shiftTree C₂ j S)).T.Nonempty) :
    (maximalTree C₂ Q (shiftTree C₂ j S)).IsTree C₁ C₂ M := by
  have hC₂ : 1 < C₂ := lt_of_le_of_lt hC.one_le hC.lt₁
  refine ⟨hS.top_subset, ⟨?_, exists_int_eq_shift hC hS j⟩, fun P hP =>
    (mem_maximalTree.1 hP).2.1, fun P hP => (mem_maximalTree.1 hP).2.2⟩
  obtain ⟨P, hP⟩ := hne
  obtain ⟨hPQ, -, hPω⟩ := mem_maximalTree.1 hP
  refine abs_le_of_mem_ωm hC hρ (hQ P hPQ) (hPω ?_)
  have hr : 0 < (C₂ - 1) / (4 * S.I.length) := by
    have := S.I.length_pos
    apply div_pos <;> linarith
  exact ⟨by simp only [maximalTree_ξ, shiftTree_I, shiftTree_ξ]; linarith,
    by simp only [maximalTree_ξ, shiftTree_I, shiftTree_ξ]; linarith⟩

end Shift

end PrimeCarleson.Proof.Oplus
