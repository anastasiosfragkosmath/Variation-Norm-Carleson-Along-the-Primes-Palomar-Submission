module

public import PrimeCarleson.Proof.Oplus.TreeSmall.Cases

/-!
# The density bound on `J` ([O+] L2152-L2199)

Source: [O+] `usedensitybound`, L2152–L2157 (L2152-L2199): for
a tree `T` which is `l`-lacunary, `l⁺`-overlapping or `l⁻`-overlapping, and `J ∈ 𝒥`,
`∫_{J ∩ E} ∑_{k : ξ_{k-1}(x) ∈ Ω_J} |a_k(x)|^{r'} dx ≲ den^{r'} |J|`
with `Ω_J = ⋃_{P ∈ T, |I| ≥ C''|J|} ω_l`, `C'' = 8C₁/(C₂ - 1)`.

* `Linearization.tailSum L Ω x = ∑_{k : ξ_{k-1}(x) ∈ Ω} |a_k(x)|^{r'}` (in `ℝ≥0∞`);
* `lintegral_le_of_density_le`: the defining inequality of the density for one nonempty tree
  `T' ⊂ S`, `∫_E (1 + |x - c(I_{T'})|/|I_{T'}|)^{-4} ∑_{ξ_{k-1}(x) ∈ ω_{T'}} |a_k(x)|^{r'} dx ≤
  den^{r'} |I_{T'}|` when `density(S) ≤ den`;
* `usedensitybound` (the claim, with the constant `4 (11/2)^4`): the one-multitile tree `T'` of the
  three cases of `Cases.lean` has top interval `J'`, `|J'| ≤ 4|J|`, and the weight at `x ∈ J` is at
  least `(2/11)^4`.

The top data of `T'` must be admissible for the ambient `M` (`J' ⊂ [-2^M, 2^M)`, `ξ' ∈ 𝒳_top`),
which the source does not check: `J' ⊂ [-2^M, 2^M)` follows from `Ω_J ≠ ∅` (some `|I| ≥ C''|J|`
with `I ⊂ I_T ⊂ [-2^M, 2^M)` forces `|J'| ≤ 4|J| ≤ 2^M`, as `C'' ≥ 8`), and `ξ' ∈ 𝒳_top` follows
from the hypothesis that the multitiles of `T` lie in the square `[-2^M, 2^M]²`
(`shifted_mem_Xtop`). `E` is measurable, as in the source.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

/-- `∑_{k : ξ_{k-1}(x) ∈ Ω} |a_k(x)|^{r'}`, the sum appearing in the density and in
(usedensitybound), valued in `ℝ≥0∞`. -/
def Linearization.tailSum {r : ℝ} (L : Linearization r) (Ω : Set ℝ) (x : ℝ) : ℝ≥0∞ :=
  ∑ k : Fin L.K, ‖L.a k x‖ₑ ^ Real.conjExponent r *
    Ω.indicator (fun _ => (1 : ℝ≥0∞)) (L.ξ k.castSucc x)

/-- The tail sum is monotone in the set. -/
theorem Linearization.tailSum_mono {r : ℝ} (L : Linearization r) {Ω Ω' : Set ℝ} (h : Ω ⊆ Ω')
    (x : ℝ) : L.tailSum Ω x ≤ L.tailSum Ω' x := by
  unfold Linearization.tailSum
  refine Finset.sum_le_sum fun k _ => ?_
  gcongr

/-- The tail sum over the empty set vanishes. -/
@[simp] theorem Linearization.tailSum_empty {r : ℝ} (L : Linearization r) (x : ℝ) :
    L.tailSum ∅ x = 0 := by
  simp [Linearization.tailSum]

section Density

variable {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ C₃ : ℝ} {M : ℤ}

/-- **The defining inequality of the density, for one tree.** If `density(S) ≤ den` and `T' ⊂ S` is
a nonempty tree, then
`∫_E (1 + |x - c(I_{T'})|/|I_{T'}|)^{-4} ∑_{k : ξ_{k-1}(x) ∈ ω_{T'}} |a_k(x)|^{r'} dx ≤
den^{r'} |I_{T'}|` (L2195-L2199). -/
theorem lintegral_le_of_density_le {r : ℝ} (hr : 1 < r) (L : Linearization r) (E : Set ℝ)
    {S : Set (Multitile ρ)} {den : ℝ≥0∞} (h : density C₁ C₂ M L E S ≤ den)
    {𝒯' : MultitileTree ρ} (hT' : 𝒯'.IsTree C₁ C₂ M) (hne : 𝒯'.T.Nonempty)
    (hsub : (𝒯'.T : Set (Multitile ρ)) ⊆ S) :
    ∫⁻ x in E, ENNReal.ofReal ((1 + |x - 𝒯'.I.center| / 𝒯'.I.length) ^ (-4 : ℤ)) *
        L.tailSum (𝒯'.ωT C₂) x ≤ den ^ Real.conjExponent r * ENNReal.ofReal 𝒯'.I.length := by
  have hr' : 0 < Real.conjExponent r := by
    unfold Real.conjExponent
    exact div_pos (by linarith) (by linarith)
  have hI := 𝒯'.I.length_pos
  have h1 : ((ENNReal.ofReal 𝒯'.I.length)⁻¹ * ∫⁻ x in E,
      ENNReal.ofReal ((1 + |x - 𝒯'.I.center| / 𝒯'.I.length) ^ (-4 : ℤ)) *
        L.tailSum (𝒯'.ωT C₂) x) ^ (1 / Real.conjExponent r) ≤ den := by
    refine le_trans ?_ h
    unfold density
    exact le_iSup₂_of_le 𝒯' hT' (le_iSup₂_of_le hne hsub le_rfl)
  rw [one_div, ENNReal.rpow_inv_le_iff hr',
    ENNReal.inv_mul_le_iff (ENNReal.ofReal_pos.2 hI).ne' ENNReal.ofReal_ne_top] at h1
  rw [mul_comm]
  exact h1

/-- **The weight step** (L2195-L2199, L2102-L2105): if `Ω ⊂ ω_{T'}` for a nonempty tree `T' ⊂ S`
and `1 + |x - c(I_{T'})|/|I_{T'}| ≤ B` for `x ∈ J`, then
`∫_{J ∩ E} ∑_{ξ_{k-1}(x) ∈ Ω} |a_k(x)|^{r'} ≤ B⁴ den^{r'} |I_{T'}|` when `density(S) ≤ den`. -/
theorem lintegral_tailSum_le_of_weight {r : ℝ} (hr : 1 < r) (L : Linearization r) {E : Set ℝ}
    (hE : MeasurableSet E) {S : Set (Multitile ρ)} {den : ℝ≥0∞}
    (h : density C₁ C₂ M L E S ≤ den) {𝒯' : MultitileTree ρ} (hT' : 𝒯'.IsTree C₁ C₂ M)
    (hne : 𝒯'.T.Nonempty) (hsub : (𝒯'.T : Set (Multitile ρ)) ⊆ S) {Ω : Set ℝ}
    (hΩ : Ω ⊆ 𝒯'.ωT C₂) {J : Dyadic} {B : ℝ}
    (hB : ∀ x ∈ J.toSet, 1 + |x - 𝒯'.I.center| / 𝒯'.I.length ≤ B) :
    ∫⁻ x in J.toSet ∩ E, L.tailSum Ω x ≤
      ENNReal.ofReal (B ^ 4) * (den ^ Real.conjExponent r * ENNReal.ofReal 𝒯'.I.length) := by
  have hI := 𝒯'.I.length_pos
  have hmeas : MeasurableSet (J.toSet ∩ E) := J.measurableSet_toSet.inter hE
  have hpt : ∀ x ∈ J.toSet ∩ E, L.tailSum Ω x ≤ ENNReal.ofReal (B ^ 4) *
      (ENNReal.ofReal ((1 + |x - 𝒯'.I.center| / 𝒯'.I.length) ^ (-4 : ℤ)) *
        L.tailSum (𝒯'.ωT C₂) x) := by
    intro x hx
    have ht := hB x hx.1
    have h0 : 0 < 1 + |x - 𝒯'.I.center| / 𝒯'.I.length := by positivity
    have hw : (B ^ 4)⁻¹ ≤ (1 + |x - 𝒯'.I.center| / 𝒯'.I.length) ^ (-4 : ℤ) := by
      rw [show (-4 : ℤ) = -((4 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast]
      exact inv_anti₀ (by positivity) (pow_le_pow_left₀ h0.le ht 4)
    have hBpos : 0 < B := lt_of_lt_of_le h0 ht
    have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (B ^ 4) *
        ENNReal.ofReal ((1 + |x - 𝒯'.I.center| / 𝒯'.I.length) ^ (-4 : ℤ)) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      rw [← ENNReal.ofReal_one]
      refine ENNReal.ofReal_le_ofReal ?_
      calc (1 : ℝ) = B ^ 4 * (B ^ 4)⁻¹ := by field_simp
        _ ≤ _ := by gcongr
    calc L.tailSum Ω x ≤ L.tailSum (𝒯'.ωT C₂) x := L.tailSum_mono hΩ x
      _ = 1 * L.tailSum (𝒯'.ωT C₂) x := (one_mul _).symm
      _ ≤ (ENNReal.ofReal (B ^ 4) *
          ENNReal.ofReal ((1 + |x - 𝒯'.I.center| / 𝒯'.I.length) ^ (-4 : ℤ))) *
            L.tailSum (𝒯'.ωT C₂) x := by gcongr
      _ = _ := mul_assoc _ _ _
  calc ∫⁻ x in J.toSet ∩ E, L.tailSum Ω x
      ≤ ∫⁻ x in J.toSet ∩ E, ENNReal.ofReal (B ^ 4) *
        (ENNReal.ofReal ((1 + |x - 𝒯'.I.center| / 𝒯'.I.length) ^ (-4 : ℤ)) *
          L.tailSum (𝒯'.ωT C₂) x) := setLIntegral_mono' hmeas hpt
    _ = ENNReal.ofReal (B ^ 4) * ∫⁻ x in J.toSet ∩ E,
        ENNReal.ofReal ((1 + |x - 𝒯'.I.center| / 𝒯'.I.length) ^ (-4 : ℤ)) *
          L.tailSum (𝒯'.ωT C₂) x := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (B ^ 4) * ∫⁻ x in E,
        ENNReal.ofReal ((1 + |x - 𝒯'.I.center| / 𝒯'.I.length) ^ (-4 : ℤ)) *
          L.tailSum (𝒯'.ωT C₂) x := by
        gcongr
        exact Set.inter_subset_right
    _ ≤ ENNReal.ofReal (B ^ 4) * (den ^ Real.conjExponent r * ENNReal.ofReal 𝒯'.I.length) := by
        gcongr
        exact lintegral_le_of_density_le hr L E h hT' hne hsub

/-- **The final step of (usedensitybound)** (L2195-L2199): if `Ω ⊂ ω_{T'}` for a nonempty tree
`T' ⊂ S` whose top interval has `|I_{T'}| ≤ 4|J|` and `|x - c(I_{T'})| ≤ (9/2)|I_{T'}|` for
`x ∈ J`, then `∫_{J ∩ E} ∑_{ξ_{k-1}(x) ∈ Ω} |a_k(x)|^{r'} ≤ 4(11/2)^4 den^{r'} |J|`. -/
theorem lintegral_tailSum_le_of_tree {r : ℝ} (hr : 1 < r) (L : Linearization r) {E : Set ℝ}
    (hE : MeasurableSet E) {S : Set (Multitile ρ)} {den : ℝ≥0∞}
    (h : density C₁ C₂ M L E S ≤ den) {𝒯' : MultitileTree ρ} (hT' : 𝒯'.IsTree C₁ C₂ M)
    (hne : 𝒯'.T.Nonempty) (hsub : (𝒯'.T : Set (Multitile ρ)) ⊆ S) {Ω : Set ℝ}
    (hΩ : Ω ⊆ 𝒯'.ωT C₂) {J : Dyadic} (h4 : 𝒯'.I.length ≤ 4 * J.length)
    (hdist : ∀ x ∈ J.toSet, |x - 𝒯'.I.center| ≤ 9 / 2 * 𝒯'.I.length) :
    ∫⁻ x in J.toSet ∩ E, L.tailSum Ω x ≤
      ENNReal.ofReal (4 * (11 / 2) ^ 4) * den ^ Real.conjExponent r * ENNReal.ofReal J.length := by
  have hI := 𝒯'.I.length_pos
  have h1 := lintegral_tailSum_le_of_weight hr L hE h hT' hne hsub hΩ (J := J) (B := 11 / 2)
    (fun x hx => by
      have := hdist x hx
      have h2 : |x - 𝒯'.I.center| / 𝒯'.I.length ≤ 9 / 2 := by
        rw [div_le_iff₀ hI]; linarith
      linarith)
  refine h1.trans ?_
  calc ENNReal.ofReal ((11 / 2) ^ 4) * (den ^ Real.conjExponent r * ENNReal.ofReal 𝒯'.I.length)
      ≤ ENNReal.ofReal ((11 / 2) ^ 4) *
        (den ^ Real.conjExponent r * ENNReal.ofReal (4 * J.length)) := by gcongr
    _ = ENNReal.ofReal (4 * (11 / 2) ^ 4) * den ^ Real.conjExponent r *
        ENNReal.ofReal J.length := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
        ring

/-- **`usedensitybound`** ([O+] L2152-L2199). Let `T` be an `l`-lacunary, `l⁺`-overlapping or
`l⁻`-overlapping tree of multitiles inside the square `[-2^M, 2^M]²` with `T ⊂ S`,
`density(S) ≤ den`, and `J ∈ 𝒥`. Then
`∫_{J ∩ E} ∑_{k : ξ_{k-1}(x) ∈ Ω_J} |a_k(x)|^{r'} dx ≤ 4(11/2)^4 den^{r'} |J|`. -/
theorem usedensitybound (hC : AdmissibleConstants C₁ C₂ C₃) (hρ : ρ.IsStd) {r : ℝ} (hr : 1 < r)
    (L : Linearization r) {E : Set ℝ} (hE : MeasurableSet E) {S : Set (Multitile ρ)}
    {den : ℝ≥0∞} (hden : density C₁ C₂ M L E S ≤ den) {𝒯 : MultitileTree ρ}
    (hT : 𝒯.IsTree C₁ C₂ M) (hsq : ∀ P ∈ 𝒯.T, P.InSquare M)
    (hsub : (𝒯.T : Set (Multitile ρ)) ⊆ S) (hspec : 𝒯.IsSpecial C₂) {J : Dyadic}
    (hJ : 𝒯.IsMaxAvoiding J) :
    ∫⁻ x in J.toSet ∩ E, L.tailSum (𝒯.OmegaJ (Cpp C₁ C₂) J) x ≤
      ENNReal.ofReal (4 * (11 / 2) ^ 4) * den ^ Real.conjExponent r * ENNReal.ofReal J.length := by
  by_cases hΩ : ∃ P₀ ∈ 𝒯.T, Cpp C₁ C₂ * J.length ≤ P₀.I.length
  swap
  · have h0 : 𝒯.OmegaJ (Cpp C₁ C₂) J = ∅ := by
      ext y
      simp only [MultitileTree.OmegaJ, mem_ofPred_eq, mem_empty_iff_false, iff_false]
      rintro ⟨P, hP, hl, -⟩
      exact hΩ ⟨P, hP, hl⟩
    rw [h0]
    simp
  obtain ⟨P₀, hP₀, hP₀l⟩ := hΩ
  obtain ⟨P, hP, -, J', hJ'1, hJ'2, hJ'sub, hJ'dist⟩ :=
    MultitileTree.exists_nearby_tile_and_interval hJ
  have hC8 := eight_le_Cpp hC
  have hJpos := J.length_pos
  have hIT : 𝒯.I.length ≤ 2 * (2 : ℝ) ^ M :=
    Dyadic.length_le_of_subset_Icc (hT.top_subset.trans Ico_subset_Icc_self)
  have hI₀ : P₀.I.length ≤ 𝒯.I.length :=
    Dyadic.length_le_iff.2 (Dyadic.k_le_of_toSet_subset (hT.time P₀ hP₀))
  have hJ'M : J'.toSet ⊆ Ico (-(2 : ℝ) ^ M) ((2 : ℝ) ^ M) := by
    refine Dyadic.subset_Ico_of_length_le (z := P.I.left) (hJ'sub P.I.left_mem_toSet)
      (hT.top_subset (hT.time P hP P.I.left_mem_toSet)) ?_
    nlinarith
  have hne : (MultitileTree.single P J' 𝒯.ξ).T.Nonempty := Finset.singleton_nonempty P
  have hsubS : ∀ ξ', ((MultitileTree.single P J' ξ').T : Set (Multitile ρ)) ⊆ S := by
    intro ξ'
    rw [MultitileTree.single_T, Finset.coe_singleton, Set.singleton_subset_iff]
    exact hsub hP
  rcases hspec with hlac | ⟨hov, hplus⟩ | ⟨hov, hminus⟩
  · obtain ⟨hT', hΩ'⟩ := case_lacunary hC hρ hT hlac hP (hsq P hP) hJ'2 hJ'sub hJ'M
    exact lintegral_tailSum_le_of_tree hr L hE hden hT' (Finset.singleton_nonempty P) (hsubS _)
      hΩ' hJ'2 hJ'dist
  · obtain ⟨hT', hΩ'⟩ := case_plus_overlapping hC hρ hT hov hplus hP hJ'2 hJ'sub hJ'M
    exact lintegral_tailSum_le_of_tree hr L hE hden hT' (Finset.singleton_nonempty P) (hsubS _)
      hΩ' hJ'2 hJ'dist
  · obtain ⟨hT', hΩ'⟩ := case_minus_overlapping hC hρ hT hov hminus hP (hsq P hP) hJ'2 hJ'sub hJ'M
    exact lintegral_tailSum_le_of_tree hr L hE hden hT' (Finset.singleton_nonempty P) (hsubS _)
      hΩ' hJ'2 hJ'dist

end Density

end PrimeCarleson.Proof.Oplus
