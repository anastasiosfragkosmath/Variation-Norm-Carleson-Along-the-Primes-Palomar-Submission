module

public import PrimeCarleson.Proof.Oplus.TreeSmall.TreeSum
public import PrimeCarleson.Proof.Oplus.TreeSmall.WeightSums

/-!
# The `l`-lacunary case of the large-interval estimate ([O+] L2201-L2252)

Source: [O+] `treeestimatelargeintervals`, L2201–L2252 (the lacunary case and its unique-scale
claim).

* `lacunary_no_smaller_scale`, `lacunary_unique_scale` (L2204-L2216): in an `l`-lacunary tree
  satisfying (separationofscales) and (separationprop2), if `P, P' ∈ T`, `ξ_{k-1}(x) ∈ ω_l`,
  `ξ_k(x) ∈ ω_h` for `P` and `ξ_{k'-1}(x) ∈ ω_l'`, `ξ_{k'}(x) ∈ ω_h'` for `P'`, then
  `|I| = |I'|` and `k = k'`: at each `x` at most one scale and one index `k` occur. (The proof
  also shows that no `ξ_j(x)` lies in `ω_l'` for a tile of larger time interval; the condition on
  `ξ_{k'}(x)` is used only for the equal-scale case.)
* `treeSum_zero_or_le_of_lacunary`: the resulting pointwise bound, `|∑_{P ∈ T'} ⟨f, φ_P⟩ φ_P(x)
  a_P(x)| ≤ K₁ ene |a_k(x)|` for the unique `k` (or the sum vanishes), using
  `|⟨f, φ_P⟩| ≤ ene |I|^{1/2}` (the energy bound for single multitiles), the wave packet bound
  `|φ_P(x)| ≲ |I|^{-1/2}(1 + |x - c(I)|/|I|)^{-2}` and the sum of the weights over the disjoint
  time intervals of one scale (`WeightSums.lean`, Observation (iii)).
* `lacunary_case` (L2244-L2249): for `q ≥ r'` and `J ∈ 𝒥`,
  `∫_J |∑_{P ∈ T : |I| ≥ C''|J|} ⟨f, φ_P⟩ φ_P a_P 1_E|^q ≤ K ene^q den^{r'} |J|`, from
  `usedensitybound`, `q ≥ r'` and `|a_k| ≤ 1`; `lacunary_case_sum`: summing over `J ∈ 𝒥` meeting
  `16 I_T` (total length `≤ 48 |I_T|`) gives `K ene^q den^{r'} |I_T|`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

section UniqueScale

variable {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ C₃ : ℝ} {M : ℤ}

/-- In a tree with (separationprop2) multitiles of the same time length have the same `ω_u`
(this is the first step of Observation (iii)). -/
theorem ωu_eq_of_I_length_eq_of_tree (hC : AdmissibleConstants C₁ C₂ C₃) (hρ : ρ.IsStd)
    {𝒯 : MultitileTree ρ} (hT : 𝒯.IsTree C₁ C₂ M)
    (hp2 : SeparationProp2 C₁ (𝒯.T : Set (Multitile ρ))) {P P' : Multitile ρ} (hP : P ∈ 𝒯.T)
    (hP' : P' ∈ 𝒯.T) (hlen : P.I.length = P'.I.length) : P.ωu = P'.ωu := by
  have hC2 : 1 < C₂ := lt_of_le_of_lt hC.one_le hC.lt₁
  have hξ := 𝒯.mem_ωT_self hC2
  have h1 : 𝒯.ξ ∈ P.ωuDil C₁ := Multitile.ωm_subset_ωuDil hC hρ P (hT.freq P hP hξ)
  have h2 : 𝒯.ξ ∈ P'.ωuDil C₁ := Multitile.ωm_subset_ωuDil hC hρ P' (hT.freq P' hP' hξ)
  exact hp2 P hP P' hP' ⟨𝒯.ξ, h1, h2⟩ (Multitile.ωu_length_eq_of_I_length_eq hlen)

/-- **`ξ_𝒯` is at least `sup C₂ ω_l(P)` in an `l`-lacunary tree.** -/
theorem lacunary_xi_ge (hC : AdmissibleConstants C₁ C₂ C₃) {𝒯 : MultitileTree ρ}
    (hT : 𝒯.IsTree C₁ C₂ M) (hlac : 𝒯.IsLacunary C₂) {P : Multitile ρ} (hP : P ∈ 𝒯.T) :
    P.ωu.center - ((ρ.m : ℝ) + 1) * P.ωu.length + C₂ * P.ωu.length / 2 ≤ 𝒯.ξ := by
  have h1 := hlac P hP
  rw [Multitile.ωlDil_eq] at h1
  have h2 := (tree_xi_bounds hC hT hP).1
  by_contra hcon
  exact h1 ⟨by linarith, by linarith⟩

/-- Every point of `ω_h` is at least `sup C₂ ω_u` (`C₂ ω_u ∩ ω_h = ∅`, L1173-L1174). -/
theorem Multitile.ge_of_mem_ωh (hC : AdmissibleConstants C₁ C₂ C₃) (hρ : ρ.IsStd)
    (P : Multitile ρ) {z : ℝ} (hz : z ∈ P.ωh) : P.ωu.center + C₂ * P.ωu.length / 2 ≤ z := by
  have hdisj := (hC.geometry ρ hρ Fact.out P.ωu).2.1
  have h1 := ρ.left_lt_of_mem_ωh P.ωu hz
  have hL := P.ωu.length_pos
  have hcen := P.ωu.center_eq
  by_contra hcon
  rw [not_le] at hcon
  refine Set.disjoint_left.1 hdisj ?_ hz
  have hCL : 0 ≤ (C₂ - 1) * P.ωu.length :=
    mul_nonneg (by linarith [hC.one_le, hC.lt₁]) hL.le
  rw [Dyadic.mem_dilate]
  constructor <;> linarith

/-- **No tile with a larger time interval can have `ξ_j(x) ∈ ω_l'`** once some `P` has
`ξ_{k-1}(x) ∈ ω_l`, `ξ_k(x) ∈ ω_h` (L2208-L2216). -/
theorem lacunary_no_smaller_scale (hC : AdmissibleConstants C₁ C₂ C₃) (hρ : ρ.IsStd)
    {𝒯 : MultitileTree ρ} (hT : 𝒯.IsTree C₁ C₂ M) (hlac : 𝒯.IsLacunary C₂)
    (hsc : SeparationOfScales C₁ C₂ C₃ (𝒯.T : Set (Multitile ρ))) {r : ℝ} (L : Linearization r)
    (x : ℝ) {P P' : Multitile ρ} (hP : P ∈ 𝒯.T) (hP' : P' ∈ 𝒯.T)
    (hlt : P'.ωu.length < P.ωu.length) {k : Fin L.K}
    (h1 : L.ξ k.castSucc x ∈ P.ωl ∧ L.ξ k.succ x ∈ P.ωh) (j : Fin (L.K + 1))
    (hj : L.ξ j x ∈ P'.ωl) : False := by
  have hC₂ : 1 < C₂ := lt_of_le_of_lt hC.one_le hC.lt₁
  have hC1 : 0 < C₁ := by linarith [hC.one_le, hC.lt₁, hC.lt₂]
  have hL := P.ωu.length_pos
  have hL' := P'.ωu.length_pos
  have hs2 := hC.two_m_add_one_add_le hρ
  have hsc' := hsc P hP P' hP' hlt
  have h7 : 2 * C₁ * P'.ωu.length ≤ (C₂ - C₃) * P.ωu.length := by
    calc 2 * C₁ * P'.ωu.length = 2 * (C₁ * P'.ωu.length) := by ring
      _ ≤ 2 * (C₁ * ((C₂ - C₃) / (2 * C₁) * P.ωu.length)) := by gcongr
      _ = (C₂ - C₃) * P.ωu.length := by field_simp
  have hξP := lacunary_xi_ge hC hT hlac hP
  have hξP' := lacunary_xi_ge hC hT hlac hP'
  have hξP2 := (tree_xi_bounds hC hT hP).2
  have hξP2' := (tree_xi_bounds hC hT hP').2
  have hy := (Multitile.mem_ωl_iff P).1 h1.1
  have hw := (Multitile.mem_ωl_iff P').1 hj
  have hz := Multitile.ge_of_mem_ωh hC hρ P h1.2
  have hk : ((ρ.m : ℝ) + 1 + (C₂ + 1) / 2) * P'.ωu.length ≤ C₁ * P'.ωu.length :=
    mul_le_mul_of_nonneg_right (by linarith [hC.lt₂, hC.one_le]) hL'.le
  have hyw : L.ξ k.castSucc x < L.ξ j x := by
    have hC3 := hC.one_le
    nlinarith [hy.2, hw.1]
  have hwz : L.ξ j x < L.ξ k.succ x := by
    have hk2 : 0 ≤ (C₂ - 1) / 2 * P'.ωu.length := mul_nonneg (by linarith) hL'.le
    nlinarith [hw.2]
  have hj1 : k.castSucc < j := (L.strictMono_ξ x).lt_iff_lt.1 hyw
  have hj2 : j < k.succ := (L.strictMono_ξ x).lt_iff_lt.1 hwz
  rw [Fin.lt_def] at hj1 hj2
  simp only [Fin.val_castSucc, Fin.val_succ] at hj1 hj2
  omega

/-- **The unique scale in a lacunary tree** ([O+] L2204-L2216): in an `l`-lacunary tree satisfying
the separation assumptions, if `P, P' ∈ T` and the indices `k, k'` satisfy `ξ_{k-1}(x) ∈ ω_l`,
`ξ_k(x) ∈ ω_h` (for `P`) and `ξ_{k'-1}(x) ∈ ω_l'`, `ξ_{k'}(x) ∈ ω_h'` (for `P'`), then `|I| = |I'|`
and `k = k'`: there is at most one scale and at most one index `k`. -/
theorem lacunary_unique_scale (hC : AdmissibleConstants C₁ C₂ C₃) (hρ : ρ.IsStd)
    {𝒯 : MultitileTree ρ} (hT : 𝒯.IsTree C₁ C₂ M) (hlac : 𝒯.IsLacunary C₂)
    (hsep : Separated C₁ C₂ C₃ (𝒯.T : Set (Multitile ρ))) {r : ℝ} (L : Linearization r) (x : ℝ)
    {P P' : Multitile ρ} (hP : P ∈ 𝒯.T) (hP' : P' ∈ 𝒯.T) {k k' : Fin L.K}
    (h1 : L.ξ k.castSucc x ∈ P.ωl ∧ L.ξ k.succ x ∈ P.ωh)
    (h2 : L.ξ k'.castSucc x ∈ P'.ωl ∧ L.ξ k'.succ x ∈ P'.ωh) :
    P.I.length = P'.I.length ∧ k = k' := by
  rcases lt_trichotomy P.I.length P'.I.length with hlt | heq | hgt
  · exact (lacunary_no_smaller_scale hC hρ hT hlac hsep.scales L x hP hP'
      (Multitile.ωu_length_lt_of_I_length_lt (P := P') (P' := P) hlt) h1 k'.castSucc h2.1).elim
  · refine ⟨heq, ?_⟩
    have hωu := ωu_eq_of_I_length_eq_of_tree hC hρ hT hsep.prop2 hP hP' heq
    have hl : P'.ωl = P.ωl := by simp [Multitile.ωl, hωu]
    have hh : P'.ωh = P.ωh := by simp [Multitile.ωh, hωu]
    rw [hl, hh] at h2
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hle : L.ξ k.succ x ≤ L.ξ k'.castSucc x := (L.strictMono_ξ x).monotone (by
        rw [Fin.le_def, Fin.val_succ, Fin.val_castSucc]; exact Fin.lt_def.1 hlt)
      exact absurd (P.lt_of_mem_ωl_of_mem_ωh h2.1 h1.2) (not_lt.2 hle)
    · have hle : L.ξ k'.succ x ≤ L.ξ k.castSucc x := (L.strictMono_ξ x).monotone (by
        rw [Fin.le_def, Fin.val_succ, Fin.val_castSucc]; exact Fin.lt_def.1 hgt)
      exact absurd (P.lt_of_mem_ωl_of_mem_ωh h1.1 h2.2) (not_lt.2 hle)
  · exact (lacunary_no_smaller_scale hC hρ hT hlac hsep.scales L x hP' hP
      (Multitile.ωu_length_lt_of_I_length_lt (P := P) (P' := P') hgt) h2 k.castSucc h1.1).elim

end UniqueScale

section Pointwise

variable {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ C₃ : ℝ} {M : ℤ}

/-- `|⟨f, φ_P⟩| ≤ ene |I|^{1/2}` when `energy(S) ≤ ene` and `P ∈ S` lies in the square
(L2231-L2233: "the energy bound for single multitiles"). -/
theorem norm_coeff_le_of_energy_le {ch : ProfileChoice} {f : ℝ → ℂ}
    (hC : AdmissibleConstants C₁ C₂ C₃) (hρ : ρ.IsStd) {S : Set (Multitile ρ)} {ene : ℝ}
    (hene : 0 ≤ ene) (hen : energy C₁ C₂ M ch f S ≤ ENNReal.ofReal ene) {P : Multitile ρ}
    (hPS : P ∈ S) (hP : P.InSquare M) : ‖P.coeff ch f‖ ≤ ene * √P.I.length := by
  have h := norm_sq_coeff_le_of_energy_le hC hρ hene hen hPS hP
  have h2 := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul (sq_nonneg ene), Real.sqrt_sq hene] at h2

omit [Fact ρ.IsOneOrTwo] in
/-- The product `|⟨f, φ_P⟩| |φ_P(x)|` is at most `ene · Cw · (1 + |x - c(I)|/|I|)^{-N}` when
`|φ_P(x)| ≤ Cw |I|^{-1/2} (1 + |x - c(I)|/|I|)^{-N}`. -/
theorem norm_coeff_mul_wavePacket_le {ch : ProfileChoice} {f : ℝ → ℂ} {Cw : ℝ} {N : ℕ}
    {P : Multitile ρ} {x ene : ℝ} (hene : 0 ≤ ene) (hc : ‖P.coeff ch f‖ ≤ ene * √P.I.length)
    (hw : ‖P.wavePacket ch x‖ ≤
      Cw * (√P.I.length)⁻¹ * (1 + |x - P.I.center| / P.I.length) ^ (-(N : ℤ))) :
    ‖P.coeff ch f * P.wavePacket ch x‖ ≤
      ene * Cw * (1 + |P.I.center - x| / P.I.length) ^ (-(N : ℤ)) := by
  have hI := P.I.length_pos
  have hs : 0 < √P.I.length := Real.sqrt_pos.2 hI
  rw [norm_mul, abs_sub_comm]
  calc ‖P.coeff ch f‖ * ‖P.wavePacket ch x‖
      ≤ (ene * √P.I.length) * (Cw * (√P.I.length)⁻¹ *
        (1 + |x - P.I.center| / P.I.length) ^ (-(N : ℤ))) :=
        mul_le_mul hc hw (norm_nonneg _) (by positivity)
    _ = ene * Cw * (1 + |x - P.I.center| / P.I.length) ^ (-(N : ℤ)) := by
        field_simp

/-- **The weight sum over the multitiles of one scale in a tree**: for `P₀ ∈ T'` ⊂ the tree and
`F = {P ∈ T' : |I| = |I₀|}`, `∑_{P ∈ F} (1 + |c(I) - x|/|I|)^{-2} ≤ 9/2`
(L2242-L2243: "`∑_{P ∈ T : |I| = 2^m} (1 + |x - c(I)|/|I|)^{-N} ≤ C`"). -/
theorem sum_scale_weight_le_nine_halves (hC : AdmissibleConstants C₁ C₂ C₃) (hρ : ρ.IsStd)
    {𝒯 : MultitileTree ρ} (hT : 𝒯.IsTree C₁ C₂ M)
    (hp2 : SeparationProp2 C₁ (𝒯.T : Set (Multitile ρ))) {T' : Finset (Multitile ρ)}
    (hT' : T' ⊆ 𝒯.T) (ℓ : ℝ) (hℓ : 0 < ℓ) (x : ℝ) :
    ∑ P ∈ T'.filter (fun P => P.I.length = ℓ), (1 + |P.I.center - x| / P.I.length) ^
      (-((2 : ℕ) : ℤ)) ≤ 9 / 2 := by
  classical
  have hdisj : ((T'.filter (fun P => P.I.length = ℓ) : Finset (Multitile ρ)) :
      Set (Multitile ρ)).PairwiseDisjoint fun P => P.I.toSet := by
    intro P hP P' hP' hne
    have h1 := Finset.mem_filter.1 (Finset.mem_coe.1 hP)
    have h2 := Finset.mem_filter.1 (Finset.mem_coe.1 hP')
    exact treeobs_disjoint_time hC hρ 𝒯 hT hp2 (hT' h1.1) (hT' h2.1) hne
      (Multitile.ωu_length_eq_of_I_length_eq (h1.2.trans h2.2.symm))
  have h := sum_one_add_abs_zpow_le (T'.filter (fun P => P.I.length = ℓ)) Multitile.I hℓ
    (fun P hP => (Finset.mem_filter.1 hP).2) hdisj (N := 2) le_rfl x (d := 0) le_rfl
    (fun P _ y _ => abs_nonneg _)
  calc ∑ P ∈ T'.filter (fun P => P.I.length = ℓ), (1 + |P.I.center - x| / P.I.length) ^
        (-((2 : ℕ) : ℤ))
      = ∑ P ∈ T'.filter (fun P => P.I.length = ℓ), (1 + |P.I.center - x| / ℓ) ^
        (-((2 : ℕ) : ℤ)) :=
        Finset.sum_congr rfl fun P hP => by rw [(Finset.mem_filter.1 hP).2]
    _ ≤ _ := h
    _ = 9 / 2 := by norm_num

end Pointwise

section LacunaryCase

variable {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ C₃ : ℝ} {M : ℤ}

/-- **The pointwise bound for an `l`-lacunary tree** (L2218-L2243). For `T' ⊂ T` and every `x`,
either `∑_{P ∈ T'} ⟨f, φ_P⟩ φ_P(x) a_P(x) = 0`, or there is `k` with `ξ_{k-1}(x) ∈ ω_l` for some
`P₀ ∈ T'` such that the sum has modulus at most `(9/2) Cw ene |a_k(x)|`, where
`|φ_P(x)| ≤ Cw |I|^{-1/2} (1 + |x - c(I)|/|I|)^{-2}` for all multitiles. -/
theorem treeSum_zero_or_le_of_lacunary {Cw : ℝ}
    (hCw : ∀ (ρ' : Idx) (ch' : ProfileChoice) (P : Multitile ρ') (x : ℝ), ‖P.wavePacket ch' x‖ ≤
      Cw * (√P.I.length)⁻¹ * (1 + |x - P.I.center| / P.I.length) ^ (-((2 : ℕ) : ℤ)))
    (hCw0 : 0 ≤ Cw) (hC : AdmissibleConstants C₁ C₂ C₃) (hρ : ρ.IsStd) {𝒯 : MultitileTree ρ}
    (hT : 𝒯.IsTree C₁ C₂ M) (hlac : 𝒯.IsLacunary C₂)
    (hsep : Separated C₁ C₂ C₃ (𝒯.T : Set (Multitile ρ))) (hsq : ∀ P ∈ 𝒯.T, P.InSquare M)
    {S : Set (Multitile ρ)} (hsub : (𝒯.T : Set (Multitile ρ)) ⊆ S) {ch : ProfileChoice}
    {f : ℝ → ℂ} {ene : ℝ} (hene : 0 ≤ ene) (hen : energy C₁ C₂ M ch f S ≤ ENNReal.ofReal ene)
    {r : ℝ} (L : Linearization r) {T' : Finset (Multitile ρ)} (hT' : T' ⊆ 𝒯.T) (x : ℝ) :
    ∑ P ∈ T', P.coeff ch f * P.wavePacket ch x * P.aP L x = 0 ∨
      ∃ k : Fin L.K, (∃ P₀ ∈ T', L.ξ k.castSucc x ∈ P₀.ωl) ∧
        ‖∑ P ∈ T', P.coeff ch f * P.wavePacket ch x * P.aP L x‖ ≤
          9 / 2 * Cw * ene * ‖L.a k x‖ := by
  classical
  by_cases h : ∃ P₀ ∈ T', ∃ k : Fin L.K, L.ξ k.castSucc x ∈ P₀.ωl ∧ L.ξ k.succ x ∈ P₀.ωh
  · right
    obtain ⟨P₀, hP₀, k, hk⟩ := h
    refine ⟨k, ⟨P₀, hP₀, hk.1⟩, ?_⟩
    have hℓ := P₀.I.length_pos
    -- the bound for each term
    have hterm : ∀ P ∈ T', ‖P.coeff ch f * P.wavePacket ch x * P.aP L x‖ ≤
        if P.I.length = P₀.I.length then
          ene * Cw * ‖L.a k x‖ * (1 + |P.I.center - x| / P.I.length) ^ (-((2 : ℕ) : ℤ))
        else 0 := by
      intro P hP
      by_cases hex : ∃ k' : Fin L.K, L.ξ k'.castSucc x ∈ P.ωl ∧ L.ξ k'.succ x ∈ P.ωh
      · obtain ⟨k', hk'⟩ := hex
        obtain ⟨hlen, hkk⟩ := lacunary_unique_scale hC hρ hT hlac hsep L x (hT' hP₀) (hT' hP)
          hk hk'
        subst hkk
        rw [P.aP_eq_of_mem L x hk'.1 hk'.2, norm_mul]
        split_ifs with hl
        swap
        · exact absurd hlen.symm hl
        have h1 := norm_coeff_mul_wavePacket_le (ch := ch) (f := f) (P := P) (x := x) hene
          (norm_coeff_le_of_energy_le hC hρ hene hen (hsub (Finset.mem_coe.2 (hT' hP)))
            (hsq P (hT' hP))) (hCw ρ ch P x)
        calc ‖P.coeff ch f * P.wavePacket ch x‖ * ‖L.a k x‖
            ≤ (ene * Cw * (1 + |P.I.center - x| / P.I.length) ^ (-((2 : ℕ) : ℤ))) * ‖L.a k x‖ :=
              mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
          _ = _ := by ring
      · have h0 : P.aP L x = 0 := P.aP_eq_zero_of_not L x fun k' hk' => hex ⟨k', hk'⟩
        rw [h0]
        simp only [mul_zero, norm_zero]
        have hw : 0 ≤ (1 + |P.I.center - x| / P.I.length) ^ (-((2 : ℕ) : ℤ)) := by
          have := P.I.length_pos
          positivity
        split_ifs
        · exact mul_nonneg (by positivity) hw
        · exact le_rfl
    have hsum := sum_scale_weight_le_nine_halves hC hρ hT hsep.prop2 hT' P₀.I.length hℓ x
    have hnn : 0 ≤ ene * Cw * ‖L.a k x‖ := by positivity
    calc ‖∑ P ∈ T', P.coeff ch f * P.wavePacket ch x * P.aP L x‖
        ≤ ∑ P ∈ T', ‖P.coeff ch f * P.wavePacket ch x * P.aP L x‖ := norm_sum_le _ _
      _ ≤ ∑ P ∈ T', if P.I.length = P₀.I.length then
          ene * Cw * ‖L.a k x‖ * (1 + |P.I.center - x| / P.I.length) ^ (-((2 : ℕ) : ℤ))
          else 0 := Finset.sum_le_sum hterm
      _ = ∑ P ∈ T'.filter (fun P => P.I.length = P₀.I.length),
          ene * Cw * ‖L.a k x‖ * (1 + |P.I.center - x| / P.I.length) ^ (-((2 : ℕ) : ℤ)) :=
          (Finset.sum_filter _ _).symm
      _ = ene * Cw * ‖L.a k x‖ * ∑ P ∈ T'.filter (fun P => P.I.length = P₀.I.length),
          (1 + |P.I.center - x| / P.I.length) ^ (-((2 : ℕ) : ℤ)) := (Finset.mul_sum _ _ _).symm
      _ ≤ ene * Cw * ‖L.a k x‖ * (9 / 2) := mul_le_mul_of_nonneg_left hsum hnn
      _ = 9 / 2 * Cw * ene * ‖L.a k x‖ := by ring
  · left
    refine Finset.sum_eq_zero fun P hP => ?_
    have h0 : P.aP L x = 0 := P.aP_eq_zero_of_not L x fun k hk => h ⟨P, hP, k, hk⟩
    rw [h0, mul_zero]

end LacunaryCase

section LacunaryIntegral

/-- `‖a‖ₑ ≤ 1` when `‖a‖^{r'} ≤ 1`, `r' > 0`. -/
theorem enorm_le_one_of_rpow_le_one {a : ℂ} {p : ℝ} (hp : 0 < p) (h : ‖a‖ ^ p ≤ 1) :
    ‖a‖ₑ ≤ 1 := by
  rw [← ofReal_norm, ← ENNReal.ofReal_one]
  refine ENNReal.ofReal_le_ofReal ?_
  by_contra hcon
  rw [not_le] at hcon
  exact absurd h (not_le.2 (Real.one_lt_rpow hcon hp))

/-- **`treeestimatelargeintervals`** ([O+] L2201-L2252). There is a constant `K`
(depending on `r` and `q ≥ r'` only) such that for every `l`-lacunary tree `T ⊂ S` of multitiles
in the square `[-2^M, 2^M]²` with the separation assumptions, `energy(S) ≤ ene`,
`density(S) ≤ den`, and every `J ∈ 𝒥`,
`∫_J |∑_{P ∈ T : |I| ≥ C''|J|} ⟨f, φ_P⟩ φ_P a_P 1_E|^q ≤ K ene^q den^{r'} |J|`. -/
theorem lacunary_case {r q : ℝ} (hr : 1 < r) (hq : Real.conjExponent r ≤ q) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ C₃ : ℝ} {M : ℤ},
      AdmissibleConstants C₁ C₂ C₃ → ρ.IsStd → ∀ (ch : ProfileChoice) (f : ℝ → ℂ) {E : Set ℝ},
      MeasurableSet E → ∀ (L : Linearization r) {S : Set (Multitile ρ)} {ene den : ℝ},
      0 ≤ ene → 0 ≤ den → energy C₁ C₂ M ch f S ≤ ENNReal.ofReal ene →
      density C₁ C₂ M L E S ≤ ENNReal.ofReal den → ∀ (𝒯 : MultitileTree ρ),
      𝒯.IsTree C₁ C₂ M → (∀ P ∈ 𝒯.T, P.InSquare M) → (𝒯.T : Set (Multitile ρ)) ⊆ S →
      𝒯.IsLacunary C₂ → Separated C₁ C₂ C₃ (𝒯.T : Set (Multitile ρ)) → ∀ {J : Dyadic},
      𝒯.IsMaxAvoiding J →
        ∫⁻ x in J.toSet, ‖treeSum ch f L E (𝒯.T.filter fun P => Cpp C₁ C₂ * J.length ≤
            P.I.length) x‖ₑ ^ q ≤
          ENNReal.ofReal (K * ene ^ q * den ^ Real.conjExponent r * J.length) := by
  classical
  obtain ⟨Cw, hCw0, hCw⟩ := Multitile.exists_norm_wavePacket_le 2
  have hr' : 0 < Real.conjExponent r := by
    unfold Real.conjExponent
    exact div_pos (by linarith) (by linarith)
  have hq0 : 0 < q := lt_of_lt_of_le hr' hq
  refine ⟨(9 / 2 * Cw) ^ q * (4 * (11 / 2) ^ 4), by positivity, ?_⟩
  intro ρ _ C₁ C₂ C₃ M hC hρ ch f E hE L S ene den hene hden hen hde 𝒯 hT hsq hsub hlac hsep J hJ
  set K₁ : ℝ := 9 / 2 * Cw with hK₁
  have hK₁0 : 0 ≤ K₁ := by positivity
  set T' := 𝒯.T.filter fun P => Cpp C₁ C₂ * J.length ≤ P.I.length with hT'def
  have hT' : T' ⊆ 𝒯.T := Finset.filter_subset _ _
  have hpt : ∀ x, ‖treeSum ch f L E T' x‖ₑ ^ q ≤ ENNReal.ofReal ((K₁ * ene) ^ q) *
      E.indicator (L.tailSum (𝒯.OmegaJ (Cpp C₁ C₂) J)) x := by
    intro x
    by_cases hx : x ∈ E
    · rw [Set.indicator_of_mem hx]
      have hts : treeSum ch f L E T' x =
          ∑ P ∈ T', P.coeff ch f * P.wavePacket ch x * P.aP L x := by
        unfold treeSum
        simp [Set.indicator_of_mem hx]
      rw [hts]
      rcases treeSum_zero_or_le_of_lacunary hCw hCw0 hC hρ hT hlac hsep hsq hsub hene hen L hT' x
        with h0 | ⟨k, ⟨P₀, hP₀, hξ⟩, hle⟩
      · rw [h0, enorm_zero, ENNReal.zero_rpow_of_pos hq0]
        exact zero_le
      · have h1 : ‖∑ P ∈ T', P.coeff ch f * P.wavePacket ch x * P.aP L x‖ₑ ≤
            ENNReal.ofReal (K₁ * ene) * ‖L.a k x‖ₑ := by
          rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (by positivity)]
          exact ENNReal.ofReal_le_ofReal (by rw [hK₁]; exact hle)
        have hak : ‖L.a k x‖ₑ ≤ 1 :=
          enorm_le_one_of_rpow_le_one hr' (L.norm_rpow_le_one k x)
        have hmem : L.ξ k.castSucc x ∈ 𝒯.OmegaJ (Cpp C₁ C₂) J :=
          ⟨P₀, (Finset.mem_filter.1 hP₀).1, (Finset.mem_filter.1 hP₀).2, hξ⟩
        have h2 : ‖L.a k x‖ₑ ^ Real.conjExponent r ≤
            L.tailSum (𝒯.OmegaJ (Cpp C₁ C₂) J) x := by
          unfold Linearization.tailSum
          refine le_trans ?_ (Finset.single_le_sum (f := fun k : Fin L.K => ‖L.a k x‖ₑ ^
            Real.conjExponent r * (𝒯.OmegaJ (Cpp C₁ C₂) J).indicator (fun _ => (1 : ℝ≥0∞))
              (L.ξ k.castSucc x)) (fun _ _ => zero_le) (Finset.mem_univ k))
          simp [Set.indicator_of_mem hmem]
        calc ‖∑ P ∈ T', P.coeff ch f * P.wavePacket ch x * P.aP L x‖ₑ ^ q
            ≤ (ENNReal.ofReal (K₁ * ene) * ‖L.a k x‖ₑ) ^ q := by gcongr
          _ = ENNReal.ofReal (K₁ * ene) ^ q * ‖L.a k x‖ₑ ^ q :=
              ENNReal.mul_rpow_of_nonneg _ _ hq0.le
          _ ≤ ENNReal.ofReal (K₁ * ene) ^ q * ‖L.a k x‖ₑ ^ Real.conjExponent r := by
              have h := ENNReal.rpow_le_rpow_of_exponent_ge hak hq
              gcongr
          _ ≤ ENNReal.ofReal (K₁ * ene) ^ q *
              L.tailSum (𝒯.OmegaJ (Cpp C₁ C₂) J) x := by gcongr
          _ = ENNReal.ofReal ((K₁ * ene) ^ q) *
              L.tailSum (𝒯.OmegaJ (Cpp C₁ C₂) J) x := by
              rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hq0.le]
    · rw [Set.indicator_of_notMem hx]
      have : treeSum ch f L E T' x = 0 := by
        unfold treeSum
        simp [Set.indicator_of_notMem hx]
      rw [this, enorm_zero, ENNReal.zero_rpow_of_pos hq0]
      exact zero_le
  have hU := usedensitybound hC hρ hr L hE hde hT hsq hsub (Or.inl hlac) hJ
  calc ∫⁻ x in J.toSet, ‖treeSum ch f L E T' x‖ₑ ^ q
      ≤ ∫⁻ x in J.toSet, ENNReal.ofReal ((K₁ * ene) ^ q) *
        E.indicator (L.tailSum (𝒯.OmegaJ (Cpp C₁ C₂) J)) x := lintegral_mono hpt
    _ = ENNReal.ofReal ((K₁ * ene) ^ q) * ∫⁻ x in J.toSet,
        E.indicator (L.tailSum (𝒯.OmegaJ (Cpp C₁ C₂) J)) x :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal ((K₁ * ene) ^ q) * ∫⁻ x in J.toSet ∩ E,
        L.tailSum (𝒯.OmegaJ (Cpp C₁ C₂) J) x := by
        rw [setLIntegral_indicator hE, Set.inter_comm]
    _ ≤ ENNReal.ofReal ((K₁ * ene) ^ q) * (ENNReal.ofReal (4 * (11 / 2) ^ 4) *
        ENNReal.ofReal den ^ Real.conjExponent r * ENNReal.ofReal J.length) := by
        gcongr
    _ = ENNReal.ofReal (K₁ ^ q * (4 * (11 / 2) ^ 4) * ene ^ q * den ^ Real.conjExponent r *
        J.length) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hden hr'.le, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [Real.mul_rpow hK₁0 hene]
        ring

/-- **The lacunary case summed over `J ∈ 𝒥` meeting `16 I_T`** (L2250-L2252): for a finite set `𝒥s`
of elements of `𝒥` meeting `16 I_T`,
`∑_{J ∈ 𝒥s} ∫_J |∑_{P ∈ T : |I| ≥ C''|J|} ⟨f, φ_P⟩ φ_P a_P 1_E|^q ≤ 48 K ene^q den^{r'} |I_T|`,
i.e. (`q ≥ r'`) `(∑_J ‖·‖_{L^q(J)}^q)^{1/q} ≲ ene den^{r'/q} |I_T|^{1/q}`. -/
theorem lacunary_case_sum {r q : ℝ} (hr : 1 < r) (hq : Real.conjExponent r ≤ q) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ C₃ : ℝ} {M : ℤ},
      AdmissibleConstants C₁ C₂ C₃ → ρ.IsStd → ∀ (ch : ProfileChoice) (f : ℝ → ℂ) {E : Set ℝ},
      MeasurableSet E → ∀ (L : Linearization r) {S : Set (Multitile ρ)} {ene den : ℝ},
      0 ≤ ene → 0 ≤ den → energy C₁ C₂ M ch f S ≤ ENNReal.ofReal ene →
      density C₁ C₂ M L E S ≤ ENNReal.ofReal den → ∀ (𝒯 : MultitileTree ρ),
      𝒯.IsTree C₁ C₂ M → (∀ P ∈ 𝒯.T, P.InSquare M) → (𝒯.T : Set (Multitile ρ)) ⊆ S →
      𝒯.IsLacunary C₂ → Separated C₁ C₂ C₃ (𝒯.T : Set (Multitile ρ)) → 𝒯.T.Nonempty →
      ∀ (𝒥s : Finset Dyadic), (∀ J ∈ 𝒥s, 𝒯.IsMaxAvoiding J ∧
        (J.toSet ∩ 𝒯.I.dilate 16).Nonempty) →
        ∑ J ∈ 𝒥s, ∫⁻ x in J.toSet, ‖treeSum ch f L E (𝒯.T.filter fun P => Cpp C₁ C₂ * J.length ≤
            P.I.length) x‖ₑ ^ q ≤
          ENNReal.ofReal (K * ene ^ q * den ^ Real.conjExponent r * (48 * 𝒯.I.length)) := by
  obtain ⟨K, hK0, hK⟩ := lacunary_case (r := r) (q := q) hr hq
  have hr' : 0 < Real.conjExponent r := by
    unfold Real.conjExponent
    exact div_pos (by linarith) (by linarith)
  refine ⟨K, hK0, ?_⟩
  intro ρ _ C₁ C₂ C₃ M hC hρ ch f E hE L S ene den hene hden hen hde 𝒯 hT hsq hsub hlac hsep hne
    𝒥s h𝒥
  calc ∑ J ∈ 𝒥s, ∫⁻ x in J.toSet, ‖treeSum ch f L E (𝒯.T.filter fun P => Cpp C₁ C₂ * J.length ≤
          P.I.length) x‖ₑ ^ q
      ≤ ∑ J ∈ 𝒥s, ENNReal.ofReal (K * ene ^ q * den ^ Real.conjExponent r * J.length) :=
        Finset.sum_le_sum fun J hJ =>
          hK hC hρ ch f hE L hene hden hen hde 𝒯 hT hsq hsub hlac hsep (h𝒥 J hJ).1
    _ = ENNReal.ofReal (∑ J ∈ 𝒥s, K * ene ^ q * den ^ Real.conjExponent r * J.length) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun J _ => by have := J.length_pos; positivity)]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (MultitileTree.sum_length_le hne hT.time 𝒥s h𝒥)
          (by positivity)

end LacunaryIntegral

end PrimeCarleson.Proof.Oplus
