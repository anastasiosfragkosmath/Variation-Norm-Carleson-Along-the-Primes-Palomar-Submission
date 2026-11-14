module

public import PrimeCarleson.Proof.Oplus.TreeSmall.Lacunary

/-!
# The single-tile bound on `J` ([O+] L2093-L2117)

Source: [O+] `treeestimatesmallintervals`, L2093–L2117: for a multitile `P` with `I ⊄ 3J` and
`q ≥ r'`,
`‖⟨f, φ_P⟩ φ_P a_P 1_E‖_{L^q(J)} ≲ ene den^{r'/q} |I|^{1/q} (1 + dist(I, J)/|I|)^{-(N-4)}`.

The proof (as in the source): the energy bound for the one-tile `l`-overlapping tree `{P}` gives
`|⟨f, φ_P⟩| ≤ ene |I|^{1/2}` (`norm_coeff_le_of_energy_le`), the wave packet bound gives
`|φ_P(x)| ≲ |I|^{-1/2} (1 + |x - c(I)|/|I|)^{-N}`, and the density bound for the one-multitile tree
`({P}, I, c(ω_l))`, whose `ω_T` contains `ω_l` (a single tree suffices, since `C₂ ≥ 2` makes
`|ω_T| = (C₂ - 1)|ω_u| ≥ |ω_l|`; the source uses about `1/(C₂ - 1)` trees), gives
`∫_{J ∩ E} |a_P|^q ≤ ∫_{J ∩ E} ∑_{ξ_{k-1} ∈ ω_l} |a_k|^{r'} ≲ den^{r'} |I| (1 + dist(I, J)/|I|)^4`,
because `I ⊄ 3J` gives `1 + |x - c(I)|/|I| ≤ (5/2)(1 + dist(I, J)/|I|)` for `x ∈ J`
(`Dyadic.one_add_abs_sub_center_div_le`). The wave packet decay is only used through the
pointwise bound for `x ∈ J`, `|x - c(I)| ≥ dist(I, J)`.

Only the following is used about the multitile: `P ∈ S` lies in the square `[-2^M, 2^M]²` (so
that `{P}` is a tree: `exists_singleton_tree` of `EnergyIncrement/Basic.lean`) and `I ⊄ 3J`;
in particular no hypothesis `|I| ≤ C''|J|`, no separation assumption, no tree `T ∋ P`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

section Measurability

variable {ρ : Idx} {r : ℝ}

/-- The tree sum is measurable (for measurable `E`). -/
theorem measurable_treeSum (ch : ProfileChoice) (f : ℝ → ℂ) (L : Linearization r) {E : Set ℝ}
    (hE : MeasurableSet E) (T : Finset (Multitile ρ)) : Measurable (treeSum ch f L E T) := by
  unfold treeSum
  refine Finset.measurable_sum _ fun P _ => ?_
  have h1 : Measurable (P.wavePacket ch) :=
    (ch.isProfile.continuous_wavePacketOf P.I P.ωu).measurable
  exact ((measurable_const.mul h1).mul (P.measurable_aP L)).mul (measurable_const.indicator hE)

end Measurability

section SingleTile

variable {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ C₃ : ℝ} {M : ℤ}

/-- **The singleton tree of `P`** with top interval `I` and top frequency `c(ω_l)`: it is a tree
(for `P` in the square `[-2^M, 2^M]²`) and `ω_l ⊂ ω_T` (as `C₂ ≥ 2`; `C₂ ∈ ℕ`, `C₂ > 1`). -/
theorem singleton_tree_ωl (hC : AdmissibleConstants C₁ C₂ C₃) (hρ : ρ.IsStd) {P : Multitile ρ}
    (hP : P.InSquare M) :
    (MultitileTree.single P P.I (ρ.ωlDyadic P.ωu).center).IsTree C₁ C₂ M ∧
      P.ωl ⊆ (MultitileTree.single P P.I (ρ.ωlDyadic P.ωu).center).ωT C₂ := by
  have hC₂ : 1 < C₂ := lt_of_le_of_lt hC.one_le hC.lt₁
  obtain ⟨k₂, hk₂⟩ := hC.nat_C₂
  have hC₂2 : 2 ≤ C₂ := by
    have : 1 < k₂ := by exact_mod_cast (hk₂ ▸ hC₂)
    rw [hk₂]; exact_mod_cast this
  have hL := P.ωu.length_pos
  have hI := P.I.length_pos
  have harea := P.length_I_mul_length_ωu
  set ξ : ℝ := (ρ.ωlDyadic P.ωu).center with hξ
  have hdil : P.ωlDil C₂ = Ico (ξ - C₂ * P.ωu.length / 2) (ξ + C₂ * P.ωu.length / 2) := by
    unfold Multitile.ωlDil Dyadic.dilate
    rw [Idx.length_ωlDyadic]
  have h1 : (C₂ - 1) / (4 * P.I.length) = (C₂ - 1) * P.ωu.length / 2 := by
    field_simp
    linarith
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · exact Dyadic.toSet_subset_Ico_of_subset_Icc hP.1
  · exact Multitile.center_ωlDyadic_mem_Xtop hρ (by linarith [hC.one_le, hC.lt₁, hC.lt₂]) hP
  · intro Q hQ
    rw [MultitileTree.single_T, Finset.mem_singleton] at hQ
    rw [hQ]
    exact subset_rfl
  · intro Q hQ
    rw [MultitileTree.single_T, Finset.mem_singleton] at hQ
    subst hQ
    have hsub : Q.ωlDil C₂ ⊆ Q.ωm C₂ := fun x hx => subset_convexHull ℝ _ (Or.inr hx)
    refine Set.Subset.trans ?_ hsub
    rw [hdil]
    refine Ico_subset_Ico ?_ ?_
    · change ξ - C₂ * Q.ωu.length / 2 ≤ ξ - (C₂ - 1) / (4 * Q.I.length)
      rw [h1]; nlinarith
    · change ξ + (C₂ - 1) / (4 * Q.I.length) ≤ ξ + C₂ * Q.ωu.length / 2
      rw [h1]; nlinarith
  · intro y hy
    rw [Multitile.mem_ωl_iff] at hy
    have hcl : ξ = P.ωu.center - ((ρ.m : ℝ) + 1) * P.ωu.length := by
      rw [hξ, Idx.center_ωlDyadic]
    change ξ - (C₂ - 1) / (4 * P.I.length) ≤ y ∧ y < ξ + (C₂ - 1) / (4 * P.I.length)
    rw [h1]
    constructor <;> nlinarith [hy.1, hy.2]

end SingleTile

section SingleTileBound

variable {ρ : Idx} [Fact ρ.IsOneOrTwo]

omit [Fact ρ.IsOneOrTwo] in
open Classical in
/-- `|a_P(x)|^q ≤ ∑_{k : ξ_{k-1}(x) ∈ ω_l} |a_k(x)|^{r'}` for `q ≥ r'` (L2102-L2108: "`|a_P(x)|^{r'}
≤ ∑_{k : ξ_{k-1}(x) ∈ ω_l} |a_k(x)|^{r'}`, `a_P = a_k` for the unique `k`, and `|a_P| ≤ 1`"). -/
theorem Multitile.enorm_aP_rpow_le_tailSum {r q : ℝ} (hr : 1 < r)
    (hq : Real.conjExponent r ≤ q) (L : Linearization r) (P : Multitile ρ) (x : ℝ) :
    ‖P.aP L x‖ₑ ^ q ≤ L.tailSum P.ωl x := by
  have hr' : 0 < Real.conjExponent r := by
    unfold Real.conjExponent
    exact div_pos (by linarith) (by linarith)
  have hq0 : 0 < q := lt_of_lt_of_le hr' hq
  by_cases hex : ∃ k : Fin L.K, L.ξ k.castSucc x ∈ P.ωl ∧ L.ξ k.succ x ∈ P.ωh
  · obtain ⟨k, hk⟩ := hex
    rw [P.aP_eq_of_mem L x hk.1 hk.2]
    have hak : ‖L.a k x‖ₑ ≤ 1 := enorm_le_one_of_rpow_le_one hr' (L.norm_rpow_le_one k x)
    calc ‖L.a k x‖ₑ ^ q ≤ ‖L.a k x‖ₑ ^ Real.conjExponent r :=
          ENNReal.rpow_le_rpow_of_exponent_ge hak hq
      _ ≤ L.tailSum P.ωl x := by
          unfold Linearization.tailSum
          refine le_trans ?_ (Finset.single_le_sum (f := fun k : Fin L.K => ‖L.a k x‖ₑ ^
            Real.conjExponent r * P.ωl.indicator (fun _ => (1 : ℝ≥0∞)) (L.ξ k.castSucc x))
            (fun _ _ => zero_le) (Finset.mem_univ k))
          simp [Set.indicator_of_mem hk.1]
  · rw [P.aP_eq_zero_of_not L x fun k hk => hex ⟨k, hk⟩, enorm_zero,
      ENNReal.zero_rpow_of_pos hq0]
    exact zero_le

variable {C₁ C₂ C₃ : ℝ} {M : ℤ}

/-- **`treeestimatesmallintervals`** ([O+] L2093-L2117). For `q ≥ r'` and
`N ∈ ℕ` there is a constant `K` such that for every multitile `P ∈ S` in the square
`[-2^M, 2^M]²` with `I ⊄ 3J`, `energy(S) ≤ ene` and `density(S) ≤ den`:
`‖⟨f, φ_P⟩ φ_P a_P 1_E‖_{L^q(J)} ≤ K ene den^{r'/q} |I|^{1/q} (1 + dist(I, J)/|I|)^{-(N-4)}`. -/
theorem single_tile_bound {r q : ℝ} (hr : 1 < r) (hq : Real.conjExponent r ≤ q) (N : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ C₃ : ℝ} {M : ℤ},
      AdmissibleConstants C₁ C₂ C₃ → ρ.IsStd → ∀ (ch : ProfileChoice) (f : ℝ → ℂ) {E : Set ℝ},
      MeasurableSet E → ∀ (L : Linearization r) {S : Set (Multitile ρ)} {ene den : ℝ},
      0 ≤ ene → 0 ≤ den → energy C₁ C₂ M ch f S ≤ ENNReal.ofReal ene →
      density C₁ C₂ M L E S ≤ ENNReal.ofReal den → ∀ {P : Multitile ρ}, P ∈ S →
      P.InSquare M → ∀ {J : Dyadic}, ¬ P.I.toSet ⊆ J.dilate 3 →
        eLpNorm (treeSum ch f L E {P}) (ENNReal.ofReal q) (volume.restrict J.toSet) ≤
          ENNReal.ofReal (K * ene * den ^ (Real.conjExponent r / q) * P.I.length ^ (1 / q) *
            (1 + P.I.dist J / P.I.length) ^ (-((N : ℤ) - 4))) := by
  classical
  obtain ⟨Cw, hCw0, hCw⟩ := Multitile.exists_norm_wavePacket_le N
  have hr' : 0 < Real.conjExponent r := by
    unfold Real.conjExponent
    exact div_pos (by linarith) (by linarith)
  have hr'1 : 1 < Real.conjExponent r := by
    unfold Real.conjExponent
    rw [lt_div_iff₀ (by linarith)]
    linarith
  have hq1 : 1 ≤ q := (hr'1.trans_le hq).le
  have hq0 : 0 < q := by linarith
  refine ⟨Cw * (5 / 2) ^ 4, by positivity, ?_⟩
  intro ρ _ C₁ C₂ C₃ M hC hρ ch f E hE L S ene den hene hden hen hde P hPS hPsq J hJ
  have hI := P.I.length_pos
  set A : ℝ := 1 + P.I.dist J / P.I.length with hA
  have hA1 : 1 ≤ A := by
    have : 0 ≤ P.I.dist J / P.I.length := div_nonneg (P.I.dist_nonneg J) hI.le
    linarith
  have hApos : 0 < A := by linarith
  set e₁ : ℝ := ene * Cw * A ^ (-(N : ℤ)) with he₁
  have he₁0 : 0 ≤ e₁ := by positivity
  clear_value e₁
  have hc := norm_coeff_le_of_energy_le hC hρ hene hen hPS hPsq
  -- the pointwise bound on `J`
  have hpt : ∀ x ∈ J.toSet, ‖treeSum ch f L E {P} x‖ₑ ^ q ≤ ENNReal.ofReal e₁ ^ q *
      E.indicator (L.tailSum P.ωl) x := by
    intro x hxJ
    by_cases hx : x ∈ E
    · rw [Set.indicator_of_mem hx]
      have hts : treeSum ch f L E {P} x = P.coeff ch f * P.wavePacket ch x * P.aP L x := by
        unfold treeSum
        simp [Set.indicator_of_mem hx]
      rw [hts]
      have h1 := norm_coeff_mul_wavePacket_le (ch := ch) (f := f) (P := P) (x := x) hene hc
        (hCw ρ ch P x)
      have h2 : (1 + |P.I.center - x| / P.I.length) ^ (-(N : ℤ)) ≤ A ^ (-(N : ℤ)) := by
        have hxA := Dyadic.one_add_dist_div_le (I := P.I) hxJ
        rw [abs_sub_comm P.I.center x, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
        exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hApos.le hxA N)
      have h3 : ‖P.coeff ch f * P.wavePacket ch x * P.aP L x‖ ≤ e₁ * ‖P.aP L x‖ := by
        rw [norm_mul]
        refine mul_le_mul_of_nonneg_right (h1.trans ?_) (norm_nonneg _)
        rw [he₁]
        exact mul_le_mul_of_nonneg_left h2 (by positivity)
      have h4 : ‖P.coeff ch f * P.wavePacket ch x * P.aP L x‖ₑ ≤
          ENNReal.ofReal e₁ * ‖P.aP L x‖ₑ := by
        rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul he₁0]
        exact ENNReal.ofReal_le_ofReal h3
      calc ‖P.coeff ch f * P.wavePacket ch x * P.aP L x‖ₑ ^ q
          ≤ (ENNReal.ofReal e₁ * ‖P.aP L x‖ₑ) ^ q := by gcongr
        _ = ENNReal.ofReal e₁ ^ q * ‖P.aP L x‖ₑ ^ q := ENNReal.mul_rpow_of_nonneg _ _ hq0.le
        _ ≤ ENNReal.ofReal e₁ ^ q * L.tailSum P.ωl x := by
            gcongr
            exact Multitile.enorm_aP_rpow_le_tailSum hr hq L P x
    · rw [Set.indicator_of_notMem hx]
      have : treeSum ch f L E {P} x = 0 := by
        unfold treeSum
        simp [Set.indicator_of_notMem hx]
      rw [this, enorm_zero, ENNReal.zero_rpow_of_pos hq0]
      exact zero_le
  -- the density bound for the singleton tree
  obtain ⟨hT', hΩ'⟩ := singleton_tree_ωl hC hρ hPsq
  have hdens := lintegral_tailSum_le_of_weight hr L hE hde hT' (Finset.singleton_nonempty P)
    (by rw [MultitileTree.single_T, Finset.coe_singleton, Set.singleton_subset_iff]; exact hPS)
    hΩ' (J := J) (B := 5 / 2 * A) (fun x hx => Dyadic.one_add_abs_sub_center_div_le hx hJ)
  have hint : ∫⁻ x in J.toSet, ‖treeSum ch f L E {P} x‖ₑ ^ q ≤ ENNReal.ofReal e₁ ^ q *
      (ENNReal.ofReal ((5 / 2 * A) ^ 4) * (ENNReal.ofReal den ^ Real.conjExponent r *
        ENNReal.ofReal P.I.length)) := by
    calc ∫⁻ x in J.toSet, ‖treeSum ch f L E {P} x‖ₑ ^ q
        ≤ ∫⁻ x in J.toSet, ENNReal.ofReal e₁ ^ q * E.indicator (L.tailSum P.ωl) x :=
          setLIntegral_mono' J.measurableSet_toSet hpt
      _ = ENNReal.ofReal e₁ ^ q * ∫⁻ x in J.toSet, E.indicator (L.tailSum P.ωl) x :=
          lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hq0.le ENNReal.ofReal_ne_top)
      _ = ENNReal.ofReal e₁ ^ q * ∫⁻ x in J.toSet ∩ E, L.tailSum P.ωl x := by
          rw [setLIntegral_indicator hE, Set.inter_comm]
      _ ≤ _ := by
          gcongr
          exact hdens
  -- assemble
  have hmeas : AEStronglyMeasurable (treeSum ch f L E {P}) (volume.restrict J.toSet) :=
    (measurable_treeSum ch f L hE {P}).aestronglyMeasurable
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hq0).ne' ENNReal.ofReal_ne_top
    hmeas, ENNReal.toReal_ofReal hq0.le]
  have hq' : 0 ≤ 1 / q := by positivity
  have h1 := ENNReal.rpow_le_rpow hint hq'
  refine h1.trans ?_
  have hX : (1 : ℝ) ≤ (5 / 2 * A) ^ 4 := one_le_pow₀ (by linarith)
  have hX0 : (0 : ℝ) ≤ (5 / 2 * A) ^ 4 := by positivity
  have hD : (0 : ℝ) ≤ den ^ (Real.conjExponent r / q) := by positivity
  have hIq : (0 : ℝ) ≤ P.I.length ^ (1 / q) := by positivity
  have h2 : (ENNReal.ofReal e₁ ^ q * (ENNReal.ofReal ((5 / 2 * A) ^ 4) *
      (ENNReal.ofReal den ^ Real.conjExponent r * ENNReal.ofReal P.I.length))) ^ (1 / q) =
      ENNReal.ofReal (e₁ * (((5 / 2 * A) ^ 4) ^ (1 / q) * (den ^ (Real.conjExponent r / q) *
        P.I.length ^ (1 / q)))) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ hq', ENNReal.mul_rpow_of_nonneg _ _ hq',
      ENNReal.mul_rpow_of_nonneg _ _ hq', ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
      mul_one_div_cancel hq0.ne', ENNReal.rpow_one, mul_one_div,
      ENNReal.ofReal_mul he₁0, ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul hD, ENNReal.ofReal_rpow_of_nonneg hX0 hq',
      ENNReal.ofReal_rpow_of_nonneg hden (by positivity),
      ENNReal.ofReal_rpow_of_nonneg hI.le hq']
  rw [h2]
  refine ENNReal.ofReal_le_ofReal ?_
  have hAz : A ^ (-(N : ℤ)) * A ^ (4 : ℕ) = A ^ (-((N : ℤ) - 4)) := by
    rw [← zpow_natCast, ← zpow_add₀ hApos.ne']
    congr 1
    push_cast
    ring
  have hroot : ((5 / 2 * A) ^ 4) ^ (1 / q) ≤ (5 / 2 * A) ^ 4 := by
    calc ((5 / 2 * A) ^ 4) ^ (1 / q) ≤ ((5 / 2 * A) ^ 4) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hX (by rw [div_le_one hq0]; exact hq1)
      _ = _ := Real.rpow_one _
  have hR : 0 ≤ den ^ (Real.conjExponent r / q) * P.I.length ^ (1 / q) := mul_nonneg hD hIq
  calc e₁ * (((5 / 2 * A) ^ 4) ^ (1 / q) * (den ^ (Real.conjExponent r / q) *
        P.I.length ^ (1 / q)))
      ≤ e₁ * ((5 / 2 * A) ^ 4 * (den ^ (Real.conjExponent r / q) * P.I.length ^ (1 / q))) := by
        gcongr
    _ = Cw * (5 / 2) ^ 4 * ene * den ^ (Real.conjExponent r / q) * P.I.length ^ (1 / q) *
        (A ^ (-(N : ℤ)) * A ^ (4 : ℕ)) := by
        rw [he₁]; ring
    _ = _ := by rw [hAz]

end SingleTileBound

end PrimeCarleson.Proof.Oplus
