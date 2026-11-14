module

public import PrimeCarleson.Proof.Oplus.TreeLarge.Blocks
public import PrimeCarleson.Proof.Oplus.TreeLarge.LocalMax

/-!
# The large-interval estimate for an `l`-overlapping tree, one interval `J` ([O+] L2255-L2398)

Source: [O+] `treeestimatelargeintervals`, the overlapping case and the integration over `J`
(L2255-L2398). For an `l`-overlapping tree satisfying
(jconsolidation), `J ∈ 𝒥` and `q ≥ r'`:

* `enorm_treeSum_le`: the pointwise Hölder bound (csvar) in `ℝ≥0∞`:
  `|∑_{P : |I| ≥ C''|J|} ⟨f, φ_P⟩ φ_P a_P 1_E (x)| ≤ τ_J(x)^{1/r'} (∑_k |block_k(x)|^r)^{1/r}` with
  `τ_J(x) = ∑_{k : ξ_{k-1}(x) ∈ Ω_J} |a_k(x)|^{r'}`;
* `overlapping_per_J` (integration over `J`): for `κ` as in the local maximal bound,
  `∫_J |∑_{P : |I| ≥ C''|J|} ⟨f, φ_P⟩ φ_P a_P 1_E|^q ≤ κ^q · 4 (11/2)^4 den^{r'} ∫_J (M W)^q`, where
  `W(y) = V^r_ℓ(ψ_ℓ * g (y))`: by `enorm_treeSum_le`, `variation_in_scale_parameter` and the local
  maximal bound the integrand is at most `τ_J(x) κ^q M[W](x')^q` for every `x' ∈ J`; integrating in
  `x'` and then in `x` and using `usedensitybound` for `∫_{J ∩ E} τ_J`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal SchwartzMap

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

open PrimeCarleson PrimeCarleson.Proof.Common PrimeCarleson.Proof.Goal0

section PerJ

variable {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ C₃ : ℝ} {M : ℤ}

open Classical in
omit [Fact ρ.IsOneOrTwo] in
/-- **The pointwise Hölder bound (csvar) in `ℝ≥0∞`** (L2258-L2274), for `x ∈ E`. -/
theorem enorm_treeSum_le {r : ℝ} (hr : 1 < r) (ch : ProfileChoice) (f : ℝ → ℂ)
    (L : Linearization r) {E : Set ℝ} (𝒯 : MultitileTree ρ) (C : ℝ) (J : Dyadic) {x : ℝ}
    (hx : x ∈ E) :
    ‖treeSum ch f L E (𝒯.T.filter fun P => C * J.length ≤ P.I.length) x‖ₑ ≤
      L.tailSum (𝒯.OmegaJ C J) x ^ (1 / Real.conjExponent r) *
        (∑ k : Fin L.K, ‖∑ P ∈ 𝒯.T.filter (fun P => C * J.length ≤ P.I.length ∧
            L.ξ k.castSucc x ∈ P.ωl ∧ L.ξ k.succ x ∈ P.ωh),
          P.coeff ch f * P.wavePacket ch x‖ₑ ^ r) ^ (1 / r) := by
  have hr0 : 0 < r := by linarith
  have hr' : 0 < Real.conjExponent r := by
    unfold Real.conjExponent
    exact div_pos (by linarith) (by linarith)
  have hts : treeSum ch f L E (𝒯.T.filter fun P => C * J.length ≤ P.I.length) x =
      ∑ P ∈ 𝒯.T.filter (fun P => C * J.length ≤ P.I.length),
        P.coeff ch f * P.wavePacket ch x * P.aP L x := by
    unfold treeSum
    simp [Set.indicator_of_mem hx]
  rw [hts]
  have h1 := csvar hr ch f L 𝒯 C J x
  set K' := Finset.univ.filter (fun k : Fin L.K => L.ξ k.castSucc x ∈ 𝒯.OmegaJ C J) with hK'
  have hτ0 : 0 ≤ ∑ k ∈ K', ‖L.a k x‖ ^ Real.conjExponent r :=
    Finset.sum_nonneg fun _ _ => by positivity
  have hβ0 : 0 ≤ ∑ k ∈ K', ‖∑ P ∈ 𝒯.T.filter (fun P => C * J.length ≤ P.I.length ∧
      L.ξ k.castSucc x ∈ P.ωl ∧ L.ξ k.succ x ∈ P.ωh), P.coeff ch f * P.wavePacket ch x‖ ^ r :=
    Finset.sum_nonneg fun _ _ => by positivity
  rw [← ofReal_norm]
  calc ENNReal.ofReal ‖∑ P ∈ 𝒯.T.filter (fun P => C * J.length ≤ P.I.length),
        P.coeff ch f * P.wavePacket ch x * P.aP L x‖
      ≤ ENNReal.ofReal ((∑ k ∈ K', ‖L.a k x‖ ^ Real.conjExponent r) ^ (1 / Real.conjExponent r) *
          (∑ k ∈ K', ‖∑ P ∈ 𝒯.T.filter (fun P => C * J.length ≤ P.I.length ∧
            L.ξ k.castSucc x ∈ P.ωl ∧ L.ξ k.succ x ∈ P.ωh),
              P.coeff ch f * P.wavePacket ch x‖ ^ r) ^ (1 / r)) := ENNReal.ofReal_le_ofReal h1
    _ = L.tailSum (𝒯.OmegaJ C J) x ^ (1 / Real.conjExponent r) *
        (∑ k ∈ K', ‖∑ P ∈ 𝒯.T.filter (fun P => C * J.length ≤ P.I.length ∧
            L.ξ k.castSucc x ∈ P.ωl ∧ L.ξ k.succ x ∈ P.ωh),
          P.coeff ch f * P.wavePacket ch x‖ₑ ^ r) ^ (1 / r) := by
        have hβe : ENNReal.ofReal (∑ k ∈ K', ‖∑ P ∈ 𝒯.T.filter (fun P => C * J.length ≤ P.I.length ∧
            L.ξ k.castSucc x ∈ P.ωl ∧ L.ξ k.succ x ∈ P.ωh),
              P.coeff ch f * P.wavePacket ch x‖ ^ r) =
            ∑ k ∈ K', ‖∑ P ∈ 𝒯.T.filter (fun P => C * J.length ≤ P.I.length ∧
            L.ξ k.castSucc x ∈ P.ωl ∧ L.ξ k.succ x ∈ P.ωh),
              P.coeff ch f * P.wavePacket ch x‖ₑ ^ r := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hr0.le, ofReal_norm]
        rw [ENNReal.ofReal_mul (by positivity), Linearization.tailSum_eq_ofReal hr L,
          ENNReal.ofReal_rpow_of_nonneg hτ0 (by positivity),
          ← hβe, ENNReal.ofReal_rpow_of_nonneg hβ0 (by positivity)]
    _ ≤ _ := by
        gcongr
        exact Finset.filter_subset _ _



omit [Fact ρ.IsOneOrTwo] in
/-- `Ω_J` is measurable (a finite union of the intervals `ω_l`). -/
theorem MultitileTree.measurableSet_OmegaJ (𝒯 : MultitileTree ρ) (C : ℝ) (J : Dyadic) :
    MeasurableSet (𝒯.OmegaJ C J) := by
  classical
  have : 𝒯.OmegaJ C J = ⋃ P ∈ 𝒯.T.filter (fun P => C * J.length ≤ P.I.length), P.ωl := by
    ext y
    simp only [MultitileTree.OmegaJ, Set.mem_ofPred_eq, Finset.mem_filter, Set.mem_iUnion,
      exists_prop]
    constructor
    · rintro ⟨P, hP, hl, hy⟩
      exact ⟨P, ⟨hP, hl⟩, hy⟩
    · rintro ⟨P, ⟨hP, hl⟩, hy⟩
      exact ⟨P, hP, hl, hy⟩
  rw [this]
  exact Finset.measurableSet_biUnion _ fun P _ => ρ.measurableSet_ωl P.ωu

/-- The tail sum is measurable for a measurable set. -/
theorem Linearization.measurable_tailSum {r : ℝ} (L : Linearization r) {Ω : Set ℝ}
    (hΩ : MeasurableSet Ω) : Measurable (L.tailSum Ω) := by
  unfold Linearization.tailSum
  refine Finset.measurable_sum _ fun k _ => ?_
  refine Measurable.mul ((L.measurable_a k).enorm.pow_const _) ?_
  exact (measurable_const.indicator hΩ).comp (L.measurable_ξ _)

open Classical in
/-- **`treeestimatelargeintervals`** ([O+] L2372-L2398). Let `𝒯` be an
`l`-overlapping tree with (jconsolidation), `ψ` the cutoff, `κ ≥ 0` as in the local maximal bound
(hypothesis `hκ`, for the demodulated tree function `g = e_T^{-1} ∑_P ⟨f, φ_P⟩ φ_P`), `q ≥ r'`,
`J ∈ 𝒥`. Then, with `W(y) = V^r_{ℓ ∈ ℤ}(ψ_ℓ * g (y))`,
`∫_J |∑_{P : |I| ≥ C''|J|} ⟨f, φ_P⟩ φ_P a_P 1_E|^q ≤ κ^q 4 (11/2)^4 den^{r'} ∫_J (M[W])^q`. -/
theorem overlapping_per_J (hC : AdmissibleConstants C₁ C₂ C₃) (hρ : ρ.IsStd) {r q : ℝ}
    (hr : 1 < r) (hq : Real.conjExponent r ≤ q) {ψ : 𝓢(ℝ, ℂ)}
    (hψ : IsPsiCutoff (C₁ / 4) (C₃ / 4) ψ) {κ : ℝ} (hκ0 : 0 ≤ κ) (ch : ProfileChoice)
    (f : ℝ → ℂ) {E : Set ℝ} (hE : MeasurableSet E) (L : Linearization r)
    {S : Set (Multitile ρ)} {den : ℝ}
    (hde : density C₁ C₂ M L E S ≤ ENNReal.ofReal den) {𝒯 : MultitileTree ρ}
    (hT : 𝒯.IsTree C₁ C₂ M) (hsq : ∀ P ∈ 𝒯.T, P.InSquare M)
    (hsub : (𝒯.T : Set (Multitile ρ)) ⊆ S) (hov : 𝒯.IsOverlapping C₂)
    (hpm : 𝒯.IsPlus ∨ 𝒯.IsMinus) (hsep : Separated C₁ C₂ C₃ (𝒯.T : Set (Multitile ρ)))
    (hjc : ∃ j : ℤ, ∀ P ∈ 𝒯.T, 𝒯.ξ - j * P.ωu.length ∈ P.ωl)
    (hκ : ∀ (ℓ₀ : ℤ) (x x' : ℝ), |x - x'| ≤ (2 : ℝ) ^ ℓ₀ →
      rVariationOn r ((↑) '' {ℓ : ℤ | ℓ₀ ≤ ℓ} : Set ℝ)
        (fun t => schwartzAvg ψ ⌊t⌋ (modTreeFn ch f 𝒯.ξ 𝒯.T) x) ≤
        ENNReal.ofReal κ * maximalHLR (varW ψ r (modTreeFn ch f 𝒯.ξ 𝒯.T)) x')
    {J : Dyadic} (hJ : 𝒯.IsMaxAvoiding J) :
    ∫⁻ x in J.toSet, ‖treeSum ch f L E
        (𝒯.T.filter fun P => Cpp C₁ C₂ * J.length ≤ P.I.length) x‖ₑ ^ q ≤
      ENNReal.ofReal (κ ^ q * (4 * (11 / 2) ^ 4)) * ENNReal.ofReal den ^ Real.conjExponent r *
        ∫⁻ x in J.toSet, maximalHLR (varW ψ r (modTreeFn ch f 𝒯.ξ 𝒯.T)) x ^ q := by
  have hr0 : 0 < r := by linarith
  have hr' : 0 < Real.conjExponent r := by
    unfold Real.conjExponent
    exact div_pos (by linarith) (by linarith)
  have hq0 : 0 < q := lt_of_lt_of_le hr' hq
  set g := modTreeFn ch f 𝒯.ξ 𝒯.T with hg
  set Ω := 𝒯.OmegaJ (Cpp C₁ C₂) J with hΩ
  set T' := 𝒯.T.filter fun P => Cpp C₁ C₂ * J.length ≤ P.I.length with hT'
  set Mx : ℝ → ℝ≥0∞ := maximalHLR (varW ψ r g) with hMx
  have hC8 := eight_le_Cpp hC
  have hJm : MeasurableSet J.toSet := J.measurableSet_toSet
  have hJpos := J.length_pos
  set pred : ℤ → Prop := fun s => Cpp C₁ C₂ * J.length ≤ (2 : ℝ) ^ s with hpred_def
  have hpred : ∀ s s' : ℤ, s ≤ s' → pred s → pred s' := fun s s' h hs =>
    hs.trans (zpow_le_zpow_right₀ (by norm_num) h)
  have hℓ₀ : ∀ P ∈ 𝒯.T, pred P.I.k → J.k ≤ P.I.k := by
    intro P _ hP
    by_contra hcon
    rw [not_le] at hcon
    have h1 : (2 : ℝ) ^ P.I.k * 2 ≤ (2 : ℝ) ^ J.k := by
      calc (2 : ℝ) ^ P.I.k * 2 = (2 : ℝ) ^ (P.I.k + 1) := by rw [zpow_add_one₀ (by norm_num)]
        _ ≤ (2 : ℝ) ^ J.k := zpow_le_zpow_right₀ (by norm_num) (by omega)
    have h2 : 8 * J.length ≤ Cpp C₁ C₂ * J.length := mul_le_mul_of_nonneg_right hC8 hJpos.le
    have h3 : J.length = (2 : ℝ) ^ J.k := rfl
    have hP' : Cpp C₁ C₂ * J.length ≤ (2 : ℝ) ^ P.I.k := hP
    nlinarith
  have hτ1 : ∀ x, L.tailSum Ω x ≤ 1 := by
    intro x
    rw [Linearization.tailSum_eq_ofReal hr L, ← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← L.sum_norm_rpow x]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => by positivity)
  have hpt : ∀ x ∈ J.toSet, ∀ x' ∈ J.toSet, ‖treeSum ch f L E T' x‖ₑ ^ q ≤
      ENNReal.ofReal κ ^ q * (E.indicator (L.tailSum Ω) x * Mx x' ^ q) := by
    intro x hx x' hx'
    by_cases hxE : x ∈ E
    · rw [Set.indicator_of_mem hxE]
      have h1 := enorm_treeSum_le hr ch f L 𝒯 (Cpp C₁ C₂) J hxE
      have h2 := variation_in_scale_parameter hC hρ hψ hr0 ch f L hT hov hsep hjc pred hpred J.k
        hℓ₀ x
      have h3 : (∑ k : Fin L.K, ‖∑ P ∈ 𝒯.T.filter (fun P => Cpp C₁ C₂ * J.length ≤ P.I.length ∧
            L.ξ k.castSucc x ∈ P.ωl ∧ L.ξ k.succ x ∈ P.ωh),
          P.coeff ch f * P.wavePacket ch x‖ₑ ^ r) ^ (1 / r) ≤
          ENNReal.ofReal κ * Mx x' := by
        refine le_trans (ENNReal.rpow_le_rpow h2 (by positivity)) ?_
        rw [← ENNReal.rpow_mul, mul_one_div_cancel hr0.ne', ENNReal.rpow_one]
        refine hκ J.k x x' ?_
        have hxJ := hx
        have hxJ' := hx'
        simp only [Dyadic.mem_toSet, Dyadic.right_eq] at hxJ hxJ'
        have : J.length = (2 : ℝ) ^ J.k := rfl
        rw [abs_le]
        constructor <;> linarith [hxJ.1, hxJ.2, hxJ'.1, hxJ'.2]
      have h5 : ‖treeSum ch f L E T' x‖ₑ ≤
          L.tailSum Ω x ^ (1 / Real.conjExponent r) * (ENNReal.ofReal κ * Mx x') :=
        h1.trans (mul_le_mul_right h3 _)
      have hexp : 1 ≤ q / Real.conjExponent r := by rw [le_div_iff₀ hr']; linarith
      calc ‖treeSum ch f L E T' x‖ₑ ^ q
          ≤ (L.tailSum Ω x ^ (1 / Real.conjExponent r) * (ENNReal.ofReal κ * Mx x')) ^ q :=
            ENNReal.rpow_le_rpow h5 hq0.le
        _ = L.tailSum Ω x ^ (q / Real.conjExponent r) * (ENNReal.ofReal κ ^ q * Mx x' ^ q) := by
            rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le, ← ENNReal.rpow_mul,
              ENNReal.mul_rpow_of_nonneg _ _ hq0.le, one_div_mul_eq_div]
        _ ≤ L.tailSum Ω x * (ENNReal.ofReal κ ^ q * Mx x' ^ q) := by
            gcongr
            calc L.tailSum Ω x ^ (q / Real.conjExponent r) ≤ L.tailSum Ω x ^ (1 : ℝ) :=
                  ENNReal.rpow_le_rpow_of_exponent_ge (hτ1 x) hexp
              _ = L.tailSum Ω x := ENNReal.rpow_one _
        _ = _ := by ring
    · rw [Set.indicator_of_notMem hxE]
      have : treeSum ch f L E T' x = 0 := by
        unfold treeSum
        simp [Set.indicator_of_notMem hxE]
      rw [this, enorm_zero, ENNReal.zero_rpow_of_pos hq0]
      simp
  -- integrate over `x'` and then over `x`
  set Φ : ℝ≥0∞ := ∫⁻ x' in J.toSet, Mx x' ^ q with hΦ
  have hvolJ : volume J.toSet = ENNReal.ofReal J.length := Dyadic.volume_toSet J
  have hvol0 : volume J.toSet ≠ 0 := by
    rw [hvolJ]; exact (ENNReal.ofReal_pos.2 hJpos).ne'
  have hvolT : volume J.toSet ≠ ⊤ := by rw [hvolJ]; exact ENNReal.ofReal_ne_top
  have hA : ∀ x ∈ J.toSet, ‖treeSum ch f L E T' x‖ₑ ^ q * volume J.toSet ≤
      ENNReal.ofReal κ ^ q * E.indicator (L.tailSum Ω) x * Φ := by
    intro x hx
    calc ‖treeSum ch f L E T' x‖ₑ ^ q * volume J.toSet
        = ∫⁻ x' in J.toSet, ‖treeSum ch f L E T' x‖ₑ ^ q := by
          rw [setLIntegral_const, mul_comm]
      _ ≤ ∫⁻ x' in J.toSet, (ENNReal.ofReal κ ^ q * E.indicator (L.tailSum Ω) x) * Mx x' ^ q :=
          setLIntegral_mono' hJm fun x' hx' => by
            have := hpt x hx x' hx'
            rw [← mul_assoc, mul_comm (ENNReal.ofReal κ ^ q), mul_assoc] at this
            calc _ ≤ _ := this
              _ = _ := by ring
      _ = _ := by rw [lintegral_const_mul' _ _ (by
            exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hq0.le ENNReal.ofReal_ne_top)
              (by
                by_cases hx : x ∈ E
                · rw [Set.indicator_of_mem hx]
                  exact ne_top_of_le_ne_top ENNReal.one_ne_top (hτ1 x)
                · rw [Set.indicator_of_notMem hx]; exact ENNReal.zero_ne_top))]
  have hspec : 𝒯.IsSpecial C₂ :=
    hpm.elim (fun h => Or.inr (Or.inl ⟨hov, h⟩)) (fun h => Or.inr (Or.inr ⟨hov, h⟩))
  have hdens := usedensitybound hC hρ hr L hE hde hT hsq hsub hspec hJ
  have hfinal : (∫⁻ x in J.toSet, ‖treeSum ch f L E T' x‖ₑ ^ q) * volume J.toSet ≤
      (ENNReal.ofReal (κ ^ q * (4 * (11 / 2) ^ 4)) * ENNReal.ofReal den ^
          Real.conjExponent r * Φ) * volume J.toSet := by
   calc (∫⁻ x in J.toSet, ‖treeSum ch f L E T' x‖ₑ ^ q) * volume J.toSet
      = ∫⁻ x in J.toSet, ‖treeSum ch f L E T' x‖ₑ ^ q * volume J.toSet :=
        (lintegral_mul_const' _ _ hvolT).symm
    _ ≤ ∫⁻ x in J.toSet, ENNReal.ofReal κ ^ q * E.indicator (L.tailSum Ω) x * Φ :=
        setLIntegral_mono' hJm hA
    _ = ENNReal.ofReal κ ^ q * (∫⁻ x in J.toSet, E.indicator (L.tailSum Ω) x) * Φ := by
        have hIm : Measurable (E.indicator (L.tailSum Ω)) :=
          (L.measurable_tailSum (𝒯.measurableSet_OmegaJ _ J)).indicator hE
        have h1 : ∫⁻ x in J.toSet, ENNReal.ofReal κ ^ q * E.indicator (L.tailSum Ω) x * Φ =
            (∫⁻ x in J.toSet, ENNReal.ofReal κ ^ q * E.indicator (L.tailSum Ω) x) * Φ :=
          lintegral_mul_const'' Φ ((measurable_const.mul hIm).aemeasurable)
        rw [h1, lintegral_const_mul' _ _
          (ENNReal.rpow_ne_top_of_nonneg hq0.le ENNReal.ofReal_ne_top)]
    _ ≤ ENNReal.ofReal κ ^ q * (ENNReal.ofReal (4 * (11 / 2) ^ 4) * ENNReal.ofReal den ^
          Real.conjExponent r * volume J.toSet) * Φ := by
        gcongr
        rw [setLIntegral_indicator hE, Set.inter_comm, hvolJ]
        exact hdens
    _ = (ENNReal.ofReal (κ ^ q * (4 * (11 / 2) ^ 4)) * ENNReal.ofReal den ^
          Real.conjExponent r * Φ) * volume J.toSet := by
        have e : ENNReal.ofReal (κ ^ q * (4 * (11 / 2) ^ 4)) =
            ENNReal.ofReal κ ^ q * ENNReal.ofReal (4 * (11 / 2) ^ 4) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_rpow_of_nonneg hκ0 hq0.le]
        rw [e]
        ring
  exact (ENNReal.mul_le_mul_iff_left hvol0 hvolT).1 hfinal


omit [Fact ρ.IsOneOrTwo] in
/-- The demodulated tree function `g = e_T^{-1} G`, `G = ∑_{P ∈ T} ⟨f, φ_P⟩ φ_P`, has the same
modulus as `G`. -/
theorem norm_modTreeFn (ch : ProfileChoice) (f : ℝ → ℂ) (ξ : ℝ) (T : Finset (Multitile ρ))
    (x : ℝ) : ‖modTreeFn ch f ξ T x‖ = ‖∑ P ∈ T, P.coeff ch f • P.wavePacket ch x‖ := by
  have : modTreeFn ch f ξ T x = (∑ P ∈ T, P.coeff ch f • P.wavePacket ch x) * e (-(x * ξ)) := by
    unfold modTreeFn modPacket
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun P _ => ?_
    rw [smul_eq_mul]
    ring
  rw [this, norm_mul, norm_e, mul_one]

omit [Fact ρ.IsOneOrTwo] in
/-- `G = ∑_P ⟨f, φ_P⟩ φ_P ∈ L²` and `g ∈ L²` with `‖g‖₂² = ‖G‖₂²`. -/
theorem eLpNorm_modTreeFn_sq (ch : ProfileChoice) (f : ℝ → ℂ) (ξ : ℝ)
    (T : Finset (Multitile ρ)) :
    MemLp (modTreeFn ch f ξ T) 2 volume ∧ eLpNorm (modTreeFn ch f ξ T) 2 volume ^ 2 =
      ENNReal.ofReal (∫ x, ‖∑ P ∈ T, P.coeff ch f • P.wavePacket ch x‖ ^ 2) := by
  have hGm : MemLp (fun x => ∑ P ∈ T, P.coeff ch f • P.wavePacket ch x) 2 volume :=
    memLp_finsetSum T fun P _ =>
      (ch.isProfile.memLp_wavePacketOf P.I P.ωu).const_smul (P.coeff ch f)
  have hgm : AEStronglyMeasurable (modTreeFn ch f ξ T) volume :=
    (fnice_modTreeFn ch f ξ T).continuous.aestronglyMeasurable
  have hg : MemLp (modTreeFn ch f ξ T) 2 volume :=
    hGm.of_le hgm (Eventually.of_forall fun x => (norm_modTreeFn ch f ξ T x).le)
  refine ⟨hg, ?_⟩
  have hint : Integrable (fun x => ‖∑ P ∈ T, P.coeff ch f • P.wavePacket ch x‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm hGm.aestronglyMeasurable).1 hGm
  rw [← lintegral_sq_eq_eLpNorm_sq hgm,
    ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun x => by positivity)]
  refine lintegral_congr fun x => ?_
  rw [← ofReal_norm, norm_modTreeFn, ENNReal.ofReal_pow (norm_nonneg _)]


end PerJ

/-- Exponent bookkeeping for the final constant of the overlapping case. -/
theorem rpow_bookkeeping_overlapping {q : ℝ} (hq1 : 1 ≤ q) {K ene I : ℝ} (hK : 0 ≤ K) (he : 0 ≤ ene)
    (hI : 0 < I) :
    (K * ene ^ 2 * I) ^ (q / 2) * (48 * I) ^ (1 - q / 2) ≤ K ^ (q / 2) * ene ^ q * (48 * I) := by
  have h1 : (K * ene ^ 2 * I) ^ (q / 2) = K ^ (q / 2) * ene ^ q * I ^ (q / 2) := by
    rw [Real.mul_rpow (by positivity) hI.le, Real.mul_rpow hK (by positivity)]
    congr 2
    rw [← Real.rpow_natCast, ← Real.rpow_mul he]
    congr 1
    push_cast
    ring
  have h2 : (48 * I) ^ (1 - q / 2) = 48 ^ (1 - q / 2) * I ^ (1 - q / 2) :=
    Real.mul_rpow (by norm_num) hI.le
  have h3 : I ^ (q / 2) * I ^ (1 - q / 2) = I := by
    rw [← Real.rpow_add hI]
    norm_num
  have h4 : (48 : ℝ) ^ (1 - q / 2) ≤ 48 := by
    calc (48 : ℝ) ^ (1 - q / 2) ≤ (48 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 48 := Real.rpow_one _
  rw [h1, h2]
  have h5 : 0 ≤ K ^ (q / 2) * ene ^ q := by positivity
  calc K ^ (q / 2) * ene ^ q * I ^ (q / 2) * (48 ^ (1 - q / 2) * I ^ (1 - q / 2))
      = (K ^ (q / 2) * ene ^ q) * 48 ^ (1 - q / 2) * (I ^ (q / 2) * I ^ (1 - q / 2)) := by ring
    _ = (K ^ (q / 2) * ene ^ q) * 48 ^ (1 - q / 2) * I := by rw [h3]
    _ ≤ (K ^ (q / 2) * ene ^ q) * 48 * I := by gcongr
    _ = _ := by ring

open Classical in
/-- **`treeestimatelargeintervals`** ([O+] L2399-L2424), summed over the
intervals `J ∈ 𝒥` meeting `16 I_T`: for `r' ≤ q ≤ 2`, `l`-overlapping trees `T ⊂ S` satisfying
(jconsolidation), `l^±`-overlapping, the separation assumptions, in the square `[-2^M, 2^M]²`, with
`density(S) ≤ den`, and every finite set `𝒥s` of elements of `𝒥` meeting `16 I_T`,
`∑_{J ∈ 𝒥s} ∫_J |∑_{P ∈ T : |I| ≥ C''|J|} ⟨f, φ_P⟩ φ_P a_P 1_E|^q ≤
K den^{r'} (48|I_T|)^{(2-q)/2} (‖∑_{P ∈ T} ⟨f, φ_P⟩ φ_P‖_{L²}^2)^{q/2}`.
The constant depends on `r` and the constants `C₁, C₂, C₃` (through the cutoff `ψ`) only. -/
theorem overlapping_sum_le_L2 {r q : ℝ} (hr : 2 < r) (hq : Real.conjExponent r ≤ q)
    (hq2 : q ≤ 2) {C₁ C₂ C₃ : ℝ} (hC : AdmissibleConstants C₁ C₂ C₃) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {ρ : Idx} [Fact ρ.IsOneOrTwo] {M : ℤ}, ρ.IsStd → ∀ (ch : ProfileChoice)
      (f : ℝ → ℂ) {E : Set ℝ}, MeasurableSet E → ∀ (L : Linearization r) {S : Set (Multitile ρ)}
      {den : ℝ}, 0 ≤ den → density C₁ C₂ M L E S ≤ ENNReal.ofReal den →
      ∀ (𝒯 : MultitileTree ρ), 𝒯.IsTree C₁ C₂ M → (∀ P ∈ 𝒯.T, P.InSquare M) →
      (𝒯.T : Set (Multitile ρ)) ⊆ S → 𝒯.IsOverlapping C₂ → (𝒯.IsPlus ∨ 𝒯.IsMinus) →
      (∃ j : ℤ, ∀ P ∈ 𝒯.T, 𝒯.ξ - j * P.ωu.length ∈ P.ωl) →
      Separated C₁ C₂ C₃ (𝒯.T : Set (Multitile ρ)) → 𝒯.T.Nonempty →
      ∀ (𝒥s : Finset Dyadic), (∀ J ∈ 𝒥s, 𝒯.IsMaxAvoiding J ∧
        (J.toSet ∩ 𝒯.I.dilate 16).Nonempty) →
        ∑ J ∈ 𝒥s, ∫⁻ x in J.toSet, ‖treeSum ch f L E (𝒯.T.filter fun P => Cpp C₁ C₂ * J.length ≤
            P.I.length) x‖ₑ ^ q ≤
          ENNReal.ofReal (K * den ^ Real.conjExponent r * ((48 * 𝒯.I.length) ^ (1 - q / 2) *
            (∫ x, ‖∑ P ∈ 𝒯.T, P.coeff ch f • P.wavePacket ch x‖ ^ 2) ^ (q / 2))) := by
  have hr1 : 1 < r := by linarith
  have hr' : 0 < Real.conjExponent r := by
    unfold Real.conjExponent
    exact div_pos (by linarith) (by linarith)
  have hr'1 : 1 < Real.conjExponent r := by
    unfold Real.conjExponent
    rw [one_lt_div (by linarith)]
    linarith
  have hq1 : 1 ≤ q := by linarith
  have hq0 : 0 < q := by linarith
  have hC3 : 0 < C₃ := by linarith [hC.one_le]
  have hC1 : 0 < C₁ := by linarith [hC.one_le, hC.lt₁, hC.lt₂]
  have h₀ : 0 < C₃ / 4 := by positivity
  have h₁ : C₃ / 4 < C₁ / 4 := by linarith [hC.lt₁, hC.lt₂]
  set ψ := psi (C₁ / 4) (C₃ / 4) h₀ h₁ with hψdef
  have hψ : IsPsiCutoff (C₁ / 4) (C₃ / 4) ψ := isPsiCutoff_psi _ _ h₀ h₁
  have hψint : ∫ t, ψ t = 1 := integral_psi _ _ h₀ h₁
  obtain ⟨κ, hκ0, hκ⟩ := rVariationOn_schwartzAvg_le_maximalHLR hC3.le hψ hr1.le
  obtain ⟨A, hAtop, hA⟩ := lintegral_maximalHLR_varW_le hψint hr
  set a : ℝ := A.toReal with ha
  have hAa : A = ENNReal.ofReal a := (ENNReal.ofReal_toReal hAtop).symm
  refine ⟨κ ^ q * (4 * (11 / 2) ^ 4) * a ^ q, by positivity, ?_⟩
  intro ρ _ M hρ ch f E hE L S den hden hde 𝒯 hT hsq hsub hov hpm hjc hsep hne 𝒥s h𝒥
  set g := modTreeFn ch f 𝒯.ξ 𝒯.T with hg
  obtain ⟨hgL2, hgsq⟩ := eLpNorm_modTreeFn_sq ch f 𝒯.ξ 𝒯.T
  have hIpos := 𝒯.I.length_pos
  set Mx : ℝ → ℝ≥0∞ := maximalHLR (varW ψ r g) with hMx
  have hκ' : ∀ (ℓ₀ : ℤ) (x x' : ℝ), |x - x'| ≤ (2 : ℝ) ^ ℓ₀ →
      rVariationOn r ((↑) '' {ℓ : ℤ | ℓ₀ ≤ ℓ} : Set ℝ) (fun t => schwartzAvg ψ ⌊t⌋ g x) ≤
        ENNReal.ofReal κ * Mx x' := fun ℓ₀ x x' h =>
    hκ (fnice_modTreeFn ch f 𝒯.ξ 𝒯.T) ℓ₀ x x' h
  have hper : ∀ J ∈ 𝒥s, ∫⁻ x in J.toSet, ‖treeSum ch f L E
      (𝒯.T.filter fun P => Cpp C₁ C₂ * J.length ≤ P.I.length) x‖ₑ ^ q ≤
      ENNReal.ofReal (κ ^ q * (4 * (11 / 2) ^ 4)) * ENNReal.ofReal den ^ Real.conjExponent r *
        ∫⁻ x in J.toSet, Mx x ^ q := fun J hJ =>
    overlapping_per_J hC hρ hr1 hq hψ hκ0 ch f hE L hde hT hsq hsub hov hpm hsep hjc hκ'
      (h𝒥 J hJ).1
  set U : Set ℝ := ⋃ J ∈ 𝒥s, J.toSet with hU
  have hdisj : (𝒥s : Set Dyadic).PairwiseDisjoint Dyadic.toSet := fun J hJ J' hJ' hne' =>
    (h𝒥 J hJ).1.disjoint (h𝒥 J' hJ').1 hne'
  have hvolU : volume U ≤ ENNReal.ofReal (48 * 𝒯.I.length) := by
    rw [hU, measure_biUnion_finset hdisj (fun J _ => J.measurableSet_toSet)]
    simp_rw [Dyadic.volume_toSet]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun J _ => J.length_pos.le)]
    exact ENNReal.ofReal_le_ofReal (MultitileTree.sum_length_le hne hT.time 𝒥s h𝒥)
  have hsumΦ : ∑ J ∈ 𝒥s, ∫⁻ x in J.toSet, Mx x ^ q = ∫⁻ x in U, Mx x ^ q := by
    rw [hU, lintegral_biUnion_finset hdisj (fun J _ => J.measurableSet_toSet)]
  have hG0 : 0 ≤ ∫ x, ‖∑ P ∈ 𝒯.T, P.coeff ch f • P.wavePacket ch x‖ ^ 2 :=
    integral_nonneg fun x => by positivity
  have hNg : eLpNorm g 2 volume ^ q =
      ENNReal.ofReal ((∫ x, ‖∑ P ∈ 𝒯.T, P.coeff ch f • P.wavePacket ch x‖ ^ 2) ^ (q / 2)) := by
    have h2 : eLpNorm g 2 volume ^ q = (eLpNorm g 2 volume ^ 2) ^ (q / 2) := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      congr 1
      push_cast
      ring
    rw [h2, hgsq, ENNReal.ofReal_rpow_of_nonneg hG0 (by positivity)]
  have hV : volume U ^ (1 - q / 2) ≤ ENNReal.ofReal ((48 * 𝒯.I.length) ^ (1 - q / 2)) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg (by positivity) (by linarith)]
    exact ENNReal.rpow_le_rpow hvolU (by linarith)
  have hcnn : (0 : ℝ) ≤ κ ^ q * (4 * (11 / 2) ^ 4) := by positivity
  calc ∑ J ∈ 𝒥s, ∫⁻ x in J.toSet, ‖treeSum ch f L E (𝒯.T.filter fun P =>
          Cpp C₁ C₂ * J.length ≤ P.I.length) x‖ₑ ^ q
      ≤ ∑ J ∈ 𝒥s, ENNReal.ofReal (κ ^ q * (4 * (11 / 2) ^ 4)) *
          ENNReal.ofReal den ^ Real.conjExponent r * ∫⁻ x in J.toSet, Mx x ^ q :=
        Finset.sum_le_sum hper
    _ = ENNReal.ofReal (κ ^ q * (4 * (11 / 2) ^ 4)) * ENNReal.ofReal den ^ Real.conjExponent r *
          ∫⁻ x in U, Mx x ^ q := by rw [← Finset.mul_sum, hsumΦ]
    _ ≤ ENNReal.ofReal (κ ^ q * (4 * (11 / 2) ^ 4)) * ENNReal.ofReal den ^ Real.conjExponent r *
          (A ^ q * eLpNorm g 2 volume ^ q * volume U ^ (1 - q / 2)) := by
        gcongr
        exact hA hq1 hq2 hgL2 U
    _ ≤ ENNReal.ofReal (κ ^ q * (4 * (11 / 2) ^ 4)) * ENNReal.ofReal den ^ Real.conjExponent r *
          (ENNReal.ofReal (a ^ q) * ENNReal.ofReal ((∫ x, ‖∑ P ∈ 𝒯.T,
            P.coeff ch f • P.wavePacket ch x‖ ^ 2) ^ (q / 2)) *
            ENNReal.ofReal ((48 * 𝒯.I.length) ^ (1 - q / 2))) := by
        rw [hAa, ENNReal.ofReal_rpow_of_nonneg (by positivity) hq0.le, hNg]
        gcongr
    _ = ENNReal.ofReal (κ ^ q * (4 * (11 / 2) ^ 4) * a ^ q * den ^ Real.conjExponent r *
          ((48 * 𝒯.I.length) ^ (1 - q / 2) * (∫ x, ‖∑ P ∈ 𝒯.T,
            P.coeff ch f • P.wavePacket ch x‖ ^ 2) ^ (q / 2))) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hden hr'.le, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

open Classical in
/-- **The overlapping case summed over `J ∈ 𝒥` meeting `16 I_T`** ([O+]
`treeestimatelargeintervals`: the overlapping case, the maximal function and variation `L²` bounds
and the `L²` norm of the tree sum; L2399-L2442). There is a constant `K` (depending on `r`, `q` and
the constants `C₁, C₂, C₃` through the cutoff `ψ`) such that for every `l`-overlapping tree `T ⊂ S`
satisfying (jconsolidation), `l^±`-overlapping, the separation assumptions, in the square
`[-2^M, 2^M]²`, with `energy(S) ≤ ene`, `density(S) ≤ den`, for `r' ≤ q ≤ 2`, and every finite set
`𝒥s` of elements of `𝒥` meeting `16 I_T`,
`∑_{J ∈ 𝒥s} ∫_J |∑_{P ∈ T : |I| ≥ C''|J|} ⟨f, φ_P⟩ φ_P a_P 1_E|^q ≤ K ene^q den^{r'} 48 |I_T|`. -/
theorem overlapping_case_sum {r q : ℝ} (hr : 2 < r) (hq : Real.conjExponent r ≤ q) (hq2 : q ≤ 2)
    {C₁ C₂ C₃ : ℝ} (hC : AdmissibleConstants C₁ C₂ C₃) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {ρ : Idx} [Fact ρ.IsOneOrTwo] {M : ℤ}, ρ.IsStd → ∀ (ch : ProfileChoice)
      (f : ℝ → ℂ) {E : Set ℝ}, MeasurableSet E → ∀ (L : Linearization r) {S : Set (Multitile ρ)}
      {ene den : ℝ}, 0 ≤ ene → 0 ≤ den → energy C₁ C₂ M ch f S ≤ ENNReal.ofReal ene →
      density C₁ C₂ M L E S ≤ ENNReal.ofReal den → ∀ (𝒯 : MultitileTree ρ),
      𝒯.IsTree C₁ C₂ M → (∀ P ∈ 𝒯.T, P.InSquare M) → (𝒯.T : Set (Multitile ρ)) ⊆ S →
      𝒯.IsOverlapping C₂ → (𝒯.IsPlus ∨ 𝒯.IsMinus) →
      (∃ j : ℤ, ∀ P ∈ 𝒯.T, 𝒯.ξ - j * P.ωu.length ∈ P.ωl) →
      Separated C₁ C₂ C₃ (𝒯.T : Set (Multitile ρ)) → 𝒯.T.Nonempty →
      ∀ (𝒥s : Finset Dyadic), (∀ J ∈ 𝒥s, 𝒯.IsMaxAvoiding J ∧
        (J.toSet ∩ 𝒯.I.dilate 16).Nonempty) →
        ∑ J ∈ 𝒥s, ∫⁻ x in J.toSet, ‖treeSum ch f L E (𝒯.T.filter fun P => Cpp C₁ C₂ * J.length ≤
            P.I.length) x‖ₑ ^ q ≤
          ENNReal.ofReal (K * ene ^ q * den ^ Real.conjExponent r * (48 * 𝒯.I.length)) := by
  have hq1 : 1 ≤ q := by
    have : 1 < Real.conjExponent r := by
      unfold Real.conjExponent
      rw [one_lt_div (by linarith)]
      linarith
    linarith
  obtain ⟨K₁, hK₁0, hK₁⟩ := overlapping_sum_le_L2 hr hq hq2 hC
  obtain ⟨K_O, hKO0, hKO⟩ := l2_norm_tree_sum
  refine ⟨K₁ * K_O ^ (q / 2), by positivity, ?_⟩
  intro ρ _ M hρ ch f E hE L S ene den hene hden hen hde 𝒯 hT hsq hsub hov hpm hjc hsep hne 𝒥s
    h𝒥
  have hIpos := 𝒯.I.length_pos
  obtain ⟨-, -, hl2⟩ := hKO hC hρ ch f hene hen 𝒯 hT hov hsep hsub
  refine (hK₁ hρ ch f hE L hden hde 𝒯 hT hsq hsub hov hpm hjc hsep hne 𝒥s h𝒥).trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have hG0 : 0 ≤ ∫ x, ‖∑ P ∈ 𝒯.T, P.coeff ch f • P.wavePacket ch x‖ ^ 2 :=
    integral_nonneg fun x => by positivity
  have hb := rpow_bookkeeping_overlapping hq1 hKO0 hene hIpos
  rw [← mul_assoc K_O] at hl2
  have h1 : (∫ x, ‖∑ P ∈ 𝒯.T, P.coeff ch f • P.wavePacket ch x‖ ^ 2) ^ (q / 2) ≤
      (K_O * ene ^ 2 * 𝒯.I.length) ^ (q / 2) :=
    Real.rpow_le_rpow hG0 hl2 (by linarith)
  calc K₁ * den ^ Real.conjExponent r * ((48 * 𝒯.I.length) ^ (1 - q / 2) *
        (∫ x, ‖∑ P ∈ 𝒯.T, P.coeff ch f • P.wavePacket ch x‖ ^ 2) ^ (q / 2))
      ≤ K₁ * den ^ Real.conjExponent r * ((48 * 𝒯.I.length) ^ (1 - q / 2) *
        (K_O * ene ^ 2 * 𝒯.I.length) ^ (q / 2)) := by gcongr
    _ = K₁ * den ^ Real.conjExponent r * ((K_O * ene ^ 2 * 𝒯.I.length) ^ (q / 2) *
        (48 * 𝒯.I.length) ^ (1 - q / 2)) := by ring
    _ ≤ K₁ * den ^ Real.conjExponent r * (K_O ^ (q / 2) * ene ^ q * (48 * 𝒯.I.length)) := by
        gcongr
    _ = _ := by ring

end PrimeCarleson.Proof.Oplus
