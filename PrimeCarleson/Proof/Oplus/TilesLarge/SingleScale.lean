module

public import PrimeCarleson.Proof.Oplus.TilesLarge.Coefficients

/-!
# The `L¹` bound off `Ω_λ` for the tiles with one time interval ([O+] L2526-L2536)

Source: [O+] `tileslargemaxprop`, L2526–L2536: for a dyadic interval `I_ℓ` with
`2^ℓ I_ℓ ⊂ Ω_λ` and `2^{ℓ+1} I_ℓ ⊄ Ω_λ`,
`‖∑_{P : I = I_ℓ} ⟨f, φ_P⟩ φ_P a_P‖_{L¹(ℝ ∖ Ω_λ)} ≲ (2^ℓ λ)^{1/r'} |I_ℓ|^{1/2}
‖φ_{P_0}‖_{L¹(ℝ ∖ Ω_λ)} ≲ 2^{-ℓ(N-2)} λ^{1/r'} |I_ℓ|`.

* `Multitile.eq_of_mem_ωl_of_same_interval`: "for each `ξ`, `I_ℓ` there is at most one `P` with
  `ξ ∈ ω_l` and `I = I_ℓ`" (for `1`- and `2`-indices, where `ω_l` is a finite dyadic interval);
* `sum_norm_aP_rpow_le_one`: hence `∑_{P : I = I_ℓ} |a_P(x)|^{r'} ≤ ∑_k |a_k(x)|^{r'} = 1`;
* `norm_sum_coeff_mul_aP_le`: the pointwise Hölder inequality in `P`
  (`|∑_P c_P φ_P(x) a_P(x)| ≤ |φ_{P_0}(x)| (∑_P |c_P|^r)^{1/r}`, all `φ_P` having the same
  modulus, `norm_wavePacketOf_eq_of_same_interval`);
* `exists_eLpNorm_single_scale_le`: the bound itself, with the explicit factor
  `((2^ℓ)⁻¹)^{N-3} λ^{1/r'} |I_ℓ|` (the source's `2^{-ℓ(N-2)} (2^ℓ)^{1/r'}` with
  `(2^ℓ)^{1/r'} ≤ 2^ℓ`; the envelope integral `∫_{ℝ ∖ Ω_λ} |I|^{-1/2} (1 + |x - c|/|I|)^{-N}`
  is estimated by `((2^ℓ/2)^{-(N-2)}) ∫ (1 + |x - c|/|I|)^{-2}`, one power of `N` weaker than the
  source's `2^{-ℓ(N-1)}`, which is immaterial since `N` is free).
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

/-! ### At most one multitile per point of `ω_l` -/

/-- For a `1`- or `2`-index, two `ρ`-multitiles with the same time interval and a common point
of `ω_l` are equal ("at most one `P` with `ξ ∈ ω_l` and `I = I_ℓ`", L2526-L2528). -/
theorem Multitile.eq_of_mem_ωl_of_same_interval {ρ : Idx} (hρ : ρ.IsOneOrTwo)
    {P P' : Multitile ρ} (hI : P.I = P'.I) {ξ : ℝ} (h : ξ ∈ P.ωl) (h' : ξ ∈ P'.ωl) : P = P' := by
  rw [Multitile.ωl_eq_toSet_ωlDyadic P hρ] at h
  rw [Multitile.ωl_eq_toSet_ωlDyadic P' hρ] at h'
  have hk : P.ωu.k = P'.ωu.k := by
    have h1 := P.area
    have h2 := P'.area
    rw [hI] at h1
    omega
  have hk' : (ρ.ωlDyadic P.ωu).k = (ρ.ωlDyadic P'.ωu).k := hk
  have heq := Dyadic.eq_of_k_eq_of_mem hk' h h'
  have hm : P.ωu.m = P'.ωu.m := by
    have := congrArg Dyadic.m heq
    simp only [Idx.ωlDyadic, Dyadic.shift] at this
    omega
  exact Multitile.ext hI (Dyadic.ext hk hm)

/-! ### The coefficients `a_P` of the multitiles with one time interval -/

/-- **`∑_{P : I = I_ℓ} |a_P(x)|^{r'} ≤ 1`** (L2527-L2530): the map `P ↦ k` with
`ξ_{k-1}(x) ∈ ω_l(P)`, `a_P(x) = a_k(x)` is injective on the multitiles with one time interval, so
`∑_P |a_P(x)|^{r'} ≤ ∑_k |a_k(x)|^{r'} = 1`. -/
theorem sum_norm_aP_rpow_le_one {ρ : Idx} (hρ : ρ.IsOneOrTwo) {r : ℝ} (hr : 1 < r)
    (L : Linearization r) (S : Finset (Multitile ρ)) {I₀ : Dyadic}
    (hS : ∀ P ∈ S, P.I = I₀) (x : ℝ) :
    ∑ P ∈ S, ‖P.aP L x‖ ^ Real.conjExponent r ≤ 1 := by
  classical
  set q : ℝ := Real.conjExponent r with hq
  have hq0 : 0 < q := by
    rw [hq]; unfold Real.conjExponent
    exact div_pos (by linarith) (by linarith)
  -- each `‖a_P(x)‖^q` is at most the sum over the compatible `k`
  have hP : ∀ P ∈ S, ‖P.aP L x‖ ^ q ≤
      ∑ k : Fin L.K, if (L.ξ k.castSucc x ∈ P.ωl ∧ L.ξ k.succ x ∈ P.ωh) then ‖L.a k x‖ ^ q
        else 0 := by
    intro P _
    by_cases hk : ∃ k : Fin L.K, L.ξ k.castSucc x ∈ P.ωl ∧ L.ξ k.succ x ∈ P.ωh
    · obtain ⟨k, hk1, hk2⟩ := hk
      rw [P.aP_eq_of_mem L x hk1 hk2]
      refine le_trans (le_of_eq ?_) (Finset.single_le_sum
        (f := fun k : Fin L.K => if (L.ξ k.castSucc x ∈ P.ωl ∧ L.ξ k.succ x ∈ P.ωh) then
          ‖L.a k x‖ ^ q else 0) (fun j _ => by split_ifs <;> positivity) (Finset.mem_univ k))
      simp [hk1, hk2]
    · push Not at hk
      rw [P.aP_eq_zero_of_not L x (fun k hk' => absurd hk'.2 (hk k hk'.1)), norm_zero,
        Real.zero_rpow hq0.ne']
      exact Finset.sum_nonneg fun j _ => by split_ifs <;> positivity
  calc ∑ P ∈ S, ‖P.aP L x‖ ^ q
      ≤ ∑ P ∈ S, ∑ k : Fin L.K, if (L.ξ k.castSucc x ∈ P.ωl ∧ L.ξ k.succ x ∈ P.ωh) then
        ‖L.a k x‖ ^ q else 0 := Finset.sum_le_sum hP
    _ = ∑ k : Fin L.K, ∑ P ∈ S, if (L.ξ k.castSucc x ∈ P.ωl ∧ L.ξ k.succ x ∈ P.ωh) then
        ‖L.a k x‖ ^ q else 0 := Finset.sum_comm
    _ ≤ ∑ k : Fin L.K, ‖L.a k x‖ ^ q := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [← Finset.sum_filter]
        have hcard : (S.filter fun P => L.ξ k.castSucc x ∈ P.ωl ∧
            L.ξ k.succ x ∈ P.ωh).card ≤ 1 := by
          refine Finset.card_le_one.2 fun P hP P' hP' => ?_
          have h1 := Finset.mem_filter.1 hP
          have h2 := Finset.mem_filter.1 hP'
          exact Multitile.eq_of_mem_ωl_of_same_interval hρ ((hS P h1.1).trans (hS P' h2.1).symm)
            h1.2.1 h2.2.1
        rw [Finset.sum_const, nsmul_eq_mul]
        have : ((S.filter fun P => L.ξ k.castSucc x ∈ P.ωl ∧ L.ξ k.succ x ∈ P.ωh).card : ℝ) ≤ 1 :=
          by exact_mod_cast hcard
        nlinarith [Real.rpow_nonneg (norm_nonneg (L.a k x)) q]
    _ = 1 := L.sum_norm_rpow x

/-- **The pointwise Hölder bound** (L2527-L2530): for multitiles `S` with a common time interval
`I₀` and any `P₀` with `P₀.I = I₀`,
`|∑_{P ∈ S} ⟨f, φ_P⟩ φ_P(x) a_P(x)| ≤ |φ_{P₀}(x)| (∑_{P ∈ S} |⟨f, φ_P⟩|^r)^{1/r}`
(all `φ_P`, `P ∈ S`, have the modulus of `φ_{P₀}`, and `∑_P |a_P(x)|^{r'} ≤ 1`). -/
theorem norm_sum_coeff_mul_aP_le {ρ : Idx} (hρ : ρ.IsOneOrTwo) {r : ℝ} (hr : 1 < r)
    (ch : ProfileChoice) (f : ℝ → ℂ) (L : Linearization r) (S : Finset (Multitile ρ))
    {I₀ : Dyadic} (hS : ∀ P ∈ S, P.I = I₀) {P₀ : Multitile ρ} (hP₀ : P₀.I = I₀) (x : ℝ) :
    ‖∑ P ∈ S, P.coeff ch f * P.wavePacket ch x * P.aP L x‖ ≤
      ‖P₀.wavePacket ch x‖ * (∑ P ∈ S, ‖P.coeff ch f‖ ^ r) ^ (1 / r) := by
  have hpq : r.HolderConjugate (Real.conjExponent r) := Real.HolderConjugate.conjExponent hr
  have hmod : ∀ P ∈ S, ‖P.wavePacket ch x‖ = ‖P₀.wavePacket ch x‖ := by
    intro P hP
    have h1 := P.area
    have h2 := P₀.area
    rw [hS P hP] at h1
    rw [hP₀] at h2
    have e := norm_wavePacketOf_eq_of_same_interval ch.fn (I := I₀) (J := P.ωu) (J' := P₀.ωu)
      h1 h2 x
    have eP : P.wavePacket ch x = wavePacketOf ch.fn I₀ P.ωu x := by rw [← hS P hP]; rfl
    have eP₀ : P₀.wavePacket ch x = wavePacketOf ch.fn I₀ P₀.ωu x := by rw [← hP₀]; rfl
    rw [eP, eP₀]
    exact e
  calc ‖∑ P ∈ S, P.coeff ch f * P.wavePacket ch x * P.aP L x‖
      ≤ ∑ P ∈ S, ‖P.coeff ch f * P.wavePacket ch x * P.aP L x‖ := norm_sum_le _ _
    _ = ‖P₀.wavePacket ch x‖ * ∑ P ∈ S, ‖P.coeff ch f‖ * ‖P.aP L x‖ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun P hP => ?_
        rw [norm_mul, norm_mul, hmod P hP]
        ring
    _ ≤ ‖P₀.wavePacket ch x‖ * ((∑ P ∈ S, ‖P.coeff ch f‖ ^ r) ^ (1 / r) *
          (∑ P ∈ S, ‖P.aP L x‖ ^ Real.conjExponent r) ^ (1 / Real.conjExponent r)) := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        exact Real.inner_le_Lp_mul_Lq_of_nonneg S hpq (fun P _ => norm_nonneg _)
          (fun P _ => norm_nonneg _)
    _ ≤ ‖P₀.wavePacket ch x‖ * ((∑ P ∈ S, ‖P.coeff ch f‖ ^ r) ^ (1 / r) * 1) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity))
          (norm_nonneg _)
        have h1 := sum_norm_aP_rpow_le_one hρ hr L S hS x
        have h2 : (0 : ℝ) ≤ 1 / Real.conjExponent r := hpq.symm.one_div_nonneg
        calc (∑ P ∈ S, ‖P.aP L x‖ ^ Real.conjExponent r) ^ (1 / Real.conjExponent r)
            ≤ 1 ^ (1 / Real.conjExponent r) :=
              Real.rpow_le_rpow (Finset.sum_nonneg fun P _ => by positivity) h1 h2
          _ = 1 := Real.one_rpow _
    _ = ‖P₀.wavePacket ch x‖ * (∑ P ∈ S, ‖P.coeff ch f‖ ^ r) ^ (1 / r) := by rw [mul_one]

/-- The tile sum `∑_{P ∈ S} ⟨f, φ_P⟩ φ_P a_P` is measurable. -/
theorem measurable_tileSum {ρ : Idx} {r : ℝ} (ch : ProfileChoice) (f : ℝ → ℂ)
    (L : Linearization r) (S : Finset (Multitile ρ)) :
    Measurable (fun x => ∑ P ∈ S, P.coeff ch f * P.wavePacket ch x * P.aP L x) := by
  refine Finset.measurable_sum _ fun P _ => ?_
  have h1 : Measurable (P.wavePacket ch) :=
    (ch.isProfile.continuous_wavePacketOf P.I P.ωu).measurable
  exact (measurable_const.mul h1).mul (P.measurable_aP L)

/-! ### The single-scale `L¹` bound -/

/-- **`tileslargemaxprop`** ([O+] L2526-L2536): for `N ≥ 3` there is `K`
(independent of `ρ`, the profile choice, `r ≥ 2`, the linearizing data, `F`, `f`, `λ`, `ℓ`) such
that for every finite set `S` of `ρ`-multitiles (`ρ` a `1`- or `2`-index) with a common time
interval `I₀` with `2^ℓ I₀ ⊂ Ω_λ` and `2^{ℓ+1} I₀ ⊄ Ω_λ`,
`‖∑_{P ∈ S} ⟨f, φ_P⟩ φ_P a_P‖_{L¹(ℝ ∖ Ω_λ)} ≤ K ((2^ℓ)⁻¹)^{N-3} λ^{1/r'} |I₀|`. -/
theorem exists_eLpNorm_single_scale_le (N : ℕ) (hN : 3 ≤ N) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {ρ : Idx}, ρ.IsOneOrTwo → ∀ {r : ℝ}, 2 ≤ r → ∀ (ch : ProfileChoice)
      (L : Linearization r) (S : Finset (Multitile ρ)) {I₀ : Dyadic}, (∀ P ∈ S, P.I = I₀) →
      ∀ {F : Set ℝ} {f : ℝ → ℂ}, MeasurableSet F → AEStronglyMeasurable f volume →
      (∀ᵐ x, ‖f x‖ ≤ F.indicator (fun _ => (1 : ℝ)) x) → ∀ {lam : ℝ}, 0 < lam → ∀ {ℓ : ℕ},
      I₀.dilate ((2 : ℝ) ^ ℓ) ⊆ maxSuperlevel F lam →
      ¬ I₀.dilate ((2 : ℝ) ^ (ℓ + 1)) ⊆ maxSuperlevel F lam →
        eLpNorm (fun x => ∑ P ∈ S, P.coeff ch f * P.wavePacket ch x * P.aP L x) 1
          (volume.restrict (maxSuperlevel F lam)ᶜ) ≤
        ENNReal.ofReal (K * (((2 : ℝ) ^ ℓ)⁻¹) ^ (N - 3) * lam ^ (1 / Real.conjExponent r) *
          I₀.length) := by
  obtain ⟨A, hA0, hA⟩ := Multitile.exists_norm_wavePacket_le N
  obtain ⟨K₄, hK₄0, hK₄⟩ := exists_rpow_sum_norm_coeff_le 2 le_rfl
  refine ⟨2 * A * K₄ * 2 ^ (N - 2), by positivity, ?_⟩
  intro ρ hρ r hr ch L S I₀ hS F f hF hfm hfF lam hlam ℓ hsub hnot
  rcases S.eq_empty_or_nonempty with rfl | ⟨P₀, hP₀⟩
  · simp
  have hr1 : 1 < r := by linarith
  have hP₀I : P₀.I = I₀ := hS P₀ hP₀
  have hL := I₀.length_pos
  set L₀ := I₀.length with hL₀
  set Ω := maxSuperlevel F lam with hΩ
  have hΩm : MeasurableSet Ωᶜ := (measurableSet_maxSuperlevel F lam).compl
  set u : ℝ := 2 ^ ℓ * lam with hu
  have hu0 : 0 < u := by positivity
  -- the `ℓ^r` bound for the coefficients
  set Y : ℝ := (∑ P ∈ S, ‖P.coeff ch f‖ ^ r) ^ (1 / r) with hY
  have hY1 : Y ≤ K₄ * u ^ (1 / Real.conjExponent r) * √L₀ :=
    hK₄ ch S hS hF hfm hfF hlam hnot hr
  -- `1 + |x - c|/|I₀| ≥ 2^ℓ / 2` off `Ω`
  have hoff : ∀ x ∈ Ωᶜ, (2 : ℝ) ^ ℓ / 2 ≤ 1 + |x - I₀.center| / L₀ := by
    intro x hx
    have hxn : x ∉ I₀.dilate ((2 : ℝ) ^ ℓ) := fun h => hx (hsub h)
    have h1 : (2 : ℝ) ^ ℓ * L₀ / 2 ≤ |x - I₀.center| := by
      by_contra hlt
      rw [not_le, abs_lt] at hlt
      exact hxn ⟨by linarith [hlt.1], by linarith [hlt.2]⟩
    have h2 : (2 : ℝ) ^ ℓ / 2 ≤ |x - I₀.center| / L₀ := by
      rw [le_div_iff₀ hL]; linarith
    linarith
  set E : ℝ := (((2 : ℝ) ^ ℓ / 2) ^ (N - 2))⁻¹ with hE
  have hE0 : 0 < E := by positivity
  set w : ℝ → ℝ := fun x => (1 + |x - I₀.center| / L₀) ^ (-2 : ℤ) with hw
  set G : ℝ → ℝ := fun x => Y * (A * (√L₀)⁻¹ * E) * w x with hG
  have hwint : Integrable w := by
    have := integrable_one_add_abs_div_zpow (N := 2) le_rfl I₀.center hL
    have h22 : (-((2 : ℕ) : ℤ)) = -2 := by norm_num
    rw [h22] at this
    exact this
  have hw0 : ∀ x, 0 ≤ w x := fun x => by simp only [hw]; positivity
  have hY0 : 0 ≤ Y := by positivity
  -- the pointwise bound
  have hpt : ∀ x ∈ Ωᶜ, ‖∑ P ∈ S, P.coeff ch f * P.wavePacket ch x * P.aP L x‖ ≤ G x := by
    intro x hx
    have h1 := norm_sum_coeff_mul_aP_le hρ hr1 ch f L S hS hP₀I x
    refine h1.trans ?_
    have h2 := hA ρ ch P₀ x
    rw [hP₀I] at h2
    have h3 : (1 + |x - I₀.center| / L₀) ^ (-(N : ℤ)) ≤ E * w x := by
      have hb : 0 < 1 + |x - I₀.center| / L₀ := by positivity
      have e : (1 + |x - I₀.center| / L₀) ^ (-(N : ℤ)) =
          ((1 + |x - I₀.center| / L₀) ^ (N - 2))⁻¹ * w x := by
        have hN2 : (N : ℤ) = ((N - 2 : ℕ) : ℤ) + 2 := by omega
        rw [hw, hN2, neg_add, zpow_add₀ hb.ne', zpow_neg, zpow_natCast]
      rw [e]
      refine mul_le_mul_of_nonneg_right ?_ (hw0 x)
      exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) (hoff x hx) _)
    calc ‖P₀.wavePacket ch x‖ * Y
        ≤ (A * (√L₀)⁻¹ * (1 + |x - I₀.center| / L₀) ^ (-(N : ℤ))) * Y :=
          mul_le_mul_of_nonneg_right h2 hY0
      _ ≤ (A * (√L₀)⁻¹ * (E * w x)) * Y := by gcongr
      _ = G x := by simp only [hG]; ring
  -- integrate
  have hGint : Integrable G := hwint.const_mul _
  have hGval : ∫ x, G x = Y * (A * (√L₀)⁻¹ * E) * (L₀ * 2) := by
    have h := integral_one_add_abs_div_zpow (N := 2) le_rfl I₀.center hL
    have h22 : (-((2 : ℕ) : ℤ)) = -2 := by norm_num
    rw [h22] at h
    simp only [hG, integral_const_mul]
    rw [show ∫ x, w x = L₀ * (2 / (((2 : ℕ) : ℝ) - 1)) from h]
    norm_num
  rw [eLpNorm_one_eq_lintegral_enorm (measurable_tileSum ch f L S).aestronglyMeasurable]
  calc ∫⁻ x in Ωᶜ, ‖∑ P ∈ S, P.coeff ch f * P.wavePacket ch x * P.aP L x‖ₑ
      ≤ ∫⁻ x in Ωᶜ, ENNReal.ofReal (G x) := by
        refine setLIntegral_mono' hΩm fun x hx => ?_
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hpt x hx)
    _ ≤ ∫⁻ x, ENNReal.ofReal (G x) := setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (∫ x, G x) := by
        rw [ofReal_integral_eq_lintegral_ofReal hGint
          (Filter.Eventually.of_forall fun x => by simp only [hG]; have := hw0 x; positivity)]
    _ ≤ _ := by
        rw [hGval]
        refine ENNReal.ofReal_le_ofReal ?_
        -- `Y (A/√L₀) E (2 L₀) ≤ K ((2^ℓ)⁻¹)^{N-3} λ^{1/r'} L₀`
        have hs : √L₀ * √L₀ = L₀ := Real.mul_self_sqrt hL.le
        have hs0 : 0 < √L₀ := Real.sqrt_pos.2 hL
        set s : ℝ := 1 / Real.conjExponent r with hs_def
        have hs1 : s ≤ 1 := by
          rw [hs_def, one_div_conjExponent_eq hr1]
          have : 0 ≤ 1 / r := by positivity
          linarith
        have hs0' : 0 ≤ s := by
          rw [hs_def, one_div_conjExponent_eq hr1]
          have : 1 / r ≤ 1 := by
            rw [div_le_one (by linarith)]; linarith
          linarith
        have h2l : (1 : ℝ) ≤ 2 ^ ℓ := one_le_pow₀ (by norm_num)
        have hus : u ^ s ≤ 2 ^ ℓ * lam ^ s := by
          rw [hu, Real.mul_rpow (by positivity) hlam.le]
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          calc ((2 : ℝ) ^ ℓ) ^ s ≤ ((2 : ℝ) ^ ℓ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le h2l hs1
            _ = 2 ^ ℓ := Real.rpow_one _
        have hEv : E = 2 ^ (N - 2) * (((2 : ℝ) ^ ℓ)⁻¹) ^ (N - 2) := by
          rw [hE, div_pow, inv_div, inv_pow]
          ring
        have hpow : (2 : ℝ) ^ ℓ * (((2 : ℝ) ^ ℓ)⁻¹) ^ (N - 2) = (((2 : ℝ) ^ ℓ)⁻¹) ^ (N - 3) := by
          obtain ⟨m, rfl⟩ : ∃ m, N = m + 3 := ⟨N - 3, by omega⟩
          have : m + 3 - 2 = (m + 3 - 3) + 1 := by omega
          rw [this, pow_succ]
          have h2 : (2 : ℝ) ^ ℓ ≠ 0 := by positivity
          field_simp
        calc Y * (A * (√L₀)⁻¹ * E) * (L₀ * 2)
            ≤ (K₄ * u ^ s * √L₀) * (A * (√L₀)⁻¹ * E) * (L₀ * 2) := by gcongr
          _ = (K₄ * u ^ s) * A * E * (L₀ * 2) * (√L₀ * (√L₀)⁻¹) := by ring
          _ = (K₄ * u ^ s) * A * E * (L₀ * 2) := by
              rw [mul_inv_cancel₀ hs0.ne', mul_one]
          _ ≤ (K₄ * (2 ^ ℓ * lam ^ s)) * A * E * (L₀ * 2) := by gcongr
          _ = 2 * A * K₄ * 2 ^ (N - 2) *
                ((2 ^ ℓ * (((2 : ℝ) ^ ℓ)⁻¹) ^ (N - 2)) * lam ^ s * L₀) := by
              rw [hEv]; ring
          _ = 2 * A * K₄ * 2 ^ (N - 2) * ((((2 : ℝ) ^ ℓ)⁻¹) ^ (N - 3) * lam ^ s * L₀) := by
              rw [hpow]
          _ = _ := by ring

end PrimeCarleson.Proof.Oplus
