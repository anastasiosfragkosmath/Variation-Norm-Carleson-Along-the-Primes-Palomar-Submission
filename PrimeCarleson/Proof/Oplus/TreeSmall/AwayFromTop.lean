module

public import PrimeCarleson.Proof.Oplus.TreeSmall.SmallIntervals

/-!
# The estimate away from the top ([O+] L2127-L2135)

Source: [O+] `treeestimate`, L2127–L2135:
"We now use (treeestimatesmallintervals) to prove
(treeestimateaway) for `ℓ ≥ 4`. Indeed, using the maximality of each `J`, we see that if `ℓ ≥ 4`
and `J ∩ (ℝ ∖ 2^ℓ I_T) ≠ ∅` then `dist(I_T, J) ≥ |J|/2` and `|J| ≥ 2^{ℓ-3}|I_T|`. [...]
Summing over all `J`, we thus obtain (treeestimateaway) for `ℓ ≥ 4`."

* `integral_far_weight`: `∫_{|x - c| ≥ R} (1 + |x - c|/L)^{-n} dx = 2L/(n-1) (1 + R/L)^{-(n-1)}`;
* `tsum_length_mul_le`: the sum `∑_J |J| F_J` over pairwise disjoint dyadic intervals `J` with
  `F_J ≤ W (1 + |x - c|/L)^{-n}` on `J` and `|x - c| ≥ R` on `J` is bounded by the integral;
* `treeestimate_away_from_top`: for `ℓ ≥ 4`, the `L^q` norm of the tree sum over `ℝ ∖ 2^ℓ I_T` is at
  most `K 2^{-ℓ(N-10)} ene den^{min(1, r'/q)} |I_T|^{1/q}`. The proof splits `ℝ ∖ 2^ℓ I_T` into the
  intervals `J ∈ 𝒥` meeting it (for which, by the maximality of `J`, `|J| ≥ (2^{ℓ-1} - 1/2)|I_T|/4`
  and `|J| ≤ 3 dist(I_T, J)`, so that every multitile has `|I| < C''|J|` and the small-interval
  estimate applies to the whole tree), applies the small-interval estimate with exponent `2N`
  (so that the `q`-th power of the decay is integrable with enough room) and sums over `J` by
  comparing `|J| (1 + dist(I_T, J)/|I_T|)^{-n}` with the integral of the weight over `J`.
  The constants `3` and `4` replace the printed `2` and `2^{ℓ-3}` (the source's displayed
  bounds are slightly too strong for `ℓ = 4`); the conclusion is the printed one.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

section FarIntegral

/-- **The weight away from the centre**: for `n ≥ 2`, `R, L > 0`,
`∫_{x ≤ c - R or x ≥ c + R} (1 + |x - c|/L)^{-n} dx = L · 2/(n-1) · (1 + R/L)^{-(n-1)}`. -/
theorem integral_far_weight {n : ℕ} (hn : 2 ≤ n) (c : ℝ) {L R : ℝ} (hL : 0 < L) (hR : 0 < R) :
    ∫ x in Iic (c - R) ∪ Ici (c + R), (1 + |x - c| / L) ^ (-(n : ℤ)) =
      L * (2 * (1 / ((n : ℝ) - 1)) * (1 + R / L) ^ (-((n : ℤ) - 1))) := by
  have hg : Integrable (fun x : ℝ => (1 + |x - c| / L) ^ (-(n : ℤ))) :=
    integrable_one_add_abs_div_zpow hn c hL
  have hdisj : Disjoint (Iic (c - R)) (Ici (c + R)) :=
    Set.disjoint_left.2 fun y hy hy' => by
      have := hy.out; have := hy'.out; linarith
  have hconv : ∀ s : Set ℝ, ∫ x in s, (1 + |x - c| / L) ^ (-(n : ℤ)) =
      L * ∫ x in s, L⁻¹ * (1 + |x - c| / L) ^ (-(n : ℤ)) := by
    intro s
    rw [integral_const_mul, ← mul_assoc, mul_inv_cancel₀ hL.ne', one_mul]
  have hL' := integral_Iio_inv_mul_one_add_abs_div_zpow hn c hL (p := c - R) (by linarith)
  have hR' := integral_Ioi_inv_mul_one_add_abs_div_zpow hn c hL (q := c + R) (by linarith)
  rw [setIntegral_union hdisj measurableSet_Ici hg.integrableOn hg.integrableOn,
    integral_Iic_eq_integral_Iio, integral_Ici_eq_integral_Ioi, hconv, hconv, hL', hR']
  have e1 : c - (c - R) = R := by ring
  have e2 : c + R - c = R := by ring
  rw [e1, e2]
  ring

/-- **A sum over disjoint dyadic intervals is controlled by an integral.** If the `J ∈ X` are
pairwise disjoint, `|x - c| ≥ R > 0` on each `J ∈ X`, and `F_J ≤ W (1 + |x - c|/L)^{-n}` for
`x ∈ J`, then `∑_{J ∈ X} |J| F_J ≤ W L (2/(n-1)) (1 + R/L)^{-(n-1)}`. -/
theorem tsum_length_mul_le {X : Set Dyadic} (hdisj : X.PairwiseDisjoint Dyadic.toSet)
    {c L R : ℝ} (hL : 0 < L) (hR : 0 < R) {n : ℕ} (hn : 2 ≤ n) {W : ℝ} (hW : 0 ≤ W)
    (F : Dyadic → ℝ) (hF : ∀ J ∈ X, ∀ x ∈ J.toSet, F J ≤ W * (1 + |x - c| / L) ^ (-(n : ℤ)))
    (hfar : ∀ J ∈ X, ∀ x ∈ J.toSet, R ≤ |x - c|) :
    ∑' J : X, ENNReal.ofReal (J.1.length * F J.1) ≤
      ENNReal.ofReal (W * (L * (2 * (1 / ((n : ℝ) - 1)) * (1 + R / L) ^ (-((n : ℤ) - 1))))) := by
  have : Countable X := (Set.to_countable X).to_subtype
  set G : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (W * (1 + |x - c| / L) ^ (-(n : ℤ))) with hG
  have hstep : ∀ J : X, ENNReal.ofReal (J.1.length * F J.1) ≤ ∫⁻ x in J.1.toSet, G x := by
    intro J
    have h1 : ENNReal.ofReal (J.1.length * F J.1) = ∫⁻ x in J.1.toSet, ENNReal.ofReal (F J.1) := by
      rw [setLIntegral_const, Dyadic.volume_toSet, ENNReal.ofReal_mul J.1.length_pos.le, mul_comm]
    rw [h1]
    refine setLIntegral_mono' J.1.measurableSet_toSet fun x hx => ?_
    exact ENNReal.ofReal_le_ofReal (hF J.1 J.2 x hx)
  have hdisj' : Pairwise (Function.onFun Disjoint fun J : X => J.1.toSet) := fun J J' hne =>
    hdisj J.2 J'.2 fun h => hne (Subtype.ext h)
  have hsub : (⋃ J : X, J.1.toSet) ⊆ Iic (c - R) ∪ Ici (c + R) := by
    intro x hx
    obtain ⟨J, hxJ⟩ := Set.mem_iUnion.1 hx
    have := hfar J.1 J.2 x hxJ
    rw [le_abs] at this
    rcases this with h | h
    · right; exact Set.mem_Ici.2 (by linarith)
    · left; exact Set.mem_Iic.2 (by linarith)
  have hint : Integrable (fun x : ℝ => W * (1 + |x - c| / L) ^ (-(n : ℤ))) :=
    (integrable_one_add_abs_div_zpow hn c hL).const_mul W
  calc ∑' J : X, ENNReal.ofReal (J.1.length * F J.1)
      ≤ ∑' J : X, ∫⁻ x in J.1.toSet, G x := ENNReal.tsum_le_tsum hstep
    _ = ∫⁻ x in ⋃ J : X, J.1.toSet, G x :=
        (lintegral_iUnion (fun J => J.1.measurableSet_toSet) hdisj' G).symm
    _ ≤ ∫⁻ x in Iic (c - R) ∪ Ici (c + R), G x := lintegral_mono_set hsub
    _ = ENNReal.ofReal (∫ x in Iic (c - R) ∪ Ici (c + R),
          W * (1 + |x - c| / L) ^ (-(n : ℤ))) := by
        rw [ofReal_integral_eq_lintegral_ofReal hint.integrableOn
          (Filter.Eventually.of_forall fun x => by positivity)]
    _ = _ := by
        rw [integral_const_mul, integral_far_weight hn c hL hR]

end FarIntegral

section AwayMain

/-- The real inequality behind the decay `2^{-ℓ(N-10)}`: for `X = 2^ℓ ≥ 16` and `1 ≤ q ≤ 2`,
`(c (1 + (X-1)/24)^{-m})^{1/q} ≤ c 24^m X^{-(N-10)}` when `c ≥ 1` and `q(N - 10) ≤ m`. -/
theorem away_real_bound {q : ℝ} (hq1 : 1 ≤ q) {N m : ℕ} (hm : q * ((N : ℝ) - 10) ≤ m) {X : ℝ}
    (hX : 16 ≤ X) {c : ℝ} (hc : 1 ≤ c) :
    (c * (1 + (X - 1) / 24) ^ (-(m : ℤ))) ^ (1 / q) ≤ (c * 24 ^ m) * X ^ (-((N : ℤ) - 10)) := by
  have hq0 : 0 < q := by linarith
  have hXpos : 0 < X := by linarith
  have hY : X / 24 ≤ 1 + (X - 1) / 24 := by linarith
  have hY0 : 0 < 1 + (X - 1) / 24 := by linarith
  have h1 : (1 + (X - 1) / 24) ^ (-(m : ℤ)) ≤ 24 ^ m * X ^ (-(m : ℤ)) := by
    rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
    calc ((1 + (X - 1) / 24) ^ m)⁻¹ ≤ ((X / 24) ^ m)⁻¹ :=
          inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hY m)
      _ = 24 ^ m * (X ^ m)⁻¹ := by rw [div_pow, inv_div, div_eq_mul_inv]
  have hP : 1 ≤ c * 24 ^ m := by
    have : (1 : ℝ) ≤ 24 ^ m := one_le_pow₀ (by norm_num)
    exact one_le_mul_of_one_le_of_one_le hc this
  have hXm : 0 ≤ X ^ (-(m : ℤ)) := by positivity
  have h2 : c * (1 + (X - 1) / 24) ^ (-(m : ℤ)) ≤ (c * 24 ^ m) * X ^ (-(m : ℤ)) := by
    calc c * (1 + (X - 1) / 24) ^ (-(m : ℤ)) ≤ c * (24 ^ m * X ^ (-(m : ℤ))) :=
          mul_le_mul_of_nonneg_left h1 (by linarith)
      _ = _ := by ring
  calc (c * (1 + (X - 1) / 24) ^ (-(m : ℤ))) ^ (1 / q)
      ≤ ((c * 24 ^ m) * X ^ (-(m : ℤ))) ^ (1 / q) :=
        Real.rpow_le_rpow (mul_nonneg (by linarith) (zpow_nonneg hY0.le _)) h2 (by positivity)
    _ = (c * 24 ^ m) ^ (1 / q) * (X ^ (-(m : ℤ))) ^ (1 / q) :=
        Real.mul_rpow (by positivity) hXm
    _ ≤ (c * 24 ^ m) * X ^ (-((N : ℤ) - 10)) := by
        have e1 : (c * 24 ^ m) ^ (1 / q) ≤ c * 24 ^ m := by
          calc (c * 24 ^ m) ^ (1 / q) ≤ (c * 24 ^ m) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le hP (by rw [div_le_one hq0]; exact hq1)
            _ = _ := Real.rpow_one _
        have e2 : (X ^ (-(m : ℤ))) ^ (1 / q) ≤ X ^ (-((N : ℤ) - 10)) := by
          rw [← Real.rpow_intCast X (-(m : ℤ)), ← Real.rpow_mul hXpos.le,
            ← Real.rpow_intCast X (-((N : ℤ) - 10))]
          refine Real.rpow_le_rpow_of_exponent_le (by linarith) ?_
          push_cast
          rw [neg_mul, one_div, ← div_eq_mul_inv, neg_le_neg_iff, le_div_iff₀ hq0]
          linarith
        have e3 : 0 ≤ (X ^ (-(m : ℤ))) ^ (1 / q) := by positivity
        exact mul_le_mul e1 e2 e3 (by positivity)

end AwayMain

section AwayTheorem

variable {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ C₃ : ℝ} {M : ℤ}

/-- For `x ∈ J ∈ 𝒥` far from the top: `1 + |x - c(I_T)|/|I_T| ≤ 4 (1 + dist(I_T, J)/|I_T|)`
(because `|J| ≤ 3 dist(I_T, J)`). -/
theorem one_add_abs_sub_center_le_four (I J : Dyadic) {x : ℝ} (hx : x ∈ J.toSet)
    (hJ : J.length ≤ 3 * I.dist J) :
    1 + |x - I.center| / I.length ≤ 4 * (1 + I.dist J / I.length) := by
  have hI := I.length_pos
  have h1 := Dyadic.abs_sub_center_le_dist (I := I) hx
  have h2 : |x - I.center| / I.length ≤ 4 * (I.dist J / I.length) + 1 / 2 := by
    rw [div_le_iff₀ hI]
    have : (4 * (I.dist J / I.length) + 1 / 2) * I.length = 4 * I.dist J + I.length / 2 := by
      field_simp
    rw [this]
    linarith
  have h3 : 0 ≤ I.dist J / I.length := div_nonneg (I.dist_nonneg J) hI.le
  linarith

/-- **`treeestimate`** ([O+] L2127-L2135, estimate (treeestimateaway) for `ℓ ≥ 4`).
Let `r ≥ 2`, `1 ≤ q ≤ 2`, `N ≥ 11`. There is a constant `K` such that for every tree `T ⊂ S` of
multitiles in the square `[-2^M, 2^M]²` with the separation assumptions, `energy(S) ≤ ene`,
`density(S) ≤ den`, and every `ℓ ≥ 4`,
`‖∑_{P ∈ T} ⟨f, φ_P⟩ φ_P a_P 1_E‖_{L^q(ℝ ∖ 2^ℓ I_T)} ≤
K 2^{-ℓ(N-10)} ene den^{min(1, r'/q)} |I_T|^{1/q}`. -/
theorem treeestimate_away_from_top {r q : ℝ} (hr : 2 ≤ r) (hq1 : 1 ≤ q) (hq2 : q ≤ 2) (N : ℕ)
    (hN : 11 ≤ N) {C₁ C₂ C₃ : ℝ} (hC : AdmissibleConstants C₁ C₂ C₃) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {ρ : Idx} [Fact ρ.IsOneOrTwo] {M : ℤ}, ρ.IsStd → ∀ (ch : ProfileChoice)
      (f : ℝ → ℂ) {E : Set ℝ}, MeasurableSet E → ∀ (L : Linearization r) {S : Set (Multitile ρ)}
      {ene den : ℝ}, 0 ≤ ene → 0 ≤ den → energy C₁ C₂ M ch f S ≤ ENNReal.ofReal ene →
      density C₁ C₂ M L E S ≤ ENNReal.ofReal den → ∀ (𝒯 : MultitileTree ρ),
      𝒯.IsTree C₁ C₂ M → (∀ P ∈ 𝒯.T, P.InSquare M) → (𝒯.T : Set (Multitile ρ)) ⊆ S →
      Separated C₁ C₂ C₃ (𝒯.T : Set (Multitile ρ)) → ∀ {ℓ : ℕ}, 4 ≤ ℓ →
        eLpNorm (treeSum ch f L E 𝒯.T) (ENNReal.ofReal q)
            (volume.restrict (𝒯.I.dilate ((2 : ℝ) ^ ℓ))ᶜ) ≤
          ENNReal.ofReal (K * ((2 : ℝ) ^ ℓ) ^ (-((N : ℤ) - 10)) * ene *
            den ^ (min 1 (Real.conjExponent r / q)) * 𝒯.I.length ^ (1 / q)) := by
  classical
  have hr1 : 1 < r := by linarith
  have hq0 : 0 < q := by linarith
  obtain ⟨K₀, hK₀0, hK₀⟩ := treeestimate_small_intervals hr hq1 hq2 (2 * N) (by omega) hC
  obtain ⟨m, hm⟩ : ∃ m : ℕ, 2 * N = m + 7 := ⟨2 * N - 7, by omega⟩
  have hm2 : 2 ≤ m + 1 := by omega
  set c₂ : ℝ := 4 ^ (m + 1) * (2 * (1 / (((m + 1 : ℕ) : ℝ) - 1))) with hc₂
  have hmpos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) - 1 := by
    have : (1 : ℝ) < ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < m + 1)
    linarith
  have hc₂1 : 1 ≤ c₂ := by
    rw [hc₂]
    have h4 : ((m + 1 : ℕ) : ℝ) - 1 ≤ 4 ^ (m + 1) := by
      have : m + 1 < 4 ^ (m + 1) := Nat.lt_pow_self (by norm_num)
      have h' : ((m + 1 : ℕ) : ℝ) < 4 ^ (m + 1) := by exact_mod_cast this
      linarith
    have e : (4 : ℝ) ^ (m + 1) * (2 * (1 / (((m + 1 : ℕ) : ℝ) - 1))) =
        2 * (4 ^ (m + 1) / (((m + 1 : ℕ) : ℝ) - 1)) := by ring
    rw [e]
    have : 1 ≤ (4 : ℝ) ^ (m + 1) / (((m + 1 : ℕ) : ℝ) - 1) := by
      rw [le_div_iff₀ hmpos]; linarith
    linarith
  refine ⟨K₀ * (c₂ * 24 ^ m), by positivity, ?_⟩
  intro ρ _ M hρ ch f E hE L S ene den hene hden hen hde 𝒯 hT hsq hsub hsep ℓ hℓ
  by_cases hne : 𝒯.T.Nonempty
  swap
  · have : treeSum ch f L E 𝒯.T = 0 := by
      rw [Finset.not_nonempty_iff_eq_empty.1 hne]
      funext x
      simp [treeSum]
    rw [this]
    simp
  set X : ℝ := (2 : ℝ) ^ ℓ with hX
  have hX16 : (16 : ℝ) ≤ X := by
    calc (16 : ℝ) = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ ℓ := pow_le_pow_right₀ (by norm_num) hℓ
  have hLt := 𝒯.I.length_pos
  set Lt := 𝒯.I.length with hLtdef
  have hX1 : 0 < (X - 1) / 24 := by linarith
  set R : ℝ := (X - 1) / 24 * Lt with hRdef
  have hRpos : 0 < R := by positivity
  set U := (𝒯.I.dilate X)ᶜ with hUdef
  set σ := min 1 (Real.conjExponent r / q) with hσ
  have hσ0 : 0 ≤ σ := by
    have hr' : 0 < Real.conjExponent r := by
      unfold Real.conjExponent
      exact div_pos (by linarith) (by linarith)
    rw [hσ]
    exact le_min zero_le_one (by positivity)
  set A₀ : ℝ := K₀ * ene * den ^ σ with hA₀
  have hA₀0 : 0 ≤ A₀ := by positivity
  set X𝒥 : Set Dyadic := {J | 𝒯.IsMaxAvoiding J ∧ (J.toSet ∩ U).Nonempty} with hX𝒥
  have : Countable X𝒥 := (Set.to_countable _).to_subtype
  have hexp : (-(((2 * N : ℕ) : ℤ) - 6)) = -((m + 1 : ℕ) : ℤ) := by
    have := hm; push_cast; omega
  -- the bound on each `J`
  have hper : ∀ J ∈ X𝒥, ∫⁻ x in J.toSet, ‖treeSum ch f L E 𝒯.T x‖ₑ ^ q ≤
      ENNReal.ofReal (A₀ ^ q) * ENNReal.ofReal (J.length *
        (1 + 𝒯.I.dist J / Lt) ^ (-((m + 1 : ℕ) : ℤ))) := by
    intro J hJ
    obtain ⟨hJmax, hmeet⟩ := hJ
    obtain ⟨hfar1, hfar2⟩ := MultitileTree.exists_far_bounds hJmax hT.time hℓ hmeet
    have hJpos := J.length_pos
    have hfilter : 𝒯.T.filter (fun P => P.I.length < Cpp C₁ C₂ * J.length) = 𝒯.T := by
      refine Finset.filter_true_of_mem fun P hP => ?_
      have hPT : P.I.length ≤ Lt :=
        Dyadic.length_le_iff.2 (Dyadic.k_le_of_toSet_subset (hT.time P hP))
      have h8 := eight_le_Cpp hC
      have hfar1' : (X / 2 - 1 / 2) * Lt ≤ 4 * J.length := hfar1
      have h16 : (15 / 2) * Lt ≤ (X / 2 - 1 / 2) * Lt :=
        mul_le_mul_of_nonneg_right (by linarith only [hX16]) hLt.le
      have h8J := mul_le_mul_of_nonneg_right h8 hJpos.le
      linarith only [hPT, h16, hfar1', h8J, hJpos, hLt]
    have hcore := hK₀ hρ ch f hE L hene hden hen hde 𝒯 hT hsq hsub hsep hJmax.1
    rw [hfilter, hexp] at hcore
    have hmeasJ : AEStronglyMeasurable (treeSum ch f L E 𝒯.T) (volume.restrict J.toSet) :=
      (measurable_treeSum ch f L hE _).aestronglyMeasurable
    have heq : ∫⁻ x in J.toSet, ‖treeSum ch f L E 𝒯.T x‖ₑ ^ q =
        (eLpNorm (treeSum ch f L E 𝒯.T) (ENNReal.ofReal q) (volume.restrict J.toSet)) ^ q := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hq0).ne'
        ENNReal.ofReal_ne_top hmeasJ, ENNReal.toReal_ofReal hq0.le, ← ENNReal.rpow_mul,
        one_div_mul_cancel hq0.ne', ENNReal.rpow_one]
    rw [heq]
    have hAJ : 1 ≤ 1 + 𝒯.I.dist J / Lt := by
      have : 0 ≤ 𝒯.I.dist J / Lt := div_nonneg (𝒯.I.dist_nonneg J) hLt.le
      linarith
    have hFpos : 0 < (1 + 𝒯.I.dist J / Lt) ^ (-((m + 1 : ℕ) : ℤ)) := by positivity
    have hF1 : (1 + 𝒯.I.dist J / Lt) ^ (-((m + 1 : ℕ) : ℤ)) ≤ 1 :=
      zpow_le_one_of_nonpos₀ hAJ (by omega)
    have hB0 : 0 ≤ K₀ * ene * den ^ σ * J.length ^ (1 / q) *
        (1 + 𝒯.I.dist J / Lt) ^ (-((m + 1 : ℕ) : ℤ)) := by positivity
    have hBq : (K₀ * ene * den ^ σ * J.length ^ (1 / q) *
        (1 + 𝒯.I.dist J / Lt) ^ (-((m + 1 : ℕ) : ℤ))) ^ q ≤
        A₀ ^ q * (J.length * (1 + 𝒯.I.dist J / Lt) ^ (-((m + 1 : ℕ) : ℤ))) := by
      rw [Real.mul_rpow (by positivity) hFpos.le, Real.mul_rpow hA₀0 (by positivity),
        ← Real.rpow_mul hJpos.le, one_div_mul_cancel hq0.ne', Real.rpow_one, mul_assoc]
      gcongr
      calc ((1 + 𝒯.I.dist J / Lt) ^ (-((m + 1 : ℕ) : ℤ))) ^ q
          ≤ ((1 + 𝒯.I.dist J / Lt) ^ (-((m + 1 : ℕ) : ℤ))) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_ge hFpos hF1 hq1
        _ = _ := Real.rpow_one _
    calc (eLpNorm (treeSum ch f L E 𝒯.T) (ENNReal.ofReal q) (volume.restrict J.toSet)) ^ q
        ≤ (ENNReal.ofReal (K₀ * ene * den ^ σ * J.length ^ (1 / q) *
            (1 + 𝒯.I.dist J / Lt) ^ (-((m + 1 : ℕ) : ℤ)))) ^ q :=
          ENNReal.rpow_le_rpow hcore hq0.le
      _ = ENNReal.ofReal ((K₀ * ene * den ^ σ * J.length ^ (1 / q) *
            (1 + 𝒯.I.dist J / Lt) ^ (-((m + 1 : ℕ) : ℤ))) ^ q) :=
          ENNReal.ofReal_rpow_of_nonneg hB0 hq0.le
      _ ≤ ENNReal.ofReal (A₀ ^ q * (J.length *
            (1 + 𝒯.I.dist J / Lt) ^ (-((m + 1 : ℕ) : ℤ)))) := ENNReal.ofReal_le_ofReal hBq
      _ = _ := ENNReal.ofReal_mul (by positivity)
  -- the covering of `U` and the sum over `J`
  have hcover : U ⊆ ⋃ J : X𝒥, J.1.toSet := by
    intro x hx
    obtain ⟨J, hJ, hxJ⟩ := MultitileTree.exists_isMaxAvoiding_mem hne x
    exact Set.mem_iUnion.2 ⟨⟨J, hJ, ⟨x, hxJ, hx⟩⟩, hxJ⟩
  have hdisj : X𝒥.PairwiseDisjoint Dyadic.toSet := fun J hJ J' hJ' hne' =>
    hJ.1.disjoint hJ'.1 hne'
  have hfar : ∀ J ∈ X𝒥, ∀ x ∈ J.toSet, R ≤ |x - 𝒯.I.center| := by
    intro J hJ x hx
    obtain ⟨hfar1, hfar2⟩ := MultitileTree.exists_far_bounds hJ.1 hT.time hℓ hJ.2
    have h1 := Dyadic.dist_le_abs_sub_center (I := 𝒯.I) hx
    rw [abs_sub_comm] at h1
    have : R ≤ J.length / 3 := by
      rw [hRdef]
      linarith
    linarith
  have hF : ∀ J ∈ X𝒥, ∀ x ∈ J.toSet, (1 + 𝒯.I.dist J / Lt) ^ (-((m + 1 : ℕ) : ℤ)) ≤
      4 ^ (m + 1) * (1 + |x - 𝒯.I.center| / Lt) ^ (-((m + 1 : ℕ) : ℤ)) := by
    intro J hJ x hx
    obtain ⟨hfar1, hfar2⟩ := MultitileTree.exists_far_bounds hJ.1 hT.time hℓ hJ.2
    have h4 := one_add_abs_sub_center_le_four 𝒯.I J hx hfar2
    have hd := 𝒯.I.dist_nonneg J
    have hdL : 0 ≤ 𝒯.I.dist J / Lt := div_nonneg hd hLt.le
    have hpa : 0 < (1 + 𝒯.I.dist J / Lt) ^ (m + 1) := by positivity
    have hpb : 0 < (1 + |x - 𝒯.I.center| / Lt) ^ (m + 1) := by positivity
    rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, inv_eq_one_div, inv_eq_one_div,
      mul_one_div, div_le_div_iff₀ hpa hpb]
    calc 1 * (1 + |x - 𝒯.I.center| / Lt) ^ (m + 1)
        ≤ (4 * (1 + 𝒯.I.dist J / Lt)) ^ (m + 1) := by
          rw [one_mul]; exact pow_le_pow_left₀ (by positivity) h4 _
      _ = _ := by rw [mul_pow]
  have hsum := tsum_length_mul_le (X := X𝒥) (c := 𝒯.I.center) hdisj hLt hRpos
    (n := m + 1) hm2 (W := 4 ^ (m + 1)) (by positivity)
    (fun J => (1 + 𝒯.I.dist J / Lt) ^ (-((m + 1 : ℕ) : ℤ))) hF hfar
  have hmeasU : AEStronglyMeasurable (treeSum ch f L E 𝒯.T) (volume.restrict U) :=
    (measurable_treeSum ch f L hE _).aestronglyMeasurable
  have htot : ∫⁻ x in U, ‖treeSum ch f L E 𝒯.T x‖ₑ ^ q ≤ ENNReal.ofReal (A₀ ^ q) *
      ENNReal.ofReal (4 ^ (m + 1) * (Lt * (2 * (1 / (((m + 1 : ℕ) : ℝ) - 1)) *
        (1 + R / Lt) ^ (-(((m + 1 : ℕ) : ℤ) - 1))))) := by
    calc ∫⁻ x in U, ‖treeSum ch f L E 𝒯.T x‖ₑ ^ q
        ≤ ∫⁻ x in ⋃ J : X𝒥, J.1.toSet, ‖treeSum ch f L E 𝒯.T x‖ₑ ^ q :=
          lintegral_mono_set hcover
      _ ≤ ∑' J : X𝒥, ∫⁻ x in J.1.toSet, ‖treeSum ch f L E 𝒯.T x‖ₑ ^ q :=
          lintegral_iUnion_le _ _
      _ ≤ ∑' J : X𝒥, ENNReal.ofReal (A₀ ^ q) * ENNReal.ofReal (J.1.length *
          (1 + 𝒯.I.dist J.1 / Lt) ^ (-((m + 1 : ℕ) : ℤ))) :=
          ENNReal.tsum_le_tsum fun J => hper J.1 J.2
      _ = ENNReal.ofReal (A₀ ^ q) * ∑' J : X𝒥, ENNReal.ofReal (J.1.length *
          (1 + 𝒯.I.dist J.1 / Lt) ^ (-((m + 1 : ℕ) : ℤ))) := ENNReal.tsum_mul_left
      _ ≤ _ := by gcongr
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hq0).ne'
    ENNReal.ofReal_ne_top hmeasU, ENNReal.toReal_ofReal hq0.le]
  have hq' : 0 ≤ 1 / q := by positivity
  refine (ENNReal.rpow_le_rpow htot hq').trans ?_
  have hY0 : 0 < 1 + (X - 1) / 24 := by linarith
  have hRL : R / Lt = (X - 1) / 24 := by rw [hRdef]; field_simp
  have hexp2 : (-(((m + 1 : ℕ) : ℤ) - 1)) = -(m : ℤ) := by push_cast; ring
  have hZ : 4 ^ (m + 1) * (Lt * (2 * (1 / (((m + 1 : ℕ) : ℝ) - 1)) *
        (1 + R / Lt) ^ (-(((m + 1 : ℕ) : ℤ) - 1)))) =
      Lt * (c₂ * (1 + (X - 1) / 24) ^ (-(m : ℤ))) := by
    rw [hRL, hexp2, hc₂]; ring
  rw [hZ, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_rpow_of_nonneg (by positivity) hq']
  refine ENNReal.ofReal_le_ofReal ?_
  have hmN : q * ((N : ℝ) - 10) ≤ (m : ℝ) := by
    have h1 : (m : ℝ) = 2 * N - 7 := by
      have : (2 * N : ℝ) = (m : ℝ) + 7 := by exact_mod_cast hm
      linarith
    have h2 : (11 : ℝ) ≤ N := by exact_mod_cast hN
    have h3 := mul_le_mul_of_nonneg_right hq2 (by linarith only [h2] : (0 : ℝ) ≤ (N : ℝ) - 10)
    linarith only [h3, h1]
  have hW := away_real_bound (q := q) hq1 (N := N) (m := m) hmN hX16 hc₂1
  have hW0 : 0 ≤ c₂ * (1 + (X - 1) / 24) ^ (-(m : ℤ)) := by positivity
  calc (A₀ ^ q * (Lt * (c₂ * (1 + (X - 1) / 24) ^ (-(m : ℤ))))) ^ (1 / q)
      = A₀ * (Lt ^ (1 / q) * (c₂ * (1 + (X - 1) / 24) ^ (-(m : ℤ))) ^ (1 / q)) := by
        rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hA₀0,
          mul_one_div_cancel hq0.ne', Real.rpow_one, Real.mul_rpow hLt.le hW0]
    _ ≤ A₀ * (Lt ^ (1 / q) * ((c₂ * 24 ^ m) * X ^ (-((N : ℤ) - 10)))) := by gcongr
    _ = _ := by rw [hA₀]; ring

end AwayTheorem

end PrimeCarleson.Proof.Oplus
