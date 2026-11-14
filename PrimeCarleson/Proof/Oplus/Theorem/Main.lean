module

public import PrimeCarleson.Proof.Oplus.Theorem.Linearized
public import PrimeCarleson.Proof.Oplus.Theorem.ChainLin

/-!
# Theorem 1.2 of [O+]: the strong `L^p(V^r)` bound for Schwartz functions

Source: [O+] `maintheorem`, L693–L705; [O+] `maintheorem`, L693–L696; [O+], L884–L890
(L693-L705 and L879-L903, in the amended form used here).

* `lintegral_chainSup_le`: for a finite set `Ξ` free of dyadic end points, the chain supremum
  `G^Ξ_{J+1}` is measurable with `∫ (G^Ξ_{J+1})^p ≤ (C ‖f‖_p)^p`, by the linearized theorem
  (the bound for a finite `Ξ`);
* `lintegral_chainSup_univ_le`: the same for `G_{J+1}`, the supremum over all chains in `ℝ`
  (the bound for fixed `K`): `G_{J+1} = sup_n G^{Ξ_n}_{J+1}` for the finite sets
  `Ξ_n ↑ {q + √2}` (`chainSup_univ_le_of_dense`), and monotone convergence in `n`;
* `strong_proved_range`: for `r' < p < 2r/(r-2)`, `‖V^r 𝒮[f]‖_{L^p} ≤ C ‖f‖_{L^p}`, by monotone
  convergence in `J` (`G_J ≤ G_{J+1}`);
* `variation_strong_all_p`: every `r > 2`, `p > r'`: for `p ≥ 2r/(r-2)` use `V^r ≤ V^{r̃}` with
  `r̃ ∈ (2, min(r, 2p/(p-2)))` (`rVariationOn_anti_exponent`) and the previous case at `(p, r̃)`;
* `variation_norm_carleson_real_proof`: the statement of `variation_norm_carleson_real`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped FourierTransform SchwartzMap ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

open PrimeCarleson PrimeCarleson.Proof.Common

/-- `∫ ‖g‖^p = ‖g‖_p^p`. -/
theorem lintegral_enorm_rpow_eq {g : ℝ → ℂ} (hg : AEStronglyMeasurable g volume) {p : ℝ}
    (hp : 0 < p) : ∫⁻ x, ‖g x‖ₑ ^ p = eLpNorm g (ENNReal.ofReal p) volume ^ p := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp [hp]) (by simp) hg,
    ENNReal.toReal_ofReal hp.le, ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp.ne',
    ENNReal.rpow_one]

/-- Monotone convergence for `p`-th powers of a monotone sequence of measurable functions. -/
theorem lintegral_iSup_rpow {p : ℝ} (hp : 0 < p) {F : ℕ → ℝ → ℝ≥0∞} (hF : ∀ n, Measurable (F n))
    (hmono : Monotone F) : ∫⁻ x, (⨆ n, F n x) ^ p = ⨆ n, ∫⁻ x, F n x ^ p := by
  have h : ∀ x, (⨆ n, F n x) ^ p = ⨆ n, F n x ^ p := fun x =>
    (ENNReal.monotone_rpow_of_nonneg hp.le).map_iSup_of_continuousAt
      (ENNReal.continuous_rpow_const (y := p)).continuousAt (ENNReal.zero_rpow_of_pos hp)
  simp_rw [h]
  exact lintegral_iSup (fun n => (hF n).pow_const p)
    (fun m n hmn x => ENNReal.rpow_le_rpow (hmono hmn x) hp.le)

/-- **The strict finite-`Ξ` bound**: the chain supremum
over a finite set `Ξ` free of dyadic end points is measurable and bounded in `L^p`, by the
linearized bound. -/
theorem lintegral_chainSup_le {r p C : ℝ} (hr : 2 < r) (hp : 0 < p)
    (hC : ∀ (L : Linearization r), AvoidsDyadicEndpoints (L.Ξ : Set ℝ) → ∀ f : 𝓢(ℝ, ℂ),
      eLpNorm (L.op f) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C * eLpNorm (⇑f) (ENNReal.ofReal p) volume)
    (f : 𝓢(ℝ, ℂ)) (Ξ : Finset ℝ) (hΞ : AvoidsDyadicEndpoints (Ξ : Set ℝ)) (J : ℕ) :
    Measurable (chainSup r f (J + 1) (↑Ξ : Set ℝ)) ∧
      ∫⁻ x, chainSup r f (J + 1) (↑Ξ : Set ℝ) x ^ p ≤
        (ENNReal.ofReal C * eLpNorm (⇑f) (ENNReal.ofReal p) volume) ^ p := by
  rcases exists_linearization_chainSup hr f Ξ J with h0 | ⟨L, hLΞ, hL⟩
  · have : chainSup r f (J + 1) (↑Ξ : Set ℝ) = fun _ => 0 := funext h0
    rw [this]
    refine ⟨measurable_const, ?_⟩
    simp [ENNReal.zero_rpow_of_pos hp]
  · have hfun : chainSup r f (J + 1) (↑Ξ : Set ℝ) = fun x => ‖L.op f x‖ₑ := funext hL
    rw [hfun]
    refine ⟨(L.measurable_op f).enorm, ?_⟩
    have hav : AvoidsDyadicEndpoints (L.Ξ : Set ℝ) := by rw [hLΞ]; exact hΞ
    rw [lintegral_enorm_rpow_eq (L.measurable_op f).aestronglyMeasurable hp]
    exact ENNReal.rpow_le_rpow (hC L hav f) hp.le

/-- **The fixed-`K` bound**: the supremum `G_{J+1}` over all chains
in `ℝ` is measurable with `∫ G_{J+1}^p ≤ (C ‖f‖_p)^p`. -/
theorem lintegral_chainSup_univ_le {r p C : ℝ} (hr : 2 < r) (hp : 0 < p)
    (hC : ∀ (L : Linearization r), AvoidsDyadicEndpoints (L.Ξ : Set ℝ) → ∀ f : 𝓢(ℝ, ℂ),
      eLpNorm (L.op f) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C * eLpNorm (⇑f) (ENNReal.ofReal p) volume)
    (f : 𝓢(ℝ, ℂ)) (J : ℕ) :
    Measurable (chainSup r f (J + 1) univ) ∧
      ∫⁻ x, chainSup r f (J + 1) univ x ^ p ≤
        (ENNReal.ofReal C * eLpNorm (⇑f) (ENNReal.ofReal p) volume) ^ p := by
  have hM := fun n => lintegral_chainSup_le hr hp hC f (shiftFinset n) (avoids_shiftFinset n) J
  have hmonoM : Monotone fun n x => chainSup r f (J + 1) (↑(shiftFinset n)) x := fun m n h x =>
    chainSup_mono_set r f (J + 1) (Finset.coe_subset.2 (monotone_shiftFinset h)) x
  have heq : ∀ x, chainSup r f (J + 1) univ x =
      ⨆ n, chainSup r f (J + 1) (↑(shiftFinset n)) x := fun x =>
    le_antisymm (chainSup_univ_le_of_dense r f (J + 1) x dense_denseShift shiftFinset
      monotone_shiftFinset fun d hd => exists_mem_shiftFinset hd)
      (iSup_le fun n => chainSup_mono_set r f (J + 1) (subset_univ _) x)
  have hfun : chainSup r f (J + 1) univ =
      fun x => ⨆ n, chainSup r f (J + 1) (↑(shiftFinset n)) x := funext heq
  rw [hfun]
  refine ⟨Measurable.iSup fun n => (hM n).1, ?_⟩
  rw [lintegral_iSup_rpow hp (fun n => (hM n).1) hmonoM]
  exact iSup_le fun n => (hM n).2

/-- **Theorem 1.2 in the proved range** ([O+] `maintheorem`): for `r > 2` and
`r' < p < 2r/(r-2)`, `‖V^r 𝒮[f]‖_{L^p} ≤ C ‖f‖_{L^p}` for every Schwartz function `f`. -/
theorem strong_proved_range {r p : ℝ} (hr : 2 < r) (hp1 : Real.conjExponent r < p)
    (hp2 : p < 2 * r / (r - 2)) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : 𝓢(ℝ, ℂ),
      eLpNorm (fun x => rVariationOn r Set.univ (fun ξ => partialFourierIntegral f ξ x))
          (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C * eLpNorm (⇑f) (ENNReal.ofReal p) volume := by
  obtain ⟨C, hC0, hC⟩ := linearized_theorem hr hp1 hp2
  have hr0 : 0 < r := by linarith
  have hp : 0 < p := lt_trans (one_pos.trans (one_lt_conjExponent (by linarith))) hp1
  refine ⟨C, hC0, fun f => ?_⟩
  set B : ℝ≥0∞ := ENNReal.ofReal C * eLpNorm (⇑f) (ENNReal.ofReal p) volume with hB
  have hbd := fun J => lintegral_chainSup_univ_le hr hp hC f J
  have hV : (fun x => rVariationOn r univ (fun ξ => partialFourierIntegral f ξ x)) =
      fun x => ⨆ J : ℕ, chainSup r f (J + 1) univ x := by
    funext x
    rw [rVariationOn_eq_iSup_chainSup]
    refine le_antisymm (iSup_le fun J => ?_)
      (iSup_le fun J => le_iSup (fun J => chainSup r f J univ x) (J + 1))
    exact (chainSup_univ_le_succ hr0 f J x).trans
      (le_iSup (fun J => chainSup r f (J + 1) univ x) J)
  have hmono : Monotone fun J x => chainSup r f (J + 1) univ x :=
    monotone_nat_of_le_succ fun J x => chainSup_univ_le_succ hr0 f (J + 1) x
  have hmeasV : Measurable fun x => ⨆ J : ℕ, chainSup r f (J + 1) univ x :=
    Measurable.iSup fun J => (hbd J).1
  rw [hV, eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp [hp]) (by simp)
    hmeasV.aestronglyMeasurable, ENNReal.toReal_ofReal hp.le]
  have h1 : ∫⁻ x, ‖⨆ J : ℕ, chainSup r f (J + 1) univ x‖ₑ ^ p ≤ B ^ p := by
    simp only [enorm_eq_self]
    rw [lintegral_iSup_rpow hp (fun J => (hbd J).1) hmono]
    exact iSup_le fun J => (hbd J).2
  calc _ ≤ (B ^ p) ^ (1 / p) := ENNReal.rpow_le_rpow h1 (by positivity)
    _ = B := by rw [← ENNReal.rpow_mul, mul_one_div_cancel hp.ne', ENNReal.rpow_one]

/-- **Theorem 1.2 for every `r > 2` and `p > r'`** ([O+] `maintheorem`): for `p ≥ 2r/(r-2)` use
`V^r ≤ V^{r̃}` for `r̃ ∈ (2, min(r, 2p/(p-2)))` and the proved range at `(p, r̃)`. -/
theorem variation_strong_all_p {r p : ℝ} (hr : 2 < r) (hp : Real.conjExponent r < p) :
    ∃ C : ℝ, ∀ f : 𝓢(ℝ, ℂ),
      eLpNorm (fun x => rVariationOn r Set.univ (fun ξ => partialFourierIntegral f ξ x))
          (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C * eLpNorm (⇑f) (ENNReal.ofReal p) volume := by
  by_cases hcase : p < 2 * r / (r - 2)
  · obtain ⟨C, -, hC⟩ := strong_proved_range hr hp hcase
    exact ⟨C, hC⟩
  · have hcase := not_lt.1 hcase
    have hr2 : 0 < r - 2 := by linarith
    have hp2 : 2 < p := by
      have : 2 < 2 * r / (r - 2) := by rw [lt_div_iff₀ hr2]; linarith
      linarith
    have hp2' : 0 < p - 2 := by linarith
    have hq : 2 < 2 * p / (p - 2) := by rw [lt_div_iff₀ hp2']; linarith
    set m : ℝ := min r (2 * p / (p - 2)) with hm
    have hm2 : 2 < m := lt_min hr hq
    set r' : ℝ := (2 + m) / 2 with hr'
    have h1 : 2 < r' := by rw [hr']; linarith
    have h2 : r' ≤ r := by
      have : m ≤ r := min_le_left _ _
      rw [hr']; linarith
    have h3 : r' < 2 * p / (p - 2) := by
      have : m ≤ 2 * p / (p - 2) := min_le_right _ _
      rw [hr']; linarith
    have hc : Real.conjExponent r' < p := by
      unfold Real.conjExponent
      have hr'1 : 0 < r' - 1 := by linarith
      rw [div_lt_iff₀ hr'1]
      nlinarith
    have hpp : p < 2 * r' / (r' - 2) := by
      have hr'2 : 0 < r' - 2 := by linarith
      rw [lt_div_iff₀ hr'2]
      rw [lt_div_iff₀ hp2'] at h3
      nlinarith
    obtain ⟨C, -, hC⟩ := strong_proved_range h1 hc hpp
    refine ⟨C, fun f => ?_⟩
    have hmeas : Measurable fun x =>
        rVariationOn r Set.univ (fun ξ => partialFourierIntegral f ξ x) := by
      simp_rw [rVariationOn_eq_iSup_chainSup]
      exact Measurable.iSup fun J => measurable_chainSup r f J univ
    refine le_trans (eLpNorm_mono_enorm hmeas.aestronglyMeasurable fun x => ?_) (hC f)
    simp only [enorm_eq_self]
    exact rVariationOn_anti_exponent (by linarith) h2 _ _

/-- **Theorem 1.2 of [O+]** (`variation_norm_carleson_real`): for `r > 2` and
`r' < p < ∞` there is `C_{p,r}` such that
`‖ ‖𝒮[f](·, x)‖_{V^r_ξ(ℝ)} ‖_{L^p(dx)} ≤ C_{p,r} ‖f‖_{L^p}` for every Schwartz function `f`. -/
theorem variation_norm_carleson_real_proof :
    ∀ r : ℝ, 2 < r → ∀ p : ℝ, r / (r - 1) < p → ∃ C : ℝ, ∀ f : 𝓢(ℝ, ℂ),
      eLpNorm (fun x => rVariationOn r Set.univ (fun ξ => partialFourierIntegral f ξ x))
          (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C * eLpNorm (⇑f) (ENNReal.ofReal p) volume :=
  fun _ hr _ hp => variation_strong_all_p hr hp

end PrimeCarleson.Proof.Oplus
