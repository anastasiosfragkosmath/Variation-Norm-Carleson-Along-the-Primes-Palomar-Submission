module

public import PrimeCarleson.Proof.Oplus.Estimates.All

/-!
# The far-window Bessel estimate for a common time interval ([O+] L1745-L1795)

Source: [O+], L1779–L1785; [O+] `energyincrementprop`, L1766–L1776 (L1745-L1795). The wave packets
`φ_P` of the multitiles `P = (I, ω_u)` with a common time interval `I` are modulates of one another,
so Bessel's inequality gives `∑_{P : P.I = I} |⟨g, φ_P⟩|² ≲ |I| ∫ |g φ_{P_I}|²` for `g` supported in
a window of length `2|I|`. Splitting `g` along the dyadic windows `K_κ` of length
`2|I| = 2^{1-k}|J|` and applying Minkowski's inequality in `ℓ²(Q)` gives the first result below; the
decay of the packets then gives the second.

* `windowK J k κ = K_κ = [2^{k_J+1-k} κ, 2^{k_J+1-k} (κ+1))`, a tiling of `ℝ`
  (`pairwise_disjoint_windowK`, `iUnion_windowK`, `windowK_length`);
* `sum_norm_sq_pairing_le_of_commonInterval_window`, `Multitile.sum_norm_sq_coeff_le_window`:
  the same-interval orthogonality of `Estimates/SameInterval.lean` for `g` supported in an
  *arbitrary* window `[a, a + 2|I|)` (not one centred at `I`);
* `Multitile.sum_enorm_sq_setIntegral_le`: the same for the integrals `∫_W g conj φ_P` over a
  window `W` of length `2|I₀|`, for `g` bounded by `1`, with `ℝ≥0∞`-valued right side;
* `sum_sq_tsum_le`: Minkowski's inequality in `ℓ²` for a countable sum of nonnegative
  `ℝ≥0∞`-vectors indexed by a finite set;
* `sumafterorth_aux` (the printed `sumafterorth`): for multitiles `Q` with `|I| = |J|/2^k`,
  `I ⊆ 2^{ℓ+1} J`, and `g` bounded by `1` vanishing on `2^{ℓ+5} J`,
  `∑_{P ∈ Q} |⟨g, φ_P⟩|² ≤ 2 (|J|/2^k) (∑_κ (∑_I ∫_{K_κ} |g φ_{P_I}|²)^{1/2})²`, the sum over the
  windows `K_κ` not meeting `2^{ℓ+2} J`;
* `tsum_lintegral_window_le`: for `f` dominated by the tail
  `C |I|^{-1/2} (1 + |x - c|/|I|)^{-4} 1_{|x - c| ≥ D}`, `∑_κ (∫_{K_κ} |f|²)^{1/2} ≲ C (D/|I|)^{-2}`
  (a Harnack inequality for the weight on the windows and a comparison of the sum over `κ` with
  an integral);
* `exists_sum_norm_sq_coeff_le_far`: `∑_{P ∈ Q} |⟨g, φ_P⟩|² ≤ K (|J|/2^k) 4^{-(k+ℓ)}` for an
  absolute constant `K` (the number of time intervals is at most `2^{ℓ+1+k}`, each contributes
  `(2^{ℓ+k})^{-2}` to `(∑_κ …)^{1/2}`; the decay exponent `N = 4` of the packets suffices).
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal FourierTransform ComplexConjugate

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

open PrimeCarleson PrimeCarleson.Proof.Common PrimeCarleson.Proof.Goal0


/-! ### Minkowski's inequality for `ℝ≥0∞`-valued sums -/

/-- Minkowski's inequality in `ℓ²(s)` for a finite sum of `ℝ≥0∞`-vectors. -/
theorem sum_sq_finset_sum_le {ι κ : Type*} (s : Finset ι) (F : Finset κ) (c : κ → ι → ℝ≥0∞) :
    (∑ i ∈ s, (∑ κ' ∈ F, c κ' i) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤
      ∑ κ' ∈ F, (∑ i ∈ s, c κ' i ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | insert a F ha ih =>
    rw [Finset.sum_insert ha]
    simp_rw [Finset.sum_insert ha]
    refine (ENNReal.Lp_add_le s (c a) (fun i => ∑ κ' ∈ F, c κ' i) (by norm_num)).trans ?_
    gcongr

/-- Minkowski's inequality in `ℓ²(s)` for a countable sum of `ℝ≥0∞`-vectors:
`(∑_i (∑'_κ c κ i)²)^{1/2} ≤ ∑'_κ (∑_i (c κ i)²)^{1/2}`. -/
theorem sum_sq_tsum_le {ι κ : Type*} (s : Finset ι) (c : κ → ι → ℝ≥0∞) :
    (∑ i ∈ s, (∑' κ', c κ' i) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤
      ∑' κ', (∑ i ∈ s, c κ' i ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  have hL : Tendsto (fun F : Finset κ => (∑ i ∈ s, (∑ κ' ∈ F, c κ' i) ^ (2 : ℝ)) ^ (1 / 2 : ℝ))
      atTop (𝓝 ((∑ i ∈ s, (∑' κ', c κ' i) ^ (2 : ℝ)) ^ (1 / 2 : ℝ))) := by
    refine (ENNReal.continuous_rpow_const.tendsto _).comp ?_
    refine tendsto_finsetSum _ fun i _ => ?_
    exact (ENNReal.continuous_rpow_const.tendsto _).comp (ENNReal.summable.hasSum)
  exact le_of_tendsto_of_tendsto' hL ENNReal.summable.hasSum
    (fun F => sum_sq_finset_sum_le s F c)


/-! ### The windows -/

/-- The dyadic window `K_κ = [2^{k_J+1-k} κ, 2^{k_J+1-k} (κ+1))` of length `2^{1-k}|J|`. -/
def windowK (J : Dyadic) (k : ℕ) (κ : ℤ) : Dyadic := ⟨J.k + 1 - k, κ⟩

/-- The window has length `2^{1-k}|J| = 2 (|J|/2^k)`. -/
theorem windowK_length (J : Dyadic) (k : ℕ) (κ : ℤ) :
    (windowK J k κ).length = 2 * (J.length / 2 ^ k) := by
  unfold windowK Dyadic.length
  simp only
  rw [zpow_sub₀ (by norm_num), zpow_add_one₀ (by norm_num), zpow_natCast]
  ring

/-- Membership in a dyadic interval via the floor. -/
theorem Dyadic.mem_toSet_iff_floor (I : Dyadic) (x : ℝ) : x ∈ I.toSet ↔ ⌊x / I.length⌋ = I.m := by
  have hL := I.length_pos
  rw [Int.floor_eq_iff, Dyadic.mem_toSet, le_div_iff₀ hL, div_lt_iff₀ hL]
  unfold Dyadic.left Dyadic.right Dyadic.length
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> nlinarith

/-- Distinct dyadic intervals of the same scale are disjoint. -/
theorem Dyadic.disjoint_of_k_eq_of_m_ne {I I' : Dyadic} (hk : I.k = I'.k) (hm : I.m ≠ I'.m) :
    Disjoint I.toSet I'.toSet := by
  refine Set.disjoint_left.2 fun x hx hx' => ?_
  rw [Dyadic.mem_toSet_iff_floor] at hx hx'
  have hL : I.length = I'.length := by unfold Dyadic.length; rw [hk]
  rw [hL] at hx
  exact hm (hx.symm.trans hx')

/-- The windows are pairwise disjoint. -/
theorem pairwise_disjoint_windowK (J : Dyadic) (k : ℕ) :
    Pairwise (Function.onFun Disjoint fun κ : ℤ => (windowK J k κ).toSet) := by
  intro a b hab
  exact Dyadic.disjoint_of_k_eq_of_m_ne rfl hab

/-- The windows cover `ℝ`. -/
theorem iUnion_windowK (J : Dyadic) (k : ℕ) : ⋃ κ : ℤ, (windowK J k κ).toSet = univ := by
  refine eq_univ_of_forall fun x => mem_iUnion.2 ⟨⌊x / (windowK J k 0).length⌋, ?_⟩
  rw [Dyadic.mem_toSet_iff_floor]
  rfl

/-! window orthogonality -/
variable {χ : ℝ → ℝ}

/-- **Same-interval orthogonality for an arbitrary window**: the version of
`sum_norm_sq_pairing_le_of_commonInterval` for `g ∈ L²` supported in `[a, a + 2|I|)`, `a` arbitrary:
`∑_{J ∈ Ω} |⟨g, φ_{I×J}⟩|² ≤ 2|I| ∫ |g|² |φ_{I×J₀}|²`. -/
theorem sum_norm_sq_pairing_le_of_commonInterval_window (hχ : IsProfile χ) (I : Dyadic)
    (Ω : Finset Dyadic) (hΩ : ∀ J ∈ Ω, I.k + J.k = -1) {J₀ : Dyadic} (hJ₀ : I.k + J₀.k = -1)
    (a : ℝ) {g : ℝ → ℂ} (hg : MemLp g 2 volume)
    (hsupp : Function.support g ⊆ Ico a (a + 2 * I.length)) :
    ∑ J ∈ Ω, ‖pairing g (wavePacketOf χ I J)‖ ^ 2 ≤
      2 * I.length * ∫ x, ‖g x‖ ^ 2 * ‖wavePacketOf χ I J₀ x‖ ^ 2 := by
  have hI := I.length_pos
  set T : ℝ := 2 * I.length with hT
  have hT0 : 0 < T := by positivity
  set env : ℝ → ℂ := packetEnvelope χ I with henv
  have henv_eq : env = fun x => e (-(J₀.center * (x - I.center))) * wavePacketOf χ I J₀ x := by
    funext x
    rw [henv, wavePacketOf_eq_mul_packetEnvelope χ hJ₀, ← mul_assoc, ← e_add, neg_add_cancel,
      e_zero, one_mul]
  have henv_cont : Continuous env := by
    rw [henv_eq]
    exact (continuous_e.comp (by fun_prop)).mul (hχ.continuous_wavePacketOf I J₀)
  obtain ⟨A, hA0, hA⟩ := hχ.exists_norm_wavePacketOf_le 0
  have henv_bdd : ∀ x, ‖env x‖ ≤ A * (√I.length)⁻¹ := by
    intro x
    rw [henv, ← norm_wavePacketOf_eq_norm_packetEnvelope χ hJ₀]
    simpa using hA I J₀ hJ₀ x
  set u : ℝ → ℂ := fun x => g x * (starRingEnd ℂ) (env x) * e (-(x / (2 * T))) with hu
  have hu_norm : ∀ x, ‖u x‖ = ‖g x‖ * ‖env x‖ := by
    intro x
    simp [hu, norm_e]
  have hu_meas : AEStronglyMeasurable u volume :=
    (hg.aestronglyMeasurable.mul (Complex.continuous_conj.comp henv_cont).aestronglyMeasurable).mul
      (continuous_e.comp (by fun_prop)).aestronglyMeasurable
  have hu_mem : MemLp u 2 volume := by
    refine hg.of_le_mul (c := A * (√I.length)⁻¹) hu_meas (Eventually.of_forall fun x => ?_)
    rw [hu_norm, mul_comm]
    exact mul_le_mul_of_nonneg_right (henv_bdd x) (norm_nonneg _)
  have hu_supp : Function.support u ⊆ Ico a (a + ((1 : ℕ) : ℝ) * T) := by
    intro x hx
    have hgx : g x ≠ 0 := by
      intro h; apply hx; simp [hu, h]
    have hx' := hsupp (Function.mem_support.2 hgx)
    simpa using hx'
  have hpair : ∀ J ∈ Ω, ‖pairing g (wavePacketOf χ I J)‖ =
      ‖∫ x, u x * e (-((J.m : ℝ) * x / T))‖ := by
    intro J hJ
    have hk := hΩ J hJ
    have hL := Dyadic.length_eq_inv_of_area hk
    have hcen : J.center = (J.m + 1 / 2) / T := by
      have : J.center = J.length * (J.m + 1 / 2) := by
        unfold Dyadic.center Dyadic.length; ring
      rw [this, hL, hT]; field_simp
    have h1 : ∀ x : ℝ, g x * (starRingEnd ℂ) (wavePacketOf χ I J x) =
        e (J.center * I.center) * (u x * e (-((J.m : ℝ) * x / T))) := by
      intro x
      rw [wavePacketOf_eq_mul_packetEnvelope χ hk, map_mul, ← e_neg]
      have h2 : e (-(J.center * (x - I.center))) =
          e (J.center * I.center) * e (-(x / (2 * T))) * e (-((J.m : ℝ) * x / T)) := by
        rw [← e_add, ← e_add]; congr 1; rw [hcen]; field_simp; ring
      rw [h2, hu]
      simp only [henv]
      ring
    unfold pairing
    simp_rw [h1]
    rw [integral_const_mul, norm_mul, norm_e, one_mul]
  have hinj : Set.InjOn Dyadic.m (Ω : Set Dyadic) := by
    intro J hJ J' hJ' h
    have e1 := hΩ J hJ
    have e2 := hΩ J' hJ'
    exact Dyadic.ext (by omega) h
  have hsum : ∑ J ∈ Ω, ‖pairing g (wavePacketOf χ I J)‖ ^ 2 =
      ∑ m ∈ Ω.image Dyadic.m, ‖∫ x, u x * e (-((m : ℝ) * x / T))‖ ^ 2 := by
    rw [Finset.sum_image hinj]
    exact Finset.sum_congr rfl fun J hJ => by rw [hpair J hJ]
  rw [hsum]
  refine (sum_norm_sq_integral_mul_e_le hT0 (n := 1) one_pos a hu_mem hu_supp _).trans ?_
  have hint : ∫ x, ‖u x‖ ^ 2 = ∫ x, ‖g x‖ ^ 2 * ‖wavePacketOf χ I J₀ x‖ ^ 2 := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [hu_norm, mul_pow, henv, norm_wavePacketOf_eq_norm_packetEnvelope χ hJ₀]
  rw [hint]
  simp

/-- The `ρ`-multitile form of `sum_norm_sq_pairing_le_of_commonInterval_window`. -/
theorem Multitile.sum_norm_sq_coeff_le_window {ρ : Idx} (ch : ProfileChoice)
    (S : Finset (Multitile ρ)) {I₀ : Dyadic} (hS : ∀ P ∈ S, P.I = I₀) {P₀ : Multitile ρ}
    (hP₀ : P₀.I = I₀) (a : ℝ) {g : ℝ → ℂ} (hg : MemLp g 2 volume)
    (hsupp : Function.support g ⊆ Ico a (a + 2 * I₀.length)) :
    ∑ P ∈ S, ‖P.coeff ch g‖ ^ 2 ≤
      2 * I₀.length * ∫ x, ‖g x‖ ^ 2 * ‖P₀.wavePacket ch x‖ ^ 2 := by
  classical
  have hinj : Set.InjOn Multitile.ωu (S : Set (Multitile ρ)) := by
    intro P hP P' hP' h
    exact Multitile.ext ((hS P hP).trans (hS P' hP').symm) h
  have hsum : ∑ P ∈ S, ‖P.coeff ch g‖ ^ 2 =
      ∑ J ∈ S.image Multitile.ωu, ‖pairing g (wavePacketOf ch.fn I₀ J)‖ ^ 2 := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun P hP => ?_
    have := hS P hP
    unfold Multitile.coeff Multitile.wavePacket Multitile.packetOf
    rw [this]
  rw [hsum]
  have hΩ : ∀ J ∈ S.image Multitile.ωu, I₀.k + J.k = -1 := by
    intro J hJ
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hJ
    have := P.area
    rw [hS P hP] at this
    exact this
  have hk₀ : I₀.k + P₀.ωu.k = -1 := by
    have := P₀.area
    rw [hP₀] at this
    exact this
  have h := sum_norm_sq_pairing_le_of_commonInterval_window ch.isProfile I₀ _ hΩ hk₀ a hg hsupp
  refine h.trans (le_of_eq ?_)
  congr 2
  funext x
  unfold Multitile.wavePacket Multitile.packetOf
  rw [hP₀]


/-! ### The pairing over a window -/

/-- `ofReal ∫ f ≤ ∫⁻ ofReal f` for a nonnegative function (no integrability needed). -/
theorem ofReal_integral_le_lintegral_ofReal {f : ℝ → ℝ} (hf : ∀ x, 0 ≤ f x) :
    ENNReal.ofReal (∫ x, f x) ≤ ∫⁻ x, ENNReal.ofReal (f x) := by
  by_cases h : Integrable f volume
  · rw [ofReal_integral_eq_lintegral_ofReal h (Eventually.of_forall hf)]
  · rw [integral_undef h]; simp

/-- `‖z‖ₑ ^ 2 = ofReal (‖z‖ ^ 2)`. -/
theorem enorm_sq_eq_ofReal {E : Type*} [SeminormedAddCommGroup E] (z : E) :
    ‖z‖ₑ ^ 2 = ENNReal.ofReal (‖z‖ ^ 2) := by
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- **The pairings with a window**: for the packets with a common time interval `I₀`, the window
`W` of length `2|I₀|` and a function `g` bounded by `1`,
`∑_{P : I = I₀} |∫_W g conj φ_P|² ≤ 2|I₀| ∫_W |g φ_{P₀}|²`. -/
theorem Multitile.sum_enorm_sq_setIntegral_le {ρ : Idx} (ch : ProfileChoice)
    (S : Finset (Multitile ρ)) {I₀ : Dyadic} (hS : ∀ P ∈ S, P.I = I₀) {P₀ : Multitile ρ}
    (hP₀ : P₀.I = I₀) (W : Dyadic) (hW : W.length = 2 * I₀.length) {g : ℝ → ℂ}
    (hgm : AEStronglyMeasurable g volume) (hgb : ∀ᵐ x, ‖g x‖ ≤ 1) :
    ∑ P ∈ S, ‖∫ x in W.toSet, g x * (starRingEnd ℂ) (P.wavePacket ch x)‖ₑ ^ 2 ≤
      ENNReal.ofReal (2 * I₀.length) *
        ∫⁻ x in W.toSet, ‖g x * P₀.wavePacket ch x‖ₑ ^ 2 := by
  set gW : ℝ → ℂ := W.toSet.indicator g with hgW
  have hmeas : MeasurableSet W.toSet := W.measurableSet_toSet
  have hmemLp : MemLp gW 2 volume := by
    rw [hgW, memLp_indicator_iff_restrict hmeas.nullMeasurableSet]
    have : IsFiniteMeasure (volume.restrict W.toSet) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ico_lt_top⟩
    exact MemLp.of_bound hgm.restrict 1 (ae_restrict_of_ae hgb)
  have hsupp : Function.support gW ⊆ Ico W.left (W.left + 2 * I₀.length) := by
    intro x hx
    have hxW : x ∈ W.toSet := by
      by_contra h
      exact hx (by simp [hgW, h])
    refine ⟨hxW.1, ?_⟩
    have := hxW.2
    rw [Dyadic.right_eq, hW] at this
    exact this
  have hcoeff : ∀ P ∈ S, ∫ x in W.toSet, g x * (starRingEnd ℂ) (P.wavePacket ch x) =
      P.coeff ch gW := by
    intro P _
    unfold Multitile.coeff pairing
    rw [← integral_indicator hmeas]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ W.toSet <;> simp [hgW, hx]
  have h := Multitile.sum_norm_sq_coeff_le_window ch S hS hP₀ W.left hmemLp hsupp
  have h1 : ∑ P ∈ S, ‖∫ x in W.toSet, g x * (starRingEnd ℂ) (P.wavePacket ch x)‖ₑ ^ 2 =
      ENNReal.ofReal (∑ P ∈ S, ‖P.coeff ch gW‖ ^ 2) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun P _ => by positivity)]
    refine Finset.sum_congr rfl fun P hP => ?_
    rw [hcoeff P hP, enorm_sq_eq_ofReal]
  rw [h1]
  refine (ENNReal.ofReal_le_ofReal h).trans ?_
  rw [ENNReal.ofReal_mul (by have := I₀.length_pos; positivity)]
  refine mul_le_mul_right ?_ _
  refine (ofReal_integral_le_lintegral_ofReal (fun x => by positivity)).trans ?_
  rw [← lintegral_indicator hmeas]
  refine le_of_eq (lintegral_congr fun x => ?_)
  by_cases hx : x ∈ W.toSet
  · simp only [hgW, Set.indicator_of_mem hx]
    rw [enorm_sq_eq_ofReal, norm_mul, mul_pow]
  · simp [hgW, hx]

/-! ### Splitting along the windows -/

/-- A window meeting `J.dilate (2^(ℓ+2))` lies in `J.dilate (2^(ℓ+5))`, where `g` vanishes. -/
theorem eq_zero_of_not_disjoint_windowK {J : Dyadic} {ℓ k : ℕ} {κ : ℤ} {g : ℝ → ℂ}
    (hg0 : ∀ x ∈ J.dilate (2 ^ (ℓ + 5)), g x = 0)
    (h : ¬ Disjoint (windowK J k κ).toSet (J.dilate (2 ^ (ℓ + 2)))) :
    ∀ x ∈ (windowK J k κ).toSet, g x = 0 := by
  intro x hx
  obtain ⟨y, hy, hyD⟩ := Set.not_disjoint_iff.1 h
  apply hg0
  have hJ := J.length_pos
  have hlen := windowK_length J k κ
  have hk : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hd : J.length / 2 ^ k ≤ J.length := div_le_self hJ.le hk
  have hP : (1 : ℝ) ≤ 2 ^ ℓ := one_le_pow₀ (by norm_num)
  have hPL : J.length ≤ 2 ^ ℓ * J.length := by nlinarith
  have e2 : (2 : ℝ) ^ (ℓ + 2) = 4 * 2 ^ ℓ := by ring
  have e5 : (2 : ℝ) ^ (ℓ + 5) = 32 * 2 ^ ℓ := by ring
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  obtain ⟨hD1, hD2⟩ := hyD
  rw [Dyadic.right_eq, hlen] at hx2 hy2
  rw [e2] at hD1 hD2
  rw [Dyadic.dilate, e5]
  constructor <;> nlinarith

/-- The window integrals of `g conj φ_P` add up to the coefficient `⟨g, φ_P⟩`. -/
theorem Multitile.hasSum_setIntegral_windowK {ρ : Idx} (ch : ProfileChoice) (P : Multitile ρ)
    (J : Dyadic) (k : ℕ) {g : ℝ → ℂ} (hgm : AEStronglyMeasurable g volume)
    (hgb : ∀ᵐ x, ‖g x‖ ≤ 1) :
    HasSum (fun κ : ℤ => ∫ x in (windowK J k κ).toSet,
      g x * (starRingEnd ℂ) (P.wavePacket ch x)) (P.coeff ch g) := by
  have hint : Integrable (fun x => g x * (starRingEnd ℂ) (P.wavePacket ch x)) :=
    integrable_mul_conj_wavePacketOf_of_bdd ch.isProfile hgm hgb P.I P.ωu
  have h := hasSum_integral_iUnion (μ := volume)
    (s := fun κ : ℤ => (windowK J k κ).toSet) (fun κ => (windowK J k κ).measurableSet_toSet)
    (pairwise_disjoint_windowK J k) (by rw [iUnion_windowK]; exact hint.integrableOn)
  rw [iUnion_windowK, Measure.restrict_univ] at h
  exact h

open Classical in
/-- **The sum after orthogonality** ([O+] L1758-L1795, `sumafterorth`): for the multitiles
`Q` with time intervals of length `|J|/2^k` inside `2^{ℓ+1} J`, and `g` bounded by `1` vanishing on
`2^{ℓ+5} J`, `∑_{P ∈ Q} |⟨g, φ_P⟩|² ≤ 2 · (|J|/2^k) (∑_κ (∑_I ∫_{K_κ} |g φ_{P_I}|²)^{1/2})²`, the
sum over the windows `K_κ` of length `2^{1-k}|J|` not meeting `2^{ℓ+2} J`. -/
theorem sumafterorth_aux : ∃ K : ℝ, 0 ≤ K ∧ ∀ {ρ : Idx} (ch : ProfileChoice) (J : Dyadic)
    (ℓ k : ℕ) (Q : Finset (Multitile ρ)),
    (∀ P ∈ Q, P.I.length = J.length / 2 ^ k ∧ P.I.toSet ⊆ J.dilate (2 ^ (ℓ + 1))) →
    ∀ (Pι : Dyadic → Multitile ρ), (∀ P ∈ Q, (Pι P.I).I = P.I) →
    ∀ {g : ℝ → ℂ}, AEStronglyMeasurable g volume → (∀ᵐ x, ‖g x‖ ≤ 1) →
      (∀ x ∈ J.dilate (2 ^ (ℓ + 5)), g x = 0) →
    ENNReal.ofReal (∑ P ∈ Q, ‖P.coeff ch g‖ ^ 2) ≤
      ENNReal.ofReal (K * (J.length / 2 ^ k)) *
        (∑' κ : ℤ, if Disjoint (windowK J k κ).toSet (J.dilate (2 ^ (ℓ + 2))) then
          (∑ I ∈ Q.image Multitile.I, ∫⁻ x in (windowK J k κ).toSet,
            ‖g x * (Pι I).wavePacket ch x‖ₑ ^ 2) ^ (1 / 2 : ℝ) else 0) ^ 2 := by
  refine ⟨2, by norm_num, ?_⟩
  intro ρ ch J ℓ k Q hQ Pι hPι g hgm hgb hg0
  set T : ℝ := 2 * (J.length / 2 ^ k) with hT
  have hT0 : 0 ≤ T := by have := J.length_pos; positivity
  set good : ℤ → Prop := fun κ => Disjoint (windowK J k κ).toSet (J.dilate (2 ^ (ℓ + 2))) with hgood
  set c : ℤ → Multitile ρ → ℝ≥0∞ := fun κ P => if good κ then
    ‖∫ x in (windowK J k κ).toSet, g x * (starRingEnd ℂ) (P.wavePacket ch x)‖ₑ else 0 with hc
  set W : ℤ → ℝ≥0∞ := fun κ => ∑ I ∈ Q.image Multitile.I, ∫⁻ x in (windowK J k κ).toSet,
    ‖g x * (Pι I).wavePacket ch x‖ₑ ^ 2 with hW
  -- the coefficient is bounded by the sum over the windows
  have h1 : ∀ P ∈ Q, ‖P.coeff ch g‖ₑ ≤ ∑' κ, c κ P := by
    intro P _
    have hs := Multitile.hasSum_setIntegral_windowK ch P J k hgm hgb
    have hcoef : P.coeff ch g = ∑' κ : ℤ, (if good κ then
        ∫ x in (windowK J k κ).toSet, g x * (starRingEnd ℂ) (P.wavePacket ch x) else 0) := by
      rw [← hs.tsum_eq]
      refine tsum_congr fun κ => ?_
      by_cases hκ : good κ
      · rw [ite_eq_left hκ]
      · rw [ite_eq_right hκ]
        exact setIntegral_eq_zero_of_forall_eq_zero fun x hx => by
          rw [eq_zero_of_not_disjoint_windowK hg0 hκ x hx, zero_mul]
    rw [hcoef]
    refine enorm_tsum_le_tsum_enorm.trans (le_of_eq (tsum_congr fun κ => ?_))
    by_cases hκ : good κ <;> simp [hc, hκ]
  -- the pairings with one window
  have h2 : ∀ κ, good κ → ∑ P ∈ Q, c κ P ^ 2 ≤ ENNReal.ofReal T * W κ := by
    intro κ hκ
    simp only [hc, ite_eq_left hκ]
    rw [← Finset.sum_fiberwise_of_maps_to (g := Multitile.I) (t := Q.image Multitile.I)
      (fun P hP => Finset.mem_image_of_mem _ hP)]
    rw [hW, Finset.mul_sum]
    refine Finset.sum_le_sum fun I hI => ?_
    obtain ⟨P₁, hP₁, rfl⟩ := Finset.mem_image.1 hI
    have hlen : P₁.I.length = J.length / 2 ^ k := (hQ P₁ hP₁).1
    have h := Multitile.sum_enorm_sq_setIntegral_le ch (Q.filter fun P => P.I = P₁.I)
      (fun P hP => (Finset.mem_filter.1 hP).2) (hPι P₁ hP₁) (windowK J k κ)
      (by rw [windowK_length, hlen]) hgm hgb
    rw [hT, ← hlen]
    exact h
  -- Minkowski
  have h3 : ENNReal.ofReal (∑ P ∈ Q, ‖P.coeff ch g‖ ^ 2) ≤
      (∑' κ, (∑ P ∈ Q, c κ P ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) ^ 2 := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun P _ => by positivity)]
    calc ∑ P ∈ Q, ENNReal.ofReal (‖P.coeff ch g‖ ^ 2)
        = ∑ P ∈ Q, ‖P.coeff ch g‖ₑ ^ 2 := by simp_rw [enorm_sq_eq_ofReal]
      _ ≤ ∑ P ∈ Q, (∑' κ, c κ P) ^ (2 : ℝ) := by
          refine Finset.sum_le_sum fun P hP => ?_
          rw [ENNReal.rpow_two]
          exact pow_le_pow_left' (h1 P hP) 2
      _ = ((∑ P ∈ Q, (∑' κ, c κ P) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) := by
          rw [← ENNReal.rpow_mul]; norm_num
      _ ≤ (∑' κ, (∑ P ∈ Q, c κ P ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) :=
          ENNReal.rpow_le_rpow (sum_sq_tsum_le Q c) (by norm_num)
      _ = _ := ENNReal.rpow_two _
  refine h3.trans ?_
  have h4 : ∀ κ, (∑ P ∈ Q, c κ P ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤
      (ENNReal.ofReal T) ^ (1 / 2 : ℝ) * (if good κ then W κ ^ (1 / 2 : ℝ) else 0) := by
    intro κ
    by_cases hκ : good κ
    · rw [ite_eq_left hκ, ← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
      refine ENNReal.rpow_le_rpow ?_ (by norm_num)
      simp_rw [ENNReal.rpow_two]
      exact h2 κ hκ
    · simp [hc, hκ]
  calc (∑' κ, (∑ P ∈ Q, c κ P ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) ^ 2
      ≤ (∑' κ, (ENNReal.ofReal T) ^ (1 / 2 : ℝ) * (if good κ then W κ ^ (1 / 2 : ℝ) else 0)) ^ 2 :=
        pow_le_pow_left' (ENNReal.tsum_le_tsum h4) 2
    _ = ENNReal.ofReal T * (∑' κ, (if good κ then W κ ^ (1 / 2 : ℝ) else 0)) ^ 2 := by
        rw [ENNReal.tsum_mul_left, mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        norm_num
    _ = _ := by rw [hT]

/-! ### The far-field bound for one time interval -/

/-- Harnack inequality for the weight `(1 + |x - c|/L)^{-4}` on a window of length `2L`. -/
theorem far_weight_le_mul_of_abs_sub_le {L c x y : ℝ} (hL : 0 < L) (hxy : |x - y| ≤ 2 * L) :
    (1 + |x - c| / L) ^ (-((4 : ℕ) : ℤ)) ≤ 81 * (1 + |y - c| / L) ^ (-((4 : ℕ) : ℤ)) := by
  have ha : (1 : ℝ) ≤ 1 + |x - c| / L := by
    have : 0 ≤ |x - c| / L := by positivity
    linarith
  have hyc : |y - c| ≤ |x - c| + 2 * L := by
    calc |y - c| = |(x - c) + (y - x)| := by ring_nf
      _ ≤ |x - c| + |y - x| := abs_add_le _ _
      _ ≤ |x - c| + 2 * L := by
          have := abs_sub_comm y x
          linarith
  have hb : 1 + |y - c| / L ≤ 3 * (1 + |x - c| / L) := by
    have : |y - c| / L ≤ |x - c| / L + 2 := by
      have h1 : |y - c| / L ≤ (|x - c| + 2 * L) / L := by gcongr
      have h2 : (|x - c| + 2 * L) / L = |x - c| / L + 2 := by field_simp
      linarith
    have h0 : 0 ≤ |x - c| / L := by positivity
    linarith
  set a : ℝ := 1 + |x - c| / L with ha'
  set b : ℝ := 1 + |y - c| / L with hb'
  have hbpos : 0 < b := by positivity
  have hapos : 0 < a := by linarith
  have h4 : b ^ 4 ≤ 81 * a ^ 4 := by
    calc b ^ 4 ≤ (3 * a) ^ 4 := pow_le_pow_left₀ hbpos.le hb 4
      _ = 81 * a ^ 4 := by ring
  rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
  calc (a ^ 4)⁻¹ = 81 * (81 * a ^ 4)⁻¹ := by field_simp
    _ ≤ 81 * (b ^ 4)⁻¹ := by gcongr

/-- `√(a + b) ≤ √a + √b` in `ℝ≥0∞`, for finite sums. -/
theorem sqrt_sum_le_sum_sqrt {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞) :
    (∑ i ∈ s, f i) ^ (1 / 2 : ℝ) ≤ ∑ i ∈ s, f i ^ (1 / 2 : ℝ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (ENNReal.rpow_add_le_add_rpow _ _ (by norm_num) (by norm_num)).trans
      (add_le_add_right ih _)

/-- The tail integral of the weight: the part of `∫ (1 + |x - c|/L)^{-4}` beyond `|x - c| ≥ D/2` is
at most `(1 + D/(2L))^{-2} · 2L`. -/
theorem lintegral_far_weight_le {L c D C : ℝ} (hL : 0 < L) (hC : 0 ≤ C) (hD : 0 ≤ D) :
    ∫⁻ x, (if D / 2 ≤ |x - c| then ENNReal.ofReal (C * (√L)⁻¹ *
        (1 + |x - c| / L) ^ (-((4 : ℕ) : ℤ))) else 0) ≤
      ENNReal.ofReal (C * (√L)⁻¹ * (1 + D / (2 * L)) ^ (-((2 : ℕ) : ℤ)) * (2 * L)) := by
  set ε : ℝ := (1 + D / (2 * L)) ^ (-((2 : ℕ) : ℤ)) with hε
  have hs : 0 < √L := Real.sqrt_pos.2 hL
  have hε0 : 0 ≤ ε := by positivity
  have hint : Integrable (fun x : ℝ => (1 + |x - c| / L) ^ (-((2 : ℕ) : ℤ))) :=
    integrable_one_add_abs_div_zpow (by norm_num) c hL
  have hpt : ∀ x : ℝ, (if D / 2 ≤ |x - c| then ENNReal.ofReal (C * (√L)⁻¹ *
        (1 + |x - c| / L) ^ (-((4 : ℕ) : ℤ))) else 0) ≤
      ENNReal.ofReal (C * (√L)⁻¹ * ε * (1 + |x - c| / L) ^ (-((2 : ℕ) : ℤ))) := by
    intro x
    by_cases h : D / 2 ≤ |x - c|
    · rw [ite_eq_left h]
      refine ENNReal.ofReal_le_ofReal ?_
      have hu : 1 + D / (2 * L) ≤ 1 + |x - c| / L := by
        have : D / (2 * L) ≤ |x - c| / L := by
          rw [show D / (2 * L) = (D / 2) / L by field_simp]
          gcongr
        linarith
      have hu0 : 0 < 1 + D / (2 * L) := by positivity
      have h1 : (1 + |x - c| / L) ^ (-((2 : ℕ) : ℤ)) ≤ ε := by
        rw [hε, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
        exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hu0.le hu 2)
      have h4 : (1 + |x - c| / L) ^ (-((4 : ℕ) : ℤ)) =
          (1 + |x - c| / L) ^ (-((2 : ℕ) : ℤ)) * (1 + |x - c| / L) ^ (-((2 : ℕ) : ℤ)) := by
        rw [← zpow_add₀ (by positivity)]; norm_num
      rw [h4]
      have hpos : 0 ≤ C * (√L)⁻¹ := by positivity
      have h2 : 0 ≤ (1 + |x - c| / L) ^ (-((2 : ℕ) : ℤ)) := by positivity
      calc C * (√L)⁻¹ * ((1 + |x - c| / L) ^ (-((2 : ℕ) : ℤ)) *
            (1 + |x - c| / L) ^ (-((2 : ℕ) : ℤ)))
          ≤ C * (√L)⁻¹ * (ε * (1 + |x - c| / L) ^ (-((2 : ℕ) : ℤ))) := by
            gcongr
        _ = _ := by ring
    · rw [ite_eq_right h]; exact zero_le
  calc ∫⁻ x, (if D / 2 ≤ |x - c| then ENNReal.ofReal (C * (√L)⁻¹ *
        (1 + |x - c| / L) ^ (-((4 : ℕ) : ℤ))) else 0)
      ≤ ∫⁻ x, ENNReal.ofReal (C * (√L)⁻¹ * ε * (1 + |x - c| / L) ^ (-((2 : ℕ) : ℤ))) :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (∫ x, C * (√L)⁻¹ * ε * (1 + |x - c| / L) ^ (-((2 : ℕ) : ℤ))) := by
        rw [ofReal_integral_eq_lintegral_ofReal (hint.const_mul _)
          (Eventually.of_forall fun x => by positivity)]
    _ = _ := by
        rw [integral_const_mul, integral_one_add_abs_div_zpow (by norm_num) c hL]
        norm_num
        ring_nf

/-- **Far-field bound for the windows**: if `f` is dominated by the tail
`C |I|^{-1/2} (1 + |x - c|/L)^{-4} 1_{|x - c| ≥ D}` (with `L = |I|`, `D ≥ 4L`), then for any tiling
of `ℝ` by measurable sets `K_κ` of measure `2L` and diameter at most `2L`,
`∑_κ (∫_{K_κ} |f|²)^{1/2} ≤ 18 C (1 + D/(2L))^{-2}`. -/
theorem tsum_lintegral_window_le {K : ℤ → Set ℝ} (hK : ∀ κ, MeasurableSet (K κ))
    (hdisj : Pairwise (Function.onFun Disjoint K)) (hcov : ⋃ κ, K κ = univ)
    {L : ℝ} (hL : 0 < L) (hdiam : ∀ κ, ∀ x ∈ K κ, ∀ y ∈ K κ, |x - y| ≤ 2 * L)
    (hvol : ∀ κ, volume (K κ) = ENNReal.ofReal (2 * L))
    {c D C : ℝ} (hC : 0 ≤ C) (hD : 4 * L ≤ D) {f : ℝ → ℂ}
    (hf : ∀ᵐ x, ‖f x‖ ≤ if D ≤ |x - c| then
      C * (√L)⁻¹ * (1 + |x - c| / L) ^ (-((4 : ℕ) : ℤ)) else 0) :
    ∑' κ, (∫⁻ x in K κ, ‖f x‖ₑ ^ 2) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (18 * C * (1 + D / (2 * L)) ^ (-((2 : ℕ) : ℤ))) := by
  have hs : 0 < √L := Real.sqrt_pos.2 hL
  have hss : √L * √L = L := Real.mul_self_sqrt hL.le
  have hD0 : 0 ≤ D := by linarith
  set v : ℝ → ℝ := fun x => C * (√L)⁻¹ * (1 + |x - c| / L) ^ (-((4 : ℕ) : ℤ)) with hv
  have hvnn : ∀ x, 0 ≤ v x := fun x => by simp only [hv]; positivity
  have hvc : Continuous v := by
    refine continuous_const.mul (Continuous.zpow₀ (by fun_prop) _ fun x => Or.inl ?_)
    positivity
  set G : ℝ → ℝ≥0∞ := fun x => if D ≤ |x - c| then ENNReal.ofReal (v x) else 0 with hG
  set G' : ℝ → ℝ≥0∞ := fun x => if D / 2 ≤ |x - c| then ENNReal.ofReal (v x) else 0 with hG'
  have hG'm : Measurable G' := by
    refine Measurable.ite (measurableSet_le measurable_const (by fun_prop)) ?_ measurable_const
    exact ENNReal.measurable_ofReal.comp hvc.measurable
  have hfG : ∀ᵐ x, ‖f x‖ₑ ≤ G x := by
    filter_upwards [hf] with x hx
    by_cases h : D ≤ |x - c|
    · rw [ite_eq_left h] at hx
      simp only [hG, ite_eq_left h]
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal hx
    · rw [ite_eq_right h] at hx
      have : f x = 0 := norm_le_zero_iff.1 hx
      simp [this]
  have hGG' : ∀ x, G x ≤ G' x := by
    intro x
    by_cases h : D ≤ |x - c|
    · have h' : D / 2 ≤ |x - c| := by linarith
      simp only [hG, hG', ite_eq_left h, ite_eq_left h']; exact le_rfl
    · simp [hG, h]
  set a : ℤ → ℝ≥0∞ := fun κ => ∫⁻ y in K κ, G' y with ha
  -- the sup of `G` over a window is at most a multiple of the integral of `G'`
  have hsup : ∀ κ, ∀ x ∈ K κ, G x ≤ ENNReal.ofReal (81 / L) * a κ := by
    intro κ x hx
    by_cases hF : D ≤ |x - c|
    · have h1 : ∀ y ∈ K κ, G x ≤ ENNReal.ofReal 81 * G' y := by
        intro y hy
        have hxy := hdiam κ x hx y hy
        have hy' : D / 2 ≤ |y - c| := by
          have : |x - c| ≤ |y - c| + |x - y| := by
            calc |x - c| = |(y - c) + (x - y)| := by ring_nf
              _ ≤ _ := abs_add_le _ _
          linarith
        simp only [hG, hG', ite_eq_left hF, ite_eq_left hy']
        rw [← ENNReal.ofReal_mul (by norm_num)]
        refine ENNReal.ofReal_le_ofReal ?_
        simp only [hv]
        have := far_weight_le_mul_of_abs_sub_le (c := c) hL hxy
        have h0 : 0 ≤ C * (√L)⁻¹ := by positivity
        calc C * (√L)⁻¹ * (1 + |x - c| / L) ^ (-((4 : ℕ) : ℤ))
            ≤ C * (√L)⁻¹ * (81 * (1 + |y - c| / L) ^ (-((4 : ℕ) : ℤ))) :=
              mul_le_mul_of_nonneg_left this h0
          _ = _ := by ring
      have h2 : G x * ENNReal.ofReal (2 * L) ≤ ENNReal.ofReal 81 * a κ := by
        calc G x * ENNReal.ofReal (2 * L) = ∫⁻ _ in K κ, G x := by
              rw [setLIntegral_const, hvol]
          _ ≤ ∫⁻ y in K κ, ENNReal.ofReal 81 * G' y := setLIntegral_mono' (hK κ) h1
          _ = ENNReal.ofReal 81 * a κ := lintegral_const_mul _ hG'm
      have h3 : ENNReal.ofReal L * G x ≤ ENNReal.ofReal 81 * a κ := by
        refine le_trans ?_ h2
        rw [mul_comm]
        exact mul_le_mul_right (ENNReal.ofReal_le_ofReal (by linarith)) _
      have h4 := (ENNReal.mul_le_iff_le_inv (r := ENNReal.ofReal L)
        (by simpa using hL) ENNReal.ofReal_ne_top).1 h3
      refine h4.trans (le_of_eq ?_)
      rw [← mul_assoc, ← ENNReal.ofReal_inv_of_pos hL, ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      field_simp
    · simp [hG, hF]
  -- one window
  have hwin : ∀ κ, (∫⁻ x in K κ, ‖f x‖ₑ ^ 2) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (9 / √L) * a κ := by
    intro κ
    have h1 : ∫⁻ x in K κ, ‖f x‖ₑ ^ 2 ≤ ENNReal.ofReal (81 / L) * a κ ^ 2 := by
      calc ∫⁻ x in K κ, ‖f x‖ₑ ^ 2
          ≤ ∫⁻ x in K κ, (ENNReal.ofReal (81 / L) * a κ) * G' x := by
            refine lintegral_mono_ae ?_
            filter_upwards [ae_restrict_of_ae hfG, ae_restrict_mem (hK κ)] with x hx hxK
            rw [sq]
            exact mul_le_mul' (hx.trans (hsup κ x hxK)) (hx.trans (hGG' x))
        _ = (ENNReal.ofReal (81 / L) * a κ) * a κ := lintegral_const_mul _ hG'm
        _ = _ := by ring
    calc (∫⁻ x in K κ, ‖f x‖ₑ ^ 2) ^ (1 / 2 : ℝ)
        ≤ (ENNReal.ofReal (81 / L) * a κ ^ 2) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow h1 (by norm_num)
      _ = ENNReal.ofReal (81 / L) ^ (1 / 2 : ℝ) * (a κ ^ 2) ^ (1 / 2 : ℝ) :=
          ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
      _ = ENNReal.ofReal (9 / √L) * a κ := by
          congr 1
          · rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
            congr 1
            have : (81 : ℝ) / L = (9 / √L) ^ 2 := by
              rw [div_pow, Real.sq_sqrt hL.le]; norm_num
            rw [this, ← Real.sqrt_eq_rpow, Real.sqrt_sq (by positivity)]
          · rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
  have hsum : ∑' κ, a κ = ∫⁻ x, G' x := by
    rw [← lintegral_iUnion hK hdisj, hcov, Measure.restrict_univ]
  calc ∑' κ, (∫⁻ x in K κ, ‖f x‖ₑ ^ 2) ^ (1 / 2 : ℝ)
      ≤ ∑' κ, ENNReal.ofReal (9 / √L) * a κ := ENNReal.tsum_le_tsum hwin
    _ = ENNReal.ofReal (9 / √L) * ∫⁻ x, G' x := by rw [ENNReal.tsum_mul_left, hsum]
    _ ≤ ENNReal.ofReal (9 / √L) * ENNReal.ofReal (C * (√L)⁻¹ *
          (1 + D / (2 * L)) ^ (-((2 : ℕ) : ℤ)) * (2 * L)) :=
        mul_le_mul_right (lintegral_far_weight_le hL hC hD0) _
    _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        calc 9 / √L * (C * (√L)⁻¹ * (1 + D / (2 * L)) ^ (-((2 : ℕ) : ℤ)) * (2 * L))
            = 9 / √L * (C * (√L)⁻¹ * (1 + D / (2 * L)) ^ (-((2 : ℕ) : ℤ)) *
              (2 * (√L * √L))) := by rw [hss]
          _ = _ := by field_simp; ring


/-! ### Counting and the geometry of the far region -/

/-- Dyadic intervals of a common length `L` inside `[a, b)` are at most `(b - a)/L` in number. -/
theorem card_mul_le_of_dyadic_subset {A : Finset Dyadic} {L a b : ℝ} (hab : a ≤ b)
    (hL : ∀ I ∈ A, I.length = L) (hsub : ∀ I ∈ A, I.toSet ⊆ Ico a b) :
    (A.card : ℝ) * L ≤ b - a := by
  have hk : ∀ I ∈ A, ∀ I' ∈ A, I.k = I'.k := by
    intro I hI I' hI'
    have h : I.length = I'.length := (hL I hI).trans (hL I' hI').symm
    exact zpow_right_injective₀ (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) h
  have hdisj : (A : Set Dyadic).PairwiseDisjoint Dyadic.toSet := by
    intro I hI I' hI' hne
    exact Dyadic.disjoint_of_k_eq_of_m_ne (hk I hI I' hI')
      (fun hm => hne (Dyadic.ext (hk I hI I' hI') hm))
  have h1 := measure_biUnion_finset (μ := volume) hdisj (fun I _ => I.measurableSet_toSet)
  have h2 : volume (⋃ I ∈ A, I.toSet) ≤ volume (Ico a b) :=
    measure_mono (iUnion₂_subset hsub)
  rw [h1, Real.volume_Ico] at h2
  have h3 : ∑ I ∈ A, volume I.toSet = (A.card : ℝ≥0∞) * ENNReal.ofReal L := by
    rw [Finset.sum_congr rfl (fun I hI => by rw [Dyadic.volume_toSet, hL I hI]),
      Finset.sum_const, nsmul_eq_mul]
  rw [h3, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ENNReal.ofReal_le_ofReal_iff'] at h2
  rcases h2 with h2 | h2
  · exact h2
  · have : (A.card : ℝ) * L = 0 ∨ (A.card : ℝ) * L < 0 := by
      rcases lt_or_eq_of_le h2 with h | h
      · exact Or.inr h
      · exact Or.inl h
    rcases this with h | h
    · linarith
    · exfalso
      have : 0 ≤ (A.card : ℝ) * L := by
        by_cases hA : A = ∅
        · simp [hA]
        · obtain ⟨I, hI⟩ := Finset.nonempty_iff_ne_empty.2 hA
          have := (hL I hI) ▸ I.length_pos
          positivity
      linarith

/-- The interval `I` lies in `2^{ℓ+1} J`, `g` vanishes on `2^{ℓ+5} J`, so the points where `g ≠ 0`
are at distance `≥ 15 · 2^ℓ |J|` from the center of `I`. -/
theorem le_abs_sub_center_of_ne_zero {J I : Dyadic} {ℓ k : ℕ} {g : ℝ → ℂ}
    (hI : I.toSet ⊆ J.dilate (2 ^ (ℓ + 1)))
    (hg0 : ∀ x ∈ J.dilate (2 ^ (ℓ + 5)), g x = 0) {x : ℝ} (hx : g x ≠ 0) :
    15 * 2 ^ (ℓ + k) * (J.length / 2 ^ k) ≤ |x - I.center| := by
  have hJ := J.length_pos
  have hIl := I.length_pos
  have hcen : I.center ∈ I.toSet := by
    refine ⟨?_, ?_⟩
    · rw [Dyadic.center_eq]; linarith
    · rw [Dyadic.center_eq, Dyadic.right_eq]; linarith
  have hc := hI hcen
  obtain ⟨hc1, hc2⟩ := hc
  have hnot : x ∉ J.dilate (2 ^ (ℓ + 5)) := fun h => hx (hg0 x h)
  have e1 : (2 : ℝ) ^ (ℓ + 1) = 2 * 2 ^ ℓ := by ring
  have e5 : (2 : ℝ) ^ (ℓ + 5) = 32 * 2 ^ ℓ := by ring
  have ek : (2 : ℝ) ^ (ℓ + k) = 2 ^ ℓ * 2 ^ k := pow_add _ _ _
  have hk0 : (0 : ℝ) < 2 ^ k := by positivity
  have hR : 15 * 2 ^ (ℓ + k) * (J.length / 2 ^ k) = 15 * 2 ^ ℓ * J.length := by
    rw [ek]; field_simp
  rw [hR]
  rw [e1] at hc1 hc2
  rw [Dyadic.dilate, e5, mem_Ico, not_and_or, not_le, not_lt] at hnot
  rcases hnot with h | h
  · have : -(x - I.center) ≤ |x - I.center| := neg_le_abs _
    nlinarith
  · have : x - I.center ≤ |x - I.center| := le_abs_self _
    nlinarith

/-! ### The decay of the far windows -/

/-- **The far-window Bessel estimate** ([O+] L1745-L1795): the multitiles `Q` have time intervals
of length `|J|/2^k` inside `2^{ℓ+1} J`, and `g` is bounded by `1` and vanishes on `2^{ℓ+5} J`;
then `∑_{P ∈ Q} |⟨g, φ_P⟩|² ≤ K (|J|/2^k) 4^{-(k+ℓ)}` for an absolute constant `K`. -/
theorem exists_sum_norm_sq_coeff_le_far : ∃ K : ℝ, 0 ≤ K ∧ ∀ {ρ : Idx} (ch : ProfileChoice)
    (J : Dyadic) (ℓ k : ℕ) (Q : Finset (Multitile ρ)),
    (∀ P ∈ Q, P.I.length = J.length / 2 ^ k ∧ P.I.toSet ⊆ J.dilate (2 ^ (ℓ + 1))) →
    ∀ {g : ℝ → ℂ}, AEStronglyMeasurable g volume → (∀ᵐ x, ‖g x‖ ≤ 1) →
      (∀ x ∈ J.dilate (2 ^ (ℓ + 5)), g x = 0) →
    ∑ P ∈ Q, ‖P.coeff ch g‖ ^ 2 ≤ K * (J.length / 2 ^ k) * (1 / 4) ^ (k + ℓ) := by
  classical
  obtain ⟨K₁, hK₁, h1⟩ := sumafterorth_aux
  obtain ⟨Cφ, hCφ, hφ⟩ := Multitile.exists_norm_wavePacket_le 4
  refine ⟨K₁ * (36 * Cφ) ^ 2, by positivity, ?_⟩
  intro ρ ch J ℓ k Q hQ g hgm hgb hg0
  rcases Q.eq_empty_or_nonempty with rfl | ⟨P₀, hP₀⟩
  · simp only [Finset.sum_empty]; have := J.length_pos; positivity
  have hJ := J.length_pos
  set L : ℝ := J.length / 2 ^ k with hLdef
  have hL : 0 < L := by positivity
  set R : ℝ := 2 ^ (ℓ + k) with hRdef
  have hR1 : (1 : ℝ) ≤ R := one_le_pow₀ (by norm_num)
  have hR0 : 0 < R := by linarith
  -- a representative of each time interval
  let Pι : Dyadic → Multitile ρ := fun I => if h : ∃ P ∈ Q, P.I = I then h.choose else P₀
  have hPι : ∀ P ∈ Q, (Pι P.I).I = P.I := by
    intro P hP
    have h : ∃ P' ∈ Q, P'.I = P.I := ⟨P, hP, rfl⟩
    have h' : Pι P.I = h.choose := by simp [Pι, h]
    rw [h']
    exact h.choose_spec.2
  have h := h1 ch J ℓ k Q hQ Pι hPι hgm hgb hg0
  set D : ℝ := 15 * R * L with hD
  -- the number of time intervals
  have hcard : ((Q.image Multitile.I).card : ℝ) ≤ 2 * R := by
    have hc := card_mul_le_of_dyadic_subset (A := Q.image Multitile.I) (L := L)
      (a := J.center - 2 ^ (ℓ + 1) * J.length / 2) (b := J.center + 2 ^ (ℓ + 1) * J.length / 2)
      (by have : (0 : ℝ) < 2 ^ (ℓ + 1) := by positivity
          nlinarith)
      (fun I hI => by
        obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hI
        exact (hQ P hP).1)
      (fun I hI => by
        obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hI
        exact (hQ P hP).2)
    have h2 : J.center + 2 ^ (ℓ + 1) * J.length / 2 - (J.center - 2 ^ (ℓ + 1) * J.length / 2) =
        2 * R * L := by
      have : J.length = 2 ^ k * L := by rw [hLdef]; field_simp
      rw [hRdef, pow_add, pow_add, this]; ring
    rw [h2] at hc
    exact le_of_mul_le_mul_right hc hL
  -- the tail
  have hS : (∑' κ : ℤ, if Disjoint (windowK J k κ).toSet (J.dilate (2 ^ (ℓ + 2))) then
      (∑ I ∈ Q.image Multitile.I, ∫⁻ x in (windowK J k κ).toSet,
        ‖g x * (Pι I).wavePacket ch x‖ₑ ^ 2) ^ (1 / 2 : ℝ) else 0) ≤
      ENNReal.ofReal (36 * Cφ / R) := by
    calc (∑' κ : ℤ, if Disjoint (windowK J k κ).toSet (J.dilate (2 ^ (ℓ + 2))) then
          (∑ I ∈ Q.image Multitile.I, ∫⁻ x in (windowK J k κ).toSet,
            ‖g x * (Pι I).wavePacket ch x‖ₑ ^ 2) ^ (1 / 2 : ℝ) else 0)
        ≤ ∑' κ : ℤ, ∑ I ∈ Q.image Multitile.I, (∫⁻ x in (windowK J k κ).toSet,
            ‖g x * (Pι I).wavePacket ch x‖ₑ ^ 2) ^ (1 / 2 : ℝ) := by
          refine ENNReal.tsum_le_tsum fun κ => ?_
          split_ifs
          · exact sqrt_sum_le_sum_sqrt _ _
          · exact zero_le
      _ = ∑ I ∈ Q.image Multitile.I, ∑' κ : ℤ, (∫⁻ x in (windowK J k κ).toSet,
            ‖g x * (Pι I).wavePacket ch x‖ₑ ^ 2) ^ (1 / 2 : ℝ) :=
          Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)
      _ ≤ ∑ I ∈ Q.image Multitile.I, ENNReal.ofReal (18 * Cφ * (1 + D / (2 * L)) ^
            (-((2 : ℕ) : ℤ))) := by
          refine Finset.sum_le_sum fun I hI => ?_
          obtain ⟨P₁, hP₁, rfl⟩ := Finset.mem_image.1 hI
          have hlen : P₁.I.length = L := (hQ P₁ hP₁).1
          have hIι : (Pι P₁.I).I = P₁.I := hPι P₁ hP₁
          refine tsum_lintegral_window_le (c := P₁.I.center) (D := D) (C := Cφ)
            (fun κ => (windowK J k κ).measurableSet_toSet) (pairwise_disjoint_windowK J k)
            (iUnion_windowK J k) hL ?_ ?_ hCφ (by rw [hD]; nlinarith) ?_
          · intro κ x hx y hy
            have hx2 := hx.2
            have hy1 := hy.1
            rw [Dyadic.right_eq, windowK_length] at hx2
            have hx1 := hx.1
            have hy2 := hy.2
            rw [Dyadic.right_eq, windowK_length] at hy2
            rw [abs_le]
            constructor <;> linarith
          · intro κ
            rw [Dyadic.volume_toSet, windowK_length]
          · filter_upwards [hgb] with x hx
            by_cases hgx : g x = 0
            · rw [hgx, zero_mul, norm_zero]
              split_ifs <;> positivity
            · have hfar := le_abs_sub_center_of_ne_zero (k := k) (hQ P₁ hP₁).2 hg0 hgx
              have hfar' : D ≤ |x - P₁.I.center| := by rw [hD, hRdef]; exact hfar
              rw [ite_eq_left hfar', norm_mul]
              have hb := hφ ρ ch (Pι P₁.I) x
              rw [hIι, hlen] at hb
              calc ‖g x‖ * ‖(Pι P₁.I).wavePacket ch x‖
                  ≤ 1 * (Cφ * (√L)⁻¹ * (1 + |x - P₁.I.center| / L) ^ (-((4 : ℕ) : ℤ))) :=
                    mul_le_mul hx hb (norm_nonneg _) zero_le_one
                _ = _ := one_mul _
      _ = ((Q.image Multitile.I).card : ℝ≥0∞) * ENNReal.ofReal (18 * Cφ *
            (1 + D / (2 * L)) ^ (-((2 : ℕ) : ℤ))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ENNReal.ofReal (36 * Cφ / R) := by
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
          refine ENNReal.ofReal_le_ofReal ?_
          have hε : (1 + D / (2 * L)) ^ (-((2 : ℕ) : ℤ)) ≤ (R ^ 2)⁻¹ := by
            rw [zpow_neg, zpow_natCast]
            refine inv_anti₀ (by positivity) (pow_le_pow_left₀ hR0.le ?_ 2)
            have : D / (2 * L) = 15 * R / 2 := by rw [hD]; field_simp
            rw [this]; linarith
          calc ((Q.image Multitile.I).card : ℝ) * (18 * Cφ * (1 + D / (2 * L)) ^
                (-((2 : ℕ) : ℤ)))
              ≤ (2 * R) * (18 * Cφ * (R ^ 2)⁻¹) := by gcongr
            _ = 36 * Cφ / R := by field_simp; ring
  -- conclusion
  have h2 : ENNReal.ofReal (∑ P ∈ Q, ‖P.coeff ch g‖ ^ 2) ≤
      ENNReal.ofReal (K₁ * L * (36 * Cφ / R) ^ 2) := by
    rw [← hLdef] at h
    have hq : 0 ≤ 36 * Cφ / R := by positivity
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hq]
    exact h.trans (mul_le_mul_right (pow_le_pow_left' hS 2) _)
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h2
  refine h2.trans (le_of_eq ?_)
  have hR2 : R ^ 2 = 4 ^ (k + ℓ) := by
    rw [hRdef, ← pow_mul, mul_comm, pow_mul, add_comm]; norm_num
  rw [div_pow, hR2, one_div, inv_pow]
  field_simp

end PrimeCarleson.Proof.Oplus
