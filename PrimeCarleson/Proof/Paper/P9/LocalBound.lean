module

public import PrimeCarleson.Proof.Paper.P9.NormRepl
public import PrimeCarleson.Proof.Paper.P9.A1B1
public import PrimeCarleson.Proof.Paper.P9.GammaSep
public import PrimeCarleson.Proof.Paper.P9.VarCarInput
public import PrimeCarleson.Proof.Paper.P2.Weights

/-!
# The `J`-local bound of `p:global-shell-var`

Source: main paper `p:global-shell-var`, L2020–L2071.

* `exists_gcoef_bound` (the totient bound, L2064–L2071): `|μ(q)/φ(q)| ≤ 2 C loglog(10+Q)/Q`
  for `Q/2 < q ≤ Q` (`e:totientbound`);
* `famNorm_densR_le`: `(∑_{a/q} ‖F_{a/q}‖²)^{1/2} ≤ τ ‖f‖` (the norm replacement and the totient
  weights);
* `KQSetup.local_bound` (the application of `p:variable`, L2064–L2070): for the interval
`J = [u, u + ℓ]`, `ℓ = c Q^{-2}`, and finite `T ⊂ J ∩ [0, 1)`, with
  `Γ_Q`, `g_{a/q}(x) = e(a x/q)`, `I = 3J`, `A₁² = 2/c_I`, `B₁ = Q A₁` (`c_I = 3ℓ/100`), at the
  fixed exponent `s`: `‖V^ρ(T^Q_λ f : λ ∈ T)‖_{ℓ²} ≤ 15 E(ρ,s) C_s C₀ Q^{γ(ρ,s)} τ_Q ‖f‖`,
  and the single-`λ` bound `‖T^Q_λ f‖_{ℓ²} ≤ 15 C₀ τ_Q ‖f‖` (Theorem B(b)), where
  `τ_Q ≥ max_q |μ(q)|/φ(q)`, `C₀` the uniform sup/BV bound of `K̂_Q`, `C_s` the constant of
  `LVarCarZ s`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal FourierTransform SchwartzMap

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Goal0 PrimeCarleson.Proof.Common

/-- **The totient bound** (Source: main paper `p:global-shell-var`, L2064–L2071):
`|μ(q)/φ(q)| ≤ 2 C loglog(10+Q)/Q` for `Q/2 < q ≤ Q`, with the absolute constant `C` of
`e:totientbound`. -/
theorem exists_gcoef_bound : ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ, 1 ≤ Q → ∀ r ∈ gammaQ Q,
    ‖gcoef r‖ ≤ 2 * C * Real.log (Real.log (10 + (Q : ℝ))) / Q := by
  obtain ⟨C, hC, h⟩ := inv_totient_le_loglog
  refine ⟨C, hC, fun Q hQ r hr => ?_⟩
  rw [mem_gammaQ_real] at hr
  obtain ⟨_, _, hlo, hhi⟩ := hr
  have hq1 : 1 ≤ r.den := r.den_pos
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hq0 : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have hφ : (0 : ℝ) < Nat.totient r.den := by exact_mod_cast Nat.totient_pos.2 r.den_pos
  have h1 := h r.den hq1
  have hnorm : ‖gcoef r‖ ≤ 1 / (Nat.totient r.den : ℝ) := by
    unfold gcoef
    rw [← Complex.ofReal_div, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hφ]
    have : |((ArithmeticFunction.moebius r.den : ℤ) : ℝ)| ≤ 1 := by
      have := ArithmeticFunction.abs_moebius_le_one (n := r.den)
      exact_mod_cast this
    rw [one_div]
    rw [div_eq_mul_inv]
    exact mul_le_of_le_one_left (inv_nonneg.2 hφ.le) this
  have hlog : Real.log (Real.log (10 + (r.den : ℝ))) ≤ Real.log (Real.log (10 + (Q : ℝ))) := by
    have hq10 : (0 : ℝ) < 10 + r.den := by positivity
    have hlog10 : 0 < Real.log (10 + (r.den : ℝ)) := Real.log_pos (by
      have : (1 : ℝ) ≤ r.den := by exact_mod_cast hq1
      linarith)
    exact Real.log_le_log hlog10 (Real.log_le_log hq10 (by linarith))
  have hL0 : 0 ≤ Real.log (Real.log (10 + (r.den : ℝ))) := by
    refine Real.log_nonneg ?_
    have : (1 : ℝ) ≤ r.den := by exact_mod_cast hq1
    have := Real.add_one_le_exp (1 : ℝ)
    have h10 : Real.exp 1 ≤ 10 + (r.den : ℝ) := by
      have := Real.exp_one_lt_d9; linarith
    exact (Real.le_log_iff_exp_le (by positivity)).2 h10
  calc ‖gcoef r‖ ≤ 1 / (Nat.totient r.den : ℝ) := hnorm
    _ ≤ C * Real.log (Real.log (10 + (r.den : ℝ))) / r.den := h1
    _ ≤ C * Real.log (Real.log (10 + (Q : ℝ))) / r.den := by gcongr
    _ ≤ 2 * C * Real.log (Real.log (10 + (Q : ℝ))) / Q := by
        have hL : 0 ≤ Real.log (Real.log (10 + (Q : ℝ))) := hL0.trans hlog
        rw [div_le_div_iff₀ hq0 hQ0]
        have : (Q : ℝ) ≤ 2 * r.den := by linarith
        have hCL : 0 ≤ C * Real.log (Real.log (10 + (Q : ℝ))) := by positivity
        linarith only [mul_le_mul_of_nonneg_left this hCL]

theorem tsum_enorm_sq_finsupp (f : ℤ →₀ ℂ) :
    ∑' x : ℤ, ‖f x‖ₑ ^ 2 = ENNReal.ofReal (∑ k ∈ f.support, ‖f k‖ ^ 2) := by
  rw [tsum_eq_sum (s := f.support) (fun x hx => by simp [Finsupp.notMem_support_iff.1 hx]),
    ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- **The pieces `F_{a/q}`** (Source: main paper `p:global-shell-var`, L1971–L1983, L1998–L2001 and
L2064–L2071): the densities `densR ϑ f r` of `F_r = (μ(q)/φ(q)) f_r` satisfy
`(∑_r ‖F_r‖²_{ℓ²})^{1/2} ≤ τ ‖f‖_{ℓ²}` if `|μ(q)/φ(q)| ≤ τ`. -/
theorem famNorm_densR_le (Q : ℕ) {θ u ℓ τ : ℝ} {ϑ : ℝ → ℝ} (hc : Continuous ϑ) (hτ0 : 0 ≤ τ)
    (hθ1 : θ < u - ℓ) (hθ2 : u + 2 * ℓ < θ + 1) (hℓ : 0 < ℓ)
    (h01 : ∀ x, 0 ≤ ϑ x ∧ ϑ x ≤ 1) (hsupp : ∀ x, x ∉ Set.Icc (u - ℓ) (u + 2 * ℓ) → ϑ x = 0)
    (hsep : ∀ ξ ξ' : ↥(gammaQ Q), ξ ≠ ξ' → ∀ v : ℤ,
      3 * ℓ < |((ξ : ℚ) : ℝ) - ((ξ' : ℚ) : ℝ) - v|)
    (hτ : ∀ r ∈ gammaQ Q, ‖gcoef r‖ ≤ τ) (f : ℤ →₀ ℂ) :
    famNorm θ (fun (r : ↥(gammaQ Q)) β => densR ϑ f r β) ≤ ENNReal.ofReal τ * l2enorm (⇑f) := by
  have hcont : ∀ r : ↥(gammaQ Q), Continuous (densR ϑ f r) := fun r =>
    (continuous_const.mul (Complex.continuous_ofReal.comp hc)).mul
      ((continuous_fourierZ f).comp (continuous_id.add continuous_const))
  have hI : ∀ r : ↥(gammaQ Q), ∑' x : ℤ, ‖invFZ θ (densR ϑ f r) x‖ₑ ^ 2 =
      ENNReal.ofReal (∫ β in θ..θ + 1, ‖densR ϑ f r β‖ ^ 2) := fun r =>
    tsum_enorm_sq_invFZ (ChartL2.of_continuousOn (hcont r).continuousOn)
  have hJ : ∀ r : ↥(gammaQ Q), ∫ β in θ..θ + 1, ‖densR ϑ f r β‖ ^ 2 ≤
      τ ^ 2 * ∫ β in θ..θ + 1, ϑ β ^ 2 * ‖fourierZ f (β + ((r : ℚ) : ℝ))‖ ^ 2 := by
    intro r
    rw [← intervalIntegral.integral_const_mul]
    have hint1 : IntervalIntegrable (fun β => ‖densR ϑ f r β‖ ^ 2) volume θ (θ + 1) :=
      ((hcont r).norm.pow 2).intervalIntegrable _ _
    have hint2 : IntervalIntegrable
        (fun β => τ ^ 2 * (ϑ β ^ 2 * ‖fourierZ f (β + ((r : ℚ) : ℝ))‖ ^ 2)) volume θ (θ + 1) :=
      (continuous_const.mul ((hc.pow 2).mul (((continuous_fourierZ f).comp
        (continuous_id.add continuous_const)).norm.pow 2))).intervalIntegrable _ _
    refine intervalIntegral.integral_mono_on (by linarith) hint1 hint2 fun β _ => ?_
    have hn : ‖densR ϑ f r β‖ = ‖gcoef r‖ * ϑ β * ‖fourierZ f (β + ((r : ℚ) : ℝ))‖ := by
      unfold densR
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (h01 β).1]
    have h2 : ‖gcoef r‖ ^ 2 ≤ τ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hτ r r.2) 2
    rw [hn]
    calc (‖gcoef r‖ * ϑ β * ‖fourierZ f (β + ((r : ℚ) : ℝ))‖) ^ 2
        = ‖gcoef r‖ ^ 2 * (ϑ β ^ 2 * ‖fourierZ f (β + ((r : ℚ) : ℝ))‖ ^ 2) := by ring
      _ ≤ τ ^ 2 * (ϑ β ^ 2 * ‖fourierZ f (β + ((r : ℚ) : ℝ))‖ ^ 2) :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
  have hsum := sum_integral_theta_le (fun r : ↥(gammaQ Q) => ((r : ℚ) : ℝ)) ϑ hc hθ1 hθ2 hℓ h01
    hsupp hsep f
  have hreal : ∑ r : ↥(gammaQ Q), ∫ β in θ..θ + 1, ‖densR ϑ f r β‖ ^ 2 ≤
      τ ^ 2 * ∑ k ∈ f.support, ‖f k‖ ^ 2 := by
    calc _ ≤ ∑ r : ↥(gammaQ Q), τ ^ 2 * ∫ β in θ..θ + 1,
          ϑ β ^ 2 * ‖fourierZ f (β + ((r : ℚ) : ℝ))‖ ^ 2 := Finset.sum_le_sum fun r _ => hJ r
      _ = τ ^ 2 * ∑ r : ↥(gammaQ Q), ∫ β in θ..θ + 1,
          ϑ β ^ 2 * ‖fourierZ f (β + ((r : ℚ) : ℝ))‖ ^ 2 := by rw [← Finset.mul_sum]
      _ ≤ τ ^ 2 * ∑ k ∈ f.support, ‖f k‖ ^ 2 := by gcongr
  have hnn : ∀ r : ↥(gammaQ Q), 0 ≤ ∫ β in θ..θ + 1, ‖densR ϑ f r β‖ ^ 2 := fun r =>
    intervalIntegral.integral_nonneg (by linarith) fun β _ => by positivity
  unfold famNorm
  simp_rw [hI]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun r _ => hnn r)]
  calc (ENNReal.ofReal (∑ r : ↥(gammaQ Q), ∫ β in θ..θ + 1, ‖densR ϑ f r β‖ ^ 2)) ^ (1 / 2 : ℝ)
      ≤ (ENNReal.ofReal (τ ^ 2 * ∑ k ∈ f.support, ‖f k‖ ^ 2)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hreal) (by norm_num)
    _ = ENNReal.ofReal τ * l2enorm (⇑f) := by
        rw [ENNReal.ofReal_mul (sq_nonneg τ), ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
          ENNReal.ofReal_pow hτ0, enorm_sq_rpow_half, l2enorm, tsum_enorm_sq_finsupp]

/-- **The `J`-local bound** (with the loss `Q^δ`), see the module docstring. -/
theorem KQSetup.local_bound (S : KQSetup) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1 / 4)
    (hS : S.P.SupportBlock S.δ) (hSc : S.P.SupportScale S.δ (c / 4))
    {s ρ Cv : ℝ} (hs : 2 < s) (hsρ : s < ρ) (hv : LVarCarZ s Cv) (hCv : 0 ≤ Cv) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (j : ℕ) (τ : ℝ), 0 ≤ τ → (∀ r ∈ gammaQ (2 ^ j), ‖gcoef r‖ ≤ τ) →
      ∀ (u : ℝ) (T : Set ℝ), T.Finite → T ⊆ Set.Ico 0 1 →
        T ⊆ Set.Icc u (u + c / ((2 : ℝ) ^ j) ^ 2) → ∀ f : ℤ →₀ ℂ,
        (∑' x : ℤ, rVariationOn ρ T (fun t => S.TQ (2 ^ j) t f x) ^ 2) ^ (1 / 2 : ℝ) ≤
          ENNReal.ofReal (15 * entropyConst ρ s * (Cv * C₀) * ((2 : ℝ) ^ j) ^ entropyGamma ρ s *
            τ) * l2enorm (⇑f) ∧
        ∀ t ∈ T, (∑' x : ℤ, ‖S.TQ (2 ^ j) t f x‖ₑ ^ 2) ^ (1 / 2 : ℝ) ≤
          ENNReal.ofReal (15 * C₀ * τ) * l2enorm (⇑f) := by
  classical
  obtain ⟨C₀, hC₀, hC⟩ := S.KQ_multiplier_properties hS hSc
  refine ⟨C₀, hC₀, fun j τ hτ0 hτ u T hT hT01 hTJ f => ?_⟩
  obtain ⟨hKb, hbv, hsup, _⟩ := hC j
  set Qr : ℝ := (2 : ℝ) ^ j with hQr
  have hQr1 : 1 ≤ Qr := one_le_pow₀ (by norm_num)
  have hQr0 : 0 < Qr := by linarith
  have hQcast : ((2 ^ j : ℕ) : ℝ) = Qr := by simp [hQr]
  set ℓ : ℝ := c / Qr ^ 2 with hℓdef
  have hℓ : 0 < ℓ := by positivity
  have hℓc : ℓ ≤ c := div_le_self hc0.le (one_le_pow₀ hQr1)
  have hℓ4 : ℓ ≤ 1 / 4 := hℓc.trans hc1
  have hδN : S.δ / S.P.NQ (2 ^ j) ≤ ℓ / 4 := by
    have h := hSc j
    rw [div_le_iff₀ (S.P.NQ_pos _), hℓdef]
    have : c / Qr ^ 2 / 4 * S.P.NQ (2 ^ j) = c / 4 * S.P.NQ (2 ^ j) / Qr ^ 2 := by ring
    rw [this, le_div_iff₀ (by positivity)]
    linarith
  have hδ0 : 0 ≤ S.δ / S.P.NQ (2 ^ j) := div_nonneg S.δ_pos.le (S.P.NQ_pos _).le
  -- the chart, the interval `I = 3J` and the cutoff data
  set θ : ℝ := u + ℓ / 2 - 1 / 2 with hθ
  set cI : ℝ := 3 * ℓ / 100 with hcI
  have hcI0 : 0 < cI := by positivity
  have hch1 : θ + 4 * cI < u - ℓ := by rw [hθ, hcI]; linarith only [hℓ4]
  have hch2 : u + 2 * ℓ + 4 * cI < θ + 1 := by rw [hθ, hcI]; linarith only [hℓ4]
  obtain ⟨D⟩ := CutoffData.nonempty (θ := θ) (a := u - ℓ) (b := u + 2 * ℓ) hcI0
    (by rw [hcI]; linarith) hch1 hch2
  obtain ⟨ϑ, hϑd, h01, hϑ1, hϑ0⟩ := exists_theta u ℓ hℓ
  have hϑc : Continuous ϑ := hϑd.continuous
  -- the frequencies `Γ_Q`
  have hsep3 : ∀ ξ ξ' : ↥(gammaQ (2 ^ j)), ξ ≠ ξ' → ∀ v : ℤ,
      3 * ℓ < |((ξ : ℚ) : ℝ) - ((ξ' : ℚ) : ℝ) - v| := by
    intro ξ ξ' hne v
    have h := gammaQ_sep ξ.2 ξ'.2 (fun h => hne (Subtype.ext h)) v
    rw [hQcast] at h
    refine lt_of_lt_of_le ?_ h
    rw [hℓdef, ← mul_div_assoc, div_lt_div_iff₀ (by positivity) (by positivity)]
    have hq2 : 0 < Qr ^ 2 := by positivity
    calc 3 * c * (Qr * Qr) = (3 * c) * Qr ^ 2 := by ring
      _ < 1 * Qr ^ 2 := mul_lt_mul_of_pos_right (by linarith only [hc1]) hq2
  have hsep2 : ∀ ξ ξ' : ↥(gammaQ (2 ^ j)), ξ ≠ ξ' → ∀ v : ℤ,
      2 * cI < |((ξ : ℚ) : ℝ) - ((ξ' : ℚ) : ℝ) - v| := fun ξ ξ' hne v => by
    have := hsep3 ξ ξ' hne v
    rw [hcI]; linarith
  -- (A) and (B)
  set A₁ : ℝ := Real.sqrt (2 / cI) with hA₁
  have hA₁0 : 0 ≤ A₁ := Real.sqrt_nonneg _
  have hA₁sq : A₁ ^ 2 = 2 / cI := Real.sq_sqrt (by positivity)
  set B₁ : ℝ := Qr * A₁ with hB₁
  have hB₁0 : 0 ≤ B₁ := by positivity
  let g : ↥(gammaQ (2 ^ j)) → ℤ → ℂ := fun r z => e (((r : ℚ) : ℝ) * (z : ℝ))
  have hA : ∀ (x : ℤ) (w : ↥(gammaQ (2 ^ j)) → ℂ),
      ∑' y : ℤ, ‖D.φ y * ∑ ξ, w ξ * g ξ (x + y)‖ₑ ^ 2 ≤
        ENNReal.ofReal (A₁ ^ 2 * ∑ ξ, ‖w ξ‖ ^ 2) := by
    intro x w
    rw [hA₁sq]
    exact D.A1_bound (fun r : ↥(gammaQ (2 ^ j)) => ((r : ℚ) : ℝ)) hsep2 x w
  have hB : ∀ x : ℤ, ∑' y : ℤ, ∑ ξ, ‖D.φ y * g ξ (x + y)‖ₑ ^ 2 ≤ ENNReal.ofReal (B₁ ^ 2) := by
    intro x
    refine (D.B1_bound (fun r : ↥(gammaQ (2 ^ j)) => ((r : ℚ) : ℝ)) x).trans ?_
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hB₁, mul_pow, hA₁sq]
    have hcard : (Fintype.card ↥(gammaQ (2 ^ j)) : ℝ) ≤ Qr ^ 2 := by
      have := card_gammaQ_le (2 ^ j)
      rw [Fintype.card_coe]
      calc (((gammaQ (2 ^ j)).card : ℕ) : ℝ) ≤ (((2 ^ j) * (2 ^ j) : ℕ) : ℝ) := by
            exact_mod_cast this
        _ = Qr ^ 2 := by push_cast; rw [hQr]; ring
    exact mul_le_mul_of_nonneg_right hcard (by positivity)
  -- admissibility
  let m : ℝ → ℝ → ℂ := fun t β => S.KQmult (2 ^ j) t β
  let H : ↥(gammaQ (2 ^ j)) → ℝ → ℂ := fun r β => densR ϑ f r β
  have hcontH : ∀ r : ↥(gammaQ (2 ^ j)), Continuous (H r) := fun r =>
    (continuous_const.mul (Complex.continuous_ofReal.comp hϑc)).mul
      ((continuous_fourierZ f).comp (continuous_id.add continuous_const))
  have hadm : VarAdmissible θ (u - ℓ) (u + 2 * ℓ) T m H :=
    { meas := fun t _ => S.measurable_KQmult (2 ^ j) t
      bdd := fun t _ => ⟨C₀, fun β _ => by simpa [m, KQSetup.KQmult] using hKb (β - t)⟩
      l2 := fun r => ChartL2.of_continuousOn (hcontH r).continuousOn
      supp := fun r β hβ => by
        simp only [H, densR]
        rw [hϑ0 β hβ]; simp }
  have hchart : ∀ t ∈ T, θ < t - S.δ / S.P.NQ (2 ^ j) ∧ t + S.δ / S.P.NQ (2 ^ j) < θ + 1 := by
    intro t ht
    have := hTJ ht
    have h2 : t ≤ u + ℓ := this.2
    constructor <;> rw [hθ] <;> linarith only [this.1, h2, hδN, hℓ4]
  have hVs : ∀ H' : ℝ → ℂ, ChartL2 θ H' → (∀ β, β ∉ Set.Icc (u - ℓ) (u + 2 * ℓ) → H' β = 0) →
      (∑' x : ℤ, rVariationOn s T (fun t => invFZ θ (fun β => m t β * H' β) x) ^ 2) ^
        (1 / 2 : ℝ) ≤ ENNReal.ofReal (Cv * C₀) * l2enorm (invFZ θ H') :=
    fun H' hH' _ => S.variation_hyp hv (by linarith) hC₀ hCv hbv hsup hKb hT hT01 hchart hH'
  -- the representation
  have hrep : ∀ t ∈ T, ∀ x : ℤ, S.TQ (2 ^ j) t f x = aSum θ g m H t x := by
    intro t ht x
    refine S.TQ_eq_aSum (2 ^ j) (ϑ := ϑ) (hchart t ht).1 (hchart t ht).2 ?_ f x
    intro β hβ
    apply hϑ1
    have hle : |β - t| ≤ S.δ / S.P.NQ (2 ^ j) := by
      by_contra hlt
      exact hβ (S.KQhat_eq_zero _ (not_le.1 hlt))
    rw [abs_le] at hle
    have := hTJ ht
    have h2 : t ≤ u + ℓ := this.2
    constructor <;> linarith only [hle.1, hle.2, this.1, h2, hδN, hℓ4]
  -- the size bounds
  have hchiA : D.chiNorm * A₁ ≤ 15 := by
    have hX := D.sum_norm_sq_chi_le'
    have hX0 : 0 ≤ ∑' y : ℤ, ‖D.χ y‖ ^ 2 := tsum_nonneg fun _ => by positivity
    have h1 : D.chiNorm * A₁ = Real.sqrt ((∑' y : ℤ, ‖D.χ y‖ ^ 2) * (2 / cI)) := by
      rw [CutoffData.chiNorm, hA₁, ← Real.sqrt_mul hX0]
    rw [h1]
    refine Real.sqrt_le_iff.2 ⟨by norm_num, ?_⟩
    calc (∑' y : ℤ, ‖D.χ y‖ ^ 2) * (2 / cI)
        ≤ ((53 / 50) * ((u + 2 * ℓ) - (u - ℓ))) * (2 / cI) := by gcongr
      _ = 212 := by rw [hcI]; field_simp; ring
      _ ≤ 15 ^ 2 := by norm_num
  have hfam : famNorm θ H ≤ ENNReal.ofReal τ * l2enorm (⇑f) :=
    famNorm_densR_le (2 ^ j) hϑc hτ0 (by linarith) (by linarith) hℓ h01 hϑ0 hsep3 hτ f
  have hA₁pos : 0 < A₁ := Real.sqrt_pos.2 (by positivity)
  set γe : ℝ := entropyGamma ρ s with hγe
  have hpow : A₁ ^ (1 - γe) * B₁ ^ γe = A₁ * Qr ^ γe := by
    rw [hB₁, Real.mul_rpow hQr0.le hA₁0, mul_comm (Qr ^ γe), ← mul_assoc,
      ← Real.rpow_add hA₁pos, sub_add_cancel, Real.rpow_one]
  have hE := entropyConst_pos hs hsρ
  have hQg : 0 ≤ Qr ^ γe := Real.rpow_nonneg hQr0.le _
  refine ⟨?_, fun t₀ ht₀ => ?_⟩
  · -- the variation bound
    have hV0 := variable_variation_le D g hadm hs hsρ hT hA₁0 hB₁0 hA hB
      (C := Cv * C₀) (mul_nonneg hCv hC₀) hVs
    have hcongr : ∀ x : ℤ, rVariationOn ρ T (fun t => S.TQ (2 ^ j) t f x) =
        rVariationOn ρ T (fun t => aSum θ g m H t x) := fun x =>
      rVariationOn_congr fun t ht => hrep t ht x
    simp_rw [hcongr]
    refine hV0.trans ?_
    have hcoef : D.chiNorm * entropyConst ρ s * (Cv * C₀) * A₁ ^ (1 - γe) * B₁ ^ γe ≤
        15 * entropyConst ρ s * (Cv * C₀) * Qr ^ γe := by
      rw [mul_assoc _ (A₁ ^ (1 - γe)) (B₁ ^ γe), hpow]
      have : D.chiNorm * entropyConst ρ s * (Cv * C₀) * (A₁ * Qr ^ γe) =
          (D.chiNorm * A₁) * (entropyConst ρ s * (Cv * C₀) * Qr ^ γe) := by ring
      rw [this, show 15 * entropyConst ρ s * (Cv * C₀) * Qr ^ γe =
        15 * (entropyConst ρ s * (Cv * C₀) * Qr ^ γe) by ring]
      exact mul_le_mul_of_nonneg_right hchiA (by positivity)
    calc ENNReal.ofReal (D.chiNorm * entropyConst ρ s * (Cv * C₀) * A₁ ^ (1 - γe) *
          B₁ ^ γe) * famNorm θ H
        ≤ ENNReal.ofReal (15 * entropyConst ρ s * (Cv * C₀) * Qr ^ γe) *
            (ENNReal.ofReal τ * l2enorm (⇑f)) :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal hcoef) hfam
      _ = _ := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  · -- the single-`λ` bound
    have hb := variable_base_point D g hadm ht₀ hA₁0 hA hC₀
      (fun β _ => by simpa [m, KQSetup.KQmult] using hKb (β - t₀))
    have hcongr : ∀ x : ℤ, S.TQ (2 ^ j) t₀ f x = aSum θ g m H t₀ x := fun x => hrep t₀ ht₀ x
    simp_rw [hcongr]
    refine hb.trans ?_
    calc ENNReal.ofReal (D.chiNorm * A₁ * C₀) * famNorm θ H
        ≤ ENNReal.ofReal (15 * C₀) * (ENNReal.ofReal τ * l2enorm (⇑f)) :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hchiA hC₀)) hfam
      _ = _ := by rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]

end PrimeCarleson.Proof.Paper
