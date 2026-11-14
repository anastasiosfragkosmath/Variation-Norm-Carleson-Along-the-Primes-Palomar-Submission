module

public import PrimeCarleson.Proof.Paper.P9.LocalBound
public import PrimeCarleson.Proof.Paper.P9.Reduction
public import PrimeCarleson.Proof.Paper.P9.Dense

/-!
# `p:global-shell-var`: `‖V^{Q,ρ} f‖_{ℓ²} ≤ C(ρ, δ) Q^δ ‖f‖_{ℓ²}`

Source: main paper `p:global-shell-var`, L1956–L2072 (the root L1956–L1958, `e:cheapvarbound`, the
choice of the exponent, the reduction to intervals, and the passage from finite `T ⊂ 𝕋` to `𝕋`, in
`Dense.lean`), in the form with a power loss `Q^δ`.

* `d1_exponent_choice` (the choice of the exponent): for `ρ > 2`, `0 < δ ≤ 1`,
  `s_e(ρ, δ) = 2 + δ(ρ - 2)/ρ` has `2 < s_e < ρ` and `γ(ρ, s_e) = δ/s_e < δ/2`;
* `global_shell_var`: for the fixed `K_Q`-data `S` with the smallness conditions (C1) `SupportBlock`
  and (C2) `SupportScale S.δ (1/16)` (the radius `δ₀`; the interval constant is `c = 1/4`), every
  `ρ > 2` and `δ > 0`, and the input `l:varcarZ` (`∀ s > 2 ∃ C, LVarCarZ s C`, a hypothesis here,
  proved in `P7/`): `∃ C, ∀ Q = 2^j, ∀ f finitely supported, ‖V^{Q,ρ} f‖_{ℓ²} ≤ C Q^δ ‖f‖_{ℓ²}`.

The bound `C(ρ, δ) Q^δ` uses `Q^{δ/2} loglog(10+Q) ≤ C_δ Q^δ`.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Goal0 PrimeCarleson.Proof.Common

/-- **The choice of the exponent**: `s_e(ρ, δ) = 2 + δ(ρ - 2)/ρ` satisfies
`2 < s_e < ρ` and `γ(ρ, s_e) = δ / s_e < δ/2`, for `ρ > 2` and `0 < δ < ρ`. -/
theorem d1_exponent_choice {ρ δ : ℝ} (hρ : 2 < ρ) (hδ : 0 < δ) (hδρ : δ < ρ) :
    2 < 2 + δ * (ρ - 2) / ρ ∧ 2 + δ * (ρ - 2) / ρ < ρ ∧
      entropyGamma ρ (2 + δ * (ρ - 2) / ρ) = δ / (2 + δ * (ρ - 2) / ρ) ∧
      δ / (2 + δ * (ρ - 2) / ρ) < δ / 2 := by
  have hρ0 : 0 < ρ := by linarith
  have h1 : 0 < δ * (ρ - 2) / ρ := by
    have : 0 < ρ - 2 := by linarith
    positivity
  have hs : 2 < 2 + δ * (ρ - 2) / ρ := by linarith
  refine ⟨hs, ?_, ?_, ?_⟩
  · have : δ * (ρ - 2) / ρ < ρ - 2 := by
      rw [div_lt_iff₀ hρ0]
      nlinarith
    linarith
  · unfold entropyGamma
    have hρ2 : ρ - 2 ≠ 0 := by linarith
    have hsne : (2 + δ * (ρ - 2) / ρ) ≠ 0 := by linarith
    field_simp
    ring
  · exact div_lt_div_of_pos_left hδ (by norm_num) hs

/-- `log log (10 + Q) ≤ C_ε Q^ε` for `Q ≥ 1`. -/
theorem loglog_le_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℝ, 1 ≤ Q → Real.log (Real.log (10 + Q)) ≤ C * Q ^ ε := by
  refine ⟨(11 : ℝ) ^ ε / ε, by positivity, fun Q hQ => ?_⟩
  have hQ0 : 0 < Q := by linarith
  have h1 : Real.log (Real.log (10 + Q)) ≤ Real.log (10 + Q) :=
    Real.log_le_self (Real.log_nonneg (by linarith))
  have h2 : Real.log (10 + Q) ≤ (10 + Q) ^ ε / ε := Real.log_le_rpow_div (by linarith) hε
  have h3 : (10 + Q) ^ ε ≤ ((11 : ℝ) * Q) ^ ε :=
    Real.rpow_le_rpow (by linarith) (by linarith) hε.le
  rw [Real.mul_rpow (by norm_num) hQ0.le] at h3
  calc Real.log (Real.log (10 + Q)) ≤ (10 + Q) ^ ε / ε := h1.trans h2
    _ ≤ (11 ^ ε * Q ^ ε) / ε := by gcongr
    _ = 11 ^ ε / ε * Q ^ ε := by ring

/-- `ENNReal` bookkeeping: `3 · (2Q · K₁ g τ ‖f‖) + 2 · (2Q · 15 C₀ τ ‖f‖) =
(6 K₁ g (Qτ) + 60 C₀ (Qτ)) ‖f‖`. -/
theorem enn_combine {Qr K1 C₀ τ g : ℝ} (hQ : 0 ≤ Qr) (hK1 : 0 ≤ K1) (hC₀ : 0 ≤ C₀)
    (hτ : 0 ≤ τ) (hg : 0 ≤ g) (l : ℝ≥0∞) :
    3 * (ENNReal.ofReal (2 * Qr) * (ENNReal.ofReal (K1 * g * τ) * l)) +
      2 * (ENNReal.ofReal (2 * Qr) * (ENNReal.ofReal (15 * C₀ * τ) * l)) =
    ENNReal.ofReal (6 * K1 * g * (Qr * τ) + 60 * C₀ * (Qr * τ)) * l := by
  have key : ∀ (c u v : ℝ), 0 ≤ c → 0 ≤ u →
      ENNReal.ofReal c * (ENNReal.ofReal u * (ENNReal.ofReal v * l)) =
        ENNReal.ofReal (c * u * v) * l := by
    intro c u v hc hu
    rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul hc, ← ENNReal.ofReal_mul (mul_nonneg hc hu)]
  rw [← ENNReal.ofReal_ofNat 3, ← ENNReal.ofReal_ofNat 2, key 3 _ _ (by norm_num) (by positivity),
    key 2 _ _ (by norm_num) (by positivity), ← add_mul, ← ENNReal.ofReal_add (by positivity)
      (by positivity)]
  congr 2
  ring

/-- `V^{Q,ρ} f(x)` is the `ρ`-variation over `[0, 1)` of `λ ↦ T^Q_λ f(x)`. -/
theorem VQr_eq (S : KQSetup) (ρ : ℝ) (Q : ℕ) (f : ℤ → ℂ) (x : ℤ) :
    S.VQr ρ Q f x = rVariationOn ρ (Set.Ico 0 1) (fun t => S.TQ Q t f x) :=
  PrimeCarleson.Proof.Common.rVariation_eq_rVariationOn ρ (fun t => S.TQ Q t f x)

/-- **From finite `T` to `𝕋`** (Source: main paper `p:global-shell-var`, L1998, first
reduction): if every finite `T ⊂ [0, 1)` has `‖V^ρ(T^Q_λ f(x) : T)‖_{ℓ²_x} ≤ B`, so has
`V^{Q,ρ}f`. -/
theorem variation_of_finite_bounds (S : KQSetup) (Q : ℕ) {ρ : ℝ} (hρ : 0 < ρ) (f : ℤ →₀ ℂ)
    {B : ℝ≥0∞} (h : ∀ T : Set ℝ, T.Finite → T ⊆ Set.Ico 0 1 →
      (∑' x : ℤ, rVariationOn ρ T (fun t => S.TQ Q t f x) ^ 2) ^ (1 / 2 : ℝ) ≤ B) :
    (∑' x : ℤ, (S.VQr ρ Q f x) ^ 2) ^ (1 / 2 : ℝ) ≤ B := by
  set F : ℕ → ℤ → ℝ≥0∞ := fun n x => rVariationOn ρ (dyadicGridIo n) (fun t => S.TQ Q t f x)
    with hF
  have hFmono : Monotone F := fun n m hnm x =>
    PrimeCarleson.Proof.Common.rVariationOn_mono_set (dyadicGridIo_mono hnm) _
  have hsup := tsum_sq_iSup_le hFmono fun n =>
    h _ (dyadicGridIo_finite n) (dyadicGridIo_subset_Ico n)
  have hpt : ∀ x : ℤ, S.VQr ρ Q f x ≤ ⨆ n, F n x := fun x => by
    rw [VQr_eq]
    exact rVariationOn_Ico_le_iSup hρ (S.continuous_TQ Q f x)
  calc (∑' x : ℤ, (S.VQr ρ Q f x) ^ 2) ^ (1 / 2 : ℝ)
      ≤ (∑' x : ℤ, (⨆ n, F n x) ^ 2) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow (ENNReal.tsum_le_tsum fun x => by
          exact pow_le_pow_left' (hpt x) 2) (by norm_num)
    _ ≤ B := hsup

/-- **Reduction of the shell bound to the local bounds** (with
`c = 1/4`, `ℓ = Q^{-2}/4`, `M = 4 Q²` intervals): if the local variation bound (with constant
`K₁ Q^γ τ`) and the single-`λ` bound (constant `15 C₀ τ`) hold, every finite `T ⊂ [0, 1)` has
`‖V^ρ(T^Q_λ f : T)‖_{ℓ²} ≤ (6 K₁ Q^γ + 60 C₀) Q τ ‖f‖`. -/
theorem finite_T_bound (S : KQSetup) {ρ : ℝ} (hρ : 2 ≤ ρ) (j : ℕ) (f : ℤ →₀ ℂ)
    {K1 C₀ γe τ : ℝ} (hK1 : 0 ≤ K1) (hC₀ : 0 ≤ C₀) (hτ0 : 0 ≤ τ)
    (hV : ∀ (u : ℝ) (T : Set ℝ), T.Finite → T ⊆ Set.Ico 0 1 →
      T ⊆ Set.Icc u (u + (1 / 4) / ((2 : ℝ) ^ j) ^ 2) →
      (∑' x : ℤ, rVariationOn ρ T (fun t => S.TQ (2 ^ j) t f x) ^ 2) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal (K1 * ((2 : ℝ) ^ j) ^ γe * τ) * l2enorm (⇑f))
    (hB : ∀ t ∈ Set.Ico (0 : ℝ) 1, (∑' x : ℤ, ‖S.TQ (2 ^ j) t f x‖ₑ ^ 2) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (15 * C₀ * τ) * l2enorm (⇑f))
    (T : Set ℝ) (hT : T.Finite) (hT01 : T ⊆ Set.Ico 0 1) :
    (∑' x : ℤ, rVariationOn ρ T (fun t => S.TQ (2 ^ j) t f x) ^ 2) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (6 * K1 * ((2 : ℝ) ^ j) ^ γe * (((2 : ℝ) ^ j) * τ) +
        60 * C₀ * (((2 : ℝ) ^ j) * τ)) * l2enorm (⇑f) := by
  have hQr0 : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  have hQ2 : ((2 : ℝ) ^ j) ^ 2 = (4 : ℝ) ^ j := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hℓ : (0 : ℝ) < (1 / 4) / ((2 : ℝ) ^ j) ^ 2 := by positivity
  have hM : 1 / ((1 / 4) / ((2 : ℝ) ^ j) ^ 2) ≤ ((4 * 4 ^ j : ℕ) : ℝ) := by
    have : (1 : ℝ) / ((1 / 4) / ((2 : ℝ) ^ j) ^ 2) = 4 * ((2 : ℝ) ^ j) ^ 2 := by field_simp
    rw [this, hQ2]
    push_cast
    exact le_refl _
  have hsqrtM : Real.sqrt ((4 * 4 ^ j : ℕ) : ℝ) = 2 * (2 : ℝ) ^ j := by
    have : ((4 * 4 ^ j : ℕ) : ℝ) = (2 * (2 : ℝ) ^ j) ^ 2 := by
      push_cast; rw [mul_pow, hQ2]; norm_num
    rw [this, Real.sqrt_sq (by positivity)]
  have hsplit := split_reduction hρ hℓ hM (fun x lam => S.TQ (2 ^ j) lam f x) hV hB hT hT01
  rw [hsqrtM] at hsplit
  refine hsplit.trans (le_of_eq ?_)
  exact enn_combine hQr0.le hK1 hC₀ hτ0 (Real.rpow_nonneg hQr0.le _) _

/-- The final constant: `(6 K₁ Q^γ + 60 C₀) · 2 C_t · loglog(10 + Q) ≤ C Q^δ` for `γ ≤ δ₁/2`,
`δ₁ ≤ δ`, `loglog(10 + Q) ≤ C_l Q^{δ₁/2}`. -/
theorem const_bound {Qr K1 C₀ Ct Cl γe δ₁ δ L : ℝ} (hQr1 : 1 ≤ Qr) (hK1 : 0 ≤ K1)
    (hC₀ : 0 ≤ C₀) (hCt : 0 ≤ Ct) (hγ : γe ≤ δ₁ / 2) (hδ₁0 : 0 < δ₁) (hδ : δ₁ ≤ δ)
    (hL : L ≤ Cl * Qr ^ (δ₁ / 2)) (hL0 : 0 ≤ L) :
    (6 * K1 * Qr ^ γe + 60 * C₀) * (2 * Ct) * L ≤
      ((6 * K1 + 60 * C₀) * (2 * Ct) * Cl) * Qr ^ δ := by
  have hQr0 : 0 < Qr := by linarith
  have h1 : Qr ^ γe ≤ Qr ^ (δ₁ / 2) := Real.rpow_le_rpow_of_exponent_le hQr1 hγ
  have h3 : Qr ^ δ₁ ≤ Qr ^ δ := Real.rpow_le_rpow_of_exponent_le hQr1 hδ
  have h4 : Qr ^ (δ₁ / 2) * Qr ^ (δ₁ / 2) = Qr ^ δ₁ := by
    rw [← Real.rpow_add hQr0]; congr 1; ring
  have hq1' : 1 ≤ Qr ^ (δ₁ / 2) := Real.one_le_rpow hQr1 (by positivity)
  have hcoef : 6 * K1 * Qr ^ γe + 60 * C₀ ≤ (6 * K1 + 60 * C₀) * Qr ^ (δ₁ / 2) := by
    nlinarith [mul_le_mul_of_nonneg_left h1 hK1]
  have hCl0 : 0 ≤ Cl := by
    by_contra hneg
    push Not at hneg
    have : Cl * Qr ^ (δ₁ / 2) < 0 := mul_neg_of_neg_of_pos hneg (by positivity)
    linarith
  calc (6 * K1 * Qr ^ γe + 60 * C₀) * (2 * Ct) * L
      ≤ ((6 * K1 + 60 * C₀) * Qr ^ (δ₁ / 2)) * (2 * Ct) * (Cl * Qr ^ (δ₁ / 2)) := by gcongr
    _ = ((6 * K1 + 60 * C₀) * (2 * Ct) * Cl) * Qr ^ δ₁ := by rw [← h4]; ring
    _ ≤ ((6 * K1 + 60 * C₀) * (2 * Ct) * Cl) * Qr ^ δ := by gcongr

/-- **`p:global-shell-var`, with the loss `Q^δ`**, see the module docstring. -/
theorem global_shell_var (S : KQSetup) (hS : S.P.SupportBlock S.δ)
    (hSc : S.P.SupportScale S.δ (1 / 16)) {ρ δ : ℝ} (hρ : 2 < ρ) (hδ : 0 < δ)
    (hvc : ∀ s : ℝ, 2 < s → ∃ C : ℝ, 0 ≤ C ∧ LVarCarZ s C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : ℕ) (f : ℤ →₀ ℂ),
      (∑' x : ℤ, (S.VQr ρ (2 ^ j) f x) ^ 2) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal (C * ((2 : ℝ) ^ j) ^ δ) * l2enorm (⇑f) := by
  classical
  have hδ₁0 : 0 < min δ 1 := lt_min hδ one_pos
  obtain ⟨hs, hsρ, hγ, hγlt⟩ := d1_exponent_choice hρ hδ₁0
    (lt_of_le_of_lt (min_le_right _ _) (by linarith))
  obtain ⟨Cv, hCv0, hv⟩ := hvc _ hs
  have hSc' : S.P.SupportScale S.δ ((1 / 4) / 4) := by
    have : ((1 : ℝ) / 4) / 4 = 1 / 16 := by norm_num
    rw [this]; exact hSc
  obtain ⟨C₀, hC₀, hloc⟩ := S.local_bound (c := 1 / 4) (by norm_num) le_rfl hS hSc' hs hsρ hv hCv0
  obtain ⟨Ct, hCt, hτ⟩ := exists_gcoef_bound
  obtain ⟨Cl, hCl, hll⟩ := loglog_le_rpow (ε := min δ 1 / 2) (by positivity)
  have hE := entropyConst_pos hs hsρ
  set K1 : ℝ := 15 * entropyConst ρ (2 + min δ 1 * (ρ - 2) / ρ) * (Cv * C₀) with hK1
  have hK10 : 0 ≤ K1 := by positivity
  refine ⟨(6 * K1 + 60 * C₀) * (2 * Ct) * Cl, by positivity, fun j f => ?_⟩
  have hQr1 : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
  have hQr0 : (0 : ℝ) < (2 : ℝ) ^ j := by linarith
  have hQcast : ((2 ^ j : ℕ) : ℝ) = (2 : ℝ) ^ j := by simp
  have hlog0 : 0 ≤ Real.log (Real.log (10 + (2 : ℝ) ^ j)) := by
    refine Real.log_nonneg ?_
    have h10 : Real.exp 1 ≤ 10 + (2 : ℝ) ^ j := by
      have := Real.exp_one_lt_d9; linarith
    exact (Real.le_log_iff_exp_le (by positivity)).2 h10
  have hτ0 : 0 ≤ 2 * Ct * Real.log (Real.log (10 + (2 : ℝ) ^ j)) / (2 : ℝ) ^ j := by positivity
  have hτb : ∀ r ∈ gammaQ (2 ^ j), ‖gcoef r‖ ≤
      2 * Ct * Real.log (Real.log (10 + (2 : ℝ) ^ j)) / (2 : ℝ) ^ j := by
    intro r hr
    have := hτ (2 ^ j) Nat.one_le_two_pow r hr
    rwa [hQcast] at this
  have hloc' := hloc j _ hτ0 hτb
  have hV : ∀ (u : ℝ) (T : Set ℝ), T.Finite → T ⊆ Set.Ico 0 1 →
      T ⊆ Set.Icc u (u + (1 / 4) / ((2 : ℝ) ^ j) ^ 2) →
      (∑' x : ℤ, rVariationOn ρ T (fun t => S.TQ (2 ^ j) t f x) ^ 2) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal (K1 * ((2 : ℝ) ^ j) ^ entropyGamma ρ (2 + min δ 1 * (ρ - 2) / ρ) *
          (2 * Ct * Real.log (Real.log (10 + (2 : ℝ) ^ j)) / (2 : ℝ) ^ j)) * l2enorm (⇑f) :=
    fun u T hT h01 hJ => (hloc' u T hT h01 hJ f).1
  have hℓ0 : (0 : ℝ) < (1 / 4) / ((2 : ℝ) ^ j) ^ 2 := by positivity
  have hB : ∀ t ∈ Set.Ico (0 : ℝ) 1, (∑' x : ℤ, ‖S.TQ (2 ^ j) t f x‖ₑ ^ 2) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (15 * C₀ * (2 * Ct * Real.log (Real.log (10 + (2 : ℝ) ^ j)) /
        (2 : ℝ) ^ j)) * l2enorm (⇑f) := by
    intro t ht
    have hsub : ({t} : Set ℝ) ⊆ Set.Icc t (t + (1 / 4) / ((2 : ℝ) ^ j) ^ 2) :=
      Set.singleton_subset_iff.2 ⟨le_refl t, by linarith⟩
    exact (hloc' t {t} (Set.finite_singleton t) (by simpa using ht) hsub f).2 t rfl
  have hfin := finite_T_bound S hρ.le j f hK10 hC₀ hτ0 hV hB
  refine (variation_of_finite_bounds S (2 ^ j) (by linarith) f hfin).trans ?_
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  have hqτ : (2 : ℝ) ^ j * (2 * Ct * Real.log (Real.log (10 + (2 : ℝ) ^ j)) / (2 : ℝ) ^ j) =
      2 * Ct * Real.log (Real.log (10 + (2 : ℝ) ^ j)) := by field_simp
  rw [hqτ]
  have hconst := const_bound (Qr := (2 : ℝ) ^ j) (K1 := K1) (C₀ := C₀) (Ct := Ct) (Cl := Cl)
    (γe := entropyGamma ρ (2 + min δ 1 * (ρ - 2) / ρ)) (δ₁ := min δ 1) (δ := δ)
    (L := Real.log (Real.log (10 + (2 : ℝ) ^ j))) hQr1 hK10 hC₀ hCt.le (by rw [hγ]; exact hγlt.le)
    hδ₁0 (min_le_left _ _) (hll _ hQr1) hlog0
  calc 6 * K1 * ((2 : ℝ) ^ j) ^ entropyGamma ρ (2 + min δ 1 * (ρ - 2) / ρ) *
        (2 * Ct * Real.log (Real.log (10 + (2 : ℝ) ^ j))) +
        60 * C₀ * (2 * Ct * Real.log (Real.log (10 + (2 : ℝ) ^ j)))
      = (6 * K1 * ((2 : ℝ) ^ j) ^ entropyGamma ρ (2 + min δ 1 * (ρ - 2) / ρ) + 60 * C₀) *
          (2 * Ct) * Real.log (Real.log (10 + (2 : ℝ) ^ j)) := by ring
    _ ≤ _ := hconst

end PrimeCarleson.Proof.Paper
