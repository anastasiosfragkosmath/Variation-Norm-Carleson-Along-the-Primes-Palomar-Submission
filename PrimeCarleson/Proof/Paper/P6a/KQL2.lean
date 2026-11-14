module

public import PrimeCarleson.Proof.Paper.P6a.KQFourier
public import PrimeCarleson.Proof.Paper.P6a.Hyps
public import PrimeCarleson.Proof.Paper.P6a.KQTile2

/-!
# The `ℓ²` bound for the `K_Q`-replacement error

Source: main paper `p:red-var`, L1483–L1502:
`‖V^r(∑_n f(x-n) w_Q(n) E_Q(n) e(λ n) : λ)‖_{ℓ²} ≲_{r,A} Q^{-A} ‖f‖_{ℓ²}`.
The proof expands `w_Q` into its rational Fourier modes `a/q ∈ Γ_Q` (the weights `1/φ(q)` sum to
`|{q ∈ (Q/2, Q]}| ≤ Q`), absorbs the shift `a/q` into the kernel, tiles the multiplier `KQerr_Q` on
`ℝ` (`l:varcarZ` needs `k̂` supported in an interval of length `1/10`; `P6a/KQTile.lean`,
`P6a/KQTile2.lean`), and applies `l:varcarZ` (hypothesis `VarCarZ`) to each piece.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson

/-- Homogeneity of `varOp` in a constant factor of the weight. -/
theorem varOp_const_mul {r : ℝ} (hr : 0 < r) (c : ℂ) (v : ℤ → ℂ) (f : ℤ →₀ ℂ) (x : ℤ) :
    varOp r (fun n => c * v n) (⇑f) x = ‖c‖ₑ * varOp r v (⇑f) x := by
  rw [varOp_eq, varOp_eq]
  have : (fun lam => weightedModSum (fun n => c * v n) (⇑f) lam x) =
      c • (fun lam => weightedModSum v (⇑f) lam x) := by
    funext lam
    simp only [weightedModSum_eq_sum_of_finsupp, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [this, PrimeCarleson.Proof.Common.rVariationOn_const_smul hr]

/-- **The `ℓ²` bound for the `K_Q`-replacement error** (Source: main paper `p:red-var`,
L1483–L1502): for `r > 2`, every `A` and every `Q ≥ 1`,
`‖V^r(∑_n f(x-n) w_Q(n) E_Q(n) e(λ n) : λ)‖_{ℓ²} ≤ C_{r,A} Q^{-A} ‖f‖_{ℓ²}`; here `E_Q` is the error
weight `∑_{k ≥ Q^{1/D₀}} ψ_k - K_Q`; `l:varcarZ` enters through `VarCarZ r`. -/
theorem KQ_error_l2 (S : KQSetup) {r : ℝ} (hr : 2 < r) (hV : VarCarZ r) (A : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Q : ℕ, 1 ≤ Q → ∀ f : ℤ →₀ ℂ,
      eLpNorm (varOp r (fun n => wQ Q n * errW S Q n) (⇑f)) (ENNReal.ofReal 2) Measure.count ≤
        ENNReal.ofReal (C * (Q : ℝ) ^ (-A)) * eLpNorm (⇑f) (ENNReal.ofReal 2) Measure.count := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := S.KQerr_eVariation_le (A + 1)
  obtain ⟨C₂, hC₂0, hC₂⟩ := integral_norm_KQerr_le S (A + 1)
  obtain ⟨C_T, hCT0, hCT⟩ := tile_varOp_bound_shift hr hV
  refine ⟨C_T * (C₁ + C₂), by positivity, fun Q hQ f => ?_⟩
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hr0 : 0 < r := by linarith
  obtain ⟨hint, hL⟩ := hC₂ Q hQ
  set B : ℝ := C_T * (C₁ * (Q : ℝ) ^ (-(A + 1)) + C₂ * (Q : ℝ) ^ (-(A + 1))) with hB
  have hB0 : 0 ≤ B := by positivity
  -- the shifted bound for `E_Q`
  have hshift : ∀ c : ℝ, eLpNorm (varOp r (fun n : ℤ => errW S Q n * e (c * (n : ℝ))) (⇑f))
      (ENNReal.ofReal 2) Measure.count ≤
      ENNReal.ofReal B * eLpNorm (⇑f) (ENNReal.ofReal 2) Measure.count := by
    intro c
    have h := hCT (S.KQerr Q) (C₁ * (Q : ℝ) ^ (-(A + 1))) (C₂ * (Q : ℝ) ^ (-(A + 1)))
      (by positivity) (by positivity) hint (hC₁ Q hQ) hL c f
    have hfun : (fun n : ℤ => errW S Q n * e (c * (n : ℝ))) =
        fun n : ℤ => (∫ ξ : ℝ, S.KQerr Q ξ * e ((n : ℝ) * ξ)) * e (c * (n : ℝ)) := by
      funext n; rw [errW_eq_integral]
    rw [hfun]
    exact h.trans (le_of_eq (by rw [hB]))
  -- the expansion of `w_Q`
  set J : Finset (Σ _ : ℕ, ℕ) := (Finset.Ioc (Q / 2) Q).sigma
    (fun q => (Finset.range q).filter (fun a => Nat.Coprime a q)) with hJ
  set cq : (Σ _ : ℕ, ℕ) → ℂ := fun i =>
    ((((ArithmeticFunction.moebius i.1 : ℤ) : ℝ) / (Nat.totient i.1 : ℝ) : ℝ) : ℂ) with hcq
  set sh : (Σ _ : ℕ, ℕ) → ℝ := fun i => (i.2 : ℝ) / (i.1 : ℝ) with hsh
  have hweight : (fun n : ℤ => wQ Q n * errW S Q n) =
      fun n : ℤ => ∑ i ∈ J, cq i * (errW S Q n * e (sh i * (n : ℝ))) := by
    funext n
    rw [wQ_eq_sum_ramanujanSum, Finset.sum_mul, hJ, Finset.sum_sigma]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [ramanujanSum_eq_sum_range, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [hcq, hsh]
    rw [show (a : ℝ) * n / q = (a : ℝ) / q * n by ring]
    push_cast
    ring
  have hcoef : ∑ i ∈ J, ‖cq i‖ₑ ≤ ENNReal.ofReal (Q : ℝ) := by
    have h1 : ∀ i ∈ J, ‖cq i‖ₑ ≤ ENNReal.ofReal (1 / (Nat.totient i.1 : ℝ)) := by
      intro i _
      simp only [hcq]
      rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_div]
      refine ENNReal.ofReal_le_ofReal ?_
      have : |((ArithmeticFunction.moebius i.1 : ℤ) : ℝ)| ≤ 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      have hφ : |(Nat.totient i.1 : ℝ)| = Nat.totient i.1 := abs_of_nonneg (Nat.cast_nonneg _)
      rw [hφ]
      exact div_le_div_of_nonneg_right this (Nat.cast_nonneg _)
    refine (Finset.sum_le_sum h1).trans ?_
    rw [hJ]
    have h2 : ∀ q ∈ Finset.Ioc (Q / 2) Q,
        ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
          ENNReal.ofReal (1 / (Nat.totient q : ℝ)) = 1 := by
      intro q hq
      have hq1 : 1 ≤ q := by
        have := (Finset.mem_Ioc.1 hq).1
        omega
      have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.2 hq1
      rw [Finset.sum_const, nsmul_eq_mul]
      have hcard : (((Finset.range q).filter (fun a => Nat.Coprime a q)).card : ℝ) =
          Nat.totient q := by
        rw [Nat.totient_eq_card_coprime]
        congr 2
        ext a
        simp [Nat.coprime_comm]
      rw [show ((((Finset.range q).filter (fun a => Nat.Coprime a q)).card : ℕ) : ℝ≥0∞) =
        ENNReal.ofReal (((Finset.range q).filter (fun a => Nat.Coprime a q)).card : ℝ) by
          simp, hcard, ← ENNReal.ofReal_mul hφ.le]
      rw [mul_one_div_cancel hφ.ne']
      simp
    calc ∑ x ∈ (Finset.Ioc (Q / 2) Q).sigma
          (fun q => (Finset.range q).filter (fun a => Nat.Coprime a q)),
          ENNReal.ofReal (1 / (Nat.totient x.1 : ℝ))
        = ∑ q ∈ Finset.Ioc (Q / 2) Q, ∑ a ∈ (Finset.range q).filter
            (fun a => Nat.Coprime a q), ENNReal.ofReal (1 / (Nat.totient q : ℝ)) := by
          rw [Finset.sum_sigma]
      _ = ∑ q ∈ Finset.Ioc (Q / 2) Q, (1 : ℝ≥0∞) := Finset.sum_congr rfl h2
      _ ≤ ENNReal.ofReal (Q : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.card_Ioc]
          have : ((Q - Q / 2 : ℕ) : ℝ≥0∞) ≤ ((Q : ℕ) : ℝ≥0∞) := by
            exact_mod_cast Nat.sub_le _ _
          refine this.trans (le_of_eq ?_)
          simp
  -- the variation
  have hpt : ∀ x : ℤ, varOp r (fun n => wQ Q n * errW S Q n) (⇑f) x ≤
      ∑ i ∈ J, ‖cq i‖ₑ * varOp r (fun n : ℤ => errW S Q n * e (sh i * (n : ℝ))) (⇑f) x := by
    intro x
    rw [hweight]
    refine (varOp_sum_weight_le (by linarith) J
      (fun i n => cq i * (errW S Q n * e (sh i * (n : ℝ)))) f x).trans ?_
    exact Finset.sum_le_sum fun i _ => (varOp_const_mul hr0 _ _ f x).le
  -- the `ℓ²` norm
  calc eLpNorm (varOp r (fun n => wQ Q n * errW S Q n) (⇑f)) (ENNReal.ofReal 2) Measure.count
      ≤ eLpNorm (fun x => ∑ i ∈ J, ‖cq i‖ₑ * varOp r (fun n : ℤ => errW S Q n *
          e (sh i * (n : ℝ))) (⇑f) x) (ENNReal.ofReal 2) Measure.count :=
        eLpNorm_count_mono_enn hpt _
    _ ≤ ∑ i ∈ J, eLpNorm (fun x => ‖cq i‖ₑ * varOp r (fun n : ℤ => errW S Q n *
          e (sh i * (n : ℝ))) (⇑f) x) (ENNReal.ofReal 2) Measure.count :=
        eLpNorm_count_finset_sum_le _ _ (by norm_num)
    _ = ∑ i ∈ J, ‖cq i‖ₑ * eLpNorm (varOp r (fun n : ℤ => errW S Q n *
          e (sh i * (n : ℝ))) (⇑f)) (ENNReal.ofReal 2) Measure.count :=
        Finset.sum_congr rfl fun i _ => eLpNorm_count_const_mul _ _ (by norm_num)
    _ ≤ ∑ i ∈ J, ‖cq i‖ₑ * (ENNReal.ofReal B * eLpNorm (⇑f) (ENNReal.ofReal 2) Measure.count) :=
        Finset.sum_le_sum fun i _ => mul_le_mul' le_rfl (hshift _)
    _ = (∑ i ∈ J, ‖cq i‖ₑ) * (ENNReal.ofReal B * eLpNorm (⇑f) (ENNReal.ofReal 2)
          Measure.count) := by rw [Finset.sum_mul]
    _ ≤ ENNReal.ofReal (Q : ℝ) * (ENNReal.ofReal B * eLpNorm (⇑f) (ENNReal.ofReal 2)
          Measure.count) := mul_le_mul' hcoef le_rfl
    _ = ENNReal.ofReal ((Q : ℝ) * B) * eLpNorm (⇑f) (ENNReal.ofReal 2) Measure.count := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hQ0.le]
    _ = ENNReal.ofReal (C_T * (C₁ + C₂) * (Q : ℝ) ^ (-A)) *
          eLpNorm (⇑f) (ENNReal.ofReal 2) Measure.count := by
        congr 2
        have : (Q : ℝ) * (Q : ℝ) ^ (-(A + 1)) = (Q : ℝ) ^ (-A) := by
          have e : (Q : ℝ) ^ (-A) = (Q : ℝ) ^ (1 + -(A + 1)) := by congr 1; ring
          rw [e, Real.rpow_add hQ0, Real.rpow_one]
        rw [hB]
        calc (Q : ℝ) * (C_T * (C₁ * (Q : ℝ) ^ (-(A + 1)) + C₂ * (Q : ℝ) ^ (-(A + 1))))
            = C_T * (C₁ + C₂) * ((Q : ℝ) * (Q : ℝ) ^ (-(A + 1))) := by ring
          _ = _ := by rw [this]

end PrimeCarleson.Proof.Paper
