module

public import PrimeCarleson.Proof.Paper.P6c.Tile
public import PrimeCarleson.Proof.Paper.P6a.KQL2
public import PrimeCarleson.Proof.Paper.P6a.KQReplace

/-!
# The maximal `K_Q`-replacement

Source: main paper `s:red`, L1527–L1528: "the replacement of `∑_{Q^{1/D₀} ≤ k} ψ_k` by `K_Q` is
identical". Maximal counterpart of `KQ_error_l2`/`KQ_replacement` of `P6a/KQL2.lean`,
`P6a/KQReplace.lean`.

* `errW_sup_bound`: for `1 < p < ∞` and every `A`,
  `‖sup_λ|∑_n f(x-n) w_Q(n) E_Q(n) e(λ n)|‖_{ℓ^p} ≲_{p,A} Q^{-A} ‖f‖_{ℓ^p}`, `E_Q = ∑_{k ≥ Q^{1/D₀}}
  ψ_k - K_Q`: `w_Q` is expanded into its rational Fourier modes `a/q ∈ Γ_Q` (`∑ 1/φ(q) ≤ Q`), the
  characters `e(a n / q)` do not change the supremum over `λ` (`supOp_mul_e`), and the error
  multiplier `KQerr_Q` is estimated by `tile_sup_bound`: no interpolation is needed, because the
  supremum is bounded directly for every `p > 1`;
* `KQ_replacement_sup`: `‖sup_λ|∑_n f(x-n) w_Q(n) ∑_{k ≥ Q^{1/D₀}} ψ_k(n) e(λ n)|‖_{ℓ^p} ≤
  ‖C^Q f‖_{ℓ^p} + C Q^{-100} ‖f‖_{ℓ^p}` (the `n = 0` term of `C^Q` is part of `E_Q`, which is
  small in every `n` by the same estimate).
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Goal0

/-- **The maximal `K_Q`-replacement, the error bound**: for `1 < p < ∞` and every `A`,
`‖sup_λ|∑_n f(x-n) w_Q(n) E_Q(n) e(λ n)|‖_{ℓ^p} ≤ C_{p,A} Q^{-A} ‖f‖_{ℓ^p}` (conditional on
`hO`). -/
theorem errW_sup_bound (hO : OplusVariationBound) (S : KQSetup) {p : ℝ} (hp : 1 < p) (A : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Q : ℕ, 1 ≤ Q → ∀ f : ℤ →₀ ℂ,
      eLpNorm (supOp (fun n => wQ Q n * errW S Q n) (⇑f)) (ENNReal.ofReal p) Measure.count ≤
        ENNReal.ofReal (C * (Q : ℝ) ^ (-A)) * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := S.KQerr_eVariation_le (A + 1)
  obtain ⟨C₂, hC₂0, hC₂⟩ := integral_norm_KQerr_le S (A + 1)
  obtain ⟨C_T, hCT0, hCT⟩ := tile_sup_bound hO hp
  refine ⟨C_T * (C₁ + C₂), by positivity, fun Q hQ f => ?_⟩
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hp1 : 1 ≤ p := hp.le
  obtain ⟨hint, hL⟩ := hC₂ Q hQ
  set B : ℝ := C_T * (C₁ * (Q : ℝ) ^ (-(A + 1)) + C₂ * (Q : ℝ) ^ (-(A + 1))) with hB
  have hB0 : 0 ≤ B := by positivity
  -- the bound for `E_Q`
  have hE : eLpNorm (supOp (errW S Q) (⇑f)) (ENNReal.ofReal p) Measure.count ≤
      ENNReal.ofReal B * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
    have h := hCT (S.KQerr Q) (C₁ * (Q : ℝ) ^ (-(A + 1))) (C₂ * (Q : ℝ) ^ (-(A + 1)))
      (by positivity) (by positivity) hint (hC₁ Q hQ) hL f
    have hfun : (fun n : ℤ => ∫ ξ : ℝ, S.KQerr Q ξ * e ((n : ℝ) * ξ)) = errW S Q := by
      funext n; rw [errW_eq_integral]
    rw [hfun] at h
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
  -- the maximal operator
  have hpt : ∀ x : ℤ, supOp (fun n => wQ Q n * errW S Q n) (⇑f) x ≤
      ENNReal.ofReal (Q : ℝ) * supOp (errW S Q) (⇑f) x := by
    intro x
    rw [hweight]
    refine (supOp_sum_weight_le J
      (fun i n => cq i * (errW S Q n * e (sh i * (n : ℝ)))) f x).trans ?_
    calc ∑ i ∈ J, supOp (fun n => cq i * (errW S Q n * e (sh i * (n : ℝ)))) (⇑f) x
        ≤ ∑ i ∈ J, ‖cq i‖ₑ * supOp (errW S Q) (⇑f) x :=
          Finset.sum_le_sum fun i _ => by
            refine (supOp_const_mul_le (cq i) _ _ x).trans ?_
            rw [supOp_mul_e]
      _ = (∑ i ∈ J, ‖cq i‖ₑ) * supOp (errW S Q) (⇑f) x := (Finset.sum_mul _ _ _).symm
      _ ≤ ENNReal.ofReal (Q : ℝ) * supOp (errW S Q) (⇑f) x := mul_le_mul' hcoef le_rfl
  calc eLpNorm (supOp (fun n => wQ Q n * errW S Q n) (⇑f)) (ENNReal.ofReal p) Measure.count
      ≤ eLpNorm (fun x => ENNReal.ofReal (Q : ℝ) * supOp (errW S Q) (⇑f) x)
          (ENNReal.ofReal p) Measure.count := eLpNorm_count_mono_enn hpt _
    _ = ENNReal.ofReal (Q : ℝ) * eLpNorm (supOp (errW S Q) (⇑f)) (ENNReal.ofReal p)
          Measure.count := eLpNorm_count_const_mul _ _ (by linarith)
    _ ≤ ENNReal.ofReal (Q : ℝ) * (ENNReal.ofReal B * eLpNorm (⇑f) (ENNReal.ofReal p)
          Measure.count) := mul_le_mul' le_rfl hE
    _ = ENNReal.ofReal ((Q : ℝ) * B) * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hQ0.le]
    _ = ENNReal.ofReal (C_T * (C₁ + C₂) * (Q : ℝ) ^ (-A)) *
          eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
        congr 2
        have : (Q : ℝ) * (Q : ℝ) ^ (-(A + 1)) = (Q : ℝ) ^ (-A) := by
          have e : (Q : ℝ) ^ (-A) = (Q : ℝ) ^ (1 + -(A + 1)) := by congr 1; ring
          rw [e, Real.rpow_add hQ0, Real.rpow_one]
        rw [hB]
        calc (Q : ℝ) * (C_T * (C₁ * (Q : ℝ) ^ (-(A + 1)) + C₂ * (Q : ℝ) ^ (-(A + 1))))
            = C_T * (C₁ + C₂) * ((Q : ℝ) * (Q : ℝ) ^ (-(A + 1))) := by ring
          _ = _ := by rw [this]

/-- The pointwise triangle inequality of the maximal replacement:
`sup_λ|w_Q ∑_{k ≥ k₀} ψ_k| ≤ C^Q f + sup_λ|w_Q E_Q|`. -/
theorem supOp_psiTail_le (S : KQSetup) (Q : ℕ) (f : ℤ →₀ ℂ) (x : ℤ) :
    supOp (fun n => wQ Q n * psiTailZ S.ψ (S.P.kmin Q) n) (⇑f) x ≤
      S.CQ Q (⇑f) x + supOp (fun n => wQ Q n * errW S Q n) (⇑f) x := by
  rw [CQ_eq_supOp]
  have : (fun n => wQ Q n * psiTailZ S.ψ (S.P.kmin Q) n) =
      (fun n => wQ Q n * S.KQz Q n) + (fun n => wQ Q n * errW S Q n) := by
    funext n
    simp only [Pi.add_apply, errW]
    ring
  rw [this]
  exact supOp_add_weight_le _ _ f x

/-- **The maximal `K_Q`-replacement**: for `1 < p < ∞` (conditional on `hO`) there is `C` such
that for every `Q ≥ 1` and finitely supported `f`,
`‖sup_λ|∑_n f(x-n) w_Q(n) ∑_{k ≥ Q^{1/D₀}} ψ_k(n) e(λ n)|‖_{ℓ^p} ≤ ‖C^Q f‖_{ℓ^p} +
C Q^{-100} ‖f‖_{ℓ^p}`. -/
theorem KQ_replacement_sup (hO : OplusVariationBound) (S : KQSetup) {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Q : ℕ, 1 ≤ Q → ∀ f : ℤ →₀ ℂ,
      eLpNorm (supOp (fun n => wQ Q n * psiTailZ S.ψ (S.P.kmin Q) n) (⇑f))
          (ENNReal.ofReal p) Measure.count ≤
        eLpNorm (S.CQ Q (⇑f)) (ENNReal.ofReal p) Measure.count +
          ENNReal.ofReal (C * (Q : ℝ) ^ (-(100 : ℝ))) *
            eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
  obtain ⟨C, hC0, hC⟩ := errW_sup_bound hO S hp 100
  refine ⟨C, hC0, fun Q hQ f => ?_⟩
  have hmono : eLpNorm (supOp (fun n => wQ Q n * psiTailZ S.ψ (S.P.kmin Q) n) (⇑f))
      (ENNReal.ofReal p) Measure.count ≤
      eLpNorm (fun x => S.CQ Q (⇑f) x + supOp (fun n => wQ Q n * errW S Q n) (⇑f) x)
        (ENNReal.ofReal p) Measure.count :=
    eLpNorm_count_mono_enn (fun x => supOp_psiTail_le S Q f x) _
  exact hmono.trans ((eLpNorm_count_add_le _ _ hp.le).trans (add_le_add le_rfl (hC Q hQ f)))

end PrimeCarleson.Proof.Paper
