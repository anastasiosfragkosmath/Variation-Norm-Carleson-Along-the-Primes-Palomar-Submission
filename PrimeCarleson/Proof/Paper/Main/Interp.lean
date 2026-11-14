module

public import PrimeCarleson.Proof.Paper.P6a.HighQ

/-!
# The parametrised high-denominator sum of `p:red-var`

Source: main paper `p:red-var`, L1456–L1458, as input of the choice of the range of `p` in `t:main`
(the paper does not construct this range).

The sum is bounded by interpolating between the `ℓ²` bound `highQ_var_L2_red` and the crude `ℓ^s`
bound `highQ_crude` of `P6a/HighQ.lean`. This file takes the interpolation data `(s, ϑ)` as
parameters, so that `D₁(p, r)` is explicit in `r` and `p`: the threshold is
`D₁ = 32 / (ϑ (1 - 2/r))` (the proof gives `2/c · (2ϑ/r + 2)` with `c = (3/16) ϑ (1 - 2/r)`,
bounded by `32 / (ϑ (1 - 2/r))`).

* `VarOpInterp r p s ϑ`: the Marcinkiewicz interpolation property of `varOp` between `ℓ²` and
  `ℓ^s` at `ℓ^p`, with weight `ϑ` (the conclusion of `varOp_interp` of `P6a/Interp.lean`);
* `varOp_interp_param`: `VarOpInterp r p s ϑ` for `1/p = ϑ/2 + (1-ϑ)/s`, `s ≠ 2`;
* `varOp_interp_two`: `VarOpInterp r 2 2 1`;
* `highQ_sum_param`: the high-denominator sum of `p:red-var` for every `D₀ ≥ 32 / (ϑ (1 - 2/r))`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson

/-- The interpolation property of `varOp` between `ℓ²` and `ℓ^s` at `ℓ^p` with weight `ϑ`: a
weight `u` whose operator `f ↦ V^r(∑_n f(x-n) u(n) e(λ n) : λ)` is bounded on `ℓ²` with norm
`≤ M₀` and on `ℓ^s` with norm `≤ M₁` is bounded on `ℓ^p` with norm `≤ C M₀^ϑ M₁^{1-ϑ}`
(`varOp_interp` of `P6a/Interp.lean` with the exponents as parameters). -/
def VarOpInterp (r p s ϑ : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : ℤ → ℂ) (M₀ M₁ : ℝ), 0 < M₀ → 0 < M₁ →
    (∀ f : ℤ →₀ ℂ, eLpNorm (varOp r u (⇑f)) (ENNReal.ofReal 2) Measure.count ≤
      ENNReal.ofReal M₀ * eLpNorm (⇑f) (ENNReal.ofReal 2) Measure.count) →
    (∀ f : ℤ →₀ ℂ, eLpNorm (varOp r u (⇑f)) (ENNReal.ofReal s) Measure.count ≤
      ENNReal.ofReal M₁ * eLpNorm (⇑f) (ENNReal.ofReal s) Measure.count) →
    ∀ f : ℤ →₀ ℂ, eLpNorm (varOp r u (⇑f)) (ENNReal.ofReal p) Measure.count ≤
      ENNReal.ofReal (C * M₀ ^ ϑ * M₁ ^ (1 - ϑ)) *
        eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count

/-- **Interpolation of `varOp` with the exponents as parameters** (interpolation by the
Marcinkiewicz theorem; `varOp_interp` of `P6a/Interp.lean`): for `r > 2`, `s > 0`, `s ≠ 2`,
`θ ∈ (0, 1)` and `1/p = θ/2 + (1-θ)/s`, `VarOpInterp r p s θ`. -/
theorem varOp_interp_param {r p s θ : ℝ} (hr : 2 < r) (hs0 : 0 < s) (hs2 : s ≠ 2)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hpθ : 1 / p = θ / 2 + (1 - θ) / s) :
    VarOpInterp r p s θ := by
  obtain ⟨Cint, hCint⟩ :=
    PrimeCarleson.Proof.Common.exists_eLpNorm_count_le_interpolation_finsupp_ofReal
    (α := ℤ) (β := ℤ) (E := ℂ) (ε := ℝ≥0∞) (p₀ := 2) (p₁ := s) (p := p) (θ := 1 - θ)
    (by norm_num) hs0 (Ne.symm hs2) (by linarith) (by linarith) (by rw [hpθ]; ring_nf)
  refine ⟨Cint, Cint.2, fun u M₀ M₁ hM₀ hM₁ h₀ h₁ f => ?_⟩
  have key := hCint (fun g => varOp r u (⇑g)) M₀.toNNReal M₁.toNNReal
    (by simpa using hM₀) (by simpa using hM₁)
    (fun g g' x => by simpa using varOp_add_left_le (by linarith) u g g' x)
    (fun g => by simpa [ENNReal.ofReal] using h₀ g)
    (fun g => by simpa [ENNReal.ofReal] using h₁ g) f
  refine key.trans (le_of_eq ?_)
  rw [show 1 - (1 - θ) = θ by ring]
  congr 1
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_rpow_of_nonneg hM₀.le hθ0.le,
    ← ENNReal.ofReal_rpow_of_nonneg hM₁.le (by linarith), ENNReal.ofReal_coe_nnreal]
  rfl

/-- The case `p = 2`: `VarOpInterp r 2 2 1` (the `ℓ²` bound is the hypothesis). -/
theorem varOp_interp_two (r : ℝ) : VarOpInterp r 2 2 1 := by
  refine ⟨1, zero_le_one, fun u M₀ M₁ hM₀ hM₁ h₀ _ f => ?_⟩
  simpa [Real.rpow_one, Real.rpow_zero] using h₀ f

/-- The explicit threshold: `2/c · (2ϑ/r + 2) ≤ 32 / (ϑ (1 - 2/r))` for
`c = ϑ · (3/8)(1 - 2/r) / 2`, `0 < ϑ ≤ 1`, `r > 2`. -/
theorem highQ_D₁_le {r ϑ : ℝ} (hr : 2 < r) (hϑ0 : 0 < ϑ) (hϑ1 : ϑ ≤ 1) :
    2 / (ϑ * (3 / 8 * (1 - 2 / r)) / 2) * (2 * ϑ / r + 2) ≤ 32 / (ϑ * (1 - 2 / r)) := by
  have hr0 : 0 < r := by linarith
  have ha : 0 < 1 - 2 / r := by
    rw [sub_pos, div_lt_one hr0]; exact hr
  have h3 : 2 * ϑ / r + 2 ≤ 3 := by
    have : 2 * ϑ / r ≤ 1 := by
      rw [div_le_one hr0]; linarith
    linarith
  have hc : 0 < ϑ * (3 / 8 * (1 - 2 / r)) / 2 := by positivity
  calc 2 / (ϑ * (3 / 8 * (1 - 2 / r)) / 2) * (2 * ϑ / r + 2)
      ≤ 2 / (ϑ * (3 / 8 * (1 - 2 / r)) / 2) * 3 :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = 32 / (ϑ * (1 - 2 / r)) := by field_simp; norm_num

/-- **The high-denominator sum of `p:red-var`** (L1456–L1458) with the interpolation data as
parameters: for
`r > 2`, `s ≥ r'`, `ϑ ∈ (0, 1]` with `VarOpInterp r p s ϑ` and every `D₀ ≥ 32 / (ϑ (1 - 2/r))` the
sum over `k ≥ 1` and the dyadic `Q = 2^j` with `k^{D₀} < Q ≤ M(k)` of
`‖V^r(∑_n f(x-n) w_Q(n) ψ_k(n) e(λ n) : λ)‖_{ℓ^p}` is `≲ ‖f‖_{ℓ^p}`. -/
theorem highQ_sum_param {r p s ϑ : ℝ} (hr : 2 < r) (hs : r / (r - 1) ≤ s) (hϑ0 : 0 < ϑ)
    (hϑ1 : ϑ ≤ 1) (hint : VarOpInterp r p s ϑ) :
    ∀ ψ : PsiData, LocalU3VarRed ψ r → ∀ D₀ : ℝ, 32 / (ϑ * (1 - 2 / r)) ≤ D₀ → ∃ C : ℝ, 0 ≤ C ∧
      ∀ f : ℤ →₀ ℂ,
      ∑' k : ℕ, ∑ j ∈ highJ D₀ (k + 1),
          eLpNorm (varOp r (pairW ψ (k + 1) j) (⇑f)) (ENNReal.ofReal p) Measure.count ≤
        ENNReal.ofReal C * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
  obtain ⟨Cint, hCint0, hint⟩ := hint
  have ha : 0 < 1 - 2 / r := by
    rw [sub_pos, div_lt_one (by linarith)]; exact hr
  set a₃ : ℝ := 3 / 8 * (1 - 2 / r) with ha₃
  have ha₃0 : 0 < a₃ := by positivity
  set η : ℝ := ϑ * a₃ / 2 with hη
  have hη0 : 0 < η := by positivity
  set c : ℝ := ϑ * a₃ / 2 with hc
  have hc0 : 0 < c := by positivity
  intro ψ hLoc D₀ hD₀'
  have hD₀ : 2 / c * (2 * ϑ / r + 2) ≤ D₀ := (highQ_D₁_le hr hϑ0 hϑ1).trans hD₀'
  obtain ⟨C₀, hC₀, h₀⟩ := highQ_var_L2_red ψ hr hLoc hη0
  obtain ⟨C₁, hC₁, h₁⟩ := highQ_crude ψ hr hs
  obtain ⟨Cη, hCη0, hCη⟩ := KMTT.exists_pow_log_le_rpow hη0
  set C₀' : ℝ := max C₀ 1 with hC₀'
  set C₁' : ℝ := max (C₁ * Cη) 1 with hC₁'
  have hC₀'0 : 0 < C₀' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hC₁'0 : 0 < C₁' := lt_of_lt_of_le one_pos (le_max_right _ _)
  set q : ℝ := (2 : ℝ) ^ (-(c / 2)) with hq
  have hq0 : 0 < q := by positivity
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  set K : ℝ := Cint * C₀' ^ ϑ * C₁' ^ (1 - ϑ) with hK
  have hK0 : 0 ≤ K := by positivity
  -- the bound for a single pair
  have hpair : ∀ (k j : ℕ), 1 ≤ k → (2 : ℝ) ^ j ≤ cutoffM k → ∀ f : ℤ →₀ ℂ,
      eLpNorm (varOp r (pairW ψ k j) (⇑f)) (ENNReal.ofReal p) Measure.count ≤
        ENNReal.ofReal (K * (k : ℝ) ^ (2 * ϑ / r) * ((2 : ℝ) ^ j) ^ (-c)) *
          eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
    intro k j hk hj f
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have hQ : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
    have hQ1 : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
    have hX₀ : 0 < C₀' * ((k : ℝ) ^ (2 / r) * ((2 : ℝ) ^ j) ^ (-(3 / 8) * (1 - 2 / r) + η)) := by
      positivity
    have hX₁ : 0 < C₁' * ((2 : ℝ) ^ j) ^ η := by positivity
    have h := hint (pairW ψ k j) _ _ hX₀ hX₁
      (fun g => (h₀ k j hk hj g).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (by
        have := mul_le_mul_of_nonneg_right (le_max_left C₀ 1)
          (by positivity : 0 ≤ (k : ℝ) ^ (2 / r) *
            ((2 : ℝ) ^ j) ^ (-(3 / 8) * (1 - 2 / r) + η))
        calc C₀ * (k : ℝ) ^ (2 / r) * ((2 : ℝ) ^ j) ^ (-(3 / 8) * (1 - 2 / r) + η)
            = C₀ * ((k : ℝ) ^ (2 / r) * ((2 : ℝ) ^ j) ^ (-(3 / 8) * (1 - 2 / r) + η)) := by ring
          _ ≤ _ := this)) le_rfl))
      (fun g => (h₁ k j hk g).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (by
        have h2 := hCη ((2 : ℝ) ^ j) hQ1
        calc C₁ * (1 + Real.log ((2 : ℝ) ^ j)) ^ 3 ≤ C₁ * (Cη * ((2 : ℝ) ^ j) ^ η) :=
              mul_le_mul_of_nonneg_left h2 hC₁
          _ = (C₁ * Cη) * ((2 : ℝ) ^ j) ^ η := by ring
          _ ≤ C₁' * ((2 : ℝ) ^ j) ^ η :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))) le_rfl)) f
    refine h.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (le_of_eq ?_)) le_rfl)
    rw [Real.mul_rpow hC₀'0.le (by positivity), Real.mul_rpow hC₁'0.le (by positivity),
      Real.mul_rpow (Real.rpow_nonneg hk0.le _) (Real.rpow_nonneg hQ.le _),
      ← Real.rpow_mul hk0.le, ← Real.rpow_mul hQ.le, ← Real.rpow_mul hQ.le]
    have e1 : ((2 : ℝ) ^ j) ^ ((-(3 / 8) * (1 - 2 / r) + η) * ϑ) *
        ((2 : ℝ) ^ j) ^ (η * (1 - ϑ)) = ((2 : ℝ) ^ j) ^ (-c) := by
      rw [← Real.rpow_add hQ]; congr 1
      simp only [hη, hc, ha₃]; ring
    have e2 : (k : ℝ) ^ (2 / r * ϑ) = (k : ℝ) ^ (2 * ϑ / r) := by congr 1; ring
    rw [e2]
    calc Cint * (C₀' ^ ϑ * ((k : ℝ) ^ (2 * ϑ / r) *
          ((2 : ℝ) ^ j) ^ ((-(3 / 8) * (1 - 2 / r) + η) * ϑ))) *
        (C₁' ^ (1 - ϑ) * ((2 : ℝ) ^ j) ^ (η * (1 - ϑ)))
        = K * (k : ℝ) ^ (2 * ϑ / r) * (((2 : ℝ) ^ j) ^ ((-(3 / 8) * (1 - 2 / r) + η) * ϑ) *
            ((2 : ℝ) ^ j) ^ (η * (1 - ϑ))) := by rw [hK]; ring
      _ = _ := by rw [e1]
  -- the sum over `j` for fixed `k`
  have hjsum : ∀ (k : ℕ), 1 ≤ k → ∀ f : ℤ →₀ ℂ,
      ∑ j ∈ highJ D₀ k, eLpNorm (varOp r (pairW ψ k j) (⇑f)) (ENNReal.ofReal p) Measure.count ≤
        ENNReal.ofReal (K * (1 - q)⁻¹ * (k : ℝ) ^ (2 * ϑ / r - D₀ * (c / 2))) *
          eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
    intro k hk f
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have hmem : ∀ j ∈ highJ D₀ k, (2 : ℝ) ^ j ≤ cutoffM k ∧ (k : ℝ) ^ D₀ < (2 : ℝ) ^ j := by
      intro j hj
      unfold highJ at hj
      rw [Finset.mem_filter, mem_jSet_iff] at hj
      exact ⟨hj.1, not_le.1 hj.2⟩
    have hb : ∀ j ∈ highJ D₀ k,
        K * (k : ℝ) ^ (2 * ϑ / r) * ((2 : ℝ) ^ j) ^ (-c) ≤
          K * (k : ℝ) ^ (2 * ϑ / r) * ((k : ℝ) ^ D₀) ^ (-(c / 2)) * q ^ j := by
      intro j hj
      obtain ⟨-, hj2⟩ := hmem j hj
      have hQ : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
      have hkD : (0 : ℝ) < (k : ℝ) ^ D₀ := Real.rpow_pos_of_pos hk0 _
      have e1 : ((2 : ℝ) ^ j) ^ (-c) =
          ((2 : ℝ) ^ j) ^ (-(c / 2)) * ((2 : ℝ) ^ j) ^ (-(c / 2)) := by
        rw [← Real.rpow_add hQ]; congr 1; ring
      have e2 : ((2 : ℝ) ^ j) ^ (-(c / 2)) = q ^ j := by
        rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast,
          ← Real.rpow_mul (by norm_num)]
        congr 1; ring
      have e3 : ((2 : ℝ) ^ j) ^ (-(c / 2)) ≤ ((k : ℝ) ^ D₀) ^ (-(c / 2)) :=
        Real.rpow_le_rpow_of_nonpos hkD hj2.le (by linarith)
      rw [e1]
      calc K * (k : ℝ) ^ (2 * ϑ / r) * (((2 : ℝ) ^ j) ^ (-(c / 2)) * ((2 : ℝ) ^ j) ^ (-(c / 2)))
          ≤ K * (k : ℝ) ^ (2 * ϑ / r) * (((k : ℝ) ^ D₀) ^ (-(c / 2)) * q ^ j) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            rw [e2] at e3 ⊢
            exact mul_le_mul e3 le_rfl (by positivity) (by positivity)
        _ = _ := by ring
    have hgeo : ∑ j ∈ highJ D₀ k, q ^ j ≤ (1 - q)⁻¹ := by
      refine ((summable_geometric_of_lt_one hq0.le hq1).sum_le_tsum _
        (fun j _ => by positivity)).trans ?_
      rw [tsum_geometric_of_lt_one hq0.le hq1]
    have hreal : ∑ j ∈ highJ D₀ k, K * (k : ℝ) ^ (2 * ϑ / r) * ((2 : ℝ) ^ j) ^ (-c) ≤
        K * (1 - q)⁻¹ * (k : ℝ) ^ (2 * ϑ / r - D₀ * (c / 2)) := by
      calc _ ≤ ∑ j ∈ highJ D₀ k,
            K * (k : ℝ) ^ (2 * ϑ / r) * ((k : ℝ) ^ D₀) ^ (-(c / 2)) * q ^ j :=
            Finset.sum_le_sum hb
        _ = K * (k : ℝ) ^ (2 * ϑ / r) * ((k : ℝ) ^ D₀) ^ (-(c / 2)) *
            ∑ j ∈ highJ D₀ k, q ^ j := by rw [← Finset.mul_sum]
        _ ≤ K * (k : ℝ) ^ (2 * ϑ / r) * ((k : ℝ) ^ D₀) ^ (-(c / 2)) * (1 - q)⁻¹ :=
            mul_le_mul_of_nonneg_left hgeo (by positivity)
        _ = K * (1 - q)⁻¹ * (k : ℝ) ^ (2 * ϑ / r - D₀ * (c / 2)) := by
            have e : (k : ℝ) ^ (2 * ϑ / r - D₀ * (c / 2)) =
                (k : ℝ) ^ (2 * ϑ / r) * (k : ℝ) ^ (D₀ * -(c / 2)) := by
              rw [← Real.rpow_add hk0]; congr 1; ring
            rw [← Real.rpow_mul hk0.le, e]; ring
    calc ∑ j ∈ highJ D₀ k, eLpNorm (varOp r (pairW ψ k j) (⇑f)) (ENNReal.ofReal p) Measure.count
        ≤ ∑ j ∈ highJ D₀ k, ENNReal.ofReal (K * (k : ℝ) ^ (2 * ϑ / r) * ((2 : ℝ) ^ j) ^ (-c)) *
            eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count :=
          Finset.sum_le_sum fun j hj => hpair k j hk (hmem j hj).1 f
      _ = (∑ j ∈ highJ D₀ k, ENNReal.ofReal (K * (k : ℝ) ^ (2 * ϑ / r) *
            ((2 : ℝ) ^ j) ^ (-c))) * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
          rw [Finset.sum_mul]
      _ = ENNReal.ofReal (∑ j ∈ highJ D₀ k, K * (k : ℝ) ^ (2 * ϑ / r) *
            ((2 : ℝ) ^ j) ^ (-c)) * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => by positivity)]
      _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal hreal) le_rfl
  -- summation over `k`
  have hexp : ∀ k : ℕ, 1 ≤ k →
      (k : ℝ) ^ (2 * ϑ / r - D₀ * (c / 2)) ≤ (k : ℝ) ^ (-2 : ℝ) := by
    intro k hk
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    refine Real.rpow_le_rpow_of_exponent_le hk1 ?_
    have h2 : 2 * ϑ / r + 2 ≤ D₀ * (c / 2) := by
      have h3 : 2 * ϑ / r + 2 = (2 / c * (2 * ϑ / r + 2)) * (c / 2) := by
        field_simp
      rw [h3]
      exact mul_le_mul_of_nonneg_right hD₀ (by positivity)
    linarith
  refine ⟨K * (1 - q)⁻¹ * ∑' k : ℕ, (((k + 1 : ℕ) : ℝ)) ^ (-2 : ℝ), by
    have : 0 ≤ (1 - q)⁻¹ := inv_nonneg.2 (by linarith)
    positivity, fun f => ?_⟩
  calc ∑' k : ℕ, ∑ j ∈ highJ D₀ (k + 1),
        eLpNorm (varOp r (pairW ψ (k + 1) j) (⇑f)) (ENNReal.ofReal p) Measure.count
      ≤ ∑' k : ℕ, ENNReal.ofReal (K * (1 - q)⁻¹ * (((k + 1 : ℕ) : ℝ)) ^ (-2 : ℝ)) *
          eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
        refine ENNReal.tsum_le_tsum fun k => (hjsum (k + 1) (by omega) f).trans ?_
        refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
        have : 0 ≤ K * (1 - q)⁻¹ := mul_nonneg hK0 (inv_nonneg.2 (by linarith))
        exact mul_le_mul_of_nonneg_left (hexp (k + 1) (by omega)) this
    _ = _ := tsum_ofReal_shift_sq_mul _ (mul_nonneg hK0 (inv_nonneg.2 (by linarith))) _

end PrimeCarleson.Proof.Paper
