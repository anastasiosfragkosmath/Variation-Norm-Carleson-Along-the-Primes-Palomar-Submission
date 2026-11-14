module

public import PrimeCarleson.Proof.Paper.P6c.Pieces
public import PrimeCarleson.Proof.Paper.P6c.Interp
public import PrimeCarleson.Proof.Paper.P6a.Residual

/-!
# The residual term of the maximal operator

Source: main paper `s:red`, L1525–L1527 (the paper: "the residual and high-denominator terms are
controlled by the maximal `U³`-estimate of Lemma `e:U3maxmod` and the same `U³`-decay inputs").
The maximal counterpart of
`minor_var_L2_red`, `minor_var_crude_red` and `residual_sum` of `P6a/Residual.lean`:

* `residual_L2_sup`: `‖sup_λ|∑_n f(x-n) (w - w_{≤ M(k)})(n) ψ_k(n) e(λ n)|‖_{ℓ²}
  ≲_A k^{-A}‖f‖_{ℓ²}` from `e:U3maxmod` (`sup_L2_piece`) and `e:minor-U3-var-red`
  (`minor_U3_var_red`, `FplusProp31`);
* `residual_crude_sup`: the `ℓ^s` bound `≲ k` for every `s ≥ 1` (Young, the moment
  `‖w - w_{≤ M(k)}‖_{L²([2^k])} ≲ k`);
* `residual_sum_sup`: for every `1 < p < ∞`,
  `∑_k ‖sup_λ|…(w - w_{≤ M(k)}) ψ_k …|‖_{ℓ^p} ≲_p ‖f‖_{ℓ^p}`, by Marcinkiewicz interpolation
  (`supOp_interp`) and `∑_k k^{-2} < ∞`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson

/-- **The residual `ℓ²` bound**: for every `A`,
`‖sup_λ|∑_n f(x-n) (w - w_{≤ M(k)})(n) ψ_k(n) e(λ n)|‖_{ℓ²} ≲_A k^{-A} ‖f‖_{ℓ²}`
(conditional on `[F+, Proposition 3.1]`, through `e:minor-U3-var-red`). -/
theorem residual_L2_sup (ψ : PsiData) (hF : FplusProp31) (A : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 1 ≤ k → ∀ f : ℤ →₀ ℂ,
      eLpNorm (supOp (fun n => resWeight k n * psiKz ψ k n) (⇑f)) (ENNReal.ofReal 2)
          Measure.count ≤
        ENNReal.ofReal (C * (k : ℝ) ^ (-A)) * eLpNorm (⇑f) (ENNReal.ofReal 2) Measure.count := by
  obtain ⟨C_L, hCL0, hL⟩ := sup_L2_piece ψ
  obtain ⟨C_U, hCU0, hU⟩ := minor_U3_var_red hF A
  refine ⟨C_L * C_U, by positivity, fun k hk f => ?_⟩
  set N : ℕ+ := ⟨2 ^ k, by positivity⟩ with hNdef
  have hN : (N : ℕ) = 2 ^ k := rfl
  refine (hL k N hN (resWeight k) (resWeight_neg k) ⇑f).trans ?_
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  calc C_L * gowersNormInterval 3 N (resWeight k)
      ≤ C_L * (C_U * (k : ℝ) ^ (-A)) := mul_le_mul_of_nonneg_left (hU k N hk hN) hCL0
    _ = C_L * C_U * (k : ℝ) ^ (-A) := by ring

/-- **The residual crude bound**: for every `s ≥ 1`,
`‖sup_λ|∑_n f(x-n) (w - w_{≤ M(k)})(n) ψ_k(n) e(λ n)|‖_{ℓ^s} ≲ k ‖f‖_{ℓ^s}`. -/
theorem residual_crude_sup (ψ : PsiData) {s : ℝ} (hs : 1 ≤ s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 1 ≤ k → ∀ f : ℤ →₀ ℂ,
      eLpNorm (supOp (fun n => resWeight k n * psiKz ψ k n) (⇑f)) (ENNReal.ofReal s)
          Measure.count ≤
        ENNReal.ofReal (C * (k : ℝ)) * eLpNorm (⇑f) (ENNReal.ofReal s) Measure.count := by
  obtain ⟨C_c, hCc0, hc⟩ := crude_sup_piece ψ
  obtain ⟨C_M, hCM0, hM⟩ := residual_L2_moment_oneSided
  refine ⟨C_c * C_M, by positivity, fun k hk f => ?_⟩
  set N : ℕ+ := ⟨2 ^ k, by positivity⟩ with hNdef
  have hN : (N : ℕ) = 2 ^ k := rfl
  refine (hc k N hN (resWeight k) (resWeight_neg k) s hs ⇑f).trans ?_
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  calc C_c * lpNormOn 2 (bracket N) (resWeight k) ≤ C_c * (C_M * k) :=
        mul_le_mul_of_nonneg_left (hM k N hk hN) hCc0
    _ = C_c * C_M * k := by ring

/-- **The residual sum**: for every `1 < p < ∞` there is `C`
with `∑_{k ≥ 1} ‖sup_λ|∑_n f(x-n) (w - w_{≤ M(k)})(n) ψ_k(n) e(λ n)|‖_{ℓ^p} ≤ C ‖f‖_{ℓ^p}`
(interpolating `residual_L2_sup` with `A = A(p)` large and `residual_crude_sup`;
`∑_k k^{-2} < ∞`). -/
theorem residual_sum_sup (ψ : PsiData) {p : ℝ} (hp : 1 < p) (hF : FplusProp31) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℤ →₀ ℂ,
      ∑' k : ℕ, eLpNorm (supOp (fun n => resWeight (k + 1) n * psiKz ψ (k + 1) n) (⇑f))
          (ENNReal.ofReal p) Measure.count ≤
        ENNReal.ofReal C * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
  obtain ⟨s, ϑ, Cint, hs, hϑ0, hϑ1, hCint0, hint⟩ := supOp_interp hp
  set A : ℝ := 3 / ϑ with hAdef
  have hAϑ : -A * ϑ = -3 := by rw [hAdef]; field_simp
  obtain ⟨C₀, hC₀, h₀⟩ := residual_L2_sup ψ hF A
  obtain ⟨C₁, hC₁, h₁⟩ := residual_crude_sup ψ hs.le
  set C₀' : ℝ := max C₀ 1 with hC₀'
  set C₁' : ℝ := max C₁ 1 with hC₁'
  have hC₀'0 : 0 < C₀' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hC₁'0 : 0 < C₁' := lt_of_lt_of_le one_pos (le_max_right _ _)
  set K : ℝ := Cint * C₀' ^ ϑ * C₁' ^ (1 - ϑ) with hK
  have hpt : ∀ (k : ℕ) (f : ℤ →₀ ℂ),
      eLpNorm (supOp (fun n => resWeight (k + 1) n * psiKz ψ (k + 1) n) (⇑f))
          (ENNReal.ofReal p) Measure.count ≤
        ENNReal.ofReal (K * (((k + 1 : ℕ) : ℝ)) ^ (-2 : ℝ)) *
          eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
    intro k f
    have hk1 : 1 ≤ k + 1 := by omega
    have hk0 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    have hk1r : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast hk1
    set κ : ℝ := ((k + 1 : ℕ) : ℝ) with hκ
    have hX₀ : 0 < C₀' * κ ^ (-A) := by positivity
    have hX₁ : 0 < C₁' * κ := by positivity
    have h := hint (fun n => resWeight (k + 1) n * psiKz ψ (k + 1) n) (C₀' * κ ^ (-A))
      (C₁' * κ) hX₀ hX₁
      (fun g => (h₀ (k + 1) hk1 g).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))) le_rfl))
      (fun g => (h₁ (k + 1) hk1 g).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))) le_rfl)) f
    refine h.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
    rw [rpow_mul_rpow_aux hC₀'0.le hk0.le, Real.mul_rpow hC₁'0.le hk0.le]
    have hκe : κ ^ (-A * ϑ) * κ ^ (1 - ϑ) = κ ^ (-2 - ϑ) := by
      rw [← Real.rpow_add hk0, hAϑ]; congr 1; ring
    have hle : κ ^ (-2 - ϑ) ≤ κ ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hk1r (by linarith)
    calc Cint * (C₀' ^ ϑ * κ ^ (-A * ϑ)) * (C₁' ^ (1 - ϑ) * κ ^ (1 - ϑ))
        = K * (κ ^ (-A * ϑ) * κ ^ (1 - ϑ)) := by rw [hK]; ring
      _ = K * κ ^ (-2 - ϑ) := by rw [hκe]
      _ ≤ K * κ ^ (-2 : ℝ) := mul_le_mul_of_nonneg_left hle (by positivity)
  have hsum : Summable (fun k : ℕ => (((k + 1 : ℕ) : ℝ)) ^ (-2 : ℝ)) :=
    summable_shift_rpow_neg_two
  refine ⟨K * ∑' k : ℕ, (((k + 1 : ℕ) : ℝ)) ^ (-2 : ℝ), by positivity, fun f => ?_⟩
  calc ∑' k : ℕ, eLpNorm (supOp (fun n => resWeight (k + 1) n * psiKz ψ (k + 1) n) (⇑f))
          (ENNReal.ofReal p) Measure.count
      ≤ ∑' k : ℕ, ENNReal.ofReal (K * (((k + 1 : ℕ) : ℝ)) ^ (-2 : ℝ)) *
          eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count :=
        ENNReal.tsum_le_tsum fun k => hpt k f
    _ = ENNReal.ofReal (K * ∑' k : ℕ, (((k + 1 : ℕ) : ℝ)) ^ (-2 : ℝ)) *
          eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count :=
        tsum_ofReal_shift_sq_mul K (by positivity) _

end PrimeCarleson.Proof.Paper
