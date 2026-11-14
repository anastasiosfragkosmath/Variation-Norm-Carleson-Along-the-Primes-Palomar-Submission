module

public import PrimeCarleson.Proof.Paper.P6a.Moments
public import PrimeCarleson.Proof.Paper.P6a.Cutoff
public import PrimeCarleson.Proof.Paper.P6a.Interp

/-!
# The residual term of the proof of `p:red-var`

Source: main paper `p:red-var`, L1283–L1387: `e:minor-var-L2-red` (the `ℓ²` bound from
`e:local-U3-var-red`, `e:minor-U3-var-red` and the `ℓ²` moment of the residual, L1305–L1310),
`e:minor-var-crude-red` (the crude `ℓ^s` bound), and the sum over `k` of the interpolated bounds
(L1374–L1387). `e:local-U3-var-red` enters through `LocalU3VarRed` and `[F+, Proposition 3.1]`
through `FplusProp31`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson

/-- `(c x^a)^ϑ = c^ϑ x^{aϑ}` for `c, x ≥ 0`. -/
theorem rpow_mul_rpow_aux {c x a ϑ : ℝ} (hc : 0 ≤ c) (hx : 0 ≤ x) :
    (c * x ^ a) ^ ϑ = c ^ ϑ * x ^ (a * ϑ) := by
  rw [Real.mul_rpow hc (Real.rpow_nonneg hx _), ← Real.rpow_mul hx]

/-- **`e:minor-var-L2-red`** (L1311-L1321): for every `A`,
`‖V^r(∑_n f(x-n) (w - w_{≤ M(k)})(n) ψ_k(n) e(λ n) : λ)‖_{ℓ²}
≲_{A,r} k^{-A(1-2/r) + O_r(1)} ‖f‖_{ℓ²}`
(the `O_r(1)` is `4/r`). -/
theorem minor_var_L2_red (ψ : PsiData) {r : ℝ} (hr : 2 < r) (hLoc : LocalU3VarRed ψ r)
    (hF : FplusProp31) (A : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 1 ≤ k → ∀ f : ℤ →₀ ℂ,
      eLpNorm (varOp r (fun n => resWeight k n * psiKz ψ k n) (⇑f)) (ENNReal.ofReal 2)
          Measure.count ≤
        ENNReal.ofReal (C * (k : ℝ) ^ (4 / r - A * (1 - 2 / r))) *
          eLpNorm (⇑f) (ENNReal.ofReal 2) Measure.count := by
  obtain ⟨C_L, hCL0, hL⟩ := hLoc
  obtain ⟨C_U, hCU0, hU⟩ := minor_U3_var_red hF A
  obtain ⟨C_M, hCM0, hM⟩ := residual_L2_moment_oneSided
  have ha : 0 < 1 - 2 / r := by
    rw [sub_pos, div_lt_one (by linarith)]; exact hr
  have hb : 0 < 2 / r := by positivity
  refine ⟨C_L * C_U ^ (1 - 2 / r) * C_M ^ (2 / r), by positivity, fun k hk f => ?_⟩
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  set N : ℕ+ := ⟨2 ^ k, by positivity⟩ with hNdef
  have hN : (N : ℕ) = 2 ^ k := rfl
  refine (hL k N hk hN (resWeight k) (resWeight_neg k) f).trans ?_
  have hU1 := hU k N hk hN
  have hM1 := hM k N hk hN
  have hU0 : 0 ≤ gowersNormInterval 3 N (resWeight k) := by
    rw [gowersNormInterval_eq_gowersNormOn]; exact gowersNormOn_nonneg _ _ _
  have hM0 := lpNormOn_nonneg 2 (bracket N) (resWeight k)
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  calc C_L * (k : ℝ) ^ (2 / r) * gowersNormInterval 3 N (resWeight k) ^ (1 - 2 / r) *
        lpNormOn 2 (bracket N) (resWeight k) ^ (2 / r)
      ≤ C_L * (k : ℝ) ^ (2 / r) * (C_U * (k : ℝ) ^ (-A)) ^ (1 - 2 / r) *
          (C_M * k) ^ (2 / r) := by
        gcongr
    _ = C_L * C_U ^ (1 - 2 / r) * C_M ^ (2 / r) * (k : ℝ) ^ (4 / r - A * (1 - 2 / r)) := by
        rw [rpow_mul_rpow_aux hCU0 hk0.le, show (C_M * (k : ℝ)) ^ (2 / r) =
          C_M ^ (2 / r) * (k : ℝ) ^ (2 / r) from Real.mul_rpow hCM0 hk0.le]
        have : (k : ℝ) ^ (4 / r - A * (1 - 2 / r)) =
            (k : ℝ) ^ (2 / r) * (k : ℝ) ^ (-A * (1 - 2 / r)) * (k : ℝ) ^ (2 / r) := by
          rw [← Real.rpow_add hk0, ← Real.rpow_add hk0]; congr 1; ring
        rw [this]; ring

/-- **`e:minor-var-crude-red`** (L1360-L1371): for every `s ≥ r'`,
`‖V^r(∑_n f(x-n) (w - w_{≤ M(k)})(n) ψ_k(n) e(λ n) : λ)‖_{ℓ^s} ≲_{s,r} k^{O_r(1)} ‖f‖_{ℓ^s}`
(the `O_r(1)` is `1`). -/
theorem minor_var_crude_red (ψ : PsiData) {r : ℝ} (hr : 2 < r) {s : ℝ} (hs : r / (r - 1) ≤ s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 1 ≤ k → ∀ f : ℤ →₀ ℂ,
      eLpNorm (varOp r (fun n => resWeight k n * psiKz ψ k n) (⇑f)) (ENNReal.ofReal s)
          Measure.count ≤
        ENNReal.ofReal (C * (k : ℝ)) * eLpNorm (⇑f) (ENNReal.ofReal s) Measure.count := by
  obtain ⟨C_c, hCc0, hc⟩ := crude_piece_le ψ hr
  obtain ⟨C_M, hCM0, hM⟩ := residual_L2_moment_oneSided
  have hr1 : 0 < r - 1 := by linarith
  have hr'1 : 1 ≤ r / (r - 1) := by rw [le_div_iff₀ hr1]; linarith
  have hr'2 : r / (r - 1) ≤ 2 := by rw [div_le_iff₀ hr1]; linarith
  refine ⟨C_c * C_M, by positivity, fun k hk f => ?_⟩
  set N : ℕ+ := ⟨2 ^ k, by positivity⟩ with hNdef
  have hN : (N : ℕ) = 2 ^ k := rfl
  refine (hc k N hk hN (resWeight k) (resWeight_neg k) s hs f).trans ?_
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  have h1 := lpNormOn_le_two hr'1 hr'2 (bracket_nonempty N) (resWeight k)
  have h2 := hM k N hk hN
  calc C_c * lpNormOn (r / (r - 1)) (bracket N) (resWeight k)
      ≤ C_c * (C_M * k) := mul_le_mul_of_nonneg_left (h1.trans h2) hCc0
    _ = C_c * C_M * k := by ring

/-- **The residual sum** (Source: main paper `p:red-var`, L1374–L1387): for `p > r'`,
`∑_{k ≥ 1} ‖V^r(∑_n f(x-n) (w - w_{≤ M(k)})(n) ψ_k(n) e(λ n) : λ)‖_{ℓ^p} ≲_{p,r} ‖f‖_{ℓ^p}`
(interpolating `e:minor-var-L2-red` and `e:minor-var-crude-red` by Marcinkiewicz, with
`A = A(p, r)` large, `∑_k k^{-2} < ∞`). -/
theorem residual_sum (ψ : PsiData) {r p : ℝ} (hr : 2 < r) (hp : r / (r - 1) < p)
    (hLoc : LocalU3VarRed ψ r) (hF : FplusProp31) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℤ →₀ ℂ,
      ∑' k : ℕ, eLpNorm (varOp r (fun n => resWeight (k + 1) n * psiKz ψ (k + 1) n) (⇑f))
          (ENNReal.ofReal p) Measure.count ≤
        ENNReal.ofReal C * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
  obtain ⟨s, ϑ, Cint, hs, hϑ0, hϑ1, hCint0, hint⟩ := varOp_interp hr hp
  have ha : 0 < 1 - 2 / r := by
    rw [sub_pos, div_lt_one (by linarith)]; exact hr
  set a : ℝ := 1 - 2 / r with hadef
  set A : ℝ := (4 * ϑ / r + 3) / (ϑ * a) with hAdef
  obtain ⟨C₀, hC₀, h₀⟩ := minor_var_L2_red ψ hr hLoc hF A
  obtain ⟨C₁, hC₁, h₁⟩ := minor_var_crude_red ψ hr hs
  set C₀' : ℝ := max C₀ 1 with hC₀'
  set C₁' : ℝ := max C₁ 1 with hC₁'
  have hC₀'0 : 0 < C₀' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hC₁'0 : 0 < C₁' := lt_of_lt_of_le one_pos (le_max_right _ _)
  -- the exponent
  have hexp : ϑ * (4 / r - A * a) + (1 - ϑ) = -2 - ϑ := by
    have hAa : A * a = (4 * ϑ / r + 3) / ϑ := by
      rw [hAdef]; field_simp
    rw [mul_sub, show ϑ * (A * a) = 4 * ϑ / r + 3 by rw [hAa]; field_simp]
    ring
  set K : ℝ := Cint * C₀' ^ ϑ * C₁' ^ (1 - ϑ) with hK
  have hpt : ∀ (k : ℕ) (f : ℤ →₀ ℂ),
      eLpNorm (varOp r (fun n => resWeight (k + 1) n * psiKz ψ (k + 1) n) (⇑f))
          (ENNReal.ofReal p) Measure.count ≤
        ENNReal.ofReal (K * (((k + 1 : ℕ) : ℝ)) ^ (-2 : ℝ)) *
          eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
    intro k f
    have hk1 : 1 ≤ k + 1 := by omega
    have hk0 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    have hk1r : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast hk1
    set κ : ℝ := ((k + 1 : ℕ) : ℝ) with hκ
    have hX₀ : 0 < C₀' * κ ^ (4 / r - A * a) := by positivity
    have hX₁ : 0 < C₁' * κ := by positivity
    have h := hint (fun n => resWeight (k + 1) n * psiKz ψ (k + 1) n) (C₀' * κ ^ (4 / r - A * a))
      (C₁' * κ) hX₀ hX₁
      (fun g => (h₀ (k + 1) hk1 g).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))) le_rfl))
      (fun g => (h₁ (k + 1) hk1 g).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))) le_rfl)) f
    refine h.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
    rw [rpow_mul_rpow_aux hC₀'0.le hk0.le, Real.mul_rpow hC₁'0.le hk0.le]
    have hκe : κ ^ ((4 / r - A * a) * ϑ) * κ ^ (1 - ϑ) = κ ^ (-2 - ϑ) := by
      rw [← Real.rpow_add hk0]; congr 1; linarith
    have hle : κ ^ (-2 - ϑ) ≤ κ ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hk1r (by linarith)
    calc Cint * (C₀' ^ ϑ * κ ^ ((4 / r - A * a) * ϑ)) * (C₁' ^ (1 - ϑ) * κ ^ (1 - ϑ))
        = K * (κ ^ ((4 / r - A * a) * ϑ) * κ ^ (1 - ϑ)) := by rw [hK]; ring
      _ = K * κ ^ (-2 - ϑ) := by rw [hκe]
      _ ≤ K * κ ^ (-2 : ℝ) := by
          refine mul_le_mul_of_nonneg_left hle (by positivity)
  -- summation
  have hsum : Summable (fun k : ℕ => (((k + 1 : ℕ) : ℝ)) ^ (-2 : ℝ)) :=
    (summable_nat_add_iff (f := fun k : ℕ => (k : ℝ) ^ (-2 : ℝ)) 1).2
      (Real.summable_nat_rpow.2 (by norm_num))
  refine ⟨K * ∑' k : ℕ, (((k + 1 : ℕ) : ℝ)) ^ (-2 : ℝ), by positivity, fun f => ?_⟩
  calc ∑' k : ℕ, eLpNorm (varOp r (fun n => resWeight (k + 1) n * psiKz ψ (k + 1) n) (⇑f))
          (ENNReal.ofReal p) Measure.count
      ≤ ∑' k : ℕ, ENNReal.ofReal (K * (((k + 1 : ℕ) : ℝ)) ^ (-2 : ℝ)) *
          eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count :=
        ENNReal.tsum_le_tsum fun k => hpt k f
    _ = (∑' k : ℕ, ENNReal.ofReal (K * (((k + 1 : ℕ) : ℝ)) ^ (-2 : ℝ))) *
          eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by rw [ENNReal.tsum_mul_right]
    _ = ENNReal.ofReal (K * ∑' k : ℕ, (((k + 1 : ℕ) : ℝ)) ^ (-2 : ℝ)) *
          eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
        congr 1
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity)
          (hsum.mul_left K), tsum_mul_left]

end PrimeCarleson.Proof.Paper
