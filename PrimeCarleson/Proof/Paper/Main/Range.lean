module

public import PrimeCarleson.Proof.Paper.Main.Setup

/-!
# The explicit range `(𝐜(r), 𝐂(r))` of `t:main` and its limits

`sources/Variational_Carleson.tex` L302-L305 and L1760-L1761 (Source: main paper `t:main`,
L302–L305; main paper `t:main`, L304). The paper never constructs `𝐜(r)` and `𝐂(r)` and does not
prove their limits; here they are

* `θ(r) = 1 / √(1 + μ(r))` (`thetaR`), with `μ(r) = r (1 - 2/r)² / (404 K)` (`muR`), so that
  `(1-θ)/θ² = √(1+μ)² - √(1+μ) < μ` (`thetaR_cond`) and `θ(r) → 0`;
* `1/𝐜(r) = θ/2 + (1-θ)/s₋` with `s₋ = 1 + 2/r ∈ (r', 2)` (`cR`);
* `1/𝐂(r) = θ/2 + (1-θ)/s₊` with `s₊ = r > 2` (`CR`).

`r' < 𝐜(r) < 2 < 𝐂(r)` (`cR_gt`, `cR_lt`, `two_lt_CR`), `𝐜(r) → 1` (`tendsto_cR`) and
`𝐂(r) → ∞` (`tendsto_CR`). `exists_theta_gt` is the monotonicity used to pass from the exponents
`𝐜(r)`, `𝐂(r)` to every `p` in between (`Main/Root.lean`).
-/

@[expose] public noncomputable section

open Filter Topology

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

/-- The interpolation weight `θ(r) = 1 / √(1 + μ(r))` at the endpoints of the range. -/
def thetaR (r : ℝ) : ℝ := 1 / Real.sqrt (1 + muR r)

/-- The lower endpoint `𝐜(r)`: `1/𝐜(r) = θ(r)/2 + (1 - θ(r))/s₋` with `1/s₋ = r/(r+2)`, i.e.
`s₋ = 1 + 2/r` (`r' < s₋ < 2` for `r > 2`). -/
def cR (r : ℝ) : ℝ := (thetaR r / 2 + (1 - thetaR r) * (r / (r + 2)))⁻¹

/-- The upper endpoint `𝐂(r)`: `1/𝐂(r) = θ(r)/2 + (1 - θ(r))/r`. -/
def CR (r : ℝ) : ℝ := (thetaR r / 2 + (1 - thetaR r) / r)⁻¹

/-- `θ(r) > 0` for `r > 2`. -/
theorem thetaR_pos {r : ℝ} (hr : 2 < r) : 0 < thetaR r := by
  have := muR_pos hr
  unfold thetaR
  positivity

/-- `1 < √(1 + μ(r))` for `r > 2`. -/
theorem one_lt_sqrt_muR {r : ℝ} (hr : 2 < r) : 1 < Real.sqrt (1 + muR r) := by
  have := muR_pos hr
  rw [Real.lt_sqrt (by norm_num)]
  linarith

/-- `θ(r) < 1` for `r > 2`. -/
theorem thetaR_lt_one {r : ℝ} (hr : 2 < r) : thetaR r < 1 := by
  have h1 := one_lt_sqrt_muR hr
  unfold thetaR
  rw [div_lt_one (by linarith)]
  exact h1

/-- `(1 - θ(r)) / θ(r)² < μ(r)` for `r > 2`: with `q = √(1 + μ)` the left side is `q² - q`. -/
theorem thetaR_cond {r : ℝ} (hr : 2 < r) : (1 - thetaR r) / thetaR r ^ 2 < muR r := by
  have hμ := muR_pos hr
  have hq1 := one_lt_sqrt_muR hr
  have hq2 : Real.sqrt (1 + muR r) ^ 2 = 1 + muR r := Real.sq_sqrt (by linarith)
  unfold thetaR
  set q := Real.sqrt (1 + muR r) with hq
  have hq0 : q ≠ 0 := by linarith
  have : (1 - 1 / q) / (1 / q) ^ 2 = q ^ 2 - q := by field_simp
  rw [this]
  linarith

/-- The mixed exponent at the lower endpoint lies in `(1/2, (r-1)/r)`. -/
theorem cR_inner_bounds {r : ℝ} (hr : 2 < r) :
    1 / 2 < thetaR r / 2 + (1 - thetaR r) * (r / (r + 2)) ∧
      thetaR r / 2 + (1 - thetaR r) * (r / (r + 2)) < (r - 1) / r := by
  have hθ0 := thetaR_pos hr
  have hθ1 := thetaR_lt_one hr
  have hr0 : 0 < r := by linarith
  have hr2 : 0 < r + 2 := by linarith
  have hr2' : 0 < r - 2 := by linarith
  set θ := thetaR r with hθ
  have e1 : r / (r + 2) - 1 / 2 = (r - 2) / (2 * (r + 2)) := by field_simp; ring
  have e2 : (r - 1) / r - 1 / 2 = (r - 2) / (2 * r) := by field_simp; ring
  have e3 : (r - 1) / r - r / (r + 2) = (r - 2) / (r * (r + 2)) := by field_simp; ring
  constructor
  · have : θ / 2 + (1 - θ) * (r / (r + 2)) - 1 / 2 = (1 - θ) * ((r - 2) / (2 * (r + 2))) := by
      rw [← e1]; ring
    have h : 0 < (1 - θ) * ((r - 2) / (2 * (r + 2))) := mul_pos (by linarith) (by positivity)
    linarith
  · have : (r - 1) / r - (θ / 2 + (1 - θ) * (r / (r + 2))) =
        θ * ((r - 2) / (2 * r)) + (1 - θ) * ((r - 2) / (r * (r + 2))) := by
      rw [← e2, ← e3]; ring
    have h : 0 < θ * ((r - 2) / (2 * r)) + (1 - θ) * ((r - 2) / (r * (r + 2))) :=
      add_pos (mul_pos hθ0 (by positivity)) (mul_pos (by linarith) (by positivity))
    linarith

/-- `r' < 𝐜(r)` for `r > 2`. -/
theorem cR_gt {r : ℝ} (hr : 2 < r) : r / (r - 1) < cR r := by
  obtain ⟨h1, h2⟩ := cR_inner_bounds hr
  have hr0 : 0 < r := by linarith
  have hr1 : 0 < r - 1 := by linarith
  have hin : 0 < thetaR r / 2 + (1 - thetaR r) * (r / (r + 2)) := by linarith
  unfold cR
  rw [← inv_div, inv_lt_inv₀ (by positivity) hin]
  exact h2

/-- `𝐜(r) < 2` for `r > 2`. -/
theorem cR_lt {r : ℝ} (hr : 2 < r) : cR r < 2 := by
  obtain ⟨h1, -⟩ := cR_inner_bounds hr
  unfold cR
  rw [inv_lt_comm₀ (by linarith) (by norm_num)]
  norm_num
  exact h1

/-- `2 < 𝐂(r)` for `r > 2`. -/
theorem two_lt_CR {r : ℝ} (hr : 2 < r) : 2 < CR r := by
  have hθ0 := thetaR_pos hr
  have hθ1 := thetaR_lt_one hr
  have hr0 : 0 < r := by linarith
  have h1 : 0 < 1 / 2 - 1 / r := by
    rw [sub_pos]; exact one_div_lt_one_div_of_lt (by norm_num) hr
  have hpos : 0 < thetaR r / 2 + (1 - thetaR r) / r := by
    have : 0 < (1 - thetaR r) / r := div_pos (by linarith) hr0
    linarith
  have hlt : thetaR r / 2 + (1 - thetaR r) / r < 1 / 2 := by
    have : 1 / 2 - (thetaR r / 2 + (1 - thetaR r) / r) = (1 - thetaR r) * (1 / 2 - 1 / r) := by
      ring
    have h : 0 < (1 - thetaR r) * (1 / 2 - 1 / r) := mul_pos (by linarith) h1
    linarith
  unfold CR
  rw [lt_inv_comm₀ (by norm_num) hpos]
  linarith

/-- **Monotonicity along a segment**: if `c = θ u₀ + (1-θ) u₁` with `0 < θ < 1` and `u` lies
strictly between `c` and `u₀`, then `u = θ' u₀ + (1-θ') u₁` for some `θ' ∈ (θ, 1)`. -/
theorem exists_theta_gt {u₀ u₁ u c θ : ℝ} (hθ1 : θ < 1) (hc : c = θ * u₀ + (1 - θ) * u₁)
    (hu : (c < u ∧ u < u₀) ∨ (u₀ < u ∧ u < c)) :
    ∃ θ' : ℝ, θ < θ' ∧ θ' < 1 ∧ u = θ' * u₀ + (1 - θ') * u₁ := by
  have hd : u₀ - c = (1 - θ) * (u₀ - u₁) := by rw [hc]; ring
  have h1θ : 0 < 1 - θ := by linarith
  rcases hu with ⟨hcu, huu₀⟩ | ⟨huu₀, hcu⟩
  · have hpos : 0 < u₀ - u₁ := by
      have : 0 < (1 - θ) * (u₀ - u₁) := by rw [← hd]; linarith
      exact pos_of_mul_pos_right this h1θ.le
    refine ⟨θ + (u - c) / (u₀ - u₁), ?_, ?_, ?_⟩
    · have : 0 < (u - c) / (u₀ - u₁) := div_pos (by linarith) hpos
      linarith
    · have : (u - c) / (u₀ - u₁) < 1 - θ := by
        rw [div_lt_iff₀ hpos]; nlinarith
      linarith
    · have : (u - c) / (u₀ - u₁) * (u₀ - u₁) = u - c := div_mul_cancel₀ _ hpos.ne'
      rw [hc] at this ⊢
      nlinarith
  · have hneg : u₀ - u₁ < 0 := by
      have : (1 - θ) * (u₀ - u₁) < 0 := by rw [← hd]; linarith
      by_contra hcon
      have := not_lt.1 hcon
      nlinarith
    refine ⟨θ + (u - c) / (u₀ - u₁), ?_, ?_, ?_⟩
    · have : 0 < (u - c) / (u₀ - u₁) := div_pos_of_neg_of_neg (by linarith) hneg
      linarith
    · have : (u - c) / (u₀ - u₁) < 1 - θ := by
        rw [div_lt_iff_of_neg hneg]; nlinarith
      linarith
    · have : (u - c) / (u₀ - u₁) * (u₀ - u₁) = u - c := div_mul_cancel₀ _ hneg.ne
      rw [hc] at this ⊢
      nlinarith

/-- `(1-θ')/θ'² ≤ (1-θ)/θ²` for `0 < θ ≤ θ' ≤ 1`. -/
theorem sub_div_sq_anti {θ θ' : ℝ} (hθ0 : 0 < θ) (hθθ' : θ ≤ θ') (hθ' : θ' ≤ 1) :
    (1 - θ') / θ' ^ 2 ≤ (1 - θ) / θ ^ 2 :=
  div_le_div₀ (by linarith) (by linarith) (by positivity) (pow_le_pow_left₀ hθ0.le hθθ' 2)

/-- `μ(r) → ∞` as `r → ∞`. -/
theorem tendsto_muR : Tendsto muR atTop atTop := by
  have hK := mainK_ge
  have h1 : Tendsto (fun r : ℝ => (r - 4) / (404 * mainK)) atTop atTop := by
    refine Tendsto.atTop_div_const (by positivity) ?_
    exact tendsto_atTop_atTop.2 fun b => ⟨b + 4, fun a ha => by linarith⟩
  refine tendsto_atTop_mono' atTop ?_ h1
  filter_upwards [eventually_gt_atTop 0] with r hr
  unfold muR
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  have : r * (1 - 2 / r) ^ 2 = r - 4 + 4 / r := by field_simp; ring
  rw [this]
  have : 0 < 4 / r := by positivity
  linarith

/-- `θ(r) → 0` as `r → ∞`. -/
theorem tendsto_thetaR : Tendsto thetaR atTop (𝓝 0) := by
  have h : Tendsto (fun r : ℝ => Real.sqrt (1 + muR r)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_atTop_add_const_left atTop 1 tendsto_muR)
  refine (tendsto_inv_atTop_zero.comp h).congr fun r => ?_
  simp [thetaR, one_div]

/-- `r / (r + 2) → 1` as `r → ∞`. -/
theorem tendsto_div_add_two : Tendsto (fun r : ℝ => r / (r + 2)) atTop (𝓝 1) := by
  have h : Tendsto (fun r : ℝ => 1 - 2 / (r + 2)) atTop (𝓝 1) := by
    have h2 : Tendsto (fun r : ℝ => 2 / (r + 2)) atTop (𝓝 0) :=
      Tendsto.div_atTop tendsto_const_nhds (tendsto_atTop_add_const_right atTop 2 tendsto_id)
    simpa using tendsto_const_nhds.sub h2
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with r hr
  field_simp
  ring

/-- **The limit `𝐜(r) → 1`** (Source: main paper `t:main`, L304): `𝐜(r) → 1` as `r → ∞`. -/
theorem tendsto_cR : Tendsto cR atTop (𝓝 1) := by
  have h1 : Tendsto (fun r : ℝ => thetaR r / 2 + (1 - thetaR r) * (r / (r + 2))) atTop (𝓝 1) := by
    have := (tendsto_thetaR.div_const 2).add
      (((tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_thetaR).mul tendsto_div_add_two)
    simpa using this
  have h2 := h1.inv₀ one_ne_zero
  rw [inv_one] at h2
  exact h2

/-- **The limit `𝐂(r) → ∞`** (Source: main paper `t:main`, L304): `𝐂(r) → ∞` as `r → ∞`. -/
theorem tendsto_CR : Tendsto CR atTop atTop := by
  have h0 : Tendsto (fun r : ℝ => thetaR r / 2 + (1 - thetaR r) / r) atTop (𝓝 0) := by
    have := (tendsto_thetaR.div_const 2).add
      (((tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_thetaR).mul
        (tendsto_inv_atTop_zero (𝕜 := ℝ)))
    simpa [div_eq_mul_inv] using this
  have h : Tendsto (fun r : ℝ => thetaR r / 2 + (1 - thetaR r) / r) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨h0, ?_⟩
    filter_upwards [eventually_gt_atTop 2] with r hr
    have h1 := thetaR_pos hr
    have h2 := thetaR_lt_one hr
    have : 0 < (1 - thetaR r) / r := div_pos (by linarith) (by linarith)
    change 0 < thetaR r / 2 + (1 - thetaR r) / r
    linarith
  exact h.inv_tendsto_nhdsGT_zero

end PrimeCarleson.Proof.Paper
