module

public import PrimeCarleson.Proof.Paper.Main.RedVar
public import PrimeCarleson.Proof.Paper.P6b.Main
public import PrimeCarleson.Proof.Paper.P10.BlockSum
public import PrimeCarleson.Proof.Paper.P4b.Smooth

/-!
# The bound for a fixed pair `(r, p)` with explicit parameters

Source: main paper `t:main`, L1530–L1543 and L1735–L1761; the paper does not choose the parameters
explicitly (L302–L305).

For `r > 2`, an exponent `s > r' = r/(r-1)` and `θ ∈ (0, 1)` with `1/p = θ/2 + (1-θ)/s` the
paper's numerical condition `(1-θ)/r < θ ε α / 2` (L1554) is decided by the explicit choices
`α = (1 - 2/r)/2` and `D₀ = K / (θ (1 - 2/r))`, `ε = 1/(101 D₀)`, where `K = 32 + max(1/κ₀, 1)`
is an absolute constant (`κ₀ = blockKappaZero`, the `ℓ²` saving of `C^Q` for `κ ≤ κ₀`). The
threshold `D₀ ≥ 32/(θ (1 - 2/r))` of the high-denominator sum is the explicit `D₁(p, r)` of
`Main/Interp.lean`. The numerical condition becomes `(1-θ)/θ² < μ(r)` with
`μ(r) = r (1 - 2/r)² / (404 K)` (`muR`), which does not mention `p` or `s`.

* `exists_KQSetup_exact`: a setup with prescribed `D₀`, `ε = 1/(101 D₀)`, `SupportBlock` and
  `SupportScale (1/16)`;
* `tmain_pair` (the bound for a fixed exponent, L1735–L1761): `‖V^r_P f‖_{ℓ^p} ≤ K ‖f‖_{ℓ^p}`
  for `p ≠ 2` given
  `(1-θ)/θ² < μ(r)`;
* `tmain_two`: the case `p = 2`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson

/-- The absolute constant `K = 32 + max(1/κ₀, 1)`: `D₀ ≥ K` gives the `ℓ²` saving of `C^Q`
(`κ₀ = blockKappaZero`) and `K ≥ 33`. -/
def mainK : ℝ := 32 + max (1 / blockKappaZero) 1

/-- `K ≥ 33`. -/
theorem mainK_ge : 33 ≤ mainK := by
  unfold mainK
  have := le_max_right (1 / blockKappaZero) 1
  linarith

/-- `1/κ₀ ≤ K`. -/
theorem inv_blockKappaZero_le_mainK : 1 / blockKappaZero ≤ mainK := by
  unfold mainK
  have := le_max_left (1 / blockKappaZero) 1
  linarith

/-- The quantity `μ(r) = r (1 - 2/r)² / (404 K)` bounding `(1-θ)/θ²` in the numerical condition of
`e:interp-var-l2-condition` (L1554) for the choices of `D₀` and `α` of this file. -/
def muR (r : ℝ) : ℝ := r * (1 - 2 / r) ^ 2 / (404 * mainK)

/-- `μ(r) > 0` for `r > 2`. -/
theorem muR_pos {r : ℝ} (hr : 2 < r) : 0 < muR r := by
  have hr0 : 0 < r := by linarith
  have ha : 0 < 1 - 2 / r := by rw [sub_pos, div_lt_one hr0]; exact hr
  have := mainK_ge
  unfold muR
  positivity

/-- **Setups of `K_Q` with `D₀` prescribed**: for every `D > 0` there is a setup `S` (the fixed
cutoffs `ψ`, `φ` and the parameters `D₀ = D`, `ε = 1/(101 D)`) satisfying (C1) `SupportBlock` and
(C2) `SupportScale (1/16)`. -/
theorem exists_KQSetup_exact {D : ℝ} (hD : 0 < D) :
    ∃ S : KQSetup, S.P.D₀ = D ∧ S.P.ε = 1 / (101 * D) ∧ S.P.SupportBlock S.δ ∧
      S.P.SupportScale S.δ (1 / 16) := by
  let P : KQParams := ⟨D, 1 / (101 * D), hD, by positivity, (KQParams.eps_le_iff hD).2 le_rfl⟩
  obtain ⟨δ, hδ, hδS⟩ := P.exists_delta0 (c := 1 / 16) (by norm_num)
  obtain ⟨φ⟩ := PhiData.nonempty hδ
  obtain ⟨ψ⟩ := PsiData.nonempty
  exact ⟨⟨ψ, δ, hδ, φ, P⟩, rfl, rfl, (hδS δ hδ le_rfl).1, (hδS δ hδ le_rfl).2⟩

/-- `D₀ ≥ 1/κ₀` gives the `ℓ²` saving `CQL2Saving S` of `C^Q` (Source: main paper, L1742–L1745; the
quantifier form `exists_D₀_cqL2Saving` of `P10/BlockSum.lean` with its threshold `1/κ₀` named). -/
theorem cqL2Saving_of_D₀_ge (hO : OplusVariationBound) (S : KQSetup)
    (hS : S.P.SupportBlock S.δ) (hD : 1 / blockKappaZero ≤ S.P.D₀) : CQL2Saving S := by
  refine cqL2Saving_of_kappa_le hO S hS ?_
  have hk0 := blockKappaZero_pos
  have hD0 := S.P.D₀_pos
  have hε := S.P.ε_pos
  have h1 : 1 / S.P.D₀ ≤ blockKappaZero := by
    rw [div_le_iff₀ hD0]
    rw [div_le_iff₀ hk0] at hD
    linarith
  unfold KQParams.kappa
  linarith

/-- The arithmetic of the numerical condition: for `D = K / (θ a)` and `ε = 1/(101 D)`,
`(1-θ)/θ² < r a² / (404 K)` is `(1-θ)/r < θ (ε (a/2) / 2)`. -/
theorem range_cond_arith {r θ a K D ε : ℝ} (hr0 : 0 < r) (hθ0 : 0 < θ) (ha0 : 0 < a)
    (hK : 0 < K) (hD : D = K / (θ * a)) (hε : ε = 1 / (101 * D))
    (hμ : (1 - θ) / θ ^ 2 < r * a ^ 2 / (404 * K)) :
    (1 - θ) / r < θ * (ε * (a / 2) / 2) := by
  have hε' : ε = θ * a / (101 * K) := by
    rw [hε, hD]; field_simp
  rw [div_lt_div_iff₀ (by positivity) (by positivity)] at hμ
  rw [hε', div_lt_iff₀ hr0]
  have h : θ * (θ * a / (101 * K) * (a / 2) / 2) * r = r * a ^ 2 * θ ^ 2 / (404 * K) := by
    field_simp; ring
  rw [h, lt_div_iff₀ (by positivity)]
  nlinarith

/-- `p > r'` for `1/p = θ/2 + (1-θ)/s` with `θ ∈ (0, 1)` and `s > r'`, `r > 2`. -/
theorem lt_of_interp {r s θ p : ℝ} (hr : 2 < r) (hs : r / (r - 1) < s) (hθ0 : 0 < θ)
    (hθ1 : θ < 1) (hpθ : 1 / p = θ / 2 + (1 - θ) / s) : r / (r - 1) < p := by
  have hr0 : 0 < r := by linarith
  have hr1 : 0 < r - 1 := by linarith
  have hr'0 : 0 < r / (r - 1) := div_pos hr0 hr1
  have hs0 : 0 < s := hr'0.trans hs
  have hp0 : 0 < p := by
    have : 0 < 1 / p := by
      rw [hpθ]
      have : 0 < (1 - θ) / s := div_pos (by linarith) hs0
      have : 0 < θ / 2 := by positivity
      linarith
    exact one_div_pos.1 this
  have h1 : 1 / p < 1 / (r / (r - 1)) := by
    rw [hpθ, one_div_div]
    have h2 : 1 / s < (r - 1) / r := by
      have := one_div_lt_one_div_of_lt hr'0 hs
      rwa [one_div_div] at this
    have h3 : 1 / 2 < (r - 1) / r := by
      rw [div_lt_div_iff₀ (by norm_num) hr0]; linarith
    have key : (r - 1) / r - (θ / 2 + (1 - θ) / s) =
        θ * ((r - 1) / r - 1 / 2) + (1 - θ) * ((r - 1) / r - 1 / s) := by ring
    have := add_pos (mul_pos hθ0 (sub_pos.2 h3)) (mul_pos (sub_pos.2 hθ1) (sub_pos.2 h2))
    linarith
  exact (one_div_lt_one_div hp0 hr'0).1 h1

/-- **The bound of `t:main` for a fixed exponent `p`** (Source: main paper `t:main`, L1735–L1761,
with the exponents and weights of the choices at L1530–L1543 and L1188–L1192 as parameters): for
`r > 2`, `s > r'`, `s ≠ 2`, `θ ∈ (0, 1)` with `1/p = θ/2 + (1-θ)/s` (so `p ≠ 2`, `p > r'`) and
`(1-θ)/θ² < μ(r)` there is `0 < K` with `‖V^r_P f‖_{ℓ^p} ≤ K ‖f‖_{ℓ^p}` for all finitely supported
`f`. Conditional on `hO` (`[O+]`) and `hF` (`[F+, Proposition 3.1]`). -/
theorem tmain_pair (hO : OplusVariationBound) (hF : FplusProp31) {r s θ p : ℝ} (hr : 2 < r)
    (hs : r / (r - 1) < s) (hs2 : s ≠ 2) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hpθ : 1 / p = θ / 2 + (1 - θ) / s) (hμ : (1 - θ) / θ ^ 2 < muR r) :
    ∃ K : ℝ, 0 < K ∧ ∀ f : ℤ →₀ ℂ,
      eLpNorm (primeVariation r f) (ENNReal.ofReal p) Measure.count ≤
        ENNReal.ofReal K * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
  have hr0 : 0 < r := by linarith
  have hr1 : 0 < r - 1 := by linarith
  have hr'0 : 0 < r / (r - 1) := div_pos hr0 hr1
  have hs0 : 0 < s := hr'0.trans hs
  have ha0 : 0 < 1 - 2 / r := by rw [sub_pos, div_lt_one hr0]; exact hr
  have ha1 : 1 - 2 / r < 1 := by
    have : 0 < 2 / r := by positivity
    linarith
  have hp : r / (r - 1) < p := lt_of_interp hr hs hθ0 hθ1 hpθ
  have hKc := mainK_ge
  have hθa : 0 < θ * (1 - 2 / r) := mul_pos hθ0 ha0
  have hθa1 : θ * (1 - 2 / r) < 1 := by nlinarith
  have hD0 : 0 < mainK / (θ * (1 - 2 / r)) := div_pos (by linarith) hθa
  obtain ⟨S, hSD, hSε, hS, hSc⟩ := exists_KQSetup_exact hD0
  have hDge : mainK ≤ mainK / (θ * (1 - 2 / r)) := by
    rw [le_div_iff₀ hθa]; nlinarith
  have hCQ : CQL2Saving S := cqL2Saving_of_D₀_ge hO S hS
    (by rw [hSD]; exact inv_blockKappaZero_le_mainK.trans hDge)
  have hint : VarOpInterp r p s θ := varOp_interp_param hr hs0 hs2 hθ0 hθ1 hpθ
  have hH := highQSum_of_param hr hs.le hθ0 hθ1.le hint
  have hD32 : 32 / (θ * (1 - 2 / r)) ≤ S.P.D₀ := by
    rw [hSD]; exact div_le_div_of_nonneg_right (by linarith) hθa.le
  have hcond : (1 - θ) / r < θ * (S.P.ε * ((1 - 2 / r) / 2) / 2) :=
    range_cond_arith hr0 hθ0 ha0 (by linarith) hSD (by rw [hSD]; exact hSε) hμ
  have hrange : p = 2 ∨ ∃ s θ α : ℝ, r / (r - 1) < s ∧ 0 < θ ∧ θ < 1 ∧
      1 / p = θ / 2 + (1 - θ) / s ∧ 0 < α ∧ α < 1 - 2 / r ∧
      (1 - θ) / r < θ * (S.P.ε * α / 2) :=
    Or.inr ⟨s, θ, (1 - 2 / r) / 2, hs, hθ0, hθ1, hpθ, by positivity, by linarith, hcond⟩
  exact red_var_param hr hp hF (varCarZ_of_oplusBound hO hr) hH S
    (localU3VarRed_holds S.ψ hr) hD32 (red_var_premise hO S hS hSc hCQ hr hrange)

/-- **The bound of `t:main` for `p = 2`** (L1589: for `p = 2` the `ℓ²` power saving
alone gives `e:red-var`): for `r > 2` there is `0 < K` with
`‖V^r_P f‖_{ℓ²} ≤ K ‖f‖_{ℓ²}` for all finitely supported `f`. -/
theorem tmain_two (hO : OplusVariationBound) (hF : FplusProp31) {r : ℝ} (hr : 2 < r) :
    ∃ K : ℝ, 0 < K ∧ ∀ f : ℤ →₀ ℂ,
      eLpNorm (primeVariation r f) (ENNReal.ofReal 2) Measure.count ≤
        ENNReal.ofReal K * eLpNorm (⇑f) (ENNReal.ofReal 2) Measure.count := by
  have hr0 : 0 < r := by linarith
  have hr1 : 0 < r - 1 := by linarith
  have hr'2 : r / (r - 1) < 2 := by rw [div_lt_iff₀ hr1]; linarith
  have ha0 : 0 < 1 - 2 / r := by rw [sub_pos, div_lt_one hr0]; exact hr
  have ha1 : 1 - 2 / r < 1 := by
    have : 0 < 2 / r := by positivity
    linarith
  have hKc := mainK_ge
  have hD0 : 0 < mainK / (1 - 2 / r) := div_pos (by linarith) ha0
  obtain ⟨S, hSD, -, hS, hSc⟩ := exists_KQSetup_exact hD0
  have hDge : mainK ≤ mainK / (1 - 2 / r) := by
    rw [le_div_iff₀ ha0]; nlinarith
  have hCQ : CQL2Saving S := cqL2Saving_of_D₀_ge hO S hS
    (by rw [hSD]; exact inv_blockKappaZero_le_mainK.trans hDge)
  have hH := highQSum_of_param hr (hr'2.le.trans le_rfl) one_pos le_rfl (varOp_interp_two r)
  have hD32 : 32 / (1 * (1 - 2 / r)) ≤ S.P.D₀ := by
    rw [hSD, one_mul]; exact div_le_div_of_nonneg_right (by linarith) ha0.le
  exact red_var_param hr hr'2 hF (varCarZ_of_oplusBound hO hr) hH S
    (localU3VarRed_holds S.ψ hr) hD32
    (red_var_premise hO S hS hSc hCQ hr (Or.inl rfl))

end PrimeCarleson.Proof.Paper
