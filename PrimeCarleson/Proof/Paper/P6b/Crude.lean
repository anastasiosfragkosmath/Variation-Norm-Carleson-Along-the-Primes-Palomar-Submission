module

public import PrimeCarleson.Proof.Paper.P6b.Dilation
public import PrimeCarleson.Proof.Paper.P6b.Weights
public import PrimeCarleson.Proof.Paper.P7.Disc
public import PrimeCarleson.Proof.Paper.P7.DiscSup
public import PrimeCarleson.Proof.Paper.P5.Support

/-!
# The crude `ℓ^s` bounds `‖V^{Q,r} f‖_s ≲ Q^{1/r+o(1)} ‖f‖_s`, `‖C^Q f‖_s ≲ Q^{o(1)}`

Source: main paper `l:red-var-l2`, L1694–L1706, L1706–L1715 and L1729–L1731; main paper
`e:crude-var-Q-bound`, L1592–L1597. The input `c:disc` is `cdisc_of_oplus` (`P7/`), the single-`λ`
and maximal bound is `sup_modulated_of_oplus`; both are conditional on `hO : OplusVariationBound`.
The uniform bounded variation of the multipliers `K̂_{Q,d}` is `KQd_uniform_BV` (`P5/`), under the
support condition `SupportBlock`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Common

/-- For `s > 1` there is `r > 2` with `r' = r/(r-1) < s`. -/
theorem exists_exponent_gt {s : ℝ} (hs : 1 < s) : ∃ r : ℝ, 2 < r ∧ r / (r - 1) < s := by
  have hs1 : 0 < s - 1 := by linarith
  refine ⟨max 3 (s / (s - 1)) + 1, by linarith [le_max_left 3 (s / (s - 1))], ?_⟩
  have hr : s / (s - 1) < max 3 (s / (s - 1)) + 1 := by linarith [le_max_right 3 (s / (s - 1))]
  have h3 : 3 ≤ max 3 (s / (s - 1)) := le_max_left _ _
  rw [div_lt_iff₀ (by linarith)]
  have := (div_lt_iff₀ hs1).1 hr
  nlinarith

/-- Minkowski's inequality for the nested weighted sums of the Möbius expansion. -/
theorem eLpNorm_nested_sum_le {p : ℝ} (hp : 1 ≤ p) (B : Finset ℕ) (w : ℕ → ℝ≥0∞)
    (c : ℕ → ℝ≥0∞) (A : ℕ → ℤ → ℝ≥0∞) (M : ℝ≥0∞)
    (hA : ∀ q ∈ B, ∀ d ∈ q.divisors, eLpNorm (A d) (ENNReal.ofReal p) Measure.count ≤ M) :
    eLpNorm (fun x => ∑ q ∈ B, w q * ∑ d ∈ q.divisors, c d * A d x) (ENNReal.ofReal p)
        Measure.count ≤ (∑ q ∈ B, w q * ∑ d ∈ q.divisors, c d) * M := by
  have hp0 : 0 < p := by linarith
  refine (eLpNorm_count_finset_sum_le B (fun q x => w q * ∑ d ∈ q.divisors, c d * A d x) hp).trans
    ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun q hq => ?_
  rw [eLpNorm_count_const_mul _ _ hp0, mul_assoc]
  refine mul_le_mul_right ?_ _
  refine (eLpNorm_count_finset_sum_le _ (fun d x => c d * A d x) hp).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun d hd => ?_
  rw [eLpNorm_count_const_mul _ _ hp0]
  exact mul_le_mul_right (hA q hq d hd) _

/-- The `ℝ≥0∞` weight sum is the `ofReal` of the real one. -/
theorem enn_weight_sum (B : Finset ℕ) (a c : ℝ) (hc : 0 ≤ c) :
    ∑ q ∈ B, ENNReal.ofReal (1 / (Nat.totient q : ℝ)) *
        ∑ d ∈ q.divisors, ENNReal.ofReal (c * (d : ℝ) ^ a) =
      ENNReal.ofReal (c * ∑ q ∈ B, (1 / (Nat.totient q : ℝ)) *
        ∑ d ∈ q.divisors, (d : ℝ) ^ a) := by
  rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg (fun q _ => by positivity)]
  refine Finset.sum_congr rfl fun q _ => ?_
  have h1 : ∑ d ∈ q.divisors, ENNReal.ofReal (c * (d : ℝ) ^ a) =
      ENNReal.ofReal (c * ∑ d ∈ q.divisors, (d : ℝ) ^ a) := by
    rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg (fun d _ => by positivity)]
  rw [h1, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

/-- **The application of `c:disc`** (Source: main paper `l:red-var-l2`, L1694–L1706), variational
part: for `r > 2`, `s > r'` there is `C` with
`‖V^r(∑_m f(x - dm) K_{Q,d}(m) e(λ m) : λ)‖_{ℓ^s_x} ≤ C ‖f‖_{ℓ^s}` uniformly in `Q = 2^j` and
`1 ≤ d ≤ Q` (conditional on `hO`; `c:disc` and the uniform bounded variation of `K̂_{Q,d}`, Source:
main paper `s:red`, L1694–L1695). -/
theorem disc_application (hO : OplusVariationBound) (S : KQSetup) (hS : S.P.SupportBlock S.δ)
    {r s : ℝ} (hr : 2 < r) (hs : r / (r - 1) < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j d : ℕ), 1 ≤ d → d ≤ 2 ^ j → ∀ f : ℤ →₀ ℂ,
      eLpNorm (fun x : ℤ => rVariationOn r (Set.Ico 0 1)
          (fun lam => dilSum (S.KQdhat (2 ^ j) d) (d : ℤ) f x lam)) (ENNReal.ofReal s)
          Measure.count ≤
        ENNReal.ofReal C * eLpNorm (⇑f) (ENNReal.ofReal s) Measure.count := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := cdisc_of_oplus hO hr hs
  obtain ⟨Cb, hCb0, hCb⟩ := S.KQd_uniform_BV hS
  refine ⟨C₁ * Cb, mul_nonneg hC₁0 hCb0, fun j d hd hdQ f => ?_⟩
  obtain ⟨-, hvar, hsupp, -⟩ := hCb j d hd hdQ
  have hmeas : Measurable (S.KQdhat (2 ^ j) d) :=
    (S.measurable_KQhat _).comp (measurable_id.div_const _)
  have h := hC₁ (S.KQdhat (2 ^ j) d) Cb hCb0 hmeas (fun ξ h => hsupp (Function.mem_support.2 h))
    hvar d hd f (Set.Ico 0 1) le_rfl
  exact h

/-- **The application of `c:disc`, the supremum term** ("bounded in the same way"): for `s > 1`,
`‖sup_λ |∑_m f(x - dm) K_{Q,d}(m) e(λ m)|‖_{ℓ^s_x} ≤ C ‖f‖_{ℓ^s}` uniformly in `Q = 2^j` and
`1 ≤ d ≤ Q` (conditional on `hO`; `sup_modulated_of_oplus` with `r = r(s)`). -/
theorem sup_application (hO : OplusVariationBound) (S : KQSetup) (hS : S.P.SupportBlock S.δ)
    {s : ℝ} (hs : 1 < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j d : ℕ), 1 ≤ d → d ≤ 2 ^ j → ∀ f : ℤ →₀ ℂ,
      eLpNorm (fun x : ℤ => ⨆ lam ∈ Set.Ico (0 : ℝ) 1,
          ‖dilSum (S.KQdhat (2 ^ j) d) (d : ℤ) f x lam‖ₑ) (ENNReal.ofReal s) Measure.count ≤
        ENNReal.ofReal C * eLpNorm (⇑f) (ENNReal.ofReal s) Measure.count := by
  obtain ⟨r, hr, hrs⟩ := exists_exponent_gt hs
  obtain ⟨C₁, hC₁0, hC₁⟩ := sup_modulated_of_oplus hO hr hrs
  obtain ⟨Cb, hCb0, hCb⟩ := S.KQd_uniform_BV hS
  refine ⟨C₁ * Cb, mul_nonneg hC₁0 hCb0, fun j d hd hdQ f => ?_⟩
  obtain ⟨-, hvar, hsupp, -⟩ := hCb j d hd hdQ
  have hmeas : Measurable (S.KQdhat (2 ^ j) d) :=
    (S.measurable_KQhat _).comp (measurable_id.div_const _)
  have h := hC₁ (S.KQdhat (2 ^ j) d) Cb hCb0 hmeas (fun ξ h => hsupp (Function.mem_support.2 h))
    hvar d hd f (Set.Ico 0 1) le_rfl
  exact h

/-- **The crude `ℓ^s` bound by the Möbius sum** (Source: main paper `l:red-var-l2`, L1706–L1715),
first inequality: for `r > 2`, `s > r'`,
`‖V^{Q,r} f‖_{ℓ^s} ≤ C ∑_{Q/2 < q ≤ Q} φ(q)⁻¹ ∑_{d ∣ q} d^{1/r} ‖f‖_{ℓ^s}` for `Q = 2^j`, with `C`
depending on `s`, `r` only (conditional on `hO`). -/
theorem crude_s_bound_sum (hO : OplusVariationBound) (S : KQSetup) (hS : S.P.SupportBlock S.δ)
    {r s : ℝ} (hr : 2 < r) (hs : r / (r - 1) < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : ℕ) (f : ℤ →₀ ℂ),
      eLpNorm (S.VQr r (2 ^ j) (⇑f)) (ENNReal.ofReal s) Measure.count ≤
        ENNReal.ofReal (C * ∑ q ∈ Finset.Ioc (2 ^ j / 2) (2 ^ j),
          (1 / (Nat.totient q : ℝ)) * ∑ d ∈ q.divisors, (d : ℝ) ^ (1 / r)) *
          eLpNorm (⇑f) (ENNReal.ofReal s) Measure.count := by
  have hs1 : 1 ≤ s := by
    have : 1 ≤ r / (r - 1) := by rw [le_div_iff₀ (by linarith)]; linarith
    linarith
  obtain ⟨Cd, hCd0, hCd⟩ := disc_application hO S hS hr hs
  refine ⟨3 * Cd, by positivity, fun j f => ?_⟩
  have hpt : ∀ x : ℤ, S.VQr r (2 ^ j) (⇑f) x ≤ ∑ q ∈ Finset.Ioc (2 ^ j / 2) (2 ^ j),
      ENNReal.ofReal (1 / (Nat.totient q : ℝ)) * ∑ d ∈ q.divisors,
        ENNReal.ofReal (3 * (d : ℝ) ^ (1 / r)) * rVariationOn r (Set.Ico 0 1)
          (fun lam => dilSum (S.KQdhat (2 ^ j) d) (d : ℤ) f x lam) := fun x =>
    mobius_var_pointwise S (by linarith) (2 ^ j) f x
  refine (eLpNorm_count_mono_enn hpt _).trans ?_
  refine (eLpNorm_nested_sum_le hs1 (Finset.Ioc (2 ^ j / 2) (2 ^ j))
    (fun q => ENNReal.ofReal (1 / (Nat.totient q : ℝ)))
    (fun d => ENNReal.ofReal (3 * (d : ℝ) ^ (1 / r)))
    (fun d x => rVariationOn r (Set.Ico 0 1)
      (fun lam => dilSum (S.KQdhat (2 ^ j) d) (d : ℤ) f x lam))
    (ENNReal.ofReal Cd * eLpNorm (⇑f) (ENNReal.ofReal s) Measure.count) ?_).trans ?_
  · intro q hq d hd
    have hq' := Finset.mem_Ioc.1 hq
    exact hCd j d (Nat.pos_of_mem_divisors hd) ((Nat.divisor_le hd).trans hq'.2) f
  · rw [enn_weight_sum _ _ _ (by norm_num), ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    refine le_of_eq ?_
    congr 2
    ring

/-- **`e:crude-var-Q-bound`** (Source: main paper, L1592–L1597, L1706–L1715): for `r > 2`, `s > r'`
and `δ > 0` there is `C` with `‖V^{Q,r} f‖_{ℓ^s} ≤ C Q^{1/r+δ} ‖f‖_{ℓ^s}` for `Q = 2^j` (the paper's
`Q^{1/r+o(1)}`; conditional on `hO`). -/
theorem crude_var_Q_bound (hO : OplusVariationBound) (S : KQSetup) (hS : S.P.SupportBlock S.δ)
    {r s : ℝ} (hr : 2 < r) (hs : r / (r - 1) < s) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : ℕ) (f : ℤ →₀ ℂ),
      eLpNorm (S.VQr r (2 ^ j) (⇑f)) (ENNReal.ofReal s) Measure.count ≤
        ENNReal.ofReal (C * ((2 : ℝ) ^ j) ^ (1 / r + δ)) *
          eLpNorm (⇑f) (ENNReal.ofReal s) Measure.count := by
  obtain ⟨C₁, hC₁0, h₁⟩ := crude_s_bound_sum hO S hS hr hs
  have hr0 : 0 < r := by linarith
  obtain ⟨Cw, hCw0, hw⟩ := weight_sum_le (a := 1 / r) (by positivity) hδ
  refine ⟨C₁ * Cw, mul_nonneg hC₁0 hCw0, fun j f => (h₁ j f).trans ?_⟩
  refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
  have := hw (2 ^ j) Nat.one_le_two_pow
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hC₁0
  simpa using this

/-- **The crude bound for `C^Q`** (Source: main paper `l:red-var-l2`, L1729–L1731): for every
`s > 1` and `δ > 0` there is `C` with `‖C^Q f‖_{ℓ^s} ≤ C Q^δ ‖f‖_{ℓ^s}` for `Q = 2^j` (the paper's
`Q^{o(1)}`; conditional on `hO`; the auxiliary `r = r(s)` with `r' < s` is chosen inside). -/
theorem maximal_crude_bound (hO : OplusVariationBound) (S : KQSetup) (hS : S.P.SupportBlock S.δ)
    {s : ℝ} (hs : 1 < s) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : ℕ) (f : ℤ →₀ ℂ),
      eLpNorm (S.CQ (2 ^ j) (⇑f)) (ENNReal.ofReal s) Measure.count ≤
        ENNReal.ofReal (C * ((2 : ℝ) ^ j) ^ δ) *
          eLpNorm (⇑f) (ENNReal.ofReal s) Measure.count := by
  obtain ⟨Cd, hCd0, hCd⟩ := sup_application hO S hS hs
  obtain ⟨Cw, hCw0, hw⟩ := weight_sum_le (a := 0) le_rfl hδ
  refine ⟨Cd * Cw, mul_nonneg hCd0 hCw0, fun j f => ?_⟩
  have hpt : ∀ x : ℤ, S.CQ (2 ^ j) (⇑f) x ≤ ∑ q ∈ Finset.Ioc (2 ^ j / 2) (2 ^ j),
      ENNReal.ofReal (1 / (Nat.totient q : ℝ)) * ∑ d ∈ q.divisors,
        ENNReal.ofReal (1 * (d : ℝ) ^ (0 : ℝ)) *
          ⨆ lam ∈ Set.Ico (0 : ℝ) 1, ‖dilSum (S.KQdhat (2 ^ j) d) (d : ℤ) f x lam‖ₑ := by
    intro x
    refine (CQ_le_mobius S (2 ^ j) f x).trans (le_of_eq ?_)
    simp
  refine (eLpNorm_count_mono_enn hpt _).trans ?_
  refine (eLpNorm_nested_sum_le (by linarith) (Finset.Ioc (2 ^ j / 2) (2 ^ j))
    (fun q => ENNReal.ofReal (1 / (Nat.totient q : ℝ)))
    (fun d => ENNReal.ofReal (1 * (d : ℝ) ^ (0 : ℝ)))
    (fun d x => ⨆ lam ∈ Set.Ico (0 : ℝ) 1, ‖dilSum (S.KQdhat (2 ^ j) d) (d : ℤ) f x lam‖ₑ)
    (ENNReal.ofReal Cd * eLpNorm (⇑f) (ENNReal.ofReal s) Measure.count) ?_).trans ?_
  · intro q hq d hd
    have hq' := Finset.mem_Ioc.1 hq
    exact hCd j d (Nat.pos_of_mem_divisors hd) ((Nat.divisor_le hd).trans hq'.2) f
  · rw [enn_weight_sum _ _ _ (by norm_num), ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
    have := hw (2 ^ j) Nat.one_le_two_pow
    have h2 : (((2 ^ j : ℕ) : ℝ)) = (2 : ℝ) ^ j := by push_cast; rfl
    rw [h2, zero_add] at this
    calc 1 * (∑ q ∈ Finset.Ioc (2 ^ j / 2) (2 ^ j), (1 / (Nat.totient q : ℝ)) *
          ∑ d ∈ q.divisors, (d : ℝ) ^ (0 : ℝ)) * Cd
        ≤ 1 * (Cw * ((2 : ℝ) ^ j) ^ δ) * Cd := by gcongr
      _ = Cd * Cw * ((2 : ℝ) ^ j) ^ δ := by ring

end PrimeCarleson.Proof.Paper
