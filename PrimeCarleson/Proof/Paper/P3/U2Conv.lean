module

public import PrimeCarleson.Proof.Paper.P3.Basic
public import PrimeCarleson.Proof.Paper.P2.U2Fourier
public import PrimeCarleson.Proof.Paper.P2.Normalization

/-!
# The `U²` convolution estimate

Source: main paper `e:U2-conv`, L813–L821 (proof L822–L837): for finitely supported `F, G` at scale
`N`, `‖E_{n ∈ [N]} F(n) G(x - n)‖_{L²_x} ≲ ‖F‖_{U²} ‖G‖_{U²}` with the `U²` norms normalized at
scale `N`.

* `sum_norm_sq_convZ_le`: the unnormalized core (Plancherel and Cauchy-Schwarz, the paper's chain
  `‖F * G‖_{ℓ²}² = ∫ |F̂|²|Ĝ|² ≤ (∫ |F̂|⁴)^{1/2} (∫ |Ĝ|⁴)^{1/2} = ‖F‖_{U²(ℤ)}² ‖G‖_{U²(ℤ)}²`,
  `e:U2-ell4`): `‖F * G‖_{ℓ²}² ≤ ‖F‖_{U²}² ‖G‖_{U²}²`;
* `u2_conv`: the normalized form for `F` supported in `[N]` and `G` supported in `[-N, 2N]`, the
  support conditions of the use at L839-L855 (`F = Δ_h w`, `G = Δ_{-h} f`), with the `L²_x` norm
  over `[-N, 2N]`, the `U²` norms over `[N]` and `[-N, 2N]` (normalized as in L702–L707):
  `‖E_{n ∈ [N]} F(n) G(x-n)‖_{L²_x([-N,2N])}² ≤
  18 ‖F‖_{U²([N])}² ‖G‖_{U²([-N,2N])}²`. The normalizing constants are controlled by
  `gowersNorm_indicator_pow_le` (`‖1_I‖_{U²}⁴ ≤ 9 |I|³`, Source: main paper `s:Prelim`, L706).
-/

@[expose] public noncomputable section

open scoped ComplexConjugate

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Goal0

/-- Cauchy-Schwarz for continuous nonnegative functions on `[0, 1]`:
`(∫ a b)² ≤ (∫ a²)(∫ b²)` (the discriminant of `t ↦ ∫ (a - t b)²`). -/
theorem integral_mul_sq_le_interval {a b : ℝ → ℝ} (ha : Continuous a) (hb : Continuous b) :
    (∫ ξ in (0 : ℝ)..1, a ξ * b ξ) ^ 2 ≤
      (∫ ξ in (0 : ℝ)..1, a ξ ^ 2) * ∫ ξ in (0 : ℝ)..1, b ξ ^ 2 := by
  have hi : ∀ g : ℝ → ℝ, Continuous g → IntervalIntegrable g MeasureTheory.volume 0 1 :=
    fun g hg => hg.intervalIntegrable _ _
  have hexp : ∀ t : ℝ, ∫ ξ in (0 : ℝ)..1, (a ξ - t * b ξ) ^ 2 =
      (∫ ξ in (0 : ℝ)..1, a ξ ^ 2) - 2 * t * (∫ ξ in (0 : ℝ)..1, a ξ * b ξ) +
        t ^ 2 * ∫ ξ in (0 : ℝ)..1, b ξ ^ 2 := by
    intro t
    have e1 : (fun ξ => (a ξ - t * b ξ) ^ 2) =
        fun ξ => (a ξ ^ 2 - (2 * t) * (a ξ * b ξ)) + t ^ 2 * b ξ ^ 2 := by
      funext ξ
      ring
    rw [e1, intervalIntegral.integral_add ((hi _ (by fun_prop)))
      ((hi _ (by fun_prop))), intervalIntegral.integral_sub (hi _ (by fun_prop))
      ((hi _ (by fun_prop))), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  have hquad : ∀ t : ℝ, 0 ≤ (∫ ξ in (0 : ℝ)..1, b ξ ^ 2) * (t * t) +
      (-2 * ∫ ξ in (0 : ℝ)..1, a ξ * b ξ) * t + ∫ ξ in (0 : ℝ)..1, a ξ ^ 2 := by
    intro t
    have h0 : 0 ≤ ∫ ξ in (0 : ℝ)..1, (a ξ - t * b ξ) ^ 2 :=
      intervalIntegral.integral_nonneg zero_le_one fun ξ _ => sq_nonneg _
    rw [hexp] at h0
    nlinarith [h0]
  have hd := discrim_le_zero hquad
  unfold discrim at hd
  nlinarith [hd]

/-- **The `U²` convolution estimate, unnormalized** (Source: main paper `e:U2-conv`, L813–L821,
proof L822–L837):
`‖F * G‖_{ℓ²(ℤ)}² ≤ ‖F‖_{U²(ℤ)}² ‖G‖_{U²(ℤ)}²` for finitely supported `F, G`
(Plancherel, Cauchy-Schwarz in `ξ` and `e:U2-ell4`). -/
theorem sum_norm_sq_convZ_le (P Q : ℤ →₀ ℂ) :
    ∑ n ∈ (Common.convZ P Q).support, ‖Common.convZ P Q n‖ ^ 2 ≤
      gowersNorm 2 P ^ 2 * gowersNorm 2 Q ^ 2 := by
  have hP := gowersNorm_two_pow_four_eq_integral P
  have hQ := gowersNorm_two_pow_four_eq_integral Q
  set a : ℝ → ℝ := fun ξ => ‖Common.fourierZ P ξ‖ ^ 2 with ha
  set b : ℝ → ℝ := fun ξ => ‖Common.fourierZ Q ξ‖ ^ 2 with hb
  have hac : Continuous a := (Common.continuous_fourierZ P).norm.pow 2
  have hbc : Continuous b := (Common.continuous_fourierZ Q).norm.pow 2
  have hZ : ∑ n ∈ (Common.convZ P Q).support, ‖Common.convZ P Q n‖ ^ 2 =
      ∫ ξ in (0 : ℝ)..1, a ξ * b ξ := by
    rw [Common.sum_norm_sq_eq_integral]
    refine intervalIntegral.integral_congr fun ξ _ => ?_
    simp only [Common.fourierZ_convZ, norm_mul, ha, hb]
    ring
  have hX : ∫ ξ in (0 : ℝ)..1, a ξ ^ 2 = gowersNorm 2 P ^ 4 := by
    rw [hP]
    refine intervalIntegral.integral_congr fun ξ _ => ?_
    simp only [ha]
    ring
  have hY : ∫ ξ in (0 : ℝ)..1, b ξ ^ 2 = gowersNorm 2 Q ^ 4 := by
    rw [hQ]
    refine intervalIntegral.integral_congr fun ξ _ => ?_
    simp only [hb]
    ring
  have hcs := integral_mul_sq_le_interval hac hbc
  rw [hX, hY, ← hZ] at hcs
  have h0 : 0 ≤ ∑ n ∈ (Common.convZ P Q).support, ‖Common.convZ P Q n‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => by positivity
  have hn1 : 0 ≤ gowersNorm 2 P := gowersNorm_nonneg 2 P
  have hn2 : 0 ≤ gowersNorm 2 Q := gowersNorm_nonneg 2 Q
  refine le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (by positivity) ?_
  calc (∑ n ∈ (Common.convZ P Q).support, ‖Common.convZ P Q n‖ ^ 2) ^ 2
      ≤ gowersNorm 2 P ^ 4 * gowersNorm 2 Q ^ 4 := hcs
    _ = (gowersNorm 2 P ^ 2 * gowersNorm 2 Q ^ 2) ^ 2 := by ring

/-- For `g` supported in `I`, `restrictFinset I g` is `g`. -/
theorem restrictFinset_eq_self_of_support (I : Finset ℤ) (g : ℤ → ℂ)
    (hg : ∀ y, y ∉ I → g y = 0) (y : ℤ) : restrictFinset I g y = g y := by
  rw [restrictFinset_apply]
  by_cases hy : y ∈ I
  · simp [hy]
  · simp [hy, hg y hy]

/-- The `[N]`-average of `F(n) G(x - n)` is `N⁻¹ (F * G)(x)` for `F` supported in `[N]`. -/
theorem expect_bracket_mul_eq_convZ (N : ℕ+) (F G : ℤ → ℂ) (hF : ∀ n, n ∉ bracket N → F n = 0)
    (hG : ∀ y, y ∉ maxWindow N → G y = 0) (x : ℤ) :
    expect (bracket N) (fun n => F n * G (x - n)) =
      (N : ℂ)⁻¹ *
        Common.convZ (restrictFinset (bracket N) F) (restrictFinset (maxWindow N) G) x := by
  have hsub : (restrictFinset (bracket N) F).support ⊆ bracket N := by
    intro k hk
    by_contra hkn
    exact (Finsupp.mem_support_iff.1 hk) (by simp [restrictFinset_apply, hkn])
  rw [Common.convZ_apply, Finsupp.sum, Finset.sum_subset hsub (fun k hk hk' => by
    rw [Finsupp.notMem_support_iff.1 hk', zero_mul])]
  simp only [expect, card_bracket]
  congr 1
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [restrictFinset_eq_self_of_support _ F hF, restrictFinset_eq_self_of_support _ G hG]

/-- The `U²`-norm of a function supported in `I` is its normalized norm times `‖1_I‖_{U²(ℤ)}`. -/
theorem gowersNorm_restrictFinset_eq (s : ℕ+) {I : Finset ℤ} (hI : I.Nonempty) (g : ℤ → ℂ) :
    gowersNorm s (restrictFinset I g) =
      gowersNormOn s I g * gowersNorm s (restrictFinset I 1) :=
  (gowersNormOn_mul_norm_one s hI g).symm

/-- `‖1_{[N]}‖_{U²(ℤ)}⁴ ≤ 9 N³`. -/
theorem gowersNorm_two_bracket_pow_le (N : ℕ+) :
    gowersNorm 2 (restrictFinset (bracket N) 1) ^ 4 ≤ 9 * ((N : ℕ) : ℝ) ^ 3 := by
  have h := gowersNorm_indicator_pow_le 2 1 (N : ℕ)
  rw [← bracket_eq_Icc] at h
  calc _ ≤ 3 ^ 2 * ((N : ℕ) : ℝ) ^ 3 := by simpa using h
    _ = _ := by norm_num

/-- `‖1_{[-N,2N]}‖_{U²(ℤ)}⁴ ≤ 9 (3N+1)³`. -/
theorem gowersNorm_two_maxWindow_pow_le (N : ℕ+) :
    gowersNorm 2 (restrictFinset (maxWindow N) 1) ^ 4 ≤ 9 * (3 * ((N : ℕ) : ℝ) + 1) ^ 3 := by
  have h := gowersNorm_indicator_pow_le 2 (-(N : ℤ)) (3 * (N : ℕ) + 1)
  rw [← maxWindow_eq_Icc] at h
  calc _ ≤ 3 ^ 2 * (3 * ((N : ℕ) : ℝ) + 1) ^ 3 := by simpa using h
    _ = _ := by norm_num

/-- **`e:U2-conv`, normalized form** (Source: main paper `e:U2-conv`, L813–L837): for `F` supported
in
`[N]` and `G` supported in `[-N, 2N]`,
`‖E_{n ∈ [N]} F(n) G(x-n)‖_{L²_x([-N,2N])}² ≤ 18 ‖F‖_{U²([N])}² ‖G‖_{U²([-N,2N])}²`. -/
theorem u2_conv (N : ℕ+) (F G : ℤ → ℂ) (hF : ∀ n, n ∉ bracket N → F n = 0)
    (hG : ∀ y, y ∉ maxWindow N → G y = 0) :
    lpNormOn 2 (maxWindow N) (fun x => expect (bracket N) (fun n => F n * G (x - n))) ^ 2 ≤
      18 * gowersNormOn 2 (bracket N) F ^ 2 * gowersNormOn 2 (maxWindow N) G ^ 2 := by
  classical
  set FF := restrictFinset (bracket N) F with hFF
  set GG := restrictFinset (maxWindow N) G with hGG
  set u₁ := gowersNorm 2 (restrictFinset (bracket N) 1) with hu₁
  set u₂ := gowersNorm 2 (restrictFinset (maxWindow N) 1) with hu₂
  set n₁ := gowersNormOn 2 (bracket N) F with hn₁
  set n₂ := gowersNormOn 2 (maxWindow N) G with hn₂
  have hNr : (1 : ℝ) ≤ ((N : ℕ) : ℝ) := by exact_mod_cast N.pos
  set Nr : ℝ := ((N : ℕ) : ℝ) with hNrdef
  have hN0 : (0 : ℝ) < Nr := by linarith
  set L : ℝ := 3 * Nr + 1 with hL
  have hL0 : 0 < L := by rw [hL]; linarith
  have hXc : ((maxWindow N).card : ℝ) = L := by
    rw [card_maxWindow]
    push_cast
    rfl
  -- the convolution identity
  have hconv : ∀ x, ‖expect (bracket N) (fun n => F n * G (x - n))‖ =
      Nr⁻¹ * ‖Common.convZ FF GG x‖ := fun x => by
    rw [expect_bracket_mul_eq_convZ N F G hF hG x, norm_mul, norm_inv, Complex.norm_natCast]
  -- the sum over the window
  have hS : lpNormOn 2 (maxWindow N) (fun x => expect (bracket N) (fun n => F n * G (x - n))) ^ 2
      ≤ (L * Nr ^ 2)⁻¹ * (gowersNorm 2 FF ^ 2 * gowersNorm 2 GG ^ 2) := by
    rw [lpNormOn_two_sq, hXc]
    simp_rw [hconv]
    have h1 : ∑ x ∈ maxWindow N, (Nr⁻¹ * ‖Common.convZ FF GG x‖) ^ 2 ≤
        Nr⁻¹ ^ 2 * ∑ n ∈ (Common.convZ FF GG).support, ‖Common.convZ FF GG n‖ ^ 2 := by
      simp_rw [mul_pow]
      rw [← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have hc : ∑ x ∈ maxWindow N, ‖Common.convZ FF GG x‖ ^ 2 =
          ∑ x ∈ maxWindow N ∩ (Common.convZ FF GG).support, ‖Common.convZ FF GG x‖ ^ 2 := by
        symm
        refine Finset.sum_subset Finset.inter_subset_left fun x hx hx' => ?_
        have h0 : Common.convZ FF GG x = 0 := by
          by_contra h
          exact hx' (Finset.mem_inter.2 ⟨hx, Finsupp.mem_support_iff.2 h⟩)
        simp [h0]
      rw [hc]
      exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
        fun _ _ _ => by positivity
    have h2 := sum_norm_sq_convZ_le FF GG
    calc L⁻¹ * ∑ x ∈ maxWindow N, (Nr⁻¹ * ‖Common.convZ FF GG x‖) ^ 2
        ≤ L⁻¹ * (Nr⁻¹ ^ 2 * (gowersNorm 2 FF ^ 2 * gowersNorm 2 GG ^ 2)) :=
          mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity)))
            (by positivity)
      _ = (L * Nr ^ 2)⁻¹ * (gowersNorm 2 FF ^ 2 * gowersNorm 2 GG ^ 2) := by
          field_simp
  -- normalization
  have hI₁ : (bracket N).Nonempty := bracket_nonempty N
  have hI₂ : (maxWindow N).Nonempty := maxWindow_nonempty N
  have hFFn : gowersNorm 2 FF = n₁ * u₁ := gowersNorm_restrictFinset_eq 2 hI₁ F
  have hGGn : gowersNorm 2 GG = n₂ * u₂ := gowersNorm_restrictFinset_eq 2 hI₂ G
  have hu1b : u₁ ^ 4 ≤ 9 * Nr ^ 3 := gowersNorm_two_bracket_pow_le N
  have hu2b : u₂ ^ 4 ≤ 9 * L ^ 3 := gowersNorm_two_maxWindow_pow_le N
  have hn1 : 0 ≤ n₁ := gowersNormOn_nonneg _ _ _
  have hn2 : 0 ≤ n₂ := gowersNormOn_nonneg _ _ _
  have hu1 : 0 ≤ u₁ := gowersNorm_nonneg _ _
  have hu2 : 0 ≤ u₂ := gowersNorm_nonneg _ _
  set S := lpNormOn 2 (maxWindow N) (fun x => expect (bracket N) (fun n => F n * G (x - n)))
    with hSdef
  have hS0 : 0 ≤ S := lpNormOn_nonneg _ _ _
  rw [hFFn, hGGn] at hS
  refine le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (by positivity) ?_
  have hS2 : (S ^ 2) ^ 2 ≤ ((L * Nr ^ 2)⁻¹ * ((n₁ * u₁) ^ 2 * (n₂ * u₂) ^ 2)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hS 2
  have hprod : u₁ ^ 4 * u₂ ^ 4 ≤ 81 * Nr ^ 3 * L ^ 3 := by
    calc u₁ ^ 4 * u₂ ^ 4 ≤ (9 * Nr ^ 3) * (9 * L ^ 3) :=
          mul_le_mul hu1b hu2b (by positivity) (by positivity)
      _ = 81 * Nr ^ 3 * L ^ 3 := by ring
  have hLN : L ≤ 4 * Nr := by rw [hL]; linarith
  calc (S ^ 2) ^ 2 ≤ ((L * Nr ^ 2)⁻¹ * ((n₁ * u₁) ^ 2 * (n₂ * u₂) ^ 2)) ^ 2 := hS2
    _ = (L * Nr ^ 2)⁻¹ ^ 2 * (n₁ ^ 4 * n₂ ^ 4) * (u₁ ^ 4 * u₂ ^ 4) := by ring
    _ ≤ (L * Nr ^ 2)⁻¹ ^ 2 * (n₁ ^ 4 * n₂ ^ 4) * (81 * Nr ^ 3 * L ^ 3) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = 81 * (L / Nr) * (n₁ ^ 4 * n₂ ^ 4) := by field_simp
    _ ≤ 81 * 4 * (n₁ ^ 4 * n₂ ^ 4) := by
        have : L / Nr ≤ 4 := by rw [div_le_iff₀ hN0]; linarith
        have h4 : 0 ≤ n₁ ^ 4 * n₂ ^ 4 := by positivity
        nlinarith [mul_le_mul_of_nonneg_right this h4]
    _ = (18 * n₁ ^ 2 * n₂ ^ 2) ^ 2 := by ring

end PrimeCarleson.Proof.Paper
