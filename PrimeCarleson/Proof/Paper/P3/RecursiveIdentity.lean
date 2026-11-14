module

public import PrimeCarleson.Proof.Paper.P3.VanDerCorput
public import PrimeCarleson.Proof.Paper.P3.U2Conv
public import PrimeCarleson.Proof.Paper.P2.Foliate

/-!
# From the `U²` convolution estimate to the `U³` norms

Source: main paper `e:U3maxmod`, L839–L884 (end of the proof of Lemma `e:U3maxmod`). Paper steps
proved here, all for `w` supported in `[N]`, `f` supported in `[-N, 2N]` and an arbitrary selector
`θ : ℤ → ℝ`:

* application of the `U²` convolution estimate (L839–L863; `apply_U2_conv`,
  `four_pow_le_expect_U2_sq`): with `F = Δ_h w` and
  `G = Δ_{-h} f`, `‖E_n Δ_h w(n) Δ_{-h} f(x-n)‖_{L²_x([-N,2N])}² ≤
  18 ‖Δ_h w‖_{U²([N])}² ‖Δ_{-h} f‖_{U²([-N,2N])}²` and hence
  `‖A_θ f‖_{L⁴([-N,2N])}⁴ ≤ 162 E_{|h| ≤ N} ‖Δ_h w‖_{U²([N])}² ‖Δ_{-h} f‖_{U²([-N,2N])}²`;
* Cauchy–Schwarz in `h` (L864–L876; `four_pow_le_sqrt_mul_sqrt`):
  `‖A_θ f‖⁴ ≤ 162 (E_h ‖Δ_h w‖_{U²([N])}⁴)^{1/2} (E_h ‖Δ_{-h} f‖_{U²([-N,2N])}⁴)^{1/2}`;
* the recursive identity (L877–L883; `expect_gowersNormOn_two_conjDiff_pow_le_w`,
  `expect_gowersNormOn_two_conjDiff_pow_le_f`, `four_pow_le_U3`): the recursive identity `e:foliate`
  for `s = 2` (`‖g‖_{U³(ℤ)}⁸ = ∑_h ‖Δ_h g‖_{U²(ℤ)}⁴`, with the passage from the full sum over `h` to
  `|h| ≤ N` by positivity) and the normalizing constants of `P2/Normalization.lean` (Source: main
  paper `s:Prelim`, L706; `‖1_I‖_{U³}⁸ ≤ 27 |I|⁴`, `‖1_I‖_{U²}⁴ ≥ |I|³/32`) give
  `E_{|h| ≤ N} ‖Δ_h w‖_{U²([N])}⁴ ≤ 432 ‖w‖_{U³([N])}⁸`,
  `E_{|h| ≤ N} ‖Δ_{-h} f‖_{U²([-N,2N])}⁴ ≤ 1296 ‖f‖_{U³([-N,2N])}⁸`, hence
  `‖A_θ f‖_{L⁴([-N,2N])}⁴ ≤ 122472 ‖w‖_{U³([N])}⁴ ‖f‖_{U³([-N,2N])}⁴`.
-/

@[expose] public noncomputable section

open scoped ComplexConjugate

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Goal0

/-- The cardinality of the symmetric range `{-N, …, N}` is `2N + 1`. -/
theorem card_Icc_neg_self_pnat (N : ℕ+) :
    ((Finset.Icc (-(N : ℤ)) (N : ℤ)).card : ℝ) = 2 * ((N : ℕ) : ℝ) + 1 := by
  have : ((N : ℤ) + 1 - -(N : ℤ)).toNat = 2 * (N : ℕ) + 1 := by omega
  rw [Int.card_Icc, this]
  push_cast
  ring

/-- `Δ_h g` of a function supported in `I`, restricted to `I`, is the one-step finitely supported
difference of `g 1_I`. -/
theorem restrictFinset_conjDiff (I : Finset ℤ) (g : ℤ → ℂ) (hg : ∀ y, y ∉ I → g y = 0) (k : ℤ) :
    restrictFinset I (conjDiff k g) =
      multDiffFinsupp 1 (fun _ => k) (restrictFinset I g) := by
  ext y
  rw [multDiffFinsupp_one_apply, restrictFinset_apply, restrictFinset_apply,
    restrictFinset_apply, conjDiff_apply]
  by_cases hy : y ∈ I
  · by_cases hy' : y + k ∈ I
    · simp [hy, hy']
    · simp [hy, hy', hg _ hy']
  · simp [hy]

/-- `Δ_h g` of a function supported in `I` is supported in `I`. -/
theorem conjDiff_eq_zero_of_notMem (I : Finset ℤ) (g : ℤ → ℂ) (hg : ∀ y, y ∉ I → g y = 0)
    (k : ℤ) (y : ℤ) (hy : y ∉ I) : conjDiff k g y = 0 := by
  rw [conjDiff_apply, hg y hy, zero_mul]

/-- **The recursive identity `e:foliate` for `s = 2`, normalized**: for `I = [a, a + L - 1]`
(`L ≥ 1`), `g` supported in `I` and any set `H ⊆ [-L, L]` of shifts,
`∑_{k ∈ H} ‖Δ_k g‖_{U²(I)}⁴ ≤ 864 L ‖g‖_{U³(I)}⁸`. -/
theorem sum_gowersNormOn_two_conjDiff_le (a : ℤ) (L : ℕ) (hL : 1 ≤ L) (g : ℤ → ℂ)
    (hg : ∀ y, y ∉ Finset.Icc a (a + (L : ℤ) - 1) → g y = 0) (H : Finset ℤ)
    (hH : H ⊆ Finset.Icc (-(L : ℤ)) L) :
    ∑ k ∈ H, gowersNormOn 2 (Finset.Icc a (a + (L : ℤ) - 1)) (conjDiff k g) ^ 4 ≤
      864 * (L : ℝ) * gowersNormOn 3 (Finset.Icc a (a + (L : ℤ) - 1)) g ^ 8 := by
  classical
  set I : Finset ℤ := Finset.Icc a (a + (L : ℤ) - 1) with hI
  have hIne : I.Nonempty := ⟨a, Finset.mem_Icc.2 ⟨le_rfl, by omega⟩⟩
  set FF := restrictFinset I g with hFF
  have hFFI : ∀ x, FF x ≠ 0 → x ∈ I := fun x hx => by
    by_contra h
    exact hx (by simp [hFF, restrictFinset_apply, h])
  have hB : ∀ x y, FF x ≠ 0 → FF y ≠ 0 → y - x ∈ Finset.Icc (-(L : ℤ)) L := by
    intro x y hx hy
    have h1 := Finset.mem_Icc.1 (hFFI x hx)
    have h2 := Finset.mem_Icc.1 (hFFI y hy)
    exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
  have hfol := gowersNorm_three_pow_eight_eq_sum FF _ hB
  set u₂ := gowersNorm 2 (restrictFinset I 1) with hu₂
  set u₃ := gowersNorm 3 (restrictFinset I 1) with hu₃
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hu₂b : (L : ℝ) ^ 3 ≤ 32 * u₂ ^ 4 := by
    have h := pow_le_gowersNorm_indicator_pow 2 a L
    norm_num at h
    linarith
  have hu₃b : u₃ ^ 8 ≤ 27 * (L : ℝ) ^ 4 := by
    have h := gowersNorm_indicator_pow_le 3 a L
    norm_num at h
    linarith
  have hu₂pos : 0 < u₂ ^ 4 := by
    have : 0 < (L : ℝ) ^ 3 := by positivity
    linarith
  have hterm : ∀ k, gowersNormOn 2 I (conjDiff k g) ^ 4 =
      gowersNorm 2 (multDiffFinsupp 1 (fun _ => k) FF) ^ 4 / u₂ ^ 4 := by
    intro k
    rw [gowersNormOn, ← restrictFinset_conjDiff I g hg k, div_pow]
  have hsum : ∑ k ∈ H, gowersNormOn 2 I (conjDiff k g) ^ 4 ≤
      gowersNorm 3 FF ^ 8 / u₂ ^ 4 := by
    simp_rw [hterm]
    rw [← Finset.sum_div, hfol]
    exact div_le_div_of_nonneg_right (Finset.sum_le_sum_of_subset_of_nonneg hH
      fun _ _ _ => by positivity) hu₂pos.le
  have hn3 : gowersNorm 3 FF = gowersNormOn 3 I g * u₃ := (gowersNormOn_mul_norm_one 3 hIne g).symm
  refine hsum.trans ?_
  rw [hn3, mul_pow, div_le_iff₀ hu₂pos]
  have hn3nn : 0 ≤ gowersNormOn 3 I g ^ 8 := by positivity
  calc gowersNormOn 3 I g ^ 8 * u₃ ^ 8 ≤ gowersNormOn 3 I g ^ 8 * (27 * (L : ℝ) ^ 4) :=
        mul_le_mul_of_nonneg_left hu₃b hn3nn
    _ ≤ gowersNormOn 3 I g ^ 8 * (864 * (L : ℝ) * u₂ ^ 4) := by
        refine mul_le_mul_of_nonneg_left ?_ hn3nn
        nlinarith [mul_le_mul_of_nonneg_left hu₂b hLr.le]
    _ = 864 * (L : ℝ) * gowersNormOn 3 I g ^ 8 * u₂ ^ 4 := by ring

/-- The sum over `|h| ≤ N` of `‖Δ_h w‖_{U²([N])}⁴` for `w` supported in `[N]`:
`≤ 864 N ‖w‖_{U³([N])}⁸`. -/
theorem sum_gowersNormOn_two_conjDiff_le_w (N : ℕ+) (w : ℤ → ℂ)
    (hw : ∀ n, n ∉ bracket N → w n = 0) :
    ∑ h ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), gowersNormOn 2 (bracket N) (conjDiff h w) ^ 4 ≤
      864 * ((N : ℕ) : ℝ) * gowersNormOn 3 (bracket N) w ^ 8 := by
  rw [bracket_eq_Icc] at hw ⊢
  exact sum_gowersNormOn_two_conjDiff_le 1 (N : ℕ) N.pos w hw _ (fun h hh => by simpa using hh)

/-- The sum over `|h| ≤ N` of `‖Δ_{-h} f‖_{U²([-N,2N])}⁴` for `f` supported in `[-N, 2N]`:
`≤ 864 (3N+1) ‖f‖_{U³([-N,2N])}⁸`. -/
theorem sum_gowersNormOn_two_conjDiff_le_f (N : ℕ+) (f : ℤ → ℂ)
    (hf : ∀ y, y ∉ maxWindow N → f y = 0) :
    ∑ h ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), gowersNormOn 2 (maxWindow N) (conjDiff (-h) f) ^ 4 ≤
      864 * (3 * ((N : ℕ) : ℝ) + 1) * gowersNormOn 3 (maxWindow N) f ^ 8 := by
  have hf' := hf
  rw [maxWindow_eq_Icc] at hf' ⊢
  have key := sum_gowersNormOn_two_conjDiff_le (-(N : ℤ)) (3 * (N : ℕ) + 1) (by omega) f hf'
    (Finset.Icc (-(N : ℤ)) (N : ℤ)) (fun h hh => by
      simp only [Finset.mem_Icc] at hh ⊢
      push_cast
      omega)
  have hre : ∑ h ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      gowersNormOn 2 (Finset.Icc (-(N : ℤ)) (-(N : ℤ) + ((3 * (N : ℕ) + 1 : ℕ) : ℤ) - 1))
        (conjDiff (-h) f) ^ 4 =
      ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      gowersNormOn 2 (Finset.Icc (-(N : ℤ)) (-(N : ℤ) + ((3 * (N : ℕ) + 1 : ℕ) : ℤ) - 1))
        (conjDiff k f) ^ 4 := by
    refine Finset.sum_nbij' (fun h => -h) (fun k => -k) ?_ ?_ ?_ ?_ ?_
    · intro h hh
      simp only [Finset.mem_Icc] at hh ⊢
      omega
    · intro h hh
      simp only [Finset.mem_Icc] at hh ⊢
      omega
    · intro h _
      simp
    · intro h _
      simp
    · intro h _
      simp
  rw [hre]
  simpa using key

/-- The expectation over `|h| ≤ N` of `‖Δ_h w‖_{U²([N])}⁴` is at most `432 ‖w‖_{U³([N])}⁸`
(the passage from the full `h`-sum to `|h| ≤ N` and the normalizing constants). -/
theorem expect_gowersNormOn_two_conjDiff_pow_le_w (N : ℕ+) (w : ℤ → ℂ)
    (hw : ∀ n, n ∉ bracket N → w n = 0) :
    (Finset.Icc (-(N : ℤ)) (N : ℤ)).expect
        (fun h => gowersNormOn 2 (bracket N) (conjDiff h w) ^ 4) ≤
      432 * gowersNormOn 3 (bracket N) w ^ 8 := by
  have hN : (1 : ℝ) ≤ ((N : ℕ) : ℝ) := by exact_mod_cast N.pos
  rw [Finset.expect_eq_sum_div_card, card_Icc_neg_self_pnat, div_le_iff₀ (by linarith)]
  refine (sum_gowersNormOn_two_conjDiff_le_w N w hw).trans ?_
  have : 0 ≤ gowersNormOn 3 (bracket N) w ^ 8 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right (show (0 : ℝ) ≤ 432 by norm_num) this]

/-- The expectation over `|h| ≤ N` of `‖Δ_{-h} f‖_{U²([-N,2N])}⁴` is at most
`1296 ‖f‖_{U³([-N,2N])}⁸`. -/
theorem expect_gowersNormOn_two_conjDiff_pow_le_f (N : ℕ+) (f : ℤ → ℂ)
    (hf : ∀ y, y ∉ maxWindow N → f y = 0) :
    (Finset.Icc (-(N : ℤ)) (N : ℤ)).expect
        (fun h => gowersNormOn 2 (maxWindow N) (conjDiff (-h) f) ^ 4) ≤
      1296 * gowersNormOn 3 (maxWindow N) f ^ 8 := by
  have hN : (1 : ℝ) ≤ ((N : ℕ) : ℝ) := by exact_mod_cast N.pos
  rw [Finset.expect_eq_sum_div_card, card_Icc_neg_self_pnat, div_le_iff₀ (by linarith)]
  refine (sum_gowersNormOn_two_conjDiff_le_f N f hf).trans ?_
  have : 0 ≤ gowersNormOn 3 (maxWindow N) f ^ 8 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right (show (0 : ℝ) ≤ 432 by norm_num) this]

/-- **Application of the `U²` convolution estimate, first part** (Source: main paper `e:U3maxmod`,
L839–L855): `U²`-convolution with `F = Δ_h w`, `G = Δ_{-h} f`. -/
theorem apply_U2_conv (N : ℕ+) (w f : ℤ → ℂ) (hw : ∀ n, n ∉ bracket N → w n = 0)
    (hf : ∀ y, y ∉ maxWindow N → f y = 0) (h : ℤ) :
    lpNormOn 2 (maxWindow N) (fun x =>
        expect (bracket N) (fun n => conjDiff h w n * conjDiff (-h) f (x - n))) ^ 2 ≤
      18 * gowersNormOn 2 (bracket N) (conjDiff h w) ^ 2 *
        gowersNormOn 2 (maxWindow N) (conjDiff (-h) f) ^ 2 :=
  u2_conv N (conjDiff h w) (conjDiff (-h) f)
    (fun n hn => conjDiff_eq_zero_of_notMem (bracket N) w hw h n hn)
    (fun y hy => conjDiff_eq_zero_of_notMem (maxWindow N) f hf (-h) y hy)

/-- **Application of the `U²` convolution estimate, second part** (Source: main paper `e:U3maxmod`,
L856–L863): substituting into `e:xh-average`,
`‖A_θ f‖_{L⁴([-N,2N])}⁴ ≤ 162 E_{|h| ≤ N} ‖Δ_h w‖_{U²([N])}² ‖Δ_{-h} f‖_{U²([-N,2N])}²`. -/
theorem four_pow_le_expect_U2_sq (N : ℕ+) (w f : ℤ → ℂ) (hw : ∀ n, n ∉ bracket N → w n = 0)
    (hf : ∀ y, y ∉ maxWindow N → f y = 0) (θ : ℤ → ℝ) :
    lpNormOn 4 (maxWindow N) (fun x => modAverage N w f (θ x) x) ^ 4 ≤
      162 * (Finset.Icc (-(N : ℤ)) (N : ℤ)).expect (fun h =>
        gowersNormOn 2 (bracket N) (conjDiff h w) ^ 2 *
          gowersNormOn 2 (maxWindow N) (conjDiff (-h) f) ^ 2) := by
  refine (xh_average N w f hw θ).trans ?_
  have hmono : (Finset.Icc (-(N : ℤ)) (N : ℤ)).expect (fun h =>
      lpNormOn 2 (maxWindow N) (fun x =>
        expect (bracket N) (fun n => conjDiff h w n * conjDiff (-h) f (x - n))) ^ 2) ≤
      (Finset.Icc (-(N : ℤ)) (N : ℤ)).expect (fun h => 18 * (
        gowersNormOn 2 (bracket N) (conjDiff h w) ^ 2 *
          gowersNormOn 2 (maxWindow N) (conjDiff (-h) f) ^ 2)) :=
    Finset.expect_le_expect fun h _ => by
      have := apply_U2_conv N w f hw hf h
      linarith
  rw [← Finset.mul_expect] at hmono
  linarith

/-- Cauchy-Schwarz for expectations: `E(u v) ≤ (E u²)^{1/2} (E v²)^{1/2}`. -/
theorem expect_mul_le_sqrt_mul_sqrt (B : Finset ℤ) (u v : ℤ → ℝ) :
    B.expect (fun h => u h * v h) ≤
      Real.sqrt (B.expect fun h => u h ^ 2) * Real.sqrt (B.expect fun h => v h ^ 2) := by
  rcases B.eq_empty_or_nonempty with rfl | hB
  · simp
  have hc : (0 : ℝ) < B.card := by exact_mod_cast hB.card_pos
  rw [← Real.sqrt_mul (Finset.expect_nonneg fun h _ => by positivity)]
  refine Real.le_sqrt_of_sq_le ?_
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq B u v
  simp only [Finset.expect_eq_sum_div_card]
  rw [div_pow, div_mul_div_comm, ← sq]
  exact div_le_div_of_nonneg_right hcs (by positivity)

/-- **Cauchy–Schwarz in `h`** (Source: main paper `e:U3maxmod`, L864–L876):
`‖A_θ f‖_{L⁴([-N,2N])}⁴ ≤ 162 (E_{|h| ≤ N} ‖Δ_h w‖_{U²([N])}⁴)^{1/2}
(E_{|h| ≤ N} ‖Δ_{-h} f‖_{U²([-N,2N])}⁴)^{1/2}`. -/
theorem four_pow_le_sqrt_mul_sqrt (N : ℕ+) (w f : ℤ → ℂ) (hw : ∀ n, n ∉ bracket N → w n = 0)
    (hf : ∀ y, y ∉ maxWindow N → f y = 0) (θ : ℤ → ℝ) :
    lpNormOn 4 (maxWindow N) (fun x => modAverage N w f (θ x) x) ^ 4 ≤
      162 * (Real.sqrt ((Finset.Icc (-(N : ℤ)) (N : ℤ)).expect fun h =>
          gowersNormOn 2 (bracket N) (conjDiff h w) ^ 4) *
        Real.sqrt ((Finset.Icc (-(N : ℤ)) (N : ℤ)).expect fun h =>
          gowersNormOn 2 (maxWindow N) (conjDiff (-h) f) ^ 4)) := by
  refine (four_pow_le_expect_U2_sq N w f hw hf θ).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  have := expect_mul_le_sqrt_mul_sqrt (Finset.Icc (-(N : ℤ)) (N : ℤ))
    (fun h => gowersNormOn 2 (bracket N) (conjDiff h w) ^ 2)
    (fun h => gowersNormOn 2 (maxWindow N) (conjDiff (-h) f) ^ 2)
  simpa only [← pow_mul] using this

/-- **The recursive identity** (Source: main paper `e:U3maxmod`, L877–L883):
`‖A_θ f‖_{L⁴([-N,2N])}⁴ ≤ 122472 ‖w‖_{U³([N])}⁴ ‖f‖_{U³([-N,2N])}⁴`, from the two `h`-averages
(`expect_gowersNormOn_two_conjDiff_pow_le_w`, `expect_gowersNormOn_two_conjDiff_pow_le_f`) and the
Cauchy-Schwarz step. -/
theorem four_pow_le_U3 (N : ℕ+) (w f : ℤ → ℂ) (hw : ∀ n, n ∉ bracket N → w n = 0)
    (hf : ∀ y, y ∉ maxWindow N → f y = 0) (θ : ℤ → ℝ) :
    lpNormOn 4 (maxWindow N) (fun x => modAverage N w f (θ x) x) ^ 4 ≤
      122472 * (gowersNormOn 3 (bracket N) w ^ 4 * gowersNormOn 3 (maxWindow N) f ^ 4) := by
  refine (four_pow_le_sqrt_mul_sqrt N w f hw hf θ).trans ?_
  have h1 := expect_gowersNormOn_two_conjDiff_pow_le_w N w hw
  have h2 := expect_gowersNormOn_two_conjDiff_pow_le_f N f hf
  have hn1 : 0 ≤ gowersNormOn 3 (bracket N) w := gowersNormOn_nonneg _ _ _
  have hn2 : 0 ≤ gowersNormOn 3 (maxWindow N) f := gowersNormOn_nonneg _ _ _
  have hs1 : Real.sqrt ((Finset.Icc (-(N : ℤ)) (N : ℤ)).expect fun h =>
      gowersNormOn 2 (bracket N) (conjDiff h w) ^ 4) ≤ 21 * gowersNormOn 3 (bracket N) w ^ 4 := by
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    calc _ ≤ 432 * gowersNormOn 3 (bracket N) w ^ 8 := h1
      _ ≤ (21 * gowersNormOn 3 (bracket N) w ^ 4) ^ 2 := by
          have : 0 ≤ gowersNormOn 3 (bracket N) w ^ 8 := by positivity
          nlinarith
  have hs2 : Real.sqrt ((Finset.Icc (-(N : ℤ)) (N : ℤ)).expect fun h =>
      gowersNormOn 2 (maxWindow N) (conjDiff (-h) f) ^ 4) ≤
      36 * gowersNormOn 3 (maxWindow N) f ^ 4 := by
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    calc _ ≤ 1296 * gowersNormOn 3 (maxWindow N) f ^ 8 := h2
      _ = (36 * gowersNormOn 3 (maxWindow N) f ^ 4) ^ 2 := by ring
  calc _ ≤ 162 * ((21 * gowersNormOn 3 (bracket N) w ^ 4) *
        (36 * gowersNormOn 3 (maxWindow N) f ^ 4)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hs1 hs2 (Real.sqrt_nonneg _) (by positivity))
          (by norm_num)
    _ = 122472 * (gowersNormOn 3 (bracket N) w ^ 4 * gowersNormOn 3 (maxWindow N) f ^ 4) := by
        ring

end PrimeCarleson.Proof.Paper
