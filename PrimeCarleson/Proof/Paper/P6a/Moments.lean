module

public import PrimeCarleson.Proof.Paper.P6a.Basic
public import PrimeCarleson.Proof.KMTT.BlockMoment
public import PrimeCarleson.Proof.Paper.Defs.Norms
public import PrimeCarleson.Proof.FplusProp21.Application

/-!
# Moments of the residual `w - w_{≤ M(k)}` and of the blocks `w_Q`; the crude bound

Source: main paper `p:red-var`, L1305–L1310 (the `ℓ²` moment of the residual), L1338–L1359 (its
crude moment), L1416–L1419 and L1434–L1456 (the moments of `w_Q` used by `e:highQ-var-L2-red` and in
the crude high-denominator bound). The input is the moment bound for `w_Q` ([FKT1] Lemma 3.1):
`PrimeCarleson.Proof.KMTT.moment_wQ` and `norm_L2_wQ_le`.

Also the crude weight bound used by every crude `ℓ^s` estimate (`l:crude-lambda-var-scale` with
`N₀ = 2^k`): for an even `u`,
`2^{k/r} ‖u ψ_k‖_{ℓ^{r'}} ≲ ‖u‖_{L^{r'}([2^k])}` (`crude_piece_le`).
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson

/-! ### Helpers -/

/-- `[N] = {1, …, N}` for `N : ℕ+` is KMTT's `intervalN N`. -/
theorem intervalN_pnat (N : ℕ+) : KMTT.intervalN ((N : ℕ) : ℝ) = bracket N := by
  ext n
  rw [KMTT.mem_intervalN, mem_bracket]
  constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨h1, ?_⟩ <;> exact_mod_cast h2

/-- Minkowski's inequality for finite sums in `lpNormOn`, `p ≥ 1`. -/
theorem lpNormOn_finset_sum_le {ι : Type*} {p : ℝ} (hp : 1 ≤ p) (X : Finset ℤ) (s : Finset ι)
    (g : ι → ℤ → ℂ) :
    lpNormOn p X (fun n => ∑ j ∈ s, g j n) ≤ ∑ j ∈ s, lpNormOn p X (g j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have : (fun n => ∑ j ∈ (∅ : Finset ι), g j n) = 0 := by funext n; simp
    rw [this, Finset.sum_empty, lpNormOn_zero (zero_lt_one.trans_le hp)]
  | insert j s hj ih =>
    have : (fun n => ∑ i ∈ insert j s, g i n) = g j + fun n => ∑ i ∈ s, g i n := by
      funext n
      simp [Finset.sum_insert hj]
    rw [this, Finset.sum_insert hj]
    exact (lpNormOn_add_le hp X _ _).trans (add_le_add_right ih _)

/-- `‖-f‖_{L^p(X)} = ‖f‖_{L^p(X)}`. -/
theorem lpNormOn_neg' {p : ℝ} (hp : 0 < p) (X : Finset ℤ) (f : ℤ → ℂ) :
    lpNormOn p X (fun n => -f n) = lpNormOn p X f := by
  have : (fun n => -f n) = (-1 : ℂ) • f := by funext n; simp
  rw [this, lpNormOn_smul hp]
  simp

/-- Hölder (power mean): `‖f‖_{L^p(X)} ≤ ‖f‖_{L²(X)}` for `1 ≤ p ≤ 2` and `X` nonempty. -/
theorem lpNormOn_le_two {p : ℝ} (hp1 : 1 ≤ p) (hp2 : p ≤ 2) {X : Finset ℤ} (hX : X.Nonempty)
    (f : ℤ → ℂ) : lpNormOn p X f ≤ lpNormOn 2 X f := by
  have h := KMTT.avg_rpow_le_sqrt_avg_sq X hX (fun n => ‖f n‖) (fun _ => norm_nonneg _) hp1 hp2
  rw [lpNormOn_two]
  unfold lpNormOn
  simpa [one_div] using h

/-- A sup bound bounds the normalized `L^p` norm. -/
theorem lpNormOn_le_of_forall_le {p : ℝ} (hp : 0 < p) {X : Finset ℤ} (hX : X.Nonempty) {f : ℤ → ℂ}
    {B : ℝ} (hB : 0 ≤ B) (h : ∀ n ∈ X, ‖f n‖ ≤ B) : lpNormOn p X f ≤ B := by
  have hc : (0 : ℝ) < X.card := by exact_mod_cast hX.card_pos
  have h1 : ∑ n ∈ X, ‖f n‖ ^ p ≤ X.card * B ^ p := by
    calc ∑ n ∈ X, ‖f n‖ ^ p ≤ ∑ _n ∈ X, B ^ p :=
          Finset.sum_le_sum fun n hn => Real.rpow_le_rpow (norm_nonneg _) (h n hn) hp.le
      _ = X.card * B ^ p := by simp
  unfold lpNormOn
  calc ((X.card : ℝ)⁻¹ * ∑ n ∈ X, ‖f n‖ ^ p) ^ (1 / p)
      ≤ ((X.card : ℝ)⁻¹ * (X.card * B ^ p)) ^ (1 / p) :=
        Real.rpow_le_rpow (by positivity) (mul_le_mul_of_nonneg_left h1 (by positivity))
          (by positivity)
    _ = B := by
        rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul, ← Real.rpow_mul hB,
          mul_one_div_cancel hp.ne', Real.rpow_one]

/-- `t = k^{1/10} ≥ 1` and `t^10 = k` for `k ≥ 1`. -/
theorem tenth_root_facts {k : ℕ} (hk : 1 ≤ k) :
    1 ≤ (k : ℝ) ^ ((1 : ℝ) / 10) ∧ ((k : ℝ) ^ ((1 : ℝ) / 10)) ^ 10 = k := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  refine ⟨Real.one_le_rpow hk1 (by norm_num), ?_⟩
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
  norm_num

/-- `j ∈ jSet k` forces `j log 2 ≤ k^{1/10}`. -/
theorem log_two_mul_le_of_mem_jSet {k j : ℕ} (hj : j ∈ jSet k) :
    (j : ℝ) * Real.log 2 ≤ (k : ℝ) ^ ((1 : ℝ) / 10) := by
  have h := mem_jSet_iff.1 hj
  unfold cutoffM at h
  have := (Real.log_le_iff_le_exp (by positivity)).2 h
  rwa [Real.log_pow] at this

/-- The number of dyadic blocks `2^j ≤ M(k)` is at most `3 k^{1/10}`. -/
theorem card_jSet_le {k : ℕ} (hk : 1 ≤ k) :
    ((jSet k).card : ℝ) ≤ 3 * (k : ℝ) ^ ((1 : ℝ) / 10) := by
  obtain ⟨ht1, -⟩ := tenth_root_facts hk
  set t : ℝ := (k : ℝ) ^ ((1 : ℝ) / 10) with ht
  have hlog2 : (0.69 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hsub : jSet k ⊆ Finset.range (⌊2 * t⌋₊ + 1) := by
    intro j hj
    have h := log_two_mul_le_of_mem_jSet hj
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have : (j : ℝ) ≤ 2 * t := by nlinarith
    exact Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.le_floor this))
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_range] at h1
  have h2 : (⌊2 * t⌋₊ : ℝ) ≤ 2 * t := Nat.floor_le (by linarith)
  have h3 : ((jSet k).card : ℝ) ≤ ⌊2 * t⌋₊ + 1 := by exact_mod_cast h1
  linarith

/-! ### The moments -/

/-- **Moments of `w_Q`, `L²` form** (Source: main paper L1416–L1419, citing [FKT1] Lemma 3.1):
`‖w_Q‖_{L²([N])} ≤ C (1 + log Q)^3`
for every natural `Q ≥ 1` and every `N` (in particular `N = 2^k`). -/
theorem wQ_moment_L2 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q : ℕ) (N : ℕ+), 1 ≤ Q →
      lpNormOn 2 (bracket N) (wQ Q) ≤ C * (1 + Real.log Q) ^ 3 := by
  obtain ⟨C, hC, h⟩ := KMTT.norm_L2_wQ_le
  refine ⟨C, hC, fun Q N hQ => ?_⟩
  have hN1 : (1 : ℝ) ≤ ((N : ℕ) : ℝ) := by exact_mod_cast N.pos
  have h1 := h Q ((N : ℕ) : ℝ) hQ hN1
  rw [intervalN_pnat, one_div] at h1
  rw [lpNormOn_two_eq_sqrt]
  exact h1

/-- **The `ℓ²` moment of the residual, one-sided form**: `‖w - w_{≤ M(k)}‖_{L²([2^k])} ≤ C k`
(`|w(n)| ≤ log n ≤ k` on `[2^k]` and Minkowski over the dyadic blocks `Q ≤ M(k)`,
`‖w_Q‖_{L²([2^k])} ≤ C (1 + log Q)^3`). -/
theorem residual_L2_moment_oneSided :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (N : ℕ+), 1 ≤ k → (N : ℕ) = 2 ^ k →
      lpNormOn 2 (bracket N) (resWeight k) ≤ C * k := by
  obtain ⟨C₂, hC₂, h₂⟩ := wQ_moment_L2
  refine ⟨1 + 24 * C₂, by positivity, fun k N hk hN => ?_⟩
  obtain ⟨ht1, ht10⟩ := tenth_root_facts hk
  set t : ℝ := (k : ℝ) ^ ((1 : ℝ) / 10) with ht
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hlog2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hlog2' : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  -- decomposition `u_k = w + (-∑_j w_{2^j})`
  have hdecomp : resWeight k = fun n => wFun n + -∑ j ∈ jSet k, wQ (2 ^ j) n := by
    funext n
    simp [resWeight, wLeM_eq_sum, jSet, sub_eq_add_neg]
  have hne : (bracket N).Nonempty := bracket_nonempty N
  -- the term `w`
  have hw : lpNormOn 2 (bracket N) wFun ≤ k := by
    refine lpNormOn_le_of_forall_le two_pos hne (by positivity) fun n hn => ?_
    have hn' := mem_bracket.1 hn
    have hnpos : 0 < n.natAbs := by omega
    have hnle : n.natAbs ≤ 2 ^ k := by
      have : n ≤ ((N : ℕ) : ℤ) := hn'.2
      rw [hN] at this
      omega
    refine (norm_wFun_le_log n).trans ?_
    calc Real.log (n.natAbs : ℝ) ≤ Real.log ((2 : ℝ) ^ k) :=
          Real.log_le_log (by exact_mod_cast hnpos) (by exact_mod_cast hnle)
      _ = k * Real.log 2 := by rw [Real.log_pow]
      _ ≤ k := by nlinarith
  -- the blocks
  have hblock : ∀ j ∈ jSet k, lpNormOn 2 (bracket N) (wQ (2 ^ j)) ≤ 8 * C₂ * t ^ 3 := by
    intro j hj
    have h1 := h₂ (2 ^ j) N Nat.one_le_two_pow
    have hl := log_two_mul_le_of_mem_jSet hj
    have hlog : Real.log ((2 ^ j : ℕ) : ℝ) = j * Real.log 2 := by
      rw [Nat.cast_pow, Real.log_pow]; norm_num
    rw [hlog] at h1
    have h3 : (1 + (j : ℝ) * Real.log 2) ^ 3 ≤ (2 * t) ^ 3 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 3
    calc lpNormOn 2 (bracket N) (wQ (2 ^ j)) ≤ C₂ * (1 + (j : ℝ) * Real.log 2) ^ 3 := h1
      _ ≤ C₂ * (2 * t) ^ 3 := mul_le_mul_of_nonneg_left h3 hC₂
      _ = 8 * C₂ * t ^ 3 := by ring
  have hsum : lpNormOn 2 (bracket N) (fun n => ∑ j ∈ jSet k, wQ (2 ^ j) n) ≤
      3 * t * (8 * C₂ * t ^ 3) := by
    refine (lpNormOn_finset_sum_le (by norm_num) _ _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ _ hblock).trans ?_
    rw [nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (card_jSet_le hk) (by positivity)
  rw [hdecomp]
  refine (lpNormOn_add_le (by norm_num) _ _ _).trans ?_
  rw [lpNormOn_neg' two_pos]
  have ht4 : t ^ 4 ≤ k := by
    rw [← ht10]; exact pow_le_pow_right₀ ht1 (by norm_num)
  calc lpNormOn 2 (bracket N) wFun + lpNormOn 2 (bracket N) (fun n => ∑ j ∈ jSet k, wQ (2 ^ j) n)
      ≤ k + 3 * t * (8 * C₂ * t ^ 3) := add_le_add hw hsum
    _ = k + 24 * C₂ * t ^ 4 := by ring
    _ ≤ (1 + 24 * C₂) * k := by
      nlinarith [mul_le_mul_of_nonneg_left ht4 (by positivity : 0 ≤ 24 * C₂)]

/-- **The crude weight bound.** Let `r > 2`, `r' = r/(r-1)`. There is `C` (depending on `r` and
`ψ`) such that for every `k ≥ 1`, `N = 2^k`, every even `u : ℤ → ℂ`, every `s ≥ r'` and every
finitely supported `f`,
`‖V^r(∑_n f(x-n) u(n) ψ_k(n) e(λ n) : λ)‖_{ℓ^s} ≤ C ‖u‖_{L^{r'}([N])} ‖f‖_{ℓ^s}`
(`l:crude-lambda-var-scale` with `N₀ = 2^k`: `2^{k/r} ‖u ψ_k‖_{ℓ^{r'}} ≲ ‖u‖_{L^{r'}([2^k])}`,
`ψ_k` odd and `|ψ_k| ≤ 2^{-k} ‖ψ‖_∞`). -/
theorem crude_piece_le (ψ : PsiData) {r : ℝ} (hr : 2 < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (N : ℕ+), 1 ≤ k → (N : ℕ) = 2 ^ k → ∀ u : ℤ → ℂ,
      (∀ n, u (-n) = u n) → ∀ s : ℝ, r / (r - 1) ≤ s → ∀ f : ℤ →₀ ℂ,
        eLpNorm (varOp r (fun n => u n * psiKz ψ k n) (⇑f)) (ENNReal.ofReal s) Measure.count ≤
          ENNReal.ofReal (C * lpNormOn (r / (r - 1)) (bracket N) u) *
            eLpNorm (⇑f) (ENNReal.ofReal s) Measure.count := by
  have hr1 : 0 < r - 1 := by linarith
  set ρ : ℝ := r / (r - 1) with hρ
  have hrr : r.HolderConjugate ρ := Real.HolderConjugate.conjExponent (by linarith)
  have hρ1 : 1 < ρ := hrr.symm.lt
  have hρ0 : 0 < ρ := by linarith
  obtain ⟨C₀, hC₀, hcrude⟩ := crude_lambda_var_scale hr.le hrr
  obtain ⟨B, hB⟩ := ψ.hasCompactSupport.exists_bound_of_continuous ψ.contDiff.continuous
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  refine ⟨2 * C₀ * B, by positivity, fun k N hk hN u hu s hs f => ?_⟩
  have hs1 : 1 ≤ s := hρ1.le.trans hs
  set X : ℝ := (2 : ℝ) ^ k with hXdef
  have hX0 : 0 < X := by positivity
  have hX2 : 2 ≤ X := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
  have hNr : ((N : ℕ) : ℝ) = X := by rw [hN]; push_cast; rfl
  set w : ℤ → ℂ := fun n => u n * psiKz ψ k n with hw
  have hsupp : ∀ n : ℤ, X < |(n : ℝ)| → w n = 0 := by
    intro n hn
    have : (2 : ℝ) ^ k ≤ (n.natAbs : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs]; exact hn.le
    simp [hw, psiKz_eq_zero_of_ge ψ this]
  have h := (hcrude X hX2 w (⇑f) hsupp s hs1).1 hs
  set S : Finset ℤ := Finset.Icc (-(2 ^ k : ℤ)) (2 ^ k) with hSdef
  have hS : ∀ n ∉ S, w n = 0 := by
    intro n hn
    refine hsupp n ?_
    rw [hSdef, Finset.mem_Icc, not_and_or, not_le, not_le] at hn
    rcases hn with h1 | h1
    · have h2 : (n : ℝ) < -(2 : ℝ) ^ k := by exact_mod_cast h1
      calc X < -(n : ℝ) := by rw [hXdef]; linarith
        _ ≤ |(n : ℝ)| := neg_le_abs _
    · have h2 : (2 : ℝ) ^ k < (n : ℝ) := by exact_mod_cast h1
      exact lt_of_lt_of_le (by rw [hXdef]; exact h2) (le_abs_self _)
  -- the norm of `w`
  have hnorm : eLpNorm w (ENNReal.ofReal ρ) Measure.count =
      ENNReal.ofReal ((∑ n ∈ S, ‖w n‖ ^ ρ) ^ (1 / ρ)) := by
    rw [eLpNorm_count_eq_tsum w hρ0, tsum_enorm_rpow_eq_ofReal_sum hS hρ0,
      ENNReal.ofReal_rpow_of_nonneg (Finset.sum_nonneg fun _ _ => by positivity)
        (by positivity)]
  -- pointwise bounds
  have hpsi : ∀ n : ℤ, ‖psiKz ψ k n‖ ≤ B / X := by
    intro n
    unfold psiKz psiK
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos hX0]
    have hb := hB (n * X⁻¹)
    rw [Real.norm_eq_abs] at hb
    calc X⁻¹ * |ψ.toFun (n * X⁻¹)| ≤ X⁻¹ * B :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = B / X := by ring
  have hwle : ∀ n : ℤ, ‖w n‖ ≤ (B / X) * ‖u n‖ := by
    intro n
    simp only [hw, norm_mul]
    calc ‖u n‖ * ‖psiKz ψ k n‖ ≤ ‖u n‖ * (B / X) :=
          mul_le_mul_of_nonneg_left (hpsi n) (norm_nonneg _)
      _ = B / X * ‖u n‖ := by ring
  have hw0 : w 0 = 0 := by simp [hw, psiKz_zero]
  have hweven : ∀ n : ℤ, ‖w (-n)‖ ^ ρ = ‖w n‖ ^ ρ := by
    intro n
    have : ‖w (-n)‖ = ‖w n‖ := by simp [hw, hu, psiKz_neg]
    rw [this]
  -- the sum over `S`
  have hsumS : ∑ n ∈ S, ‖w n‖ ^ ρ ≤ 2 * ((B / X) ^ ρ * (X * lpNormOn ρ (bracket N) u ^ ρ)) := by
    have h0 : (0 : ℤ) ∈ S := by
      have h2k : (0 : ℤ) ≤ 2 ^ k := by positivity
      rw [hSdef, Finset.mem_Icc]; constructor <;> linarith
    rw [← Finset.sum_erase S (f := fun n => ‖w n‖ ^ ρ) (a := 0)
      (by simp [hw0, Real.zero_rpow hρ0.ne'])]
    have h1 := KMTT.sum_le_two_mul_of_even (S := S.erase 0) (N := X) (fun n => ‖w n‖ ^ ρ)
      (fun n => Real.rpow_nonneg (norm_nonneg _) _) hweven (fun n hn => by
        rw [Finset.mem_erase, hSdef, Finset.mem_Icc] at hn
        obtain ⟨hn0, h1, h2⟩ := hn
        refine ⟨Int.one_le_abs hn0, ?_⟩
        rw [← Int.cast_abs, hXdef]
        have : |n| ≤ 2 ^ k := abs_le.2 ⟨h1, h2⟩
        exact_mod_cast this)
    rw [← hNr, intervalN_pnat] at h1
    refine h1.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    calc ∑ n ∈ bracket N, ‖w n‖ ^ ρ ≤ ∑ n ∈ bracket N, (B / X) ^ ρ * ‖u n‖ ^ ρ :=
          Finset.sum_le_sum fun n _ => by
            rw [← Real.mul_rpow (by positivity) (norm_nonneg _)]
            exact Real.rpow_le_rpow (norm_nonneg _) (hwle n) hρ0.le
      _ = (B / X) ^ ρ * ∑ n ∈ bracket N, ‖u n‖ ^ ρ := by rw [Finset.mul_sum]
      _ = (B / X) ^ ρ * (X * lpNormOn ρ (bracket N) u ^ ρ) := by
          rw [lpNormOn_rpow hρ0, card_bracket, hNr]
          congr 1
          field_simp
  -- the real inequality
  set Λ : ℝ := lpNormOn ρ (bracket N) u with hΛ
  have hΛ0 : 0 ≤ Λ := lpNormOn_nonneg _ _ _
  have hreal : C₀ * X ^ (1 / r) * (∑ n ∈ S, ‖w n‖ ^ ρ) ^ (1 / ρ) ≤ 2 * C₀ * B * Λ := by
    have h1 : (∑ n ∈ S, ‖w n‖ ^ ρ) ^ (1 / ρ) ≤
        (2 * ((B / X) ^ ρ * (X * Λ ^ ρ))) ^ (1 / ρ) :=
      Real.rpow_le_rpow (Finset.sum_nonneg fun _ _ => by positivity) hsumS (by positivity)
    have h2 : (2 * ((B / X) ^ ρ * (X * Λ ^ ρ))) ^ (1 / ρ) =
        2 ^ (1 / ρ) * ((B / X) * X ^ (1 / ρ) * Λ) := by
      have hBX : 0 ≤ B / X := by positivity
      rw [Real.mul_rpow (by norm_num) (by positivity), Real.mul_rpow (by positivity)
        (by positivity), Real.mul_rpow hX0.le (by positivity), ← Real.rpow_mul hBX,
        ← Real.rpow_mul hΛ0, mul_one_div_cancel hρ0.ne', Real.rpow_one, Real.rpow_one]
      ring
    have hXexp : X ^ (1 / r) * X ^ (1 / ρ) = X := by
      rw [← Real.rpow_add hX0]
      have := hrr.inv_add_inv_eq_one
      rw [one_div, one_div, this, Real.rpow_one]
    have h2ρ : (2 : ℝ) ^ (1 / ρ) ≤ 2 := by
      calc (2 : ℝ) ^ (1 / ρ) ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) ((div_le_one hρ0).2 hρ1.le)
        _ = 2 := Real.rpow_one 2
    calc C₀ * X ^ (1 / r) * (∑ n ∈ S, ‖w n‖ ^ ρ) ^ (1 / ρ)
        ≤ C₀ * X ^ (1 / r) * (2 ^ (1 / ρ) * ((B / X) * X ^ (1 / ρ) * Λ)) := by
          rw [← h2]
          exact mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = C₀ * 2 ^ (1 / ρ) * B * Λ * ((X ^ (1 / r) * X ^ (1 / ρ)) / X) := by
          field_simp
      _ = C₀ * 2 ^ (1 / ρ) * B * Λ := by rw [hXexp, div_self hX0.ne', mul_one]
      _ ≤ 2 * C₀ * B * Λ := by
          have : C₀ * 2 ^ (1 / ρ) * B * Λ = C₀ * B * Λ * 2 ^ (1 / ρ) := by ring
          rw [this]
          calc C₀ * B * Λ * 2 ^ (1 / ρ) ≤ C₀ * B * Λ * 2 :=
                mul_le_mul_of_nonneg_left h2ρ (by positivity)
            _ = 2 * C₀ * B * Λ := by ring
  refine h.trans ?_
  rw [hnorm, ← ENNReal.ofReal_mul (by positivity)]
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal hreal) le_rfl

end PrimeCarleson.Proof.Paper
