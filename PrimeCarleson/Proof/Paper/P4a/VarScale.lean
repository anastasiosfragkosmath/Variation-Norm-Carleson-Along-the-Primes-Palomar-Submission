module

public import PrimeCarleson.Proof.Paper.P4a.Embed
public import PrimeCarleson.Proof.Paper.P4a.LpCount
public import PrimeCarleson.Proof.Paper.Defs.Modulated

/-!
# `ℓ^p` bounds for the `r`-variation of modulated convolutions at scale `N₀`

Source: main paper `l:crude-lambda-var-scale`, L1072–L1096 (statement) and L1139–L1182 (proof, in
the three steps L1139–L1151, L1152–L1169 and L1170–L1182); consumers: `p:red-var` at L1328 and L1435
(in `P6a/`), with `w = u_k ψ_k` or `w_Q ψ_k` and `N₀ = 2^k`.

For `r > 2`, `r' = r/(r-1)`, `w` supported in `{|n| ≤ N₀}` and
`T_λ f(x) = ∑_n f(x-n) w(n) e(λ n)` (`Paper.weightedModSum`):

* `pointwise_embed`: `V^r(T_λ f(x) : λ ∈ 𝕋) ≤ C_r N₀^{1/r} (∑_n |w(n)|^{r'} |f(x-n)|^{r'})^{1/r'}`
  (the embedding `embed_variation` with `c_n = w(n) f(x-n)`);
* `eLpNorm_sum_translate_le` (`p ≥ r'`, Minkowski in `ℓ^{p/r'}`) and
  `eLpNorm_sum_translate_le_of_le` (`p ≤ r'`, subadditivity of `t ↦ t^{p/r'}`) bound the `ℓ^p_x`
  norm of the right-hand side by `‖w‖_{ℓ^{r'}} ‖f‖_{ℓ^p}`, respectively `‖w‖_{ℓ^p} ‖f‖_{ℓ^p}`;
* `crude_lambda_var_scale_nat` and `crude_lambda_var_scale`: the two estimates of the lemma, with
  an integral and a real scale `N₀`.

All inequalities are in `ℝ≥0∞` and hold without finiteness hypotheses on `f`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Common PrimeCarleson.Proof.Goal0

/-- **The pointwise embedding step of `l:crude-lambda-var-scale`** (L1139–L1151): let `r, r'` be
conjugate exponents with `2 ≤ r`. There is a constant `C` depending only on `r` such that for every
`N₀ ≥ 1`, every `w : ℤ → ℂ` supported in `{|n| ≤ N₀}` and every `f : ℤ → ℂ` (the sum
`T_λ f(x) = ∑_n f(x-n) w(n) e(λ n)` is finite), and every `x ∈ ℤ`,
`V^r(T_λ f(x) : λ ∈ 𝕋) ≤ C N₀^{1/r} (∑_n |w(n)|^{r'} |f(x-n)|^{r'})^{1/r'}` (`e:embed` with
`c_n = w(n) f(x-n)`). The right-hand side is in `ℝ≥0∞`. Source: main paper
`l:crude-lambda-var-scale`, L1139–L1151. -/
theorem pointwise_embed {r r' : ℝ} (hr : 2 ≤ r) (hrr' : r.HolderConjugate r') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N₀ : ℕ), 0 < N₀ → ∀ (w f : ℤ → ℂ),
      (∀ n ∉ Finset.Icc (-(N₀ : ℤ)) N₀, w n = 0) → ∀ x : ℤ,
      pointwiseVariation r (fun lam x => weightedModSum w f lam x) x ≤
        ENNReal.ofReal (C * (N₀ : ℝ) ^ (1 / r)) *
          (∑ n ∈ Finset.Icc (-(N₀ : ℤ)) N₀, ‖w n‖ₑ ^ r' * ‖f (x - n)‖ₑ ^ r') ^ (1 / r') := by
  obtain ⟨C, hC, h⟩ := embed_variation hr hrr'
  have hr'0 : 0 < r' := hrr'.symm.pos
  refine ⟨C, hC, fun N₀ hN₀ w f hw x => ?_⟩
  set S : Finset ℤ := Finset.Icc (-(N₀ : ℤ)) N₀ with hS
  have hP : (fun lam => weightedModSum w f lam x) =
      fun lam => ∑ n ∈ S, (w n * f (x - n)) * e (lam * n) := by
    funext lam
    rw [weightedModSum_eq_sum w f lam x S hw]
    exact Finset.sum_congr rfl fun n _ => by ring
  have h1 := h N₀ hN₀ (fun n => w n * f (x - n))
  change rVariationOn r (Set.Ico 0 1) (fun lam => weightedModSum w f lam x) ≤ _
  rw [hP]
  refine h1.trans (le_of_eq ?_)
  rw [ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [← sum_enorm_rpow_rpow_eq_ofReal S (fun n => w n * f (x - n)) hr'0]
  have hsum : ∑ n ∈ S, ‖w n * f (x - n)‖ₑ ^ r' = ∑ n ∈ S, ‖w n‖ₑ ^ r' * ‖f (x - n)‖ₑ ^ r' :=
    Finset.sum_congr rfl fun n _ => by rw [enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ hr'0.le]
  rw [hsum]


/-! ### Minkowski and subadditivity in `ℓ^p_x` -/

/-- Translation invariance of `ℓ^p` sums over `ℤ`. -/
theorem tsum_enorm_rpow_translate {E : Type*} [NormedAddCommGroup E] (f : ℤ → E) (n : ℤ) (p : ℝ) :
    ∑' x, ‖f (x - n)‖ₑ ^ p = ∑' x, ‖f x‖ₑ ^ p :=
  (Equiv.subRight n).tsum_eq (fun x => ‖f x‖ₑ ^ p)

/-- Subadditivity of `t ↦ t^q`, `0 < q ≤ 1`, for finite sums in `ℝ≥0∞`. -/
theorem rpow_finsetSum_le_finsetSum_rpow_of_le_one {ι : Type*} (s : Finset ι) (a : ι → ℝ≥0∞) {q : ℝ}
    (hq0 : 0 < q) (hq1 : q ≤ 1) : (∑ i ∈ s, a i) ^ q ≤ ∑ i ∈ s, a i ^ q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ENNReal.zero_rpow_of_pos hq0]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (ENNReal.rpow_add_le_add_rpow _ _ hq0.le hq1).trans (add_le_add_right ih _)

/-- **The Minkowski case of `l:crude-lambda-var-scale`, the displayed estimate** (L1152–L1169): for
`0 < r' ≤ p` (so `p/r' ≥ 1`), a finite set `S` and `w, f : ℤ → ℂ`,
`‖(∑_{n ∈ S} |w(n)|^{r'} |f(x-n)|^{r'})^{1/r'}‖_{ℓ^p_x} ≤ (∑_{n ∈ S} |w(n)|^{r'})^{1/r'} ‖f‖_{ℓ^p}`:
`l:crude-lambda-var-scale`, L1152–L1169 (with Minkowski's inequality). -/
theorem eLpNorm_sum_translate_le {S : Finset ℤ} (w f : ℤ → ℂ) {r' p : ℝ} (hr' : 0 < r')
    (hp : r' ≤ p) :
    eLpNorm (fun x => (∑ n ∈ S, ‖w n‖ₑ ^ r' * ‖f (x - n)‖ₑ ^ r') ^ (1 / r'))
        (ENNReal.ofReal p) Measure.count ≤
      (∑ n ∈ S, ‖w n‖ₑ ^ r') ^ (1 / r') * eLpNorm f (ENNReal.ofReal p) Measure.count := by
  have hp0 : 0 < p := hr'.trans_le hp
  set q : ℝ := p / r' with hq
  have hq1 : 1 ≤ q := (one_le_div hr').2 hp
  have hq0 : 0 < q := by linarith
  have hrq : r' * q = p := by rw [hq]; field_simp
  set a : ℤ → ℤ → ℝ≥0∞ := fun n x => ‖w n‖ₑ ^ r' * ‖f (x - n)‖ₑ ^ r' with ha
  set t : ℝ≥0∞ := ∑' x, ‖f x‖ₑ ^ p with ht
  set W : ℝ≥0∞ := ∑ n ∈ S, ‖w n‖ₑ ^ r' with hW
  set A : ℝ≥0∞ := ∑' x, (∑ n ∈ S, a n x) ^ q with hA
  have h1 : A ^ (1 / q) ≤ W * t ^ (1 / q) := by
    have hmink := eLpNorm_count_finset_sum_le S a hq1
    rw [eLpNorm_count_eq_tsum_enn _ hq0] at hmink
    have hterm : ∀ n, eLpNorm (a n) (ENNReal.ofReal q) Measure.count =
        ‖w n‖ₑ ^ r' * t ^ (1 / q) := by
      intro n
      rw [eLpNorm_count_eq_tsum_enn _ hq0]
      have h : ∑' x, (a n x) ^ q = ‖w n‖ₑ ^ p * t := by
        simp_rw [ha, ENNReal.mul_rpow_of_nonneg _ _ hq0.le, ← ENNReal.rpow_mul, hrq]
        rw [ENNReal.tsum_mul_left, tsum_enorm_rpow_translate]
      rw [h, ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul]
      congr 2
      rw [hq]; field_simp
    simp_rw [hterm] at hmink
    rw [← Finset.sum_mul] at hmink
    exact hmink
  have h2 : eLpNorm (fun x => (∑ n ∈ S, a n x) ^ (1 / r')) (ENNReal.ofReal p) Measure.count =
      A ^ (1 / p) := by
    rw [eLpNorm_count_eq_tsum_enn _ hp0]
    congr 2
    funext x
    rw [← ENNReal.rpow_mul]
    congr 1
    rw [hq]; field_simp
  have h3 : A ^ (1 / p) ≤ W ^ (1 / r') * t ^ (1 / p) := by
    calc A ^ (1 / p) = (A ^ (1 / q)) ^ (q / p) := by
          rw [← ENNReal.rpow_mul]
          congr 1
          field_simp
      _ ≤ (W * t ^ (1 / q)) ^ (q / p) := ENNReal.rpow_le_rpow h1 (by positivity)
      _ = W ^ (1 / r') * t ^ (1 / p) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul]
          congr 2
          · rw [hq]; field_simp
          · field_simp
  rw [eLpNorm_count_eq_tsum f hp0]
  exact h2.trans_le h3


/-- **The subadditivity case of `l:crude-lambda-var-scale`, the displayed estimate** (L1170–L1182):
for `0 < p ≤ r'` (so `p/r' ≤ 1`), a finite set `S` and `w, f : ℤ → ℂ`,
`‖(∑_{n ∈ S} |w(n)|^{r'} |f(x-n)|^{r'})^{1/r'}‖_{ℓ^p_x}^p ≤ ∑_{n∈S} |w(n)|^p ‖f‖_{ℓ^p}^p`, stated as
the `p`-th root: the subadditivity of `t ↦ t^{p/r'}` and the interchange of the sums. Source: main
paper `l:crude-lambda-var-scale`, L1170–L1182. -/
theorem eLpNorm_sum_translate_le_of_le {S : Finset ℤ} (w f : ℤ → ℂ) {r' p : ℝ} (hp : 0 < p)
    (hpr : p ≤ r') :
    eLpNorm (fun x => (∑ n ∈ S, ‖w n‖ₑ ^ r' * ‖f (x - n)‖ₑ ^ r') ^ (1 / r'))
        (ENNReal.ofReal p) Measure.count ≤
      (∑ n ∈ S, ‖w n‖ₑ ^ p) ^ (1 / p) * eLpNorm f (ENNReal.ofReal p) Measure.count := by
  have hr' : 0 < r' := hp.trans_le hpr
  set q : ℝ := p / r' with hq
  have hq1 : q ≤ 1 := (div_le_one hr').2 hpr
  have hq0 : 0 < q := by positivity
  have hrq : r' * q = p := by rw [hq]; field_simp
  set t : ℝ≥0∞ := ∑' x, ‖f x‖ₑ ^ p with ht
  have hpt : ∀ x, ((∑ n ∈ S, ‖w n‖ₑ ^ r' * ‖f (x - n)‖ₑ ^ r') ^ (1 / r')) ^ p ≤
      ∑ n ∈ S, ‖w n‖ₑ ^ p * ‖f (x - n)‖ₑ ^ p := by
    intro x
    rw [← ENNReal.rpow_mul, show 1 / r' * p = q by rw [hq]; field_simp]
    refine (rpow_finsetSum_le_finsetSum_rpow_of_le_one S _ hq0 hq1).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, hrq]
  have hsum : ∑' x, ((∑ n ∈ S, ‖w n‖ₑ ^ r' * ‖f (x - n)‖ₑ ^ r') ^ (1 / r')) ^ p ≤
      (∑ n ∈ S, ‖w n‖ₑ ^ p) * t := by
    calc _ ≤ ∑' x, ∑ n ∈ S, ‖w n‖ₑ ^ p * ‖f (x - n)‖ₑ ^ p := ENNReal.tsum_le_tsum hpt
      _ = ∑ n ∈ S, ∑' x, ‖w n‖ₑ ^ p * ‖f (x - n)‖ₑ ^ p :=
          Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)
      _ = ∑ n ∈ S, ‖w n‖ₑ ^ p * t := by
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [ENNReal.tsum_mul_left, tsum_enorm_rpow_translate]
      _ = (∑ n ∈ S, ‖w n‖ₑ ^ p) * t := by rw [Finset.sum_mul]
  rw [eLpNorm_count_eq_tsum_enn _ hp, eLpNorm_count_eq_tsum f hp]
  calc _ ≤ ((∑ n ∈ S, ‖w n‖ₑ ^ p) * t) ^ (1 / p) := ENNReal.rpow_le_rpow hsum (by positivity)
    _ = _ := ENNReal.mul_rpow_of_nonneg _ _ (by positivity)


/-- The `ℓ^p` norm of a sequence carried by a finite set `S` is the finite sum. -/
theorem eLpNorm_count_eq_sum_of_support {S : Finset ℤ} {w : ℤ → ℂ} (hw : ∀ n ∉ S, w n = 0)
    {p : ℝ} (hp : 0 < p) :
    eLpNorm w (ENNReal.ofReal p) Measure.count = (∑ n ∈ S, ‖w n‖ₑ ^ p) ^ (1 / p) := by
  rw [eLpNorm_count_eq_tsum w hp,
    tsum_eq_sum (s := S) (fun n hn => by simp [hw n hn, ENNReal.zero_rpow_of_pos hp])]

/-- **`l:crude-lambda-var-scale`** with an integral scale `N₀` (the form of the proof): for
conjugate exponents `2 ≤ r`, `r'` there is a constant `C` depending only on `r` (not on `p`) such
that for `N₀ ≥ 1`, `w` supported in `{|n| ≤ N₀}`, any `f`, and `p ≥ 1`:
if `p ≥ r'`: `‖V^r(T_λ f : λ ∈ 𝕋)‖_{ℓ^p} ≤ C N₀^{1/r} ‖w‖_{ℓ^{r'}} ‖f‖_{ℓ^p}`;
if `p < r'`: `‖V^r(T_λ f : λ ∈ 𝕋)‖_{ℓ^p} ≤ C N₀^{1/r} ‖w‖_{ℓ^p} ‖f‖_{ℓ^p}`.
Here `T_λ f(x) = ∑_n f(x-n) w(n) e(λ n)` is `weightedModSum w f λ x` and
`V^r(T_λ f : λ ∈ 𝕋)(x)` is `pointwiseVariation r (T_λ f) x`. -/
theorem crude_lambda_var_scale_nat {r r' : ℝ} (hr : 2 ≤ r) (hrr' : r.HolderConjugate r') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N₀ : ℕ), 0 < N₀ → ∀ (w f : ℤ → ℂ),
      (∀ n ∉ Finset.Icc (-(N₀ : ℤ)) N₀, w n = 0) → ∀ p : ℝ, 1 ≤ p →
      (r' ≤ p →
        eLpNorm (pointwiseVariation r (fun lam x => weightedModSum w f lam x))
            (ENNReal.ofReal p) Measure.count ≤
          ENNReal.ofReal (C * (N₀ : ℝ) ^ (1 / r)) * eLpNorm w (ENNReal.ofReal r') Measure.count *
            eLpNorm f (ENNReal.ofReal p) Measure.count) ∧
      (p < r' →
        eLpNorm (pointwiseVariation r (fun lam x => weightedModSum w f lam x))
            (ENNReal.ofReal p) Measure.count ≤
          ENNReal.ofReal (C * (N₀ : ℝ) ^ (1 / r)) * eLpNorm w (ENNReal.ofReal p) Measure.count *
            eLpNorm f (ENNReal.ofReal p) Measure.count) := by
  obtain ⟨C, hC, hpt⟩ := pointwise_embed hr hrr'
  have hr'0 : 0 < r' := hrr'.symm.pos
  refine ⟨C, hC, fun N₀ hN₀ w f hw p hp => ?_⟩
  have hp0 : 0 < p := by linarith
  set S : Finset ℤ := Finset.Icc (-(N₀ : ℤ)) N₀ with hS
  set K : ℝ≥0∞ := ENNReal.ofReal (C * (N₀ : ℝ) ^ (1 / r)) with hK
  set G : ℤ → ℝ≥0∞ := fun x => (∑ n ∈ S, ‖w n‖ₑ ^ r' * ‖f (x - n)‖ₑ ^ r') ^ (1 / r') with hG
  have hV : eLpNorm (pointwiseVariation r (fun lam x => weightedModSum w f lam x))
        (ENNReal.ofReal p) Measure.count ≤ K * eLpNorm G (ENNReal.ofReal p) Measure.count := by
    calc _ ≤ eLpNorm (fun x => K * G x) (ENNReal.ofReal p) Measure.count :=
          eLpNorm_count_mono_enn (fun x => hpt N₀ hN₀ w f hw x) _
      _ = K * eLpNorm G (ENNReal.ofReal p) Measure.count := eLpNorm_count_const_mul K G hp0
  refine ⟨fun hpr => ?_, fun hpr => ?_⟩
  · rw [eLpNorm_count_eq_sum_of_support hw hr'0, mul_assoc]
    exact hV.trans (mul_le_mul_right (eLpNorm_sum_translate_le w f hr'0 hpr) _)
  · rw [eLpNorm_count_eq_sum_of_support hw hp0, mul_assoc]
    exact hV.trans (mul_le_mul_right (eLpNorm_sum_translate_le_of_le w f hp0 hpr.le) _)


/-- **`l:crude-lambda-var-scale`** (L1072-L1096): let `2 ≤ r` and `r' = r/(r-1)` (conjugate
exponents). There is a constant `C`, depending only on `r`, such that for every real `N₀ ≥ 2`, every
`w : ℤ → ℂ` supported in `{|n| ≤ N₀}`, every `f : ℤ → ℂ` and every `p ≥ 1`,
* if `p ≥ r'`: `‖V^r(T_λ f : λ ∈ 𝕋)‖_{ℓ^p(ℤ)} ≤ C N₀^{1/r} ‖w‖_{ℓ^{r'}(ℤ)} ‖f‖_{ℓ^p(ℤ)}`;
* if `p < r'`: `‖V^r(T_λ f : λ ∈ 𝕋)‖_{ℓ^p(ℤ)} ≤ C N₀^{1/r} ‖w‖_{ℓ^p(ℤ)} ‖f‖_{ℓ^p(ℤ)}`,
where `T_λ f(x) = ∑_n f(x-n) w(n) e(λ n)` (`weightedModSum`) and the variation is over
`𝕋 = [0, 1)`. Source: main paper `l:crude-lambda-var-scale`, L1072–L1096. The statement is stronger
than the paper's in
three respects: `r = 2` is allowed (the paper has `r > 2`), the constant does not depend on `p`
(`≲_{p,r}` is printed), and `f` need not be finitely supported (the inequality is in `ℝ≥0∞`).
The case of an integral scale is `crude_lambda_var_scale_nat`. -/
theorem crude_lambda_var_scale {r r' : ℝ} (hr : 2 ≤ r) (hrr' : r.HolderConjugate r') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N₀ : ℝ), 2 ≤ N₀ → ∀ (w f : ℤ → ℂ),
      (∀ n : ℤ, N₀ < |(n : ℝ)| → w n = 0) → ∀ p : ℝ, 1 ≤ p →
      (r' ≤ p →
        eLpNorm (pointwiseVariation r (fun lam x => weightedModSum w f lam x))
            (ENNReal.ofReal p) Measure.count ≤
          ENNReal.ofReal (C * N₀ ^ (1 / r)) * eLpNorm w (ENNReal.ofReal r') Measure.count *
            eLpNorm f (ENNReal.ofReal p) Measure.count) ∧
      (p < r' →
        eLpNorm (pointwiseVariation r (fun lam x => weightedModSum w f lam x))
            (ENNReal.ofReal p) Measure.count ≤
          ENNReal.ofReal (C * N₀ ^ (1 / r)) * eLpNorm w (ENNReal.ofReal p) Measure.count *
            eLpNorm f (ENNReal.ofReal p) Measure.count) := by
  obtain ⟨C, hC, h⟩ := crude_lambda_var_scale_nat hr hrr'
  refine ⟨C, hC, fun N₀ hN₀ w f hw p hp => ?_⟩
  have hN₀0 : (0 : ℝ) ≤ N₀ := by linarith
  set N : ℕ := ⌊N₀⌋₊ with hN
  have hN2 : 2 ≤ N := Nat.le_floor (by exact_mod_cast hN₀)
  have hNle : (N : ℝ) ≤ N₀ := Nat.floor_le hN₀0
  have hwN : ∀ n ∉ Finset.Icc (-(N : ℤ)) N, w n = 0 := by
    intro n hn
    refine hw n ?_
    have h1 : (N : ℤ) < |n| := by
      rw [Finset.mem_Icc] at hn
      rw [lt_abs]
      omega
    have h2 : ((N : ℤ) : ℝ) + 1 ≤ |(n : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast h1
    have h3 := Nat.lt_floor_add_one N₀
    push_cast at h2
    linarith
  obtain ⟨h1, h2⟩ := h N (by omega) w f hwN p hp
  have hmono : ENNReal.ofReal (C * (N : ℝ) ^ (1 / r)) ≤ ENNReal.ofReal (C * N₀ ^ (1 / r)) := by
    refine ENNReal.ofReal_le_ofReal ?_
    gcongr
  refine ⟨fun hpr => (h1 hpr).trans ?_, fun hpr => (h2 hpr).trans ?_⟩
  · gcongr
  · gcongr

end PrimeCarleson.Proof.Paper
