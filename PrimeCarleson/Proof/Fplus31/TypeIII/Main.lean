module

public import PrimeCarleson.Proof.Fplus31.TypeIII.Decomposition
public import PrimeCarleson.Proof.Fplus31.TypeIII.TypeI
public import PrimeCarleson.Proof.Fplus31.TypeIII.TypeII
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The type I / type II dichotomy for `Λ - Λ_{C,w}`

Part of the proof of [F+] Proposition 3.1. Its consumers are the type I step (`hI`, `C2/TypeI.lean`)
and the type II step (four-fold bound, `C2/TypeIIBoxes.lean`). All the pieces are in this directory:
Vaughan's identity at `N^{1/3}` (`Vaughan.lean`), the exact decomposition with the Brun truncation
of `Λ_C` (`Decomposition.lean`), the type I extraction (`TypeI.lean`) and the bilinear
Cauchy–Schwarz type II extraction (`BilinearCS.lean`, `TypeII.lean`, with the divisor moments of
`Divisor.lean`). Here they are assembled:

* `log_two_le`: `⌊log₂ D⌋ + 1 ≤ 2 (1 + log N)` for `D ≤ N`;
* `card_cube_le`: `#{n ≤ N : n³ ≤ N} ≤ N^{1/3}`; `two_add_exp_five_lt`: `2 + e⁵ < 151`;
* `norm_smallPart_le`, `norm_brunErr_le`: the negligible parts;
* `typeIPart_alt`: the averaging step `‖typeIPart‖ ≥ ζ (1 + log N)` ⟹ one cut-off sum is `≥ ζ`;
* `sum_Icc_int_natCast`: sums over `[1, N] ⊆ ℤ` and `⊆ ℕ`; `dvdSum_eq_floor_sum`: the type I atom
  in the form `∑_{n ≤ ⌊N'/ℓ⌋} φ(ℓ n)` of the type I step;
* `vonMangoldt_sub_cramer_typeI_or_typeII`: the dichotomy (type I `hI` of the type I step, or the
  type II four-fold bound of the type II step), and `..._of_brun` with the numeric Brun bound of
  `cramer_brun_L1_Icc`;
* `typeII_pairs`: the pigeonhole of the type II step, from the four-fold bound to `≫ x L²` pairs
  `(ℓ, ℓ')` with a large correlation `‖∑_m φ(ℓ m) conj φ(ℓ' m)‖`.
-/

@[expose] public noncomputable section

open Finset

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

/-- `⌊log₂ D⌋ + 1 ≤ 2 (1 + log N)` for `1 ≤ D ≤ N`. -/
theorem log_two_le {D N : ℕ} (hD : 1 ≤ D) (hDN : D ≤ N) :
    ((Nat.log 2 D + 1 : ℕ) : ℝ) ≤ 2 * (1 + Real.log N) := by
  have h1 : (2 : ℝ) ^ Nat.log 2 D ≤ D := by exact_mod_cast Nat.pow_log_le_self 2 (by omega)
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  have h2 : (Nat.log 2 D : ℝ) * Real.log 2 ≤ Real.log D := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) h1
  have h3 : Real.log D ≤ Real.log N := Real.log_le_log hDpos (by exact_mod_cast hDN)
  have h4 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have h5 : (0 : ℝ) ≤ Nat.log 2 D := Nat.cast_nonneg _
  push_cast
  linarith only [h2, h3, mul_le_mul_of_nonneg_left h4.le h5, h5]

/-- The number of `n ≤ N` with `n³ ≤ N` is at most `N^{1/3}`. -/
theorem card_cube_le (N : ℕ) :
    (((Icc 1 N).filter fun n => n ^ 3 ≤ N).card : ℝ) ≤ (N : ℝ) ^ ((3 : ℝ)⁻¹) := by
  set x : ℝ := (N : ℝ) ^ ((3 : ℝ)⁻¹) with hx
  have hx0 : 0 ≤ x := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hsub : (Icc 1 N).filter (fun n => n ^ 3 ≤ N) ⊆ Icc 1 ⌊x⌋₊ := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
    refine ⟨hn.1.1, Nat.le_floor ?_⟩
    rw [hx, Real.le_rpow_inv_iff_of_pos (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by norm_num)]
    have : ((n : ℝ)) ^ (3 : ℝ) = (n : ℝ) ^ 3 := by exact_mod_cast Real.rpow_natCast (n : ℝ) 3
    rw [this]
    exact_mod_cast hn.2
  calc (((Icc 1 N).filter fun n => n ^ 3 ≤ N).card : ℝ) ≤ (Icc 1 ⌊x⌋₊).card := by
        exact_mod_cast Finset.card_le_card hsub
    _ = ⌊x⌋₊ := by simp
    _ ≤ x := Nat.floor_le hx0

/-- `2 + e⁵ < 151`. -/
theorem two_add_exp_five_lt : 2 + Real.exp 5 < 151 := by
  have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h2 : Real.exp 5 = Real.exp 1 ^ 5 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have h3 : Real.exp 1 ^ 5 < (2.7182818286 : ℝ) ^ 5 :=
    pow_lt_pow_left₀ h1 (Real.exp_pos 1).le (by norm_num)
  rw [h2]
  have : (2.7182818286 : ℝ) ^ 5 < 149 := by norm_num
  linarith

/-- The small part is negligible. -/
theorem norm_smallPart_le {N : ℕ} (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) :
    ‖smallPart N f‖ ≤ Real.log N * (N : ℝ) ^ ((3 : ℝ)⁻¹) := by
  unfold smallPart
  refine (norm_sum_le _ _).trans ?_
  calc ∑ n ∈ Icc 1 N, ‖(((if n ^ 3 ≤ N then ArithmeticFunction.vonMangoldt n else 0 : ℝ)) : ℂ) *
        f n‖ ≤ ∑ n ∈ Icc 1 N, (if n ^ 3 ≤ N then ArithmeticFunction.vonMangoldt n else 0) := by
        refine Finset.sum_le_sum fun n _ => ?_
        rw [norm_mul, Complex.norm_real]
        have h0 : 0 ≤ (if n ^ 3 ≤ N then ArithmeticFunction.vonMangoldt n else 0) := by
          split_ifs
          · exact ArithmeticFunction.vonMangoldt_nonneg
          · exact le_rfl
        rw [Real.norm_of_nonneg h0]
        exact mul_le_of_le_one_right h0 (hf n)
    _ = ∑ n ∈ (Icc 1 N).filter (fun n => n ^ 3 ≤ N), ArithmeticFunction.vonMangoldt n := by
        rw [Finset.sum_filter]
    _ ≤ ∑ _n ∈ (Icc 1 N).filter (fun n => n ^ 3 ≤ N), Real.log N := by
        refine Finset.sum_le_sum fun n hn => ?_
        have hnN : n ≤ N := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).2
        refine ArithmeticFunction.vonMangoldt_le_log.trans ?_
        have hn1 : 1 ≤ n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
        exact Real.log_le_log (by exact_mod_cast hn1) (by exact_mod_cast hnN)
    _ = ((Icc 1 N).filter fun n => n ^ 3 ≤ N).card * Real.log N := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ) ^ ((3 : ℝ)⁻¹) * Real.log N := by
        by_cases hN : N = 0
        · subst hN
          simp
        · exact mul_le_mul_of_nonneg_right (card_cube_le N) (Real.log_nonneg (by
            exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN))
    _ = Real.log N * (N : ℝ) ^ ((3 : ℝ)⁻¹) := mul_comm _ _

/-- The Brun error is bounded by the `L¹` norm of `Λ_{C,w} - Λ_{C,w}^{(k)}`. -/
theorem norm_brunErr_le {N w k : ℕ} (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) :
    ‖brunErr N w k f‖ ≤ ∑ n ∈ Icc 1 N, |cramerModel w (n : ℤ) - brunTrunc w k (n : ℤ)| := by
  unfold brunErr
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
  exact mul_le_of_le_one_right (abs_nonneg _) (hf n)

/-- Averaging over the cut-offs: if `ζ (1 + log N) ≤ ‖typeIPart‖`, then one of the cut-off type I
sums (`K = N` with coefficients `a_d`, or `K < N` with the Möbius weights) has norm `≥ ζ`. -/
theorem typeIPart_alt {N w k : ℕ} (f : ℕ → ℂ) {ζ : ℝ}
    (h : ζ * (1 + Real.log N) ≤ ‖typeIPart N w k f‖) :
    ζ ≤ ‖∑ d ∈ Icc 1 (cubeLevel N), (typeICoeff N w k d : ℂ) * dvdSum f d N‖ ∨
      ∃ K < N, ζ ≤ ‖∑ d ∈ Icc 1 (cubeLevel N), (moebiusCut N d : ℂ) * dvdSum f d K‖ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  unfold typeIPart at h
  have hB : ‖∑ K ∈ range N, (logStep K : ℂ) *
      ∑ d ∈ Icc 1 (cubeLevel N), (moebiusCut N d : ℂ) * dvdSum f d K‖ ≤ ζ * Real.log N := by
    calc _ ≤ ∑ K ∈ range N, ‖(logStep K : ℂ) *
          ∑ d ∈ Icc 1 (cubeLevel N), (moebiusCut N d : ℂ) * dvdSum f d K‖ := norm_sum_le _ _
      _ ≤ ∑ K ∈ range N, logStep K * ζ := by
          refine Finset.sum_le_sum fun K hK => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (logStep_nonneg K)]
          exact mul_le_mul_of_nonneg_left (h2 K (Finset.mem_range.mp hK)).le (logStep_nonneg K)
      _ = ζ * Real.log N := by
          rw [← Finset.sum_mul, sum_range_logStep, mul_comm]
  have hlog : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have := norm_sub_le (∑ d ∈ Icc 1 (cubeLevel N), (typeICoeff N w k d : ℂ) * dvdSum f d N)
    (∑ K ∈ range N, (logStep K : ℂ) *
      ∑ d ∈ Icc 1 (cubeLevel N), (moebiusCut N d : ℂ) * dvdSum f d K)
  linarith only [h, hB, h1, this]

/-- Sums over `[1, N] ⊆ ℤ` and over `[1, N] ⊆ ℕ` (cast to `ℤ`) agree. -/
theorem sum_Icc_int_natCast {M : Type*} [AddCommMonoid M] (g : ℤ → M) (N : ℕ) :
    ∑ n ∈ Finset.Icc (1 : ℤ) N, g n = ∑ n ∈ Icc 1 N, g (n : ℤ) := by
  refine Finset.sum_nbij' (fun z => z.toNat) (fun n => (n : ℤ)) ?_ ?_ ?_ ?_ ?_
  · intro z hz
    simp only [Finset.mem_Icc] at hz ⊢
    omega
  · intro n hn
    simp only [Finset.mem_Icc] at hn ⊢
    omega
  · intro z hz
    simp only [Finset.mem_Icc] at hz
    omega
  · intro n _
    simp
  · intro z hz
    simp only [Finset.mem_Icc] at hz
    congr 1
    omega

/-- The cut-off sum `∑_{n ≤ N', ℓ ∣ n} φ(n)` in the form `∑_{n ≤ ⌊N'/ℓ⌋} φ(ℓ n)` used by the type I
step. -/
theorem dvdSum_eq_floor_sum (φ : ℤ → ℂ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (N' : ℕ) :
    dvdSum (fun n : ℕ => φ (n : ℤ)) ℓ N' = ∑ n ∈ Icc 1 ⌊(N' : ℝ) / ℓ⌋₊, φ ((ℓ : ℤ) * n) := by
  rw [dvdSum_eq_sum_mul _ hℓ, Nat.floor_div_eq_div]
  exact Finset.sum_congr rfl fun n _ => by push_cast; rfl

/-- **The type I / type II dichotomy for `Λ - Λ_{C,w}`** (Leng23 Proposition
`p:type1type2correlation` with Vaughan's identity at `N^{1/3}` and the Brun truncation of `Λ_C`).
Let `φ : ℤ → ℂ` be bounded by `1` and supported on `[1, N]` (in the application
`φ = 1_P · star (T.eval)`), and suppose `‖∑_{n ≤ N} (Λ - Λ_{C,w})(n) φ(n)‖ ≥ η N`, the Brun
truncation `Λ_{C,w}^{(k)}` of level `w^k ≤ N^{2/3}` is `L¹`-close (`hbrun`, the output of
`cramer_brun_L1_Icc`) and `8 N^{1/3} log N ≤ η N` (`hsmall`). Then:

* (type I; the hypothesis `hI` of the type I step) there are a cut-off `N' ≤ N`, a scale
  `L ≤ N^{2/3}` and `≥ δ L` integers `ℓ ∈ (L/2, L]` with `‖∑_{n ≤ N'/ℓ} φ(ℓ n)‖ ≥ δ N/L`,
  `δ = η/(2^13 (1+log N)³)`; or
* (type II; the four-fold bound of the type II step) there are `N^{1/3} < L, M ≤ N^{2/3}` with
  `L M ∈ [η N/(16 (1+log N)⁵), 4 N)` and
  `fourFold φ (L/2, L] (M/2, M] ≥ η⁴ N²/(2^20 (1+log N)^18)`. -/
theorem vonMangoldt_sub_cramer_typeI_or_typeII
    {N w k : ℕ} (hN : 1 ≤ N) (hw : 2 ≤ w) (hwN : w ≤ N) (hlevel : (w ^ k) ^ 3 ≤ N ^ 2)
    {η : ℝ} (hη : 0 < η) (hsmall : 8 * Real.log N * (N : ℝ) ^ ((3 : ℝ)⁻¹) ≤ η * N)
    (hbrun : ∑ n ∈ Finset.Icc (1 : ℤ) N, |cramerModel w n - brunTrunc w k n| ≤ η * N / 8)
    (φ : ℤ → ℂ) (hφ : ∀ n, ‖φ n‖ ≤ 1) (hφN : ∀ n : ℤ, n ∉ Finset.Icc (1 : ℤ) N → φ n = 0)
    (hcorr : η * N ≤ ‖∑ n ∈ Icc 1 N,
      ((ArithmeticFunction.vonMangoldt n - cramerModel w (n : ℤ) : ℝ) : ℂ) * φ n‖) :
    (∃ N' ≤ N, ∃ L : ℕ, 1 ≤ L ∧ L ^ 3 ≤ N ^ 2 ∧ ∃ Λ' : Finset ℕ,
        (∀ ℓ ∈ Λ', (L : ℝ) / 2 < ℓ ∧ (ℓ : ℝ) ≤ L) ∧
        η / (2 ^ 13 * (1 + Real.log N) ^ 3) * L ≤ Λ'.card ∧
        ∀ ℓ ∈ Λ', η / (2 ^ 13 * (1 + Real.log N) ^ 3) * ((N : ℝ) / L) ≤
          ‖∑ n ∈ Icc 1 ⌊(N' : ℝ) / ℓ⌋₊, φ ((ℓ : ℤ) * n)‖) ∨
    (∃ L M : ℕ, N < L ^ 3 ∧ L ^ 3 ≤ N ^ 2 ∧ N < M ^ 3 ∧ M ^ 3 ≤ N ^ 2 ∧
        η / (16 * (1 + Real.log N) ^ 5) * N ≤ (L : ℝ) * M ∧ (L : ℝ) * M < 4 * N ∧
        η ^ 4 / (2 ^ 20 * (1 + Real.log N) ^ 18) * (N : ℝ) ^ 2 ≤
          fourFold (fun n : ℕ => φ (n : ℤ)) (dyadicBlock L) (dyadicBlock M)) := by
  set f : ℕ → ℂ := fun n => φ (n : ℤ) with hfdef
  have hf : ∀ n, ‖f n‖ ≤ 1 := fun n => hφ _
  have hf0 : ∀ n, N < n → f n = 0 := fun n hn => hφN _ (by
    simp only [Finset.mem_Icc, not_and, not_le]
    intro _
    exact_mod_cast hn)
  have hdec := correlation_decomposition hN (by omega : 1 ≤ w) hlevel f hf0
  have hcorr' : η * N ≤ ‖smallPart N f + brunErr N w k f + typeIPart N w k f +
      typeIIPart N f‖ := by
    rw [← hdec]
    exact hcorr
  have hs := norm_smallPart_le (N := N) f hf
  have hb := norm_brunErr_le (N := N) (w := w) (k := k) f hf
  rw [← sum_Icc_int_natCast (fun z : ℤ => |cramerModel w z - brunTrunc w k z|) N] at hb
  have hlogN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set lam : ℝ := 1 + Real.log N with hlam
  have hlam1 : 1 ≤ lam := le_add_of_nonneg_right hlogN
  have hlampos : 0 < lam := zero_lt_one.trans_le hlam1
  have hsum : η * N * 3 / 4 ≤ ‖typeIPart N w k f + typeIIPart N f‖ := by
    have h1 : ‖smallPart N f + brunErr N w k f + typeIPart N w k f + typeIIPart N f‖ ≤
        ‖smallPart N f‖ + ‖brunErr N w k f‖ + ‖typeIPart N w k f + typeIIPart N f‖ := by
      calc _ = ‖smallPart N f + brunErr N w k f + (typeIPart N w k f + typeIIPart N f)‖ := by
            rw [add_assoc _ (typeIPart N w k f)]
        _ ≤ ‖smallPart N f + brunErr N w k f‖ + ‖typeIPart N w k f + typeIIPart N f‖ :=
            norm_add_le _ _
        _ ≤ _ := by gcongr; exact norm_add_le _ _
    linarith
  have hD1 : 1 ≤ cubeLevel N := cubeLevel_pos hN
  have hDN : cubeLevel N ≤ N := cubeLevel_le N
  have hDpow : cubeLevel N ^ 3 ≤ N ^ 2 := cubeLevel_pow_le hN
  have hJ := log_two_le hD1 hDN
  have hJpos : (0 : ℝ) < ((Nat.log 2 (cubeLevel N) + 1 : ℕ) : ℝ) := by positivity
  by_cases hI : η * N / 4 ≤ ‖typeIPart N w k f‖
  · -- type I
    left
    set ζ : ℝ := η * N / 4 / lam with hζ
    have hζpos : 0 < ζ := by positivity
    have hIζ : ζ * lam ≤ ‖typeIPart N w k f‖ := by
      rw [hζ, div_mul_cancel₀ _ hlampos.ne']
      exact hI
    set A : ℝ := (2 + Real.exp 5) * lam with hA
    have hApos : 0 < A := by positivity
    have h151 := two_add_exp_five_lt
    have hkey : ∀ (a : ℕ → ℝ) (N' : ℕ), N' ≤ N →
        (∀ d ∈ Icc 1 (cubeLevel N), |a d| ≤ A) →
        ζ ≤ ‖∑ d ∈ Icc 1 (cubeLevel N), (a d : ℂ) * dvdSum f d N'‖ →
        ∃ N' ≤ N, ∃ L : ℕ, 1 ≤ L ∧ L ^ 3 ≤ N ^ 2 ∧ ∃ Λ' : Finset ℕ,
          (∀ ℓ ∈ Λ', (L : ℝ) / 2 < ℓ ∧ (ℓ : ℝ) ≤ L) ∧
          η / (2 ^ 13 * lam ^ 3) * L ≤ Λ'.card ∧
          ∀ ℓ ∈ Λ', η / (2 ^ 13 * lam ^ 3) * ((N : ℝ) / L) ≤
            ‖∑ n ∈ Icc 1 ⌊(N' : ℝ) / ℓ⌋₊, φ ((ℓ : ℤ) * n)‖ := by
      intro a N' hN' hA' h
      obtain ⟨L, hL1, hLD, Ls, hLs, hcard, hval⟩ := typeI_extract f N (cubeLevel N) hD1 hDpow
        (fun n _ => hf n) (fun d => (a d : ℂ)) hApos (fun d hd => by
          rw [Complex.norm_real, Real.norm_eq_abs]
          exact hA' d hd) hN' hζpos h
      have hδ : η / (2 ^ 13 * lam ^ 3) ≤
          ζ / (4 * N * A * ((Nat.log 2 (cubeLevel N) + 1 : ℕ) : ℝ)) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have h1 : (2 + Real.exp 5) * ((Nat.log 2 (cubeLevel N) + 1 : ℕ) : ℝ) ≤ 151 * (2 * lam) :=
          mul_le_mul h151.le hJ hJpos.le (by norm_num)
        have h2 : ζ * (2 ^ 13 * lam ^ 3) = 2048 * η * N * lam ^ 2 := by
          rw [hζ]
          field_simp
          ring
        rw [h2, hA]
        have h3 : η * (4 * N * ((2 + Real.exp 5) * lam) *
            ((Nat.log 2 (cubeLevel N) + 1 : ℕ) : ℝ)) =
            4 * η * N * lam * ((2 + Real.exp 5) * ((Nat.log 2 (cubeLevel N) + 1 : ℕ) : ℝ)) := by
          ring
        rw [h3]
        calc 4 * η * N * lam * ((2 + Real.exp 5) * ((Nat.log 2 (cubeLevel N) + 1 : ℕ) : ℝ))
            ≤ 4 * η * N * lam * (151 * (2 * lam)) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
          _ ≤ 2048 * η * N * lam ^ 2 := by
              have hprod : 0 < η * N * lam ^ 2 := by positivity
              linarith only [hprod]
      refine ⟨N', hN', L, hL1, (Nat.pow_le_pow_left hLD 3).trans hDpow, Ls,
        fun ℓ hℓ => mem_dyadicBlock.mp (hLs hℓ), ?_, ?_⟩
      · exact (mul_le_mul_of_nonneg_right hδ (Nat.cast_nonneg L)).trans hcard
      · intro ℓ hℓ
        have hℓ1 : 1 ≤ ℓ := by
          have := (mem_dyadicBlock.mp (hLs hℓ)).1
          have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
          have : (0 : ℝ) < ℓ := lt_of_le_of_lt (by positivity) this
          exact_mod_cast this
        rw [← dvdSum_eq_floor_sum φ hℓ1 N']
        exact (mul_le_mul_of_nonneg_right hδ (by positivity)).trans (hval ℓ hℓ)
    rcases typeIPart_alt f hIζ with h | ⟨K, hK, h⟩
    · refine hkey (typeICoeff N w k) N le_rfl (fun d hd => ?_) h
      have hd' := Finset.mem_Icc.mp hd
      have := abs_typeICoeff_le (k := k) hw hwN (hd'.2.trans hDN) hd'.1
      refine this.trans ?_
      rw [hA, hlam]
      exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) (by positivity)
    · refine hkey (moebiusCut N) K hK.le (fun d _ => ?_) h
      refine (abs_moebiusCut_le N d).trans ?_
      rw [hA]
      exact one_le_mul_of_one_le_of_one_le
        ((by norm_num : (1 : ℝ) ≤ 2).trans (le_add_of_nonneg_right (Real.exp_pos 5).le)) hlam1
  · -- type II
    right
    have hII : η * N / 4 ≤ ‖typeIIPart N f‖ := by
      have := norm_add_le (typeIPart N w k f) (typeIIPart N f)
      push Not at hI
      have h5 := mul_pos hη hNpos
      linarith only [hsum, hI, h5, this]
    obtain ⟨L, M, hNL, hL3, hNM, hM3, hLM, hLM4, hF⟩ := typeII_extract f N (cubeLevel N) hD1
      hDpow hf hf0
      (fun c => (typeIICoeffA N c : ℂ)) (fun w => (typeTwoCoeff N w : ℂ)) (A := lam) hlampos
      (fun c hc => by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact (abs_typeIICoeffA_le hN ((Finset.mem_Icc.mp hc).2.trans hDN)).trans
          (by rw [hlam]; exact le_add_of_nonneg_left zero_le_one))
      (fun w _ => by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact abs_typeTwoCoeff_le N w)
      (fun c hc => by
        by_contra hle
        refine hc ?_
        unfold typeIICoeffA
        rw [ite_eq_right_iff.mpr (fun h => absurd h hle)]
        simp)
      (fun w hw0 => by
        by_contra hle
        exact hw0 (by rw [typeTwoCoeff_eq_zero (not_lt.mp hle)]; simp))
      (ξ := η * N / 4) (by positivity) hII
    refine ⟨L, M, hNL, hL3, hNM, hM3, ?_, hLM4, ?_⟩
    · refine le_trans ?_ hLM
      rw [le_div_iff₀ (by positivity)]
      have hJ2 : ((Nat.log 2 (cubeLevel N) + 1 : ℕ) : ℝ) ^ 2 ≤ (2 * lam) ^ 2 :=
        pow_le_pow_left₀ hJpos.le hJ 2
      calc η / (16 * lam ^ 5) * N * (((Nat.log 2 (cubeLevel N) + 1 : ℕ) : ℝ) ^ 2 * lam * lam ^ 2)
          ≤ η / (16 * lam ^ 5) * N * ((2 * lam) ^ 2 * lam * lam ^ 2) := by gcongr
        _ = η * N / 4 := by field_simp; ring
    · refine le_trans ?_ hF
      set J : ℝ := ((Nat.log 2 (cubeLevel N) + 1 : ℕ) : ℝ) with hJdef
      have hJ2 : J ^ 2 ≤ (2 * lam) ^ 2 := pow_le_pow_left₀ hJpos.le hJ 2
      have hq : η * N / (16 * lam ^ 2) ≤ η * N / 4 / J ^ 2 := by
        rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
        calc η * N * (4 * J ^ 2) ≤ η * N * (4 * (2 * lam) ^ 2) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hJ2 (by norm_num))
                (by positivity)
          _ = η * N * (16 * lam ^ 2) := by ring
      have hq4 : (η * N / (16 * lam ^ 2)) ^ 4 ≤ (η * N / 4 / J ^ 2) ^ 4 :=
        pow_le_pow_left₀ (by positivity) hq 4
      calc η ^ 4 / (2 ^ 20 * lam ^ 18) * (N : ℝ) ^ 2
          = (η * N / (16 * lam ^ 2)) ^ 4 / (16 * lam ^ 4 * lam ^ 6 * (N : ℝ) ^ 2) := by
            field_simp
            ring
        _ ≤ (η * N / 4 / J ^ 2) ^ 4 / (16 * lam ^ 4 * lam ^ 6 * (N : ℝ) ^ 2) :=
            div_le_div_of_nonneg_right hq4 (by positivity)

/-- **The pigeonhole of the type II step, in the form of the type II conclusion**: a four-fold bound
`x N² ≤ fourFold f (L/2, L] (M/2, M]` with `L M < 4 N`, `0 < x ≤ 1` for a function bounded by `1`
yields `≥ (x/32) L²` pairs `(ℓ, ℓ')` of `(L/2, L]` with
`‖∑_{m ∈ (M/2, M]} f(ℓ m) conj f(ℓ' m)‖ ≥ (x/8) M`. -/
theorem typeII_pairs (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) {N L M : ℕ} (hM : 1 ≤ M) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x ≤ 1) (hLM : (L : ℝ) * M < 4 * N)
    (hF : x * (N : ℝ) ^ 2 ≤ fourFold f (dyadicBlock L) (dyadicBlock M)) :
    ∃ P ⊆ dyadicBlock L ×ˢ dyadicBlock L, x / 32 * (L : ℝ) ^ 2 ≤ P.card ∧
      ∀ p ∈ P, x / 8 * M ≤ ‖∑ m ∈ dyadicBlock M, f (p.1 * m) * (starRingEnd ℂ) (f (p.2 * m))‖ := by
  obtain ⟨P, hP, hcard, hval⟩ := exists_pairs_of_fourFold f hf (dyadicBlock L) (dyadicBlock M)
    (X := x * (N : ℝ) ^ 2) (θ := x / 8 * M) hF
  refine ⟨P, hP, ?_, hval⟩
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hcL : ((dyadicBlock L).card : ℝ) ≤ L := by exact_mod_cast card_dyadicBlock_le L
  have hcM : ((dyadicBlock M).card : ℝ) ≤ M := by exact_mod_cast card_dyadicBlock_le M
  have hLM0 : (0 : ℝ) ≤ (L : ℝ) * M := by positivity
  have hLM2 : ((L : ℝ) * M) ^ 2 ≤ 16 * (N : ℝ) ^ 2 := by
    calc ((L : ℝ) * M) ^ 2 ≤ (4 * (N : ℝ)) ^ 2 := pow_le_pow_left₀ hLM0 hLM.le 2
      _ = 16 * (N : ℝ) ^ 2 := by ring
  have h1 : ((dyadicBlock L).card : ℝ) ^ 2 * (x / 8 * M) ^ 2 ≤ x * (N : ℝ) ^ 2 / 4 := by
    calc ((dyadicBlock L).card : ℝ) ^ 2 * (x / 8 * M) ^ 2 ≤ (L : ℝ) ^ 2 * (x / 8 * M) ^ 2 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hcL 2) (sq_nonneg _)
      _ = x ^ 2 * ((L : ℝ) * M) ^ 2 / 64 := by ring
      _ ≤ x ^ 2 * (16 * (N : ℝ) ^ 2) / 64 := by gcongr
      _ = x ^ 2 * (N : ℝ) ^ 2 / 4 := by ring
      _ ≤ x * (N : ℝ) ^ 2 / 4 := by
          have h5 : x ^ 2 ≤ x := pow_le_of_le_one hx0.le hx1 two_ne_zero
          have h6 := mul_le_mul_of_nonneg_right h5 (sq_nonneg (N : ℝ))
          linarith only [h6]
  have h2 : x * (N : ℝ) ^ 2 / 2 ≤ (P.card : ℝ) * (M : ℝ) ^ 2 := by
    have hcM2 : (P.card : ℝ) * ((dyadicBlock M).card : ℝ) ^ 2 ≤ (P.card : ℝ) * (M : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hcM 2) (Nat.cast_nonneg _)
    have : 0 ≤ x * (N : ℝ) ^ 2 := by positivity
    linarith
  have h3 : x / 32 * (L : ℝ) ^ 2 * (M : ℝ) ^ 2 ≤ (P.card : ℝ) * (M : ℝ) ^ 2 := by
    have : x / 32 * (L : ℝ) ^ 2 * (M : ℝ) ^ 2 = x / 32 * ((L : ℝ) * M) ^ 2 := by ring
    rw [this]
    have h4 : x / 32 * ((L : ℝ) * M) ^ 2 ≤ x / 32 * (16 * (N : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hLM2 (by positivity)
    linarith
  exact le_of_mul_le_mul_right h3 (by positivity)

/-- **The dichotomy with the numeric Brun bound** of `cramer_brun_L1_Icc` in place of the abstract
`L¹` hypothesis. -/
theorem vonMangoldt_sub_cramer_typeI_or_typeII_of_brun
    {N w k : ℕ} (hN : 1 ≤ N) (hw : 2 ≤ w) (hwN : w ≤ N) (hlevel : (w ^ k) ^ 3 ≤ N ^ 2)
    {η : ℝ} (hη : 0 < η) (hsmall : 8 * Real.log N * (N : ℝ) ^ ((3 : ℝ)⁻¹) ≤ η * N)
    (hbrun : Real.exp 5 * Real.log w *
      ((N : ℝ) * (Real.exp 1 * (Real.log (Real.log w) + 4) / ((k + 1 : ℕ) : ℝ)) ^ (k + 1) +
        (w : ℝ) ^ (k + 1)) ≤ η * N / 8)
    (φ : ℤ → ℂ) (hφ : ∀ n, ‖φ n‖ ≤ 1) (hφN : ∀ n : ℤ, n ∉ Finset.Icc (1 : ℤ) N → φ n = 0)
    (hcorr : η * N ≤ ‖∑ n ∈ Icc 1 N,
      ((ArithmeticFunction.vonMangoldt n - cramerModel w (n : ℤ) : ℝ) : ℂ) * φ n‖) :
    (∃ N' ≤ N, ∃ L : ℕ, 1 ≤ L ∧ L ^ 3 ≤ N ^ 2 ∧ ∃ Λ' : Finset ℕ,
        (∀ ℓ ∈ Λ', (L : ℝ) / 2 < ℓ ∧ (ℓ : ℝ) ≤ L) ∧
        η / (2 ^ 13 * (1 + Real.log N) ^ 3) * L ≤ Λ'.card ∧
        ∀ ℓ ∈ Λ', η / (2 ^ 13 * (1 + Real.log N) ^ 3) * ((N : ℝ) / L) ≤
          ‖∑ n ∈ Icc 1 ⌊(N' : ℝ) / ℓ⌋₊, φ ((ℓ : ℤ) * n)‖) ∨
    (∃ L M : ℕ, N < L ^ 3 ∧ L ^ 3 ≤ N ^ 2 ∧ N < M ^ 3 ∧ M ^ 3 ≤ N ^ 2 ∧
        η / (16 * (1 + Real.log N) ^ 5) * N ≤ (L : ℝ) * M ∧ (L : ℝ) * M < 4 * N ∧
        η ^ 4 / (2 ^ 20 * (1 + Real.log N) ^ 18) * (N : ℝ) ^ 2 ≤
          fourFold (fun n : ℕ => φ (n : ℤ)) (dyadicBlock L) (dyadicBlock M)) :=
  vonMangoldt_sub_cramer_typeI_or_typeII hN hw hwN hlevel hη hsmall
    ((cramer_brun_L1_Icc w k N hw).trans hbrun) φ hφ hφN hcorr

end PrimeCarleson.Proof.Fplus31
