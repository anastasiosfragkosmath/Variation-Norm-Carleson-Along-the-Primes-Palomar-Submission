module

public import PrimeCarleson.Proof.Oplus.External.THMaximal

/-!
# Sparsity of `F` near a scale of `Ω_λ` ([O+] L2510-L2512)

Source: [O+] `tileslargemaxprop`, L2510–L2512 (and L2487-L2490): `Ω_λ = {M[1_F] > λ}` (the
Hardy–Littlewood maximal function, `maxSuperlevel` of `External/THMaximal.lean`), `I_ℓ` a dyadic
interval with `2^ℓ I_ℓ ⊂ Ω_λ` and `2^{ℓ+1} I_ℓ ⊄ Ω_λ` (display `(2lIOmega)`). "Since `2^{ℓ+1} I_ℓ`
is not contained in `Ω_λ`, we have `|F ∩ 2^{j+1} I_ℓ| ≤ C 2^{max(ℓ,j)} |I_ℓ| λ` for each `j`."

* `volume_inter_Icc_le_of_not_subset`: for every `n`, the closed interval
  `[c(I) - 2^n |I|, c(I) + 2^n |I|]` has `|F ∩ ·| ≤ 2 λ 2^{max(ℓ,n)} |I|`;
* `volume_inter_dilate_le_of_not_subset`: the printed form, with `C = 2`;
* `integral_weight_inter_le_of_not_subset`: the weighted form
  `∫_F (1 + |y - c(I)|/|I|)^{-2} dy ≤ 16 λ 2^ℓ |I|` (Section E of `External/THMaximal.lean`), the
  form used for the sup bound and the `ℓ²` bound of the coefficients.

The dilate `2^{j+1} I` is `Ico (c - 2^j |I|) (c + 2^j |I|)` (`Dyadic.dilate_two_pow_succ`).
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

/-- The dilate `2^{j+1} I` is `[c(I) - 2^j |I|, c(I) + 2^j |I|)`. -/
theorem Dyadic.dilate_two_pow_succ (I : Dyadic) (j : ℕ) :
    I.dilate ((2 : ℝ) ^ (j + 1)) =
      Ico (I.center - 2 ^ j * I.length) (I.center + 2 ^ j * I.length) := by
  unfold Dyadic.dilate
  rw [pow_succ]
  congr 1 <;> ring

/-- A point of `2^{ℓ+1} I` is at distance at most `2^ℓ |I|` from the center of `I`. -/
theorem Dyadic.abs_sub_center_le_of_mem_dilate_succ {I : Dyadic} {ℓ : ℕ} {x : ℝ}
    (hx : x ∈ I.dilate ((2 : ℝ) ^ (ℓ + 1))) : |x - I.center| ≤ 2 ^ ℓ * I.length := by
  rw [Dyadic.dilate_two_pow_succ] at hx
  obtain ⟨h1, h2⟩ := hx
  rw [abs_le]
  constructor <;> linarith

/-- The dilate `2^{j+1} I` lies in the closed interval `[c(I) - 2^j |I|, c(I) + 2^j |I|]`. -/
theorem Dyadic.dilate_two_pow_succ_subset_Icc (I : Dyadic) (j : ℕ) :
    I.dilate ((2 : ℝ) ^ (j + 1)) ⊆
      Icc (I.center - 2 ^ j * I.length) (I.center + 2 ^ j * I.length) := by
  rw [Dyadic.dilate_two_pow_succ]
  exact Ico_subset_Icc_self

variable {F : Set ℝ} {lam : ℝ} {I : Dyadic} {ℓ : ℕ}

/-- **The sparsity of `F` near a scale** ([O+] L2510-L2512; closed-interval form): if
`2^{ℓ+1} I ⊄ Ω_λ` then `|F ∩ [c - 2^n |I|, c + 2^n |I|]| ≤ 2 λ 2^{max(ℓ,n)} |I|` for every `n`. -/
theorem volume_inter_Icc_le_of_not_subset (hF : MeasurableSet F) (hlam : 0 ≤ lam)
    (h : ¬ I.dilate ((2 : ℝ) ^ (ℓ + 1)) ⊆ maxSuperlevel F lam) (n : ℕ) :
    volume (F ∩ Icc (I.center - 2 ^ n * I.length) (I.center + 2 ^ n * I.length)) ≤
      ENNReal.ofReal (2 * lam * 2 ^ (max ℓ n) * I.length) := by
  obtain ⟨x₀, hx₀, hx₀Ω⟩ := Set.not_subset.1 h
  have hL := I.length_pos
  have hx := Dyadic.abs_sub_center_le_of_mem_dilate_succ hx₀
  rw [abs_le] at hx
  by_cases hn : ℓ ≤ n
  · -- the interval already contains `x₀`
    have h2 : (2 : ℝ) ^ ℓ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
    have h3 : (2 : ℝ) ^ ℓ * I.length ≤ 2 ^ n * I.length := by gcongr
    have hab : I.center - 2 ^ n * I.length < I.center + 2 ^ n * I.length := by
      have : (0 : ℝ) < 2 ^ n := by positivity
      nlinarith
    have := volume_inter_Icc_le_of_notMem hF hlam hx₀Ω (by linarith [hx.1])
      (by linarith [hx.2]) hab
    rw [max_eq_right hn]
    refine this.trans (le_of_eq ?_)
    congr 1
    ring
  · have hn' : n ≤ ℓ := (not_le.1 hn).le
    have h2 : (2 : ℝ) ^ n ≤ 2 ^ ℓ := pow_le_pow_right₀ (by norm_num) hn'
    have h3 : (2 : ℝ) ^ n * I.length ≤ 2 ^ ℓ * I.length := by gcongr
    have hab : I.center - 2 ^ ℓ * I.length < I.center + 2 ^ ℓ * I.length := by
      have : (0 : ℝ) < 2 ^ ℓ := by positivity
      nlinarith
    have h4 := volume_inter_Icc_le_of_notMem hF hlam hx₀Ω (by linarith [hx.1])
      (by linarith [hx.2]) hab
    have h5 : F ∩ Icc (I.center - 2 ^ n * I.length) (I.center + 2 ^ n * I.length) ⊆
        F ∩ Icc (I.center - 2 ^ ℓ * I.length) (I.center + 2 ^ ℓ * I.length) :=
      inter_subset_inter_right _ (Icc_subset_Icc (by linarith) (by linarith))
    rw [max_eq_left hn']
    refine (measure_mono h5).trans (h4.trans (le_of_eq ?_))
    congr 1
    ring

/-- **The sparsity of `F` near a scale** ([O+] L2510-L2512; the printed form, `C = 2`): if
`2^{ℓ+1} I ⊄ Ω_λ` then `|F ∩ 2^{j+1} I| ≤ 2 · 2^{max(ℓ,j)} |I| λ` for every `j ≥ 0`. -/
theorem volume_inter_dilate_le_of_not_subset (hF : MeasurableSet F) (hlam : 0 ≤ lam)
    (h : ¬ I.dilate ((2 : ℝ) ^ (ℓ + 1)) ⊆ maxSuperlevel F lam) (j : ℕ) :
    volume (F ∩ I.dilate ((2 : ℝ) ^ (j + 1))) ≤
      ENNReal.ofReal (2 * lam * 2 ^ (max ℓ j) * I.length) :=
  (measure_mono (inter_subset_inter_right _ (I.dilate_two_pow_succ_subset_Icc j))).trans
    (volume_inter_Icc_le_of_not_subset hF hlam h j)

/-- `2^{max(ℓ,n)} ≤ 2^ℓ 2^n`. -/
theorem two_pow_max_le (ℓ n : ℕ) : (2 : ℝ) ^ (max ℓ n) ≤ 2 ^ ℓ * 2 ^ n := by
  rcases le_total ℓ n with hn | hn
  · rw [max_eq_right hn]
    have : (1 : ℝ) ≤ 2 ^ ℓ := one_le_pow₀ (by norm_num)
    have h2 : (0 : ℝ) < 2 ^ n := by positivity
    nlinarith
  · rw [max_eq_left hn]
    have : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    have h2 : (0 : ℝ) < 2 ^ ℓ := by positivity
    nlinarith

/-- The bound of the form used by Section E of `External/THMaximal.lean`:
`|F ∩ [c - 2^n |I|, c + 2^n |I|]| ≤ (2^ℓ λ) · 2 · (2^n |I|)`. -/
theorem volume_inter_Icc_le_mul (hF : MeasurableSet F) (hlam : 0 ≤ lam)
    (h : ¬ I.dilate ((2 : ℝ) ^ (ℓ + 1)) ⊆ maxSuperlevel F lam) (n : ℕ) :
    volume (F ∩ Icc (I.center - 2 ^ n * I.length) (I.center + 2 ^ n * I.length)) ≤
      ENNReal.ofReal (2 ^ ℓ * lam * (2 * (2 ^ n * I.length))) := by
  refine (volume_inter_Icc_le_of_not_subset hF hlam h n).trans (ENNReal.ofReal_le_ofReal ?_)
  have hL := I.length_pos
  have h1 := two_pow_max_le ℓ n
  have h3 : 0 ≤ 2 * lam * I.length := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h1 h3]

/-- **The weighted mass of `F` near a scale**: if `2^{ℓ+1} I ⊄ Ω_λ` then
`∫_F (1 + |y - c(I)|/|I|)^{-2} dy ≤ 16 · 2^ℓ λ |I|`. -/
theorem integral_weight_inter_le_of_not_subset (hF : MeasurableSet F) (hlam : 0 ≤ lam)
    (h : ¬ I.dilate ((2 : ℝ) ^ (ℓ + 1)) ⊆ maxSuperlevel F lam) :
    ∫ y in F, (1 + |y - I.center| / I.length) ^ (-2 : ℤ) ≤ 16 * (2 ^ ℓ * lam) * I.length :=
  integral_indicator_mul_weight_le (by positivity) I.length_pos
    (fun n => volume_inter_Icc_le_mul hF hlam h n)

end PrimeCarleson.Proof.Oplus
