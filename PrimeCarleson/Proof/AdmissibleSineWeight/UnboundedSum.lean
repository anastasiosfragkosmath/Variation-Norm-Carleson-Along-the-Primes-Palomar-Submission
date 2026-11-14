module

public import PrimeCarleson.Frozen.CarlesonMax
public import PrimeCarleson.Frozen.SineWeight
import PrimeCarleson.Proof.AdmissibleSineWeight.UnboundedAbel
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Logarithmic lower bound for the sine-weighted maximal operator

Helper file for the unboundedness half of the Appendix A.1 lemma
(`PrimeCarleson.admissible_sineWeight_carleson_unbounded`).

For `0 < α < 1` and `q₀ ≥ 3` we test `𝒞_v` with `v = sineWeight α q₀` on the indicator
`1_{[-4K, 4K]}` of an interval, with the frequency `λ = 1 / q₀`. For `|x| ≤ K` the terms with
`|n| ≤ 3K` of the modulated sum are `v(|n|) e(n / q₀) / n`; pairing `n` with `-n` the imaginary
part of the sum is `2 ∑_{m ≤ 3K} v(m) sin(2π m / q₀) / m`, up to an error of at most `4 / 3`
from the terms `3K < |n| ≤ 5K`. Writing `sin² = (1 - cos 2·) / 2` and using the bounded sums of
`UnboundedAbel`, this is at least `α log (3K + 1) - C`, where `C` depends only on `α` and `q₀`.

Main result: `PrimeCarleson.Proof.exists_carlesonMax_lower`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PrimeCarleson.Proof

/-- The test function `1_{[-L, L]}`. -/
def unboundedTest (L : ℕ) : ℤ →₀ ℂ :=
  Finsupp.indicator (Finset.Icc (-(L : ℤ)) L) fun _ _ => 1

/-- The summand `v(m) sin(2π m/q₀)/m` of the imaginary part. -/
def sineTerm (α : ℝ) (q₀ m : ℕ) : ℝ :=
  (1 + α * Real.sin (2 * Real.pi * m / q₀)) * Real.sin (2 * Real.pi * m / q₀) / m

/-- Pointwise values of the test function. -/
theorem unboundedTest_apply (L : ℕ) (n : ℤ) :
    unboundedTest L n = if n ∈ Finset.Icc (-(L : ℤ)) L then 1 else 0 := by
  simp [unboundedTest, Finsupp.indicator_apply]

/-- The imaginary part of `w e(t) / n` for real `w`, `t`. -/
theorem im_term (w t : ℝ) (n : ℤ) :
    (((w : ℂ)) * e t / (n : ℂ)).im = w * Real.sin (2 * Real.pi * t) / n := by
  have : (w : ℂ) * e t / (n : ℂ) =
      ((w / n : ℝ) : ℂ) * Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) := by
    simp only [e]
    push_cast
    ring_nf
  rw [this, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
  ring

/-- The imaginary part of the `n`-th summand, in terms of the even function `sineTerm`. -/
theorem sineWeight_natAbs_mul (α : ℝ) (q₀ : ℕ) (n : ℤ) :
    sineWeight α q₀ n.natAbs * Real.sin (2 * Real.pi * (1 / q₀ * n)) / n =
      sineTerm α q₀ n.natAbs := by
  obtain ⟨m, rfl | rfl⟩ : ∃ m : ℕ, n = m ∨ n = -m := ⟨n.natAbs, Int.natAbs_eq n⟩
  · have : 2 * Real.pi * (1 / (q₀ : ℝ) * (m : ℝ)) = 2 * Real.pi * m / q₀ := by ring
    simp only [Int.natAbs_natCast, sineWeight, sineTerm, this, Int.cast_natCast]
  · have : 2 * Real.pi * (1 / (q₀ : ℝ) * -(m : ℝ)) = -(2 * Real.pi * m / q₀) := by ring
    simp only [Int.natAbs_neg, Int.natAbs_natCast, sineWeight, sineTerm, Int.cast_neg,
      Int.cast_natCast]
    rw [this, Real.sin_neg, mul_neg, neg_div_neg_eq]

/-- The imaginary part of the modulated sum of the test function at frequency `1 / q₀`. -/
theorem im_modulatedSum_unboundedTest (α : ℝ) (q₀ L : ℕ) (x : ℤ) :
    (modulatedSum (sineWeight α q₀) (unboundedTest L) (1 / q₀) x).im =
      ∑ n ∈ Finset.Icc (x - L) (x + L), sineTerm α q₀ n.natAbs := by
  unfold modulatedSum
  rw [tsum_eq_sum (s := Finset.Icc (x - L) (x + L))]
  · rw [Complex.im_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_Icc] at hn
    by_cases h0 : n = 0
    · simp [h0, sineTerm]
    · have hmem : x - n ∈ Finset.Icc (-(L : ℤ)) L := by
        rw [Finset.mem_Icc]; omega
      simp only [h0, ↓reduceIte, unboundedTest_apply, hmem, one_mul]
      rw [im_term, sineWeight_natAbs_mul]
  · intro n hn
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
    by_cases h0 : n = 0
    · simp [h0]
    · have hmem : x - n ∉ Finset.Icc (-(L : ℤ)) L := by
        rw [Finset.mem_Icc]; omega
      simp [h0, unboundedTest_apply, hmem]

/-- Pairing `n` with `-n` in a symmetric sum of an even function. -/
theorem sum_Icc_natAbs (F : ℕ → ℝ) (M : ℕ) :
    ∑ n ∈ Finset.Icc (-(M : ℤ)) M, F n.natAbs = F 0 + 2 * ∑ m ∈ Finset.range M, F (m + 1) := by
  induction M with
  | zero => simp
  | succ M ih =>
    have hset : Finset.Icc (-((M + 1 : ℕ) : ℤ)) ((M + 1 : ℕ) : ℤ) =
        insert (-((M + 1 : ℕ) : ℤ)) (insert ((M + 1 : ℕ) : ℤ) (Finset.Icc (-(M : ℤ)) M)) := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have h1 : ((M + 1 : ℕ) : ℤ) ∉ Finset.Icc (-(M : ℤ)) M := by
      simp only [Finset.mem_Icc]; omega
    have h2 : (-((M + 1 : ℕ) : ℤ)) ∉ insert ((M + 1 : ℕ) : ℤ) (Finset.Icc (-(M : ℤ)) M) := by
      simp only [Finset.mem_insert, Finset.mem_Icc]; omega
    rw [hset, Finset.sum_insert h2, Finset.sum_insert h1, ih, Finset.sum_range_succ]
    simp only [Int.natAbs_neg, Int.natAbs_natCast]
    ring

/-- The trivial bound `|sineTerm m| ≤ 2 / m`. -/
theorem abs_sineTerm_le (α : ℝ) (hα : |α| ≤ 1) (q₀ m : ℕ) (hm : 1 ≤ m) :
    |sineTerm α q₀ m| ≤ 2 / m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  unfold sineTerm
  rw [abs_div, abs_of_pos hm0]
  refine div_le_div_of_nonneg_right ?_ hm0.le
  rw [abs_mul]
  have hs : |Real.sin (2 * Real.pi * m / q₀)| ≤ 1 := Real.abs_sin_le_one _
  have h1 : |1 + α * Real.sin (2 * Real.pi * m / q₀)| ≤ 2 := by
    calc _ ≤ |(1 : ℝ)| + |α * Real.sin (2 * Real.pi * m / q₀)| := abs_add_le _ _
      _ ≤ 1 + 1 * 1 := by
        rw [abs_one, abs_mul]
        gcongr
      _ = 2 := by norm_num
  calc |1 + α * Real.sin (2 * Real.pi * m / q₀)| * |Real.sin (2 * Real.pi * m / q₀)|
      ≤ 2 * 1 := by gcongr
    _ = 2 := by norm_num

/-- Splitting `sin²` as `(1 - cos 2·) / 2`. -/
theorem sineTerm_succ_eq (α : ℝ) (q₀ m : ℕ) :
    sineTerm α q₀ (m + 1) =
      Real.sin (2 * Real.pi * ((m : ℝ) + 1) / q₀) / ((m : ℝ) + 1) +
        α / 2 * (1 / ((m : ℝ) + 1)) -
        α / 2 * (Real.cos (4 * Real.pi * ((m : ℝ) + 1) / q₀) / ((m : ℝ) + 1)) := by
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  set x : ℝ := 2 * Real.pi * ((m : ℝ) + 1) / q₀ with hx
  have h4 : 4 * Real.pi * ((m : ℝ) + 1) / q₀ = 2 * x := by rw [hx]; ring
  have hc : Real.cos (2 * x) = 1 - 2 * Real.sin x ^ 2 := by
    rw [Real.cos_two_mul, Real.cos_sq']; ring
  unfold sineTerm
  push_cast
  rw [h4, hc, ← hx]
  field_simp
  ring

/-- Lower bound for the one-sided sum of `sineTerm`: `(α / 2) log (M + 1) - O(1)`. -/
theorem sum_sineTerm_lower (α : ℝ) (hα : 0 ≤ α) (q₀ : ℕ) (B : ℝ)
    (hB : ∀ M : ℕ,
      |∑ m ∈ Finset.range M, Real.sin (2 * Real.pi * ((m : ℝ) + 1) / q₀) / ((m : ℝ) + 1)| ≤ B ∧
      |∑ m ∈ Finset.range M, Real.cos (4 * Real.pi * ((m : ℝ) + 1) / q₀) / ((m : ℝ) + 1)| ≤ B)
    (M : ℕ) :
    α / 2 * Real.log ((M : ℝ) + 1) - (1 + α / 2) * B ≤
      ∑ m ∈ Finset.range M, sineTerm α q₀ (m + 1) := by
  have hharm : Real.log ((M : ℝ) + 1) ≤ ∑ m ∈ Finset.range M, 1 / ((m : ℝ) + 1) := by
    have h := log_add_one_le_harmonic M
    have h' : (harmonic M : ℝ) = ∑ m ∈ Finset.range M, 1 / ((m : ℝ) + 1) := by
      simp [harmonic]
    rw [← h']
    simpa using h
  simp_rw [sineTerm_succ_eq, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  obtain ⟨h1, h2⟩ := hB M
  have h1' := (abs_le.1 h1).1
  have h2' := (abs_le.1 h2).2
  have h3 : α / 2 * Real.log ((M : ℝ) + 1) ≤
      α / 2 * ∑ m ∈ Finset.range M, 1 / ((m : ℝ) + 1) := by gcongr
  have h4 : α / 2 * ∑ m ∈ Finset.range M, Real.cos (4 * Real.pi * ((m : ℝ) + 1) / q₀) /
      ((m : ℝ) + 1) ≤ α / 2 * B := by gcongr
  nlinarith

/-- Lower bound for the imaginary part on the window `[x - 4K, x + 4K]`, `|x| ≤ K`. -/
theorem sum_Icc_lower (α : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1) (q₀ : ℕ) (B : ℝ)
    (hB : ∀ M : ℕ,
      |∑ m ∈ Finset.range M, Real.sin (2 * Real.pi * ((m : ℝ) + 1) / q₀) / ((m : ℝ) + 1)| ≤ B ∧
      |∑ m ∈ Finset.range M, Real.cos (4 * Real.pi * ((m : ℝ) + 1) / q₀) / ((m : ℝ) + 1)| ≤ B)
    (K : ℕ) (hK : 1 ≤ K) (x : ℤ) (hx₁ : -(K : ℤ) ≤ x) (hx₂ : x ≤ K) :
    α * Real.log (3 * K + 1) - ((2 + α) * B + 4 / 3) ≤
      ∑ n ∈ Finset.Icc (x - ((4 * K : ℕ) : ℤ)) (x + ((4 * K : ℕ) : ℤ)),
        sineTerm α q₀ n.natAbs := by
  have hα : |α| ≤ 1 := by rw [abs_of_pos hα₀]; exact hα₁.le
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  set s₁ : Finset ℤ := Finset.Icc (-((3 * K : ℕ) : ℤ)) ((3 * K : ℕ) : ℤ) with hs₁
  set s₂ : Finset ℤ := Finset.Icc (x - ((4 * K : ℕ) : ℤ)) (x + ((4 * K : ℕ) : ℤ)) with hs₂
  have hsub : s₁ ⊆ s₂ := by
    intro n hn
    simp only [hs₁, hs₂, Finset.mem_Icc] at hn ⊢
    push_cast at hn ⊢
    omega
  have hcard : (s₂ \ s₁).card = 2 * K := by
    rw [Finset.card_sdiff_of_subset hsub, hs₁, hs₂, Int.card_Icc, Int.card_Icc]
    push_cast
    omega
  have herr : |∑ n ∈ s₂ \ s₁, sineTerm α q₀ n.natAbs| ≤ (2 * K : ℕ) * (2 / (3 * K + 1)) := by
    calc _ ≤ ∑ n ∈ s₂ \ s₁, |sineTerm α q₀ n.natAbs| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ s₂ \ s₁, 2 / ((3 * K + 1 : ℕ) : ℝ) := by
          refine Finset.sum_le_sum fun n hn => ?_
          rw [Finset.mem_sdiff] at hn
          have hn' : 3 * K + 1 ≤ n.natAbs := by
            obtain ⟨-, hn2⟩ := hn
            simp only [hs₁, Finset.mem_Icc] at hn2
            push_cast at hn2
            omega
          refine (abs_sineTerm_le α hα q₀ _ (by omega)).trans ?_
          have h1 : (((3 * K + 1 : ℕ)) : ℝ) ≤ (n.natAbs : ℝ) := by exact_mod_cast hn'
          have h2 : (0 : ℝ) < ((3 * K + 1 : ℕ) : ℝ) := by positivity
          exact div_le_div_of_nonneg_left (by norm_num) h2 h1
      _ = (2 * K : ℕ) * (2 / (3 * K + 1)) := by
          rw [Finset.sum_const, hcard, nsmul_eq_mul]
          push_cast
          ring
  have herr' : ((2 * K : ℕ) : ℝ) * (2 / (3 * K + 1)) ≤ 4 / 3 := by
    push_cast
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    linarith
  have hsplit := Finset.sum_sdiff (f := fun n : ℤ => sineTerm α q₀ n.natAbs) hsub
  have hs1 : ∑ n ∈ s₁, sineTerm α q₀ n.natAbs =
      2 * ∑ m ∈ Finset.range (3 * K), sineTerm α q₀ (m + 1) := by
    rw [hs₁, sum_Icc_natAbs (fun m => sineTerm α q₀ m) (3 * K)]
    simp [sineTerm]
  have hlow := sum_sineTerm_lower α hα₀.le q₀ B hB (3 * K)
  have hlog : Real.log (((3 * K : ℕ) : ℝ) + 1) = Real.log (3 * K + 1) := by push_cast; rfl
  rw [hlog] at hlow
  have habs := (abs_le.1 herr).1
  have : ∑ n ∈ s₂, sineTerm α q₀ n.natAbs =
      ∑ n ∈ s₂ \ s₁, sineTerm α q₀ n.natAbs + ∑ n ∈ s₁, sineTerm α q₀ n.natAbs := hsplit.symm
  rw [this, hs1]
  nlinarith

/-- Logarithmic lower bound for `𝒞_v 1_{[-4K, 4K]}` on `[-K, K]`. -/
theorem exists_carlesonMax_lower (α : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1) (q₀ : ℕ) (hq₀ : 3 ≤ q₀) :
    ∃ C : ℝ, ∀ K : ℕ, 1 ≤ K → ∀ x : ℤ, -(K : ℤ) ≤ x → x ≤ K →
      ENNReal.ofReal (α * Real.log (3 * K + 1) - C) ≤
        carlesonMax (sineWeight α q₀) (unboundedTest (4 * K)) x := by
  obtain ⟨B, -, hB⟩ := exists_bound_sin_cos_sums q₀ hq₀
  refine ⟨(2 + α) * B + 4 / 3, fun K hK x hx₁ hx₂ => ?_⟩
  have hq : (3 : ℝ) ≤ q₀ := by exact_mod_cast hq₀
  have hlam : (1 / (q₀ : ℝ)) ∈ Set.Ico (0 : ℝ) 1 := by
    refine ⟨by positivity, ?_⟩
    rw [div_lt_one (by linarith)]
    linarith
  have him := sum_Icc_lower α hα₀ hα₁ q₀ B hB K hK x hx₁ hx₂
  rw [← im_modulatedSum_unboundedTest α q₀ (4 * K) x] at him
  calc ENNReal.ofReal (α * Real.log (3 * K + 1) - ((2 + α) * B + 4 / 3))
      ≤ ENNReal.ofReal ((modulatedSum (sineWeight α q₀) (unboundedTest (4 * K)) (1 / q₀) x).im) :=
        ENNReal.ofReal_le_ofReal him
    _ ≤ ‖modulatedSum (sineWeight α q₀) (unboundedTest (4 * K)) (1 / q₀) x‖ₑ := by
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (Complex.abs_im_le_norm _))
    _ ≤ carlesonMax (sineWeight α q₀) (unboundedTest (4 * K)) x :=
        le_iSup₂_of_le (1 / (q₀ : ℝ)) hlam le_rfl

end PrimeCarleson.Proof
