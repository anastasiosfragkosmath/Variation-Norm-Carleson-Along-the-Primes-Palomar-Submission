module

public import PrimeCarleson.Proof.Paper.P3.Basic

/-!
# The van der Corput step of `e:U3maxmod`

Source: main paper `e:U3maxmod`, L732–L801, the first part of the proof of Lemma `e:U3maxmod`. Paper
steps proved here:

* `e:vdc-local` (`vdcLocal`): for `a` supported in `[N]`,
  `|E_{n ∈ [N]} a(n)|⁴ ≤ 9 E_{|h| ≤ N} |E_{n ∈ [N]} Δ_h a(n)|²`. The
  squaring identity `e:double` gives `|E a|² = (2N+1)/N · E_{|h| ≤ N} E_n Δ_h a` exactly, and
  Cauchy-Schwarz in `h` gives the constant `((2N+1)/N)² ≤ 9`;
* `e:first-diff` (`first_diff`): for `w` supported in `[N]`, every `λ` and every `x`,
  `|A_λ f(x)|⁴ ≤ 9 E_{|h| ≤ N} |E_{n ∈ [N]} Δ_h w(n) Δ_{-h} f(x - n)|²`, where
  `Δ_h w(n) = w(n) conj w(n+h)` and `Δ_{-h} f(y) = f(y) conj f(y - h)`; the phase
  `e(λ n)` drops out of the absolute value (`Δ_h e(λ·) = e(-λ h)`);
* `e:xh-average` (`xh_average`): the average over `x ∈ [-N, 2N]` for an arbitrary selector
  `θ`: `‖A_θ f‖_{L⁴([-N,2N])}⁴ ≤ 9 E_{|h| ≤ N} ‖E_n Δ_h w(n) Δ_{-h} f(x-n)‖_{L²_x([-N,2N])}²`;
* the linearization (L733–L743; `linearization`): if the linearized estimate
  `‖A_θ f‖_{L⁴(X)} ≤ K` holds for every selector `θ : ℤ → ℝ`, then
  `‖sup_λ |A_λ f|‖_{L⁴(X)} ≤ K` (the supremum is attained, `iSup_norm_eq_of_periodic`).

`A_λ f(x) = E_{n ∈ [N]} f(x-n) w(n) e(λ n)` is `Paper.modAverage`; `E_X` is `expect`,
`‖·‖_{L^p(X)}` is `lpNormOn`, `Δ_h` is `conjDiff`.
-/

@[expose] public noncomputable section

open scoped ComplexConjugate

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Goal0

/-- The normalized expectation of a constant multiple. -/
theorem expect_const_mul_cpx (X : Finset ℤ) (c : ℂ) (g : ℤ → ℂ) :
    expect X (fun n => c * g n) = c * expect X g := by
  unfold expect
  rw [← Finset.mul_sum]
  ring

/-- **`e:vdc-local`** (Source: main paper `e:vdc-local`, L753–L773), for `a` supported in `[N]`:
`|E_{n ∈ [N]} a(n)|⁴ ≤ 9 E_{|h| ≤ N} |E_{n ∈ [N]} Δ_h a(n)|²` with `Δ_h a(n) = a(n) conj a(n+h)`. -/
theorem vdcLocal (N : ℕ+) (a : ℤ → ℂ) (ha : ∀ n, n ∉ bracket N → a n = 0) :
    ‖expect (bracket N) a‖ ^ 4 ≤
      9 * (Finset.Icc (-(N : ℤ)) (N : ℤ)).expect
        (fun h => ‖expect (bracket N) (conjDiff h a)‖ ^ 2) := by
  classical
  set I := bracket N with hI
  set B : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ) with hB
  have hBd : ∀ x ∈ I, ∀ y ∈ I, y - x ∈ B := by
    intro x hx y hy
    rw [hI, mem_bracket] at hx hy
    simp only [hB, Finset.mem_Icc]
    omega
  have key := norm_sq_sum_eq_sum_conjDiff I B hBd a ha
  rw [Finset.sum_comm] at key
  set P : ℤ → ℂ := fun h => ∑ x ∈ I, conjDiff h a x with hP
  have h1 : ‖∑ x ∈ I, a x‖ ^ 2 ≤ ∑ h ∈ B, ‖P h‖ := by
    have : ‖∑ x ∈ I, a x‖ ^ 2 = ‖∑ h ∈ B, P h‖ := by
      have := congrArg (fun z : ℂ => ‖z‖) key
      simpa using this
    rw [this]
    exact norm_sum_le _ _
  have h2 : (∑ h ∈ B, ‖P h‖) ^ 2 ≤ (B.card : ℝ) * ∑ h ∈ B, ‖P h‖ ^ 2 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq B (fun h => ‖P h‖) (fun _ => (1 : ℝ))
    simpa [mul_comm] using this
  have h3 : ‖∑ x ∈ I, a x‖ ^ 4 ≤ (B.card : ℝ) * ∑ h ∈ B, ‖P h‖ ^ 2 := by
    calc ‖∑ x ∈ I, a x‖ ^ 4 = (‖∑ x ∈ I, a x‖ ^ 2) ^ 2 := by ring
      _ ≤ (∑ h ∈ B, ‖P h‖) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
      _ ≤ _ := h2
  have hNpos : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast N.pos
  have hBc : (B.card : ℝ) = 2 * (N : ℝ) + 1 := by
    have : ((N : ℤ) + 1 - -(N : ℤ)).toNat = 2 * (N : ℕ) + 1 := by omega
    rw [hB, Int.card_Icc, this]
    push_cast
    ring
  have hE : ∀ g : ℤ → ℂ, ‖expect I g‖ = (N : ℝ)⁻¹ * ‖∑ x ∈ I, g x‖ := by
    intro g
    simp [expect, hI, card_bracket]
  rw [hE, Finset.expect_eq_sum_div_card, hBc]
  simp_rw [hE]
  have hSig : 0 ≤ ∑ h ∈ B, ‖P h‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  have hsq : ∑ h ∈ B, ((N : ℝ)⁻¹ * ‖∑ x ∈ I, conjDiff h a x‖) ^ 2 =
      ((N : ℝ)⁻¹) ^ 2 * ∑ h ∈ B, ‖P h‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun h _ => by ring
  rw [hsq, mul_pow]
  have hN0 : (0 : ℝ) < N := by linarith
  rw [hBc] at h3
  have hc : ((N : ℝ)⁻¹) ^ 4 * (2 * (N : ℝ) + 1) ≤ 9 * (((N : ℝ)⁻¹) ^ 2 / (2 * (N : ℝ) + 1)) := by
    have h1 : 0 < 2 * (N : ℝ) + 1 := by linarith
    rw [← mul_div_assoc, le_div_iff₀ h1]
    have h2 : ((2 * (N : ℝ) + 1) / N) ^ 2 ≤ 9 := by
      have : (2 * (N : ℝ) + 1) / N ≤ 3 := by rw [div_le_iff₀ hN0]; linarith
      nlinarith [div_nonneg h1.le hN0.le]
    have h3 : 0 ≤ ((N : ℝ)⁻¹) ^ 2 := by positivity
    calc ((N : ℝ)⁻¹) ^ 4 * (2 * (N : ℝ) + 1) * (2 * (N : ℝ) + 1)
        = ((N : ℝ)⁻¹) ^ 2 * (((2 * (N : ℝ) + 1) / N) ^ 2) := by field_simp
      _ ≤ ((N : ℝ)⁻¹) ^ 2 * 9 := mul_le_mul_of_nonneg_left h2 h3
      _ = 9 * ((N : ℝ)⁻¹) ^ 2 := by ring
  calc ((N : ℝ)⁻¹) ^ 4 * ‖∑ x ∈ I, a x‖ ^ 4
      ≤ ((N : ℝ)⁻¹) ^ 4 * ((2 * (N : ℝ) + 1) * ∑ h ∈ B, ‖P h‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = (((N : ℝ)⁻¹) ^ 4 * (2 * (N : ℝ) + 1)) * ∑ h ∈ B, ‖P h‖ ^ 2 := by ring
    _ ≤ (9 * (((N : ℝ)⁻¹) ^ 2 / (2 * (N : ℝ) + 1))) * ∑ h ∈ B, ‖P h‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hc hSig
    _ = 9 * ((((N : ℝ)⁻¹) ^ 2 * ∑ h ∈ B, ‖P h‖ ^ 2) / (2 * (N : ℝ) + 1)) := by ring

/-- **`e:first-diff`** (Source: main paper `e:first-diff`, L775–L798): for `w` supported in `[N]`
and every `λ`, `x`,
`|A_λ f(x)|⁴ ≤ 9 E_{|h| ≤ N} |E_{n ∈ [N]} Δ_h w(n) Δ_{-h} f(x - n)|²`, where
`Δ_h w(n) = w(n) conj w(n + h)` and `Δ_{-h} f(y) = f(y) conj f(y - h)`. -/
theorem first_diff (N : ℕ+) (w f : ℤ → ℂ) (hw : ∀ n, n ∉ bracket N → w n = 0) (lam : ℝ)
    (x : ℤ) :
    ‖modAverage N w f lam x‖ ^ 4 ≤
      9 * (Finset.Icc (-(N : ℤ)) (N : ℤ)).expect (fun h =>
        ‖expect (bracket N) (fun n => conjDiff h w n * conjDiff (-h) f (x - n))‖ ^ 2) := by
  set a : ℤ → ℂ := fun n => f (x - n) * w n * e (lam * n) with ha
  have hsupp : ∀ n, n ∉ bracket N → a n = 0 := fun n hn => by simp [ha, hw n hn]
  have h1 := vdcLocal N a hsupp
  have hmain : modAverage N w f lam x = expect (bracket N) a := rfl
  rw [hmain]
  refine h1.trans (mul_le_mul_of_nonneg_left (le_of_eq ?_) (by norm_num))
  refine Finset.expect_congr rfl fun h _ => ?_
  have hpt : ∀ n, conjDiff h a n =
      e (-(lam * h)) * (conjDiff h w n * conjDiff (-h) f (x - n)) := by
    intro n
    simp only [conjDiff_apply, ha, map_mul]
    have hx : x - (n + h) = x - n + -h := by ring
    rw [hx]
    have he : e (lam * ((n + h : ℤ) : ℝ)) = e (lam * n) * e (lam * h) := by
      rw [← e_add]; congr 1; push_cast; ring
    have hneg : e (-(lam * h)) = conj (e (lam * h)) := e_neg _
    rw [he, map_mul, hneg]
    have hu : e (lam * (n : ℝ)) * (starRingEnd ℂ) (e (lam * (n : ℝ))) = 1 := by
      rw [← e_neg, ← e_add]
      simp [e_zero]
    linear_combination (f (x - n) * w n * (starRingEnd ℂ) (f (x - n + -h)) *
      (starRingEnd ℂ) (w (n + h)) * (starRingEnd ℂ) (e (lam * (h : ℝ)))) * hu
  have : expect (bracket N) (conjDiff h a) =
      e (-(lam * h)) * expect (bracket N) (fun n => conjDiff h w n * conjDiff (-h) f (x - n)) := by
    rw [← expect_const_mul_cpx]
    exact congrArg (expect (bracket N)) (funext hpt)
  rw [this, norm_mul, norm_e, one_mul]

/-- **`e:xh-average`** (Source: main paper `e:xh-average`, L801–L811): for `w` supported in `[N]`
and an arbitrary selector `θ`,
`‖A_θ f‖_{L⁴([-N,2N])}⁴ ≤ 9 E_{|h| ≤ N} ‖E_{n ∈ [N]} Δ_h w(n) Δ_{-h} f(x-n)‖_{L²_x([-N,2N])}²`,
`A_θ f(x) = E_{n ∈ [N]} w(n) f(x-n) e(θ(x) n)`. -/
theorem xh_average (N : ℕ+) (w f : ℤ → ℂ) (hw : ∀ n, n ∉ bracket N → w n = 0)
    (θ : ℤ → ℝ) :
    lpNormOn 4 (maxWindow N) (fun x => modAverage N w f (θ x) x) ^ 4 ≤
      9 * (Finset.Icc (-(N : ℤ)) (N : ℤ)).expect (fun h =>
        lpNormOn 2 (maxWindow N) (fun x =>
          expect (bracket N) (fun n => conjDiff h w n * conjDiff (-h) f (x - n))) ^ 2) := by
  classical
  set X := maxWindow N with hX
  set B : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ) with hB
  rw [lpNormOn_four_pow]
  simp_rw [lpNormOn_two_sq]
  have hpt : ∀ x ∈ X, ‖modAverage N w f (θ x) x‖ ^ 4 ≤ 9 * B.expect (fun h =>
      ‖expect (bracket N) (fun n => conjDiff h w n * conjDiff (-h) f (x - n))‖ ^ 2) :=
    fun x _ => first_diff N w f hw (θ x) x
  simp only [Finset.expect_eq_sum_div_card]
  have hcard : (0 : ℝ) ≤ (X.card : ℝ)⁻¹ := inv_nonneg.2 (Nat.cast_nonneg _)
  calc (X.card : ℝ)⁻¹ * ∑ x ∈ X, ‖modAverage N w f (θ x) x‖ ^ 4
      ≤ (X.card : ℝ)⁻¹ * ∑ x ∈ X, 9 * ((∑ h ∈ B, ‖expect (bracket N)
          (fun n => conjDiff h w n * conjDiff (-h) f (x - n))‖ ^ 2) / (B.card : ℝ)) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x hx => ?_) hcard
        have := hpt x hx
        simpa only [Finset.expect_eq_sum_div_card] using this
    _ = 9 * ((∑ h ∈ B, (X.card : ℝ)⁻¹ * ∑ x ∈ X, ‖expect (bracket N)
          (fun n => conjDiff h w n * conjDiff (-h) f (x - n))‖ ^ 2) / (B.card : ℝ)) := by
        rw [← Finset.mul_sum, ← Finset.sum_div, ← Finset.mul_sum, Finset.sum_comm]
        ring

/-- **Linearization of the supremum** (Source: main paper `e:U3maxmod`, L733–L743, L884): if
the linearized estimate `‖A_θ f‖_{L⁴(X)} ≤ K` holds for every selector `θ : ℤ → ℝ`
(`A_θ f(x) = E_{n ∈ [N]} w(n) f(x-n) e(θ(x) n)`), then
`‖sup_λ |A_λ f|‖_{L⁴(X)} ≤ K`: the supremum over `λ` is attained, so it is a selector. -/
theorem linearization (N : ℕ+) (w f : ℤ → ℂ) (X : Finset ℤ) (K : ℝ)
    (h : ∀ θ : ℤ → ℝ, lpNormOn 4 X (fun x => modAverage N w f (θ x) x) ≤ K) :
    lpNormOn 4 X (fun x => ((⨆ lam : ℝ, ‖modAverage N w f lam x‖ : ℝ) : ℂ)) ≤ K := by
  choose m hm using fun x => iSup_norm_eq_of_periodic (continuous_modAverage_lam N w f x)
    (periodic_modAverage_lam N w f x)
  refine le_trans (le_of_eq ?_) (h m)
  unfold lpNormOn
  refine congrArg (fun y : ℝ => y ^ (1 / (4 : ℝ))) (congrArg (fun y : ℝ => (X.card : ℝ)⁻¹ * y) ?_)
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.iSup_nonneg fun _ => norm_nonneg _),
    (hm x).1]

end PrimeCarleson.Proof.Paper
