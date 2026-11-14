module

public import Mathlib.NumberTheory.LSeries.PrimesInAP
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# The `3 + 4 cos + cos 2` and `1 + chi` positivity of the logarithmic derivatives

Part of the classical zero-free region (`ZeroFree/Main.lean`).

* `character_log_derivative_positivity`: the de la Vallee Poussin inequality
  `0 ≤ 3 (-ζ'/ζ)(σ) + 4 Re (-L'/L)(σ + it, χ) + Re (-L'/L)(σ + 2it, χ²)` for `σ > 1`.
* `real_character_log_derivative_positivity`: for a real character,
  `0 ≤ (-ζ'/ζ)(σ) + (-L'/L)(σ, χ)`.
* `principal_neg_real_log_derivative_le`: `-Re L'/L(s, χ₀) ≤ -Re ζ'/ζ(s) + log q` for the principal
  character `χ₀` modulo `q` and `re s > 1`.

Provenance (upstream openai/math, commit 4eaee87, Apache-2.0; the upstream files are not vendored).
The declarations from `characterPhase` to `character_log_derivative_positivity` are those of the
upstream file `lean/OAI/NumberTheory/Jacobsthal/Harmonic/CharacterPositivity.lean`, and the
declarations from `localEulerFactor` to `principal_neg_real_log_derivative_le` are those of the
upstream file `lean/OAI/NumberTheory/Jacobsthal/Sieve/PrincipalEulerCorrection.lean` (both
Mathlib-only).  `real_character_log_derivative_positivity` is not from upstream.
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31.ZeroFree

open scoped ComplexOrder

/-- The phase `n^{-it}`. -/
def characterPhase (n : ℕ) (t : ℝ) : ℂ := (n : ℂ) ^ (-(t : ℂ) * Complex.I)

/-- The phase has modulus one. -/
lemma characterPhase_norm {n : ℕ} (hn : n ≠ 0) (t : ℝ) : ‖characterPhase n t‖ = 1 := by
  unfold characterPhase
  rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
  simp

/-- The phase of `2t` is the square of the phase of `t`. -/
lemma characterPhase_double {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    characterPhase n (2 * t) = characterPhase n t ^ 2 := by
  unfold characterPhase
  rw [sq, ← Complex.cpow_add _ _ (by exact_mod_cast hn : (n : ℂ) ≠ 0)]
  congr 1
  push_cast
  ring

/-- Splitting of the `n`-th term of the twisted `Λ`-series on the line `re s = σ`. -/
lemma twist_vonMangoldt_term_split {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (sigma t : ℝ) (n : ℕ) :
    LSeries.term (fun k => chi k * (ArithmeticFunction.vonMangoldt k : ℂ))
      ((sigma : ℂ) + (t : ℂ) * Complex.I) n =
    LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) (sigma : ℂ) n *
      chi n * characterPhase n t := by
  by_cases hn : n = 0
  · simp [hn]
  · have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn,
      Complex.cpow_add _ _ hnC]
    unfold characterPhase
    rw [neg_mul, Complex.cpow_neg]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

/-- `3 + 4 Re u + Re u² ≥ 0` for `‖u‖ ≤ 1`. -/
lemma character_positivity_polynomial (u : ℂ) (hu : ‖u‖ ≤ 1) :
    0 ≤ 3 + 4 * u.re + (u ^ 2).re := by
  have hsq : u.re ^ 2 + u.im ^ 2 ≤ 1 := by
    have h := Complex.sq_norm u
    rw [Complex.normSq_apply] at h
    nlinarith [norm_nonneg u]
  simp only [pow_two, Complex.mul_re]
  nlinarith [sq_nonneg (1 + u.re)]

/-- The `n`-th term of the `3-4-1` combination is a nonnegative real. -/
lemma vonMangoldt_three_four_one_nonneg {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (sigma t : ℝ) (n : ℕ) :
    0 ≤ (3 * LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) (sigma : ℂ) n +
      4 * LSeries.term (fun k => chi k * (ArithmeticFunction.vonMangoldt k : ℂ))
        ((sigma : ℂ) + (t : ℂ) * Complex.I) n +
      LSeries.term (fun k => (chi ^ 2) k * (ArithmeticFunction.vonMangoldt k : ℂ))
        ((sigma : ℂ) + (2 * t : ℝ) * Complex.I) n).re := by
  by_cases hn : n = 0
  · simp [hn]
  · let a : ℂ := LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) (sigma : ℂ) n
    let u : ℂ := chi n * characterPhase n t
    have hu : ‖u‖ ≤ 1 := by
      dsimp only [u]
      rw [norm_mul, characterPhase_norm hn, mul_one]
      exact chi.norm_le_one n
    have ha : 0 ≤ a := LSeries.term_nonneg
      (by exact_mod_cast (ArithmeticFunction.vonMangoldt_nonneg (n := n))) sigma
    have ha' := Complex.nonneg_iff.mp ha
    rw [twist_vonMangoldt_term_split, twist_vonMangoldt_term_split,
      characterPhase_double hn]
    have hp : (chi ^ 2) n = (chi n) ^ 2 := chi.pow_apply' (by decide) n
    rw [hp]
    have heq : 3 * a + 4 * (a * chi n * characterPhase n t) +
        a * (chi n) ^ 2 * (characterPhase n t) ^ 2 = a * (3 + 4 * u + u ^ 2) := by
      dsimp [u]; ring
    change 0 ≤ (3 * a + 4 * (a * chi n * characterPhase n t) +
      a * (chi n) ^ 2 * (characterPhase n t) ^ 2).re
    rw [heq, Complex.mul_re, ← ha'.2]
    simp only [zero_mul, sub_zero]
    apply mul_nonneg ha'.1
    simpa using character_positivity_polynomial u hu

/-- The twisted `Λ`-series is the negative logarithmic derivative of the `L`-function. -/
lemma twisted_series_eq_actual_log_derivative {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => chi n * (ArithmeticFunction.vonMangoldt n : ℂ)) s =
      -deriv (DirichletCharacter.LFunction chi) s / DirichletCharacter.LFunction chi s := by
  change LSeries ((fun n : ℕ => chi n) * (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))) s = _
  rw [DirichletCharacter.LSeries_twist_vonMangoldt_eq chi hs,
    ← DirichletCharacter.deriv_LFunction_eq_deriv_LSeries chi hs,
    ← DirichletCharacter.LFunction_eq_LSeries chi hs]

/-- **The `3-4-1` inequality** for `ζ`, `L(·, χ)`, `L(·, χ²)` at `σ`, `σ + it`, `σ + 2it`. -/
theorem character_log_derivative_positivity {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (sigma t : ℝ) (hs : 1 < sigma) :
    0 ≤ 3 * (-deriv riemannZeta (sigma : ℂ) / riemannZeta (sigma : ℂ)).re +
      4 * (-deriv (DirichletCharacter.LFunction chi) ((sigma : ℂ) + (t : ℂ) * Complex.I) /
        DirichletCharacter.LFunction chi ((sigma : ℂ) + (t : ℂ) * Complex.I)).re +
      (-deriv (DirichletCharacter.LFunction (chi ^ 2))
          ((sigma : ℂ) + (2 * t : ℝ) * Complex.I) /
        DirichletCharacter.LFunction (chi ^ 2) ((sigma : ℂ) + (2 * t : ℝ) * Complex.I)).re := by
  let a := LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (sigma : ℂ)
  let b := LSeries.term (fun n => chi n * (ArithmeticFunction.vonMangoldt n : ℂ))
    ((sigma : ℂ) + (t : ℂ) * Complex.I)
  let c := LSeries.term (fun n => (chi ^ 2) n * (ArithmeticFunction.vonMangoldt n : ℂ))
    ((sigma : ℂ) + (2 * t : ℝ) * Complex.I)
  have ha : Summable a := ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hs)
  have hb : Summable b :=
    DirichletCharacter.LSeriesSummable_twist_vonMangoldt chi (by simpa using hs)
  have hc : Summable c :=
    DirichletCharacter.LSeriesSummable_twist_vonMangoldt (chi ^ 2) (by simpa using hs)
  have hsum := ((ha.mul_left (3 : ℂ)).add (hb.mul_left (4 : ℂ))).add hc
  have hvalue := ((ha.hasSum.mul_left (3 : ℂ)).add (hb.hasSum.mul_left (4 : ℂ))).add hc.hasSum
  have hpositive : 0 ≤ (∑' n : ℕ, (3 * a n + 4 * b n + c n)).re := by
    rw [Complex.re_tsum hsum]
    exact tsum_nonneg (fun n => vonMangoldt_three_four_one_nonneg chi sigma t n)
  rw [hvalue.tsum_eq] at hpositive
  change 0 ≤ (3 * LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (sigma : ℂ) +
    4 * LSeries (fun n => chi n * (ArithmeticFunction.vonMangoldt n : ℂ))
      ((sigma : ℂ) + (t : ℂ) * Complex.I) +
    LSeries (fun n => (chi ^ 2) n * (ArithmeticFunction.vonMangoldt n : ℂ))
      ((sigma : ℂ) + (2 * t : ℝ) * Complex.I)).re at hpositive
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by simpa using hs),
    twisted_series_eq_actual_log_derivative chi (by simpa using hs),
    twisted_series_eq_actual_log_derivative (chi ^ 2) (by simpa using hs)] at hpositive
  simpa [Complex.add_re, Complex.mul_re] using hpositive

/-- **The `1 + χ` inequality** for a real character: `0 ≤ (-ζ'/ζ)(σ) + (-L'/L)(σ, χ)`. -/
theorem real_character_log_derivative_positivity {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hreal : ∀ a : ZMod q, (chi a).im = 0) (sigma : ℝ)
    (hs : 1 < sigma) :
    0 ≤ (-deriv riemannZeta (sigma : ℂ) / riemannZeta (sigma : ℂ)).re +
      (-deriv (DirichletCharacter.LFunction chi) (sigma : ℂ) /
        DirichletCharacter.LFunction chi (sigma : ℂ)).re := by
  let a := LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (sigma : ℂ)
  let b := LSeries.term (fun n => chi n * (ArithmeticFunction.vonMangoldt n : ℂ)) (sigma : ℂ)
  have ha : Summable a := ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hs)
  have hb : Summable b :=
    DirichletCharacter.LSeriesSummable_twist_vonMangoldt chi (by simpa using hs)
  have hterm : ∀ n : ℕ, 0 ≤ (a n + b n).re := by
    intro n
    by_cases hn : n = 0
    · simp [a, b, hn]
    · have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      have hbn : b n = a n * chi n := by
        simp only [a, b]
        rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
        ring
      have han : 0 ≤ a n := LSeries.term_nonneg
        (by exact_mod_cast (ArithmeticFunction.vonMangoldt_nonneg (n := n))) sigma
      have ha' := Complex.nonneg_iff.mp han
      have hc : (chi n).im = 0 := hreal n
      have hc1 : -1 ≤ (chi n).re := by
        have h1 := Complex.abs_re_le_norm (chi n)
        have h2 := chi.norm_le_one n
        have := (abs_le.1 (h1.trans h2)).1
        linarith
      rw [hbn, Complex.add_re, Complex.mul_re, hc, ← ha'.2]
      simp only [mul_zero, sub_zero]
      nlinarith [ha'.1]
  have hsum := ha.add hb
  have hvalue := ha.hasSum.add hb.hasSum
  have hpositive : 0 ≤ (∑' n : ℕ, (a n + b n)).re := by
    rw [Complex.re_tsum hsum]
    exact tsum_nonneg hterm
  rw [hvalue.tsum_eq] at hpositive
  change 0 ≤ (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (sigma : ℂ) +
    LSeries (fun n => chi n * (ArithmeticFunction.vonMangoldt n : ℂ)) (sigma : ℂ)).re
    at hpositive
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by simpa using hs),
    twisted_series_eq_actual_log_derivative chi (by simpa using hs)] at hpositive
  simpa [Complex.add_re] using hpositive

/-- The Euler factor `1 - α p^{-s}`. -/
def localEulerFactor (alpha : ℂ) (p : ℕ) (s : ℂ) : ℂ :=
  1 - alpha * (p : ℂ) ^ (-s)

/-- `‖p^{-s}‖ ≤ 1/2` for a prime `p` and `re s ≥ 1`. -/
lemma prime_cpow_neg_norm_le_half {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 1 ≤ s.re) :
    ‖(p : ℂ) ^ (-s)‖ ≤ 1 / 2 := by
  rw [Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re]
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  calc
    _ ≤ (p : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    _ = 1 / (p : ℝ) := by rw [Real.rpow_neg_one, one_div]
    _ ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hpR

/-- The Euler factor does not vanish for `re s ≥ 1`. -/
lemma localEulerFactor_ne_zero {p : ℕ} (hp : p.Prime) {alpha s : ℂ}
    (ha : ‖alpha‖ ≤ 1) (hs : 1 ≤ s.re) : localEulerFactor alpha p s ≠ 0 := by
  have hu : ‖alpha * (p : ℂ) ^ (-s)‖ ≤ 1 / 2 := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right ha (norm_nonneg _)).trans
      (by simpa using prime_cpow_neg_norm_le_half hp hs)
  intro hz
  have he : alpha * (p : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp hz).symm
  rw [he, norm_one] at hu
  norm_num at hu

/-- The Euler factor is entire. -/
lemma localEulerFactor_differentiable {p : ℕ} (hp : p.Prime) (alpha : ℂ) :
    Differentiable ℂ (localEulerFactor alpha p) := by
  unfold localEulerFactor
  fun_prop (disch := exact Or.inl (by exact_mod_cast hp.ne_zero))

/-- The derivative of the Euler factor. -/
lemma localEulerFactor_deriv {p : ℕ} (hp : p.Prime) (alpha s : ℂ) :
    deriv (localEulerFactor alpha p) s =
      (Real.log (p : ℝ) : ℂ) * (alpha * (p : ℂ) ^ (-s)) := by
  have hn : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hd := ((((hasDerivAt_id s).neg).const_cpow (c := (p : ℂ)) (Or.inl hn)).const_mul
    alpha).const_sub 1
  simp only [Pi.neg_apply, id_eq] at hd
  convert! hd.deriv using 1
  rw [← Complex.natCast_log]
  ring

/-- The logarithmic derivative of the Euler factor has norm at most `log p`. -/
lemma norm_logDeriv_localEulerFactor {p : ℕ} (hp : p.Prime) {alpha s : ℂ}
    (ha : ‖alpha‖ ≤ 1) (hs : 1 ≤ s.re) :
    ‖logDeriv (localEulerFactor alpha p) s‖ ≤ Real.log (p : ℝ) := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by linarith)
  have hu : ‖alpha * (p : ℂ) ^ (-s)‖ ≤ 1 / 2 := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right ha (norm_nonneg _)).trans
      (by simpa using prime_cpow_neg_norm_le_half hp hs)
  have hden : ‖alpha * (p : ℂ) ^ (-s)‖ ≤ ‖localEulerFactor alpha p s‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (alpha * (p : ℂ) ^ (-s))
    rw [norm_one] at h
    change 1 - ‖alpha * (p : ℂ) ^ (-s)‖ ≤ ‖localEulerFactor alpha p s‖ at h
    linarith
  rw [logDeriv_apply, localEulerFactor_deriv hp, norm_div, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog]
  exact (div_le_iff₀ (norm_pos_iff.mpr (localEulerFactor_ne_zero hp ha hs))).mpr
    (mul_le_mul_of_nonneg_left hden hlog)

/-- `∑_{p ∣ q} log p ≤ log q`. -/
lemma sum_log_primeFactors_le_log (q : ℕ) [NeZero q] :
    ∑ p ∈ q.primeFactors, Real.log (p : ℝ) ≤ Real.log (q : ℝ) := by
  have hpos : 0 < ∏ p ∈ q.primeFactors, (p : ℝ) :=
    Finset.prod_pos (fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos)
  rw [← Real.log_prod (fun p hp => by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero)]
  apply Real.log_le_log hpos
  have h : (((∏ p ∈ q.primeFactors, p : ℕ) : ℕ) : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast Nat.le_of_dvd (NeZero.pos q) (Nat.prod_primeFactors_dvd q)
  simpa only [Nat.cast_prod] using! h

/-- The Euler-factor corrections have logarithmic derivative of norm at most `log q`. -/
theorem norm_euler_log_correction_le_log (q : ℕ) [NeZero q] (S : Finset ℕ)
    (hS : S ⊆ q.primeFactors) (alpha : ℕ → ℂ) (ha : ∀ p ∈ S, ‖alpha p‖ ≤ 1)
    {s : ℂ} (hs : 1 ≤ s.re) :
    ‖∑ p ∈ S, logDeriv (localEulerFactor (alpha p) p) s‖ ≤ Real.log (q : ℝ) := by
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum (fun p hp => norm_logDeriv_localEulerFactor
    (Nat.prime_of_mem_primeFactors (hS hp)) (ha p hp) hs)).trans
  apply (Finset.sum_le_sum_of_subset_of_nonneg hS (fun p hp _ =>
    Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le))).trans
  exact sum_log_primeFactors_le_log q

/-- The Euler product over the primes dividing `q`. -/
def modulusEulerProduct (q : ℕ) (s : ℂ) : ℂ :=
  ∏ p ∈ q.primeFactors, localEulerFactor 1 p s

/-- `L'/L (χ₀) = ζ'/ζ + ∑_{p ∣ q} (Euler factor)'/(Euler factor)` on `re s > 1`. -/
lemma principal_log_derivative_eq (q : ℕ) [NeZero q] {s : ℂ} (hs : 1 < s.re) :
    logDeriv (DirichletCharacter.LFunctionTrivChar q) s = logDeriv riemannZeta s +
      ∑ p ∈ q.primeFactors, logDeriv (localEulerFactor 1 p) s := by
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs
  have he : DirichletCharacter.LFunctionTrivChar q =ᶠ[nhds s]
      (fun z => modulusEulerProduct q z * riemannZeta z) := by
    filter_upwards [isOpen_ne.mem_nhds hs1] with z hz
    simpa only [modulusEulerProduct, localEulerFactor, one_mul] using
      (DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (N := q) hz)
  have hf (p : ℕ) (hp : p ∈ q.primeFactors) : localEulerFactor 1 p s ≠ 0 :=
    localEulerFactor_ne_zero (Nat.prime_of_mem_primeFactors hp) (by simp) hs.le
  have hd (p : ℕ) (hp : p ∈ q.primeFactors) : DifferentiableAt ℂ (localEulerFactor 1 p) s :=
    (localEulerFactor_differentiable (Nat.prime_of_mem_primeFactors hp) 1).differentiableAt
  have hprod : modulusEulerProduct q s ≠ 0 := Finset.prod_ne_zero_iff.mpr hf
  have hdiff : DifferentiableAt ℂ (modulusEulerProduct q) s :=
    DifferentiableAt.fun_finsetProd hd
  have hld : logDeriv (DirichletCharacter.LFunctionTrivChar q) s =
      logDeriv (fun z => modulusEulerProduct q z * riemannZeta z) s := by
    simp only [logDeriv_apply, he.deriv_eq, he.eq_of_nhds]
  rw [hld, logDeriv_fun_mul s hprod (riemannZeta_ne_zero_of_one_le_re hs.le) hdiff
    (differentiableAt_riemannZeta hs1)]
  have hsum : logDeriv (modulusEulerProduct q) s =
      ∑ p ∈ q.primeFactors, logDeriv (localEulerFactor 1 p) s := logDeriv_fun_prod hf hd
  rw [hsum, add_comm]

/-- `‖L'/L (χ₀) - ζ'/ζ‖ ≤ log q` on `re s > 1`. -/
theorem norm_principal_log_derivative_difference (q : ℕ) [NeZero q]
    {s : ℂ} (hs : 1 < s.re) :
    ‖logDeriv (DirichletCharacter.LFunctionTrivChar q) s - logDeriv riemannZeta s‖ ≤
      Real.log (q : ℝ) := by
  rw [principal_log_derivative_eq q hs, add_sub_cancel_left]
  exact norm_euler_log_correction_le_log q q.primeFactors (Finset.Subset.refl _)
    (fun _ => 1) (by intro p hp; simp) hs.le

/-- **The principal character**: `-Re L'/L(χ₀) ≤ -Re ζ'/ζ + log q` for `re s > 1`. -/
theorem principal_neg_real_log_derivative_le (q : ℕ) [NeZero q]
    {s : ℂ} (hs : 1 < s.re) :
    (-logDeriv (DirichletCharacter.LFunctionTrivChar q) s).re ≤
      (-logDeriv riemannZeta s).re + Real.log (q : ℝ) := by
  have h := (Complex.re_le_norm (-(logDeriv (DirichletCharacter.LFunctionTrivChar q) s -
    logDeriv riemannZeta s))).trans
    (by simpa only [norm_neg] using norm_principal_log_derivative_difference q hs)
  simp only [Complex.neg_re, Complex.sub_re] at h ⊢
  linarith

end PrimeCarleson.Proof.Fplus31.ZeroFree
