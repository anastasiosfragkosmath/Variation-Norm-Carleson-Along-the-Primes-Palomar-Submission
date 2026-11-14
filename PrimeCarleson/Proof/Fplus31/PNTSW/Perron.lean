module

public import PrimeCarleson.Proof.Fplus31.PNT.Riesz
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The exact Perron formula for the Riesz mean on a line `re s = σ`, `σ > 1`

Part of the prime number theorem in progressions on the classical zero-free region
(`PNTSW/Main.lean`). This is the exact Perron formula on a line `re s = σ` with `σ > 1`, from the
Mellin transform of the Riesz kernel (`PNT/Riesz.lean`): the contour has to be put
close to the `1`-line, because the truncation at height `T` costs `y^{σ+1} / T`. For a Dirichlet
character `χ` modulo `q` (principal included; `q = 1` is `ζ`), `y > 0` and `σ > 1`,

`2π ∑_{n ≤ y} χ(n) Λ(n) (y - n) = ∫_ℝ -(L'/L)(σ + it) · y^{σ+1+it} / ((σ+it)(σ+1+it)) dt`

(`riesz_formula`), with no truncation error.

* `rieszKernel`, `rieszIntegrand`: the kernel and the integrand;
* `riesz_perron_of`: Mellin inversion of the Riesz kernel on `re s = σ`;
* `riesz_formula`, `integrable_rieszIntegrand_line`: the exact formula and the integrability of the
  integrand on the line.
-/

@[expose] public noncomputable section

open MeasureTheory Complex ArithmeticFunction LSeries
open scoped Real

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31.PNTSW

/-- The kernel `y^{s+1} / (s (s+1))` of the Riesz-Perron integrand. -/
def rieszKernel (y : ℝ) (s : ℂ) : ℂ := (y : ℂ) ^ (s + 1) / (s * (s + 1))

/-- The integrand `-(L'/L)(s) · y^{s+1} / (s (s+1))` of the Riesz-Perron formula. -/
def rieszIntegrand (L : ℂ → ℂ) (y : ℝ) (s : ℂ) : ℂ :=
  -(deriv L s / L s) * rieszKernel y s

/-- `σ + it ≠ 0` for `σ > 0`. -/
theorem line_ne_zero {σ : ℝ} (hσ : 0 < σ) (t : ℝ) : (σ : ℂ) + t * I ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  linarith

/-- `σ + it + 1 ≠ 0` for `σ > 0`. -/
theorem line_add_one_ne_zero {σ : ℝ} (hσ : 0 < σ) (t : ℝ) : (σ : ℂ) + t * I + 1 ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  linarith

/-- `1 + t² ≤ ‖σ + it‖ ‖σ + it + 1‖` for `σ ≥ 1`. -/
theorem one_add_sq_le_norm_mul_norm {σ : ℝ} (hσ : 1 ≤ σ) (t : ℝ) :
    1 + t ^ 2 ≤ ‖(σ : ℂ) + t * I‖ * ‖(σ : ℂ) + t * I + 1‖ := by
  have hn1 : 1 + t ^ 2 ≤ ‖(σ : ℂ) + t * I‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; nlinarith [sq_nonneg t]
  have hn2 : ‖(σ : ℂ) + t * I‖ ≤ ‖(σ : ℂ) + t * I + 1‖ := by
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
      Complex.normSq_apply, Complex.normSq_apply]
    simp; nlinarith [sq_nonneg t]
  have := mul_le_mul_of_nonneg_left hn2 (norm_nonneg ((σ : ℂ) + t * I))
  nlinarith [this, hn1]

/-- `‖y^{s+1}/(s(s+1))‖ ≤ y^{σ+1} /(1 + t²)` on `re s = σ ≥ 1`. -/
theorem norm_rieszKernel_le {σ : ℝ} (hσ : 1 ≤ σ) {y : ℝ} (hy : 0 < y) (t : ℝ) :
    ‖rieszKernel y ((σ : ℂ) + t * I)‖ ≤ y ^ (σ + 1) * (1 + t ^ 2)⁻¹ := by
  unfold rieszKernel
  rw [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]
  have h3 : (((σ : ℂ) + t * I) + 1).re = σ + 1 := by simp
  rw [h3, div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hy.le _)
  have hpos : 0 < 1 + t ^ 2 := by positivity
  exact inv_anti₀ hpos (one_add_sq_le_norm_mul_norm hσ t)

/-- The Riesz kernel is continuous on the line `re s = σ > 0`. -/
theorem continuous_rieszKernel {σ : ℝ} (hσ : 0 < σ) {y : ℝ} (hy : 0 < y) :
    Continuous (fun t : ℝ => rieszKernel y ((σ : ℂ) + t * I)) := by
  unfold rieszKernel
  refine Continuous.div ?_ (by fun_prop) fun t => mul_ne_zero (line_ne_zero hσ t)
    (line_add_one_ne_zero hσ t)
  exact (by fun_prop : Continuous fun t : ℝ => (σ : ℂ) + t * I + 1).const_cpow
    (Or.inl (by exact_mod_cast hy.ne'))

/-- The Mellin transform of the Riesz kernel is integrable on the line `re s = σ`, `σ ≥ 1`. -/
theorem rieszW_verticalIntegrable_of {σ : ℝ} (hσ : 1 ≤ σ) :
    Complex.VerticalIntegrable (mellin (fun u : ℝ => (rieszW u : ℂ))) σ := by
  unfold Complex.VerticalIntegrable
  have hform : (fun y : ℝ => mellin (fun u : ℝ => (rieszW u : ℂ)) ((σ : ℂ) + y * Complex.I)) =
      fun y : ℝ => 1 / (((σ : ℂ) + y * Complex.I) * (((σ : ℂ) + y * Complex.I) + 1)) := by
    funext y
    apply mellin_rieszW
    simp; linarith
  change MeasureTheory.Integrable (fun y : ℝ => mellin (fun u : ℝ => (rieszW u : ℂ))
    ((σ : ℂ) + y * Complex.I))
  rw [hform]
  refine integrable_inv_one_add_sq.mono' ?_ ?_
  · apply Continuous.aestronglyMeasurable
    apply Continuous.div continuous_const (by fun_prop)
    intro y
    exact mul_ne_zero (line_ne_zero (by linarith) y) (line_add_one_ne_zero (by linarith) y)
  · refine Filter.Eventually.of_forall (fun y => ?_)
    rw [norm_div, norm_one, norm_mul]
    have h := one_add_sq_le_norm_mul_norm hσ y
    have hpos : 0 < 1 + y ^ 2 := by positivity
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le hpos h

/-- Perron-type formula with the Riesz kernel on the line `re s = σ`, `σ ≥ 1`: for `x > 0`,
`(1/2πi) ∫_{re s = σ} x^{-s} / (s(s+1)) ds = max (1 - x) 0`. -/
theorem riesz_perron_of {σ : ℝ} (hσ : 1 ≤ σ) {x : ℝ} (hx : 0 < x) :
    mellinInv σ (fun s : ℂ => 1 / (s * (s + 1))) x = (rieszW x : ℂ) := by
  have h := mellinInv_mellin_eq σ (fun u : ℝ => (rieszW u : ℂ)) hx
    (rieszW_mellinConvergent σ (by linarith)) (rieszW_verticalIntegrable_of hσ)
    (Complex.continuous_ofReal.comp rieszW_continuous).continuousAt
  rw [← h]
  unfold mellinInv
  congr 2
  funext y
  rw [mellin_rieszW]
  simp
  linarith

/-- `n^{-s} y^{s+1} = y (n/y)^{-s}` for positive `n` and `y`. -/
theorem natCast_cpow_mul_ofReal_cpow {n : ℕ} (hn : n ≠ 0) {y : ℝ} (hy : 0 < y) (s : ℂ) :
    (n : ℂ) ^ (-s) * (y : ℂ) ^ (s + 1) = (y : ℂ) * (((n : ℝ) / y : ℝ) : ℂ) ^ (-s) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have key : ∀ x : ℝ, 0 < x → ∀ z : ℂ, (x : ℂ) ^ z = Complex.exp (Real.log x * z) := by
    intro x hx z
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), ← Complex.ofReal_log hx.le]
  have hnc : (n : ℂ) = ((n : ℝ) : ℂ) := by simp
  have hyc : (y : ℂ) = Complex.exp (Real.log y) := by
    rw [← Complex.ofReal_exp, Real.exp_log hy]
  rw [hnc, key _ hn', key _ hy, key _ (div_pos hn' hy), Real.log_div hn'.ne' hy.ne']
  conv_rhs => rw [hyc]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The twisted von Mangoldt coefficients `χ(n) Λ(n)`. -/
def twistVonMangoldt {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ := χ n * (Λ n : ℂ)

/-- `χ(0) Λ(0) = 0`. -/
theorem twistVonMangoldt_zero {q : ℕ} (χ : DirichletCharacter ℂ q) : twistVonMangoldt χ 0 = 0 := by
  simp [twistVonMangoldt]

/-- The `n`-th term of the Perron integrand on the line `re s = σ`. -/
def perronTerm {q : ℕ} (χ : DirichletCharacter ℂ q) (σ y : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  term (twistVonMangoldt χ) ((σ : ℂ) + t * I) n * rieszKernel y ((σ : ℂ) + t * I)

/-- The Perron terms are continuous. -/
theorem continuous_perronTerm {q : ℕ} (χ : DirichletCharacter ℂ q) {σ : ℝ} (hσ : 0 < σ) {y : ℝ}
    (hy : 0 < y) (n : ℕ) : Continuous (perronTerm χ σ y n) := by
  unfold perronTerm
  refine Continuous.mul ?_ (continuous_rieszKernel hσ hy)
  rcases eq_or_ne n 0 with rfl | hn
  · simpa using continuous_const
  · have : (fun t : ℝ => term (twistVonMangoldt χ) ((σ : ℂ) + t * I) n) =
        fun t : ℝ => twistVonMangoldt χ n * (n : ℂ) ^ (-((σ : ℂ) + t * I)) := by
      funext t
      exact term_def₀ (twistVonMangoldt_zero χ) _ n
    rw [this]
    exact continuous_const.mul
      ((by fun_prop : Continuous fun t : ℝ => -((σ : ℂ) + t * I)).const_cpow
        (Or.inl (by exact_mod_cast hn)))

/-- The domination of the Perron terms by `|χ(n)Λ(n)| n^{-σ} y^{σ+1} /(1+t²)`. -/
theorem norm_perronTerm_le {q : ℕ} (χ : DirichletCharacter ℂ q) {σ : ℝ} (hσ : 1 ≤ σ) {y : ℝ}
    (hy : 0 < y) (n : ℕ) (t : ℝ) :
    ‖perronTerm χ σ y n t‖ ≤
      ‖term (twistVonMangoldt χ) (σ : ℂ) n‖ * (y ^ (σ + 1) * (1 + t ^ 2)⁻¹) := by
  unfold perronTerm
  rw [norm_mul]
  refine mul_le_mul (le_of_eq ?_) (norm_rieszKernel_le hσ hy t) (norm_nonneg _) (norm_nonneg _)
  rw [norm_term_eq, norm_term_eq]
  simp

/-- The Perron terms are integrable on the line. -/
theorem integrable_perronTerm {q : ℕ} (χ : DirichletCharacter ℂ q) {σ : ℝ} (hσ : 1 ≤ σ) {y : ℝ}
    (hy : 0 < y) (n : ℕ) : Integrable (perronTerm χ σ y n) := by
  refine (integrable_inv_one_add_sq.const_mul
    (‖term (twistVonMangoldt χ) (σ : ℂ) n‖ * y ^ (σ + 1))).mono'
    (continuous_perronTerm χ (by linarith) hy n).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => ?_)
  refine (norm_perronTerm_le χ hσ hy n t).trans (le_of_eq ?_)
  ring

/-- The integrals of the norms of the Perron terms are summable. -/
theorem summable_integral_norm_perronTerm {q : ℕ} (χ : DirichletCharacter ℂ q) {σ : ℝ}
    (hσ : 1 < σ) {y : ℝ} (hy : 0 < y) :
    Summable fun n : ℕ => ∫ t : ℝ, ‖perronTerm χ σ y n t‖ := by
  have hsum : Summable fun n : ℕ => ‖term (twistVonMangoldt χ) (σ : ℂ) n‖ :=
    (DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ (s := (σ : ℂ))
      (by simpa using hσ)).norm
  refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun t => norm_nonneg _)
    (fun n => ?_) (hsum.mul_right (y ^ (σ + 1) * π))
  calc ∫ t : ℝ, ‖perronTerm χ σ y n t‖
      ≤ ∫ t : ℝ, ‖term (twistVonMangoldt χ) (σ : ℂ) n‖ * y ^ (σ + 1) * (1 + t ^ 2)⁻¹ := by
        refine integral_mono (integrable_perronTerm χ hσ.le hy n).norm
          (integrable_inv_one_add_sq.const_mul _) fun t => ?_
        refine (norm_perronTerm_le χ hσ.le hy n t).trans (le_of_eq ?_)
        ring
    _ = ‖term (twistVonMangoldt χ) (σ : ℂ) n‖ * (y ^ (σ + 1) * π) := by
        rw [integral_const_mul, integral_univ_inv_one_add_sq]
        ring

/-- The `n`-th Perron integral: `∫ χ(n)Λ(n) n^{-s} y^{s+1}/(s(s+1)) dt = 2π χ(n)Λ(n) (y-n)^+`. -/
theorem integral_perronTerm {q : ℕ} (χ : DirichletCharacter ℂ q) {σ : ℝ} (hσ : 1 ≤ σ) {y : ℝ}
    (hy : 0 < y) (n : ℕ) :
    ∫ t : ℝ, perronTerm χ σ y n t =
      ((2 * π : ℝ) : ℂ) * (twistVonMangoldt χ n * ((max (y - n) 0 : ℝ) : ℂ)) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [perronTerm, twistVonMangoldt_zero]
  have hx : (0 : ℝ) < (n : ℝ) / y := by
    have : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    positivity
  have hp := riesz_perron_of hσ hx
  unfold mellinInv at hp
  rw [Complex.real_smul] at hp
  have hint : ∫ t : ℝ, (((n : ℝ) / y : ℝ) : ℂ) ^ (-((σ : ℂ) + t * I)) •
      (fun s : ℂ => 1 / (s * (s + 1))) ((σ : ℂ) + t * I) =
      ((2 * π : ℝ) : ℂ) * (rieszW ((n : ℝ) / y) : ℂ) := by
    have h2π : ((2 * π : ℝ) : ℂ) ≠ 0 := by
      have : (2 * π : ℝ) ≠ 0 := by positivity
      exact_mod_cast this
    rw [← hp, ← mul_assoc, ← Complex.ofReal_mul,
      mul_one_div_cancel (by positivity : (2 * π : ℝ) ≠ 0)]
    simp
  have hpt : ∀ t : ℝ, perronTerm χ σ y n t = twistVonMangoldt χ n * (y : ℂ) *
      ((((n : ℝ) / y : ℝ) : ℂ) ^ (-((σ : ℂ) + t * I)) •
        (fun s : ℂ => 1 / (s * (s + 1))) ((σ : ℂ) + t * I)) := by
    intro t
    unfold perronTerm rieszKernel
    rw [term_def₀ (twistVonMangoldt_zero χ), smul_eq_mul]
    have := natCast_cpow_mul_ofReal_cpow hn hy ((σ : ℂ) + t * I)
    calc _ = twistVonMangoldt χ n * ((n : ℂ) ^ (-((σ : ℂ) + t * I)) *
          (y : ℂ) ^ ((σ : ℂ) + t * I + 1)) / ((σ : ℂ) + t * I) /
          ((σ : ℂ) + t * I + 1) := by
          rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_inv]
          ring
      _ = _ := by
          rw [this]
          simp only [div_eq_mul_inv, mul_inv]
          ring
  simp_rw [hpt]
  rw [integral_const_mul, hint]
  have hmax : (y : ℂ) * (rieszW ((n : ℝ) / y) : ℂ) = ((max (y - n) 0 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    unfold rieszW
    rw [mul_max_of_nonneg _ _ hy.le]
    congr 1
    · field_simp
    · simp
  calc _ = twistVonMangoldt χ n * ((2 * π : ℝ) : ℂ) * ((y : ℂ) * (rieszW ((n : ℝ) / y) : ℂ)) := by
        ring
    _ = _ := by rw [hmax]; ring

/-- For `re s = σ > 1`, the sum of the Perron terms is `-(L'/L)(s) y^{s+1}/(s(s+1))`. -/
theorem tsum_perronTerm {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {σ : ℝ} (hσ : 1 < σ)
    (y : ℝ) (t : ℝ) :
    ∑' n : ℕ, perronTerm χ σ y n t =
      rieszIntegrand (DirichletCharacter.LFunction χ) y ((σ : ℂ) + t * I) := by
  have hs : 1 < ((σ : ℂ) + t * I).re := by simpa using hσ
  unfold perronTerm
  rw [tsum_mul_right]
  unfold rieszIntegrand
  congr 1
  have h1 : (∑' n : ℕ, term (twistVonMangoldt χ) ((σ : ℂ) + t * I) n) =
      LSeries (fun n : ℕ => χ n * (Λ n : ℂ)) ((σ : ℂ) + t * I) := rfl
  rw [h1]
  have h2 : LSeries (fun n : ℕ => χ n * (Λ n : ℂ)) ((σ : ℂ) + t * I) =
      -deriv (LSeries fun n : ℕ => (χ n : ℂ)) ((σ : ℂ) + t * I) /
        LSeries (fun n : ℕ => (χ n : ℂ)) ((σ : ℂ) + t * I) :=
    DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs
  rw [h2, neg_div, DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs,
    DirichletCharacter.LFunction_eq_LSeries χ hs]

/-- **The exact Perron formula for the Riesz mean.**  For every Dirichlet character `χ`, `σ > 1`
and `y > 0`: `2π ∑_{n ≤ y} χ(n) Λ(n) (y - n) =
∫ -(L'/L)(σ+it) y^{σ+1+it}/((σ+it)(σ+1+it)) dt`. -/
theorem riesz_formula {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {σ : ℝ} (hσ : 1 < σ)
    {y : ℝ} (hy : 0 < y) :
    ((2 * π : ℝ) : ℂ) * ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, χ n * (Λ n : ℂ) * ((y : ℂ) - n) =
      ∫ t : ℝ, rieszIntegrand (DirichletCharacter.LFunction χ) y ((σ : ℂ) + t * I) := by
  have h1 := integral_tsum_of_summable_integral_norm
    (fun n => integrable_perronTerm χ hσ.le hy n) (summable_integral_norm_perronTerm χ hσ hy)
  have h2 : (∫ t : ℝ, ∑' n : ℕ, perronTerm χ σ y n t) =
      ∫ t : ℝ, rieszIntegrand (DirichletCharacter.LFunction χ) y ((σ : ℂ) + t * I) := by
    congr 1
    funext t
    exact tsum_perronTerm χ hσ y t
  rw [← h2, ← h1]
  simp_rw [integral_perronTerm χ hσ.le hy]
  rw [tsum_mul_left]
  congr 1
  rw [tsum_eq_sum (s := Finset.Icc 1 ⌊y⌋₊)]
  · refine Finset.sum_congr rfl fun n hn => ?_
    have hn' := Finset.mem_Icc.mp hn
    have hle : (n : ℝ) ≤ y := (Nat.cast_le.mpr hn'.2).trans (Nat.floor_le hy.le)
    rw [max_eq_left (by linarith)]
    simp [twistVonMangoldt]
  · intro n hn
    rcases eq_or_ne n 0 with rfl | hn0
    · simp [twistVonMangoldt_zero]
    · have hgt : y < n := by
        refine (Nat.floor_lt hy.le).mp ?_
        rw [Finset.mem_Icc] at hn
        omega
      rw [max_eq_right (by linarith)]
      simp

/-- The Perron integrand `-(L'/L)(σ+it) y^{σ+1+it}/((σ+it)(σ+1+it))` is integrable on the line
`re s = σ`, `σ > 1` (the sum of the Perron terms, uniformly dominated by `C y^{σ+1} /(1+t²)`). -/
theorem integrable_rieszIntegrand_line {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {σ : ℝ}
    (hσ : 1 < σ) {y : ℝ} (hy : 0 < y) :
    Integrable fun t : ℝ =>
      rieszIntegrand (DirichletCharacter.LFunction χ) y ((σ : ℂ) + t * I) := by
  have heq : (fun t : ℝ => rieszIntegrand (DirichletCharacter.LFunction χ) y
      ((σ : ℂ) + t * I)) = fun t : ℝ => ∑' n : ℕ, perronTerm χ σ y n t :=
    funext fun t => (tsum_perronTerm χ hσ y t).symm
  rw [heq]
  have hsum : Summable fun n : ℕ => ‖term (twistVonMangoldt χ) (σ : ℂ) n‖ :=
    (DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ (s := (σ : ℂ))
      (by simpa using hσ)).norm
  have hinv : ∀ t : ℝ, (1 + t ^ 2)⁻¹ ≤ 1 := fun t =>
    inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg t])
  have hy3 : 0 ≤ y ^ (σ + 1) := Real.rpow_nonneg hy.le _
  have hcont : Continuous fun t : ℝ => ∑' n : ℕ, perronTerm χ σ y n t := by
    refine continuous_tsum (fun n => continuous_perronTerm χ (by linarith) hy n)
      (hsum.mul_right (y ^ (σ + 1))) fun n t => ?_
    refine (norm_perronTerm_le χ hσ.le hy n t).trans ?_
    exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right hy3 (hinv t)) (norm_nonneg _)
  refine (integrable_inv_one_add_sq.const_mul ((∑' n : ℕ, ‖term (twistVonMangoldt χ) (σ : ℂ) n‖) *
    y ^ (σ + 1))).mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
  have hs : Summable fun n : ℕ => ‖perronTerm χ σ y n t‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => norm_perronTerm_le χ hσ.le hy n t) (hsum.mul_right _)
  calc ‖∑' n : ℕ, perronTerm χ σ y n t‖ ≤ ∑' n : ℕ, ‖perronTerm χ σ y n t‖ :=
        norm_tsum_le_tsum_norm hs
    _ ≤ ∑' n : ℕ, ‖term (twistVonMangoldt χ) (σ : ℂ) n‖ * (y ^ (σ + 1) * (1 + t ^ 2)⁻¹) :=
        hs.tsum_le_tsum (fun n => norm_perronTerm_le χ hσ.le hy n t) (hsum.mul_right _)
    _ = (∑' n : ℕ, ‖term (twistVonMangoldt χ) (σ : ℂ) n‖) * (y ^ (σ + 1) * (1 + t ^ 2)⁻¹) :=
        tsum_mul_right
    _ = _ := by ring

end PrimeCarleson.Proof.Fplus31.PNTSW
