module

public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.PNat.Basic
public import Mathlib.Analysis.Complex.Basic

/-!
# Expectations and normalized `L^p` norms on finite subsets of `ℤ`

The notation of `sources/Variational_Carleson.tex` (Source: main paper `s:Prelim`, L682–L695): for
an integer `N ≥ 1` the interval `[N] = {1, …, N}` (`bracket`), and for a finite set `X ⊆ ℤ`

* `expect X f = E_{n ∈ X} f(n) = |X|⁻¹ ∑_{n ∈ X} f(n)` (`expect`, `expect_bracket`);
* `lpNormOn p X f = ‖f‖_{L^p(X)}`, the normalized norm with
  `‖f‖_{L^p(X)}^p = |X|⁻¹ ∑_{n ∈ X} |f(n)|^p` (`lpNormOn_rpow`), in the shape
  `(|X|⁻¹ ∑ ‖f n‖^p)^{1/p}` of `Common/GowersLp.lean` (`lpNormOn_two`).

The norms `‖·‖_{L^p([-N, 2N])}` and `‖·‖_{L^p([2^k])}` of the later statements are the
instances `X = Icc (-N) (2N)` and `X = Icc 1 (2^k)`. The formulas are the paper's verbatim:
they have source meaning for `X` nonempty and `p > 0`, and every lemma that depends on this
carries the hypothesis `0 < p` (and `1 ≤ p` for Minkowski, `lpNormOn_add_le`).
-/

@[expose] public noncomputable section

open scoped ComplexConjugate

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

/-- The interval `[N] = {1, …, N}` of integers (Source: main paper `s:Prelim`, L682–L684),
for `N : ℕ+`. -/
def bracket (N : ℕ+) : Finset ℤ := Finset.Icc 1 (N : ℤ)

/-- Membership in `[N]`. -/
theorem mem_bracket {N : ℕ+} {n : ℤ} : n ∈ bracket N ↔ 1 ≤ n ∧ n ≤ (N : ℤ) := by
  simp [bracket]

/-- `|[N]| = N`. -/
theorem card_bracket (N : ℕ+) : (bracket N).card = (N : ℕ) := by
  simp [bracket, Int.card_Icc]

/-- `[N]` is nonempty. -/
theorem bracket_nonempty (N : ℕ+) : (bracket N).Nonempty :=
  ⟨1, mem_bracket.2 ⟨le_rfl, by exact_mod_cast N.pos⟩⟩

/-- The expectation `E_{n ∈ X} f(n) := |X|⁻¹ ∑_{n ∈ X} f(n)` (Source: main paper `s:Prelim`,
L685–L689), for a finite `X ⊆ ℤ`. -/
def expect (X : Finset ℤ) (f : ℤ → ℂ) : ℂ := (X.card : ℂ)⁻¹ * ∑ n ∈ X, f n

/-- `E_{n ∈ [N]} f(n) = N⁻¹ ∑_{n ∈ [N]} f(n)` (L682-L684). -/
theorem expect_bracket (N : ℕ+) (f : ℤ → ℂ) :
    expect (bracket N) f = (N : ℂ)⁻¹ * ∑ n ∈ Finset.Icc (1 : ℤ) N, f n := by
  simp [expect, bracket]

/-- The normalized `L^p(X)` norm `‖f‖_{L^p(X)} := (|X|⁻¹ ∑_{n ∈ X} |f(n)|^p)^{1/p}`
(Source: main paper `s:Prelim`, L690–L695), for a finite `X ⊆ ℤ`. -/
def lpNormOn (p : ℝ) (X : Finset ℤ) (f : ℤ → ℂ) : ℝ :=
  ((X.card : ℝ)⁻¹ * ∑ n ∈ X, ‖f n‖ ^ p) ^ (1 / p)

/-- `‖f‖_{L^p(X)} ≥ 0`. -/
theorem lpNormOn_nonneg (p : ℝ) (X : Finset ℤ) (f : ℤ → ℂ) : 0 ≤ lpNormOn p X f :=
  Real.rpow_nonneg (mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _)) _

/-- The defining identity `‖f‖_{L^p(X)}^p = |X|⁻¹ ∑_{n ∈ X} |f(n)|^p` (L690-L695). -/
theorem lpNormOn_rpow {p : ℝ} (hp : 0 < p) (X : Finset ℤ) (f : ℤ → ℂ) :
    lpNormOn p X f ^ p = (X.card : ℝ)⁻¹ * ∑ n ∈ X, ‖f n‖ ^ p := by
  rw [lpNormOn, ← Real.rpow_mul (mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _)),
    one_div, inv_mul_cancel₀ hp.ne', Real.rpow_one]

/-- The case `p = 2`, in the shape used in `Common/GowersLp.lean`:
`‖f‖_{L²(X)} = (|X|⁻¹ ∑ ‖f n‖²)^{1/2}`. -/
theorem lpNormOn_two (X : Finset ℤ) (f : ℤ → ℂ) :
    lpNormOn 2 X f = ((X.card : ℝ)⁻¹ * ∑ n ∈ X, ‖f n‖ ^ 2) ^ ((1 : ℝ) / 2) := by
  simp [lpNormOn]

/-- The case `p = 2` as a square root. -/
theorem lpNormOn_two_eq_sqrt (X : Finset ℤ) (f : ℤ → ℂ) :
    lpNormOn 2 X f = Real.sqrt ((X.card : ℝ)⁻¹ * ∑ n ∈ X, ‖f n‖ ^ 2) := by
  rw [lpNormOn_two, Real.sqrt_eq_rpow]

/-- `‖0‖_{L^p(X)} = 0` for `p > 0`. -/
theorem lpNormOn_zero {p : ℝ} (hp : 0 < p) (X : Finset ℤ) : lpNormOn p X 0 = 0 := by
  simp [lpNormOn, Real.zero_rpow hp.ne', hp.ne']

/-- The prefactor form `‖f‖_{L^p(X)} = (|X|⁻¹)^{1/p} (∑ ‖f n‖^p)^{1/p}`. -/
theorem lpNormOn_eq_mul (p : ℝ) (X : Finset ℤ) (f : ℤ → ℂ) :
    lpNormOn p X f = ((X.card : ℝ)⁻¹) ^ (1 / p) * (∑ n ∈ X, ‖f n‖ ^ p) ^ (1 / p) := by
  rw [lpNormOn, Real.mul_rpow (inv_nonneg.2 (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _)]

/-- Homogeneity: `‖c f‖_{L^p(X)} = |c| ‖f‖_{L^p(X)}` for `p > 0`. -/
theorem lpNormOn_smul {p : ℝ} (hp : 0 < p) (c : ℂ) (X : Finset ℤ) (f : ℤ → ℂ) :
    lpNormOn p X (c • f) = ‖c‖ * lpNormOn p X f := by
  have h : ∀ n, ‖(c • f) n‖ ^ p = ‖c‖ ^ p * ‖f n‖ ^ p := fun n => by
    simp [Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
  rw [lpNormOn_eq_mul, lpNormOn_eq_mul]
  simp_rw [h]
  rw [← Finset.mul_sum, Real.mul_rpow (Real.rpow_nonneg (norm_nonneg _) _)
    (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _),
    ← Real.rpow_mul (norm_nonneg _), mul_one_div_cancel hp.ne', Real.rpow_one]
  ring

/-- **Minkowski's inequality** for the normalized norms, `1 ≤ p`:
`‖f + g‖_{L^p(X)} ≤ ‖f‖_{L^p(X)} + ‖g‖_{L^p(X)}`. -/
theorem lpNormOn_add_le {p : ℝ} (hp : 1 ≤ p) (X : Finset ℤ) (f g : ℤ → ℂ) :
    lpNormOn p X (f + g) ≤ lpNormOn p X f + lpNormOn p X g := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hmink := Real.Lp_add_le_of_nonneg (s := X) (f := fun n => ‖f n‖) (g := fun n => ‖g n‖) hp
    (fun _ _ => norm_nonneg _) (fun _ _ => norm_nonneg _)
  have h1 : (∑ n ∈ X, ‖(f + g) n‖ ^ p) ^ (1 / p) ≤
      (∑ n ∈ X, (‖f n‖ + ‖g n‖) ^ p) ^ (1 / p) := by
    refine Real.rpow_le_rpow (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _)
      (Finset.sum_le_sum fun n _ => ?_) (by positivity)
    exact Real.rpow_le_rpow (norm_nonneg _) (by simpa using norm_add_le (f n) (g n)) hp0.le
  rw [lpNormOn_eq_mul, lpNormOn_eq_mul, lpNormOn_eq_mul, ← mul_add]
  exact mul_le_mul_of_nonneg_left (h1.trans hmink) (Real.rpow_nonneg (inv_nonneg.2
    (Nat.cast_nonneg _)) _)

end PrimeCarleson.Proof.Paper
