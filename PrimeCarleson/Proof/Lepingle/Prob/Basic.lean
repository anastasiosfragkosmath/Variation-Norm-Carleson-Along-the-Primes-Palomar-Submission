module

public import Mathlib.Probability.Martingale.OptionalSampling
public import Mathlib.Probability.Martingale.OptionalStopping
public import Mathlib.Probability.Process.Predictable
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

/-!
# Maximal and square functions of a martingale: definitions and basic API

Definitions of Zorin-Kranich's notes (P. Zorin-Kranich, *Lecture notes on martingale
inequalities*, arXiv:2404.17197v1), `00-background.tex` and `01-BDG.tex`, for the Lépingle part
of the proof (Source: Zorin-Kranich's notes, 00-background.tex L3–L126 and 01-BDG.tex L7–L16,
L18–L36, L129–L135).

The filtered probability space is `(Ω, (ℱ n)_{n : ℕ}, μ)` with Mathlib's
`MeasureTheory.Filtration ℕ m0`; martingales are Mathlib's `MeasureTheory.Martingale`
(`StronglyAdapted` and `μ[f m | ℱ n] =ᵐ f n`), valued in `E` (here `𝕜 = ℝ` or `ℂ`, via `RCLike`).

* `incr f k = f (k+1) - f k` (the increment `df_{k+1}` of Zorin-Kranich's notes);
* `maxUpTo f n = sup_{k ≤ n} ‖f k‖` (`Mf_n`), `maxFn f = sup_n ‖f n‖` (`Mf`), in `ℝ≥0∞`;
* `sqUpTo f n = (∑_{k<n} ‖incr f k‖²)^{1/2}` (`Sf_n` when `f 0 = 0`), `sqFn f = sup_n sqUpTo f n`
  (`Sf = (∑_k ‖df_k‖²)^{1/2}`), in `ℝ≥0∞`.

The values are in `ℝ≥0∞` so that `Mf` and `Sf` need no finiteness hypothesis; for a martingale
that is constant after time `N` they equal `maxUpTo f N` and `sqUpTo f N`.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Finset
open scoped ENNReal NNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Lepingle

section Defs

variable {Ω : Type*} {E : Type*} [NormedAddCommGroup E]

/-- The increment `incr f k = f_{k+1} - f_k` of a process (`df_{k+1}` in the notation of
Zorin-Kranich's notes). -/
def incr (f : ℕ → Ω → E) (k : ℕ) (ω : Ω) : E := f (k + 1) ω - f k ω

/-- The maximal function up to time `n`: `Mf_n(ω) = sup_{k ≤ n} ‖f_k(ω)‖`
(Zorin-Kranich's notes, Definition 1.1), valued in `ℝ≥0∞`. -/
def maxUpTo (f : ℕ → Ω → E) (n : ℕ) (ω : Ω) : ℝ≥0∞ := (range (n + 1)).sup fun k => ‖f k ω‖ₑ

/-- The maximal function `Mf(ω) = sup_n ‖f_n(ω)‖`. -/
def maxFn (f : ℕ → Ω → E) (ω : Ω) : ℝ≥0∞ := ⨆ n, ‖f n ω‖ₑ

/-- The square function up to time `n`: `(∑_{k < n} ‖f_{k+1} - f_k‖²)^{1/2}`. For `f 0 = 0` this is
`Sf_n = (∑_{k ≤ n} ‖df_k‖²)^{1/2}` of Zorin-Kranich's notes, Definition 1.6. -/
def sqUpTo (f : ℕ → Ω → E) (n : ℕ) (ω : Ω) : ℝ≥0∞ :=
  (∑ k ∈ range n, ‖incr f k ω‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)

/-- The square function `Sf = sup_n Sf_n = (∑_k ‖df_k‖²)^{1/2}`. -/
def sqFn (f : ℕ → Ω → E) (ω : Ω) : ℝ≥0∞ := ⨆ n, sqUpTo f n ω

variable {f : ℕ → Ω → E} {ω : Ω}

theorem incr_apply (f : ℕ → Ω → E) (k : ℕ) (ω : Ω) : incr f k ω = f (k + 1) ω - f k ω := rfl

theorem le_maxUpTo {n k : ℕ} (hk : k ≤ n) : ‖f k ω‖ₑ ≤ maxUpTo f n ω :=
  le_sup (f := fun k => ‖f k ω‖ₑ) (mem_range.2 (Nat.lt_succ_of_le hk))

theorem maxUpTo_le_iff {n : ℕ} {c : ℝ≥0∞} :
    maxUpTo f n ω ≤ c ↔ ∀ k ≤ n, ‖f k ω‖ₑ ≤ c := by
  simp only [maxUpTo, Finset.sup_le_iff, mem_range, Nat.lt_succ_iff]

theorem maxUpTo_zero (f : ℕ → Ω → E) (ω : Ω) : maxUpTo f 0 ω = ‖f 0 ω‖ₑ := by
  simp [maxUpTo]

theorem maxUpTo_succ (f : ℕ → Ω → E) (n : ℕ) (ω : Ω) :
    maxUpTo f (n + 1) ω = max (maxUpTo f n ω) ‖f (n + 1) ω‖ₑ := by
  simp only [maxUpTo, Finset.range_add_one (n := n + 1), Finset.sup_insert]
  rw [max_comm]

theorem le_maxFn (n : ℕ) : ‖f n ω‖ₑ ≤ maxFn f ω := le_iSup (fun n => ‖f n ω‖ₑ) n

theorem maxUpTo_le_maxFn (n : ℕ) : maxUpTo f n ω ≤ maxFn f ω :=
  maxUpTo_le_iff.2 fun k _ => le_maxFn k

theorem maxFn_le_iff {c : ℝ≥0∞} : maxFn f ω ≤ c ↔ ∀ n, ‖f n ω‖ₑ ≤ c := iSup_le_iff

theorem sqUpTo_zero (f : ℕ → Ω → E) (ω : Ω) : sqUpTo f 0 ω = 0 := by
  simp [sqUpTo]

theorem sqUpTo_mono {n n' : ℕ} (h : n ≤ n') : sqUpTo f n ω ≤ sqUpTo f n' ω := by
  unfold sqUpTo
  gcongr

theorem sqUpTo_le_sqFn (n : ℕ) : sqUpTo f n ω ≤ sqFn f ω := le_iSup (fun n => sqUpTo f n ω) n

theorem sqFn_le_iff {c : ℝ≥0∞} : sqFn f ω ≤ c ↔ ∀ n, sqUpTo f n ω ≤ c := iSup_le_iff

/-- `‖f_{k+1} - f_k‖ ≤ 2 Mf`. -/
theorem enorm_incr_le_two_mul_maxFn (k : ℕ) : ‖incr f k ω‖ₑ ≤ 2 * maxFn f ω := by
  calc ‖incr f k ω‖ₑ ≤ ‖f (k + 1) ω‖ₑ + ‖f k ω‖ₑ := enorm_sub_le
    _ ≤ maxFn f ω + maxFn f ω := add_le_add (le_maxFn _) (le_maxFn _)
    _ = 2 * maxFn f ω := (two_mul _).symm

end Defs

section Measurability

variable {Ω : Type*} {m : MeasurableSpace Ω} {𝕜 : Type*} [RCLike 𝕜] {f : ℕ → Ω → 𝕜}

theorem measurable_incr (hf : ∀ k, Measurable (f k)) (k : ℕ) : Measurable (incr f k) :=
  (hf (k + 1)).sub (hf k)

theorem measurable_maxUpTo {n : ℕ} (hf : ∀ k ≤ n, Measurable (f k)) :
    Measurable (maxUpTo f n) := by
  induction n with
  | zero =>
    have : maxUpTo f 0 = fun ω => ‖f 0 ω‖ₑ := funext fun ω => maxUpTo_zero f ω
    rw [this]
    exact (hf 0 le_rfl).enorm
  | succ n ih =>
    have : maxUpTo f (n + 1) = fun ω => max (maxUpTo f n ω) ‖f (n + 1) ω‖ₑ :=
      funext fun ω => maxUpTo_succ f n ω
    rw [this]
    exact (ih fun k hk => hf k (hk.trans n.le_succ)).max (hf (n + 1) le_rfl).enorm

theorem measurable_maxFn (hf : ∀ k, Measurable (f k)) : Measurable (maxFn f) :=
  Measurable.iSup fun k => (hf k).enorm

theorem measurable_sqUpTo {n : ℕ} (hf : ∀ k ≤ n, Measurable (f k)) : Measurable (sqUpTo f n) := by
  unfold sqUpTo
  refine Measurable.pow_const (Finset.measurable_sum _ fun k hk => ?_) _
  have hk' : k + 1 ≤ n := Finset.mem_range.1 hk
  exact (((hf (k + 1) hk').sub (hf k (k.le_succ.trans hk'))).enorm).pow_const _

end Measurability

end PrimeCarleson.Proof.Lepingle
