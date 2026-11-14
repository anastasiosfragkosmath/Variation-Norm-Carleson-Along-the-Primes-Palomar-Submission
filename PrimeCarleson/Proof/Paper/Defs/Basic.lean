module

public import PrimeCarleson.Proof.Common.Variation
public import PrimeCarleson.Proof.Goal0.Basic
public import Mathlib.Analysis.Normed.Group.AddCircle
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Data.ZMod.Basic

/-!
# Basic notation of `sources/Variational_Carleson.tex`

The definitions of the introduction (L248-L259) and of the general notation of the
Preliminaries (L549-L571), with the characterization lemmas the later files use.

Paper steps proved here:

* the `r`-variation (Source: main paper, L248–L256): the `r`-variation is the
  `PrimeCarleson.rVariationOn` (`rVariationOn_le_iff`: it is the supremum over finite increasing
  subsequences of the index set);
* the pointwise variation (Source: main paper `e:fxnvar`, L256–L259):
  `pointwiseVariation` for the index set `𝕋 = [0, 1)`, `V^r(f_λ(x) : λ ∈ 𝕋)`;
* the basic notation (Source: main paper, L549–L563): `‖x‖_𝕋` (`torusNorm`, with
  `torusNorm_le_abs_sub`) and `Mod_θ` (`modZ`);
* the dilation (Source: main paper, L568–L571): the `L¹`-normalized dilation `φ_N(x) = N⁻¹ φ(x / N)`
  (`dilate`, with `contDiff_dilate`).

Conventions: `V^r` is `ℝ≥0∞`-valued (the `rVariationOn`); `𝕋 = [0, 1)` as in the
`rVariation`; `N : ℝ` for `φ_N` (the paper's `N(Q)` is real).
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal ComplexConjugate ContDiff

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Goal0

/-! ### The `r`-variation (L248-L256) -/

/-- The `r`-variation is bounded by `B` exactly when every finite increasing subsequence
of `S` gives at most `B` (Source: main paper, L248–L256: the supremum over finite increasing
subsequences). -/
theorem rVariationOn_le_iff {r : ℝ} {S : Set ℝ} {a : ℝ → ℂ} {B : ℝ≥0∞} :
    rVariationOn r S a ≤ B ↔ ∀ (J : ℕ) (t : Fin (J + 1) → ℝ), StrictMono t → (∀ i, t i ∈ S) →
      (∑ i : Fin J, ‖a (t i.castSucc) - a (t i.succ)‖ₑ ^ r) ^ (1 / r) ≤ B :=
  ⟨fun h _ _ hm hS => (MswTransference.le_rVariationOn hm hS).trans h,
    MswTransference.rVariationOn_le⟩

/-- `(x^r)^{1/r} = x` in `ℝ≥0∞` for `r > 0`. -/
theorem enorm_rpow_rpow_one_div {r : ℝ} (hr : 0 < r) (x : ℝ≥0∞) : (x ^ r) ^ (1 / r) = x := by
  rw [← ENNReal.rpow_mul, mul_one_div_cancel hr.ne', ENNReal.rpow_one]

/-- A two-point increasing subsequence: `|a_λ - a_λ'| ≤ V^r` for `λ < λ'` in `S`. -/
theorem enorm_sub_le_rVariationOn_of_lt {r : ℝ} (hr : 0 < r) {S : Set ℝ} {a : ℝ → ℂ}
    {l l' : ℝ} (hl : l ∈ S) (hl' : l' ∈ S) (hlt : l < l') :
    ‖a l - a l'‖ₑ ≤ rVariationOn r S a := by
  have hm : StrictMono (![l, l'] : Fin 2 → ℝ) := by
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    fin_cases i
    simpa using hlt
  have hS : ∀ i, (![l, l'] : Fin 2 → ℝ) i ∈ S := by
    intro i
    fin_cases i <;> simp [hl, hl']
  have h := MswTransference.le_rVariationOn (r := r) (a := a) hm hS
  simp only [Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero,
    Fin.castSucc_zero, Fin.succ_zero_eq_one, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  rwa [enorm_rpow_rpow_one_div hr] at h

/-- Any two points of `S` are at distance at most `V^r`, for every `r > 0`. -/
theorem enorm_sub_le_rVariationOn {r : ℝ} (hr : 0 < r) {S : Set ℝ} {a : ℝ → ℂ} {l l' : ℝ}
    (hl : l ∈ S) (hl' : l' ∈ S) : ‖a l - a l'‖ₑ ≤ rVariationOn r S a := by
  rcases lt_trichotomy l l' with hlt | rfl | hgt
  · exact enorm_sub_le_rVariationOn_of_lt hr hl hl' hlt
  · simp
  · rw [enorm_sub_rev]
    exact enorm_sub_le_rVariationOn_of_lt hr hl' hl hgt

/-! ### The pointwise variation of a family of functions (L256-L259) -/

/-- The pointwise `r`-variation over the index set `𝕋 = [0, 1)` (the `rVariation`). -/
def pointwiseVariation {X : Type*} (r : ℝ) (f : ℝ → X → ℂ) (x : X) : ℝ≥0∞ :=
  rVariation r fun l => f l x

/-! ### The basic notation (L549-L563) -/

/-- `‖x‖_𝕋 := min_{k ∈ ℤ} |x - k|` (Source: main paper, L549–L554): the infimum
over `k ∈ ℤ` of `|x - k|`. -/
def torusNorm (x : ℝ) : ℝ := ⨅ k : ℤ, |x - (k : ℝ)|

/-- `‖x‖_𝕋 ≤ |x - k|` for every integer `k`. -/
theorem torusNorm_le_abs_sub (x : ℝ) (k : ℤ) : torusNorm x ≤ |x - (k : ℝ)| :=
  ciInf_le ⟨0, by rintro _ ⟨k, rfl⟩; exact abs_nonneg _⟩ k

/-- The modulation `Mod_θ g(x) := e(θ x) g(x)` of a function on `ℤ` (Source: main paper,
L555–L558). -/
def modZ (θ : ℝ) (g : ℤ → ℂ) (x : ℤ) : ℂ := e (θ * x) * g x

/-! ### The `L¹`-normalized dilation (L568-L571) -/

/-- The `L¹`-normalized dilation `φ_N(x) := N⁻¹ φ(x / N)` (Source: main paper, L568–L571), for a
function `φ` on `ℝ` and `N > 0`; the paper evaluates it at
integers `x = n`. -/
def dilate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (N : ℝ) (φ : ℝ → E) (x : ℝ) : E :=
  (1 / N) • φ (x / N)

section Dilate

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Smoothness of `φ` passes to `φ_N`. -/
theorem contDiff_dilate {n : WithTop ℕ∞} {φ : ℝ → E} (hφ : ContDiff ℝ n φ) (N : ℝ) :
    ContDiff ℝ n (dilate N φ) :=
  ContDiff.smul contDiff_const (hφ.comp (contDiff_id.div_const N))

end Dilate

end PrimeCarleson.Proof.Paper
