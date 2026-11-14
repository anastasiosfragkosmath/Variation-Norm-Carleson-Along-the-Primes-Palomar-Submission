module

public import PrimeCarleson.Frozen.PartialFourierIntegral
public import PrimeCarleson.Proof.Oplus.Defs.Dyadic
public import PrimeCarleson.Proof.Common.FourierR
public import PrimeCarleson.Proof.Goal0.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.NumberTheory.Real.Irrational

/-!
# The partial Fourier integral and the linearized operator of [O+]

[O+]:

* L679-L690 (Source: [O+], L679–L690): for a Schwartz function `f` on `ℝ`,
  `𝒮[f](ξ, x) = ∫_{-∞}^ξ f̂(η) e^{2πiηx} dη` with `f̂(η) = ∫ f(y) e^{-2πiyη} dy`. This is the
  `PrimeCarleson.partialFourierIntegral` (reused, not redefined); here its API:
  `partialFourierIntegral_eq` (in terms of Mathlib's `𝓕`), integrability of the integrand
  (`integrable_fourier_mul_e`), and the difference formula
  `𝒮[f](ξ', x) - 𝒮[f](ξ, x) = ∫_{ξ}^{ξ'} f̂(η) e^{2πiηx} dη` (L880-L883),
  `partialFourierIntegral_sub_eq_integral_Ioc`.
* L905-L916 (Source: [O+], L905–L916): linearizing data `K ∈ ℕ`, a finite
  set `Ξ`, measurable `ξ_0(x) < ⋯ < ξ_K(x)` with values in `Ξ`, measurable `a_1(x), …, a_K(x)` with
  `|a_1(x)|^{r'} + ⋯ + |a_K(x)|^{r'} = 1`, and the operator
  `𝒮'[f](x) = ∑_{k=1}^K (𝒮[f](ξ_k(x), x) - 𝒮[f](ξ_{k-1}(x), x)) a_k(x)`.

`AvoidsDyadicEndpoints Ξ` is the standing assumption of L897-L899 that `Ξ` contains no number
`n 2^m` (no endpoint of a dyadic interval). It is kept apart from the structure, which is the data
of L905-L912 verbatim.

Indexing: the data are `ξ : Fin (K+1) → ℝ → ℝ` and `a : Fin K → ℝ → ℂ`; for `k : Fin K` the
function `a k` is the paper's `a_{k+1}`, so that `a k` is paired with `ξ k.castSucc = ξ_{k}`
(the paper's `ξ_{(k+1)-1}`) and `ξ k.succ` (the paper's `ξ_{k+1}`). The exponent `r'` is
`Real.conjExponent r = r / (r - 1)`. No range of `r` is required by the definition (the paper
takes `r > 2` in the theorems).
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped FourierTransform SchwartzMap

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

open PrimeCarleson PrimeCarleson.Proof.Common PrimeCarleson.Proof.Goal0

/-! ### API for `partialFourierIntegral` -/

/-- `𝒮[f](ξ, x) = ∫_{-∞}^ξ f̂(η) e(ηx) dη` with Mathlib's Fourier transform `𝓕`. -/
theorem partialFourierIntegral_eq (f : 𝓢(ℝ, ℂ)) (ξ x : ℝ) :
    partialFourierIntegral f ξ x = ∫ η in Iic ξ, 𝓕 (⇑f) η * e (η * x) := by
  unfold partialFourierIntegral
  refine setIntegral_congr_fun measurableSet_Iic fun η _ => ?_
  rw [fourier_eq_integral_e]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  ring

/-- The Fourier transform of a Schwartz function is Schwartz, hence `f̂ e(·x)` is integrable. -/
theorem integrable_fourier_mul_e (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    Integrable (fun η : ℝ => 𝓕 (⇑f) η * e (η * x)) := by
  have h1 : Integrable (⇑(𝓕 f : 𝓢(ℝ, ℂ))) := (𝓕 f : 𝓢(ℝ, ℂ)).integrable
  have h2 : (⇑(𝓕 f : 𝓢(ℝ, ℂ))) = 𝓕 (⇑f) := SchwartzMap.fourier_coe f
  rw [h2] at h1
  refine h1.norm.mono' ((h1.aestronglyMeasurable).mul ?_) (Filter.Eventually.of_forall fun η => ?_)
  · exact (continuous_e.comp (continuous_id.mul continuous_const)).aestronglyMeasurable
  · rw [norm_mul, norm_e, mul_one]

/-- `𝒮[f](ξ', x) - 𝒮[f](ξ, x) = ∫_ξ^{ξ'} f̂(η) e(ηx) dη` (L880-L883 of [O+]). -/
theorem partialFourierIntegral_sub_eq_intervalIntegral (f : 𝓢(ℝ, ℂ)) (ξ ξ' x : ℝ) :
    partialFourierIntegral f ξ' x - partialFourierIntegral f ξ x =
      ∫ η in ξ..ξ', 𝓕 (⇑f) η * e (η * x) := by
  rw [partialFourierIntegral_eq, partialFourierIntegral_eq]
  exact intervalIntegral.integral_Iic_sub_Iic (integrable_fourier_mul_e f x).integrableOn
    (integrable_fourier_mul_e f x).integrableOn

/-- For `ξ ≤ ξ'`: `𝒮[f](ξ', x) - 𝒮[f](ξ, x) = ∫_{(ξ, ξ']} f̂(η) e(ηx) dη`. -/
theorem partialFourierIntegral_sub_eq_integral_Ioc (f : 𝓢(ℝ, ℂ)) {ξ ξ' : ℝ} (h : ξ ≤ ξ')
    (x : ℝ) :
    partialFourierIntegral f ξ' x - partialFourierIntegral f ξ x =
      ∫ η in Ioc ξ ξ', 𝓕 (⇑f) η * e (η * x) := by
  rw [partialFourierIntegral_sub_eq_intervalIntegral, intervalIntegral.integral_of_le h]

/-- The same with the open interval `(ξ, ξ')`, as the display at L880-L883 of [O+]. -/
theorem partialFourierIntegral_sub_eq_integral_Ioo (f : 𝓢(ℝ, ℂ)) {ξ ξ' : ℝ} (h : ξ ≤ ξ')
    (x : ℝ) :
    partialFourierIntegral f ξ' x - partialFourierIntegral f ξ x =
      ∫ η in Ioo ξ ξ', 𝓕 (⇑f) η * e (η * x) := by
  rw [partialFourierIntegral_sub_eq_integral_Ioc f h, integral_Ioc_eq_integral_Ioo]

/-! ### Linearizing data and the linearized operator -/

/-- The linearizing data of [O+] L905-L912 for the exponent `r` (`r' = r/(r-1)`): `K ∈ ℕ`, a
finite set `Ξ ⊆ ℝ`, measurable functions `ξ_0(x) < ⋯ < ξ_K(x)` with values in `Ξ`, and measurable
`a_1(x), …, a_K(x)` with `∑ |a_k(x)|^{r'} = 1`. The paper's `a_{k+1}` is `a k` for `k : Fin K`. -/
structure Linearization (r : ℝ) where
  /-- The number `K` of frequency increments. -/
  K : ℕ
  /-- The finite set `Ξ` of values of the `ξ_k`. -/
  Ξ : Finset ℝ
  /-- The frequencies `ξ_0(x) < ⋯ < ξ_K(x)`. -/
  ξ : Fin (K + 1) → ℝ → ℝ
  /-- The coefficients; `a k` is the paper's `a_{k+1}`. -/
  a : Fin K → ℝ → ℂ
  measurable_ξ : ∀ k, Measurable (ξ k)
  strictMono_ξ : ∀ x, StrictMono fun k => ξ k x
  ξ_mem : ∀ k x, ξ k x ∈ Ξ
  measurable_a : ∀ k, Measurable (a k)
  sum_norm_rpow : ∀ x, ∑ k, ‖a k x‖ ^ (Real.conjExponent r) = 1

namespace Linearization

variable {r : ℝ} (L : Linearization r)

/-- The linearized operator
`𝒮'[f](x) = ∑_{k=1}^K (𝒮[f](ξ_k(x), x) - 𝒮[f](ξ_{k-1}(x), x)) a_k(x)` ([O+] L913-L916). -/
def op (f : 𝓢(ℝ, ℂ)) (x : ℝ) : ℂ :=
  ∑ k : Fin L.K, (partialFourierIntegral f (L.ξ k.succ x) x -
    partialFourierIntegral f (L.ξ k.castSucc x) x) * L.a k x

/-- `ξ_{k-1}(x) < ξ_k(x)`. -/
theorem ξ_castSucc_lt (k : Fin L.K) (x : ℝ) : L.ξ k.castSucc x < L.ξ k.succ x :=
  L.strictMono_ξ x (Fin.castSucc_lt_succ)

/-- Each `‖a_k(x)‖^{r'}` is at most `1` (a summand of the normalized sum `∑ ‖a_k(x)‖^{r'} = 1`). -/
theorem norm_rpow_le_one (k : Fin L.K) (x : ℝ) : ‖L.a k x‖ ^ (Real.conjExponent r) ≤ 1 := by
  rw [← L.sum_norm_rpow x]
  exact Finset.single_le_sum (f := fun j : Fin L.K => ‖L.a j x‖ ^ (Real.conjExponent r))
    (fun j _ => by positivity) (Finset.mem_univ k)

end Linearization

/-! ### The standing assumption on `Ξ`: no endpoints of dyadic intervals -/

/-- A set of frequencies contains no number `n 2^m`, `m, n ∈ ℤ`, "i.e. no endpoints of dyadic
intervals" ([O+] L897-L899, L1117-L1121): the standing assumption on the finite set `Ξ` of the
linearizing frequencies, used for the partition `𝒥_{ξ,ξ'} = ⋃_{ρ ∈ R} 𝒥_{ξ,ξ',ρ}` and for the
reflection `x ↦ -x`. -/
def AvoidsDyadicEndpoints (Ξ : Set ℝ) : Prop :=
  ∀ ξ ∈ Ξ, ∀ n m : ℤ, ξ ≠ (n : ℝ) * (2 : ℝ) ^ m

end PrimeCarleson.Proof.Oplus
