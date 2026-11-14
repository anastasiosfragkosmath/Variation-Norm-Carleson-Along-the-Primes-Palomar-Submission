module

public import PrimeCarleson.Proof.Paper.P7.Basic
public import Mathlib.Analysis.BoundedVariation
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Step-function approximation of a multiplier of bounded variation

Proof of `l:varcar` for a multiplier `m(ξ - λ) = h(ξ - λ)` whose distribution function `h` is a
function of bounded variation (`VarcarBV.lean`). This file holds the two elementary ingredients:

* `mulInt_halfLineSum`: for a finite combination `∑ᵢ cᵢ 1_{[xᵢ, ∞)}` of half-line indicators, the
  multiplier output `λ ↦ ∫ h_step(ξ - λ) g(ξ) dξ` is `∑ᵢ cᵢ (∫g - Φ_g(xᵢ + λ))` with
  `Φ_g(y) = ∫_{ξ ≤ y} g` (Source: main paper `l:varcar`, L1792–L1795, finitely supported `dm`);
* `gridStep_eq`: the grid approximation `h_δ(s) = h(u + ⌊(s - u)/δ⌋ δ)` of a function `h`
  vanishing off `[u, w]` is the finite combination `∑_{k ≤ K} (h(x_k) - h(x_{k-1})) 1_{[x_k, ∞)}`
  with `x_k = u + kδ`, whose coefficients have total mass at most the variation of `h`.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Common PrimeCarleson.Proof.MswTransference

/-- The partial integral `Φ_g(λ) = ∫_{ξ ≤ λ} g(ξ) dξ`. For `g(ξ) = f̂(ξ) e(xξ)` this is
`(f̂(ξ) 1_{(-∞, 0]}(ξ - λ))^∨(x)`, the half-line projection of `[O+]`. -/
def partialInt (g : ℝ → ℂ) (lam : ℝ) : ℂ := ∫ ξ in Set.Iic lam, g ξ

/-- The output of the multiplier `ξ ↦ h(ξ - λ)` on the density `g`:
`λ ↦ ∫ h(ξ - λ) g(ξ) dξ`. For `g(ξ) = f̂(ξ) e(xξ)` this is `(f̂(ξ) h(ξ - λ))^∨(x)`. -/
def mulInt (h g : ℝ → ℂ) (lam : ℝ) : ℂ := ∫ ξ, h (ξ - lam) * g ξ

/-- `Φ_g` is continuous for integrable `g`. -/
theorem continuous_partialInt {g : ℝ → ℂ} (hg : Integrable g) : Continuous (partialInt g) := by
  have h0 : Continuous fun b : ℝ => ∫ x in (0 : ℝ)..b, g x :=
    intervalIntegral.continuous_primitive (fun _ _ => hg.intervalIntegrable) 0
  have h1 : partialInt g = fun b => partialInt g 0 + ∫ x in (0 : ℝ)..b, g x := by
    funext b
    have := intervalIntegral.integral_Iic_sub_Iic hg.integrableOn hg.integrableOn (a := 0) (b := b)
    unfold partialInt
    rw [← this]
    ring
  rw [h1]
  exact continuous_const.add h0

/-- `∫_{ξ ≥ y} g = ∫ g - Φ_g(y)`. -/
theorem integral_Ici_eq_sub {g : ℝ → ℂ} (hg : Integrable g) (y : ℝ) :
    ∫ ξ in Set.Ici y, g ξ = (∫ ξ, g ξ) - partialInt g y := by
  rw [integral_Ici_eq_integral_Ioi]
  have := integral_add_compl (measurableSet_Iic (a := y)) hg
  rw [Set.compl_Iic] at this
  unfold partialInt
  rw [← this]
  ring

/-- A finite combination `∑ᵢ cᵢ 1_{[xᵢ, ∞)}` of half-line indicators (the distribution function of
`∑ᵢ cᵢ δ_{xᵢ}`). -/
def halfLineSum {ι : Type*} (s : Finset ι) (c : ι → ℂ) (x : ι → ℝ) (t : ℝ) : ℂ :=
  ∑ i ∈ s, c i * (Set.Ici (x i)).indicator (fun _ => (1 : ℂ)) t

/-- **Finite case of the fundamental-theorem-of-calculus representation of `l:varcar`** (Source:
main paper `l:varcar`, L1792–L1795): for the multiplier `∑ᵢ cᵢ 1_{[xᵢ, ∞)}(ξ - λ)` (distribution
function of `dm = ∑ᵢ cᵢ δ_{xᵢ}`) and an integrable density `g`,
`∫ h(ξ - λ) g(ξ) dξ = ∑ᵢ cᵢ (∫ g - Φ_g(xᵢ + λ))`; i.e. the differences over `λ` are the integrals
`∑ᵢ cᵢ ∫_{(xᵢ + λ, xᵢ + λ']} g` of interval projections. -/
theorem mulInt_halfLineSum {ι : Type*} (s : Finset ι) (c : ι → ℂ) (x : ι → ℝ) {g : ℝ → ℂ}
    (hg : Integrable g) (lam : ℝ) :
    mulInt (halfLineSum s c x) g lam =
      ∑ i ∈ s, c i * ((∫ ξ, g ξ) - partialInt g (x i + lam)) := by
  unfold mulInt halfLineSum
  have h1 : ∀ ξ : ℝ, (∑ i ∈ s, c i * (Set.Ici (x i)).indicator (fun _ => (1 : ℂ)) (ξ - lam)) *
      g ξ = ∑ i ∈ s, c i * (Set.Ici (x i + lam)).indicator g ξ := by
    intro ξ
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hξ : x i + lam ≤ ξ
    · have h2 : x i ≤ ξ - lam := by linarith
      simp [Set.indicator, Set.mem_Ici, hξ, h2]
    · have h2 : ¬ x i ≤ ξ - lam := by intro h; apply hξ; linarith
      simp [Set.indicator, Set.mem_Ici, hξ, h2]
  simp_rw [h1]
  rw [integral_finsetSum _ fun i _ => (hg.indicator measurableSet_Ici).const_mul (c i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, integral_indicator measurableSet_Ici, integral_Ici_eq_sub hg]

/-! ### The grid step function -/

/-- The grid step function `∑_{k ≤ K} (h(x_k) - h(x_{k-1})) 1_{[x_k, ∞)}`, `x_k = u + kδ`. -/
def gridStep (h : ℝ → ℂ) (u δ : ℝ) (K : ℕ) : ℝ → ℂ :=
  halfLineSum (Finset.range (K + 1)) (fun k : ℕ => h (u + k * δ) - h (u + ((k : ℝ) - 1) * δ))
    (fun k : ℕ => u + k * δ)

/-- The grid step function is the grid approximation `h(u + ⌊(s - u)/δ⌋ δ)`, for `h` vanishing
off `[u, w]` and `w < u + Kδ`. -/
theorem gridStep_eq {h : ℝ → ℂ} {u w δ : ℝ} (hδ : 0 < δ)
    (hsupp : ∀ s, s ∉ Set.Icc u w → h s = 0) {K : ℕ} (hK : w < u + K * δ) (s : ℝ) :
    gridStep h u δ K s = h (u + ⌊(s - u) / δ⌋ * δ) := by
  unfold gridStep halfLineSum
  set m : ℤ := ⌊(s - u) / δ⌋ with hm
  have hiff : ∀ k : ℕ, u + (k : ℝ) * δ ≤ s ↔ (k : ℤ) ≤ m := by
    intro k
    rw [hm, Int.le_floor, le_div_iff₀ hδ]
    push_cast
    constructor <;> intro h <;> linarith
  have hind : ∀ k : ℕ, (Set.Ici (u + (k : ℝ) * δ)).indicator (fun _ => (1 : ℂ)) s =
      if (k : ℤ) ≤ m then 1 else 0 := by
    intro k
    simp only [Set.indicator, Set.mem_Ici, hiff]
  simp_rw [hind]
  by_cases hm0 : m < 0
  · have hnone : ∀ k : ℕ, ¬ (k : ℤ) ≤ m := fun k => by
      have : (0 : ℤ) ≤ k := Int.natCast_nonneg k
      lia
    simp only [hnone, ite_false, mul_zero, Finset.sum_const_zero]
    symm
    apply hsupp
    intro hmem
    have h1 : (m : ℝ) ≤ -1 := by exact_mod_cast (by lia : m ≤ -1)
    have h2 := hmem.1
    nlinarith
  · push Not at hm0
    obtain ⟨m', hm'⟩ : ∃ m' : ℕ, m = m' := ⟨m.toNat, (Int.toNat_of_nonneg hm0).symm⟩
    have hcast : ∀ k : ℕ, ((k : ℤ) ≤ m) ↔ k ≤ m' := by
      intro k
      rw [hm']
      exact Nat.cast_le
    simp_rw [hcast]
    have hfilt : ∑ k ∈ Finset.range (K + 1), (h (u + k * δ) - h (u + ((k : ℝ) - 1) * δ)) *
        (if k ≤ m' then (1 : ℂ) else 0) =
        ∑ k ∈ Finset.range (min K m' + 1), (h (u + k * δ) - h (u + ((k : ℝ) - 1) * δ)) := by
      simp_rw [mul_ite, mul_one, mul_zero]
      rw [← Finset.sum_filter]
      congr 1
      ext k
      simp only [Finset.mem_filter, Finset.mem_range]
      lia
    rw [hfilt]
    have htel := Finset.sum_range_sub (fun k : ℕ => h (u + ((k : ℝ) - 1) * δ)) (min K m' + 1)
    have hrw : ∑ k ∈ Finset.range (min K m' + 1), (h (u + k * δ) - h (u + ((k : ℝ) - 1) * δ)) =
        h (u + (((min K m' + 1 : ℕ) : ℝ) - 1) * δ) - h (u + (((0 : ℕ) : ℝ) - 1) * δ) := by
      rw [← htel]
      refine Finset.sum_congr rfl fun k _ => ?_
      congr 2
      push_cast
      ring_nf
    rw [hrw]
    have hzero : h (u + (((0 : ℕ) : ℝ) - 1) * δ) = 0 := by
      apply hsupp
      intro hmem
      have := hmem.1
      simp at this
      linarith
    rw [hzero, sub_zero, hm']
    rcases le_total m' K with hle | hle
    · rw [min_eq_right hle]
      congr 2
      push_cast
      ring
    · rw [min_eq_left hle]
      have h1 : h (u + (((K + 1 : ℕ) : ℝ) - 1) * δ) = 0 := by
        apply hsupp
        intro hmem
        have := hmem.2
        push_cast at this
        linarith
      have h2 : h (u + (m' : ℤ) * δ) = 0 := by
        apply hsupp
        intro hmem
        have := hmem.2
        have h3 : (K : ℝ) ≤ m' := by exact_mod_cast hle
        have h4 : (K : ℝ) * δ ≤ (m' : ℝ) * δ := mul_le_mul_of_nonneg_right h3 hδ.le
        push_cast at this
        linarith
      rw [h1, h2]

end PrimeCarleson.Proof.Paper
