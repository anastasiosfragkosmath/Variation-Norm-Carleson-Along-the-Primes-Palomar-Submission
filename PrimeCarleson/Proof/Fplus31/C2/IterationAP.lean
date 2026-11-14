module

public import PrimeCarleson.Proof.Fplus31.C2.TypeI

/-!
# The iteration, arithmetic progressions

Part of the type I / type II iteration of `C2/CMain.lean` (proof of [F+] Proposition 3.1). The
iteration keeps `f` in the original variable and restricts to the progression
`P = {n ∈ [lo, hi] : n ≡ r (q)}` (Leng23 L1252-L1262). This file is the bookkeeping of these
progressions: the finset `apInt` of integers and `apPts` of one-variable points (the `Q` of a
`LengStart`), the indicator `progIndicator` of `TypeI.lean` as a sum over the progression, and the
decomposition of a progression into blocks of equal length and residue classes modulo the block's
own modulus, which is the cell structure of the pigeonhole of `IterationPigeon.lean`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

open Finset
open scoped BigOperators

/-- The progression `{n ∈ [lo, hi] : n ≡ r (mod q)}` of integers. -/
def apInt (q : ℕ) (r lo hi : ℤ) : Finset ℤ :=
  (Finset.Icc lo hi).filter fun n => n ≡ r [ZMOD q]

/-- Membership in `apInt`. -/
theorem mem_apInt {q : ℕ} {r lo hi n : ℤ} :
    n ∈ apInt q r lo hi ↔ lo ≤ n ∧ n ≤ hi ∧ n ≡ r [ZMOD q] := by
  simp only [apInt, Finset.mem_filter, Finset.mem_Icc]
  tauto

/-- The progression as a finset of one-variable integer points. -/
def apPts (q : ℕ) (r lo hi : ℤ) : Finset (Unit → ℤ) :=
  (apInt q r lo hi).image fun n _ => n

/-- The map `n ↦ (fun _ => n)` is injective. -/
theorem injective_const_unit : Function.Injective (fun (n : ℤ) (_ : Unit) => n) :=
  fun _ _ h => congrFun h ()

/-- The cardinality of `apPts` is that of `apInt`. -/
theorem card_apPts (q : ℕ) (r lo hi : ℤ) : (apPts q r lo hi).card = (apInt q r lo hi).card := by
  rw [apPts, Finset.card_image_of_injective _ injective_const_unit]

/-- An average over the points of `apPts` is the average over the progression. -/
theorem expect_apPts (q : ℕ) (r lo hi : ℤ) (G : (Unit → ℤ) → ℂ) :
    (𝔼 x ∈ apPts q r lo hi, G x) = 𝔼 n ∈ apInt q r lo hi, G (fun _ => n) := by
  rw [apPts, Finset.expect_image (fun a _ b _ h => injective_const_unit h)]

/-- The norm of an average over the progression is the norm of the sum divided by the size. -/
theorem norm_expect_apPts (q : ℕ) (r lo hi : ℤ) (G : (Unit → ℤ) → ℂ) :
    ‖𝔼 x ∈ apPts q r lo hi, G x‖ =
      ‖∑ n ∈ apInt q r lo hi, G (fun _ => n)‖ / ((apInt q r lo hi).card : ℝ) := by
  rw [expect_apPts, Finset.expect_eq_sum_div_card, norm_div, Complex.norm_natCast]

/-- The progression lies in `[lo, hi]`. -/
theorem apInt_subset_Icc (q : ℕ) (r lo hi : ℤ) : apInt q r lo hi ⊆ Finset.Icc lo hi :=
  Finset.filter_subset _ _

/-- The progression has at most `N` elements when `[lo, hi] ⊆ [1, N]`. -/
theorem card_apInt_le {q : ℕ} {r lo hi : ℤ} {N : ℕ} (hlo : 1 ≤ lo) (hhi : hi ≤ N) :
    (apInt q r lo hi).card ≤ N := by
  calc (apInt q r lo hi).card ≤ (Finset.Icc lo hi).card :=
        Finset.card_le_card (apInt_subset_Icc _ _ _ _)
    _ ≤ (Finset.Icc (1 : ℤ) N).card := Finset.card_le_card (Finset.Icc_subset_Icc hlo hhi)
    _ = N := by simp

/-- The indicator of the progression is `1` on it and `0` off it. -/
theorem progIndicator_eq_ite (q : ℕ) (r lo hi n : ℤ) :
    progIndicator q r lo hi n = if n ∈ apInt q r lo hi then 1 else 0 := by
  unfold progIndicator
  by_cases h : lo ≤ n ∧ n ≤ hi ∧ n ≡ r [ZMOD q]
  · rw [ite_eq_left h, ite_eq_left (mem_apInt.mpr h)]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (mem_apInt.mp h'))]

/-- **The weighted sum against `1_P · e` over `[1, N]`** is the sum over the progression
`P = apInt q r lo hi ⊆ [1, N]`. -/
theorem sum_Icc_progIndicator_mul (q : ℕ) (r lo hi : ℤ) {N : ℕ} (hlo : 1 ≤ lo) (hhi : hi ≤ N)
    (g e : ℤ → ℂ) :
    ∑ n ∈ Finset.Icc (1 : ℤ) N, g n * (progIndicator q r lo hi n * e n) =
      ∑ n ∈ apInt q r lo hi, g n * e n := by
  have hsub : apInt q r lo hi ⊆ Finset.Icc (1 : ℤ) N := fun n hn => by
    obtain ⟨h1, h2, -⟩ := mem_apInt.mp hn
    exact Finset.mem_Icc.mpr ⟨hlo.trans h1, h2.trans (by exact_mod_cast hhi)⟩
  rw [← Finset.sum_subset hsub (fun n _ hn => ?_)]
  · refine Finset.sum_congr rfl fun n hn => ?_
    rw [progIndicator_eq_ite, ite_eq_left hn, one_mul]
  · rw [progIndicator_eq_ite, ite_eq_right hn]
    simp

end PrimeCarleson.Proof.Fplus31
