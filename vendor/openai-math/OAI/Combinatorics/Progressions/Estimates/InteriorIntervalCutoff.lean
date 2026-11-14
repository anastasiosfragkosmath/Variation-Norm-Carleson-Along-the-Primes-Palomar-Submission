/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/InteriorIntervalCutoff.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.CyclicCutNeighborhood
public import OAI.Combinatorics.Progressions.Estimates.LinearCutoff
public import OAI.Combinatorics.Progressions.Fourier.RectangularGridCharacter
@[expose] public section

namespace OAI

section

namespace Erdos3

theorem abs_sub_le_of_circle_dist_on_interior {x y η δ : ℝ}
    (hx : η ≤ x ∧ x ≤ 1 - η) (hy : η ≤ y ∧ y ≤ 1 - η)
    (hδ : δ < 2 * η) (hdist : dist (x : CircleFourier.Circle) (y : CircleFourier.Circle) ≤ δ) :
    |x - y| ≤ δ := by
  rw [dist_eq_norm, ← QuotientAddGroup.mk_sub, UnitAddCircle.norm_eq] at hdist
  have hxy : |x - y| ≤ 1 - 2 * η := abs_le.mpr ⟨by linarith, by linarith⟩
  have hz : |(round (x - y) : ℝ)| ≤ |x - y - (round (x - y) : ℝ)| + |x - y| := by
    calc
      _ = |((round (x - y) : ℝ) - (x - y)) + (x - y)| := by ring_nf
      _ ≤ |(round (x - y) : ℝ) - (x - y)| + |x - y| := abs_add_le _ _
      _ = _ := by rw [abs_sub_comm (round (x - y) : ℝ) (x - y)]
  have hzlt : |(round (x - y) : ℝ)| < 1 := by linarith
  have hzlo : (-1 : ℤ) < round (x - y) := by exact_mod_cast (abs_lt.mp hzlt).1
  have hzhi : round (x - y) < (1 : ℤ) := by exact_mod_cast (abs_lt.mp hzlt).2
  have hz0 : round (x - y) = 0 := by omega
  simpa only [hz0, Int.cast_zero, sub_zero] using hdist

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

def frozenRealSection {Z Ξ : Type*} (F : Z → Ξ → ℝ) (a : Option Ξ) (z : Z) : ℝ :=
  a.elim 0 (F z)

theorem frozenRealSection_unit_interval {Z Ξ : Type*} (F : Z → Ξ → ℝ)
    (hF : ∀ z a, 0 ≤ F z a ∧ F z a ≤ 1) (a : Option Ξ) (z : Z) :
    0 ≤ frozenRealSection F a z ∧ frozenRealSection F a z ≤ 1 := by
  cases a with
  | none => simp [frozenRealSection]
  | some a => exact hF z a

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem expect_abs_le_of_exceptional_set {X : Type*} [Fintype X] [Nonempty X]
    (E : Finset X) (f : X → ℝ) {M ε : ℝ} (hε : 0 ≤ ε)
    (hcap : ∀ x, |f x| ≤ M) (hgood : ∀ x, x ∉ E → |f x| ≤ ε) :
    (𝔼 x, |f x|) ≤ ε + M * (E.card : ℝ) / Fintype.card X := by
  classical
  have hbound (x : X) : |f x| ≤ ε + if x ∈ E then M else 0 := by
    by_cases hx : x ∈ E
    · simp only [hx, ↓reduceIte]
      exact (hcap x).trans (le_add_of_nonneg_left hε)
    · simpa only [hx, ↓reduceIte, add_zero] using hgood x hx
  calc
    _ ≤ (𝔼 x : X, (ε + if x ∈ E then M else 0)) := Finset.expect_le_expect (fun x _ => hbound x)
    _ = ε + M * (E.card : ℝ) / Fintype.card X := by
      rw [Finset.expect_add_distrib, Fintype.expect_const]
      congr 1
      simp [Fintype.expect_eq_sum_div_card, Finset.sum_ite_mem, mul_comm]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3

noncomputable def cyclicWrapExceptional {N : ℕ} [NeZero N] (h : ZMod N) (ρ : ℝ) : Finset (ZMod N) :=
  cyclicCutNeighborhood N 0 (N * ρ) ∪ cyclicCutNeighborhood N N (N * ρ) ∪
    cyclicCutNeighborhood N ((N - h.val : ℕ) : ℤ) (N * ρ)

theorem cyclicWrapExceptional_card_le {N : ℕ} [NeZero N] (h : ZMod N)
    {ρ : ℝ} (hρ : 0 ≤ ρ) : ((cyclicWrapExceptional h ρ).card : ℝ) ≤ 6 * N * ρ + 3 := by
  have hδ : 0 ≤ (N : ℝ) * ρ := mul_nonneg (Nat.cast_nonneg _) hρ
  have h0 := cyclicCutNeighborhood_card_le N 0 hδ
  have hN := cyclicCutNeighborhood_card_le N N hδ
  have hw := cyclicCutNeighborhood_card_le N ((N - h.val : ℕ) : ℤ) hδ
  have hu := Finset.card_union_le (cyclicCutNeighborhood N 0 (N * ρ))
    (cyclicCutNeighborhood N N (N * ρ))
  have hv := Finset.card_union_le
    (cyclicCutNeighborhood N 0 (N * ρ) ∪ cyclicCutNeighborhood N N (N * ρ))
    (cyclicCutNeighborhood N ((N - h.val : ℕ) : ℤ) (N * ρ))
  have hu' : ((cyclicCutNeighborhood N 0 (N * ρ) ∪ cyclicCutNeighborhood N N (N * ρ)).card : ℝ) ≤
      (cyclicCutNeighborhood N 0 (N * ρ)).card + (cyclicCutNeighborhood N N (N * ρ)).card := by
    exact_mod_cast hu
  have hv' : ((cyclicWrapExceptional h ρ).card : ℝ) ≤
      (cyclicCutNeighborhood N 0 (N * ρ) ∪ cyclicCutNeighborhood N N (N * ρ)).card +
        (cyclicCutNeighborhood N ((N - h.val : ℕ) : ℤ) (N * ρ)).card := by
    exact_mod_cast hv
  linarith

theorem cyclicWrapExceptional_density_le {N : ℕ} [NeZero N] (h : ZMod N)
    {ρ : ℝ} (hρ : 0 ≤ ρ) : ((cyclicWrapExceptional h ρ).card : ℝ) / N ≤ 6 * ρ + 3 / N := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  calc
    _ ≤ (6 * (N : ℝ) * ρ + 3) / N :=
      div_le_div_of_nonneg_right (cyclicWrapExceptional_card_le h hρ) (Nat.cast_nonneg _)
    _ = _ := by field_simp

theorem outside_cyclicWrapExceptional {N : ℕ} [NeZero N] (h x : ZMod N) {ρ : ℝ}
    (hx : x ∉ cyclicWrapExceptional h ρ) :
    ρ < (x.val : ℝ) / N ∧ (x.val : ℝ) / N < 1 - ρ ∧
      (N : ℝ) * ρ < |(x.val : ℝ) - ((N - h.val : ℕ) : ℝ)| := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hxN : (x.val : ℝ) < N := Nat.cast_lt.mpr x.val_lt
  simp only [cyclicWrapExceptional, Finset.mem_union, not_or, mem_cyclicCutNeighborhood] at hx
  have h0 : (N : ℝ) * ρ < (x.val : ℝ) := by
    simpa only [Int.cast_zero, sub_zero,
      abs_of_nonneg (show (0 : ℝ) ≤ x.val from Nat.cast_nonneg _)] using lt_of_not_ge hx.1.1
  have h1 : (N : ℝ) * ρ < (N : ℝ) - x.val := by
    simpa only [Int.cast_natCast, abs_of_neg (sub_neg.mpr hxN), neg_sub] using lt_of_not_ge hx.1.2
  refine ⟨(lt_div_iff₀ hN).mpr (by nlinarith), (div_lt_iff₀ hN).mpr (by nlinarith), ?_⟩
  simpa only [Int.cast_natCast] using lt_of_not_ge hx.2

end Erdos3

end

section

namespace Erdos3

theorem good_circle_observations_control_representatives {N : ℕ} [NeZero N]
    (h x y : ZMod N) {ρ : ℝ} (hρ : 0 < ρ)
    (hx : x ∉ cyclicWrapExceptional h ρ) (hy : y ∉ cyclicWrapExceptional h ρ)
    (hdist : dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ρ) :
    |(x.val : ℝ) / N - (y.val : ℝ) / N| ≤ ρ := by
  have hx' := outside_cyclicWrapExceptional h x hx
  have hy' := outside_cyclicWrapExceptional h y hy
  apply abs_sub_le_of_circle_dist_on_interior ⟨hx'.1.le, hx'.2.1.le⟩ ⟨hy'.1.le, hy'.2.1.le⟩
    (by linarith)
  simpa only [ZMod.toAddCircle_apply] using hdist

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

end OAI
