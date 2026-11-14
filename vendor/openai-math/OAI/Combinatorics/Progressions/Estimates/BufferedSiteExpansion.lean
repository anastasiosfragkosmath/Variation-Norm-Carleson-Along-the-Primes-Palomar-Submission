/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/BufferedSiteExpansion.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic
public import Mathlib.Topology.MetricSpace.Lipschitz
@[expose] public section

namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem lipschitz_mul_star_of_bounds {X : Type*} [PseudoMetricSpace X]
    (f g : X → ℂ) {Kf Kg Bf Bg : ℝ≥0}
    (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
    (hBf : ∀ x, ‖f x‖ ≤ Bf) (hBg : ∀ x, ‖g x‖ ≤ Bg) :
    LipschitzWith (Bf * Kg + Bg * Kf) (fun x => f x * star (g x)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm]
  have he : f x * star (g x) - f y * star (g y) =
      f x * star (g x - g y) + (f x - f y) * star (g y) := by
    rw [star_sub]
    ring
  rw [he]
  calc
    _ ≤ ‖f x * star (g x - g y)‖ + ‖(f x - f y) * star (g y)‖ := norm_add_le _ _
    _ = ‖f x‖ * ‖g x - g y‖ + ‖f x - f y‖ * ‖g y‖ := by rw [norm_mul, norm_mul, norm_star, norm_star]
    _ ≤ Bf * (Kg * dist x y) + (Kf * dist x y) * Bg := by
      apply add_le_add
      · exact mul_le_mul (hBf x) (by simpa only [dist_eq_norm] using hg.dist_le_mul x y)
          (norm_nonneg _) Bf.coe_nonneg
      · exact mul_le_mul (by simpa only [dist_eq_norm] using hf.dist_le_mul x y) (hBg y)
          (norm_nonneg _) (mul_nonneg Kf.coe_nonneg dist_nonneg)
    _ = _ := by push_cast; ring

end Erdos3

end

section

open scoped NNReal BigOperators

namespace Erdos3

theorem lipschitz_mul_of_bounds {X : Type*} [PseudoMetricSpace X]
    (f g : X → ℂ) {Kf Kg Bf Bg : ℝ≥0}
    (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
    (hBf : ∀ x, ‖f x‖ ≤ Bf) (hBg : ∀ x, ‖g x‖ ≤ Bg) :
    LipschitzWith (Bf * Kg + Bg * Kf) (fun x => f x * g x) := by
  have hstar : LipschitzWith Kg (fun x => star (g x)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_eq_norm, ← star_sub, norm_star] using hg.dist_le_mul x y
  simpa only [star_star] using lipschitz_mul_star_of_bounds f (fun x => star (g x)) hf hstar
    hBf (fun x => by simpa only [norm_star] using hBg x)

theorem bounded_lipschitz_finset_prod {ι X : Type*} [PseudoMetricSpace X]
    (s : Finset ι) (f : ι → X → ℂ) {B K : ℝ≥0} (hB : 1 ≤ B)
    (hf : ∀ i ∈ s, LipschitzWith K (f i)) (hn : ∀ i ∈ s, ∀ x, ‖f i x‖ ≤ B) :
    (∀ x, ‖∏ i ∈ s, f i x‖ ≤ (B : ℝ) ^ s.card) ∧
      LipschitzWith (s.card * K * B ^ s.card) (fun x => ∏ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    constructor
    · intro x
      simp
    · simpa only [Finset.prod_empty, Finset.card_empty, Nat.cast_zero, zero_mul] using
        (LipschitzWith.const (α := X) (1 : ℂ))
  | @insert a s ha ih =>
    obtain ⟨hns, hls⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      (fun i hi => hn i (Finset.mem_insert_of_mem hi))
    simp only [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    constructor
    · intro x
      rw [norm_mul, pow_succ']
      exact mul_le_mul (hn a (Finset.mem_insert_self _ _) x) (hns x) (norm_nonneg _) B.coe_nonneg
    · have hm := lipschitz_mul_of_bounds (f a) (fun x => ∏ i ∈ s, f i x)
        (hf a (Finset.mem_insert_self _ _)) hls (hn a (Finset.mem_insert_self _ _))
        (Bg := B ^ s.card) (fun x => by simpa only [NNReal.coe_pow] using hns x)
      apply hm.weaken
      simp only [Nat.cast_add, Nat.cast_one, pow_succ]
      have hh := mul_le_mul_of_nonneg_left hB (show 0 ≤ K * B ^ s.card from zero_le)
      nlinarith

theorem bounded_lipschitz_fintype_prod {ι X : Type*} [Fintype ι] [PseudoMetricSpace X]
    (f : ι → X → ℂ) {B K : ℝ≥0} (hB : 1 ≤ B)
    (hf : ∀ i, LipschitzWith K (f i)) (hn : ∀ i x, ‖f i x‖ ≤ B) :
    (∀ x, ‖∏ i, f i x‖ ≤ (B : ℝ) ^ Fintype.card ι) ∧
      LipschitzWith (Fintype.card ι * K * B ^ Fintype.card ι) (fun x => ∏ i, f i x) := by
  simpa only [Finset.card_univ] using
    bounded_lipschitz_finset_prod Finset.univ f hB (fun i _ => hf i) (fun i _ => hn i)

end Erdos3

end

section

namespace Erdos3
open scoped NNReal

end Erdos3

end

section

namespace Erdos3
open scoped Classical BigOperators NNReal

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

variable {S T U D : Type*} [Fintype S] [Fintype T]

end Erdos3

end

end OAI
