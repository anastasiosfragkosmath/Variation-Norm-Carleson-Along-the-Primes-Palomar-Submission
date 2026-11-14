/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Geometry/QuantitativeMetricPartition.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Topology.MetricSpace.Lipschitz
public import OAI.Combinatorics.Progressions.Dynamics.CandidateFrontSourceLossBudget
public import OAI.Combinatorics.Progressions.Estimates.NormalizedCutoffs
public import OAI.Combinatorics.Progressions.Sampling.NormalizedRealBoxHalfGrid
@[expose] public section

namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {ι X : Type*} [Fintype ι] [PseudoMetricSpace X]

noncomputable def boxCoverMeshCount (B : ℝ) (K : ℝ≥0) (ε : ℝ) : ℕ :=
  ⌈2 * B * K / ε⌉₊ + 1

theorem boxCoverMeshCount_pos (B : ℝ) (K : ℝ≥0) (ε : ℝ) : 0 < boxCoverMeshCount B K ε := by
  unfold boxCoverMeshCount
  omega

theorem boxCoverMeshCount_error {B ε : ℝ} (K : ℝ≥0) (hε : 0 < ε) :
    K * (2 * B / boxCoverMeshCount B K ε) ≤ ε := by
  have hN : (0 : ℝ) < boxCoverMeshCount B K ε := by exact_mod_cast boxCoverMeshCount_pos B K ε
  have hceil : 2 * B * K / ε ≤ (boxCoverMeshCount B K ε : ℝ) := by
    exact (Nat.le_ceil _).trans (by unfold boxCoverMeshCount; push_cast; linarith)
  have hm := (div_le_iff₀ hε).mp hceil
  rw [← mul_div_assoc, div_le_iff₀ hN]
  nlinarith

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {X : Type*} [PseudoMetricSpace X]

noncomputable def metricTent (c : X) (r : ℝ) (x : X) : ℝ := max 0 (2 * r - dist x c)

theorem metricTent_nonneg (c : X) (r : ℝ) (x : X) : 0 ≤ metricTent c r x := le_max_left _ _

theorem metricTent_le (c : X) {r : ℝ} (hr : 0 ≤ r) (x : X) : metricTent c r x ≤ 2 * r :=
  max_le (by linarith) (by linarith [dist_nonneg (x := x) (y := c)])

theorem metricTent_zero_of_far (c x : X) {r : ℝ} (hx : 2 * r ≤ dist x c) : metricTent c r x = 0 := by
  exact max_eq_left (by linarith)

theorem abs_metricTent_sub_le (c : X) (r : ℝ) (x y : X) :
    |metricTent c r x - metricTent c r y| ≤ dist x y := by
  calc
    _ = |max (2 * r - dist x c) 0 - max (2 * r - dist y c) 0| := by
      simp only [metricTent, max_comm]
    _ ≤ |(2 * r - dist x c) - (2 * r - dist y c)| := abs_max_sub_max_le_abs _ _ _
    _ = |dist x c - dist y c| := by
      rw [show (2 * r - dist x c) - (2 * r - dist y c) = -(dist x c - dist y c) by ring, abs_neg]
    _ ≤ dist x y := abs_dist_sub_le x y c

variable {ι : Type*} [Fintype ι]

noncomputable def metricTentSum (c : ι → X) (r : ℝ) (x : X) : ℝ := ∑ i, metricTent (c i) r x

theorem metricTentSum_ge (c : ι → X) {r : ℝ} (hcover : ∀ x, ∃ i, dist x (c i) ≤ r) (x : X) :
    r ≤ metricTentSum c r x := by
  obtain ⟨i, hi⟩ := hcover x
  calc
    r ≤ metricTent (c i) r x := (by linarith : r ≤ 2 * r - dist x (c i)).trans (le_max_right _ _)
    _ ≤ metricTentSum c r x := Finset.single_le_sum (fun j _ => metricTent_nonneg (c j) r x) (Finset.mem_univ i)

theorem abs_metricTentSum_sub_le (c : ι → X) (r : ℝ) (x y : X) :
    |metricTentSum c r x - metricTentSum c r y| ≤ Fintype.card ι * dist x y := by
  unfold metricTentSum
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |metricTent (c i) r x - metricTent (c i) r y| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, dist x y := Finset.sum_le_sum fun i _ => abs_metricTent_sub_le (c i) r x y
    _ = _ := by simp

noncomputable def metricTentPartition (c : ι → X) (r : ℝ) (i : ι) (x : X) : ℝ :=
  metricTent (c i) r x / metricTentSum c r x

theorem metricTentPartition_nonneg (c : ι → X) (r : ℝ) (i : ι) (x : X) :
    0 ≤ metricTentPartition c r i x :=
  div_nonneg (metricTent_nonneg _ _ _) (Finset.sum_nonneg fun j _ => metricTent_nonneg (c j) r x)

theorem sum_metricTentPartition (c : ι → X) {r : ℝ} (hr : 0 < r)
    (hcover : ∀ x, ∃ i, dist x (c i) ≤ r) (x : X) : ∑ i, metricTentPartition c r i x = 1 := by
  simp only [metricTentPartition, ← Finset.sum_div]
  exact div_self (hr.trans_le (metricTentSum_ge c hcover x)).ne'

theorem metricTentPartition_le_one (c : ι → X) {r : ℝ} (hr : 0 < r)
    (hcover : ∀ x, ∃ i, dist x (c i) ≤ r) (i : ι) (x : X) : metricTentPartition c r i x ≤ 1 := by
  rw [← sum_metricTentPartition c hr hcover x]
  exact Finset.single_le_sum (fun j _ => metricTentPartition_nonneg c r j x) (Finset.mem_univ i)

theorem metricTentPartition_zero_of_far (c : ι → X) (r : ℝ) (i : ι) (x : X)
    (hx : 2 * r ≤ dist x (c i)) : metricTentPartition c r i x = 0 := by
  simp only [metricTentPartition, metricTent_zero_of_far (c i) x hx, zero_div]

theorem abs_metricTentPartition_sub_le (c : ι → X) {r : ℝ} (hr : 0 < r)
    (hcover : ∀ x, ∃ i, dist x (c i) ≤ r) (i : ι) (x y : X) :
    |metricTentPartition c r i x - metricTentPartition c r i y| ≤
      ((2 * Fintype.card ι + 1) / r) * dist x y := by
  have h := abs_div_sub_div_bound hr (metricTentSum_ge c hcover x) (metricTentSum_ge c hcover y)
    dist_nonneg (by positivity : 0 ≤ 2 * r) (by positivity : 0 ≤ (Fintype.card ι : ℝ) * dist x y)
    (abs_metricTent_sub_le (c i) r x y)
    (by simpa only [abs_of_nonneg (metricTent_nonneg _ _ _)] using metricTent_le (c i) hr.le y)
    (abs_metricTentSum_sub_le c r x y)
  apply h.trans_eq
  field_simp
  ring

theorem lipschitz_metricTentPartition (c : ι → X) {r : ℝ≥0} (hr : 0 < r)
    (hcover : ∀ x, ∃ i, dist x (c i) ≤ r) (i : ι) :
    LipschitzWith ((2 * Fintype.card ι + 1) / r) (metricTentPartition c r i) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [Real.dist_eq, NNReal.coe_div, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_one,
    NNReal.coe_ofNat] using abs_metricTentPartition_sub_le c (show (0 : ℝ) < r from hr) hcover i x y

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem boxCoverMeshCount_add_one_le_exp {B ε p : ℝ} (K : ℝ≥0)
    (hB0 : 0 ≤ B) (hε : 0 < ε) (hp : 0 ≤ p)
    (hB : B ≤ Real.exp p) (hK : (K : ℝ) ≤ Real.exp p) (hεinv : 1 / ε ≤ Real.exp p) :
    ((boxCoverMeshCount B K ε + 1 : ℕ) : ℝ) ≤ Real.exp (3 * p + 4) := by
  have hprod : 2 * B * K / ε ≤ 2 * Real.exp (3 * p) := by
    calc
      _ = 2 * (B * K * (1 / ε)) := by ring
      _ ≤ 2 * (Real.exp p * Real.exp p * Real.exp p) := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 2; ring
  have hceil := (Nat.ceil_lt_add_one (by positivity : 0 ≤ 2 * B * K / ε)).le
  have hone : 1 ≤ Real.exp (3 * p) := Real.one_le_exp (by linarith)
  have hfive : (5 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  calc
    _ ≤ 5 * Real.exp (3 * p) := by
      unfold boxCoverMeshCount
      push_cast
      linarith
    _ ≤ Real.exp 4 * Real.exp (3 * p) := mul_le_mul_of_nonneg_right hfive (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem shifted_power_self_mono {p : ℝ} (hp : 0 ≤ p) {C D : ℕ} (hC : 1 ≤ C) (hCD : C ≤ D) :
    (p + C) ^ C ≤ (p + D) ^ D := by
  have hD : (1 : ℝ) ≤ D := by exact_mod_cast hC.trans hCD
  apply (pow_le_pow_left₀ (by positivity) (add_le_add le_rfl (Nat.cast_le.mpr hCD)) C).trans
  exact pow_le_pow_right₀ (by linarith) hCD

theorem metricPartition_constant_le_exp (n : ℕ) (r : ℝ≥0) {p : ℝ}
    (hp : 0 ≤ p) (hn : (n : ℝ) ≤ Real.exp p) (hr : 1 / (r : ℝ) ≤ Real.exp p) :
    (((2 * n + 1 : ℝ≥0) / r : ℝ≥0) : ℝ) ≤ Real.exp (2 * p + 2) := by
  have hnum : 2 * (n : ℝ) + 1 ≤ 3 * Real.exp p := by
    linarith [Real.one_le_exp_iff.mpr hp]
  have hthree : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  change (2 * (n : ℝ) + 1) / r ≤ _
  calc
    _ = (2 * (n : ℝ) + 1) * (1 / r) := by ring
    _ ≤ (3 * Real.exp p) * Real.exp p :=
      mul_le_mul hnum hr (by positivity) (by positivity)
    _ = 3 * Real.exp (2 * p) := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    _ ≤ Real.exp 2 * Real.exp (2 * p) := mul_le_mul_of_nonneg_right hthree (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

end OAI
