/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Dynamics/SpectralLogBudget.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Sampling.LocalSamplingBudget
@[expose] public section

namespace OAI

section

namespace Erdos3.CyclicCrootSisask

noncomputable def spectralIterations (epsilon p : ℝ) : ℕ :=
  ⌈(p + Real.log (16 / epsilon)) / Real.log 2⌉₊ + 1

noncomputable def spectralIterationFactor (epsilon : ℝ) : ℝ :=
  (1 + Real.log (16 / epsilon)) / Real.log 2 + 2

theorem spectralIterations_pos (epsilon p : ℝ) : 0 < spectralIterations epsilon p := by
  unfold spectralIterations
  omega

theorem spectralIterations_le {epsilon p : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon1 : epsilon ≤ 1) (hp : 0 ≤ p) :
    (spectralIterations epsilon p : ℝ) ≤ spectralIterationFactor epsilon * (p + 1) := by
  have hlog : 0 ≤ Real.log (16 / epsilon) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hepsilon]
    linarith
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ (p + Real.log (16 / epsilon)) / Real.log 2 by positivity)
  have hfirst : (spectralIterations epsilon p : ℝ) ≤
      (p + Real.log (16 / epsilon)) / Real.log 2 + 2 := by
    unfold spectralIterations
    push_cast
    linarith
  apply hfirst.trans
  unfold spectralIterationFactor
  apply (le_of_sub_nonneg ?_)
  have hid : ((1 + Real.log (16 / epsilon)) / Real.log 2 + 2) * (p + 1) -
      ((p + Real.log (16 / epsilon)) / Real.log 2 + 2) =
      (1 + p * Real.log (16 / epsilon)) / Real.log 2 + 2 * p := by ring
  rw [hid]
  positivity

theorem half_pow_spectralIterations_mul_exp_le {epsilon p : ℝ} (hepsilon : 0 < epsilon) :
    (1 / 2 : ℝ) ^ spectralIterations epsilon p * Real.exp p ≤ epsilon / 16 := by
  let q := spectralIterations epsilon p
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hq : (p + Real.log (16 / epsilon)) / Real.log 2 ≤ (q : ℝ) := by
    apply (Nat.le_ceil _).trans
    dsimp [q, spectralIterations]
    exact_mod_cast Nat.le_succ _
  have hmul := (div_le_iff₀ htwo).mp hq
  have hpow : (1 / 2 : ℝ) ^ q = Real.exp (-((q : ℝ) * Real.log 2)) := by
    rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    simp [one_div, inv_pow]
  calc
    (1 / 2 : ℝ) ^ q * Real.exp p = Real.exp (-((q : ℝ) * Real.log 2) + p) := by
      rw [hpow, ← Real.exp_add]
    _ ≤ Real.exp (-Real.log (16 / epsilon)) := Real.exp_le_exp.mpr (by linarith)
    _ = epsilon / 16 := by
      rw [Real.exp_neg, Real.exp_log (by positivity : 0 < 16 / epsilon)]
      field_simp

end Erdos3.CyclicCrootSisask

end

section

namespace Erdos3

end Erdos3

end

end OAI
