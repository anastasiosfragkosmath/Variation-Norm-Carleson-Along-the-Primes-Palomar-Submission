/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Geometry/NativeCorrelationCoordinates.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.NativeCrossFactorization
@[expose] public section

namespace OAI

section

namespace Erdos3.NativeVectorCorrelation

open scoped TensorProduct BigOperators

attribute [local instance] lie algebra topology topologicalAdd continuousSMul hausdorff

noncomputable def mapCoordinates {I J : Type*} {degree N : ℕ} [NeZero N] {p : ℝ}
    {f : I → ZMod N → ℂ} (W : NativeVectorCorrelation degree N p f)
    (g : J → ZMod N → ℂ) (e : I → J) (he : ∀ i x, g (e i) x = f i x) :
    NativeVectorCorrelation degree N p g :=
  { W with coordinate := e W.coordinate
           correlation := by simpa only [he] using W.correlation }

noncomputable def scaleSignal {I : Type*} {degree N : ℕ} [NeZero N] {p q : ℝ}
    {f : I → ZMod N → ℂ} (W : NativeVectorCorrelation degree N p f)
    (c : ℂ) (hq : 0 ≤ q) (hc : Real.exp (-q) ≤ ‖c‖) :
    NativeVectorCorrelation degree N (p + q) (fun i x => c * f i x) :=
  { W with
    complexity := W.complexity.mono (le_add_of_nonneg_right hq)
    correlation := by
      have he : (𝔼 x, (c * f W.coordinate x) * star (W.test.evalCyclic N (fun _ => x))) =
          c * (𝔼 x, f W.coordinate x * star (W.test.evalCyclic N (fun _ => x))) := by
        simp only [mul_assoc, Finset.mul_expect]
      rw [he, norm_mul, show -(p + q) = -q + -p by ring, Real.exp_add]
      exact mul_le_mul hc W.correlation (Real.exp_nonneg _) (norm_nonneg _) }

theorem exists_half_signal {I : Type*} {degree N : ℕ} [NeZero N] {p : ℝ}
    {f : I → ZMod N → ℂ} (W : NativeVectorCorrelation degree N p f) :
    Nonempty (NativeVectorCorrelation degree N (p + 1) (fun i x => f i x / 2)) := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hc : Real.exp (-1) ≤ ‖(1 / 2 : ℂ)‖ := by
    norm_num only [norm_div, norm_one, Complex.norm_ofNat]
    rw [Real.exp_neg, one_div]
    exact (inv_le_inv₀ (Real.exp_pos 1) (by norm_num : (0 : ℝ) < 2)).mpr htwo
  have h := W.scaleSignal (1 / 2) (by norm_num : (0 : ℝ) ≤ 1) hc
  refine ⟨h.mapCoordinates _ id ?_⟩
  intro i x
  simp only [id_eq, div_eq_mul_inv, one_mul, mul_comm]

end Erdos3.NativeVectorCorrelation

end

end OAI
