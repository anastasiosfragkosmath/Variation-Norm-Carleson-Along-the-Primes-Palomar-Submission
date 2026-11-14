/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Fourier/TorusCircleActions.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.PeriodicIsometricAction
@[expose] public section

namespace OAI

section

namespace Erdos3.CircleFourier.IsometricCircleAction

open MeasureTheory
open scoped BigOperators

variable {X : Type*} [PseudoMetricSpace X]

def Commutes (A B : IsometricCircleAction X) : Prop :=
  ∀ t u x, A.act t (B.act u x) = B.act u (A.act t x)

theorem component_equivariant (A : IsometricCircleAction X) (N : ℕ) (h : ℤ)
    {f : X → ℂ} (g : X → X) (z : ℂ)
    (hg : ∀ t x, A.act t (g x) = g (A.act t x))
    (hf : ∀ x, f (g x) = z * f x) (x : X) :
    A.component N h f (g x) = z * A.component N h f x := by
  unfold component fejerComponent circleFourierComponent
  change (fejerCoefficient N h : ℂ) *
      (∫ t : Circle, character ((-(-h)) • t) * f (A.act t (g x)) ∂circleHaar) =
    z * ((fejerCoefficient N h : ℂ) *
      (∫ t : Circle, character ((-(-h)) • t) * f (A.act t x) ∂circleHaar))
  have heq : (∫ t : Circle, character ((-(-h)) • t) * f (A.act t (g x)) ∂circleHaar) =
      z * (∫ t : Circle, character ((-(-h)) • t) * f (A.act t x) ∂circleHaar) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with t
    rw [hg, hf]
    ring
  rw [heq]
  ring

theorem component_preserves_character (A B : IsometricCircleAction X) (hAB : A.Commutes B)
    (N : ℕ) (h n : ℤ) {f : X → ℂ}
    (hf : ∀ t x, f (B.act t x) = character (n • t) * f x) (t : Circle) (x : X) :
    A.component N h f (B.act t x) = character (n • t) * A.component N h f x :=
  A.component_equivariant N h (B.act t) (character (n • t)) (fun u x => hAB u t x) (hf t) x

theorem component_sum {ι : Type*} (A : IsometricCircleAction X) (N : ℕ) (h : ℤ)
    (s : Finset ι) (f : ι → X → ℂ) (hf : ∀ i ∈ s, Continuous (f i)) (x : X) :
    A.component N h (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, A.component N h (f i) x := by
  let := A.toAddAction
  let := A.toContinuousVAdd
  unfold component fejerComponent circleFourierComponent
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum]
  · exact Finset.mul_sum s _ _
  · intro i hi
    exact integrable_circleFourierComponent (-h) (hf i hi) x

end Erdos3.CircleFourier.IsometricCircleAction

end

section

namespace Erdos3.CircleFourier

open scoped BigOperators

variable {ι X : Type*} [Fintype ι] [DecidableEq ι] [PseudoMetricSpace X]
  [AddAction (ι → Circle) X] [ContinuousVAdd (ι → Circle) X]

end Erdos3.CircleFourier

end

end OAI
