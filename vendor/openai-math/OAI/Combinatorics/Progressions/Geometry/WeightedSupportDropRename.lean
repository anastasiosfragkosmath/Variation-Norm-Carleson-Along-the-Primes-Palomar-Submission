/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Geometry/WeightedSupportDropRename.lean
Changes: Lean module/public-import conversion; unneeded declarations and imports were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import Mathlib.Algebra.MvPolynomial.Rename
public import OAI.Combinatorics.Progressions.Polynomial.MixedWeightedPolynomialRename
@[expose] public section

namespace OAI


namespace Erdos3

open MvPolynomial

variable {σ R : Type*} [CommRing R]

noncomputable def weightedSupportDrop (w : σ → ℕ) (n r : ℕ) : Submodule R (MvPolynomial σ R) :=
  MvPolynomial.restrictSupport R {a | Finsupp.weight w a + r ≤ n}

theorem mem_weightedSupportDrop_iff (w : σ → ℕ) (n r : ℕ) (P : MvPolynomial σ R) :
    P ∈ weightedSupportDrop w n r ↔ ∀ a ∈ P.support, Finsupp.weight w a + r ≤ n := Iff.rfl

theorem weightedSupportDrop_zero (w : σ → ℕ) (n : ℕ) :
    weightedSupportDrop (R := R) w n 0 = weightedSupportLE w n := by
  ext P
  simp only [mem_weightedSupportDrop_iff, Nat.add_zero]
  rfl

theorem weightedSupportDrop_antitone {w : σ → ℕ} {n r s : ℕ} {P : MvPolynomial σ R}
    (hrs : r ≤ s) (hP : P ∈ weightedSupportDrop w n s) : P ∈ weightedSupportDrop w n r := by
  intro a ha
  change Finsupp.weight w a + r ≤ n
  exact (Nat.add_le_add_left hrs _).trans (hP ha)

theorem weightedSupportDrop_mul {w : σ → ℕ} {d e r s : ℕ} {P Q : MvPolynomial σ R}
    (hP : P ∈ weightedSupportDrop w d r) (hQ : Q ∈ weightedSupportDrop w e s) :
    P * Q ∈ weightedSupportDrop w (d + e) (r + s) := by
  classical
  intro a ha
  obtain ⟨b, hb, c, hc, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul P Q ha)
  have h1 : Finsupp.weight w b + r ≤ d := hP hb
  have h2 : Finsupp.weight w c + s ≤ e := hQ hc
  change Finsupp.weight w (b + c) + (r + s) ≤ d + e
  rw [map_add]
  omega

theorem weightedSupportDrop_mul_LE {w : σ → ℕ} {d e r : ℕ} {P Q : MvPolynomial σ R}
    (hP : P ∈ weightedSupportDrop w d r) (hQ : Q ∈ weightedSupportLE w e) :
    P * Q ∈ weightedSupportDrop w (d + e) r := by
  rw [← weightedSupportDrop_zero] at hQ
  simpa only [Nat.add_zero] using weightedSupportDrop_mul hP hQ

theorem weightedSupportLE_mul_drop {w : σ → ℕ} {d e r : ℕ} {P Q : MvPolynomial σ R}
    (hP : P ∈ weightedSupportLE w d) (hQ : Q ∈ weightedSupportDrop w e r) :
    P * Q ∈ weightedSupportDrop w (d + e) r := by
  rw [mul_comm, Nat.add_comm d e]
  exact weightedSupportDrop_mul_LE hQ hP

end Erdos3


namespace Erdos3

open MvPolynomial

variable {σ τ R : Type*} [CommRing R]

end Erdos3

end OAI
