/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/WeightedTranslationShearExponential.lean
Changes: Lean module/public-import conversion; unneeded declarations and imports were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Nilpotent.BCHQuotientLocalIsometry
public import OAI.Combinatorics.Progressions.Estimates.PrimitiveExtension
public import OAI.Combinatorics.Progressions.Estimates.SquarefreeSplitCount
public import OAI.Combinatorics.Progressions.Estimates.WeightedDerivationDrop
public import OAI.Combinatorics.Progressions.Geometry.BoxCornerMean
public import OAI.Combinatorics.Progressions.Polynomial.RealPolynomialChartSubstitution
@[expose] public section

namespace OAI

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators

variable {σ : Type*} [Fintype σ]

theorem scalarDirectionalDerivative_direction_add (x z : σ → ℚ) (P : MvPolynomial σ ℚ) :
    scalarDirectionalDerivative (x + z) P =
      scalarDirectionalDerivative x P + scalarDirectionalDerivative z P := by
  simp only [scalarDirectionalDerivative_apply, Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem scalarDirectionalDerivative_direction_smul (r : ℚ) (x : σ → ℚ)
    (P : MvPolynomial σ ℚ) :
    scalarDirectionalDerivative (r • x) P = r • scalarDirectionalDerivative x P := by
  simp only [scalarDirectionalDerivative_apply, Pi.smul_apply, smul_eq_mul, smul_smul, Finset.smul_sum]

theorem scalarDirectionalDerivative_direction_zero (P : MvPolynomial σ ℚ) :
    scalarDirectionalDerivative (0 : σ → ℚ) P = 0 := by
  simp [scalarDirectionalDerivative_apply]

theorem scalarDirectionalDerivative_commute (x z : σ → ℚ) (P : MvPolynomial σ ℚ) :
    scalarDirectionalDerivative x (scalarDirectionalDerivative z P) =
      scalarDirectionalDerivative z (scalarDirectionalDerivative x P) := by
  have h : ⁅scalarDirectionalDerivative x, scalarDirectionalDerivative z⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro i
    simp only [Derivation.commutator_apply, scalarDirectionalDerivative_X,
      scalarDirectionalDerivative_C, sub_self, Derivation.zero_apply]
  have hh := congrArg (fun D : Derivation ℚ (MvPolynomial σ ℚ) (MvPolynomial σ ℚ) => D P) h
  exact sub_eq_zero.mp hh

@[ext] structure PolynomialTranslationLie (σ : Type*) where
  base : σ → ℚ
  polynomial : MvPolynomial σ ℚ

namespace PolynomialTranslationLie

noncomputable def toProd : PolynomialTranslationLie σ ≃ (σ → ℚ) × MvPolynomial σ ℚ where
  toFun x := (x.base, x.polynomial)
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance : AddCommGroup (PolynomialTranslationLie σ) := toProd.addCommGroup
noncomputable instance : Module ℚ (PolynomialTranslationLie σ) :=
  { toProd with map_add' _ _ := rfl : PolynomialTranslationLie σ ≃+ (σ → ℚ) × MvPolynomial σ ℚ }.module ℚ

omit [Fintype σ] in
@[simp] theorem base_zero : (0 : PolynomialTranslationLie σ).base = 0 := rfl
omit [Fintype σ] in
@[simp] theorem polynomial_zero : (0 : PolynomialTranslationLie σ).polynomial = 0 := rfl
omit [Fintype σ] in
@[simp] theorem base_add (x y : PolynomialTranslationLie σ) : (x+y).base = x.base+y.base := rfl
omit [Fintype σ] in
@[simp] theorem polynomial_add (x y : PolynomialTranslationLie σ) : (x+y).polynomial = x.polynomial+y.polynomial := rfl
omit [Fintype σ] in
@[simp] theorem base_smul (r : ℚ) (x : PolynomialTranslationLie σ) : (r • x).base = r • x.base := rfl
omit [Fintype σ] in
@[simp] theorem polynomial_smul (r : ℚ) (x : PolynomialTranslationLie σ) : (r • x).polynomial = r • x.polynomial := rfl

noncomputable instance : Bracket (PolynomialTranslationLie σ) (PolynomialTranslationLie σ) where
  bracket x y := ⟨0, scalarDirectionalDerivative x.base y.polynomial -
    scalarDirectionalDerivative y.base x.polynomial⟩

@[simp] theorem base_lie (x y : PolynomialTranslationLie σ) : ⁅x,y⁆.base = 0 := rfl
@[simp] theorem polynomial_lie (x y : PolynomialTranslationLie σ) : ⁅x,y⁆.polynomial =
    scalarDirectionalDerivative x.base y.polynomial - scalarDirectionalDerivative y.base x.polynomial := rfl

noncomputable instance : LieRing (PolynomialTranslationLie σ) where
  add_lie x y z := by
    ext <;> simp [scalarDirectionalDerivative_direction_add]; abel
  lie_add x y z := by
    ext <;> simp [scalarDirectionalDerivative_direction_add]; abel
  lie_self x := by ext <;> simp
  leibniz_lie x y z := by
    ext
    · simp
    · simp only [polynomial_lie, base_lie, polynomial_add, map_sub,
        scalarDirectionalDerivative_direction_zero, sub_zero, zero_sub]
      rw [scalarDirectionalDerivative_commute x.base y.base,
        scalarDirectionalDerivative_commute x.base z.base,
        scalarDirectionalDerivative_commute y.base z.base]
      abel_nf

noncomputable instance : LieAlgebra ℚ (PolynomialTranslationLie σ) where
  lie_smul r x y := by
    ext <;> simp [scalarDirectionalDerivative_direction_smul, smul_sub]

end PolynomialTranslationLie
end Erdos3

end

section

namespace Erdos3

open MvPolynomial

variable {σ : Type*} [Fintype σ]

theorem scalarDirectionalDerivative_weight_drop (w : σ → ℕ) (x : σ → ℚ) (k : ℕ)
    (hx : ∀ i, w i < k → x i = 0) {n r : ℕ} {P : MvPolynomial σ ℚ}
    (hP : P ∈ weightedSupportDrop w n r) :
    scalarDirectionalDerivative x P ∈ weightedSupportDrop w n (r + k) := by
  apply weightedDerivation_apply w (scalarDirectionalDerivative x) k _ hP
  intro i
  rw [scalarDirectionalDerivative_X]
  by_cases hi : k ≤ w i
  · exact (monomial_mem_restrictSupport ℚ).mpr (Or.inl (by simpa using hi))
  · rw [hx i (by omega), map_zero]
    exact Submodule.zero_mem _

namespace PolynomialTranslationLie

noncomputable def weightedLayer (w : σ → ℕ) (d k : ℕ) : Submodule ℚ (PolynomialTranslationLie σ) where
  carrier := {x | (∀ i, w i < k → x.base i = 0) ∧
    x.polynomial ∈ weightedSupportDrop w d k}
  zero_mem' := ⟨by simp, Submodule.zero_mem _⟩
  add_mem' := by
    intro x y hx hy
    exact ⟨fun i hi => by simp [hx.1 i hi, hy.1 i hi],
      Submodule.add_mem _ hx.2 hy.2⟩
  smul_mem' := by
    intro r x hx
    exact ⟨fun i hi => by simp [hx.1 i hi], Submodule.smul_mem _ r hx.2⟩

omit [Fintype σ] in
theorem weightedLayer_antitone (w : σ → ℕ) (d : ℕ) : Antitone (weightedLayer w d) := by
  intro i j hij x hx
  exact ⟨fun a ha => hx.1 a (ha.trans_le hij), weightedSupportDrop_antitone hij hx.2⟩

theorem weightedLayer_lie_mem (w : σ → ℕ) (d : ℕ) {i j : ℕ}
    {x y : PolynomialTranslationLie σ} (hx : x ∈ weightedLayer w d i)
    (hy : y ∈ weightedLayer w d j) : ⁅x,y⁆ ∈ weightedLayer w d (i+j) := by
  refine ⟨by simp, ?_⟩
  change scalarDirectionalDerivative x.base y.polynomial -
    scalarDirectionalDerivative y.base x.polynomial ∈ _
  apply Submodule.sub_mem
  · simpa only [Nat.add_comm j i] using scalarDirectionalDerivative_weight_drop w x.base i hx.1 hy.2
  · exact scalarDirectionalDerivative_weight_drop w y.base j hy.1 hx.2

noncomputable def weightedSubalgebra (w : σ → ℕ) (d : ℕ) : LieSubalgebra ℚ (PolynomialTranslationLie σ) :=
  { weightedLayer w d 1 with
    lie_mem' := fun hx hy => weightedLayer_antitone w d (by omega : 1 ≤ 1+1)
      (weightedLayer_lie_mem w d hx hy) }

@[simp] theorem mem_weightedSubalgebra (w : σ → ℕ) (d : ℕ) (x : PolynomialTranslationLie σ) :
    x ∈ weightedSubalgebra w d ↔ x ∈ weightedLayer w d 1 := Iff.rfl

end PolynomialTranslationLie
end Erdos3

end

section

namespace Erdos3.PolynomialTranslationLie

open MvPolynomial

variable {σ : Type*} [Fintype σ]

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open MvPolynomial
open scoped TensorProduct

variable {σ : Type*} [Fintype σ]

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open MvPolynomial
open scoped TensorProduct

variable {σ : Type*} [Fintype σ]

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open MvPolynomial
open scoped BigOperators

variable {σ : Type*} [Fintype σ]

end Erdos3.PolynomialTranslationLie

end

end OAI
