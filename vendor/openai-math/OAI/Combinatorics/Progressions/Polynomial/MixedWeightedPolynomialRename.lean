/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Polynomial/MixedWeightedPolynomialRename.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Polynomial.Derivative
public import OAI.Combinatorics.Progressions.Polynomial.VectorPolynomialReconstruction
@[expose] public section

namespace OAI

section

namespace Erdos3

open MvPolynomial
open scoped Pointwise

variable {σ R : Type*} [CommRing R]

noncomputable def polynomialTranslate (h : σ → R) : MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  MvPolynomial.aeval (fun i => X i + C (h i))

@[simp] theorem polynomialTranslate_X (h : σ → R) (i : σ) :
    polynomialTranslate h (X i) = X i + C (h i) := by simp [polynomialTranslate]

@[simp] theorem polynomialTranslate_C (h : σ → R) (r : R) :
    polynomialTranslate h (C r) = C r := by simp [polynomialTranslate]

noncomputable def weightedSupportLE (w : σ → ℕ) (d : ℕ) : Submodule R (MvPolynomial σ R) :=
  MvPolynomial.restrictSupport R {α | Finsupp.weight w α ≤ d}

noncomputable def weightedSupportLT (w : σ → ℕ) (d : ℕ) : Submodule R (MvPolynomial σ R) :=
  MvPolynomial.restrictSupport R {α | Finsupp.weight w α < d}

theorem weightedSupportLE_monomial (w : σ → ℕ) (α : σ →₀ ℕ) (r : R) :
    monomial α r ∈ weightedSupportLE w (Finsupp.weight w α) := by
  apply (monomial_mem_restrictSupport R).mpr
  left
  change Finsupp.weight w α ≤ Finsupp.weight w α
  exact le_rfl

theorem weightedSupportLE_mul {w : σ → ℕ} {d e : ℕ} {p q : MvPolynomial σ R}
    (hp : p ∈ weightedSupportLE w d) (hq : q ∈ weightedSupportLE w e) :
    p * q ∈ weightedSupportLE w (d + e) := by
  classical
  intro α hα
  obtain ⟨β, hβ, γ, hγ, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul p q hα)
  exact (map_add (Finsupp.weight w) β γ).trans_le (Nat.add_le_add (hp hβ) (hq hγ))

theorem weightedSupportLT_mul_LE {w : σ → ℕ} {d e : ℕ} {p q : MvPolynomial σ R}
    (hp : p ∈ weightedSupportLT w d) (hq : q ∈ weightedSupportLE w e) :
    p * q ∈ weightedSupportLT w (d + e) := by
  classical
  intro α hα
  obtain ⟨β, hβ, γ, hγ, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul p q hα)
  exact (map_add (Finsupp.weight w) β γ).trans_lt (Nat.add_lt_add_of_lt_of_le (hp hβ) (hq hγ))

theorem weightedSupportLE_mul_LT {w : σ → ℕ} {d e : ℕ} {p q : MvPolynomial σ R}
    (hp : p ∈ weightedSupportLE w d) (hq : q ∈ weightedSupportLT w e) :
    p * q ∈ weightedSupportLT w (d + e) := by
  rw [mul_comm, Nat.add_comm]
  exact weightedSupportLT_mul_LE hq hp

private theorem translation_bounds_mul (h : σ → R) (w : σ → ℕ)
    (p q : MvPolynomial σ R) (d e : ℕ)
    (hp : p ∈ weightedSupportLE w d)
    (htp : polynomialTranslate h p ∈ weightedSupportLE w d)
    (htq : polynomialTranslate h q ∈ weightedSupportLE w e)
    (hdp : polynomialTranslate h p - p ∈ weightedSupportLT w d)
    (hdq : polynomialTranslate h q - q ∈ weightedSupportLT w e) :
    polynomialTranslate h (p * q) ∈ weightedSupportLE w (d + e) ∧
      polynomialTranslate h (p * q) - p * q ∈ weightedSupportLT w (d + e) := by
  refine ⟨by rw [map_mul]; exact weightedSupportLE_mul htp htq, ?_⟩
  rw [map_mul, show polynomialTranslate h p * polynomialTranslate h q - p * q =
    (polynomialTranslate h p - p) * polynomialTranslate h q + p * (polynomialTranslate h q - q) by ring]
  exact (weightedSupportLT w (d + e)).add_mem (weightedSupportLT_mul_LE hdp htq)
    (weightedSupportLE_mul_LT hp hdq)

theorem polynomialTranslate_monomial_bounds (h : σ → R) (w : σ → ℕ)
    (hw : ∀ i, 0 < w i) (α : σ →₀ ℕ) :
    polynomialTranslate h (monomial α 1) ∈ weightedSupportLE w (Finsupp.weight w α) ∧
      polynomialTranslate h (monomial α 1) - monomial α 1 ∈
        weightedSupportLT w (Finsupp.weight w α) := by
  classical
  have hX (i : σ) : polynomialTranslate h (X i) ∈ weightedSupportLE w (w i) ∧
      polynomialTranslate h (X i) - X i ∈ weightedSupportLT w (w i) := by
    have hi : (X i : MvPolynomial σ R) ∈ weightedSupportLE w (w i) := by
      simpa only [X, Finsupp.weight_single, one_smul] using weightedSupportLE_monomial w (Finsupp.single i 1) (1 : R)
    have hc : (C (h i) : MvPolynomial σ R) ∈ weightedSupportLE w (w i) := by
      exact (monomial_mem_restrictSupport R).mpr (Or.inl (by simp))
    refine ⟨by rw [polynomialTranslate_X]; exact (weightedSupportLE w _).add_mem hi hc, ?_⟩
    rw [polynomialTranslate_X, add_sub_cancel_left]
    exact (monomial_mem_restrictSupport R).mpr (Or.inl (by simpa using hw i))
  have hsingle (i : σ) (n : ℕ) :
      polynomialTranslate h (monomial (Finsupp.single i n) 1) ∈ weightedSupportLE w (n * w i) ∧
      polynomialTranslate h (monomial (Finsupp.single i n) 1) - monomial (Finsupp.single i n) 1 ∈
        weightedSupportLT w (n * w i) := by
    induction n with
    | zero =>
      rw [Finsupp.single_zero, zero_mul]
      change polynomialTranslate h 1 ∈ weightedSupportLE w 0 ∧
        polynomialTranslate h 1 - 1 ∈ weightedSupportLT w 0
      rw [map_one, sub_self]
      exact ⟨by simpa using weightedSupportLE_monomial w (0 : σ →₀ ℕ) (1 : R), Submodule.zero_mem _⟩
    | succ n ih =>
      have hp := weightedSupportLE_monomial w (Finsupp.single i n) (1 : R)
      simp only [Finsupp.weight_single, smul_eq_mul] at hp
      have hh := translation_bounds_mul h w (monomial (Finsupp.single i n) 1) (X i)
        (n * w i) (w i) hp ih.1 (hX i).1 ih.2 (hX i).2
      simpa only [X, monomial_mul_monomial, one_mul, ← Finsupp.single_add, Nat.succ_mul] using hh
  induction α using Finsupp.induction with
  | zero =>
    change polynomialTranslate h 1 ∈ weightedSupportLE w 0 ∧
      polynomialTranslate h 1 - 1 ∈ weightedSupportLT w 0
    rw [map_one, sub_self]
    exact ⟨by simpa using weightedSupportLE_monomial w (0 : σ →₀ ℕ) (1 : R), Submodule.zero_mem _⟩
  | @single_add i n α hi hn ih =>
    have hp := weightedSupportLE_monomial w (Finsupp.single i n) (1 : R)
    have hh := translation_bounds_mul h w (monomial (Finsupp.single i n) 1) (monomial α 1)
      (Finsupp.weight w (Finsupp.single i n)) (Finsupp.weight w α) hp
      (by simpa only [Finsupp.weight_single, smul_eq_mul] using (hsingle i n).1) ih.1
      (by simpa only [Finsupp.weight_single, smul_eq_mul] using (hsingle i n).2) ih.2
    simpa only [monomial_mul_monomial, one_mul, map_add] using hh

end Erdos3

end

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators Pointwise

variable {σ : Type*}

noncomputable def polynomialDegreeGap (k d : ℕ) : Submodule ℚ (MvPolynomial σ ℚ) :=
  MvPolynomial.restrictSupport ℚ {α | Finsupp.weight (fun _ => 1) α + k ≤ d}

theorem polynomialDegreeGap_monomial (α : σ →₀ ℕ) (c : ℚ) :
    monomial α c ∈ polynomialDegreeGap 0 (Finsupp.weight (fun _ => 1) α) :=
  (monomial_mem_restrictSupport ℚ).mpr (Or.inl (by simp))

theorem polynomialDegreeGap_mul {i j d e : ℕ} {p q : MvPolynomial σ ℚ}
    (hp : p ∈ polynomialDegreeGap i d) (hq : q ∈ polynomialDegreeGap j e) :
    p * q ∈ polynomialDegreeGap (i + j) (d + e) := by
  classical
  intro α hα
  obtain ⟨β, hβ, γ, hγ, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul p q hα)
  have hb := hp hβ
  have hc := hq hγ
  change Finsupp.weight (fun _ : σ => 1) β + i ≤ d at hb
  change Finsupp.weight (fun _ : σ => 1) γ + j ≤ e at hc
  change Finsupp.weight (fun _ : σ => 1) (β + γ) + (i + j) ≤ d + e
  rw [map_add]
  omega

theorem polynomialDegreeGap_pderiv {k d : ℕ} {p : MvPolynomial σ ℚ}
    (hp : p ∈ polynomialDegreeGap k d) (i : σ) :
    MvPolynomial.pderiv i p ∈ polynomialDegreeGap (k + 1) d := by
  classical
  intro α hα
  change α ∈ (MvPolynomial.pderiv i p).support at hα
  have hn : p.coeff (α + Finsupp.single i 1) ≠ 0 := by
    intro hz
    have hc : (MvPolynomial.pderiv i p).coeff α ≠ 0 := MvPolynomial.mem_support_iff.mp hα
    rw [MvPolynomial.coeff_pderiv, hz, zero_mul] at hc
    exact hc rfl
  have hh := hp (MvPolynomial.mem_support_iff.mpr hn)
  change Finsupp.weight (fun _ : σ => 1) (α + Finsupp.single i 1) + k ≤ d at hh
  simp only [map_add, Finsupp.weight_single, one_smul] at hh
  change Finsupp.weight (fun _ : σ => 1) α + (k + 1) ≤ d
  omega

noncomputable def scalarDirectionalDerivative [Fintype σ] (h : σ → ℚ) :
    Derivation ℚ (MvPolynomial σ ℚ) (MvPolynomial σ ℚ) :=
  ∑ i, h i • MvPolynomial.pderiv i

theorem scalarDirectionalDerivative_apply [Fintype σ] (h : σ → ℚ) (p : MvPolynomial σ ℚ) :
    scalarDirectionalDerivative h p = ∑ i, h i • MvPolynomial.pderiv i p := by
  change (Derivation.coeFnAddMonoidHom (∑ i, h i • MvPolynomial.pderiv i)) p = _
  rw [map_sum]
  simp only [Finset.sum_apply, Derivation.coeFnAddMonoidHom_apply, Derivation.smul_apply]

@[simp] theorem scalarDirectionalDerivative_C [Fintype σ] (h : σ → ℚ) (c : ℚ) :
    scalarDirectionalDerivative h (C c) = 0 := MvPolynomial.derivation_C _ _

@[simp] theorem scalarDirectionalDerivative_X [Fintype σ] (h : σ → ℚ) (j : σ) :
    scalarDirectionalDerivative h (X j) = C (h j) := by
  classical
  simp [scalarDirectionalDerivative_apply, MvPolynomial.pderiv_X, Pi.single_apply, MvPolynomial.C_eq_smul_one]

theorem scalarDirectionalDerivative_mul [Fintype σ] (h : σ → ℚ) (p q : MvPolynomial σ ℚ) :
    scalarDirectionalDerivative h (p * q) = scalarDirectionalDerivative h p * q +
      p * scalarDirectionalDerivative h q := by
  rw [Derivation.leibniz]
  simp only [smul_eq_mul]
  ring

theorem polynomialDegreeGap_directionalDerivative [Fintype σ] (h : σ → ℚ)
    {k d : ℕ} {p : MvPolynomial σ ℚ} (hp : p ∈ polynomialDegreeGap k d) :
    scalarDirectionalDerivative h p ∈ polynomialDegreeGap (k + 1) d := by
  rw [scalarDirectionalDerivative_apply]
  exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (polynomialDegreeGap_pderiv hp i))

theorem polynomialDegreeGap_translate_monomial (h : σ → ℚ) (α : σ →₀ ℕ) :
    polynomialTranslate h (monomial α 1) ∈ polynomialDegreeGap 0 (Finsupp.weight (fun _ => 1) α) := by
  intro β hβ
  simpa only [Nat.add_zero] using
    (polynomialTranslate_monomial_bounds h (fun _ => 1) (by simp) α).1 hβ

theorem polynomialDegreeGap_translate_sub_monomial (h : σ → ℚ) (α : σ →₀ ℕ) :
    polynomialTranslate h (monomial α 1) - monomial α 1 ∈
      polynomialDegreeGap 1 (Finsupp.weight (fun _ => 1) α) := by
  intro β hβ
  exact Nat.succ_le_of_lt ((polynomialTranslate_monomial_bounds h (fun _ => 1) (by simp) α).2 hβ)

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

variable {σ R S : Type*} [CommRing R] [CommRing S]

end Erdos3

end

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators

variable {σ τ R : Type*} [CommRing R]

theorem weightedSupportLE_C (w : σ → ℕ) (d : ℕ) (r : R) :
    C r ∈ weightedSupportLE w d := by
  exact (monomial_mem_restrictSupport R).mpr (Or.inl (by simp))

theorem weightedSupportLE_X (w : σ → ℕ) (i : σ) :
    (X i : MvPolynomial σ R) ∈ weightedSupportLE w (w i) := by
  simpa only [X, Finsupp.weight_single, one_smul] using
    weightedSupportLE_monomial w (Finsupp.single i 1) (1 : R)

theorem weightedSupportLE_pow {w : σ → ℕ} {d : ℕ} {p : MvPolynomial σ R}
    (hp : p ∈ weightedSupportLE w d) (n : ℕ) :
    p ^ n ∈ weightedSupportLE w (n * d) := by
  induction n with
  | zero => simpa using weightedSupportLE_C w 0 (1 : R)
  | succ n ih =>
    simpa only [pow_succ, Nat.succ_mul] using weightedSupportLE_mul ih hp

theorem weightedSupportLE_prod {ι : Type*} (s : Finset ι) (w : σ → ℕ)
    (f : ι → MvPolynomial σ R) (d : ι → ℕ)
    (hf : ∀ i ∈ s, f i ∈ weightedSupportLE w (d i)) :
    (∏ i ∈ s, f i) ∈ weightedSupportLE w (∑ i ∈ s, d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using weightedSupportLE_C w 0 (1 : R)
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact weightedSupportLE_mul (hf i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem weightedSupportLE_aeval_monomial (w : σ → ℕ) (v : τ → ℕ)
    (f : σ → MvPolynomial τ R) (hf : ∀ i, f i ∈ weightedSupportLE v (w i))
    (α : σ →₀ ℕ) (r : R) :
    aeval (R := R) f (monomial α r) ∈ weightedSupportLE v (Finsupp.weight w α) := by
  classical
  rw [aeval_monomial]
  have hprod := weightedSupportLE_prod α.support v (fun i => f i ^ α i)
    (fun i => α i * w i) (fun i _ => weightedSupportLE_pow (hf i) (α i))
  have hweight : (∑ i ∈ α.support, α i * w i) = Finsupp.weight w α := by
    simp only [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul, Nat.cast_id]
  rw [hweight] at hprod
  simpa only [zero_add, MvPolynomial.algebraMap_eq, Finsupp.prod] using
    weightedSupportLE_mul (weightedSupportLE_C v 0 r) hprod

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

variable {σ : Type*} [Fintype σ]

noncomputable def scalarTaylorRemainder (h : σ → ℚ) :
    MvPolynomial σ ℚ →ₗ[ℚ] MvPolynomial σ ℚ :=
  (polynomialTranslate h).toLinearMap - LinearMap.id - (scalarDirectionalDerivative h).toLinearMap

theorem scalarTaylorRemainder_apply (h : σ → ℚ) (p : MvPolynomial σ ℚ) :
    scalarTaylorRemainder h p = polynomialTranslate h p - p - scalarDirectionalDerivative h p := rfl

@[simp] theorem scalarTaylorRemainder_C (h : σ → ℚ) (c : ℚ) :
    scalarTaylorRemainder h (C c) = 0 := by
  rw [scalarTaylorRemainder_apply, polynomialTranslate_C, scalarDirectionalDerivative_C, sub_self, sub_zero]

@[simp] theorem scalarTaylorRemainder_X (h : σ → ℚ) (i : σ) :
    scalarTaylorRemainder h (X i) = 0 := by
  rw [scalarTaylorRemainder_apply, polynomialTranslate_X, scalarDirectionalDerivative_X]
  ring

theorem scalarTaylorRemainder_mul (h : σ → ℚ) (p q : MvPolynomial σ ℚ) :
    scalarTaylorRemainder h (p * q) =
      scalarTaylorRemainder h p * polynomialTranslate h q +
        scalarDirectionalDerivative h p * (polynomialTranslate h q - q) +
        p * scalarTaylorRemainder h q := by
  simp only [scalarTaylorRemainder_apply, map_mul, scalarDirectionalDerivative_mul]
  ring

private theorem remainder_monomial_add (h : σ → ℚ) (α β : σ →₀ ℕ)
    (hα : scalarTaylorRemainder h (monomial α 1) ∈
      polynomialDegreeGap 2 (Finsupp.weight (fun _ => 1) α))
    (hβ : scalarTaylorRemainder h (monomial β 1) ∈
      polynomialDegreeGap 2 (Finsupp.weight (fun _ => 1) β)) :
    scalarTaylorRemainder h (monomial (α + β) 1) ∈
      polynomialDegreeGap 2 (Finsupp.weight (fun _ => 1) (α + β)) := by
  rw [map_add]
  have he : (monomial (α + β) 1 : MvPolynomial σ ℚ) = monomial α 1 * monomial β 1 := by simp
  rw [he, scalarTaylorRemainder_mul]
  apply Submodule.add_mem
  · apply Submodule.add_mem
    · exact polynomialDegreeGap_mul (i := 2) (j := 0) hα (polynomialDegreeGap_translate_monomial h β)
    · exact polynomialDegreeGap_mul (i := 1) (j := 1)
        (polynomialDegreeGap_directionalDerivative h (k := 0) (polynomialDegreeGap_monomial α 1))
        (polynomialDegreeGap_translate_sub_monomial h β)
  · exact polynomialDegreeGap_mul (i := 0) (j := 2) (polynomialDegreeGap_monomial α 1) hβ

theorem scalarTaylorRemainder_monomial (h : σ → ℚ) (α : σ →₀ ℕ) :
    scalarTaylorRemainder h (monomial α 1) ∈
      polynomialDegreeGap 2 (Finsupp.weight (fun _ => 1) α) := by
  classical
  have hz : scalarTaylorRemainder h (monomial (0 : σ →₀ ℕ) 1) = 0 :=
    scalarTaylorRemainder_C h 1
  have hsingle (i : σ) (n : ℕ) : scalarTaylorRemainder h (monomial (Finsupp.single i n) 1) ∈
      polynomialDegreeGap 2 (Finsupp.weight (fun _ => 1) (Finsupp.single i n)) := by
    induction n with
    | zero => rw [Finsupp.single_zero, hz]; exact Submodule.zero_mem _
    | succ n ih =>
      rw [show Finsupp.single i (n + 1) = Finsupp.single i n + Finsupp.single i 1 from Finsupp.single_add _ _ _]
      apply remainder_monomial_add h _ _ ih
      change scalarTaylorRemainder h (X i) ∈ _
      rw [scalarTaylorRemainder_X]
      exact Submodule.zero_mem _
  induction α using Finsupp.induction with
  | zero => rw [hz]; exact Submodule.zero_mem _
  | @single_add i n α _ _ ih => exact remainder_monomial_add h _ _ (hsingle i n) ih

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

variable {σ : Type*}

end Erdos3

end

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators

variable {σ τ R : Type*} [CommRing R]

namespace SlotAffine

variable [Fintype τ] {h : ℕ}

end SlotAffine

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

variable {U B R : Type*} [CommRing R]

end Erdos3

end

end OAI
