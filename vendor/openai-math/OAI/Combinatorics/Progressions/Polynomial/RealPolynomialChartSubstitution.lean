/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Polynomial/RealPolynomialChartSubstitution.lean
Changes: Lean module/public-import conversion, removal of unneeded declarations and imports, plus compatibility
edits for Lean 4.35 and its Mathlib (vendor/provenance/openai-progressions-files.json).
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import OAI.Combinatorics.Progressions.Linear.DualDerivativeRemoval
public import OAI.Combinatorics.Progressions.Polynomial.AdaptedPolynomialSubstitution
@[expose] public section

namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

variable {σ : Type*}

namespace VectorPolynomial

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

noncomputable def directionalDerivative [Fintype σ] (h : σ → ℚ) :
    VectorPolynomial σ ℚ L →ₗ[ℚ] VectorPolynomial σ ℚ L :=
  ∑ i, h i • (MvPolynomial.pderiv i).toLinearMap.rTensor L

@[simp] theorem directionalDerivative_tmul [Fintype σ]
    (h : σ → ℚ) (p : MvPolynomial σ ℚ) (x : L) :
    directionalDerivative h (p ⊗ₜ[ℚ] x) =
      ∑ i, h i • (MvPolynomial.pderiv i p ⊗ₜ[ℚ] x) := by
  simp [directionalDerivative]

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem pderiv_lie (i : σ) (p q : VectorPolynomial σ ℚ L) :
    (MvPolynomial.pderiv i).toLinearMap.rTensor L ⁅p, q⁆ =
      ⁅(MvPolynomial.pderiv i).toLinearMap.rTensor L p, q⁆ +
        ⁅p, (MvPolynomial.pderiv i).toLinearMap.rTensor L q⁆ := by
  induction p using TensorProduct.inductionOn with
  | tmul a x =>
    induction q using TensorProduct.inductionOn with
    | tmul b y =>
      simp only [LieAlgebra.ExtendScalars.bracket_tmul, LinearMap.rTensor_tmul]
      change MvPolynomial.pderiv i (a * b) ⊗ₜ[ℚ] ⁅x, y⁆ =
        (MvPolynomial.pderiv i a * b) ⊗ₜ[ℚ] ⁅x, y⁆ +
          (a * MvPolynomial.pderiv i b) ⊗ₜ[ℚ] ⁅x, y⁆
      rw [MvPolynomial.pderiv_mul, TensorProduct.add_tmul]
    | add q r hq hr =>
      simp only [LieRing.lie_add, map_add, hq, hr]
      abel
  | add p r hp hr =>
    simp only [LieRing.add_lie, map_add, hp, hr]
    abel

theorem directionalDerivative_lie [Fintype σ] (h : σ → ℚ) (p q : VectorPolynomial σ ℚ L) :
    directionalDerivative h ⁅p, q⁆ =
      ⁅directionalDerivative h p, q⁆ + ⁅p, directionalDerivative h q⁆ := by
  simp only [directionalDerivative, LinearMap.sum_apply, LinearMap.smul_apply,
    pderiv_lie, smul_add, Finset.sum_add_distrib,
    sum_lie (L := VectorPolynomial σ ℚ L) (M := VectorPolynomial σ ℚ L),
    lie_sum (L := VectorPolynomial σ ℚ L) (M := VectorPolynomial σ ℚ L),
    smul_lie (R := ℚ) (L := VectorPolynomial σ ℚ L) (M := VectorPolynomial σ ℚ L),
    lie_smul (R := ℚ) (L := VectorPolynomial σ ℚ L) (M := VectorPolynomial σ ℚ L)]

theorem directionalDerivative_direction_add [Fintype σ]
    (h k : σ → ℚ) (p : VectorPolynomial σ ℚ L) :
    directionalDerivative (h + k) p = directionalDerivative h p + directionalDerivative k p := by
  simp only [directionalDerivative, Pi.add_apply, add_smul, Finset.sum_add_distrib,
    LinearMap.add_apply]

theorem directionalDerivative_direction_smul [Fintype σ]
    (r : ℚ) (h : σ → ℚ) (p : VectorPolynomial σ ℚ L) :
    directionalDerivative (r • h) p = r • directionalDerivative h p := by
  simp only [directionalDerivative, Pi.smul_apply, smul_eq_mul, mul_smul,
    ← Finset.smul_sum, LinearMap.smul_apply]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.NilpotentLieBCHGroup

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

abbrev PolynomialGroup (σ : Type*) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) :=
  NilpotentLieBCHGroup (VectorPolynomial σ ℚ L) s (VectorPolynomial.lowerCentralSeries_eq_bot hnil)

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

noncomputable def formalPolynomialJetLie (i : σ) :
    VectorPolynomial σ ℚ L →ₗ⁅ℚ⁆ DualLieAlgebra (VectorPolynomial σ ℚ L) where
  toLinearMap := dualConstantLie.toLinearMap +
    dualInfinitesimal.comp ((MvPolynomial.pderiv i).toLinearMap.rTensor L)
  map_lie' {P Q} := by
    change dualConstantLie ⁅P, Q⁆ +
      dualInfinitesimal ((MvPolynomial.pderiv i).toLinearMap.rTensor L ⁅P, Q⁆) =
      ⁅dualConstantLie P + dualInfinitesimal ((MvPolynomial.pderiv i).toLinearMap.rTensor L P),
        dualConstantLie Q + dualInfinitesimal ((MvPolynomial.pderiv i).toLinearMap.rTensor L Q)⁆
    apply dual_ext
    · simp only [map_add, dualBaseLinear_constant, dualBaseLinear_infinitesimal,
        add_zero, dualBaseLinear_lie]
    · simp only [map_add, dualTangentLinear_constant, dualTangentLinear_infinitesimal,
        zero_add, dualTangentLinear_lie, dualBaseLinear_constant,
        dualBaseLinear_infinitesimal, add_zero]
      rw [pderiv_lie]
      exact add_comm _ _

noncomputable def formalPolynomialJetHom (i : σ) :
    PolynomialGroup σ hnil →* DualGroup (VectorPolynomial.lowerCentralSeries_eq_bot (σ := σ) hnil) :=
  NilpotentLieBCHGroup.map (formalPolynomialJetLie i)

@[simp] theorem formalPolynomialJet_base (i : σ) (P : PolynomialGroup σ hnil) :
    dualBaseLinear (formalPolynomialJetHom i P).coord = P.coord := by
  change dualBaseLinear (dualConstantLie P.coord +
    dualInfinitesimal ((MvPolynomial.pderiv i).toLinearMap.rTensor L P.coord)) = _
  rw [map_add, dualBaseLinear_constant, dualBaseLinear_infinitesimal, add_zero]

@[simp] theorem formalPolynomialJet_tangent (i : σ) (P : PolynomialGroup σ hnil) :
    dualTangentLinear (formalPolynomialJetHom i P).coord =
      (MvPolynomial.pderiv i).toLinearMap.rTensor L P.coord := by
  change dualTangentLinear (dualConstantLie P.coord +
    dualInfinitesimal ((MvPolynomial.pderiv i).toLinearMap.rTensor L P.coord)) = _
  rw [map_add, dualTangentLinear_constant, dualTangentLinear_infinitesimal, zero_add]

@[simp] theorem formalPolynomialJet_baseHom (i : σ) (P : PolynomialGroup σ hnil) :
    dualBaseHom (formalPolynomialJetHom i P) = P :=
  NilpotentLieBCHGroup.ext (formalPolynomialJet_base i P)

noncomputable def formalLogDerivative (i : σ) (P : PolynomialGroup σ hnil) :
    VectorPolynomial σ ℚ L := dualLogDerivative (formalPolynomialJetHom i P)

theorem formalLogDerivative_remove (i : σ) (A P B : PolynomialGroup σ hnil) :
    formalLogDerivative i (A⁻¹ * P * B⁻¹) =
      dualAdjoint A⁻¹ (formalLogDerivative i P - formalLogDerivative i A) -
        dualAdjoint (A⁻¹ * P * B⁻¹) (formalLogDerivative i B) := by
  have h := dualLogDerivative_remove
    (formalPolynomialJetHom i A) (formalPolynomialJetHom i P) (formalPolynomialJetHom i B)
  simpa only [map_mul, map_inv, formalPolynomialJet_baseHom, formalLogDerivative] using h

theorem formalLogDerivative_mem_of_invariant
    (U : LieSubalgebra ℚ (VectorPolynomial σ ℚ L))
    (V : Submodule ℚ (VectorPolynomial σ ℚ L))
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (i : σ) (P : PolynomialGroup σ hnil) (hP : P.coord ∈ U)
    (hD : (MvPolynomial.pderiv i).toLinearMap.rTensor L P.coord ∈ V) :
    formalLogDerivative i P ∈ V := by
  apply dualLogDerivative_mem_of_invariant U V hUV (formalPolynomialJetHom i P)
  · simpa only [formalPolynomialJet_base] using hP
  · simpa only [formalPolynomialJet_tangent] using hD

def PolynomialDerivativeSystem (P : PolynomialGroup σ hnil)
    (small rational extra : σ → VectorPolynomial σ ℚ L) : Prop :=
  ∀ i, formalLogDerivative i P = small i + dualAdjoint P (rational i) + extra i

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

noncomputable def realPolynomialValueHom (t : σ → ℝ) :
    PolynomialGroup σ hnil →* NilpotentLieBCHGroup L s hnil :=
  NilpotentLieBCHGroup.map (eval₂Lie (R := ℚ) (S := ℝ) (L := L) t)

@[simp] theorem realPolynomialValueHom_coord (t : σ → ℝ) (P : PolynomialGroup σ hnil) :
    (realPolynomialValueHom t P).coord = eval₂ t P.coord := rfl

noncomputable def realPolynomialJet (i : σ) (t : σ → ℝ) (P : PolynomialGroup σ hnil) :
    DualGroup hnil :=
  ⟨dualConstantLie (eval₂ t P.coord) +
    dualInfinitesimal (eval₂ t ((MvPolynomial.pderiv i).toLinearMap.rTensor L P.coord))⟩

@[simp] theorem realPolynomialJet_base (i : σ) (t : σ → ℝ) (P : PolynomialGroup σ hnil) :
    dualBaseLinear (realPolynomialJet i t P).coord = eval₂ t P.coord := by
  change dualBaseLinear (dualConstantLie _ + dualInfinitesimal _) = _
  rw [map_add, dualBaseLinear_constant, dualBaseLinear_infinitesimal, add_zero]

@[simp] theorem realPolynomialJet_tangent (i : σ) (t : σ → ℝ) (P : PolynomialGroup σ hnil) :
    dualTangentLinear (realPolynomialJet i t P).coord =
      eval₂ t ((MvPolynomial.pderiv i).toLinearMap.rTensor L P.coord) := by
  change dualTangentLinear (dualConstantLie _ + dualInfinitesimal _) = _
  rw [map_add, dualTangentLinear_constant, dualTangentLinear_infinitesimal, zero_add]

@[simp] theorem realPolynomialJet_baseHom (i : σ) (t : σ → ℝ) (P : PolynomialGroup σ hnil) :
    dualBaseHom (realPolynomialJet i t P) = realPolynomialValueHom t P :=
  NilpotentLieBCHGroup.ext (realPolynomialJet_base i t P)

theorem eval₂_formalLogDerivative (i : σ) (t : σ → ℝ) (P : PolynomialGroup σ hnil) :
    eval₂ t (formalLogDerivative i P) = dualLogDerivative (realPolynomialJet i t P) := by
  have h := dualLinearLift_logDerivative hnil ⊤ (eval₂Lie (R := ℚ) (S := ℝ) (L := L) t)
    (eval₂ t) (fun a b _ => (eval₂Lie (R := ℚ) (S := ℝ) (L := L) t).map_lie a b)
    (formalPolynomialJetHom i P) (by trivial)
  simp only [dualLinearLift_apply, formalPolynomialJet_base, formalPolynomialJet_tangent,
    eval₂Lie_apply] at h
  exact h

theorem eval₂_dualAdjoint (t : σ → ℝ) (P : PolynomialGroup σ hnil)
    (Q : VectorPolynomial σ ℚ L) :
    eval₂ t (dualAdjoint P Q) = dualAdjoint (realPolynomialValueHom t P) (eval₂ t Q) := by
  have h := map_dualAdjoint (hM := hnil) (eval₂Lie (R := ℚ) (S := ℝ) (L := L) t) P Q
  simp only [eval₂Lie_apply] at h
  exact h

theorem PolynomialDerivativeSystem.real_evaluation (P : PolynomialGroup σ hnil)
    (small rational extra : σ → VectorPolynomial σ ℚ L)
    (hsystem : PolynomialDerivativeSystem P small rational extra) (i : σ) (t : σ → ℝ) :
    dualLogDerivative (realPolynomialJet i t P) = eval₂ t (small i) +
      dualAdjoint (realPolynomialValueHom t P) (eval₂ t (rational i)) + eval₂ t (extra i) := by
  have h := congrArg (eval₂ t) (hsystem i)
  simpa only [eval₂_formalLogDerivative, map_add, eval₂_dualAdjoint] using h

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct

variable {σ τ υ V : Type*} [AddCommGroup V] [Module ℚ V] [Module ℝ V]
  [IsScalarTower ℚ ℝ V]

end Erdos3.VectorPolynomial

namespace Erdos3.VectorPolynomial

variable {σ τ L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L]

end Erdos3.VectorPolynomial

namespace Erdos3.NilpotentLieBCHGroup

open VectorPolynomial

variable {σ τ L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] {s : ℕ}
  (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)

end Erdos3.NilpotentLieBCHGroup

end

end OAI
