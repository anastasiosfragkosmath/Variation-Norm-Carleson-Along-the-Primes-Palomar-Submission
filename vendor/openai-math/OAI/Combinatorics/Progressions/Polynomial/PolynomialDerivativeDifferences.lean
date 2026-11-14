/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Polynomial/PolynomialDerivativeDifferences.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Polynomial.QuantitativeOuterPolynomialProducts
@[expose] public section

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_real_adapted_dual_grid (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        (∀ x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1),
          F.RealAdaptedCoefficientGrid b ω hF (fun _ => 1) l x →
          ∀ h : σ → ℤ, F.RealAdaptedCoefficientGrid b ω hF (fun _ => 1) m
            (F.realAdaptedLogDerivative (fun i => (h i : ℚ)) x)) ∧
        (∀ (g : F.RealAdaptedPolynomialGroup (fun _ : σ => 1))
          (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)),
          F.RealAdaptedCoefficientGrid b ω hF (fun _ => 1) l g.coord →
          F.RealAdaptedCoefficientGrid b ω hF (fun _ => 1) l x →
          F.RealAdaptedCoefficientGrid b ω hF (fun _ => 1) m (dualAdjoint g x)) := by
  have hgridExists := exists_real_dual_operation_grid s
  obtain ⟨D, _, hgrid⟩ := hgridExists
  let Q : Polynomial ℕ := (Polynomial.X + Polynomial.C (s + 2)) ^ (s + 2)
  let B : Polynomial ℕ := (Q + Polynomial.C D) ^ D
  have hboundExists := exists_natPolynomial_eval_budget B
  obtain ⟨C, hC, hbound⟩ := hboundExists
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hF H p hH hp hι hσ hHp hc l hl hlp
  let : Fintype (AdaptedBasisIndex (fun _ : σ => 1) ω) :=
    adaptedBasisIndexFintype (fun _ => 1) ω s (by simp) (F.adaptedBasis_weight_le_step b ω hF)
  let q := (p + (s + 2)) ^ (s + 2)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by
    apply (le_add_of_nonneg_right (by positivity : (0 : ℝ) ≤ (s + 2))).trans
    simpa only [pow_one] using pow_le_pow_right₀
      (show (1 : ℝ) ≤ p + (s + 2) by have := Nat.cast_nonneg (α := ℝ) s; linarith)
      (show 1 ≤ s + 2 by omega)
  have hdim : (Fintype.card (AdaptedBasisIndex (fun _ : σ => 1) ω) : ℝ) ≤ q :=
    (Nat.cast_le.mpr (adaptedBasisIndex_card_le (fun _ : σ => 1) ω s (by simp)
      (F.adaptedBasis_weight_le_step b ω hF))).trans
        (symbol_dimension_bound_le_power s (Fintype.card ι) (Fintype.card σ) hp hι hσ)
  have hfinal : (q + D) ^ D ≤ (p + C) ^ C := by
    simpa [B, Q, q, Polynomial.eval₂_pow] using hbound p hp
  have hdata := hgrid (F.adaptedMonomialBasis b ω hF (fun _ : σ => 1)) H q
    (F.adaptedPolynomialFiltration (fun _ : σ => 1)).lowerCentralSeries_eq_bot
    hH hq hdim (hHp.trans (Real.exp_le_exp.mpr hpq))
    (F.adaptedMonomialBasis_bracket_height b ω hF (fun _ => 1) hH hc)
    l hl (hlp.trans (Real.exp_le_exp.mpr hpq))
  obtain ⟨m, hm, hmp, hlm, hlog, had⟩ := hdata
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr hfinal), hlm, ?_, ?_⟩
  · intro x hx h
    have hout := hlog (F.realAdaptedPolynomialJet (fun i => (h i : ℚ)) x)
      (by simpa only [F.realAdaptedPolynomialJet_base, RealAdaptedCoefficientGrid,
        Basis.equivFun_apply] using hx)
      (by simpa only [F.realAdaptedPolynomialJet_tangent, RealAdaptedCoefficientGrid,
        Basis.equivFun_apply] using F.realAdaptedDirectionalDerivative_grid b ω hF l x hx h)
    simpa only [RealAdaptedCoefficientGrid, Basis.equivFun_apply, realAdaptedLogDerivative] using hout
  · intro g x hg hx
    have hout := had g x
      (by simpa only [RealAdaptedCoefficientGrid, Basis.equivFun_apply] using hg)
      (by simpa only [RealAdaptedCoefficientGrid, Basis.equivFun_apply] using hx)
    simpa only [RealAdaptedCoefficientGrid, Basis.equivFun_apply] using hout

theorem realAdaptedAdjoint_tensor {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (w : σ → ℕ)
    (g : F.RealAdaptedPolynomialGroup w) (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :
    F.realAdaptedPolynomialTensor w (dualAdjoint g x) =
      dualAdjoint (F.realAdaptedPolynomialGroupHom w g) (F.realAdaptedPolynomialTensor w x) := by
  let φ := F.realAdaptedPolynomialTensor w
  exact dualLinearLift_adjoint (F.realification.adaptedPolynomialFiltration w).lowerCentralSeries_eq_bot
    (⊤ : LieIdeal ℚ (ℝ ⊗[ℚ] F.adaptedLieSubalgebra w)) φ φ.toLinearMap
    (fun u v _ => φ.map_lie u v) g x (by trivial)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_formal_polynomial_operation_grid (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (_hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        (∀ A : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot,
          A.coord ∈ F.realification.adaptedLieSubalgebra (fun _ => 1) →
          CoefficientGrid (b.baseChange ℝ) l A.coord →
          ∀ i : σ, CoefficientGrid (b.baseChange ℝ) m (formalLogDerivative i A)) ∧
        (∀ (A : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
          (Q : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)),
          A.coord ∈ F.realification.adaptedLieSubalgebra (fun _ => 1) →
          Q ∈ F.realification.adaptedLieSubalgebra (fun _ => 1) →
          CoefficientGrid (b.baseChange ℝ) l A.coord →
          CoefficientGrid (b.baseChange ℝ) l Q →
          CoefficientGrid (b.baseChange ℝ) m (dualAdjoint A Q)) := by
  obtain ⟨C, hC, hgrid⟩ := exists_real_adapted_dual_grid s
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hF H p hH hp hι hσ hHp hc l hl hlp
  classical
  obtain ⟨m, hm, hmp, hlm, hlog, had⟩ := hgrid F b ω hF H p hH hp hι hσ hHp hc l hl hlp
  refine ⟨m, hm, hmp, hlm, ?_, ?_⟩
  · intro A hA hAgrid i
    obtain ⟨x, hx⟩ := F.exists_real_adapted_representation b ω hF (fun _ : σ => 1) A.coord hA
    have hxgrid : F.RealAdaptedCoefficientGrid b ω hF (fun _ : σ => 1) l x := by
      apply (F.realAdaptedCoefficientGrid_iff_formal b ω hF _ l x).mpr
      rwa [hx]
    have hout := (F.realAdaptedCoefficientGrid_iff_formal b ω hF _ m _).mp
      (hlog x hxgrid (Pi.single i 1))
    have hsingle : (fun j => ((Pi.single i 1 : σ → ℤ) j : ℚ)) = Pi.single i 1 := by
      funext j
      by_cases hj : j = i <;> simp [hj]
    rw [hsingle, F.realAdaptedLogDerivative_eq_formal, hx] at hout
    exact hout
  · intro A Q hA hQ hAgrid hQgrid
    obtain ⟨x, hx⟩ := F.exists_real_adapted_representation b ω hF (fun _ : σ => 1) A.coord hA
    obtain ⟨y, hy⟩ := F.exists_real_adapted_representation b ω hF (fun _ : σ => 1) Q hQ
    let G : F.RealAdaptedPolynomialGroup (fun _ : σ => 1) := ⟨x⟩
    have hG : F.realFullPolynomialHom (fun _ : σ => 1) G = A := NilpotentLieBCHGroup.ext hx
    have hxgrid : F.RealAdaptedCoefficientGrid b ω hF (fun _ : σ => 1) l x := by
      apply (F.realAdaptedCoefficientGrid_iff_formal b ω hF _ l x).mpr
      rwa [hx]
    have hygrid : F.RealAdaptedCoefficientGrid b ω hF (fun _ : σ => 1) l y := by
      apply (F.realAdaptedCoefficientGrid_iff_formal b ω hF _ l y).mpr
      rwa [hy]
    have hout := (F.realAdaptedCoefficientGrid_iff_formal b ω hF _ m _).mp (had G y hxgrid hygrid)
    rw [F.realAdaptedAdjoint_eq_formal, hG, hy] at hout
    exact hout

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

end Erdos3.NilpotentLieFiltration

end

end OAI
