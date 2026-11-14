module

public import PrimeCarleson.Proof.Fplus31.C2.DescentState

/-!
# The sub-step: extrapolation, lift, freezing, sub-model, degree drop

Part of the type I / type II iteration of `C2/CMain.lean` (proof of [F+] Proposition 3.1). This file
composes

1. `ExtrapolatedSymbolFactorization` (the extrapolation step, `Symbol.lean`) of the symbol of `S.T`,
2. `exists_orbitFactors_of_extrapolated` (`Lift.lean`): the orbit-level factors with
   `K = W + [gr, gr]` explicit,
3. `exists_native_orbit_outer_control` (vendored library): the outer control of the factors,
4. `exists_frozen_local_models` and `exists_frozen_descent_models` (`Freeze.lean`, `Descent.lean`):
   the frozen niltests on the refiltered sub-model, or its top-quotient,
5. `finrank_lt_or_flag` (`DescentState.lean`): the potential,

into `exists_substep`. Its output is what the iteration consumes: for a window of base points `y`, a
period `P` and a niltest on a smaller model (`SubModelNiltest`: degree `s + 1`, the refiltered
sub-model of `K`, frequency `η ∘ incl` kept; or `NiltestData s` of degree `s` when `η` kills the top
layer of `K`) that approximates `S.T` on the cell `x ≡ y (P)`; the correlation with `f` is
pigeonholed over the cells in the iteration.
-/

@[expose] public noncomputable section

open OAI OAI.Erdos3
open scoped TensorProduct BigOperators NNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

open Module NilpotentLieFiltration VectorPolynomial RationalFilteredNilmanifold
  NilpotentLieBCHGroup

/-- **A frozen niltest on the refiltered sub-model of `K`**: the model (the vendored library's
`gradedRefiltration K` up to a finite-index sub-lattice, `filtration_eq`) and a niltest `T` on it of
complexity `b` and norm at most one, which is a vertical character of the top layer with the
frequency `η ∘ incl` of height at most `b` on the basis of the model. -/
structure SubModelNiltest {L : Type} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    (D : RationalFilteredNilmanifold L s d) (K : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (η : L →ₗ[ℚ] ℚ) (b : ℝ) where
  /-- The dimension of the sub-model. -/
  dim : ℕ
  [topology : TopologicalSpace (ℝ ⊗[ℚ] D.filtration.gradedRefiltrationSubalgebra K)]
  [topologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.filtration.gradedRefiltrationSubalgebra K)]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] D.filtration.gradedRefiltrationSubalgebra K)]
  [hausdorff : T2Space (ℝ ⊗[ℚ] D.filtration.gradedRefiltrationSubalgebra K)]
  /-- The refiltered sub-model. -/
  model : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra K) s dim
  /-- Its filtration is the refiltration of `D` by `K`. -/
  filtration_eq : model.filtration = D.filtration.gradedRefiltration K
  /-- The niltest. -/
  T : model.Niltest (fun _ : Unit => 1)
  complexity : T.ComplexityLE b
  norm_le : T.normBound ≤ 1
  eta_height : ∀ i, rationalLogHeight
    ((η.comp (D.filtration.gradedRefiltrationSubalgebra K).incl.toLinearMap) (model.basis i)) ≤ b
  vertical : ∀ z ∈ model.filtration.realification.subgroup s, ∀ x,
    T.observable (z • x) = CircleFourier.character
      ((realifyFunctional (η.comp (D.filtration.gradedRefiltrationSubalgebra K).incl.toLinearMap)
        z.coord : ℝ) : CircleFourier.Circle) * T.observable x

/-- A frozen sub-model niltest is a vertical niltest with the frequency `η ∘ incl`. -/
def SubModelNiltest.toVertical {L : Type} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    {D : RationalFilteredNilmanifold L s d}
    {K : LieSubalgebra ℚ D.filtration.AssociatedGraded} {η : L →ₗ[ℚ] ℚ} {b : ℝ}
    (V : SubModelNiltest D K η b) : VerticalNiltest s b where
  L := D.filtration.gradedRefiltrationSubalgebra K
  dim := V.dim
  topology := V.topology
  topologicalAdd := V.topologicalAdd
  continuousSMul := V.continuousSMul
  hausdorff := V.hausdorff
  D := V.model
  T := V.T
  η := η.comp (D.filtration.gradedRefiltrationSubalgebra K).incl.toLinearMap
  complexity := V.complexity
  norm_le := V.norm_le
  eta_height := V.eta_height
  vertical := V.vertical

/-- **The sub-step.** From a `LengStart` of degree `s + 1 ∈ {1, 2}` and an
`ExtrapolatedSymbolFactorization` of the symbol of its niltest at the scale `A ≥ e^{(p + C)^C}`: a
basis-graded `W` (killed by `η` on its top layer) and `K = W + [gr, gr]`, and

* (stay) a period `P` and for every base point `y` of the window `|y| ≤ A` a frozen niltest `V` on
  the refiltered sub-model of `K` (degree `s + 1`, dimension `dim K'`, frequency `η ∘ incl` kept)
  that approximates `S.T` on the cell `x ≡ y (P)`, `|x - y| ≤ A δ`;
* (drop) if `η` kills the top layer of `K`, the same with a niltest `N` of degree `s`;
* (potential) the sub-model has strictly smaller dimension, or the flag holds. -/
theorem exists_substep (s : ℕ) (hs : s ≤ 1) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {Q : Finset (Unit → ℤ)} {f : (Unit → ℤ) → ℂ} {p : ℝ}
      (S : LengStart (s + 1) Q f p) {A : ℝ}, 1 ≤ p → Real.exp ((p + C) ^ C) ≤ A →
      ExtrapolatedSymbolFactorization S.D.filtration S.D.basis S.omega S.hF S.η A
        (S.T.symbol S.D.basis S.omega S.hF) p →
      ∃ (W K : LieSubalgebra ℚ S.D.filtration.AssociatedGraded),
        BasisGradedSubmodule (S.D.filtration.associatedGradedBasis S.D.basis S.omega S.hF)
          S.omega W.toSubmodule ∧
        (∀ x ∈ W, basisGradeProjection (S.D.filtration.associatedGradedBasis S.D.basis S.omega
          S.hF) S.omega (s + 1) x = x →
          S.D.filtration.gradedFrequency S.D.basis S.omega S.hF S.η x = 0) ∧
        K.toSubmodule = W.toSubmodule ⊔ commutatorSubmodule S.D.filtration.AssociatedGraded ∧
        (∃ P : ℕ, 0 < P ∧ (P : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
          ∀ y : ℤ, |(y : ℝ)| ≤ A →
            ∃ V : SubModelNiltest S.D K S.η ((p + C) ^ C),
              ∀ (x : ℤ) (δ : ℝ), 0 ≤ δ → |(x : ℝ)| ≤ A → (P : ℤ) ∣ x - y →
                |(x : ℝ) - y| ≤ A * δ →
                ‖S.T.eval (fun _ => x) - V.toVertical.T.eval (fun _ => x)‖ ≤
                  Real.exp ((p + C) ^ C) * δ) ∧
        ((∀ x ∈ K, basisGradeProjection (S.D.filtration.associatedGradedBasis S.D.basis S.omega
            S.hF) S.omega (s + 1) x = x →
            S.D.filtration.gradedFrequency S.D.basis S.omega S.hF S.η x = 0) →
          ∃ P : ℕ, 0 < P ∧ (P : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
            ∀ y : ℤ, |(y : ℝ)| ≤ A →
              ∃ N : NiltestData s,
                N.dim ≤ finrank ℚ (S.D.filtration.gradedRefiltrationSubalgebra K) ∧
                N.T.ComplexityLE ((p + C) ^ C) ∧ N.T.normBound ≤ 1 ∧
                ∀ (x : ℤ) (δ : ℝ), 0 ≤ δ → |(x : ℝ)| ≤ A → (P : ℤ) ∣ x - y →
                  |(x : ℝ) - y| ≤ A * δ →
                  ‖S.T.eval (fun _ => x) - N.T.eval (fun _ => x)‖ ≤
                    Real.exp ((p + C) ^ C) * δ) ∧
        (finrank ℚ (S.D.filtration.gradedRefiltrationSubalgebra K) < S.dim ∨
          ∀ x y : S.D.filtration.AssociatedGraded,
            basisGradeProjection (S.D.filtration.associatedGradedBasis S.D.basis S.omega
              S.hF) S.omega 1 x = x →
            basisGradeProjection (S.D.filtration.associatedGradedBasis S.D.basis S.omega
              S.hF) S.omega 1 y = y →
            S.D.filtration.gradedFrequency S.D.basis S.omega S.hF S.η ⁅x, y⁆ = 0) := by
  obtain ⟨C₁, hC₁, hlift⟩ := exists_orbitFactors_of_extrapolated (s + 1)
  obtain ⟨c₁, hc₁, hout⟩ := exists_native_orbit_outer_control.{0, 0} (s + 1) 1
  obtain ⟨C₃, hC₃, hlocal⟩ := exists_frozen_local_models (s + 1)
  obtain ⟨C₄, hC₄, hdrop⟩ := exists_frozen_descent_models s
  let X : Polynomial ℕ := Polynomial.X
  let Y₁ : Polynomial ℕ := (X + Polynomial.C C₁) ^ C₁
  let Y₂ : Polynomial ℕ := (Y₁ + Polynomial.C c₁) ^ c₁
  let Y₃ : Polynomial ℕ := (Y₂ + Polynomial.C C₃) ^ C₃
  let Y₄ : Polynomial ℕ := (Y₂ + Polynomial.C C₄) ^ C₄
  let PF : Polynomial ℕ := (Y₂ + Y₃ + 4 + 2) ^ 4 + Y₄
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget PF
  refine ⟨C, hC, ?_⟩
  intro Q f p S A hp1 hA hX
  have hp0 : 0 ≤ p := by linarith
  have hd : S.dim = finrank ℚ S.L := by
    rw [Module.finrank_eq_card_basis S.D.basis, Fintype.card_fin]
  let p₁ := (p + C₁) ^ C₁
  let p₂ := (p₁ + c₁) ^ c₁
  let b₃ := (p₂ + C₃) ^ C₃
  let b₄ := (p₂ + C₄) ^ C₄
  let t := p₂ + b₃ + 4
  have hC₁R : (1 : ℝ) ≤ C₁ := by exact_mod_cast (by omega : 1 ≤ C₁)
  have hc₁R : (1 : ℝ) ≤ c₁ := by exact_mod_cast (by omega : 1 ≤ c₁)
  have hC₃R : (1 : ℝ) ≤ C₃ := by exact_mod_cast (by omega : 1 ≤ C₃)
  have hp₁ : p ≤ p₁ := by
    calc p ≤ p + C₁ := by linarith
      _ ≤ p₁ := le_self_pow₀ (by linarith) (by omega)
  have hp₁0 : 0 ≤ p₁ := hp0.trans hp₁
  have hp₁₂ : p₁ ≤ p₂ := by
    calc p₁ ≤ p₁ + c₁ := by linarith
      _ ≤ p₂ := le_self_pow₀ (by linarith) (by omega)
  have hp₂0 : 0 ≤ p₂ := hp₁0.trans hp₁₂
  have hb₃0 : 0 ≤ b₃ := by positivity
  have hb₄0 : 0 ≤ b₄ := by positivity
  have hp₂t : p₂ ≤ t := by dsimp [t]; linarith
  have hb₃t : b₃ ≤ t := by dsimp [t]; linarith
  have ht0 : 0 ≤ t := hp₂0.trans hp₂t
  have hbud : (t + 2) ^ 4 + b₄ ≤ (p + C) ^ C := by
    simpa [PF, Y₁, Y₂, Y₃, Y₄, X, p₁, p₂, b₃, b₄, t, Polynomial.eval₂_pow] using hbudget p hp0
  have htT : t ≤ (t + 2) ^ 4 := by
    calc t ≤ t + 2 := by linarith
      _ ≤ (t + 2) ^ 4 := le_self_pow₀ (by linarith) (by norm_num)
  have hfin : (t + 2) ^ 4 ≤ (p + C) ^ C := by linarith
  have hb₄F : b₄ ≤ (p + C) ^ C := by
    have : 0 ≤ (t + 2) ^ 4 := by positivity
    linarith
  have hpF : p₁ ≤ (p + C) ^ C := hp₁₂.trans (hp₂t.trans (htT.trans hfin))
  have hApos : 0 < A := lt_of_lt_of_le (Real.exp_pos _) hA
  have hA₁ : Real.exp p₁ ≤ A := (Real.exp_le_exp.mpr hpF).trans hA
  have hDg : S.D.GeometryComplexityLE p := S.complexity.1
  let g : (S.D.filtration.realification.adaptedPolynomialFiltration
      (fun _ : Unit => 1)).Group := ⟨⟨S.T.orbit.log, S.T.orbit.property⟩⟩
  obtain ⟨W, R, hWg, hη, hK⟩ := hlift S.D hd S.omega S.hF hp1 hDg S.η g A hA₁ hX
  have hA' : ∀ _i : Unit, 0 < (fun _ : Unit => A) _i := fun _ => hApos
  have hctrl := hout R hp₁0 (hDg.mono S.D hp₁) hA' (by simp)
  let R₂ := R.mono hp₁₂ hA'
  have hctrl₂ : R₂.HasOuterValueControl p₂ := hctrl
  have hD₂ : S.D.GeometryComplexityLE p₂ := hDg.mono S.D (hp₁.trans hp₁₂)
  have hT₂ : S.T.ComplexityLE p₂ := S.complexity.mono (hp₁.trans hp₁₂)
  have hp₂1 : 1 ≤ p₂ := hp1.trans (hp₁.trans hp₁₂)
  have hcap : ∀ x, ‖S.T.observable x‖ ≤ 1 := fun x =>
    (S.T.norm_le x).trans (by exact_mod_cast S.norm_le)
  have : Module.Finite ℚ S.L := Module.Finite.of_basis S.D.basis
  let H := S.D.filtration.gradedRefiltrationSubalgebra R₂.subalgebra
  let _ : TopologicalSpace (ℝ ⊗[ℚ] H) := moduleTopology ℝ _
  let _ : IsTopologicalAddGroup (ℝ ⊗[ℚ] H) := IsModuleTopology.isTopologicalAddGroup ℝ _
  let _ : T2Space (ℝ ⊗[ℚ] H) := realification_moduleTopology_t2 (Module.finBasis ℚ H)
  have hK₂ : R₂.subalgebra.toSubmodule =
      W.toSubmodule ⊔ commutatorSubmodule S.D.filtration.AssociatedGraded := hK
  obtain ⟨P, hP, hPb, hmod⟩ := hlocal S.T R₂ hp₂1 hD₂ hT₂ hApos hctrl₂ hcap
  refine ⟨W, R₂.subalgebra, hWg, hη, hK₂, ⟨P, hP, hPb.trans (Real.exp_le_exp.mpr
    ((hb₃t.trans htT).trans hfin)), ?_⟩, ?_, ?_⟩
  · intro y hy
    obtain ⟨M, hM⟩ := hmod y hy
    have hq4 : (t + 2) ^ 4 ≤ (p + C) ^ C := hfin
    refine ⟨{
      dim := finrank ℚ H
      model := M.model
      filtration_eq := M.filtration_eq
      T := M.pullTest S.T hcap
      complexity := (M.pullTest_complexity S.T hcap hp₂0 hb₃0 hT₂).mono (htT.trans hfin)
      norm_le := le_rfl
      eta_height := fun i => (frozen_eta_height M S.η ht0 (hDg.1.trans
        (hp₁.trans (hp₁₂.trans hp₂t))) (fun j => (S.eta_height j).trans
          (hp₁.trans (hp₁₂.trans hp₂t))) (fun j k => (M.inclusion_height j k).trans hb₃t) i).trans
          hq4
      vertical := frozenMiddleRealization_pullTest_vertical M S.T hcap S.η S.vertical }, ?_⟩
    intro x δ hδ hx hdvd hnear
    exact (hM x δ hδ hx hdvd hnear).trans (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr ((hb₃t.trans htT).trans hfin)) hδ)
  · intro hkill
    have hzero := S.D.filtration.real_frequency_zero_on_refiltered_top S.D.basis S.omega S.hF
      R₂.subalgebra S.η hkill
    have hinv : ∀ z : S.D.RealGroup,
        z.coord ∈ S.D.filtration.realGradedRefiltrationLayer R₂.subalgebra (s + 1) →
        ∀ x, S.T.observable (z • x) = S.T.observable x := by
      intro z hz x
      have hz' : z ∈ S.D.filtration.realification.subgroup (s + 1) :=
        S.D.filtration.realGradedRefiltrationLayer_le R₂.subalgebra (s + 1) hz
      rw [S.vertical z hz' x, hzero z.coord hz]
      simp
    obtain ⟨P', hP', hP'b, hdesc⟩ := hdrop S.T R₂ hp₂1 hD₂ hT₂ hApos hctrl₂ hinv
    refine ⟨P', hP', hP'b.trans (Real.exp_le_exp.mpr hb₄F), fun y hy => ?_⟩
    obtain ⟨N, hNdim, hNc, hNn, hNcell⟩ := hdesc y hy
    exact ⟨N, hNdim, hNc.mono hb₄F, hNn.le.trans S.norm_le, fun x δ hδ hx hdvd hnear =>
      (hNcell x δ hδ hx hdvd hnear).trans (mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr hb₄F) hδ)⟩
  · rcases finrank_lt_or_flag S.D.filtration S.D.basis S.omega S.hF (by omega : 1 ≤ s + 1)
      (by omega : s + 1 ≤ 2) S.η hWg hη hK₂ with h | h
    · exact Or.inl (lt_of_lt_of_eq h hd.symm)
    · exact Or.inr h

end PrimeCarleson.Proof.Fplus31
