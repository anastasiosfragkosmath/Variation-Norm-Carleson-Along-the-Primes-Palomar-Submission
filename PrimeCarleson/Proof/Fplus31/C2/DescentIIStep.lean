module

public import PrimeCarleson.Proof.Fplus31.C2.DescentStep
public import PrimeCarleson.Proof.Fplus31.C2.LiftII

/-!
# The sub-step, type II (extrapolation, lift, freezing, sub-model, degree drop)

Part of the type I / type II iteration of `C2/CMain.lean` (proof of [F+] Proposition 3.1). The type
II analogue of `exists_substep` (`DescentStep.lean`). The input is an
`ExtrapolatedSymbolFactorizationII` of the symbol of the niltest of a `LengStart` (the output of
`type_two_extrapolation`, `type_two_extrapolation_of_C3`); it carries the common kernel `K = K⁰` of
the product `gr × gr` in place of `K = W + [gr, gr]`, and the clauses on `η` that the descending
stage needs in place of the exposed `W`. The composition is that of `DescentStep.lean`:

1. `exists_orbitFactors_of_extrapolatedII` (`LiftII.lean`): the orbit-level factors with
   `subalgebra = K`;
2. `exists_native_orbit_outer_control` (vendored library), `exists_frozen_local_models` and
   `exists_frozen_descent_models` (`Freeze.lean`, `Descent.lean`, which are stated for any
   `NativePolynomialOrbitFactors` and are reused as they are);
3. the potential: if every weight-one element of `gr` lies in `K` the flag `η [x, y] = 0` holds by
   the flag clause of `K`, otherwise the refiltered sub-model has strictly smaller dimension
   (`finrank_gradedRefiltrationSubalgebra_lt`).

`exists_substep_typeII` has the shape of `exists_substep`, with `W` and `K = W + [gr, gr]`
replaced by `K`, `[gr, gr] ≤ K`, `η [K, K] = 0` and the conditional top-kill clause.

-/

@[expose] public noncomputable section

open OAI OAI.Erdos3
open scoped TensorProduct BigOperators NNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

open Module NilpotentLieFiltration VectorPolynomial RationalFilteredNilmanifold
  NilpotentLieBCHGroup

/-- **The sub-step, type II.** From a `LengStart` of degree `s + 1 ∈ {1, 2}` and an
`ExtrapolatedSymbolFactorizationII` of the symbol of its niltest at the scale `A ≥ e^{(p + C)^C}`:
the common kernel `K = K⁰` (basis-graded, containing `[gr, gr]`, with `η [K, K] = 0` and, if `η`
kills `[gr, gr]`, `η` killing the top layer of `K`), and

* (stay) a period `P` and for every base point `y` of the window `|y| ≤ A` a frozen niltest `V` on
  the refiltered sub-model of `K` (degree `s + 1`, dimension `dim K'`, frequency `η ∘ incl` kept)
  that approximates `S.T` on the cell `x ≡ y (P)`, `|x - y| ≤ A δ`;
* (drop) if `η` kills the top layer of `K`, the same with a niltest `N` of degree `s`;
* (potential) the sub-model has strictly smaller dimension, or the flag holds. -/
theorem exists_substep_typeII (s : ℕ) (_hs : s ≤ 1) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {Q : Finset (Unit → ℤ)} {f : (Unit → ℤ) → ℂ} {p : ℝ}
      (S : LengStart (s + 1) Q f p) {A : ℝ}, 1 ≤ p → Real.exp ((p + C) ^ C) ≤ A →
      ExtrapolatedSymbolFactorizationII S.D.filtration S.D.basis S.omega S.hF S.η A
        (S.T.symbol S.D.basis S.omega S.hF) p →
      ∃ K : LieSubalgebra ℚ S.D.filtration.AssociatedGraded,
        BasisGradedSubmodule (S.D.filtration.associatedGradedBasis S.D.basis S.omega S.hF)
          S.omega K.toSubmodule ∧
        commutatorSubmodule S.D.filtration.AssociatedGraded ≤ K.toSubmodule ∧
        (∀ x ∈ K, ∀ y ∈ K,
          S.D.filtration.gradedFrequency S.D.basis S.omega S.hF S.η ⁅x, y⁆ = 0) ∧
        ((∀ z ∈ commutatorSubmodule S.D.filtration.AssociatedGraded,
            S.D.filtration.gradedFrequency S.D.basis S.omega S.hF S.η z = 0) →
          ∀ x ∈ K, basisGradeProjection (S.D.filtration.associatedGradedBasis S.D.basis S.omega
            S.hF) S.omega (s + 1) x = x →
            S.D.filtration.gradedFrequency S.D.basis S.omega S.hF S.η x = 0) ∧
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
  obtain ⟨C₁, hC₁, hlift⟩ := exists_orbitFactors_of_extrapolatedII (s + 1)
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
  obtain ⟨R, hKg, hcomm, hflag, htop⟩ := hlift S.D hd S.omega S.hF hp1 hDg S.η g A hA₁ hX
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
  obtain ⟨P, hP, hPb, hmod⟩ := hlocal S.T R₂ hp₂1 hD₂ hT₂ hApos hctrl₂ hcap
  refine ⟨R₂.subalgebra, hKg, hcomm, hflag, htop, ⟨P, hP, hPb.trans (Real.exp_le_exp.mpr
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
  · by_cases hall : ∀ x, basisGradeProjection (S.D.filtration.associatedGradedBasis S.D.basis
        S.omega S.hF) S.omega 1 x = x → x ∈ R₂.subalgebra
    · exact Or.inr fun x y hx hy => hflag x (hall x hx) y (hall y hy)
    · push Not at hall
      exact Or.inl (lt_of_lt_of_eq (finrank_gradedRefiltrationSubalgebra_lt S.D.filtration
        S.D.basis S.omega S.hF R₂.subalgebra hall) hd.symm)

end PrimeCarleson.Proof.Fplus31
