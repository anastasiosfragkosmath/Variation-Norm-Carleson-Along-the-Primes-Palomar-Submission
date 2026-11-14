module

public import PrimeCarleson.Proof.Fplus31.C2.Lift
public import OAI.Combinatorics.Progressions.Estimates.NativeFrozenComparison
public import OAI.Combinatorics.Progressions.Estimates.NativeOrbitOuterControl
public import OAI.Combinatorics.Progressions.Estimates.NativeOrbitFreezing
public import OAI.Combinatorics.Progressions.Estimates.NativeSharedFrozenCorrelations
public import OAI.Combinatorics.Progressions.Estimates.AntisymmetricPartitionApproximation

/-!
# The sub-step, freezing: local models on the refiltered sub-model

Part of the type I / type II iteration of `C2/CMain.lean` (proof of [F+] Proposition 3.1). From the
orbit-level factors `R` of `Lift.lean` (slow, middle, rational and a lattice constant, with the
middle factor in the refiltered subgroup of `K = R.subalgebra`) the vendored library freezes the
slow and the rational factors at a base point `y`: with `a = slowValue y` and `r = rationalValue y`,
the niltest `T` is approximated on the cell `{x ≡ y (P), |x - y| ≤ A δ}` by
`x ↦ T.observable (a · middle (x) · r)`, which is a niltest on the finite-index sub-lattice model
`M.model` of the refiltered nilmanifold `gradedRefiltrationSubalgebra K` (the vendored library's
`FrozenMiddleRealization`).

* `exists_frozen_comparison`: the period `P` and the cell estimate
  `‖T.eval x - T.observable (mk (a · middle x · r))‖ ≤ e^b δ`;
* `exists_frozen_local_models`: for every base point `y` with `|y| ≤ A`, a
  `FrozenMiddleRealization` `M` whose pulled-back niltest `M.pullTest T` approximates `T` on the
  cell;
* `frozenMiddleRealization_pullTest_vertical`: if `T` is a vertical character of the top layer with
  frequency `η`, then `M.pullTest T` is one with frequency `η ∘ incl` (the frequency is kept, so the
  flag of the iteration can be tracked);
* `frozen_eta_height`: the height of `η ∘ incl` on the basis of the sub-model.

The base point `y` ranges over `|y| ≤ A`, the scale of the symbol factorization; a translation of
the orbit (`Niltest.translate`, which preserves the symbol) re-centers the window.
-/

@[expose] public noncomputable section

open OAI OAI.Erdos3
open scoped TensorProduct BigOperators NNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

open Module NilpotentLieFiltration VectorPolynomial RationalFilteredNilmanifold
  NilpotentLieBCHGroup

/-- **The cell estimate.**  There is a period `P ≤ e^b` such that for `x ≡ y (P)` in `[-A, A]` with
`|x - y| ≤ A δ`, `T.eval x` is within `e^b δ` of `T.observable (a · middle (x) · r)`, where
`a = slowValue y` and `r = rationalValue y` are the factors frozen at `y`. -/
theorem exists_frozen_comparison (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
      {D : RationalFilteredNilmanifold L s d} (T : D.Niltest (fun _ : Unit => 1)) {A p : ℝ}
      {η₀ : L →ₗ[ℚ] ℚ}
      (R : NativePolynomialOrbitFactors D ⟨⟨T.orbit.log, T.orbit.property⟩⟩ η₀
        (fun _ : Unit => A) p),
      1 ≤ p → D.GeometryComplexityLE p → T.ComplexityLE p → 0 < A →
      ∃ P : ℕ, 0 < P ∧ (P : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∀ (y x : ℤ) (δ : ℝ), 0 ≤ δ → |(y : ℝ)| ≤ A → |(x : ℝ)| ≤ A → (P : ℤ) ∣ x - y →
          |(x : ℝ) - y| ≤ A * δ →
          ‖T.eval (fun _ => x) - T.observable (QuotientGroup.mk
              (R.frozenMiddleValue (R.slowValue fun _ => y) (R.rationalValue fun _ => y)
                fun _ => x))‖ ≤ Real.exp ((p + C) ^ C) * δ := by
  obtain ⟨c₃, _, hlocal⟩ := exists_native_orbit_local_control.{0, 0} s
  let X : Polynomial ℕ := Polynomial.X
  let U₃ : Polynomial ℕ := (X + Polynomial.C c₃) ^ c₃
  let P₀ : Polynomial ℕ := X + U₃
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P₀
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d D T A p η₀ R hp1 hD hT hA
  have hp0 : 0 ≤ p := by linarith
  have hA' : ∀ _i : Unit, 0 < (fun _ : Unit => A) _i := fun _ => hA
  obtain ⟨P, hP, hPb, hperiod, hmotion⟩ := hlocal R hp0 hD (by simpa using hp1) hA'
  have hsum : p + (p + c₃) ^ c₃ ≤ (p + C) ^ C := by
    simpa [P₀, X, U₃, Polynomial.eval₂_pow] using hbudget p hp0
  have hu3 : 0 ≤ (p + c₃) ^ c₃ := by positivity
  have hb₃ : (p + c₃) ^ c₃ ≤ (p + C) ^ C := by linarith
  refine ⟨P, hP, hPb.trans (Real.exp_le_exp.mpr hb₃), ?_⟩
  intro y x δ hδ hy hx hdvd hnear
  have hy' : ∀ i : Unit, |(((fun _ : Unit => y) i : ℤ) : ℝ)| ≤ (fun _ : Unit => A) i := fun _ => hy
  have hxs : ∀ i : Unit, |(((fun _ : Unit => x) i : ℤ) : ℝ)| ≤ (fun _ : Unit => A) i :=
    fun _ => hx
  have hnear' : ∀ i : Unit, |(((fun _ : Unit => x) i : ℤ) : ℝ) -
      (((fun _ : Unit => y) i : ℤ) : ℝ)| ≤ (fun _ : Unit => A) i * δ := fun _ => hnear
  have hdvd' : ∀ i : Unit, (P : ℤ) ∣ (fun _ : Unit => x) i - (fun _ : Unit => y) i :=
    fun _ => hdvd
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  have hdist := hmotion (fun _ => x) (fun _ => y) δ hδ hxs hy' hnear'
  have hcoset := (hperiod (fun _ => x) (fun _ => y) hdvd').1
  let ax := R.slowValue (fun _ : Unit => x)
  let ay := R.slowValue (fun _ : Unit => y)
  let bx := D.filtration.adaptedPolynomialRealValueHom (fun _ : Unit => 1)
    (fun i => (((fun _ : Unit => x) i : ℤ) : ℝ)) R.middle
  let rx := R.rationalValue (fun _ : Unit => x)
  let ry := R.rationalValue (fun _ : Unit => y)
  have hTeval : T.eval (fun _ => x) = T.observable (QuotientGroup.mk (ax * bx * rx)) :=
    R.eval_niltest T rfl (fun _ => x)
  have h1 := D.observable_frozen_right_eq T.observable ax bx rx ry hcoset
  have h2 := D.frozen_observable_change_left T.observable T.lipschitz ax ay bx ry
  have hlip : (T.lipBound : ℝ) ≤ Real.exp p := by
    have h := T.observable_budget hT
    linarith [T.normBound.coe_nonneg]
  change ‖T.eval (fun _ => x) - T.observable (QuotientGroup.mk (ay * bx * ry))‖ ≤ _
  rw [hTeval, h1]
  refine h2.trans ?_
  calc (T.lipBound : ℝ) * dist ax ay
      ≤ Real.exp p * (Real.exp ((p + c₃) ^ c₃) * δ) :=
        mul_le_mul hlip hdist dist_nonneg (Real.exp_pos p).le
    _ = Real.exp (p + (p + c₃) ^ c₃) * δ := by rw [← mul_assoc, ← Real.exp_add]
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hsum) hδ

/-- **The local models of the frozen sub-step.** With the outer control of `R`
(`HasOuterValueControl p`, the values of the slow factor are bounded and those of the rational
factor lie in a grid, which the vendored library derives for any `R` at the budget `(p + C)^C`),
every base point `y` has a `FrozenMiddleRealization` whose pulled-back niltest approximates `T` on
the cell. -/
theorem exists_frozen_local_models (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
      {D : RationalFilteredNilmanifold L s d} (T : D.Niltest (fun _ : Unit => 1)) {A p : ℝ}
      {η₀ : L →ₗ[ℚ] ℚ}
      (R : NativePolynomialOrbitFactors D ⟨⟨T.orbit.log, T.orbit.property⟩⟩ η₀
        (fun _ : Unit => A) p)
      [TopologicalSpace (ℝ ⊗[ℚ] D.filtration.gradedRefiltrationSubalgebra R.subalgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.filtration.gradedRefiltrationSubalgebra R.subalgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.filtration.gradedRefiltrationSubalgebra R.subalgebra)]
      [T2Space (ℝ ⊗[ℚ] D.filtration.gradedRefiltrationSubalgebra R.subalgebra)],
      1 ≤ p → D.GeometryComplexityLE p → T.ComplexityLE p → 0 < A → R.HasOuterValueControl p →
      ∀ hcap : (∀ x, ‖T.observable x‖ ≤ 1),
      ∃ P : ℕ, 0 < P ∧ (P : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∀ y : ℤ, |(y : ℝ)| ≤ A →
          ∃ M : R.FrozenMiddleRealization (R.slowValue fun _ => y) (R.rationalValue fun _ => y)
              ((p + C) ^ C),
            ∀ (x : ℤ) (δ : ℝ), 0 ≤ δ → |(x : ℝ)| ≤ A → (P : ℤ) ∣ x - y →
              |(x : ℝ) - y| ≤ A * δ →
              ‖T.eval (fun _ => x) - (M.pullTest T hcap).eval (fun _ => x)‖ ≤
                Real.exp ((p + C) ^ C) * δ := by
  obtain ⟨c₂, _, hfrozen⟩ := exists_native_frozen_middle_realization.{0, 0} s
  obtain ⟨c₅, _, hcmp⟩ := exists_frozen_comparison s
  let X : Polynomial ℕ := Polynomial.X
  let U₂ : Polynomial ℕ := (X + Polynomial.C c₂) ^ c₂
  let U₅ : Polynomial ℕ := (X + Polynomial.C c₅) ^ c₅
  let P₀ : Polynomial ℕ := X + U₅ + U₂
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P₀
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d D T A p η₀ R _ _ _ _ hp1 hD hT hA hctrl hcap
  have hp0 : 0 ≤ p := by linarith
  obtain ⟨m, hm, hmb, hrat, hslow⟩ := hctrl
  obtain ⟨P, hP, hPb, hcell⟩ := hcmp T R hp1 hD hT hA
  have hsum : p + (p + c₅) ^ c₅ + (p + c₂) ^ c₂ ≤ (p + C) ^ C := by
    simpa [P₀, X, U₂, U₅, Polynomial.eval₂_pow] using hbudget p hp0
  have hu5 : 0 ≤ (p + c₅) ^ c₅ := by positivity
  have hu2 : 0 ≤ (p + c₂) ^ c₂ := by positivity
  have hb₅ : (p + c₅) ^ c₅ ≤ (p + C) ^ C := by linarith
  have hb₂ : (p + c₂) ^ c₂ ≤ (p + C) ^ C := by linarith
  refine ⟨P, hP, hPb.trans (Real.exp_le_exp.mpr hb₅), ?_⟩
  intro y hy
  have hy' : ∀ i : Unit, |(((fun _ : Unit => y) i : ℤ) : ℝ)| ≤ (fun _ : Unit => A) i := fun _ => hy
  obtain ⟨M⟩ := hfrozen D R hp0 hD m hm hmb (R.slowValue fun _ => y)
    (R.rationalValue fun _ => y) (hslow _ hy') (hrat _)
  refine ⟨M.mono hb₂, ?_⟩
  intro x δ hδ hx hdvd hnear
  have hpull : ((M.mono hb₂).pullTest T hcap).eval (fun _ => x) =
      T.observable (QuotientGroup.mk (R.frozenMiddleValue (R.slowValue fun _ => y)
        (R.rationalValue fun _ => y) fun _ => x)) :=
    (M.mono hb₂).pullTest_eval T hcap (fun _ => x)
  rw [hpull]
  exact (hcell y x δ hδ hy hx hdvd hnear).trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hb₅) hδ)

section Vertical

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d}
  {g : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : Unit => 1)).Group}
  {η₀ : L →ₗ[ℚ] ℚ} {A : Unit → ℝ} {p : ℝ}
  {R : NativePolynomialOrbitFactors D g η₀ A p}
  [TopologicalSpace (ℝ ⊗[ℚ] D.filtration.gradedRefiltrationSubalgebra R.subalgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.filtration.gradedRefiltrationSubalgebra R.subalgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.filtration.gradedRefiltrationSubalgebra R.subalgebra)]
  [T2Space (ℝ ⊗[ℚ] D.filtration.gradedRefiltrationSubalgebra R.subalgebra)]
  {a r : D.RealGroup} {b : ℝ} (M : R.FrozenMiddleRealization a r b)

/-- **The frozen niltest is vertical.**  If `T` is a vertical character of the top layer with
frequency `η`, the pulled-back niltest on the refiltered model is a vertical character of its top
layer with frequency `η ∘ incl`. -/
theorem frozenMiddleRealization_pullTest_vertical (T : D.Niltest (fun _ : Unit => 1))
    (hcap : ∀ x, ‖T.observable x‖ ≤ 1) (η : L →ₗ[ℚ] ℚ)
    (hvert : ∀ z ∈ D.filtration.realification.subgroup s, ∀ x,
      T.observable (z • x) =
        CircleFourier.character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) *
          T.observable x) :
    ∀ z ∈ M.model.filtration.realification.subgroup s, ∀ x,
      (M.pullTest T hcap).observable (z • x) =
        CircleFourier.character
          ((realifyFunctional (η.comp (D.filtration.gradedRefiltrationSubalgebra
            R.subalgebra).incl.toLinearMap) z.coord : ℝ) : CircleFourier.Circle) *
          (M.pullTest T hcap).observable x := by
  intro z hz x
  have hφz : (realificationMap (hnil := M.model.filtration.lowerCentralSeries_eq_bot)
      (hM := D.filtration.lowerCentralSeries_eq_bot)
      (D.filtration.gradedRefiltrationSubalgebra R.subalgebra).incl z) ∈
        D.filtration.realification.subgroup s :=
    D.filtration.realGradedRefiltrationLayer_le R.subalgebra s (M.inclusion_mem_top z hz)
  change T.observable (M.spaceMap (z • x)) = _ * T.observable (M.spaceMap x)
  rw [M.spaceMap_top_smul z hz x, hvert _ hφz, realifyFunctional_comp]
  rfl

/-- **The height of the frequency on the sub-model.**  If `η` has height `≤ q` on the basis of `D`
and the basis of the sub-model has height `≤ q` in the basis of `D`, then `η ∘ incl` has height
`≤ (q + 2)^4` on the basis of the sub-model. -/
theorem frozen_eta_height (η : L →ₗ[ℚ] ℚ) {q : ℝ} (hq : 0 ≤ q) (hd : (d : ℝ) ≤ q)
    (hη : ∀ i, rationalLogHeight (η (D.basis i)) ≤ q)
    (hinc : ∀ i j, rationalLogHeight (D.basis.repr (M.model.basis i : L) j) ≤ q) (i) :
    rationalLogHeight ((η.comp (D.filtration.gradedRefiltrationSubalgebra
      R.subalgebra).incl.toLinearMap) (M.model.basis i)) ≤ (q + 2) ^ 4 := by
  have h := linearMap_coordinate_logHeight D.basis (Module.Basis.singleton Unit ℚ) η hq
    (by simpa using hd) (fun i j => by simpa using hη i) (M.model.basis i : L) (hinc i) ()
  simpa using h

end Vertical

end PrimeCarleson.Proof.Fplus31
