module

public import PrimeCarleson.Proof.Fplus31.C2.Freeze
public import OAI.Combinatorics.Progressions.Estimates.UniformFrozenDescent
public import OAI.Combinatorics.Progressions.Estimates.UnconditionalStepDrop

/-!
# The sub-step, degree drop: the top-invariant descents

Part of the type I / type II iteration of `C2/CMain.lean` (proof of [F+] Proposition 3.1). The
degree drops in two situations, and in both the descent is the vendored library's
`exists_uniform_frozen_descent`, which descends to a finite-index sub-lattice of the model.

* `NiltestData deg`: a one-variable niltest on a model of degree `deg`, with its instances (the
  input form of the start step `exists_leng_start_or_top_invariant` and the state of the iteration
  at the degree drop);
* `exists_topInvariant_descent`: the **zero-frequency branch**. A niltest invariant under the top
  layer (the second disjunct of the start step) descends to degree `deg - 1`, same values,
  `a = r = 1`;
* `exists_frozen_descent_models`: after the extrapolation, if the frequency `η` kills the top layer
  of `K` (the observable is invariant under the refiltered top layer), the frozen niltests of
  `Freeze.lean` descend to degree `s`: for every base point `y` of the window a niltest `N.T` of
  degree `s` and dimension `≤ dim K'` that approximates `T` on the cell `x ≡ y (P)`.
-/

@[expose] public noncomputable section

open OAI OAI.Erdos3
open scoped TensorProduct BigOperators NNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

open Module NilpotentLieFiltration VectorPolynomial RationalFilteredNilmanifold
  NilpotentLieBCHGroup

/-- A one-variable niltest on a rational filtered nilmanifold of degree `deg`, with the
instances of the topology of `ℝ ⊗ L`. -/
structure NiltestData (deg : ℕ) where
  L : Type
  [lie : LieRing L]
  [algebra : LieAlgebra ℚ L]
  dim : ℕ
  [topology : TopologicalSpace (ℝ ⊗[ℚ] L)]
  [topologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
  [hausdorff : T2Space (ℝ ⊗[ℚ] L)]
  D : RationalFilteredNilmanifold L deg dim
  T : D.Niltest (fun _ : Unit => 1)

attribute [instance] NiltestData.lie NiltestData.algebra NiltestData.topology
  NiltestData.topologicalAdd NiltestData.continuousSMul NiltestData.hausdorff

/-- **The zero-frequency branch** (the second disjunct of the start step,
`exists_leng_start_or_top_invariant`): a niltest on a model of degree `s + 1` that is invariant
under the top layer descends to a niltest on a model of degree `s` and dimension `≤ d`, with the
same values (the vendored library's `exists_uniform_frozen_descent` with `a = r = 1`, `E = D`,
`φ = id`, which descends to a finite-index sub-lattice).
-/
theorem exists_topInvariant_descent (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
      (D : RationalFilteredNilmanifold L (s + 1) d) (T : D.Niltest (fun _ : Unit => 1)) {p : ℝ},
      0 ≤ p → T.ComplexityLE p →
      (∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x,
        T.observable (z • x) = T.observable x) →
      ∃ N : NiltestData s, N.dim ≤ d ∧ N.T.ComplexityLE ((p + C) ^ C) ∧
        N.T.normBound = T.normBound ∧ ∀ x, N.T.eval x = T.eval x := by
  obtain ⟨C, hC, hdesc⟩ := exists_uniform_frozen_descent.{0, 0, 0} s 1
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d D T p hp hT hinv
  obtain ⟨Λ, -, -, -, -, -, n, hn, Q, hQF, hQL, hQ, hfam⟩ :=
    hdesc D D (LieHom.id : L →ₗ⁅ℚ⁆ L) T T.orbit hp hT.1 hT
      (fun i j => rationalLogHeight_repr_basis_le D.basis hp j i) 1 one_pos
      (by simpa using Real.one_le_exp hp)
  let _ := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1)))
  let _ : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1))) :=
    IsModuleTopology.isTopologicalAddGroup ℝ _
  let _ := realification_moduleTopology_t2 Q.basis
  obtain ⟨S, hSo, hSn, hSc, hSe⟩ := hfam 1 1 (fun i => by simp [Real.exp_nonneg])
    ⟨0, by funext i; simp⟩
    (fun z hz x => by
      simp only [one_mul, mul_one, realificationMap_id_apply]
      exact hinv z hz (QuotientGroup.mk x))
  refine ⟨{ L := L ⧸ D.filtration.layerIdeal (s + 1), dim := n, D := Q, T := S }, hn, hSc,
    hSn, fun x => ?_⟩
  change S.eval x = T.eval x
  rw [hSe x]
  simp only [one_mul, mul_one, realificationMap_id_apply]
  rfl

/-- **The frozen descent models** (the degree drop when `η` kills the top layer of `K`). If `T` is
invariant under the top layer of the refiltered subgroup of `K = R.subalgebra` (which holds when `T`
is a vertical character with a frequency killing that layer), the frozen niltests descend to the
degree `s`: for every base point `y` there is a niltest `N.T` on a model of degree `s` and dimension
`≤ dim K'` (`K' = gradedRefiltrationSubalgebra K`) that approximates `T` on the cell. -/
theorem exists_frozen_descent_models (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
      {D : RationalFilteredNilmanifold L (s + 1) d} (T : D.Niltest (fun _ : Unit => 1))
      {A p : ℝ} {η₀ : L →ₗ[ℚ] ℚ}
      (R : NativePolynomialOrbitFactors D ⟨⟨T.orbit.log, T.orbit.property⟩⟩ η₀
        (fun _ : Unit => A) p),
      1 ≤ p → D.GeometryComplexityLE p → T.ComplexityLE p → 0 < A → R.HasOuterValueControl p →
      (∀ z : D.RealGroup, z.coord ∈ D.filtration.realGradedRefiltrationLayer R.subalgebra (s + 1) →
        ∀ x, T.observable (z • x) = T.observable x) →
      ∃ P : ℕ, 0 < P ∧ (P : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∀ y : ℤ, |(y : ℝ)| ≤ A →
          ∃ N : NiltestData s,
            N.dim ≤ finrank ℚ (D.filtration.gradedRefiltrationSubalgebra R.subalgebra) ∧
            N.T.ComplexityLE ((p + C) ^ C) ∧ N.T.normBound = T.normBound ∧
            ∀ (x : ℤ) (δ : ℝ), 0 ≤ δ → |(x : ℝ)| ≤ A → (P : ℤ) ∣ x - y →
              |(x : ℝ) - y| ≤ A * δ →
              ‖T.eval (fun _ => x) - N.T.eval (fun _ => x)‖ ≤ Real.exp ((p + C) ^ C) * δ := by
  obtain ⟨B, _, hmodel⟩ := exists_native_middle_model.{0, 0}
  obtain ⟨K, _, hdesc⟩ := exists_uniform_frozen_descent.{0, 0, 0} s 1
  obtain ⟨c₅, _, hcmp⟩ := exists_frozen_comparison (s + 1)
  let X : Polynomial ℕ := Polynomial.X
  let U₀ : Polynomial ℕ := X + (X + Polynomial.C B) ^ B + 4
  let U₆ : Polynomial ℕ := (U₀ + Polynomial.C K) ^ K
  let U₅ : Polynomial ℕ := (X + Polynomial.C c₅) ^ c₅
  let P₀ : Polynomial ℕ := U₆ + U₅
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P₀
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d D T A p η₀ R hp1 hD hT hA hctrl hinv
  have hp0 : 0 ≤ p := by linarith
  obtain ⟨m, hm, hmb, hrat, hslow⟩ := hctrl
  obtain ⟨P, hP, hPb, hcell⟩ := hcmp T R hp1 hD hT hA
  obtain ⟨E, hEF, _hEL, hE, hinc, h, hh⟩ := hmodel D R hp0 hD
  let _ : TopologicalSpace (ℝ ⊗[ℚ] D.filtration.gradedRefiltrationSubalgebra R.subalgebra) :=
    moduleTopology ℝ _
  let _ : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.filtration.gradedRefiltrationSubalgebra R.subalgebra) :=
    IsModuleTopology.isTopologicalAddGroup ℝ _
  let _ := realification_moduleTopology_t2 E.basis
  let t := p + (p + B) ^ B + 4
  have hu0 : 0 ≤ (p + B) ^ B := by positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpt : p ≤ t := by dsimp [t]; linarith
  have hEt : (p + B) ^ B ≤ t := by dsimp [t]; linarith
  have hsum : (t + K) ^ K + (p + c₅) ^ c₅ ≤ (p + C) ^ C := by
    simpa [P₀, U₆, U₀, U₅, X, t, Polynomial.eval₂_pow] using hbudget p hp0
  have hcost : (t + K) ^ K ≤ (p + C) ^ C := by
    have : 0 ≤ (p + c₅) ^ c₅ := by positivity
    linarith
  have hb₅ : (p + c₅) ^ c₅ ≤ (p + C) ^ C := by
    have : 0 ≤ (t + K) ^ K := by positivity
    linarith
  obtain ⟨_Λ, _hΛ, _hchar, _hnormal, _hfinite, _hindex, n, hn, Q, hQF, _hQL, _hQ, hfamily⟩ :=
    hdesc E D (D.filtration.gradedRefiltrationSubalgebra R.subalgebra).incl T h ht
      (hE.mono E hEt) (hT.mono hpt) (fun i j => (hinc j i).trans hEt)
      m hm (hmb.trans (Real.exp_le_exp.mpr hpt))
  refine ⟨P, hP, hPb.trans (Real.exp_le_exp.mpr hb₅), ?_⟩
  intro y hy
  have hy' : ∀ i : Unit, |(((fun _ : Unit => y) i : ℤ) : ℝ)| ≤ (fun _ : Unit => A) i := fun _ => hy
  let _ : TopologicalSpace (ℝ ⊗[ℚ]
      (D.filtration.gradedRefiltrationSubalgebra R.subalgebra ⧸
        E.filtration.layerIdeal (s + 1))) := moduleTopology ℝ _
  let _ : IsTopologicalAddGroup (ℝ ⊗[ℚ]
      (D.filtration.gradedRefiltrationSubalgebra R.subalgebra ⧸
        E.filtration.layerIdeal (s + 1))) := IsModuleTopology.isTopologicalAddGroup ℝ _
  let _ := realification_moduleTopology_t2 Q.basis
  have ha' : ∀ i, |(D.basis.baseChange ℝ).repr (R.slowValue fun _ => y).coord i| ≤
      Real.exp ((t + 2) ^ 1) :=
    fun i => (hslow _ hy' i).trans (Real.exp_le_exp.mpr (by simp only [pow_one]; linarith))
  obtain ⟨S, _hSo, hSn, hSc, hSe⟩ := hfamily (R.slowValue fun _ => y) (R.rationalValue fun _ => y)
    ha' (hrat _)
    (D.frozen_refiltered_top_invariant R.subalgebra E hEF T.observable hinv _ _)
  refine ⟨{ L := D.filtration.gradedRefiltrationSubalgebra R.subalgebra ⧸
      E.filtration.layerIdeal (s + 1), dim := n, D := Q, T := S }, hn, hSc.mono hcost, hSn, ?_⟩
  intro x δ hδ hx hdvd hnear
  have hSx : S.eval (fun _ => x) = T.observable (QuotientGroup.mk
      (R.frozenMiddleValue (R.slowValue fun _ => y) (R.rationalValue fun _ => y) fun _ => x)) :=
    (hSe _).trans (congrArg (fun z : D.RealGroup => T.observable (QuotientGroup.mk
      (R.slowValue (fun _ => y) * z * R.rationalValue fun _ => y))) (hh _))
  change ‖T.eval (fun _ => x) - S.eval (fun _ => x)‖ ≤ _
  rw [hSx]
  exact (hcell y x δ hδ hy hx hdvd hnear).trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hb₅) hδ)

end PrimeCarleson.Proof.Fplus31
