/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Nilpotent/NativeSquareNiltest.lean
Changes: Lean module/public-import conversion; unneeded declarations and imports were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.NativeSquareOrbit
public import OAI.Combinatorics.Progressions.Estimates.NormalizedCommonFamily
public import OAI.Combinatorics.Progressions.Dynamics.ComparisonEquivalenceBudget
public import OAI.Combinatorics.Progressions.Geometry.RealifiedSquareMetric
public import OAI.Combinatorics.Progressions.Linear.NativeRankQuotientOrbit
@[expose] public section

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup CircleFourier
open scoped TensorProduct NNReal

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s m : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (Γ : Subgroup F.Group)
  [TopologicalSpace (ℝ ⊗[ℚ] F.squareLieSubalgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] F.squareLieSubalgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] F.squareLieSubalgebra)]
  [T2Space (ℝ ⊗[ℚ] F.squareLieSubalgebra)]
  [TopologicalSpace (ℝ ⊗[ℚ] (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)))]
  [T2Space (ℝ ⊗[ℚ] (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)))]

theorem exists_square_quotient_niltest_with_orbit
    (b : Basis (Fin m) ℚ F.squareLieSubalgebra) (v : Fin m → ℕ)
    (hlayers : ∀ j, F.squareFiltration.layer j = Submodule.span ℚ (b '' {i | j ≤ v i}))
    (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates b (F.squareLattice Γ))
    (hout : bchSubgroupCoordinates b (F.squareLattice Γ) ⊆ denominatorGrid N)
    (w : σ → ℕ) (q : F.squareFiltration.realification.PolynomialOrbit w)
    (ε : F.realification.Group) (u : F.realification.Group ⧸ Γ.map realificationHom → ℂ)
    (χ : F.realification.Group → CircleFourier.Circle)
    (hu : ∀ z ∈ F.realification.subgroup (s + 1), ∀ x, u (z • x) = character (χ z) * u x)
    (A B : ℝ≥0)
    (hLip : letI := realificationQuotientMetricSpace b (F.squareLattice Γ) N hN hout
      LipschitzWith A (F.realSquareObservable Γ ε u))
    (hb : ∀ x, ‖u x‖ ≤ B) :
    let D := F.squareFiltration.topQuotientModel b v hlayers (F.squareLattice Γ) N hN hin hout
    ∀ H : ℕ, 1 ≤ H →
      (∀ i j, RationalHeightLE (D.basis.repr
        (lieQuotientMap (F.squareFiltration.layerIdeal (s + 1)) (b j)) i) H) →
      (∀ i j k, RationalHeightLE (lieStructureConstants D.basis i j k) H) →
    ∃ T : D.Niltest w,
      T.orbit = F.squareFiltration.realQuotientPolynomialOrbit
        (F.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl q ∧
      (∀ z : F.squareFiltration.realification.Group,
        T.observable (QuotientGroup.mk (F.squareFiltration.realQuotientStepHom
          (F.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl z)) =
          F.realSquareObservable Γ ε u (QuotientGroup.mk z)) ∧
      T.normBound = B ^ 2 ∧
      T.lipBound = rationalReconstructionLipschitzBound s m
        (Fintype.card {i : Fin m // ¬ s + 1 ≤ v i}) H A (B ^ 2) ∧
      ∀ x : σ → ℤ, T.eval x = F.realSquareObservable Γ ε u
        (QuotientGroup.mk (F.squareFiltration.realification.polynomialOrbitEval w x q)) := by
  dsimp only
  intro H hH he hc
  let D := F.squareFiltration.topQuotientModel b v hlayers (F.squareLattice Γ) N hN hin hout
  obtain ⟨f, hf, hfLip, hfBound⟩ := F.exists_lipschitz_realSquare_descent Γ
    b D.basis N N H hN hN hH hout D.outer_grid he hc ε u χ hu A B hLip hb
  let K := rationalReconstructionLipschitzBound s m
    (Fintype.card {i : Fin m // ¬ s + 1 ≤ v i}) H A (B ^ 2)
  let T : D.Niltest w := {
    orbit := F.squareFiltration.realQuotientPolynomialOrbit
      (F.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl q
    observable := f
    normBound := B ^ 2
    lipBound := K
    norm_le := fun x => by simpa only [NNReal.coe_pow] using hfBound x
    lipschitz := by
      let : MetricSpace (F.squareFiltration.quotientTop.realification.Group ⧸
          ((F.squareLattice Γ).map (F.squareFiltration.quotientStepHom
            (F.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl)).map realificationHom) :=
        realificationQuotientMetricSpace D.basis _ N hN D.outer_grid
      exact hfLip.weaken (by simp only [Fintype.card_fin, K]; exact le_rfl) }
  refine ⟨T, rfl, hf, rfl, rfl, ?_⟩
  intro x
  change f (QuotientGroup.mk ((F.squareFiltration.quotientTop.realification.polynomialOrbitEval w x)
    (F.squareFiltration.realQuotientPolynomialOrbit
      (F.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl q))) = _
  exact (congrArg (fun g : F.squareFiltration.quotientTop.realification.Group =>
      f (QuotientGroup.mk g))
    (F.squareFiltration.realQuotientPolynomialOrbit_eval
      (F.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl q x)).trans (hf _)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration NilpotentLieBCHGroup CircleFourier
open scoped TensorProduct NNReal

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d)
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
  [T2Space (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
  [TopologicalSpace (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1)))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1)))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1)))]
  [T2Space (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1)))]

theorem exists_uniform_square_niltest_with_budget {w : σ → ℕ} (T : D.Niltest w)
    {p : ℝ} (hp : 0 ≤ p) (hT : T.ComplexityLE p) (a b c : ℕ)
    (hrec : ∀ (m n H : ℕ) (ℓ B : ℝ≥0) (r : ℝ),
      0 ≤ r → (m : ℝ) ≤ r → (n : ℝ) ≤ r → (H : ℝ) ≤ Real.exp r →
      (ℓ : ℝ) ≤ Real.exp r → (B : ℝ) ≤ Real.exp r →
      (rationalReconstructionLipschitzBound s m n H ℓ B : ℝ) ≤ Real.exp ((r + c) ^ c)) :
    ∃ (e : Basis (Fin (finrank ℚ L)) ℚ L) (ω : Fin (finrank ℚ L) → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
      (N : ℕ) (hN : 0 < N)
      (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates
        (D.filtration.squareFinBasis e ω (hF 2)) (D.filtration.squareLattice D.lattice))
      (hout : bchSubgroupCoordinates (D.filtration.squareFinBasis e ω (hF 2))
        (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N),
      (∀ i j, rationalLogHeight (D.basis.repr (e i) j) ≤ p + 1) ∧
      let Q := D.filtration.squareFiltration.topQuotientModel
        (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
        (D.filtration.squareFinBasis_layers e ω hF)
        (D.filtration.squareLattice D.lattice) N hN hin hout
      Q.GeometryComplexityLE (squareGeometryBudget p) ∧
      ∀ (ε : D.RealGroup) (q : D.filtration.squareFiltration.realification.PolynomialOrbit w)
        (χ : D.RealGroup → CircleFourier.Circle),
        (∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x,
          T.observable (z • x) = character (χ z) * T.observable x) →
        ∀ (A : ℝ≥0), (A : ℝ) ≤ Real.exp (normalizedSquareLeftBudget a b p) →
        (letI := D.metricSpace; LipschitzWith A (fun x : D.Space => ε • x)) →
      ∃ S : Q.Niltest w,
        S.orbit = D.filtration.squareFiltration.realQuotientPolynomialOrbit
          (D.filtration.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl q ∧
        (∀ z : D.filtration.squareFiltration.realification.Group,
          S.observable (QuotientGroup.mk (D.filtration.squareFiltration.realQuotientStepHom
            (D.filtration.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl z)) =
            D.filtration.realSquareObservable D.lattice ε T.observable (QuotientGroup.mk z)) ∧
        S.normBound = T.normBound ^ 2 ∧
        S.ComplexityLE (normalizedSquareComplexityBudget a b c p) ∧
        ∀ x : σ → ℤ, S.eval x = D.filtration.realSquareObservable D.lattice ε T.observable
          (QuotientGroup.mk (D.filtration.squareFiltration.realification.polynomialOrbitEval w x q)) := by
  obtain ⟨b₀, v₀, hlayers, N, hN, hin, hout, hb₀, hgeom, hgeomQ⟩ :=
    D.exists_controlled_reduced_square_geometry hp hT.1
  let m := Fintype.card (Fin (finrank ℚ L) ⊕ {i // 2 ≤ v₀ i})
  let bs : Basis (Fin m) ℚ D.filtration.squareLieSubalgebra := D.filtration.squareFinBasis b₀ v₀ (hlayers 2)
  let v : Fin m → ℕ := squareFinWeight v₀
  have hls := D.filtration.squareFinBasis_layers b₀ v₀ hlayers
  let Q := D.filtration.squareFiltration.topQuotientModel bs v hls
    (D.filtration.squareLattice D.lattice) N hN hin hout
  refine ⟨b₀, v₀, hlayers, N, hN, hin, hout, hb₀, hgeomQ, ?_⟩
  intro ε q χ hvert A hA hALip
  have hQ : Q.GeometryComplexityLE (squareGeometryBudget p) := hgeomQ
  have hm : (m : ℝ) ≤ squareGeometryBudget p := hgeom.1
  have hQ0 := squareGeometryBudget_nonneg hp
  have hObs0 := normalizedSquareObservableBudget_nonneg a b hp
  have hB : (T.normBound : ℝ) ≤ Real.exp p := by
    have hh := T.observable_budget hT
    linarith [T.lipBound.coe_nonneg]
  have hK : (T.lipBound : ℝ) ≤ Real.exp p := by
    have hh := T.observable_budget hT
    linarith [T.normBound.coe_nonneg]
  let Hproj := ⌈Real.exp (p + 1)⌉₊
  have hproj := D.filtration.squareFinBasis_projection_height D.basis b₀ v₀ (hlayers 2)
    (one_le_ceil_exp (p + 1)) (fun i j => rationalHeightLE_ceil_exp (hb₀ j i))
  let P := coordinateLipschitzBound (Fintype.card (Fin d)) (Fintype.card (Fin m)) Hproj
  have hP : (P : ℝ) ≤ Real.exp (normalizedSquareProjectionBudget p) := by
    have heq : normalizedSquareProjectionBudget p = (squareGeometryBudget p + p + 2 + 2) ^ 2 := by
      unfold normalizedSquareProjectionBudget
      ring
    rw [heq]
    apply coordinateLipschitzBound_le_exp _ _ Hproj
      (show 0 ≤ squareGeometryBudget p + p + 2 by linarith)
    · simpa only [Fintype.card_fin] using hT.1.1.trans (by linarith : p ≤ squareGeometryBudget p + p + 2)
    · simpa only [Fintype.card_fin] using hm.trans (by linarith : squareGeometryBudget p ≤ squareGeometryBudget p + p + 2)
    · exact (ceil_exp_le_exp_add_one (by linarith : 0 ≤ p + 1)).trans
        (Real.exp_le_exp.mpr (by linarith))
  let ℓ := T.normBound * (T.lipBound * P) + T.normBound * (T.lipBound * (A * P))
  have hℓLip : letI := realificationQuotientMetricSpace bs (D.filtration.squareLattice D.lattice) N hN hout
      LipschitzWith ℓ (D.filtration.realSquareObservable D.lattice ε T.observable) :=
    D.filtration.realSquareObservable_lipschitz D.basis bs D.lattice D.grid N Hproj D.grid_pos hN
      D.outer_grid hout (fun k i => (hproj i k).1) (fun k i => (hproj i k).2)
      ε T.observable A T.lipBound T.normBound hALip T.lipschitz T.norm_le
  have hℓ : (ℓ : ℝ) ≤ Real.exp (normalizedSquareObservableBudget a b p) :=
    squareObservableLipschitz_le_exp A T.normBound T.lipBound P
      (normalizedSquareLeftBudget_nonneg a b hp) hA hB hK hP
  let H := ⌈Real.exp (squareGeometryBudget p)⌉₊
  have he (i j) : RationalHeightLE (Q.basis.repr
      (lieQuotientMap (D.filtration.squareFiltration.layerIdeal (s + 1)) (bs j)) i) H := by
    exact (quotientFinBasis_projection_height bs
      (D.filtration.squareFiltration.layerIdeal (s + 1)) {i | s + 1 ≤ v i}
      (hls (s + 1)) j i).mono (one_le_ceil_exp _)
  obtain ⟨S, hOrbit, hObs, hSB, hSK, hSval⟩ := D.filtration.exists_square_quotient_niltest_with_orbit D.lattice
    bs v hls N hN hin hout w q ε T.observable χ hvert ℓ T.normBound hℓLip T.norm_le
    H (one_le_ceil_exp _) he (fun i j k => rationalHeightLE_ceil_exp (hQ.2.2.1 i j k))
  let r := normalizedSquareReconstructionBudget a b p
  have hr : 0 ≤ r := normalizedSquareReconstructionBudget_nonneg a b hp
  have hQr : squareGeometryBudget p + 1 ≤ r := by dsimp [r, normalizedSquareReconstructionBudget]; linarith
  have hUr : normalizedSquareObservableBudget a b p ≤ r := by dsimp [r, normalizedSquareReconstructionBudget]; linarith
  have hpr : 2 * p ≤ r := by dsimp [r, normalizedSquareReconstructionBudget]; linarith
  have hB2 : (((T.normBound ^ 2 : ℝ≥0) : ℝ)) ≤ Real.exp (2 * p) := by
    rw [NNReal.coe_pow]
    calc
      _ ≤ (Real.exp p) ^ 2 := pow_le_pow_left₀ T.normBound.coe_nonneg hB 2
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hSKBound : (S.lipBound : ℝ) ≤ Real.exp ((r + c) ^ c) := by
    rw [hSK]
    apply hrec _ _ H ℓ (T.normBound ^ 2) r hr
    · exact hm.trans (by linarith)
    · exact hQ.1.trans (by linarith)
    · exact (ceil_exp_le_exp_add_one hQ0).trans (Real.exp_le_exp.mpr hQr)
    · exact hℓ.trans (Real.exp_le_exp.mpr hUr)
    · exact hB2.trans (Real.exp_le_exp.mpr hpr)
  have hSBBound : (S.normBound : ℝ) ≤ Real.exp (2 * p) := by rw [hSB]; exact hB2
  have hlog := niltest_log_bound_of_exp S.normBound S.lipBound
    (by linarith : 0 ≤ 2 * p) (by positivity : 0 ≤ (r + c) ^ c) hSBBound hSKBound
  refine ⟨S, hOrbit, hObs, hSB, ?_, hSval⟩
  constructor
  · apply hQ.mono
    change squareGeometryBudget p ≤ squareGeometryBudget p + 2 * p + (r + c) ^ c + 4
    have hpow : 0 ≤ (r + c) ^ c := by positivity
    linarith
  · apply hlog.trans
    change 2 * p + (r + c) ^ c + 4 ≤ squareGeometryBudget p + 2 * p + (r + c) ^ c + 4
    linarith

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration NilpotentLieBCHGroup CircleFourier
open scoped TensorProduct NNReal

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration NilpotentLieBCHGroup CircleFourier
open scoped TensorProduct NNReal

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open Module NilpotentLieFiltration NilpotentLieBCHGroup VectorPolynomial CircleFourier
open scoped TensorProduct NNReal

universe uσ uι uL

end Erdos3

end

end OAI
