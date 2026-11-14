/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/NativeOrbitFreezing.lean
Changes: Lean module/public-import conversion; unneeded declarations and imports were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.NativeOrbitOuterControl
public import OAI.Combinatorics.Progressions.Polynomial.UniformPolynomialPeriodBudget
@[expose] public section

namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct

theorem polynomialRationalGrid_uniform_cosets {σ L : Type*} [Fintype σ]
    [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    (D : RationalFilteredNilmanifold L s d) (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (q : ℕ) (hq : 0 < q)
    (g : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
    (hg : D.filtration.PolynomialRationalGrid D.basis w q g) (x y : σ → ℤ)
    (hxy : ∀ j, (uniformPolynomialBCHPeriod (σ := σ) D.basis s s D.grid q : ℤ) ∣ x j - y j) :
    let f := fun z : σ → ℤ => D.filtration.adaptedPolynomialRealValueHom w (fun j => (z j : ℝ)) g
    ((QuotientGroup.mk (f x) : D.Space) = QuotientGroup.mk (f y)) ∧
    ((QuotientGroup.mk (f x)⁻¹ : D.Space) = QuotientGroup.mk (f y)⁻¹) := by
  obtain ⟨P, hdegree, hden, hval⟩ :=
    D.filtration.polynomialRationalGrid_exists_coordinates D.basis w hw q hq g hg
  dsimp only
  rw [← hval (fun j => (x j : ℝ)), ← hval (fun j => (y j : ℝ))]
  exact realPolynomialBCHMap_uniform_cosets D.basis D.filtration.lowerCentralSeries_eq_bot
    D.lattice s D.grid q P hdegree hden D.inner_grid x y hxy

theorem exists_native_rational_period (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) (w : σ → ℕ),
      (∀ i, 0 < w i) → ∀ (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p →
      (Fintype.card σ : ℝ) ≤ p → ∀ (q : ℕ), 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ M : ℕ, 0 < M ∧ (M : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∀ g : (D.filtration.realification.adaptedPolynomialFiltration w).Group,
          D.filtration.PolynomialRationalGrid D.basis w q g →
          let f := fun z : σ → ℤ => D.filtration.adaptedPolynomialRealValueHom w (fun j => (z j : ℝ)) g
          ∀ x y : σ → ℤ, (∀ j, (M : ℤ) ∣ x j - y j) →
            ((QuotientGroup.mk (f x) : D.Space) = QuotientGroup.mk (f y)) ∧
            ((QuotientGroup.mk (f x)⁻¹ : D.Space) = QuotientGroup.mk (f y)⁻¹) := by
  obtain ⟨a, _, hperiod⟩ := exists_uniformPolynomialBCHPeriod_exp_bound s s
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((Polynomial.X + 1 + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ d D w hw p hp hD hσ q hq hqp
  let M := uniformPolynomialBCHPeriod (σ := σ) D.basis s s D.grid q
  have hpp : p ≤ p + 1 := le_add_of_nonneg_right zero_le_one
  have hb := hperiod (σ := σ) D.basis D.grid ⌈Real.exp p⌉₊ q (p + 1)
    (by linarith) (by simpa only [Fintype.card_fin] using hD.1.trans hpp) (hσ.trans hpp)
    (ceil_exp_le_exp_add_one hp) (hD.2.1.trans (Real.exp_le_exp.mpr hpp))
    (hqp.trans (Real.exp_le_exp.mpr hpp))
    (fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k))
  have hMb : (M : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    apply hb.trans (Real.exp_le_exp.mpr _)
    simpa [Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨M, uniformPolynomialBCHPeriod_pos D.basis s s D.grid q D.grid_pos hq, hMb,
    fun g hg x y hxy => D.polynomialRationalGrid_uniform_cosets w hw q hq g hg x y hxy⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open NilpotentLieBCHGroup
open scoped TensorProduct

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open NilpotentLieBCHGroup
open scoped TensorProduct

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3

open VectorPolynomial
open scoped TensorProduct

namespace NilpotentLieFiltration

theorem polynomialOrbitCoordinates_realValue {σ L : Type*}
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ} (F : NilpotentLieFiltration L s)
    (w : σ → ℕ) (g : F.realification.PolynomialOrbit w) (x : σ → ℤ) :
    F.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ))
        (F.realification.polynomialOrbitCoordinates w g) =
      F.realification.polynomialOrbitEval w x g := by
  apply NilpotentLieBCHGroup.ext
  change eval₂ (fun i => (x i : ℝ)) g.log = eval (fun i => (x i : ℚ)) g.log
  simpa only [map_intCast] using
    (eval₂_algebraMap (S := ℝ) (fun i => (x i : ℚ)) g.log)

end NilpotentLieFiltration

namespace RationalFilteredNilmanifold

theorem exists_native_orbit_rational_period (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) (w : σ → ℕ),
      (∀ i, 0 < w i) → ∀ (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p →
      (Fintype.card σ : ℝ) ≤ p → ∀ (q : ℕ), 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ M : ℕ, 0 < M ∧ (M : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∀ g : D.filtration.realification.PolynomialOrbit w,
          CoefficientGrid (D.basis.baseChange ℝ) q g.log →
          ∀ x y : σ → ℤ, (∀ j, (M : ℤ) ∣ x j - y j) →
            ((QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w x g) : D.Space) =
              QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w y g)) ∧
            ((QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w x g)⁻¹ : D.Space) =
              QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w y g)⁻¹) := by
  obtain ⟨C, hC, hperiod⟩ := exists_native_rational_period s
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ d D w hw p hp hD hσ q hq hqp
  obtain ⟨M, hM, hMp, hsolve⟩ := hperiod D w hw p hp hD hσ q hq hqp
  refine ⟨M, hM, hMp, ?_⟩
  intro g hg x y hxy
  have hgrid := (D.filtration.polynomialRationalGrid_iff_formal D.basis w q
    (D.filtration.realification.polynomialOrbitCoordinates w g)).mpr hg
  have h := hsolve (D.filtration.realification.polynomialOrbitCoordinates w g) hgrid x y hxy
  simpa only [D.filtration.polynomialOrbitCoordinates_realValue] using h

end RationalFilteredNilmanifold
end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_native_orbit_local_control (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
      {D : RationalFilteredNilmanifold L s d}
      {g : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group}
      {eta : L →ₗ[ℚ] ℚ} {A : σ → ℝ} {p : ℝ}
      (R : NativePolynomialOrbitFactors D g eta A p),
      0 ≤ p → D.GeometryComplexityLE p → (Fintype.card σ : ℝ) ≤ p → (∀ i, 0 < A i) →
      ∃ P : ℕ, 0 < P ∧ (P : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        (∀ x y : σ → ℤ, (∀ i, (P : ℤ) ∣ x i - y i) →
          ((QuotientGroup.mk (R.rationalValue x) : D.Space) = QuotientGroup.mk (R.rationalValue y)) ∧
          ((QuotientGroup.mk (R.rationalValue x)⁻¹ : D.Space) = QuotientGroup.mk (R.rationalValue y)⁻¹)) ∧
        (letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
          (D.basis.baseChange ℝ)
         ∀ (x y : σ → ℤ) (δ : ℝ), 0 ≤ δ →
           (∀ i, |(x i : ℝ)| ≤ A i) → (∀ i, |(y i : ℝ)| ≤ A i) →
           (∀ i, |(x i : ℝ) - (y i : ℝ)| ≤ A i * δ) →
           dist (R.slowValue x) (R.slowValue y) ≤ Real.exp ((p + C) ^ C) * δ) := by
  obtain ⟨a, _, hcoeff⟩ := exists_native_orbit_coefficient_control
  obtain ⟨b, _, hperiod⟩ := exists_native_rational_period s
  obtain ⟨c, _, hmetric⟩ := exists_polynomialSlowBound_dist_exp s 1
  let X : Polynomial ℕ := Polynomial.X
  let Q := X + (X + Polynomial.C a) ^ a + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((Q + Polynomial.C b) ^ b + (Q + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ _ _ _ d D g eta A p R hp hD hσ hA
  obtain ⟨m, hm, hmb, hgrid, hslow⟩ := hcoeff R hp hD hA
  let q := p + (p + a) ^ a + 2
  have hpow : 0 ≤ (p + a) ^ a := by positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have haq : (p + a) ^ a ≤ q := by dsimp [q]; linarith
  have hsum : (q + b) ^ b + (q + c) ^ c ≤ (p + C) ^ C := by
    simpa [Q, X, q, Polynomial.eval₂_pow] using hbudget p hp
  have hbC : (q + b) ^ b ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (by positivity)).trans hsum
  have hcC : (q + c) ^ c ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left (by positivity)).trans hsum
  obtain ⟨P, hP, hPb, hcosets⟩ := hperiod D (fun _ : σ => 1) (fun _ => Nat.zero_lt_one)
    q hq (hD.mono D hpq) (hσ.trans hpq) m hm (hmb.trans (Real.exp_le_exp.mpr haq))
  refine ⟨P, hP, hPb.trans (Real.exp_le_exp.mpr hbC), hcosets R.rational hgrid, ?_⟩
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  intro x y δ hδ hx hy hxy
  have hs := D.filtration.polynomialSlowBound_mono D.basis (fun _ : σ => 1) A hA
    (Real.exp_le_exp.mpr (by simp only [pow_one]; linarith : (p + a) ^ a ≤ (q + 2) ^ 1))
    R.slow hslow
  have hd := hmetric D (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) q hq (hD.mono D hpq)
    (hσ.trans hpq) A hA R.slow hs (fun i => (x i : ℝ)) (fun i => (y i : ℝ)) δ hδ hx hy hxy
  exact hd.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hcC) hδ)

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_orbit_factor_freezing (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) (w : σ → ℕ),
      (∀ i, 0 < w i) → ∀ (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p →
      (Fintype.card σ : ℝ) ≤ p →
      ∀ (Φ : D.Space → ℂ) (K : ℝ≥0), (∀ x, ‖Φ x‖ ≤ 1) →
      (letI := D.metricSpace; LipschitzWith K Φ) → (K : ℝ) ≤ Real.exp p →
      ∀ ε b γ g : D.filtration.realification.PolynomialOrbit w,
        ε * b * γ = g → ∀ T : σ → ℝ, (∀ i, 0 < T i) →
        CoefficientBound (D.basis.baseChange ℝ) T (Real.exp ((p + 2) ^ a)) ε.log →
        ∀ (x y : σ → ℤ) (δ : ℝ), 0 ≤ δ →
        (∀ i, |(x i : ℝ)| ≤ T i) → (∀ i, |(y i : ℝ)| ≤ T i) →
        (∀ i, |(x i : ℝ) - y i| ≤ T i * δ) →
        (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w x γ) : D.Space) =
          QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w y γ) →
        ‖Φ (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w x g)) -
          Φ (QuotientGroup.mk
            (D.filtration.realification.polynomialOrbitEval w y ε *
             D.filtration.realification.polynomialOrbitEval w x b *
             D.filtration.realification.polynomialOrbitEval w y γ))‖ ≤
          Real.exp ((p + C) ^ C) * δ := by
  obtain ⟨c, _, hmove⟩ := exists_polynomialSlowBound_dist_exp s a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (Polynomial.X + (Polynomial.X + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ _ _ _ d D w hw p hp hD hσ Φ K hΦ hLip hK ε b γ g hprod T hT hε x y δ hδ hx hy hxy hγ
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  let S : D.Niltest w := {
    orbit := g
    observable := Φ
    normBound := 1
    lipBound := K
    norm_le := hΦ
    lipschitz := hLip }
  have hslow := (D.filtration.polynomialSlowBound_iff_formal D.basis w T _
    (D.filtration.realification.polynomialOrbitCoordinates w ε)).mpr hε
  have hdist := hmove D w hw p hp hD hσ T hT
    (D.filtration.realification.polynomialOrbitCoordinates w ε) hslow
    (fun i => (x i : ℝ)) (fun i => (y i : ℝ)) δ hδ hx hy hxy
  simp only [D.filtration.polynomialOrbitCoordinates_realValue] at hdist
  have hfreeze := S.observable_freeze_factors
    (D.filtration.realification.polynomialOrbitEval w x ε)
    (D.filtration.realification.polynomialOrbitEval w y ε)
    (D.filtration.realification.polynomialOrbitEval w x b)
    (D.filtration.realification.polynomialOrbitEval w x γ)
    (D.filtration.realification.polynomialOrbitEval w y γ) hγ
  have hg : D.filtration.realification.polynomialOrbitEval w x g =
      D.filtration.realification.polynomialOrbitEval w x ε *
      D.filtration.realification.polynomialOrbitEval w x b *
      D.filtration.realification.polynomialOrbitEval w x γ := by
    rw [← hprod, map_mul, map_mul]
  rw [hg]
  apply hfreeze.trans
  have hcost : p + (p + c) ^ c ≤ (p + C) ^ C := by
    simpa [Polynomial.eval₂_pow] using hbudget p hp
  calc
    _ ≤ Real.exp p * (Real.exp ((p + c) ^ c) * δ) :=
      mul_le_mul hK hdist dist_nonneg (Real.exp_pos p).le
    _ = Real.exp (p + (p + c) ^ c) * δ := by rw [← mul_assoc, ← Real.exp_add]
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hcost) hδ

end Erdos3.RationalFilteredNilmanifold

end

end OAI
