/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/ControlledProductReconstruction.lean
Changes: Lean module/public-import conversion; unneeded declarations and imports were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Dynamics.FiniteProductBudget
public import OAI.Combinatorics.Progressions.Dynamics.ImageReconstructionLogBudget
public import OAI.Combinatorics.Progressions.Dynamics.NativeHorizontalLiftBudget
public import OAI.Combinatorics.Progressions.Dynamics.ReconstructionConstantBudget
public import OAI.Combinatorics.Progressions.Nilpotent.FactorwiseBCHCovers
@[expose] public section

namespace OAI

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {α : Type*} {M : α → Type*} [∀ a, LieRing (M a)]
  [∀ a, LieAlgebra ℚ (M a)]
  {L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem realification_liePiEval_liePiMap (φ : ∀ a, L →ₗ⁅ℚ⁆ M a)
    (x : ℝ ⊗[ℚ] L) (a : α) :
    realificationLieHom (liePiEval a) (realificationLieHom (liePiMap φ) x) =
      realificationLieHom (φ a) x := by
  induction x using TensorProduct.inductionOn with
  | tmul r x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

variable [Fintype α] {κ : α → Type*}

theorem realification_pi_basis_repr (f : ∀ a, Basis (κ a) ℚ (M a))
    (x : ℝ ⊗[ℚ] (∀ a, M a)) (a : α) (i : κ a) :
    ((Pi.basis f).baseChange ℝ).repr x ⟨a, i⟩ =
      ((f a).baseChange ℝ).repr (realificationLieHom (liePiEval a) x) i := by
  induction x using TensorProduct.inductionOn with
  | tmul r x => simp only [realificationLieHom_tmul, Basis.baseChange_repr_tmul,
      Pi.basis_repr, liePiEval_apply]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped NNReal TensorProduct

theorem exists_controlled_rational_image_reconstruction (s : ℕ) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ {ι κ L M : Type*} [Fintype ι] [Fintype κ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      (hL : LieModule.lowerCentralSeries ℚ L L s = ⊥)
      (hM : LieModule.lowerCentralSeries ℚ M M s = ⊥)
    (e : Basis ι ℚ L) (f : Basis κ ℚ M) (φ : L →ₗ⁅ℚ⁆ M)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hL))
    (Λ : Subgroup (NilpotentLieBCHGroup M s hM))
    (l m H : ℕ) (hl : 0 < l) (hm : 0 < m) (_hH : 1 ≤ H)
    (hΓ : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l)
    (_hΛin : scaledIntegerGrid m ⊆ bchSubgroupCoordinates f Λ)
    (hΛout : bchSubgroupCoordinates f Λ ⊆ denominatorGrid m)
    (_hcL : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H)
    (_hcM : ∀ i j k, RationalHeightLE (lieStructureConstants f i j k) H)
    (_hφ : ∀ i j, RationalHeightLE (f.repr (φ (e j)) i) H)
    (_hcover : Λ.map realificationHom ⊓ (realificationMap (hnil := hL) (hM := hM) φ).range ≤
      (Γ.map realificationHom).map (realificationMap (hnil := hL) (hM := hM) φ))
    (u : (NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hL) ⧸
      Γ.map realificationHom) → ℂ)
    (_hker : ∀ k ∈ (realificationMap (hnil := hL) (hM := hM) φ).ker, ∀ x,
      u (QuotientGroup.mk (k * x)) = u (QuotientGroup.mk x))
    (ℓ B : ℝ≥0)
    (_hu : letI := realificationQuotientMetricSpace e Γ l hl hΓ; LipschitzWith ℓ u)
    (_hub : ∀ x, ‖u x‖ ≤ B)
    (p : ℝ) (_hp : 0 ≤ p) (_hι : (Fintype.card ι : ℝ) ≤ p) (_hκ : (Fintype.card κ : ℝ) ≤ p)
    (_hHp : (H : ℝ) ≤ Real.exp p) (_hmp : (m : ℝ) ≤ Real.exp p)
    (_hℓp : (ℓ : ℝ) ≤ Real.exp p) (_hBp : (B : ℝ) ≤ Real.exp p),
    letI := realificationQuotientMetricSpace f Λ m hm hΛout
    ∃ (v : (NilpotentLieBCHGroup (ℝ ⊗[ℚ] M) s (realification_lowerCentralSeries_eq_bot hM) ⧸
      Λ.map realificationHom) → ℂ) (K : ℝ≥0),
      (K : ℝ) ≤ Real.exp ((p + N) ^ N) ∧ LipschitzWith K v ∧ (∀ y, ‖v y‖ ≤ 2 * B) ∧
      ∀ x, v (QuotientGroup.mk (realificationMap (hnil := hL) (hM := hM) φ x)) = u (QuotientGroup.mk x) := by
  obtain ⟨C, _, hrep⟩ := exists_bounded_image_representatives s
  obtain ⟨D, _, hprod⟩ := exists_bch_triple_product_exp_bound s 1
  obtain ⟨F, _, hleft⟩ := exists_uniform_left_lipschitz_exp_bound s 1
  obtain ⟨E, _, hbox⟩ := exists_bchBoxMetricConstant_exp_bound s D
  obtain ⟨Z, _, hlog⟩ := exists_bchLogMetricConstant_exp_bound s
  obtain ⟨N, hN, hbudget⟩ := exists_generalReconstructionLogBudget_bound C D E F Z
  refine ⟨N, hN, ?_⟩
  intro ι κ L M _ _ _ _ _ _ _ _ _ _ _ _ _ _ hL hM e f φ Γ Λ l m H hl hm hH
    hΓ hΛin hΛout hcL hcM hφ hcover u hker ℓ B hu hub p hp hι hκ hHp hmp hℓp hBp

  classical
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] L) := (e.baseChange ℝ).finiteDimensional_of_finite
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] M) := (f.baseChange ℝ).finiteDimensional_of_finite
  let := rightMetricSpace (hnil := realification_lowerCentralSeries_eq_bot hL) (e.baseChange ℝ)
  let := rightMetricSpace (hnil := realification_lowerCentralSeries_eq_bot hM) (f.baseChange ℝ)
  let := rightMetricSpace_isIsometricSMul (hnil := realification_lowerCentralSeries_eq_bot hL) (e.baseChange ℝ)
  let := rightMetricSpace_isIsometricSMul (hnil := realification_lowerCentralSeries_eq_bot hM) (f.baseChange ℝ)
  let Φ := realificationMap (hnil := hL) (hM := hM) φ
  let J := Φ.range
  obtain ⟨Q, hQ, hJ⟩ := exists_realified_image_defining_matrix (hL := hL) (hM := hM) e f φ hH hφ
  let HQ : ℝ≥0 := (2 * ((Fintype.card ι + 1) * (H * rationalKernelHeight (Fintype.card κ) H) ^ Fintype.card ι) : ℕ)
  have hQabs : ∀ i j, |(Q i j : ℝ)| ≤ HQ := by
    intro i j
    change |(Q i j : ℝ)| ≤ ((2 * ((Fintype.card ι + 1) *
      (H * rationalKernelHeight (Fintype.card κ) H) ^ Fintype.card ι) : ℕ) : ℝ)
    exact (hQ i j).abs_real_le
  let R := (((p + 2) ^ 4 + C) ^ C) + (p + 2) ^ 2
  have hR : 0 ≤ R := by dsimp [R]; positivity
  let q := p + R + 1
  have hq : 0 ≤ q := by dsimp [q]; linarith
  have hpq : p ≤ q := by dsimp [q]; linarith
  let S := {g | g ∈ J ∧ ∀ i, |(f.baseChange ℝ).repr g.coord i| ≤ Real.exp R}
  have hrepS : ∀ y : CosetImage Φ (Λ.map realificationHom),
      ∃ x, projectToCosetImage Φ (Λ.map realificationHom) x = y ∧ Φ x ∈ S := by
    intro y
    obtain ⟨x, hx, hxb⟩ := hrep hL hM e f φ Λ m H p hm hΛin hcL hφ hp hι hκ hHp hmp y
    exact ⟨x, hx, ⟨⟨x, rfl⟩, hxb⟩⟩
  have hlarge {g} (hg : g ∈ S) : ∀ i, |(f.baseChange ℝ).repr g.coord i| ≤ Real.exp ((q + 2) ^ 1) := by
    intro i
    apply (hg.2 i).trans
    apply Real.exp_le_exp.mpr
    dsimp [q]
    simp only [pow_one]
    linarith
  let W : ℝ≥0 := ⟨Real.exp ((q + D) ^ D), Real.exp_nonneg _⟩
  have hW : 1 ≤ W := Real.one_le_exp (by positivity)
  have hprodS : ∀ x ∈ S, ∀ y ∈ S, ∀ i, |(f.baseChange ℝ).repr (y⁻¹ * x).coord i| ≤ W := by
    intro x hx y hy i
    have h := hprod (f.baseChange ℝ) (lieStructureConstants f) H q
      (realification_lowerCentralSeries_eq_bot hM) y⁻¹ x 1
      (fun i j k => (realLieBasis_structure f i j k).symm) hq (hκ.trans hpq)
      (hHp.trans (Real.exp_le_exp.mpr hpq)) hcM
      (fun j => by simpa only [coord_inv, map_neg, Finsupp.neg_apply, abs_neg] using hlarge hy j)
      (hlarge hx) (fun j => by simp only [coord_one, map_zero, Finsupp.zero_apply, abs_zero]; positivity) i
    change |(f.baseChange ℝ).repr (y⁻¹ * x).coord i| ≤ Real.exp ((q + D) ^ D)
    simpa only [mul_one] using h
  obtain ⟨Kleft, _, hKleftBound, hKleft⟩ := hleft (f.baseChange ℝ) (lieStructureConstants f) H q
    (realification_lowerCentralSeries_eq_bot hM)
    (fun i j k => (realLieBasis_structure f i j k).symm) hq (hκ.trans hpq)
    (hHp.trans (Real.exp_le_exp.mpr hpq)) hcM
  obtain ⟨ε, hε, hεinv, hgap⟩ := exists_uniform_lattice_image_gap (f.baseChange ℝ)
    (lieStructureConstants f) (fun i j k => (realLieBasis_structure f i j k).symm) hcM
    Q HQ W Kleft hW hQabs m hm J (Λ.map realificationHom) hJ
    (realification_subgroup_grid f Λ m hΛout) S (fun _ h => h.1) hprodS
    (fun y hy => hKleft y⁻¹ (fun j => by
      simpa only [coord_inv, map_neg, Finsupp.neg_apply, abs_neg] using hlarge hy j))
  obtain ⟨σ, hσ, hσH⟩ := exists_bounded_linear_image_section e f φ.toLinearMap hH hφ
  have hσB : ∀ i j, |(e.baseChange ℝ).repr (σ.baseChange ℝ ((f.baseChange ℝ) j)) i| ≤
      (rationalKernelHeight (Fintype.card κ) H : ℝ) := by
    intro i j
    rw [linearMap_baseChange_basis]
    exact (hσH i j).abs_real_le
  let T := bchLogMetricConstant s (Fintype.card κ) H 1
  let K := coordinateLipschitzBound (Fintype.card ι) (Fintype.card κ)
    (rationalKernelHeight (Fintype.card κ) H) * ((Fintype.card κ : ℝ≥0) + 1) * T
  have hlift := exists_local_metric_lifts_on_image
    (hnil := realification_lowerCentralSeries_eq_bot hL) (hM := realification_lowerCentralSeries_eq_bot hM)
    (e.baseChange ℝ) (f.baseChange ℝ) (realificationLieHom φ) (σ.baseChange ℝ)
    (linearMap_baseChange_image_section φ.toLinearMap σ hσ) (rationalKernelHeight (Fintype.card κ) H)
    hσB (lieStructureConstants f) (fun i j k => (realLieBasis_structure f i j k).symm) hcM
  let := realificationQuotientMetricSpace e Γ l hl hΓ
  have hpull : LipschitzWith ℓ (fun x => u (QuotientGroup.mk x)) := by
    simpa only [mul_one, Function.comp_def] using hu.comp
      (quotientMetricSpace_lipschitz_mk (e.baseChange ℝ) (Γ.map realificationHom)
        (realification_subgroup_closed_discrete e Γ l hl hΓ).1)
  obtain ⟨v, hv, hLip, hbound⟩ := exists_ambient_image_reconstruction Φ (Γ.map realificationHom)
    (Λ.map realificationHom) (realification_subgroup_closed_discrete f Λ m hm hΛout).1
    hcover (fun x => u (QuotientGroup.mk x)) hker
    (fun γ hγ x => congrArg u (QuotientGroup.eq.mpr (by
      simpa only [mul_inv_rev, inv_mul_cancel_left, inv_mul_cancel_right] using
        (Γ.map realificationHom).inv_mem hγ)))
    S ℓ K B T⁻¹ ε (inv_pos.mpr (bchLogMetricConstant_pos _ _ _ _)) hε hpull
    (fun x => hub _) hrepS hgap hlift
  let r := generalReconstructionLogBudget C D E F Z p
  obtain ⟨hr, hpr, h18, h48, h24, hZr, hEr, hFr⟩ :=
    generalReconstructionLogBudget_bounds C D E F Z hp
  have hexp : Real.exp p ≤ Real.exp r := Real.exp_le_exp.mpr hpr
  let Asec := coordinateLipschitzBound (Fintype.card ι) (Fintype.card κ)
    (rationalKernelHeight (Fintype.card κ) H)
  let Ndim : ℝ≥0 := (Fintype.card κ : ℝ≥0) + 1
  let Den : ℝ≥0 := (matrixDenominator Q * m : ℕ)
  let Row : ℝ≥0 := Ndim * (HQ + 1)
  let Box : ℝ≥0 := ⟨bchBoxCoordinateBound s (Fintype.card κ) H W,
    bchBoxCoordinateBound_nonneg _ _ _ W.coe_nonneg⟩
  have hAsec : (Asec : ℝ) ≤ Real.exp r :=
    (imageSection_bound_le_exp _ _ H hp hι hκ hHp).trans (Real.exp_le_exp.mpr h18)
  have hNdim : (Ndim : ℝ) ≤ Real.exp r := by
    apply le_trans _ hexp
    change (Fintype.card κ : ℝ) + 1 ≤ Real.exp p
    exact (by linarith : (Fintype.card κ : ℝ) + 1 ≤ p + 1).trans (Real.add_one_le_exp p)
  have hT : (T : ℝ) ≤ Real.exp r :=
    (hlog _ H p hp hκ hHp).trans (Real.exp_le_exp.mpr hZr)
  have hDen : (Den : ℝ) ≤ Real.exp r :=
    (imageDefiningDenominator_le_exp Q (Fintype.card ι) H m hQ hp hι hκ hHp hmp).trans
      (Real.exp_le_exp.mpr h48)
  have hRow : (Row : ℝ) ≤ Real.exp r := by
    apply le_trans _ (Real.exp_le_exp.mpr h24)
    exact imageDefiningRow_bound_le_exp _ _ H hp hι hκ hHp
  have hBox : (Box : ℝ) ≤ Real.exp r := by
    have hpqd : p ≤ q + D := hpq.trans (le_add_of_nonneg_right (Nat.cast_nonneg D))
    have hwbound : (W : ℝ) ≤ Real.exp ((q + D + 2) ^ D) := by
      change Real.exp ((q + D) ^ D) ≤ _
      exact Real.exp_le_exp.mpr (pow_le_pow_left₀ (by positivity) (by linarith) D)
    have hh := (bchBoxCoordinateBound_le_bchBoxMetricConstant s (Fintype.card κ) H W).trans
      (hbox _ H W (q + D) (by positivity) (hκ.trans hpqd)
        (hHp.trans (Real.exp_le_exp.mpr hpqd)) hwbound)
    exact hh.trans (Real.exp_le_exp.mpr hEr)
  have hY : (Kleft : ℝ) ≤ Real.exp r := hKleftBound.trans (Real.exp_le_exp.mpr hFr)
  have hεformula : (ε : ℝ)⁻¹ = (T : ℝ) * Kleft + Den * Row * Box * T * Kleft + 1 := by
    rw [hεinv]
    change _ = (bchLogMetricConstant s (Fintype.card κ) H 1 : ℝ) * Kleft +
      ((matrixDenominator Q * m : ℕ) : ℝ) * (((Fintype.card κ : ℝ) + 1) * ((HQ : ℝ) + 1)) *
        bchBoxCoordinateBound s (Fintype.card κ) H W *
        (bchLogMetricConstant s (Fintype.card κ) H 1 : ℝ) * Kleft + 1
    ring
  have htotal := generalReconstructionConstant_le_exp ℓ B Asec Ndim T Den Row Box Kleft ε r hr
    (hℓp.trans hexp) (hBp.trans hexp) hAsec hNdim hT hDen hRow hBox hY hεformula
  exact ⟨v, _, htotal.trans (Real.exp_le_exp.mpr (hbudget p hp)), hLip, hbound, hv⟩

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped NNReal TensorProduct

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped NNReal TensorProduct

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
  {s : ℕ} {hL : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M s = ⊥}

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped NNReal TensorProduct BigOperators

end Erdos3

end

end OAI
