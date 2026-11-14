/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Nilpotent/BCHSmoothPartitionBudget.lean
Changes: Lean module/public-import conversion; unneeded declarations and imports were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Geometry.QuantitativeMetricPartition
public import OAI.Combinatorics.Progressions.Estimates.AmbientImageExtension
public import OAI.Combinatorics.Progressions.Nilpotent.BCHQuotientLocalIsometry
@[expose] public section

namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open Module Manifold MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable (e : Basis ι ℝ L) (v : ι → ℝ)

theorem norm_mfderiv_coordinateLine (t : ℝ) :
    letI := basisChartedSpace (hnil := hnil) e
    letI := rightRiemannianBundle (hnil := hnil) e
    ‖mfderiv 𝓘(ℝ) 𝓘(ℝ, ι → ℝ) (coordinateLine (hnil := hnil) e v) t 1‖ = coordinateL2Norm v := by
  let := basisChartedSpace (hnil := hnil) e
  let := rightRiemannianBundle (hnil := hnil) e
  have hv := (congrArg (fun w : ι → ℝ => rightVelocity e (coordinateLine (hnil := hnil) e v t) w)
    (mfderiv_coordinateLine (hnil := hnil) e v t)).trans (rightVelocity_coordinateLine e v t)
  exact (norm_tangent_eq_coordinateL2Norm e (coordinateLine (hnil := hnil) e v t) _).trans
    (congrArg coordinateL2Norm hv)

theorem enorm_mfderiv_coordinateLine (t : ℝ) :
    letI := basisChartedSpace (hnil := hnil) e
    letI := rightRiemannianBundle (hnil := hnil) e
    ‖mfderiv 𝓘(ℝ) 𝓘(ℝ, ι → ℝ) (coordinateLine (hnil := hnil) e v) t 1‖ₑ =
      ENNReal.ofReal (coordinateL2Norm v) := by
  let := basisChartedSpace (hnil := hnil) e
  let := rightRiemannianBundle (hnil := hnil) e
  rw [← ofReal_norm]
  exact congrArg ENNReal.ofReal (norm_mfderiv_coordinateLine e v t)

theorem pathELength_coordinateLine :
    letI := basisChartedSpace (hnil := hnil) e
    letI := rightRiemannianBundle (hnil := hnil) e
    pathELength 𝓘(ℝ, ι → ℝ) (coordinateLine (hnil := hnil) e v) 0 1 =
      ENNReal.ofReal (coordinateL2Norm v) := by
  let := basisChartedSpace (hnil := hnil) e
  let := rightRiemannianBundle (hnil := hnil) e
  rw [pathELength_eq_lintegral_mfderiv_Icc]
  have hf : (fun t : ℝ => ‖mfderiv 𝓘(ℝ) 𝓘(ℝ, ι → ℝ) (coordinateLine (hnil := hnil) e v) t 1‖ₑ) =
      fun _ => ENNReal.ofReal (coordinateL2Norm v) :=
    funext (enorm_mfderiv_coordinateLine e v)
  rw [hf]
  simp

theorem dist_one_le_coordinateL2Norm (g : NilpotentLieBCHGroup L s hnil) :
    letI := rightMetricSpace (hnil := hnil) e
    dist 1 g ≤ coordinateL2Norm (basisHomeomorph e g) := by
  let := basisChartedSpace (hnil := hnil) e
  let := rightRiemannianBundle (hnil := hnil) e
  let := rightMetricSpace (hnil := hnil) e
  have hedist : edist 1 g ≤ ENNReal.ofReal (coordinateL2Norm (basisHomeomorph e g)) := by
    apply (riemannianEDist_le_pathELength
      (contMDiff_coordinateLine e (basisHomeomorph e g) 1).contMDiffOn
      (coordinateLine_zero e _) (by simp only [coordinateLine_one, Homeomorph.symm_apply_apply])
      zero_le_one).trans_eq
    exact pathELength_coordinateLine e _
  rw [dist_edist]
  exact (ENNReal.toReal_mono (by simp) hedist).trans_eq
    (ENNReal.toReal_ofReal (coordinateL2Norm_nonneg _))

theorem dist_le_coordinateL2Norm_mul_inv (x y : NilpotentLieBCHGroup L s hnil) :
    letI := rightMetricSpace (hnil := hnil) e
    dist x y ≤ coordinateL2Norm (basisHomeomorph e (x * y⁻¹)) := by
  let := rightMetricSpace (hnil := hnil) e
  let := rightMetricSpace_isIsometricSMul (hnil := hnil) e
  rw [← dist_mul_right x y y⁻¹, mul_inv_cancel, dist_comm]
  exact dist_one_le_coordinateL2Norm e (x * y⁻¹)

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

open scoped NNReal

noncomputable def bchBoxMetricConstant (s d H : ℕ) (B : ℝ≥0) : ℝ≥0 :=
  ⟨(d + 1) * bchBoxCoordinateBound s d H B,
    mul_nonneg (by positivity) (bchBoxCoordinateBound_nonneg s d H B.coe_nonneg)⟩

namespace NilpotentLieBCHGroup

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ) {H : ℕ}
  (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
  (hc : ∀ i j k, RationalHeightLE (c i j k) H)

include hstructure hc

theorem dist_le_bchBoxMetricConstant (B : ℝ≥0) (hB : 1 ≤ B) {δ : ℝ} (hδ : 0 ≤ δ)
    (x y : NilpotentLieBCHGroup L s hnil)
    (hx : ∀ i, |e.repr x.coord i| ≤ B) (hy : ∀ i, |e.repr y.coord i| ≤ B)
    (hxy : ∀ i, |e.repr x.coord i - e.repr y.coord i| ≤ δ) :
    letI := rightMetricSpace (hnil := hnil) e
    dist x y ≤ bchBoxMetricConstant s (Fintype.card ι) H B * δ := by
  let := rightMetricSpace (hnil := hnil) e
  have hBr : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hcoord (i : ι) : |basisHomeomorph e (x * y⁻¹) i| ≤
      bchBoxCoordinateBound s (Fintype.card ι) H B * δ :=
    lieBCH_sub_coordinates_bound e c hstructure hc hnil x.coord y.coord hBr hδ hx hy hxy i
  calc
    _ ≤ coordinateL2Norm (basisHomeomorph e (x * y⁻¹)) := dist_le_coordinateL2Norm_mul_inv e x y
    _ ≤ (Fintype.card ι + 1) * (bchBoxCoordinateBound s (Fintype.card ι) H B * δ) :=
      coordinateL2Norm_le_card_bound _
        (mul_nonneg (bchBoxCoordinateBound_nonneg s _ H B.coe_nonneg) hδ) hcoord
    _ = _ := by change _ = ((Fintype.card ι + 1) * bchBoxCoordinateBound s (Fintype.card ι) H B) * δ; ring

theorem lipschitzOn_basisHomeomorph_symm_box (B : ℝ≥0) (hB : 1 ≤ B) :
    letI := rightMetricSpace (hnil := hnil) e
    LipschitzOnWith (bchBoxMetricConstant s (Fintype.card ι) H B)
      (basisHomeomorph (hnil := hnil) e).symm {v | ∀ i, |v i| ≤ B} := by
  let := rightMetricSpace (hnil := hnil) e
  apply LipschitzOnWith.of_dist_le_mul
  intro v hv w hw
  apply dist_le_bchBoxMetricConstant e c hstructure hc B hB dist_nonneg
  · intro i
    change |basisHomeomorph (hnil := hnil) e ((basisHomeomorph (hnil := hnil) e).symm v) i| ≤ _
    simpa only [Homeomorph.apply_symm_apply] using hv i
  · intro i
    change |basisHomeomorph (hnil := hnil) e ((basisHomeomorph (hnil := hnil) e).symm w) i| ≤ _
    simpa only [Homeomorph.apply_symm_apply] using hw i
  · intro i
    change |basisHomeomorph (hnil := hnil) e ((basisHomeomorph (hnil := hnil) e).symm v) i -
      basisHomeomorph (hnil := hnil) e ((basisHomeomorph (hnil := hnil) e).symm w) i| ≤ _
    simpa only [Homeomorph.apply_symm_apply, Real.dist_eq] using dist_le_pi_dist v w i

end NilpotentLieBCHGroup
end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped NNReal

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
  [LieRing M] [LieAlgebra ℚ M] [LieAlgebra ℝ M] [IsScalarTower ℚ ℝ M]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul ℝ M] [T2Space M]
  {s t H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M t = ⊥}

theorem dist_linear_lift_le (e : Basis ι ℝ L) (f : Basis κ ℝ M) (σ : M →ₗ[ℝ] L)
    (B : ℝ≥0) (hσB : ∀ i j, |e.repr (σ (f j)) i| ≤ B)
    (c : κ → κ → κ → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = f.repr ⁅f i, f j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H) :
    letI := rightMetricSpace (hnil := hnil) e
    letI := rightMetricSpace (hnil := hM) f
    let C := bchLogMetricConstant t (Fintype.card κ) H 1
    let K := coordinateLipschitzBound (Fintype.card ι) (Fintype.card κ) B *
      ((Fintype.card κ : ℝ≥0) + 1) * C
    ∀ g : NilpotentLieBCHGroup M t hM, dist 1 g < (C⁻¹ : ℝ≥0) →
      dist 1 (⟨σ g.coord⟩ : NilpotentLieBCHGroup L s hnil) ≤ K * dist 1 g := by
  let := rightMetricSpace (hnil := hnil) e
  let := rightMetricSpace (hnil := hM) f
  let C := bchLogMetricConstant t (Fintype.card κ) H 1
  let A := coordinateLipschitzBound (Fintype.card ι) (Fintype.card κ) B
  change ∀ g : NilpotentLieBCHGroup M t hM, dist 1 g < (C⁻¹ : ℝ≥0) →
    dist 1 (⟨σ g.coord⟩ : NilpotentLieBCHGroup L s hnil) ≤
      (A * ((Fintype.card κ : ℝ≥0) + 1) * C : ℝ≥0) * dist 1 g
  intro g hg
  have hC : (0 : ℝ) < C := bchLogMetricConstant_pos t (Fintype.card κ) H 1
  have hnear : (C : ℝ) * dist 1 g < (1 : ℝ≥0) := by
    rw [NNReal.coe_inv] at hg
    change (C : ℝ) * dist 1 g < 1
    have hh := mul_lt_mul_of_pos_left hg hC
    simpa only [mul_inv_cancel₀ hC.ne'] using hh
  have hnorm := norm_coordinates_le_of_near_one f c hstructure hc 1 le_rfl g hnear
  let h : NilpotentLieBCHGroup L s hnil := ⟨σ g.coord⟩
  have hcoord : basisHomeomorph e h = basisCoordinateMap f e σ (basisHomeomorph f g) := by
    change e.equivFun (σ g.coord) = e.equivFun (σ (f.equivFun.symm (f.equivFun g.coord)))
    rw [LinearEquiv.symm_apply_apply]
  calc
    dist 1 h ≤ coordinateL2Norm (basisHomeomorph e h) := dist_one_le_coordinateL2Norm e h
    _ ≤ (A : ℝ) * coordinateL2Norm (basisHomeomorph f g) := by
      rw [hcoord]
      exact basisCoordinateMap_L2_bound f e σ B B.coe_nonneg hσB _
    _ ≤ A * (((Fintype.card κ : ℝ) + 1) * ‖basisHomeomorph f g‖) := by
      apply mul_le_mul_of_nonneg_left _ A.coe_nonneg
      exact coordinateL2Norm_le_card_bound _ (norm_nonneg _) (fun j => by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm (basisHomeomorph f g) j)
    _ ≤ A * (((Fintype.card κ : ℝ) + 1) * ((C : ℝ) * dist 1 g)) := by
      gcongr
    _ = _ := by simp only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one]; ring

theorem exists_local_metric_lifts_of_section (e : Basis ι ℝ L) (f : Basis κ ℝ M)
    (φ : L →ₗ⁅ℝ⁆ M) (σ : M →ₗ[ℝ] L) (hσ : Function.RightInverse σ φ)
    (B : ℝ≥0) (hσB : ∀ i j, |e.repr (σ (f j)) i| ≤ B)
    (c : κ → κ → κ → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = f.repr ⁅f i, f j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H) :
    letI := rightMetricSpace (hnil := hnil) e
    letI := rightMetricSpace (hnil := hM) f
    let C := bchLogMetricConstant t (Fintype.card κ) H 1
    let K := coordinateLipschitzBound (Fintype.card ι) (Fintype.card κ) B *
      ((Fintype.card κ : ℝ≥0) + 1) * C
    ∀ g : NilpotentLieBCHGroup M t hM, dist 1 g < (C⁻¹ : ℝ≥0) →
      ∃ h : NilpotentLieBCHGroup L s hnil,
        mapReal φ h = g ∧ dist 1 h ≤ K * dist 1 g := by
  let := rightMetricSpace (hnil := hnil) e
  let := rightMetricSpace (hnil := hM) f
  dsimp only
  intro g hg
  exact ⟨⟨σ g.coord⟩, ext (hσ g.coord), dist_linear_lift_le e f σ B hσB c hstructure hc g hg⟩

theorem exists_local_metric_lifts_on_image (e : Basis ι ℝ L) (f : Basis κ ℝ M)
    (φ : L →ₗ⁅ℝ⁆ M) (σ : M →ₗ[ℝ] L)
    (hσ : (φ.toLinearMap.comp σ).comp φ.toLinearMap = φ.toLinearMap)
    (B : ℝ≥0) (hσB : ∀ i j, |e.repr (σ (f j)) i| ≤ B)
    (c : κ → κ → κ → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = f.repr ⁅f i, f j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H) :
    letI := rightMetricSpace (hnil := hnil) e
    letI := rightMetricSpace (hnil := hM) f
    let C := bchLogMetricConstant t (Fintype.card κ) H 1
    let K := coordinateLipschitzBound (Fintype.card ι) (Fintype.card κ) B *
      ((Fintype.card κ : ℝ≥0) + 1) * C
    ∀ g ∈ (mapReal (hnil := hnil) (hM := hM) φ).range, dist 1 g < (C⁻¹ : ℝ≥0) →
      ∃ h : NilpotentLieBCHGroup L s hnil,
        mapReal φ h = g ∧ dist 1 h ≤ K * dist 1 g := by
  let := rightMetricSpace (hnil := hnil) e
  let := rightMetricSpace (hnil := hM) f
  dsimp only
  intro g hgrange hg
  obtain ⟨x, hx⟩ := hgrange
  have hcoord : φ x.coord = g.coord := congrArg NilpotentLieBCHGroup.coord hx
  have hs := DFunLike.congr_fun hσ x.coord
  change φ (σ (φ x.coord)) = φ x.coord at hs
  rw [hcoord] at hs
  exact ⟨⟨σ g.coord⟩, ext hs, dist_linear_lift_le e f σ B hσB c hstructure hc g hg⟩

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

open Module

theorem coordinateL2Norm_smul {ι : Type*} [Fintype ι] (r : ℝ) (v : ι → ℝ) :
    coordinateL2Norm (r • v) = |r| * coordinateL2Norm v := by
  unfold coordinateL2Norm
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq_eq_abs]

namespace NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

def realBCHLine (v : L) (r : ℝ) : NilpotentLieBCHGroup L s hnil := ⟨r • v⟩

theorem realBCHLine_zero (v : L) : realBCHLine (hnil := hnil) v 0 = 1 := by
  apply ext
  exact zero_smul ℝ v

theorem realBCHLine_one (v : L) : realBCHLine (hnil := hnil) v 1 = ⟨v⟩ := by
  apply ext
  exact one_smul ℝ v

theorem realBCHLine_add (v : L) (r t : ℝ) :
    realBCHLine (hnil := hnil) v (r + t) = realBCHLine v r * realBCHLine v t := by
  apply ext
  change (r + t) • v = lieBCH s (r • v) (t • v)
  rw [lieBCH_eq_add_of_lie_eq_zero hnil (by simp [smul_lie, lie_smul]), add_smul]

theorem realBCHLine_commute (v : L) (hv : ∀ w : L, ⁅v, w⁆ = 0)
    (r : ℝ) (g : NilpotentLieBCHGroup L s hnil) : Commute (realBCHLine v r) g := by
  apply commute_of_lie_eq_zero
  change ⁅r • v, g.coord⁆ = 0
  rw [smul_lie, hv, smul_zero]

variable [IsScalarTower ℚ ℝ L] {ι : Type*} [Fintype ι] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]

theorem realBCHLine_dist_one_le (e : Basis ι ℝ L) (v : L) (r : ℝ) :
    letI := rightMetricSpace (hnil := hnil) e
    dist (realBCHLine (hnil := hnil) v r) 1 ≤ |r| * coordinateL2Norm (e.equivFun v) := by
  let := rightMetricSpace (hnil := hnil) e
  rw [dist_comm]
  apply (dist_one_le_coordinateL2Norm e (realBCHLine v r)).trans_eq
  change coordinateL2Norm (e.equivFun (r • v)) = _
  rw [map_smul, coordinateL2Norm_smul]

end NilpotentLieBCHGroup
end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem exists_bchBoxMetricConstant_exp_bound (s r : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ (d H : ℕ) (B : ℝ≥0) (p : ℝ),
      0 ≤ p → (d : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (B : ℝ) ≤ Real.exp ((p + 2) ^ r) →
      (bchBoxMetricConstant s d H B : ℝ) ≤ Real.exp ((p + D) ^ D) := by
  obtain ⟨C, hC, hheight⟩ := exists_bchCoordinateHeight_exp_budget s
  let D := C + 2 * s + r + 10
  refine ⟨D, by dsimp [D]; omega, ?_⟩
  intro d H B p hp hd hH hB
  let t : ℝ := p + D
  have hD3 : (3 : ℝ) ≤ D := by exact_mod_cast (show 3 ≤ D by dsimp [D]; omega)
  have ht : 3 ≤ t := by dsimp [t]; linarith
  have hp2 : p + 2 ≤ t := by dsimp [t]; linarith
  have hd1 : (d : ℝ) + 1 ≤ t := by dsimp [t]; linarith
  have hs1 : (s : ℝ) + 1 ≤ t := by
    have h : (s : ℝ) + 1 ≤ D := by exact_mod_cast (show s + 1 ≤ D by dsimp [D]; omega)
    dsimp [t]
    linarith
  have hbase : 2 * (d : ℝ) + 1 ≤ t ^ 2 := by nlinarith [sq_nonneg (t - 1)]
  have hpoly : ((d : ℝ) + 1) * (((s : ℝ) + 1) * (2 * d + 1) ^ s) * (2 * d) * s ≤
      t ^ (2 * s + 5) := by
    calc
      _ ≤ t * (t * (t ^ 2) ^ s) * t ^ 2 * t := by
        gcongr <;> linarith
      _ = _ := by rw [← pow_mul, pow_add]; ring
  have hpolyexp : ((d : ℝ) + 1) * (((s : ℝ) + 1) * (2 * d + 1) ^ s) * (2 * d) * s ≤
      Real.exp (t ^ (D - 1)) := by
    apply hpoly.trans
    apply (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ t)
      (by dsimp [D]; omega : 2 * s + 5 ≤ D - 1)).trans
    linarith [Real.add_one_le_exp (t ^ (D - 1))]
  have hcoef : (bchCoordinateHeight s d H : ℝ) ≤ Real.exp (t ^ (D - 1)) := by
    apply (hheight d H p hp hd hH).trans
    apply Real.exp_le_exp.mpr
    have hCD : (C : ℝ) ≤ D := by exact_mod_cast (show C ≤ D by dsimp [D]; omega)
    apply (pow_le_pow_left₀ (by positivity) (show p + C ≤ t by dsimp [t]; linarith) C).trans
    exact pow_le_pow_right₀ (by linarith) (by dsimp [D]; omega)
  have hlength : ((s * (2 * d + 1) : ℕ) : ℝ) ≤ t ^ 3 := by
    push_cast
    calc
      _ ≤ t * t ^ 2 := mul_le_mul (by linarith) hbase (by positivity) (by linarith)
      _ = _ := by ring
  have hinput : (B : ℝ) ^ (s * (2 * d + 1)) ≤ Real.exp (t ^ (D - 1)) := by
    calc
      _ ≤ (Real.exp ((p + 2) ^ r)) ^ (s * (2 * d + 1)) :=
        pow_le_pow_left₀ B.coe_nonneg hB _
      _ = Real.exp (((s * (2 * d + 1) : ℕ) : ℝ) * (p + 2) ^ r) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp (t ^ 3 * t ^ r) := Real.exp_le_exp.mpr
        (mul_le_mul hlength (pow_le_pow_left₀ (by linarith) hp2 r) (by positivity) (by positivity))
      _ = Real.exp (t ^ (r + 3)) := by rw [← pow_add, Nat.add_comm 3 r]
      _ ≤ Real.exp (t ^ (D - 1)) := Real.exp_le_exp.mpr
        (pow_le_pow_right₀ (by linarith) (by dsimp [D]; omega))
  change ((d : ℝ) + 1) * bchBoxCoordinateBound s d H B ≤ _
  unfold bchBoxCoordinateBound
  push_cast
  calc
    _ = (((d : ℝ) + 1) * (((s : ℝ) + 1) * (2 * d + 1) ^ s) * (2 * d) * s) *
        bchCoordinateHeight s d H * (B : ℝ) ^ (s * (2 * d + 1)) := by ring
    _ ≤ Real.exp (t ^ (D - 1)) * Real.exp (t ^ (D - 1)) * Real.exp (t ^ (D - 1)) :=
      mul_le_mul (mul_le_mul hpolyexp hcoef (by positivity) (by positivity)) hinput
        (by positivity) (by positivity)
    _ = Real.exp (3 * t ^ (D - 1)) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (t ^ D) := by
      apply Real.exp_le_exp.mpr
      calc
        _ ≤ t * t ^ (D - 1) := mul_le_mul_of_nonneg_right ht (by positivity)
        _ = _ := by rw [← pow_succ', Nat.sub_add_cancel (by dsimp [D]; omega : 1 ≤ D)]
    _ = _ := rfl

namespace NilpotentLieBCHGroup

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

end NilpotentLieBCHGroup

end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped NNReal

theorem exists_coordinateBox_metric_cover {ι L : Type*} [Fintype ι]
    [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
    [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
    {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
    (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H) (B : ℝ≥0) (hB : 1 ≤ B)
    {ε : ℝ} (hε : 0 < ε) :
    let K := bchBoxMetricConstant s (Fintype.card ι) H B
    let N := boxCoverMeshCount B K ε
    ∃ centers : (ι → Fin (N + 1)) → coordinateBox (hnil := hnil) e B,
      letI := rightMetricSpace (hnil := hnil) e
      ∀ x : coordinateBox (hnil := hnil) e B, ∃ j, dist x (centers j) ≤ ε := by
  let K := bchBoxMetricConstant s (Fintype.card ι) H B
  let N := boxCoverMeshCount B K ε
  have hN : 0 < N := boxCoverMeshCount_pos _ _ _
  let centers : (ι → Fin (N + 1)) → coordinateBox (hnil := hnil) e B := fun k =>
    ⟨(basisHomeomorph (hnil := hnil) e).symm (uniformBoxGrid B N k), by
      intro i
      change |basisHomeomorph (hnil := hnil) e
        ((basisHomeomorph (hnil := hnil) e).symm (uniformBoxGrid B N k)) i| ≤ B
      rw [Homeomorph.apply_symm_apply]
      exact uniformBoxGrid_mem B.coe_nonneg hN k i⟩
  refine ⟨centers, ?_⟩
  let := rightMetricSpace (hnil := hnil) e
  intro x
  obtain ⟨j, hj⟩ := exists_uniformBoxGrid_approx (lt_of_lt_of_le zero_lt_one hB) hN
    (basisHomeomorph (hnil := hnil) e x.val) x.property
  refine ⟨j, ?_⟩
  have h := (lipschitzOn_basisHomeomorph_symm_box (hnil := hnil) e c hstructure hc B hB).dist_le_mul
    (basisHomeomorph (hnil := hnil) e x.val) x.property
    (uniformBoxGrid B N j) (uniformBoxGrid_mem B.coe_nonneg hN j)
  have hdist := h.trans ((mul_le_mul_of_nonneg_left hj K.coe_nonneg).trans (boxCoverMeshCount_error K hε))
  simpa only [centers, Subtype.dist_eq, Homeomorph.symm_apply_apply] using hdist

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

noncomputable def bchInjectivityRadius (s d H l : ℕ) : ℝ :=
  1 / (4 * ((l : ℝ) + 1) * (bchBoxCoordinateBound s d H 1 + 1))

theorem bchInjectivityRadius_pos (s d H l : ℕ) : 0 < bchInjectivityRadius s d H l := by
  have := bchBoxCoordinateBound_nonneg s d H (B := 1) (by norm_num)
  unfold bchInjectivityRadius
  positivity

theorem bchInjectivityRadius_le_one (s d H l : ℕ) : bchInjectivityRadius s d H l ≤ 1 := by
  have hA := bchBoxCoordinateBound_nonneg s d H (B := 1) (by norm_num)
  unfold bchInjectivityRadius
  apply (div_le_one (by positivity)).mpr
  nlinarith [Nat.cast_nonneg (α := ℝ) l]

theorem bchInjectivityRadius_separation (s d H l : ℕ) (hl : 0 < l) :
    bchBoxCoordinateBound s d H 1 * (2 * bchInjectivityRadius s d H l) < 1 / (l : ℝ) := by
  have hl' : (0 : ℝ) < l := by exact_mod_cast hl
  have hl1 : (0 : ℝ) < l + 1 := by positivity
  have hA := bchBoxCoordinateBound_nonneg s d H (B := 1) (by norm_num)
  have hA1 : 0 < bchBoxCoordinateBound s d H 1 + 1 := by linarith
  have hr := bchInjectivityRadius_pos s d H l
  calc
    _ ≤ (bchBoxCoordinateBound s d H 1 + 1) * (2 * bchInjectivityRadius s d H l) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = 1 / (2 * ((l : ℝ) + 1)) := by
      unfold bchInjectivityRadius
      field_simp
      ring
    _ < 1 / (l : ℝ) := one_div_lt_one_div_of_lt hl' (by linarith)

namespace NilpotentLieBCHGroup

open Module

theorem quotient_coordinate_injOn
    {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
    [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
    [ContinuousSMul ℝ L] [T2Space L]
    {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
    (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l)
    (hgrid : ∀ g ∈ Γ, e.equivFun g.coord ∈ realDenominatorGrid l)
    (z : NilpotentLieBCHGroup L s hnil) :
    Set.InjOn (fun v : ι → ℝ => (QuotientGroup.mk (z * (basisHomeomorph e).symm v) : _ ⧸ Γ))
      {v | ∀ i, |v i| ≤ bchInjectivityRadius s (Fintype.card ι) H l} :=
  quotient_coordinate_injOn_of_radius e c hstructure hc Γ l hl hgrid
    (bchInjectivityRadius_pos _ _ _ _).le (bchInjectivityRadius_le_one _ _ _ _)
    (bchInjectivityRadius_separation _ _ _ _ hl) z

end NilpotentLieBCHGroup

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

namespace Erdos3

theorem enlarged_power_dominates_twice_add_sixteen {p : ℝ} (hp : 0 ≤ p)
    (C : ℕ) (hC : 2 ≤ C) :
    2 * (p + C) ^ C + 16 ≤ (p + (C + 5 : ℕ)) ^ (C + 5) := by
  let t : ℝ := p + (C + 5 : ℕ)
  have ht : 7 ≤ t := by
    have hC' : (2 : ℝ) ≤ C := by exact_mod_cast hC
    dsimp [t]
    push_cast
    linarith
  have hpow : 1 ≤ t ^ C := one_le_pow₀ (by linarith)
  have hq : (p + C) ^ C ≤ t ^ C := by
    apply pow_le_pow_left₀ (by positivity)
    dsimp [t]
    push_cast
    linarith
  calc
    _ ≤ 18 * t ^ C := by linarith
    _ ≤ t ^ 2 * t ^ C := mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
    _ = t ^ (C + 2) := by rw [← pow_add, Nat.add_comm]
    _ ≤ t ^ (C + 5) := pow_le_pow_right₀ (by linarith) (by omega)

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem bchBoxCoordinateBound_le_bchBoxMetricConstant (s d H : ℕ) (B : ℝ≥0) :
    bchBoxCoordinateBound s d H B ≤ (bchBoxMetricConstant s d H B : ℝ) := by
  change bchBoxCoordinateBound s d H B ≤ ((d : ℝ) + 1) * bchBoxCoordinateBound s d H B
  have := bchBoxCoordinateBound_nonneg s d H B.coe_nonneg
  nlinarith [Nat.cast_nonneg (α := ℝ) d]

theorem exists_bchInverseBoxConstant_exp_bound (s a : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ (d H : ℕ) (B : ℝ≥0) (p : ℝ),
      0 ≤ p → (d : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (B : ℝ) ≤ Real.exp ((p + 2) ^ a) →
      (bchInverseBoxConstant s d H B : ℝ) ≤ Real.exp ((p + D) ^ D) := by
  obtain ⟨C₁, hC₁, hbox⟩ := exists_bchBoxMetricConstant_exp_bound s a
  obtain ⟨C₂, hC₂, hone⟩ := exists_bchBoxMetricConstant_exp_bound s 0
  let C := C₁ + C₂ + a + 4
  have hC : 2 ≤ C := by dsimp [C]; omega
  refine ⟨C + 5, by omega, ?_⟩
  intro d H B p hp hd hH hB
  let q := (p + C) ^ C
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hC' : (2 : ℝ) ≤ C := by exact_mod_cast hC
  have hBq : (B : ℝ) ≤ Real.exp q := by
    apply hB.trans
    apply Real.exp_le_exp.mpr
    apply (pow_le_pow_left₀ (by linarith) (show p + 2 ≤ p + C by linarith) a).trans
    exact pow_le_pow_right₀ (by linarith) (by dsimp [C]; omega)
  have hAq : bchBoxCoordinateBound s d H B ≤ Real.exp q :=
    (bchBoxCoordinateBound_le_bchBoxMetricConstant s d H B).trans
      ((hbox d H B p hp hd hH hB).trans (Real.exp_le_exp.mpr
        (shifted_power_self_mono (C := C₁) (D := C) hp (by omega) (by dsimp [C]; omega))))
  have hA1q : bchBoxCoordinateBound s d H 1 ≤ Real.exp q := by
    apply (bchBoxCoordinateBound_le_bchBoxMetricConstant s d H 1).trans
    have hunit : ((1 : ℝ≥0) : ℝ) ≤ Real.exp ((p + 2) ^ 0) := by
      simpa only [NNReal.coe_one, pow_zero] using
        Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)
    apply (hone d H 1 p hp hd hH hunit).trans
    exact Real.exp_le_exp.mpr
      (shifted_power_self_mono (C := C₂) (D := C) hp (by omega) (by dsimp [C]; omega))
  have hnum : bchBoxCoordinateBound s d H B + 2 * (B : ℝ) ≤ 3 * Real.exp q := by linarith
  have hden : bchBoxCoordinateBound s d H 1 + 1 ≤ 2 * Real.exp q := by
    linarith [Real.one_le_exp hq]
  have h6 : (6 : ℝ) ≤ Real.exp 16 := by linarith [Real.add_one_le_exp (16 : ℝ)]
  change (bchBoxCoordinateBound s d H B + 2 * (B : ℝ)) *
    (bchBoxCoordinateBound s d H 1 + 1) ≤ _
  calc
    _ ≤ (3 * Real.exp q) * (2 * Real.exp q) :=
      mul_le_mul hnum hden (by have := bchBoxCoordinateBound_nonneg s d H (B := 1) (by norm_num); linarith)
        (by positivity)
    _ = 6 * Real.exp (2 * q) := by rw [show 2 * q = q + q by ring, Real.exp_add]; ring
    _ ≤ Real.exp 16 * Real.exp (2 * q) := mul_le_mul_of_nonneg_right h6 (Real.exp_nonneg _)
    _ = Real.exp (2 * q + 16) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (enlarged_power_dominates_twice_add_sixteen hp C hC)

namespace NilpotentLieBCHGroup

open Module

end NilpotentLieBCHGroup
end Erdos3

end

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

end OAI
