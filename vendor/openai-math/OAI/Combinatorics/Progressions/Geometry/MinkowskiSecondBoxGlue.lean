/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Geometry/MinkowskiSecondBoxGlue.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Linear.MinkowskiSecondBoxBasis
@[expose] public section

namespace OAI

section

namespace Erdos3.BohrLattice.MinkowskiSecondBox

open scoped BigOperators Matrix
open Erdos3.BohrLattice.BoxCertificate Set Module Submodule

def rawTailLift {n : ℕ} (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (z : Fin n → ℤ) : Fin (n + 1) → ℝ :=
  Matrix.mulVec B (Fin.cons 0 (intCastVec z))

theorem deleteProjection_rawTailLift {n : ℕ} (h : Fin (n + 1))
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (z : Fin n → ℤ) :
    deleteProjection h (fun i ↦ B i 0) (rawTailLift B z) =
      Matrix.mulVec (projectedTail h B) (intCastVec z) := by
  funext i
  simp only [deleteProjection, rawTailLift, Matrix.mulVec, dotProduct,
    projectedTail]
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, mul_zero,
    zero_add]
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  congr 1
  simp only [div_eq_mul_inv]
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

noncomputable def matrixBasis {n : ℕ} (D : Matrix (Fin n) (Fin n) ℝ)
    (hD : D.det ≠ 0) : Module.Basis (Fin n) ℝ (Fin n → ℝ) :=
  (Pi.basisFun ℝ (Fin n)).map
    (D.toLinearEquiv' (D.invertibleOfIsUnitDet (isUnit_iff_ne_zero.mpr hD)))

@[simp] theorem matrixBasis_apply {n : ℕ} (D : Matrix (Fin n) (Fin n) ℝ)
    (hD : D.det ≠ 0) (j : Fin n) :
    matrixBasis D hD j = fun i ↦ D i j := by
  ext i
  rw [matrixBasis, Module.Basis.map_apply, Pi.basisFun_apply]
  change Matrix.mulVec D (Pi.single j 1) i = D i j
  simp [Matrix.mulVec]

theorem minkowskiSecondConstant_succ (n : ℕ) :
    minkowskiSecondConstant (n + 1) =
      (2 : ℝ) ^ n * minkowskiSecondConstant n := by
  unfold minkowskiSecondConstant
  have he : (n + 1) * ((n + 1) - 1) / 2 = n + n * (n - 1) / 2 := by
    rw [← Nat.choose_two_right, ← Nat.choose_two_right]
    simp [Nat.choose_succ_succ]
  rw [he, pow_add]

theorem exists_abs_apply_eq_norm {n : ℕ} (x : Fin (n + 1) → ℝ) :
    ∃ h, |x h| = ‖x‖ := by
  classical
  obtain ⟨h, -, hh⟩ := Finset.exists_max_image Finset.univ (fun i => |x i|)
    Finset.univ_nonempty
  refine ⟨h, le_antisymm (abs_apply_le_norm x h) ?_⟩
  rw [pi_norm_le_iff_of_nonneg (abs_nonneg (x h))]
  intro i
  simpa only [Real.norm_eq_abs] using hh i (Finset.mem_univ i)

theorem realBox_smul_one_eq_const {n : ℕ} (s : ℝ) :
    realBox (s • (fun _ : Fin n ↦ (1 : ℝ))) = realBox (fun _ ↦ s) := by
  congr 1
  funext i
  simp

theorem cube_has_successiveProductCertificate :
    ∀ {n : ℕ} (b : Basis (Fin n) ℝ (Fin n → ℝ)),
      Nonempty (SuccessiveProductCertificate
        (span ℤ (Set.range b)).toAddSubgroup (fun _ ↦ 1)
        (minkowskiSecondConstant n * |(Matrix.of b).det|)) := by
  intro n
  induction n with
  | zero =>
      intro b
      refine ⟨{
        scale := fun i ↦ Fin.elim0 i
        point := fun i ↦ Fin.elim0 i
        scale_nonneg := fun i ↦ Fin.elim0 i
        point_mem := fun i ↦ Fin.elim0 i
        independent := linearIndependent_empty_type
        mem_scaledBox := fun i ↦ Fin.elim0 i
        product_le := ?_ }⟩
      simp [minkowskiSecondConstant]
  | succ n ih =>
      intro b
      classical
      let L : Submodule ℤ (Fin (n + 1) → ℝ) := span ℤ (Set.range b)
      obtain ⟨v, hvL, hv0, hvmin⟩ := exists_shortest_nonzero_of_basis b
      let vL : L := ⟨v, hvL⟩
      have hvL0 : vL ≠ 0 := by
        intro h
        apply hv0
        exact congrArg Subtype.val h
      have hμpos : ∀ x : L, x ≠ 0 → 0 < ‖(x : Fin (n + 1) → ℝ)‖ := by
        intro x hx
        exact norm_pos_iff.mpr (by
          intro h
          apply hx
          exact Subtype.ext h)
      have hμhom : ∀ (c : ℤ), 0 < c → ∀ x : L,
          ‖((c • x : L) : Fin (n + 1) → ℝ)‖ =
            (c : ℝ) * ‖(x : Fin (n + 1) → ℝ)‖ := by
        intro c hc x
        have hcast : (((c • x : L) : Fin (n + 1) → ℝ)) =
            (c : ℝ) • (x : Fin (n + 1) → ℝ) := by
          ext i
          simp
        rw [hcast]
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos]
        exact_mod_cast hc
      have hμmin : ∀ x : L, x ≠ 0 →
          ‖(vL : Fin (n + 1) → ℝ)‖ ≤ ‖(x : Fin (n + 1) → ℝ)‖ := by
        intro x hx
        exact hvmin x x.property (by
          intro h
          apply hx
          exact Subtype.ext h)
      obtain ⟨-, Bz, hBz0⟩ :=
        Erdos3.BohrLattice.PrimitiveExtension.shortest_zspan_vector_primitive_and_extends
          (Nat.succ_pos n) b vL hvL0
          (fun x : L ↦ ‖(x : Fin (n + 1) → ℝ)‖) hμpos hμhom hμmin
      let b' : Basis (Fin (n + 1)) ℝ (Fin (n + 1) → ℝ) :=
        Bz.ofZLatticeBasis ℝ L
      have hb'0 : b' 0 = v := by
        rw [show b' 0 = ((Bz 0 : L) : Fin (n + 1) → ℝ) by
          exact Basis.ofZLatticeBasis_apply ℝ L Bz 0]
        exact congrArg Subtype.val (by simpa using hBz0)
      have hb'span : span ℤ (Set.range b') = L := by
        exact Bz.ofZLatticeBasis_span ℝ L
      let M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := (Matrix.of b')ᵀ
      have hMdet : M.det ≠ 0 := by
        have hbdet : (Pi.basisFun ℝ (Fin (n + 1))).det b' ≠ 0 :=
          (AlternatingMap.map_basis_ne_zero_iff b'
            (Pi.basisFun ℝ (Fin (n + 1))).det).mpr
              (Pi.basisFun ℝ (Fin (n + 1))).det_ne_zero
        rw [Pi.basisFun_det_apply] at hbdet
        simpa [M] using hbdet
      obtain ⟨h, hh⟩ := exists_abs_apply_eq_norm v
      have hvh : v h ≠ 0 := by
        intro hz
        have : ‖v‖ = 0 := by simpa [hz] using hh.symm
        exact hv0 (norm_eq_zero.mp this)
      have hMh0 : M h 0 ≠ 0 := by
        simpa [M, Matrix.of_apply, hb'0] using hvh
      let Q : Matrix (Fin n) (Fin n) ℝ := projectedTail h M
      have hQdet : Q.det ≠ 0 := projectedTail_det_ne_zero h M hMdet hMh0
      let qB : Basis (Fin n) ℝ (Fin n → ℝ) := projectedTailBasis h M hMdet hMh0
      obtain ⟨cq⟩ := ih qB
      have hQpoint : ∀ j, ∃ z : Fin n → ℤ,
          Matrix.mulVec Q (intCastVec z) = cq.point j := by
        intro j
        have hm := cq.point_mem j
        change cq.point j ∈ span ℤ (Set.range qB) at hm
        rw [Submodule.mem_span_range_iff_exists_fun] at hm
        obtain ⟨z, hz⟩ := hm
        refine ⟨z, ?_⟩
        rw [← hz]
        ext i
        simp [Q, qB, Matrix.mulVec, dotProduct, intCastVec, mul_comm]
      choose z hz using hQpoint
      let raw : Fin n → Fin (n + 1) → ℝ := fun j ↦ rawTailLift M (z j)
      let a : Fin n → ℤ := fun j ↦ -roundedCoefficient (raw j h / v h)
      let lift : Fin n → Fin (n + 1) → ℝ :=
        fun j ↦ raw j + (a j) • v
      let scale : Fin (n + 1) → ℝ := Fin.cons ‖v‖ (fun j ↦ 2 * cq.scale j)
      let point : Fin (n + 1) → Fin (n + 1) → ℝ := Fin.cons v lift
      have hraw_eq : ∀ j, raw j = ∑ k, (z j k) • b' k.succ := by
        intro j
        ext i
        simp [raw, rawTailLift, M, Matrix.mulVec, dotProduct, intCastVec,
          Fin.sum_univ_succ, mul_comm]
      have hrawL : ∀ j, raw j ∈ L := by
        intro j
        rw [hraw_eq]
        rw [← hb'span]
        apply sum_mem
        intro k hk
        exact smul_mem _ _ (subset_span (Set.mem_range_self k.succ))
      have hliftL : ∀ j, lift j ∈ L := by
        intro j
        change raw j + (a j) • v ∈ L
        exact add_mem (hrawL j) (smul_mem L (a j) hvL)
      have hcol0 : (fun i ↦ M i 0) = v := by
        funext i
        simp [M, Matrix.of_apply, hb'0]
      have hproj_raw : ∀ j, deleteProjection h v (raw j) = cq.point j := by
        intro j
        rw [← hcol0]
        rw [deleteProjection_rawTailLift]
        exact hz j
      have hproj_lift : ∀ j, deleteProjection h v (lift j) = cq.point j := by
        intro j
        change deleteProjection h v (raw j + (a j) • v) = cq.point j
        have hcast : (a j) • v = (a j : ℝ) • v := by
          ext i
          simp
        rw [hcast, deleteProjection_add_smul h v (raw j) (a j : ℝ) hvh]
        exact hproj_raw j
      have hqnorm : ∀ j, ‖cq.point j‖ ≤ cq.scale j := by
        intro j
        apply (mem_realBox_const_iff_norm_le (cq.scale_nonneg j) _).mp
        rw [← realBox_smul_one_eq_const]
        exact cq.mem_scaledBox j
      have ha : ∀ j, |raw j h / v h + (a j : ℝ)| ≤ (1 : ℝ) / 2 := by
        intro j
        simpa [a, sub_eq_add_neg] using
          abs_sub_roundedCoefficient_le_half (raw j h / v h)
      have hlift_upper : ∀ j, ‖lift j‖ ≤ cq.scale j + ‖v‖ / 2 := by
        intro j
        have hcast : (a j) • v = (a j : ℝ) • v := by
          ext i
          simp
        change ‖raw j + (a j) • v‖ ≤ cq.scale j + ‖v‖ / 2
        rw [hcast]
        exact reducedLift_apply_le h v (raw j) (cq.scale j) (a j : ℝ)
          hh hvh (ha j) ((congrArg norm (hproj_raw j)).le.trans (hqnorm j))
      have hlift0 : ∀ j, lift j ≠ 0 := by
        intro j hj
        apply cq.independent.ne_zero j
        rw [← hproj_lift j, hj]
        ext i
        simp [deleteProjection]
      have hshortlift : ∀ j, ‖v‖ ≤ ‖lift j‖ := by
        intro j
        exact hvmin (lift j) (hliftL j) (hlift0 j)
      have hliftnorm : ∀ j, ‖lift j‖ ≤ 2 * cq.scale j := by
        intro j
        have hu := hlift_upper j
        have hs := hshortlift j
        linarith
      have hind : LinearIndependent ℝ point := by
        rw [Fintype.linearIndependent_iff]
        intro g hg i
        have hprojrel : ∑ j, g j.succ • cq.point j = 0 := by
          have hm := congrArg (deleteProjectionLinear h v) hg
          rw [map_sum] at hm
          rw [Fin.sum_univ_succ] at hm
          simp only [point, Fin.cons_zero, Fin.cons_succ] at hm
          rw [map_smul, deleteProjectionLinear_apply,
            deleteProjection_self h v hvh, smul_zero, zero_add] at hm
          simp only [map_smul, deleteProjectionLinear_apply, map_zero] at hm
          simp_rw [hproj_lift] at hm
          exact hm
        have htail : ∀ j : Fin n, g j.succ = 0 :=
          (Fintype.linearIndependent_iff.mp cq.independent) _ hprojrel
        refine Fin.cases ?_ htail i
        rw [Fin.sum_univ_succ] at hg
        simp only [point, Fin.cons_zero, Fin.cons_succ] at hg
        simp_rw [htail] at hg
        simp only [zero_smul, Finset.sum_const_zero, add_zero] at hg
        exact (smul_eq_zero.mp hg).resolve_right hv0
      have hqdet : |(Matrix.of qB).det| = |Q.det| := by
        have hmat : Matrix.of qB = Qᵀ := by
          ext i j
          simp [qB, Q, Matrix.of_apply, Matrix.col]
        rw [hmat, Matrix.det_transpose]
      have hMabs : |M.det| = |(Matrix.of b).det| := by
        have hchange := abs_det_zspan_basis_eq b Bz
        have hmat : Matrix.of (((↑) : L → (Fin (n + 1) → ℝ)) ∘ Bz) =
            Matrix.of b' := by
          ext i j
          simp [b', Matrix.of_apply]
        rw [hmat] at hchange
        simpa [M] using hchange
      have hfactor : |(Matrix.of b).det| = ‖v‖ * |Q.det| := by
        rw [← hMabs]
        have hd := abs_det_eq_abs_pivot_mul_abs_det_projectedTail h M hMh0
        have hentry : M h 0 = v h := congrFun hcol0 h
        rw [hentry, hh] at hd
        simpa [Q] using hd
      refine ⟨{
        scale := scale
        point := point
        scale_nonneg := ?_
        point_mem := ?_
        independent := hind
        mem_scaledBox := ?_
        product_le := ?_ }⟩
      · intro i
        refine Fin.cases (norm_nonneg v) (fun j ↦ ?_) i
        exact mul_nonneg (by norm_num) (cq.scale_nonneg j)
      · intro i
        refine Fin.cases hvL (fun j ↦ hliftL j) i
      · intro i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · rw [realBox_smul_one_eq_const]
          apply (mem_realBox_const_iff_norm_le (norm_nonneg v) v).mpr
          simp
        · have hm := (mem_realBox_const_iff_norm_le
              (mul_nonneg (by norm_num) (cq.scale_nonneg j)) (lift j)).mpr
              (hliftnorm j)
          rw [realBox_smul_one_eq_const]
          simpa [scale, point] using hm
      · have hcq : ∏ j, cq.scale j ≤ minkowskiSecondConstant n * |Q.det| := by
          simpa [hqdet] using cq.product_le
        calc
          ∏ i, scale i = ‖v‖ * ((2 : ℝ) ^ n * ∏ j, cq.scale j) := by
            simp [scale, Fin.prod_univ_succ, Finset.prod_mul_distrib,
              Finset.prod_const]
          _ ≤ ‖v‖ * ((2 : ℝ) ^ n *
              (minkowskiSecondConstant n * |Q.det|)) := by
            gcongr
          _ = minkowskiSecondConstant (n + 1) * |(Matrix.of b).det| := by
            rw [minkowskiSecondConstant_succ, hfactor]
            ring

end Erdos3.BohrLattice.MinkowskiSecondBox

end

end OAI
