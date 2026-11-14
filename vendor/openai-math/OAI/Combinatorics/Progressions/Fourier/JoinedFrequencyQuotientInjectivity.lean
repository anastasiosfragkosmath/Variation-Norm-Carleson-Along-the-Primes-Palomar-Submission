/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Fourier/JoinedFrequencyQuotientInjectivity.lean
Changes: Lean module/public-import conversion; unneeded declarations and imports were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import Mathlib.Algebra.Lie.Prod
public import OAI.Combinatorics.Progressions.Estimates.RefilteredPointwiseSplitting
public import OAI.Combinatorics.Progressions.Linear.TopSubspaceAdaptedBasis
public import OAI.Combinatorics.Progressions.Fourier.VerticalFrequencyIdentification
@[expose] public section

namespace OAI

section

namespace Erdos3

open Module

theorem RationalHeightLE.inv {q : ℚ} {H : ℕ} (hq : RationalHeightLE q H) (hne : q ≠ 0) :
    RationalHeightLE q⁻¹ H := by
  have hn : q.num ≠ 0 := by
    intro hn
    apply hne
    rw [← q.num_div_den, hn, Int.cast_zero, zero_div]
  have h := rationalHeightLE_fraction (q.den : ℤ) q.num hn
    (by simpa only [Int.natAbs_natCast] using hq.2) hq.1
  have he : q⁻¹ = (q.den : ℚ) / q.num := by
    calc
      q⁻¹ = ((q.num : ℚ) / q.den)⁻¹ := congrArg Inv.inv q.num_div_den.symm
      _ = _ := inv_div _ _
  simpa only [he, Int.cast_natCast] using h

theorem exists_bounded_frequency_direction {ι V : Type*} [AddCommGroup V] [Module ℚ V]
    (b : Basis ι ℚ V) (η : V →ₗ[ℚ] ℚ) (hη : η ≠ 0)
    {H : ℕ} (hH : 1 ≤ H) (hheight : ∀ i, RationalHeightLE (η (b i)) H) :
    ∃ (v : V) (m : ℕ), 0 < m ∧ m ≤ H ∧ η v = 1 ∧
      (∀ i, RationalHeightLE (b.repr v i) H) ∧
      (fun i => b.repr v i) ∈ denominatorGrid m := by
  classical
  have hex : ∃ i, η (b i) ≠ 0 := by
    by_contra h
    push Not at h
    apply hη
    apply b.ext
    intro i
    exact h i
  obtain ⟨i, hi⟩ := hex
  let c := (η (b i))⁻¹
  let v := c • b i
  have hc : RationalHeightLE c H := (hheight i).inv hi
  have hcoord (j : ι) : b.repr v j = if i = j then c else 0 := by
    simp only [v, map_smul, Finsupp.smul_apply, Basis.repr_self, Finsupp.single_apply, smul_eq_mul]
    split_ifs <;> simp
  refine ⟨v, c.den, c.den_pos, hc.2, ?_, ?_, ?_⟩
  · change η (c • b i) = 1
    rw [map_smul, smul_eq_mul]
    exact inv_mul_cancel₀ hi
  · intro j
    rw [hcoord]
    split_ifs
    · exact hc
    · exact rationalHeightLE_zero hH
  · refine ⟨fun j => if i = j then c.num else 0, ?_⟩
    intro j
    change (c.den : ℚ) * b.repr v j = ((if i = j then c.num else 0 : ℤ) : ℚ)
    rw [hcoord]
    by_cases hj : i = j
    · simp only [hj, ite_true]
      have hcden := (div_eq_iff (show (c.den : ℚ) ≠ 0 from Nat.cast_ne_zero.mpr c.den_ne_zero)).mp c.num_div_den
      simpa only [mul_comm] using hcden.symm
    · simp only [hj, ite_false, mul_zero, Int.cast_zero]

end Erdos3

end

section

namespace Erdos3

theorem rationalLogHeight_nat_inv_mul (n : ℕ) (hn : 0 < n) {x : ℚ} {p : ℝ}
    (hx : rationalLogHeight x ≤ p) : rationalLogHeight ((n : ℚ)⁻¹ * x) ≤ p + n + 1 := by
  have hp : 0 ≤ p := (rationalLogHeight_nonneg x).trans hx
  have hnheight : RationalHeightLE (n : ℚ) (n + 1) := by simp [RationalHeightLE]
  have hinv := hnheight.inv (by exact_mod_cast hn.ne')
  apply rationalLogHeight_le_of_height (hinv.mul (rationalHeightLE_ceil_exp hx))
  calc
    (((n + 1) * ⌈Real.exp p⌉₊ : ℕ) : ℝ) = ((n : ℝ) + 1) * (⌈Real.exp p⌉₊ : ℝ) := by push_cast; rfl
    _ ≤ Real.exp (n : ℝ) * Real.exp (p + 1) :=
      mul_le_mul (Real.add_one_le_exp _) (ceil_exp_le_exp_add_one hp)
        (Nat.cast_nonneg _) (Real.exp_pos _).le
    _ = Real.exp (p + n + 1) := by rw [← Real.exp_add]; congr 1; ring

variable {L : Type*} [AddCommGroup L] [Module ℚ L]

noncomputable def dividedFrequency (n : ℕ) (η : L →ₗ[ℚ] ℚ) : L →ₗ[ℚ] ℚ := (n : ℚ)⁻¹ • η

theorem dividedFrequency_height (n : ℕ) (hn : 0 < n) (η : L →ₗ[ℚ] ℚ)
    {p : ℝ} (x : L) (hx : rationalLogHeight (η x) ≤ p) :
    rationalLogHeight (dividedFrequency n η x) ≤ p + n + 1 :=
  rationalLogHeight_nat_inv_mul n hn hx

end Erdos3

end

section

namespace Erdos3

open Module

variable {ι V : Type*} [AddCommGroup V] [Module ℚ V]

noncomputable def frequencyKernelProjection (η : V →ₗ[ℚ] ℚ) (v : V) : V →ₗ[ℚ] V :=
  LinearMap.id - η.smulRight v

@[simp] theorem frequencyKernelProjection_apply (η : V →ₗ[ℚ] ℚ) (v x : V) :
    frequencyKernelProjection η v x = x - η x • v := rfl

theorem frequencyKernelProjection_range (η : V →ₗ[ℚ] ℚ) (v : V) (hv : η v = 1) :
    LinearMap.range (frequencyKernelProjection η v) = LinearMap.ker η := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change η (y - η y • v) = 0
    simp only [map_sub, map_smul, hv, smul_eq_mul, mul_one, sub_self]
  · intro hx
    refine ⟨x, ?_⟩
    change x - η x • v = x
    rw [show η x = 0 from hx, zero_smul, sub_zero]

theorem frequencyKernel_spanning (b : Basis ι ℚ V) (η : V →ₗ[ℚ] ℚ) (v : V) (hv : η v = 1) :
    Submodule.span ℚ (Set.range (fun i => b i - η (b i) • v)) = LinearMap.ker η := by
  change Submodule.span ℚ (Set.range (frequencyKernelProjection η v ∘ b)) = _
  rw [Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_top,
    frequencyKernelProjection_range η v hv]

theorem frequencyKernel_spanning_height (b : Basis ι ℚ V) (η : V →ₗ[ℚ] ℚ) (v : V)
    {H : ℕ} (hη : ∀ i, RationalHeightLE (η (b i)) H)
    (hv : ∀ i, RationalHeightLE (b.repr v i) H) :
    ∀ i j, RationalHeightLE (b.repr (b i - η (b i) • v) j) (2 * H ^ 2) := by
  classical
  intro i j
  rw [map_sub, Finsupp.sub_apply, map_smul, Finsupp.smul_apply, smul_eq_mul]
  have hbase : RationalHeightLE (b.repr (b i) j) 1 := by
    rw [Basis.repr_self, Finsupp.single_apply]
    split_ifs
    · exact rationalHeightLE_one le_rfl
    · exact rationalHeightLE_zero le_rfl
  have h := hbase.sub ((hη i).mul (hv j))
  convert h using 1
  ring

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

theorem realifyFunctional_eq_rid (η : V →ₗ[ℚ] ℚ) (x : ℝ ⊗[ℚ] V) :
    realifyFunctional η x = TensorProduct.rid ℚ ℝ (η.baseChange ℝ x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r v =>
    simp only [realifyFunctional_tmul, LinearMap.baseChange_tmul, TensorProduct.rid_tmul,
      Rat.smul_def, mul_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem mem_realified_frequency_kernel_iff (η : V →ₗ[ℚ] ℚ) (x : ℝ ⊗[ℚ] V) :
    x ∈ (LinearMap.ker η).baseChange ℝ ↔ realifyFunctional η x = 0 := by
  rw [realification_ker, LinearMap.mem_ker, realifyFunctional_eq_rid]
  constructor
  · intro h
    rw [h, map_zero]
  · intro h
    apply (TensorProduct.rid ℚ ℝ).injective
    simpa only [map_zero] using h

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

variable {V J : Type*} [AddCommGroup V] [Module ℚ V]

def finiteFrequencyKernel (P : Submodule ℚ V) (eta : J → V →ₗ[ℚ] ℚ) :
    List J → Submodule ℚ V
  | [] => P
  | j :: js => LinearMap.ker (eta j) ⊓ finiteFrequencyKernel P eta js

theorem mem_finiteFrequencyKernel (P : Submodule ℚ V) (eta : J → V →ₗ[ℚ] ℚ)
    (js : List J) (v : V) :
    v ∈ finiteFrequencyKernel P eta js ↔ v ∈ P ∧ ∀ j ∈ js, eta j v = 0 := by
  induction js with
  | nil => simp [finiteFrequencyKernel]
  | cons j js ih =>
    simp only [finiteFrequencyKernel, Submodule.mem_inf, LinearMap.mem_ker, ih,
      List.forall_mem_cons]
    tauto

theorem finiteFrequencyKernel_le (P : Submodule ℚ V) (eta : J → V →ₗ[ℚ] ℚ) (js : List J) :
    finiteFrequencyKernel P eta js ≤ P := fun v hv => (mem_finiteFrequencyKernel P eta js v).mp hv |>.1

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

theorem realifyFunctional_comp {V W : Type*} [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W] (eta : W →ₗ[ℚ] ℚ) (f : V →ₗ[ℚ] W) (x : ℝ ⊗[ℚ] V) :
    realifyFunctional (eta.comp f) x = realifyFunctional eta (f.baseChange ℝ x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a v => simp only [realifyFunctional_tmul, LinearMap.baseChange_tmul, LinearMap.comp_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

namespace NilpotentLieFiltration

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))

theorem associatedGradedPieceMap_grade_fixed (j : ℕ) (x : F.layer j) :
    basisGradeProjection (F.associatedGradedBasis b w hF) w j (F.associatedGradedPieceMap j x) =
      F.associatedGradedPieceMap j x := by
  rw [← F.gradedPieceProjection_eq_pieceMap b w hF j x]
  apply (F.associatedGradedBasis b w hF).repr.injective
  ext i
  simp only [basisGradeProjection_repr, F.gradedPieceProjection_coordinate]
  split_ifs <;> rfl

theorem frequency_zero_on_refiltered_top (U : LieSubalgebra ℚ F.AssociatedGraded)
    (eta : L →ₗ[ℚ] ℚ)
    (hzero : ∀ x ∈ U, basisGradeProjection (F.associatedGradedBasis b w hF) w s x = x →
      F.gradedFrequency b w hF eta x = 0) :
    ∀ x ∈ F.gradedRefiltrationLayer U s, eta x = 0 := by
  intro x hx
  obtain ⟨hxs, hxU⟩ := (F.mem_gradedRefiltrationLayer U s x).mp hx
  rw [← F.gradedFrequency_top_piece b w hF eta ⟨x, hxs⟩]
  exact hzero _ hxU (F.associatedGradedPieceMap_grade_fixed b w hF s ⟨x, hxs⟩)

theorem real_frequency_zero_on_refiltered_top (U : LieSubalgebra ℚ F.AssociatedGraded)
    (eta : L →ₗ[ℚ] ℚ)
    (hzero : ∀ x ∈ U, basisGradeProjection (F.associatedGradedBasis b w hF) w s x = x →
      F.gradedFrequency b w hF eta x = 0) :
    ∀ x ∈ F.realGradedRefiltrationLayer U s, realifyFunctional eta x = 0 := by
  have hle : F.gradedRefiltrationLayer U s ≤ LinearMap.ker eta :=
    F.frequency_zero_on_refiltered_top b w hF U eta hzero
  intro x hx
  exact (mem_realified_frequency_kernel_iff eta x).mp (Submodule.baseChange_mono ℝ hle hx)

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open Module CircleFourier
open scoped TensorProduct BigOperators

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d}

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3

open Module

variable {V I J : Type*} [AddCommGroup V] [Module ℚ V]

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

variable {L Y W J : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing Y] [LieAlgebra ℚ Y] [LieRing W] [LieAlgebra ℚ W] {s : ℕ}
  (F : NilpotentLieFiltration L s) (π : L →ₗ⁅ℚ⁆ Y)
  (eta : J → L →ₗ[ℚ] ℚ) (js : List J)

def pivotAnnihilatorIdeal : LieIdeal ℚ L :=
  F.topSubspaceIdeal (finiteFrequencyKernel (F.layer s ⊓ LinearMap.ker π.toLinearMap) eta js)
    ((finiteFrequencyKernel_le _ _ _).trans inf_le_left)

variable (partner : J → W →ₗ[ℚ] ℚ)

end Erdos3.NilpotentLieFiltration

end

end OAI
