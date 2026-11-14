/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Fourier/RealQuarterTorusExtension.lean
Changes: Lean module/public-import conversion; unneeded declarations and imports were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import Mathlib.Analysis.Normed.Group.AddCircle
public import OAI.Combinatorics.Progressions.Estimates.LipschitzExtensionAlongMap
public import OAI.Combinatorics.Progressions.Geometry.DenseRealBoxCell
public import OAI.Combinatorics.Progressions.Linear.ProperCyclicKernelBasis
@[expose] public section

namespace OAI

section

namespace Erdos3

open Module

noncomputable def properCyclicCoordinateBound (r : ℕ) (δ : ℝ) : ℝ :=
  (r : ℝ) * r.factorial * properCyclicKernelBasisBound r δ ^ (r - 1)

theorem properCyclicCoordinateBound_nonneg (r : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    0 ≤ properCyclicCoordinateBound r δ := by
  have h := properCyclicKernelBasisBound_nonneg r hδ
  unfold properCyclicCoordinateBound
  positivity

theorem exists_controlled_cyclic_torus_model
    {r N : ℕ} [NeZero N] (η : (Fin r → ℤ) →+ ZMod N) (R : Fin r → ℕ)
    (hinj : Set.InjOn η {x | ∀ i, |x i| ≤ (R i : ℤ)})
    (h₀ : ZMod N) (J : Finset (ZMod N))
    (δ : ℝ) (hδ : 0 < δ) (hdense : δ * N ≤ (J.card : ℝ))
    (hrep : ∀ h ∈ J, ∃ x : Fin r → ℤ, (∀ i, |x i| ≤ (R i : ℤ)) ∧ h = h₀ + η x) :
    ∃ b : Basis (Fin r) ℤ (cyclicIntegerKernel η),
      (∀ i j, |(b i : Fin r → ℝ) j| ≤ properCyclicKernelBasisBound r δ * ((R j : ℝ) + 1)) ∧
      (∀ x : Fin r → ℝ, (∀ j, |x j| ≤ (R j : ℝ) + 1) → ∀ i,
        |cyclicKernelRealCoordinates η b x i| ≤ properCyclicCoordinateBound r δ) ∧
      Set.InjOn (fun x i => cyclicKernelCoordinateCharacter η b i x)
        {x | ∀ i, |x i| ≤ (R i : ℤ)} ∧
      ∃ t : Fin r → ℝ, (∀ i, t i ∈ Set.Ico (0 : ℝ) 1) ∧
        (∀ i, ∃ k : ℤ, (N : ℝ) * t i = (k : ℝ)) ∧
        ∀ (h : ZMod N) (x : Fin r → ℤ), h = h₀ + η x → ∀ i,
          ((cyclicKernelRealCoordinates η b (integerVectorRealMap x) i : ℝ) :
            AddCircle (1 : ℝ)) =
              ((((h.val : ℝ) - h₀.val) * t i : ℝ) : AddCircle (1 : ℝ)) := by
  obtain ⟨b, hb, t, ht, hperiod, hformula⟩ :=
    exists_proper_affine_torus_basis η R hinj h₀ J δ hδ hdense hrep
  refine ⟨b, hb, ?_, cyclicKernelCoordinateCharacters_injOn η b _ hinj,
    t, ht, hperiod, hformula⟩
  intro x hx i
  exact lattice_basis_coordinates_bound (cyclicIntegerKernel η) b
    (fun j => (R j : ℝ) + 1) (by intro j; positivity)
    (properCyclicKernelBasisBound_nonneg r hδ) hb
    (proper_cyclic_kernel_covolume_lower_bound η R hinj) x hx i

end Erdos3

end

section

namespace Erdos3

theorem properCyclicKernelBasisBound_le_exp {r : ℕ} {p : ℝ}
    (hp : 0 ≤ p) (hr : (r : ℝ) ≤ p) :
    properCyclicKernelBasisBound r (Real.exp (-p)) ≤ Real.exp ((p + 4) ^ 3) := by
  have htwo : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hpow (k : ℕ) : (2 : ℝ) ^ k ≤ Real.exp (2 * (k : ℝ)) := by
    calc
      _ ≤ (Real.exp 2) ^ k := pow_le_pow_left₀ (by norm_num) htwo k
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hk : r * (r - 1) / 2 ≤ r * r :=
    (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left r (Nat.sub_le _ _))
  have hkR : ((r * (r - 1) / 2 : ℕ) : ℝ) ≤ p ^ 2 := by
    have h : ((r * (r - 1) / 2 : ℕ) : ℝ) ≤ (r : ℝ) * r := by exact_mod_cast hk
    exact h.trans (by nlinarith [Nat.cast_nonneg (α := ℝ) r])
  have hM : BohrLattice.MinkowskiSecondBox.minkowskiSecondConstant r ≤ Real.exp (2 * p ^ 2) :=
    (hpow _).trans (Real.exp_le_exp.mpr (by linarith))
  have h2r : (2 : ℝ) ^ r ≤ Real.exp (2 * p) :=
    (hpow r).trans (Real.exp_le_exp.mpr (by linarith))
  have hrp : (r : ℝ) ≤ Real.exp p := hr.trans
    ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp p))
  have hM0 : 0 ≤ BohrLattice.MinkowskiSecondBox.minkowskiSecondConstant r := by
    unfold BohrLattice.MinkowskiSecondBox.minkowskiSecondConstant
    positivity
  have hmain : properCyclicKernelBasisBound r (Real.exp (-p)) ≤ Real.exp (2 * p ^ 2 + 4 * p) := by
    unfold properCyclicKernelBasisBound
    rw [Real.exp_neg, div_eq_mul_inv, inv_inv]
    calc
      _ ≤ Real.exp p * Real.exp (2 * p ^ 2) * Real.exp (2 * p) * Real.exp p := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  apply hmain.trans
  apply Real.exp_le_exp.mpr
  have h : 0 ≤ p ^ 3 + 10 * p ^ 2 + 44 * p + 64 := by positivity
  nlinarith

theorem properCyclicCoordinateBound_le_exp {r : ℕ} {p : ℝ}
    (hp : 0 ≤ p) (hr : (r : ℝ) ≤ p) :
    properCyclicCoordinateBound r (Real.exp (-p)) ≤ Real.exp ((p + 4) ^ 5) := by
  have hB := properCyclicKernelBasisBound_le_exp hp hr
  have hB0 := properCyclicKernelBasisBound_nonneg r (Real.exp_pos (-p))
  have hrp : (r : ℝ) ≤ Real.exp p := hr.trans
    ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp p))
  have hfac : (r.factorial : ℝ) ≤ Real.exp (p ^ 2) :=
    (factorial_le_exp_sq r).trans (Real.exp_le_exp.mpr
      (by nlinarith [Nat.cast_nonneg (α := ℝ) r]))
  have hsub : ((r - 1 : ℕ) : ℝ) ≤ p :=
    (Nat.cast_le.mpr (Nat.sub_le r 1)).trans hr
  have hpower : properCyclicKernelBasisBound r (Real.exp (-p)) ^ (r - 1) ≤
      Real.exp (p * (p + 4) ^ 3) := by
    calc
      _ ≤ (Real.exp ((p + 4) ^ 3)) ^ (r - 1) := pow_le_pow_left₀ hB0 hB _
      _ = Real.exp (((r - 1 : ℕ) : ℝ) * (p + 4) ^ 3) := by rw [Real.exp_nat_mul]
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hsub (by positivity))
  have hmain : properCyclicCoordinateBound r (Real.exp (-p)) ≤
      Real.exp (p + p ^ 2 + p * (p + 4) ^ 3) := by
    unfold properCyclicCoordinateBound
    calc
      _ ≤ Real.exp p * Real.exp (p ^ 2) * Real.exp (p * (p + 4) ^ 3) := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]
  apply hmain.trans
  apply Real.exp_le_exp.mpr
  have h : 0 ≤ p ^ 5 + 19 * p ^ 4 + 148 * p ^ 3 + 591 * p ^ 2 + 1215 * p + 1024 := by
    positivity
  nlinarith

end Erdos3

end

section

namespace Erdos3

open Module

noncomputable def centeredCircleLift (z : AddCircle (1 : ℝ)) : ℝ :=
  (AddCircle.equivIco (1 : ℝ) (-(1 / 2)) z).val

theorem centeredCircleLift_coe {y : ℝ} (hy : |y| ≤ 1 / 4) :
    centeredCircleLift (y : AddCircle (1 : ℝ)) = y := by
  apply AddCircle.equivIco_coe_of_mem
  constructor <;> linarith [(abs_le.mp hy).1, (abs_le.mp hy).2]

noncomputable def affineCyclicTorusLocalLift {r N : ℕ}
    (t c : Fin r → ℝ) (h₀ h : ZMod N) : Fin r → ℝ :=
  fun i => centeredCircleLift
    (((((h.val : ℝ) - h₀.val) * t i - c i) : ℝ) : AddCircle (1 : ℝ))

theorem exists_localized_cyclic_torus_chart
    {r N : ℕ} [NeZero N] (η : (Fin r → ℤ) →+ ZMod N) (R : Fin r → ℕ)
    (hinj : Set.InjOn η {x | ∀ i, |x i| ≤ (R i : ℤ)})
    (h₀ : ZMod N) (J : Finset (ZMod N)) (hJ : J.Nonempty)
    (δ : ℝ) (hδ : 0 < δ) (hdense : δ * N ≤ (J.card : ℝ))
    (x : ZMod N → Fin r → ℤ)
    (hx : ∀ h ∈ J, ∀ i, |x h i| ≤ (R i : ℤ))
    (hrep : ∀ h ∈ J, h = h₀ + η (x h)) (q : ℕ) (hq : 2 ≤ q) :
    ∃ b : Basis (Fin r) ℤ (cyclicIntegerKernel η),
      (∀ i j, |(b i : Fin r → ℝ) j| ≤ properCyclicKernelBasisBound r δ * ((R j : ℝ) + 1)) ∧
      ∃ t : Fin r → ℝ, (∀ i, t i ∈ Set.Ico (0 : ℝ) 1) ∧
        (∀ i, ∃ k : ℤ, (N : ℝ) * t i = (k : ℝ)) ∧
        ∃ K ⊆ J, K.Nonempty ∧
          J.card ≤ realBoxCellCount (properCyclicCoordinateBound r δ) q ^ r * K.card ∧
          ∃ c : Fin r → ℝ,
            (∀ i, |c i| ≤ properCyclicCoordinateBound r δ + (1 / 2 : ℝ) / q) ∧
            ∀ h ∈ K,
              cyclicKernelRealCoordinates η b (integerVectorRealMap (x h)) =
                c + affineCyclicTorusLocalLift t c h₀ h ∧
              (∀ i, |affineCyclicTorusLocalLift t c h₀ h i| ≤ (1 / 2 : ℝ) / q) ∧
              integerVectorRealMap (x h) = (cyclicKernelRealCoordinates η b).symm
                (c + affineCyclicTorusLocalLift t c h₀ h) := by
  classical
  obtain ⟨b, hb, hcoordinates, _, t, ht, hperiod, hphase⟩ :=
    exists_controlled_cyclic_torus_model η R hinj h₀ J δ hδ hdense
      (fun h hh => ⟨x h, hx h hh, hrep h hh⟩)
  let y (h : ZMod N) := cyclicKernelRealCoordinates η b (integerVectorRealMap (x h))
  have hy : ∀ h ∈ J, ∀ i, |y h i| ≤ properCyclicCoordinateBound r δ := by
    intro h hh i
    apply hcoordinates _ _ i
    intro j
    have hj : |(x h j : ℝ)| ≤ (R j : ℝ) := by exact_mod_cast hx h hh j
    change |(x h j : ℝ)| ≤ (R j : ℝ) + 1
    linarith
  obtain ⟨K, hKJ, hK, hcard, c, hc, hclose⟩ := exists_dense_real_box_cell J hJ y hy q (by omega)
  have hquarter : (1 / 2 : ℝ) / q ≤ 1 / 4 := by
    have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
    apply (div_le_iff₀ (by linarith : (0 : ℝ) < q)).mpr
    linarith
  refine ⟨b, hb, t, ht, hperiod, K, hKJ, hK, ?_, c, hc, ?_⟩
  · simpa only [Fintype.card_fin] using hcard
  · intro h hh
    have hlocal (i) : affineCyclicTorusLocalLift t c h₀ h i = y h i - c i := by
      have he : ((y h i - c i : ℝ) : AddCircle (1 : ℝ)) =
          (((((h.val : ℝ) - h₀.val) * t i - c i) : ℝ) : AddCircle (1 : ℝ)) := by
        rw [AddCircle.coe_sub, AddCircle.coe_sub]
        exact congrArg (fun z : AddCircle (1 : ℝ) => z - (c i : AddCircle (1 : ℝ)))
          (hphase h (x h) (hrep h (hKJ hh)) i)
      change centeredCircleLift _ = _
      rw [← he]
      exact centeredCircleLift_coe ((hclose h hh i).trans hquarter)
    have he : y h = c + affineCyclicTorusLocalLift t c h₀ h := by
      funext i
      rw [Pi.add_apply, hlocal]
      ring
    refine ⟨he, ?_, ?_⟩
    · intro i
      rw [hlocal]
      exact hclose h hh i
    · exact (LinearEquiv.eq_symm_apply (cyclicKernelRealCoordinates η b)).mpr he

end Erdos3

end

section

namespace Erdos3

theorem centeredCircleLift_eq_sub_floor (x : ℝ) :
    centeredCircleLift (x : AddCircle (1 : ℝ)) = x - (⌊x + 1 / 2⌋ : ℤ) := by
  have hmem : x - (⌊x + 1 / 2⌋ : ℤ) ∈ Set.Ico (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1) := by
    constructor
    · linarith [Int.floor_le (x + 1 / 2)]
    · linarith [Int.lt_floor_add_one (x + 1 / 2)]
  have hint : (((⌊x + 1 / 2⌋ : ℤ) : ℝ) : AddCircle (1 : ℝ)) = 0 := by
    apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
    exact ⟨⌊x + 1 / 2⌋, by simp⟩
  have he : ((x - (⌊x + 1 / 2⌋ : ℤ) : ℝ) : AddCircle (1 : ℝ)) = x := by
    rw [AddCircle.coe_sub, hint, sub_zero]
  rw [← he]
  exact AddCircle.equivIco_coe_of_mem hmem

noncomputable def affineCyclicTorusCarry {r N : ℕ}
    (t c : Fin r → ℝ) (h₀ h : ZMod N) (i : Fin r) : ℤ :=
  ⌊((h.val : ℝ) - h₀.val) * t i - c i + 1 / 2⌋

theorem affineCyclicTorusLocalLift_eq_sub_carry {r N : ℕ}
    (t c : Fin r → ℝ) (h₀ h : ZMod N) (i : Fin r) :
    affineCyclicTorusLocalLift t c h₀ h i =
      ((h.val : ℝ) - h₀.val) * t i - c i - affineCyclicTorusCarry t c h₀ h i :=
  centeredCircleLift_eq_sub_floor _

theorem affineCyclicTorusCarry_identity {r N : ℕ}
    (t c : Fin r → ℝ) (h₀ h : ZMod N) (i : Fin r) :
    (-(h₀.val : ℝ) * t i - c i) +
      ((-(affineCyclicTorusCarry t c h₀ h i) : ℤ) : ℚ) + (h.val : ℝ) * t i =
        affineCyclicTorusLocalLift t c h₀ h i := by
  rw [affineCyclicTorusLocalLift_eq_sub_carry]
  push_cast
  ring

end Erdos3

end

section

namespace Erdos3

theorem local_cyclic_torus_cell_count_le_exp {r : ℕ} {p : ℝ}
    (hp : 0 ≤ p) (hr : (r : ℝ) ≤ p) :
    ((realBoxCellCount (properCyclicCoordinateBound r (Real.exp (-p))) 8 : ℕ) : ℝ) ^ r ≤
      Real.exp ((r : ℝ) * ((p + 4) ^ 5 + 17)) := by
  have hC := properCyclicCoordinateBound_le_exp hp hr
  have hC0 := properCyclicCoordinateBound_nonneg r (Real.exp_pos (-p))
  have hm := realBoxCellCount_le hC0 8
  have hE : 1 ≤ Real.exp ((p + 4) ^ 5) := Real.one_le_exp (by positivity)
  have h17 : (17 : ℝ) ≤ Real.exp 17 := by linarith [Real.add_one_le_exp (17 : ℝ)]
  have hcount : (realBoxCellCount (properCyclicCoordinateBound r (Real.exp (-p))) 8 : ℝ) ≤
      Real.exp ((p + 4) ^ 5 + 17) := by
    calc
      _ ≤ 17 * Real.exp ((p + 4) ^ 5) := by norm_num at hm; linarith
      _ ≤ Real.exp 17 * Real.exp ((p + 4) ^ 5) :=
        mul_le_mul_of_nonneg_right h17 (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  calc
    _ ≤ (Real.exp ((p + 4) ^ 5 + 17)) ^ r := pow_le_pow_left₀ (Nat.cast_nonneg _) hcount r
    _ = _ := (Real.exp_nat_mul _ _).symm

theorem local_cyclic_torus_total_loss_le {r : ℕ} {p : ℝ}
    (hp : 0 ≤ p) (hr : (r : ℝ) ≤ p) :
    p + (r : ℝ) * ((p + 4) ^ 5 + 17) ≤ (p + 4) ^ 7 := by
  let U := p + 4
  have hU : 4 ≤ U := by dsimp [U]; linarith
  have h1 : 1 ≤ U := by linarith
  have hU0 : 0 ≤ U := by linarith
  have hpow : (4 : ℝ) ^ 3 ≤ U ^ 3 := pow_le_pow_left₀ (by norm_num) hU 3
  have hlinear : 18 * U ≤ U ^ 4 := by
    have h := mul_le_mul_of_nonneg_right hpow hU0
    nlinarith
  calc
    _ ≤ U + U * (U ^ 5 + 17) := by dsimp [U]; gcongr <;> linarith
    _ = U ^ 6 + 18 * U := by ring
    _ ≤ U ^ 6 + U ^ 4 := add_le_add (le_refl _) hlinear
    _ ≤ U ^ 6 + U ^ 6 := add_le_add (le_refl _) (pow_le_pow_right₀ h1 (by omega))
    _ ≤ U ^ 7 := by
      have h := mul_le_mul_of_nonneg_right (show (2 : ℝ) ≤ U by linarith) (pow_nonneg hU0 6)
      nlinarith

theorem local_cyclic_torus_density {r N : ℕ} {p : ℝ}
    (hp : 0 ≤ p) (hr : (r : ℝ) ≤ p) (J K : Finset (ZMod N))
    (hJ : Real.exp (-p) * N ≤ (J.card : ℝ))
    (hK : J.card ≤ realBoxCellCount (properCyclicCoordinateBound r (Real.exp (-p))) 8 ^ r * K.card) :
    Real.exp (-((p + 4) ^ 7)) * N ≤ (K.card : ℝ) := by
  let L := (r : ℝ) * ((p + 4) ^ 5 + 17)
  have hcount := local_cyclic_torus_cell_count_le_exp hp hr
  have hretain : Real.exp (-(p + L)) * N ≤ (K.card : ℝ) := by
    apply (mul_le_mul_iff_right₀ (Real.exp_pos L)).mp
    calc
      _ = Real.exp (-p) * N := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ (J.card : ℝ) := hJ
      _ ≤ ((realBoxCellCount (properCyclicCoordinateBound r (Real.exp (-p))) 8 : ℕ) : ℝ) ^ r * K.card := by
        exact_mod_cast hK
      _ ≤ Real.exp L * K.card := mul_le_mul_of_nonneg_right hcount (Nat.cast_nonneg _)
  exact (mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr (neg_le_neg (local_cyclic_torus_total_loss_le hp hr)))
    (Nat.cast_nonneg N)).trans hretain

end Erdos3

end

section

namespace Erdos3

noncomputable def centeredTorusLift {ι : Type*} (x : ι → AddCircle (1 : ℝ)) : ι → ℝ :=
  fun i => centeredCircleLift (x i)

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {D : Type*} [Fintype D]

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

end OAI
