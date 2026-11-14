/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Fourier/TranslatedBohrDifference.lean
Changes: Lean module/public-import conversion; unneeded declarations and imports were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Fourier.BohrTorusApproximation
public import OAI.Combinatorics.Progressions.Fourier.FiniteFourierSmoothing
@[expose] public section

namespace OAI

section

open Finset
open scoped BigOperators

namespace Erdos3

noncomputable section

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

def massCoeff (w : G → ℝ) (ψ : AddChar G ℂ) : ℂ :=
  ∑ x : G, (w x : ℂ) * ψ x

theorem massCoeff_realUniformMass (A : Finset G) (ψ : AddChar G ℂ) :
    massCoeff (realUniformMass A) ψ =
      ((A.card : ℝ)⁻¹ : ℂ) * Chang.spectrumSum A ψ := by
  calc
    massCoeff (realUniformMass A) ψ =
        ∑ x ∈ A, ((A.card : ℝ)⁻¹ : ℂ) * ψ x := by
      rw [massCoeff, ← Finset.sum_subset (s₁ := A) (s₂ := Finset.univ)]
      · apply Finset.sum_congr rfl
        intro x hx
        simp [realUniformMass, hx]
      · simp
      · intro x hxU hxA
        simp [realUniformMass, hxA]
    _ = ((A.card : ℝ)⁻¹ : ℂ) * Chang.spectrumSum A ψ := by
      rw [Chang.spectrumSum, Finset.mul_sum]

theorem norm_massCoeff_realUniformMass_lt_half_of_not_mem_largeSpectrum
    (A : Finset G) (hA : A.Nonempty) (ψ : AddChar G ℂ)
    (hψ : ψ ∉ Chang.largeSpectrum A (1 / 2)) :
    ‖massCoeff (realUniformMass A) ψ‖ < 1 / 2 := by
  have hcard : (0 : ℝ) < A.card := by
    exact_mod_cast hA.card_pos
  have hspectrum :
      ‖Chang.spectrumSum A ψ‖ < (1 / 2 : ℝ) * A.card := by
    apply lt_of_not_ge
    intro h
    exact hψ (Chang.mem_largeSpectrum.mpr h)
  calc
    ‖massCoeff (realUniformMass A) ψ‖ =
        (A.card : ℝ)⁻¹ * ‖Chang.spectrumSum A ψ‖ := by
      rw [massCoeff_realUniformMass, norm_mul]
      simp [norm_inv]
    _ < (A.card : ℝ)⁻¹ *
        ((1 / 2 : ℝ) * A.card) :=
      mul_lt_mul_of_pos_left hspectrum (inv_pos.mpr hcard)
    _ = 1 / 2 := by field_simp

omit [DecidableEq G] in

theorem massCoeff_massConvolution (f g : G → ℝ) (ψ : AddChar G ℂ) :
    massCoeff (massConvolution f g) ψ = massCoeff f ψ * massCoeff g ψ := by
  unfold massCoeff massConvolution
  push_cast
  calc
    ∑ x : G, (∑ y : G, (f y : ℂ) * (g (x - y) : ℂ)) * ψ x =
        ∑ x : G, ∑ y : G, (f y : ℂ) * (g (x - y) : ℂ) * ψ x := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_mul]
    _ = ∑ y : G, ∑ x : G, (f y : ℂ) * (g (x - y) : ℂ) * ψ x :=
      Finset.sum_comm
    _ =
        ∑ y : G, ((f y : ℂ) * ψ y) *
          ∑ z : G, (g z : ℂ) * ψ z := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [Finset.mul_sum]
      refine Fintype.sum_equiv (Equiv.subRight y) _ _ fun z ↦ ?_
      have hψ : ψ z = ψ y * ψ (z - y) := by
        calc
          ψ z = ψ (y + (z - y)) := congrArg ψ (by simp)
          _ = ψ y * ψ (z - y) := AddChar.map_add_eq_mul ψ y (z - y)
      simp only [Equiv.subRight_apply]
      rw [hψ]
      ring
    _ = (∑ y : G, (f y : ℂ) * ψ y) *
        ∑ z : G, (g z : ℂ) * ψ z := by
      simpa using
        (Finset.sum_mul (univ : Finset G) (fun y ↦ (f y : ℂ) * ψ y)
          (∑ z : G, (g z : ℂ) * ψ z)).symm

theorem massCoeff_convolutionPower (f : G → ℝ) (ψ : AddChar G ℂ) :
    ∀ n, massCoeff (convolutionPower f n) ψ = massCoeff f ψ ^ n := by
  intro n
  induction n with
  | zero =>
      unfold massCoeff
      rw [Fintype.sum_eq_single 0]
      · simp [realUniformMass]
      · intro y hy
        simp [realUniformMass, hy]
  | succ n ihn =>
      rw [convolutionPower_succ, massCoeff_massConvolution, ihn, pow_succ]

omit [DecidableEq G] in

theorem norm_massCoeff_le_sum {w : G → ℝ} (hw : ∀ x, 0 ≤ w x)
    (ψ : AddChar G ℂ) :
    ‖massCoeff w ψ‖ ≤ ∑ x : G, w x := by
  unfold massCoeff
  calc
    ‖∑ x : G, (w x : ℂ) * ψ x‖ ≤
        ∑ x : G, ‖(w x : ℂ) * ψ x‖ := norm_sum_le _ _
    _ = ∑ x : G, w x := by
      apply Finset.sum_congr rfl
      intro x hx
      simp [hw x]

end

end Erdos3

end

section

open Finset
open scoped BigOperators NNReal

namespace Erdos3

noncomputable section

variable {N : ℕ} [NeZero N]

theorem convolutionPower_realUniformMass_support
    (B : CyclicBohr.Set N) (σ : ℝ≥0) :
    ∀ n x, convolutionPower (realUniformMass (B.ndilate σ).carrier) n x ≠ 0 →
      x ∈ (B.ndilate ((n : ℝ≥0) * σ)).carrier := by
  intro n
  induction n with
  | zero =>
      intro x hx
      have hx0 : x = 0 := by
        simpa using
          (realUniformMass_ne_zero_iff (singleton_nonempty 0) x).mp hx
      subst x
      simpa only [Nat.cast_zero, zero_mul, CyclicBohr.Set.mem_iff,
        CyclicBohr.Set.mem_carrier] using (B.ndilate 0).zero_mem
  | succ n ihn =>
      intro x hx
      rw [convolutionPower_succ, massConvolution] at hx
      obtain ⟨y, -, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
      have hypow : convolutionPower (realUniformMass (B.ndilate σ).carrier) n y ≠ 0 :=
        (mul_ne_zero_iff.mp hy).1
      have hysmall : realUniformMass (B.ndilate σ).carrier (x - y) ≠ 0 :=
        (mul_ne_zero_iff.mp hy).2
      have hyB := ihn y hypow
      have hxyB : x - y ∈ (B.ndilate σ).carrier :=
        (realUniformMass_ne_zero_iff
          (B.ndilate σ).carrier_nonempty (x - y)).mp hysmall
      have hadd := CyclicBohr.Set.add_mem_ndilate hyB hxyB
      have hxsum : y + (x - y) = x := by simp
      rw [hxsum] at hadd
      simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul,
        CyclicBohr.Set.mem_iff, CyclicBohr.Set.mem_carrier] using hadd

def bohrSmoothingMeasure (B : CyclicBohr.Set N) (σ : ℝ≥0) (n : ℕ) : (ZMod N) → ℝ :=
  massConvolution
    (realUniformMass (B.ndilate (1 + (n : ℝ≥0) * σ)).carrier)
    (convolutionPower (realUniformMass (B.ndilate σ).carrier) n)

theorem bohrSmoothingMeasure_nonneg (B : CyclicBohr.Set N) (σ : ℝ≥0) (n : ℕ) (x : (ZMod N)) :
    0 ≤ bohrSmoothingMeasure B σ n x := by
  exact massConvolution_nonneg
    (realUniformMass_nonneg _)
    (convolutionPower_nonneg (realUniformMass_nonneg _) n) x

theorem sum_bohrSmoothingMeasure (B : CyclicBohr.Set N) (σ : ℝ≥0) (n : ℕ) :
    ∑ x : (ZMod N), bohrSmoothingMeasure B σ n x = 1 := by
  rw [bohrSmoothingMeasure, sum_massConvolution,
    sum_realUniformMass (B.ndilate (1 + (n : ℝ≥0) * σ)).carrier_nonempty,
    sum_convolutionPower
      (sum_realUniformMass (B.ndilate σ).carrier_nonempty), one_mul]

theorem bohrSmoothingMeasure_apply_of_mem
    (B : CyclicBohr.Set N) (σ : ℝ≥0) (n : ℕ) {x : (ZMod N)} (hx : x ∈ B.carrier) :
    bohrSmoothingMeasure B σ n x =
      (((B.ndilate (1 + (n : ℝ≥0) * σ)).carrier.card : ℝ)⁻¹) := by
  rw [bohrSmoothingMeasure, massConvolution_comm]
  simp only [massConvolution]
  calc
    ∑ t : (ZMod N), convolutionPower (realUniformMass (B.ndilate σ).carrier) n t *
          realUniformMass (B.ndilate (1 + (n : ℝ≥0) * σ)).carrier (x - t) =
        ∑ t : (ZMod N), convolutionPower (realUniformMass (B.ndilate σ).carrier) n t *
          (((B.ndilate (1 + (n : ℝ≥0) * σ)).carrier.card : ℝ)⁻¹) := by
      apply Finset.sum_congr rfl
      intro t ht
      by_cases hνt :
          convolutionPower (realUniformMass (B.ndilate σ).carrier) n t = 0
      · simp [hνt]
      · have htB : t ∈ (B.ndilate ((n : ℝ≥0) * σ)).carrier :=
          convolutionPower_realUniformMass_support B σ n t hνt
        have hxt : x - t ∈
            (B.ndilate (1 + (n : ℝ≥0) * σ)).carrier := by
          exact CyclicBohr.Set.sub_mem_ndilate
            (B := B) (r := 1) (s := (n : ℝ≥0) * σ)
            (by simpa only [CyclicBohr.Set.ndilate_one, CyclicBohr.Set.mem_iff,
              CyclicBohr.Set.mem_carrier] using hx) htB
        rw [realUniformMass_apply_mem hxt]
    _ = (∑ t : (ZMod N),
          convolutionPower (realUniformMass (B.ndilate σ).carrier) n t) *
        (((B.ndilate (1 + (n : ℝ≥0) * σ)).carrier.card : ℝ)⁻¹) := by
      rw [Finset.sum_mul]
    _ = (((B.ndilate (1 + (n : ℝ≥0) * σ)).carrier.card : ℝ)⁻¹) := by
      rw [sum_convolutionPower
        (sum_realUniformMass (B.ndilate σ).carrier_nonempty)]
      simp

theorem card_dilate_one_add_le_two_mul
    {B : CyclicBohr.Set N} (hreg : B.IsRankRegular) {σ : ℝ≥0} (n : ℕ)
    (hsmall : (n : ℝ≥0) * σ ≤
      1 / (100 * (2 * max B.rank 1 : ℕ) : ℝ≥0)) :
    (B.ndilate (1 + (n : ℝ≥0) * σ)).carrier.card ≤
      2 * B.carrier.card := by
  let κ : ℝ≥0 := (n : ℝ≥0) * σ
  let d : ℕ := 2 * max B.rank 1
  have hcards := hreg κ (by simpa [κ, d] using hsmall)
  have hfactor : (1 + 100 * (d : ℝ) * (κ : ℝ)) ≤ 2 := by
    have hsmallR : (κ : ℝ) ≤ 1 / (100 * (d : ℝ)) := by
      exact_mod_cast (show κ ≤ 1 / (100 * (d : ℝ≥0)) by
        simpa [κ, d] using hsmall)
    have hd : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by simp [d])
    calc
      1 + 100 * (d : ℝ) * (κ : ℝ) ≤
          1 + 100 * (d : ℝ) * (1 / (100 * (d : ℝ))) := by gcongr
      _ = 2 := by field_simp; ring
  have hcardR :
      ((B.ndilate (1 + κ)).carrier.card : ℝ) ≤
        2 * (B.carrier.card : ℝ) := by
    calc
      ((B.ndilate (1 + κ)).carrier.card : ℝ) ≤
          (1 + 100 * (d : ℝ) * (κ : ℝ)) * (B.carrier.card : ℝ) := by
        simpa [κ, d] using hcards.2
      _ ≤ 2 * (B.carrier.card : ℝ) := by gcongr
  exact_mod_cast hcardR

theorem norm_massCoeff_bohrSmoothingMeasure_le
    (B : CyclicBohr.Set N) (σ : ℝ≥0) (n : ℕ) (ψ : AddChar (ZMod N) ℂ) :
    ‖massCoeff (bohrSmoothingMeasure B σ n) ψ‖ ≤
      ‖massCoeff (realUniformMass (B.ndilate σ).carrier) ψ‖ ^ n := by
  rw [bohrSmoothingMeasure, massCoeff_massConvolution,
    massCoeff_convolutionPower, norm_mul, norm_pow]
  have houter :
      ‖massCoeff (realUniformMass
        (B.ndilate (1 + (n : ℝ≥0) * σ)).carrier) ψ‖ ≤ 1 := by
    simpa [sum_realUniformMass
      (B.ndilate (1 + (n : ℝ≥0) * σ)).carrier_nonempty] using
      norm_massCoeff_le_sum
        (w := realUniformMass
          (B.ndilate (1 + (n : ℝ≥0) * σ)).carrier)
        (realUniformMass_nonneg _) ψ
  exact mul_le_of_le_one_left (by positivity) houter

end

end Erdos3

end

section

open AddChar Finset
open scoped BigOperators NNReal

namespace Erdos3

noncomputable section

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

private lemma normalizedSpectrum_eq (A : Finset G) (psi : AddChar G ℂ) :
    (∑ x : G, (realUniformMass A x : ℂ) * psi x) =
      ((A.card : ℂ)⁻¹) * Chang.spectrumSum A psi := by
  classical
  rw [Chang.spectrumSum, Finset.mul_sum]
  calc
    (∑ x : G, (realUniformMass A x : ℂ) * psi x) =
        ∑ x : G, if x ∈ A then ((A.card : ℂ)⁻¹) * psi x else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x ∈ A <;> simp [realUniformMass, hx]
    _ = ∑ x ∈ A, ((A.card : ℂ)⁻¹) * psi x := by
      rw [← Finset.sum_filter]
      have hfilter :
          (Finset.univ.filter fun x : G ↦ x ∈ A) = A := by
        ext x
        simp
      rw [hfilter]

private lemma normalizedSpectrum_translate (A : Finset G)
    (psi : AddChar G ℂ) (t : G) :
    (1 - psi t) * (∑ x : G, (realUniformMass A x : ℂ) * psi x) =
      ∑ x : G,
        ((realUniformMass A x - realUniformMass A (x - t) : ℝ) : ℂ) *
          psi x := by
  classical
  have htranslate :
      (∑ x : G, (realUniformMass A (x - t) : ℂ) * psi x) =
        psi t * ∑ x : G, (realUniformMass A x : ℂ) * psi x := by
    rw [← (Equiv.addRight t).sum_comp]
    · change
        (∑ x : G, (realUniformMass A ((x + t) - t) : ℂ) * psi (x + t)) =
          psi t * ∑ x : G, (realUniformMass A x : ℂ) * psi x
      simp_rw [add_sub_cancel_right, map_add_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    · simp
  push_cast
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib, htranslate]
  ring

variable {N : ℕ} [NeZero N]

theorem norm_one_sub_le_of_mem_largeSpectrum
    {C : CyclicBohr.Set N} (hreg : C.IsRankRegular) {eta : ℝ} (heta : 0 < eta)
    {sigma : ℝ≥0}
    (hsigma : sigma ≤ 1 / (100 * (2 * max C.rank 1 : ℕ) : ℝ≥0))
    {psi : AddChar (ZMod N) ℂ} (hpsi : psi ∈ Chang.largeSpectrum C.carrier eta)
    {t : (ZMod N)} (ht : t ∈ (C.ndilate sigma).carrier) :
    ‖1 - psi t‖ ≤
      400 * ((max C.rank 1 : ℕ) : ℝ) * (sigma : ℝ) / eta := by
  classical
  let F : ℂ := ∑ x : (ZMod N), (realUniformMass C.carrier x : ℂ) * psi x
  have hcard : (0 : ℝ) < C.carrier.card := by
    exact_mod_cast C.carrier_nonempty.card_pos
  have hFnorm : ‖F‖ = ‖Chang.spectrumSum C.carrier psi‖ / C.carrier.card := by
    dsimp [F]
    rw [normalizedSpectrum_eq, norm_mul]
    simp [div_eq_inv_mul]
  have hlarge : eta ≤ ‖F‖ := by
    rw [hFnorm, le_div_iff₀ hcard]
    exact Chang.mem_largeSpectrum.mp hpsi
  have hphase :
      ‖1 - psi t‖ * ‖F‖ ≤
        ∑ x : (ZMod N),
          |realUniformMass C.carrier (x - t) -
            realUniformMass C.carrier x| := by
    rw [← norm_mul, normalizedSpectrum_translate C.carrier psi t]
    calc
      ‖∑ x : (ZMod N),
          ((realUniformMass C.carrier x -
              realUniformMass C.carrier (x - t) : ℝ) : ℂ) * psi x‖ ≤
          ∑ x : (ZMod N),
            ‖((realUniformMass C.carrier x -
                realUniformMass C.carrier (x - t) : ℝ) : ℂ) * psi x‖ :=
        norm_sum_le _ _
      _ = ∑ x : (ZMod N),
          |realUniformMass C.carrier (x - t) -
            realUniformMass C.carrier x| := by
        apply Finset.sum_congr rfl
        intro x _
        rw [norm_mul]
        rw [Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
        simp
  have htranslation :=
    CyclicBohr.Set.uniformMass_translation_le_of_rankRegular
      hreg hsigma ht
  have hmul :
      ‖1 - psi t‖ * eta ≤
        400 * ((max C.rank 1 : ℕ) : ℝ) * (sigma : ℝ) := by
    calc
      ‖1 - psi t‖ * eta ≤ ‖1 - psi t‖ * ‖F‖ :=
        mul_le_mul_of_nonneg_left hlarge (norm_nonneg _)
      _ ≤ ∑ x : (ZMod N),
          |realUniformMass C.carrier (x - t) -
            realUniformMass C.carrier x| := hphase
      _ ≤ 400 * ((max C.rank 1 : ℕ) : ℝ) * (sigma : ℝ) := htranslation
  exact (le_div_iff₀ heta).2 hmul

theorem norm_one_sub_le_of_mem_largeSpectrum_half
    {C : CyclicBohr.Set N} (hreg : C.IsRankRegular) {sigma : ℝ≥0}
    (hsigma : sigma ≤ 1 / (100 * (2 * max C.rank 1 : ℕ) : ℝ≥0))
    {psi : AddChar (ZMod N) ℂ} (hpsi : psi ∈ Chang.largeSpectrum C.carrier (1 / 2))
    {t : (ZMod N)} (ht : t ∈ (C.ndilate sigma).carrier) :
    ‖1 - psi t‖ ≤ 800 * ((max C.rank 1 : ℕ) : ℝ) * (sigma : ℝ) := by
  classical
  have h := norm_one_sub_le_of_mem_largeSpectrum hreg (eta := (1 / 2 : ℝ))
    (by norm_num) hsigma hpsi ht
  convert h using 1
  ring

end

end Erdos3

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.LocalConvolution

end

section

namespace Erdos3.CyclicBohr.Set

open scoped NNReal Pointwise

variable {N : ℕ} [NeZero N]

end Erdos3.CyclicBohr.Set

end

section

namespace Erdos3.CyclicBohr.Set

open scoped Pointwise NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.CyclicBohr.Set

end

end OAI
