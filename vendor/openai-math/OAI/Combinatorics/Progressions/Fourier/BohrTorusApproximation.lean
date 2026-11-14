/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Fourier/BohrTorusApproximation.lean
Changes: Lean module/public-import conversion; unneeded declarations and imports were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.LinearCutoff
public import OAI.Combinatorics.Progressions.Estimates.UniformProductAccuracy
public import OAI.Combinatorics.Progressions.Estimates.MonotoneRegularPoint
public import OAI.Combinatorics.Progressions.Fourier.CyclicAffineCharacterPhase
public import OAI.Combinatorics.Progressions.Probability.MassConvolution
@[expose] public section

namespace OAI

section

namespace Erdos3.CyclicBohr.Set

open Finset
open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

def ndilate (B : Set N) (t : ℝ≥0) : Set N := B.dilate t

@[simp] theorem radius_ndilate (B : Set N) (t : ℝ≥0) :
    (B.ndilate t).radius = t * B.radius := by simp [ndilate]

@[simp] theorem rank_ndilate (B : Set N) (t : ℝ≥0) :
    (B.ndilate t).rank = B.rank := rfl

@[simp] theorem ndilate_one (B : Set N) : B.ndilate 1 = B := by simp [ndilate]

@[simp] theorem ndilate_ndilate (B : Set N) (s t : ℝ≥0) :
    (B.ndilate s).ndilate t = B.ndilate (t * s) := by simp [ndilate]

theorem carrier_ndilate_mono {B : Set N} {s t : ℝ≥0} (hst : s ≤ t) :
    (B.ndilate s).carrier ⊆ (B.ndilate t).carrier :=
  B.dilate_mono s.coe_nonneg (by exact_mod_cast hst)

def IsRankRegular (B : Set N) : Prop :=
  let d : ℕ := 2 * max B.rank 1
  ∀ kappa : ℝ≥0,
    kappa ≤ 1 / (100 * (d : ℝ≥0)) →
      (1 - 100 * (d : ℝ) * (kappa : ℝ)) * (B.carrier.card : ℝ) ≤
          ((B.ndilate (1 - kappa)).carrier.card : ℝ) ∧
      ((B.ndilate (1 + kappa)).carrier.card : ℝ) ≤
          (1 + 100 * (d : ℝ) * (kappa : ℝ)) * (B.carrier.card : ℝ)

theorem isRankRegular_ndilate_iff (B : Set N) (rho : ℝ≥0) :
    (B.ndilate rho).IsRankRegular ↔
      let d : ℕ := 2 * max B.rank 1
      ∀ kappa : ℝ≥0,
        kappa ≤ 1 / (100 * (d : ℝ≥0)) →
          (1 - 100 * (d : ℝ) * (kappa : ℝ)) *
                ((B.ndilate rho).carrier.card : ℝ) ≤
              ((B.ndilate ((1 - kappa) * rho)).carrier.card : ℝ) ∧
          ((B.ndilate ((1 + kappa) * rho)).carrier.card : ℝ) ≤
              (1 + 100 * (d : ℝ) * (kappa : ℝ)) *
                ((B.ndilate rho).carrier.card : ℝ) := by
  simp [IsRankRegular, mul_comm]

theorem log_card_growth_lt_five_mul_rank (B : Set N) (hB : 0 < B.radius) :
    Real.log ((B.ndilate (5 / 4)).carrier.card : ℝ) -
        Real.log ((B.ndilate (1 / 4)).carrier.card : ℝ) <
      5 * (2 * max B.rank 1 : ℕ) := by
  classical
  let d : ℕ := 2 * max B.rank 1
  have hcard : (B.ndilate (5 / 4)).carrier.card ≤
      9 ^ (3 * B.rank) * (B.ndilate (1 / 4)).carrier.card := by
    calc
      (B.ndilate (5 / 4)).carrier.card ≤ (B.ndilate 2).carrier.card :=
        Finset.card_le_card (carrier_ndilate_mono
          (show (5 / 4 : NNReal) ≤ 2 by
            rw [div_le_iff₀ (by norm_num : (0 : NNReal) < 4)]
            norm_num))
      _ ≤ 9 ^ (3 * B.rank) * (B.ndilate (1 / 4)).carrier.card :=
        by simpa [ndilate] using card_two_le_nine_pow_three_rank_mul_card_quarter B hB
  have hsmall_pos : (0 : ℝ) < (B.ndilate (1 / 4)).carrier.card := by
    exact_mod_cast (B.ndilate (1 / 4)).carrier_nonempty.card_pos
  have hlarge_pos : (0 : ℝ) < (B.ndilate (5 / 4)).carrier.card := by
    exact_mod_cast (B.ndilate (5 / 4)).carrier_nonempty.card_pos
  have hlog := Real.log_le_log hlarge_pos (show
      ((B.ndilate (5 / 4)).carrier.card : ℝ) ≤
        ((9 ^ (3 * B.rank) * (B.ndilate (1 / 4)).carrier.card : ℕ) : ℝ) by
      exact_mod_cast hcard)
  rw [Nat.cast_mul, Nat.cast_pow, Real.log_mul (by positivity) hsmall_pos.ne',
    Real.log_pow] at hlog
  have hdpos : (0 : ℝ) < d := by
    exact_mod_cast (show 0 < d by simp [d])
  have hlog9 : Real.log (9 : ℝ) < 10 / 3 := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 9)
      (by norm_num : (9 : ℝ) ≤ 2 ^ 4)
    rw [Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    linarith [Real.log_two_lt_d9]
  have hmain : (3 * B.rank : ℕ) * Real.log (9 : ℝ) < 5 * d := by
    have hpos : (0 : ℝ) < (max B.rank 1 : ℕ) := by positivity
    have hrank : (B.rank : ℝ) ≤ (max B.rank 1 : ℕ) := by exact_mod_cast le_max_left B.rank 1
    push_cast
    calc
      3 * (B.rank : ℝ) * Real.log 9 ≤ 3 * (max B.rank 1 : ℕ) * Real.log 9 := by gcongr
      _ < 3 * (max B.rank 1 : ℕ) * (10 / 3) := by gcongr
      _ = 5 * d := by dsimp [d]; push_cast; ring
  dsimp [d] at hmain ⊢
  linarith

noncomputable def normalizedLogCard (B : Set N) (s : ℝ) : ℝ :=
  Real.log ((B.ndilate s.toNNReal).carrier.card : ℝ) /
    (2 * max B.rank 1 : ℕ)

theorem normalizedLogCard_monotone (B : Set N) :
    Monotone B.normalizedLogCard := by
  intro s t hst
  dsimp [normalizedLogCard]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Real.log_le_log
  · exact_mod_cast (B.ndilate s.toNNReal).carrier_nonempty.card_pos
  · exact_mod_cast Finset.card_le_card
      (carrier_ndilate_mono (B := B) (Real.toNNReal_mono hst))

theorem normalizedLogCard_buffer_growth (B : Set N) (hB : 0 < B.radius) :
    B.normalizedLogCard (5 / 4) - B.normalizedLogCard (1 / 4) < 5 := by
  classical
  have h := log_card_growth_lt_five_mul_rank B hB
  have hd : (0 : ℝ) < (2 * max B.rank 1 : ℕ) := by positivity
  have h54 : Real.toNNReal (5 / 4 : ℝ) = (5 / 4 : NNReal) := by
    apply NNReal.eq
    rw [Real.coe_toNNReal _ (by norm_num)]
    norm_num
  have h14 : Real.toNNReal (1 / 4 : ℝ) = (1 / 4 : NNReal) := by
    apply NNReal.eq
    rw [Real.coe_toNNReal _ (by norm_num)]
    norm_num
  dsimp [normalizedLogCard]
  rw [h54, h14]
  rw [div_sub_div_same]
  exact (div_lt_iff₀ hd).2 (by simpa [mul_comm] using h)

theorem exists_rankRegular_ndilate (B : Set N) (hB : 0 < B.radius) :
    ∃ rho : NNReal, 1 / 2 ≤ rho ∧ rho ≤ 1 ∧
      (B.ndilate rho).IsRankRegular := by
  classical
  let d : ℕ := 2 * max B.rank 1
  obtain ⟨r, hr, hlip⟩ := exists_regular_point_of_monotone
    B.normalizedLogCard (normalizedLogCard_monotone B)
      (normalizedLogCard_buffer_growth B hB)
  let rho : NNReal := r.toNNReal
  have hrho : (rho : ℝ) = r := Real.coe_toNNReal r (by linarith [hr.1])
  have hrho_half : (1 / 2 : NNReal) ≤ rho := by
    rw [← NNReal.coe_le_coe, hrho]
    norm_num
    exact hr.1
  have hrho_one : rho ≤ 1 := by
    rw [← NNReal.coe_le_coe, hrho]
    norm_num
    exact hr.2
  refine ⟨rho, hrho_half, hrho_one, ?_⟩
  rw [isRankRegular_ndilate_iff]
  dsimp only [rank_ndilate]
  intro kappa hkappa
  have hdposN : 0 < d := by simp [d]
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hdposN
  have hkappa_one : kappa ≤ 1 := by
    apply hkappa.trans
    rw [div_le_one]
    · exact_mod_cast (show 1 ≤ 100 * d by omega)
    · positivity
  have hkappa_real : (kappa : ℝ) ≤ 1 / (100 * (d : ℝ)) := by
    exact_mod_cast hkappa
  let sminus : NNReal := (1 - kappa) * rho
  let splus : NNReal := (1 + kappa) * rho
  have hkreal : (kappa : ℝ) ≤ 1 / 100 := by
    calc
      (kappa : ℝ) ≤ 1 / (100 * (d : ℝ)) := hkappa_real
      _ ≤ 1 / 100 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
        have hd_one : (1 : ℝ) ≤ d := by
          exact_mod_cast (show 1 ≤ d by dsimp [d]; omega)
        nlinarith
  have hrho_real : (1 / 2 : ℝ) ≤ rho ∧ (rho : ℝ) ≤ 1 := by
    exact ⟨by exact_mod_cast hrho_half, by exact_mod_cast hrho_one⟩
  have hsminus_buf : (sminus : ℝ) ∈ _root_.Set.Icc (1 / 4 : ℝ) (5 / 4) := by
    dsimp [sminus]
    rw [NNReal.coe_sub hkappa_one]
    simp only [NNReal.coe_one]
    have hk_lower : (99 / 100 : ℝ) ≤ 1 - (kappa : ℝ) := by
      nlinarith
    constructor
    · calc
        (1 / 4 : ℝ) ≤ (99 / 100) * (1 / 2) := by norm_num
        _ ≤ (1 - (kappa : ℝ)) * (rho : ℝ) := by
          exact mul_le_mul hk_lower hrho_real.1 (by norm_num)
            (sub_nonneg.mpr (by exact_mod_cast hkappa_one))
    · calc
        (1 - (kappa : ℝ)) * (rho : ℝ) ≤ 1 * rho :=
          mul_le_mul_of_nonneg_right (sub_le_self 1 (by positivity)) (by positivity)
        _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hrho_real.2 (by norm_num)
        _ ≤ 5 / 4 := by norm_num
  have hsplus_buf : (splus : ℝ) ∈ _root_.Set.Icc (1 / 4 : ℝ) (5 / 4) := by
    dsimp [splus]
    constructor <;> nlinarith
  have hdistminus : |(sminus : ℝ) - r| ≤ (kappa : ℝ) := by
    rw [← hrho]
    dsimp [sminus]
    rw [NNReal.coe_sub hkappa_one]
    simp only [NNReal.coe_one]
    have hrnonneg : (0 : ℝ) ≤ rho := by positivity
    rw [show (1 - (kappa : ℝ)) * (rho : ℝ) - rho = -(kappa * rho) by ring,
      abs_neg, abs_of_nonneg (mul_nonneg (by positivity) hrnonneg)]
    nlinarith [hrho_real.2]
  have hdistplus : |(splus : ℝ) - r| ≤ (kappa : ℝ) := by
    rw [← hrho]
    dsimp [splus]
    have hrnonneg : (0 : ℝ) ≤ rho := by positivity
    rw [show (1 + (kappa : ℝ)) * (rho : ℝ) - rho = kappa * rho by ring,
      abs_of_nonneg (mul_nonneg (by positivity) hrnonneg)]
    nlinarith [hrho_real.2]
  have hlipminus := hlip (sminus : ℝ) hsminus_buf
  have hlipplus := hlip (splus : ℝ) hsplus_buf
  simp only [normalizedLogCard, Real.toNNReal_coe,
    show r.toNNReal = rho by rfl] at hlipminus hlipplus
  change
    |Real.log ((B.ndilate sminus).carrier.card : ℝ) / d -
      Real.log ((B.ndilate rho).carrier.card : ℝ) / d| ≤
        60 * |(sminus : ℝ) - r| at hlipminus
  change
    |Real.log ((B.ndilate splus).carrier.card : ℝ) / d -
      Real.log ((B.ndilate rho).carrier.card : ℝ) / d| ≤
        60 * |(splus : ℝ) - r| at hlipplus
  rw [div_sub_div_same, abs_div, abs_of_pos hdpos] at hlipminus hlipplus
  have hlogminus :
      Real.log ((B.ndilate rho).carrier.card : ℝ) -
          Real.log ((B.ndilate sminus).carrier.card : ℝ) ≤
        60 * d * (kappa : ℝ) := by
    have habs := (div_le_iff₀ hdpos).mp hlipminus
    calc
      _ ≤ |Real.log ((B.ndilate sminus).carrier.card : ℝ) -
          Real.log ((B.ndilate rho).carrier.card : ℝ)| := by
        rw [abs_sub_comm]
        exact le_abs_self _
      _ ≤ 60 * |(sminus : ℝ) - r| * d := habs
      _ ≤ 60 * (kappa : ℝ) * d := by gcongr
      _ = 60 * d * (kappa : ℝ) := by ring
  have hlogplus :
      Real.log ((B.ndilate splus).carrier.card : ℝ) -
          Real.log ((B.ndilate rho).carrier.card : ℝ) ≤
        60 * d * (kappa : ℝ) := by
    have habs := (div_le_iff₀ hdpos).mp hlipplus
    calc
      _ ≤ |Real.log ((B.ndilate splus).carrier.card : ℝ) -
          Real.log ((B.ndilate rho).carrier.card : ℝ)| := le_abs_self _
      _ ≤ 60 * |(splus : ℝ) - r| * d := habs
      _ ≤ 60 * (kappa : ℝ) * d := by gcongr
      _ = 60 * d * (kappa : ℝ) := by ring
  let u : ℝ := 100 * d * (kappa : ℝ)
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by
    dsimp [u]
    calc
      100 * (d : ℝ) * (kappa : ℝ) ≤
          100 * d * (1 / (100 * d)) := by gcongr
      _ = 1 := by field_simp
  have hslope : 60 * d * (kappa : ℝ) = (3 / 5 : ℝ) * u := by
    dsimp [u]
    ring
  constructor
  · change (1 - u) * ((B.ndilate rho).carrier.card : ℝ) ≤
      ((B.ndilate sminus).carrier.card : ℝ)
    by_cases hu : u = 1
    · rw [hu]
      norm_num
    · have hu_lt : u < 1 := lt_of_le_of_ne hu1 hu
      have honeu : 0 < 1 - u := sub_pos.mpr hu_lt
      have hcenter : (0 : ℝ) < (B.ndilate rho).carrier.card := by
        exact_mod_cast (B.ndilate rho).carrier_nonempty.card_pos
      have hinner : (0 : ℝ) < (B.ndilate sminus).carrier.card := by
        exact_mod_cast (B.ndilate sminus).carrier_nonempty.card_pos
      rw [← Real.log_le_log_iff (mul_pos honeu hcenter) hinner]
      rw [Real.log_mul (sub_ne_zero.mpr (Ne.symm hu)) hcenter.ne']
      have hlogone := Real.log_le_sub_one_of_pos honeu
      rw [hslope] at hlogminus
      nlinarith
  · change ((B.ndilate splus).carrier.card : ℝ) ≤
      (1 + u) * ((B.ndilate rho).carrier.card : ℝ)
    have hcenter : (0 : ℝ) < (B.ndilate rho).carrier.card := by
      exact_mod_cast (B.ndilate rho).carrier_nonempty.card_pos
    have houter : (0 : ℝ) < (B.ndilate splus).carrier.card := by
      exact_mod_cast (B.ndilate splus).carrier_nonempty.card_pos
    rw [← Real.log_le_log_iff houter (mul_pos (by linarith) hcenter)]
    rw [Real.log_mul (by linarith) hcenter.ne']
    have hlogone := Real.le_log_one_add_of_nonneg hu0
    have hfrac : (3 / 5 : ℝ) * u ≤ 2 * u / (u + 2) := by
      rw [le_div_iff₀ (by linarith)]
      nlinarith
    rw [hslope] at hlogplus
    linarith

end Erdos3.CyclicBohr.Set

end

section

namespace Erdos3

open scoped BigOperators NNReal

variable {ι : Type*} [Fintype ι]

end Erdos3

end

section

namespace Erdos3.CyclicBohr.Set

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.CyclicBohr.Set

end

section

namespace Erdos3.CyclicBohr.Set

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

theorem add_mem_ndilate {B : Set N} {r s : ℝ≥0} {x y : ZMod N}
    (hx : x ∈ B.ndilate r) (hy : y ∈ B.ndilate s) :
    x + y ∈ B.ndilate (r + s) := by
  simpa only [ndilate, NNReal.coe_add] using add_mem_dilate r.coe_nonneg s.coe_nonneg hx hy

theorem sub_mem_ndilate {B : Set N} {r s : ℝ≥0} {x y : ZMod N}
    (hx : x ∈ B.ndilate r) (hy : y ∈ B.ndilate s) :
    x - y ∈ B.ndilate (r + s) := by
  simpa only [ndilate, NNReal.coe_add] using sub_mem_dilate r.coe_nonneg s.coe_nonneg hx hy

theorem uniformMass_translation_le_shell (B : Set N) {kappa : ℝ≥0}
    (hkappa : kappa ≤ 1) {t : ZMod N} (ht : t ∈ B.ndilate kappa) :
    ∑ x : ZMod N, |realUniformMass B.carrier (x - t) - realUniformMass B.carrier x| ≤
      (((B.ndilate (1 + kappa)).carrier.card : ℝ) - (B.ndilate (1 - kappa)).carrier.card) /
        B.carrier.card := by
  apply Erdos3.uniformMass_translation_le_shell
  · intro x hx
    constructor
    · have h := carrier_ndilate_mono (B := B) (show 1 - kappa ≤ 1 from tsub_le_self) hx
      simpa only [ndilate_one] using h
    · have h := sub_mem_ndilate (B := B) hx ht
      simpa only [tsub_add_cancel_of_le hkappa, ndilate_one, mem_iff, mem_carrier] using h
  · intro x hx
    rcases hx with hx | hx
    · have h := carrier_ndilate_mono (B := B) (show (1 : ℝ≥0) ≤ 1 + kappa from le_self_add)
      apply h
      simpa only [ndilate_one] using hx
    · have h := add_mem_ndilate (B := B) (r := 1) (s := kappa)
        (x := x - t) (y := t) (by simpa only [ndilate_one, mem_iff, mem_carrier] using hx) ht
      simpa only [sub_add_cancel, mem_iff, mem_carrier] using h

theorem uniformMass_translation_le_of_rankRegular {B : Set N} (hreg : B.IsRankRegular)
    {kappa : ℝ≥0} (hkappa : kappa ≤ 1 / (100 * (2 * max B.rank 1 : ℕ) : ℝ≥0))
    {t : ZMod N} (ht : t ∈ B.ndilate kappa) :
    ∑ x : ZMod N, |realUniformMass B.carrier (x - t) - realUniformMass B.carrier x| ≤
      400 * ((max B.rank 1 : ℕ) : ℝ) * (kappa : ℝ) := by
  have hkappa_one : kappa ≤ 1 := by
    apply hkappa.trans
    rw [div_le_one]
    · exact_mod_cast (show 1 ≤ 100 * (2 * max B.rank 1) by omega)
    · positivity
  have hcards := hreg kappa hkappa
  have hcenter : (0 : ℝ) < B.carrier.card := by exact_mod_cast B.card_pos
  apply (uniformMass_translation_le_shell B hkappa_one ht).trans
  rw [div_le_iff₀ hcenter]
  push_cast at hcards ⊢
  nlinarith [hcards.1, hcards.2]

end Erdos3.CyclicBohr.Set

end

section

namespace Erdos3.CyclicBohr.Set

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.CyclicBohr.Set

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.LocalConvolution

end

section

namespace Erdos3.CyclicBohr.Set

open scoped NNReal

variable {N : ℕ} [NeZero N]

def whole : Set N := ofFrequencies {0} 1 (by norm_num)

@[simp] theorem rank_whole : (whole : Set N).rank = 1 := by simp [whole]

@[simp] theorem radius_whole : (whole : Set N).radius = 1 := rfl

@[simp] theorem carrier_whole : (whole : Set N).carrier = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro x
  simp [whole, mem_carrier, ofFrequencies]

theorem exists_controlled_regular_subdilate (B : Set N) (hB : 0 < B.radius)
    (r : ℝ≥0) (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ C : Set N, C.frequencies = B.frequencies ∧ C.IsRankRegular ∧
      (r : ℝ) * B.radius / 2 ≤ C.radius ∧ C.radius ≤ r * B.radius ∧
      C.carrier ⊆ (B.ndilate r).carrier ∧
      ((r : ℝ) / 4) ^ (4 * B.rank) * (B.carrier.card : ℝ) ≤ C.carrier.card := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hr1R : (r : ℝ) ≤ 1 := by exact_mod_cast hr1
  have hB0 : 0 < (B.ndilate r).radius := by
    rw [radius_ndilate]
    exact mul_pos hrR hB
  obtain ⟨rho, hrho0, hrho1, hreg⟩ := exists_rankRegular_ndilate (B.ndilate r) hB0
  let C := (B.ndilate r).ndilate rho
  have hrho0R : (1 / 2 : ℝ) ≤ rho := by exact_mod_cast hrho0
  have hrho1R : (rho : ℝ) ≤ 1 := by exact_mod_cast hrho1
  have hC : C.radius = (rho : ℝ) * ((r : ℝ) * B.radius) := by simp only [C, radius_ndilate]
  refine ⟨C, rfl, hreg, ?_, ?_, ?_, ?_⟩
  · rw [hC]
    nlinarith [mul_nonneg hrR.le hB.le]
  · rw [hC]
    nlinarith [mul_nonneg hrR.le hB.le]
  · have h := carrier_ndilate_mono (B := B.ndilate r) hrho1
    simpa only [ndilate_one] using h
  · have hprod : 0 < (rho : ℝ) * r := mul_pos (by linarith) hrR
    have hprod1 : (rho : ℝ) * r ≤ 1 := by nlinarith
    have hvol := relative_card_lower_bound B hB hprod hprod1
    have hlower : (r : ℝ) / 4 ≤ ((rho : ℝ) * r) / 2 := by nlinarith
    have hcost := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (show (0 : ℝ) ≤ r / 4 by positivity) hlower (4 * B.rank))
      (Nat.cast_nonneg B.carrier.card : (0 : ℝ) ≤ B.carrier.card)
    have hfull := hcost.trans hvol
    simpa only [C, ndilate, dilate_dilate] using hfull

end Erdos3.CyclicBohr.Set

end

section

namespace Erdos3.CyclicBohr.Set

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.CyclicBohr.Set

end

section

namespace Erdos3.CyclicBohr.Set

open scoped NNReal

variable {N : ℕ} [NeZero N]

@[simp] theorem carrier_ndilate_whole (t : ℝ≥0) :
    ((whole : Set N).ndilate t).carrier = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro x
  simp [mem_carrier, whole, ndilate, ofFrequencies, dilate]

theorem isRankRegular_whole : (whole : Set N).IsRankRegular := by
  intro kappa _
  simp only [rank_whole, max_self, Nat.mul_one, Nat.cast_ofNat, carrier_whole,
    carrier_ndilate_whole]
  have hcard : (0 : ℝ) ≤ (Finset.univ : Finset (ZMod N)).card := Nat.cast_nonneg _
  constructor <;> nlinarith [mul_nonneg kappa.coe_nonneg hcard]

end Erdos3.CyclicBohr.Set

end

section

namespace Erdos3.CyclicBohr.Set

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.CyclicBohr.Set

end

end OAI
