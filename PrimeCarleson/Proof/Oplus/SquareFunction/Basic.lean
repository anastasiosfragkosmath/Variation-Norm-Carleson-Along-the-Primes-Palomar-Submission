module

public import PrimeCarleson.Proof.Lepingle.Prob.Dyadic
public import PrimeCarleson.Proof.Oplus.Defs.Dyadic
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Dyadic averages in `L²(ℝ)`: Pythagoras, tower property, mean-zero differences

Support for the square-function estimate of Jones–Kaufman–Rosenblatt–Wierdl at `p = 2`
(proved here) and for [O+] `varestpsi`, L2011–L2016 (L2011-L2023). The dyadic average is
`PrimeCarleson.Proof.Lepingle.dyadicAvg f k x = 2^{-k} ∫_{I_k(x)} f` (`E_k[f]` of [O+]).

* `lintegral_eq_tsum_dyadicIco`: `∫⁻ F = ∑'_m ∫⁻_{I_{k,m}} F`;
* `ConstOnDyadic k g`: `g` is constant on every dyadic interval of length `2^k`;
* `sqn_eq_add_dyadicAvg`: Pythagoras `‖f‖² = ‖E_k f‖² + ‖f - E_k f‖²`;
* `dyadicAvg_dyadicAvg_of_ge`: the tower property `E_{k'} E_k = E_{k'}` for `k ≤ k'`;
* `setIntegral_dyadicIco_dyadicDiff`: `D_j f = E_{j-1} f - E_j f` has zero mean on every
  interval of length `2^j`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

open PrimeCarleson.Proof.Lepingle

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

/-! ### The squared `L²` norm -/

/-- `‖g‖₂² = ∫⁻ ‖g‖ₑ²` equals the square of the `eLpNorm` (for a.e. strongly measurable `g`). -/
theorem lintegral_sq_eq_eLpNorm_sq {g : ℝ → ℂ} (hg : AEStronglyMeasurable g volume) :
    ∫⁻ x, ‖g x‖ₑ ^ 2 = eLpNorm g 2 volume ^ 2 := by
  have h := lintegral_rpow_enorm_eq_rpow_eLpNorm' (μ := volume) (f := g) (q := 2) two_pos
  rw [eLpNorm_eq_eLpNorm' two_ne_zero ENNReal.ofNat_ne_top hg]
  simpa [ENNReal.rpow_two] using h

/-- `L²` membership of a measurable function in terms of the squared lintegral. -/
theorem memLp_two_iff_lintegral_sq {g : ℝ → ℂ} (hg : AEStronglyMeasurable g volume) :
    MemLp g 2 volume ↔ ∫⁻ x, ‖g x‖ₑ ^ 2 < ∞ := by
  rw [lintegral_sq_eq_eLpNorm_sq hg, memLp_iff]
  constructor
  · intro h
    exact ENNReal.pow_lt_top h
  · intro h
    by_contra hcon
    rw [not_lt, top_le_iff] at hcon
    rw [hcon] at h
    simp at h

/-- A function with finite squared norm is in `L²`. -/
theorem memLp_two_of_lintegral_sq_lt_top {g : ℝ → ℂ} (hg : AEStronglyMeasurable g volume)
    (h : ∫⁻ x, ‖g x‖ₑ ^ 2 < ∞) : MemLp g 2 volume :=
  (memLp_two_iff_lintegral_sq hg).2 h

/-- The squared norm of an `L²` function is finite. -/
theorem lintegral_sq_lt_top_of_memLp {g : ℝ → ℂ} (hg : MemLp g 2 volume) :
    ∫⁻ x, ‖g x‖ₑ ^ 2 < ∞ :=
  (memLp_two_iff_lintegral_sq hg.aestronglyMeasurable).1 hg

/-! ### The dyadic partition -/

theorem mem_dyadicIco_dyadicIdx (k : ℤ) (x : ℝ) : x ∈ dyadicIco k (dyadicIdx k x) :=
  mem_dyadicIco_iff.2 rfl

/-- The dyadic intervals of length `2^k` cover `ℝ`. -/
theorem iUnion_dyadicIco (k : ℤ) : (⋃ m : ℤ, dyadicIco k m) = Set.univ :=
  Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ⟨dyadicIdx k x, mem_dyadicIco_dyadicIdx k x⟩

/-- The dyadic intervals of a fixed length are pairwise disjoint. -/
theorem pairwise_disjoint_dyadicIco_int (k : ℤ) :
    Pairwise (Function.onFun Disjoint fun m : ℤ => dyadicIco k m) := fun m m' h => by
  rw [Function.onFun, Set.disjoint_left]
  intro x hx hx'
  exact h ((mem_dyadicIco_iff.1 hx).symm.trans (mem_dyadicIco_iff.1 hx'))

/-- A lintegral over `ℝ` is the sum of the lintegrals over the dyadic intervals of length `2^k`. -/
theorem lintegral_eq_tsum_dyadicIco (k : ℤ) (F : ℝ → ℝ≥0∞) :
    ∫⁻ x, F x = ∑' m : ℤ, ∫⁻ x in dyadicIco k m, F x := by
  rw [← lintegral_iUnion (fun m => measurableSet_dyadicIco k m)
    (pairwise_disjoint_dyadicIco_int k), iUnion_dyadicIco, Measure.restrict_univ]

/-- A dyadic interval meeting a larger one lies inside it. -/
theorem dyadicIco_subset_of_mem {k N m m' : ℤ} (hk : k ≤ N) {x : ℝ} (hx : x ∈ dyadicIco k m)
    (hx' : x ∈ dyadicIco N m') : dyadicIco k m ⊆ dyadicIco N m' := by
  rcases Dyadic.toSet_subset_or_disjoint_of_k_le (I := ⟨k, m⟩) (J := ⟨N, m'⟩) hk with h | h
  · exact h
  · exact absurd (Set.disjoint_left.1 h hx hx') (by simp)

/-- `g` is constant on every dyadic interval of length `2^k`. -/
def ConstOnDyadic (k : ℤ) (g : ℝ → ℂ) : Prop :=
  ∀ x y : ℝ, dyadicIdx k x = dyadicIdx k y → g x = g y

/-- A function constant on the dyadic intervals takes one value on each of them. -/
theorem ConstOnDyadic.eq_of_mem {k m : ℤ} {g : ℝ → ℂ} (hg : ConstOnDyadic k g) {x y : ℝ}
    (hx : x ∈ dyadicIco k m) (hy : y ∈ dyadicIco k m) : g x = g y :=
  hg x y ((mem_dyadicIco_iff.1 hx).trans (mem_dyadicIco_iff.1 hy).symm)

/-- `E_k f` is constant on the dyadic intervals of length `2^k`. -/
theorem constOnDyadic_dyadicAvg (f : ℝ → ℂ) (k : ℤ) : ConstOnDyadic k (dyadicAvg f k) :=
  fun x y h => by simp only [dyadicAvg, h]

/-- A function constant on the longer intervals is constant on the shorter ones. -/
theorem ConstOnDyadic.mono {k N : ℤ} (hk : k ≤ N) {g : ℝ → ℂ} (hg : ConstOnDyadic N g) :
    ConstOnDyadic k g := by
  intro x y hxy
  have hx := mem_dyadicIco_dyadicIdx k x
  have hy : y ∈ dyadicIco k (dyadicIdx k x) := mem_dyadicIco_iff.2 hxy.symm
  have hsub := dyadicIco_subset_of_mem hk hx (mem_dyadicIco_dyadicIdx N x)
  exact hg x y ((mem_dyadicIco_iff.1 (hsub hx)).trans (mem_dyadicIco_iff.1 (hsub hy)).symm)

/-- Differences of functions constant on the dyadic intervals are constant on them. -/
theorem ConstOnDyadic.sub {k : ℤ} {g h : ℝ → ℂ} (hg : ConstOnDyadic k g)
    (hh : ConstOnDyadic k h) : ConstOnDyadic k (g - h) := fun x y hxy => by
  simp only [Pi.sub_apply, hg x y hxy, hh x y hxy]

/-! ### Integrability and linearity of the averages -/

theorem integrableOn_dyadicIco_of_memLp_two {f : ℝ → ℂ} (hf : MemLp f 2 volume) (k m : ℤ) :
    IntegrableOn f (dyadicIco k m) := by
  refine integrableOn_dyadicIco_of_memLp (p := 2) (by norm_num) ?_ k m
  simpa using hf

/-- Additivity of the dyadic average on `L²`. -/
theorem dyadicAvg_add {f g : ℝ → ℂ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) (k : ℤ)
    (x : ℝ) : dyadicAvg (f + g) k x = dyadicAvg f k x + dyadicAvg g k x := by
  simp only [dyadicAvg, Pi.add_apply]
  rw [integral_add (integrableOn_dyadicIco_of_memLp_two hf _ _)
    (integrableOn_dyadicIco_of_memLp_two hg _ _), smul_add]

/-- Subtractivity of the dyadic average on `L²`. -/
theorem dyadicAvg_sub {f g : ℝ → ℂ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) (k : ℤ)
    (x : ℝ) : dyadicAvg (f - g) k x = dyadicAvg f k x - dyadicAvg g k x := by
  simp only [dyadicAvg, Pi.sub_apply]
  rw [integral_sub (integrableOn_dyadicIco_of_memLp_two hf _ _)
    (integrableOn_dyadicIco_of_memLp_two hg _ _), smul_sub]

/-! ### Pythagoras for the dyadic average -/

theorem lintegral_sq_eq_ofReal_integral {s : Set ℝ} {g : ℝ → ℂ}
    (hg : IntegrableOn (fun x => ‖g x‖ ^ 2) s) :
    ∫⁻ x in s, ‖g x‖ₑ ^ 2 = ENNReal.ofReal (∫ x in s, ‖g x‖ ^ 2) := by
  rw [ofReal_integral_eq_lintegral_ofReal hg (Filter.Eventually.of_forall fun x => by positivity)]
  refine lintegral_congr fun x => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- Lebesgue measure restricted to a dyadic interval is finite. -/
theorem isFiniteMeasure_restrict_dyadicIco (k m : ℤ) :
    IsFiniteMeasure (volume.restrict (dyadicIco k m)) :=
  ⟨by rw [Measure.restrict_apply_univ, volume_dyadicIco]; exact ENNReal.ofReal_lt_top⟩

/-- The squared norm of an `L²` function is integrable on every set. -/
theorem integrableOn_sq_norm_of_memLp_two {f : ℝ → ℂ} (hf : MemLp f 2 volume) (s : Set ℝ) :
    IntegrableOn (fun x => ‖f x‖ ^ 2) s volume :=
  ((memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).1 hf).integrableOn

/-- Local Pythagoras on one dyadic interval: `∫_I |f|² = ∫_I |E_k f|² + ∫_I |f - E_k f|²`. -/
theorem setLIntegral_sq_eq_add_dyadicAvg {f : ℝ → ℂ} (hf : MemLp f 2 volume) (k m : ℤ) :
    ∫⁻ x in dyadicIco k m, ‖f x‖ₑ ^ 2 = (∫⁻ x in dyadicIco k m, ‖dyadicAvg f k x‖ₑ ^ 2) +
      ∫⁻ x in dyadicIco k m, ‖f x - dyadicAvg f k x‖ₑ ^ 2 := by
  have := isFiniteMeasure_restrict_dyadicIco k m
  set I := dyadicIco k m with hI
  have hmeas : MeasurableSet I := measurableSet_dyadicIco k m
  set c : ℂ := ((2 : ℝ) ^ k)⁻¹ • ∫ y in I, f y with hc
  have hav : ∀ x ∈ I, dyadicAvg f k x = c := fun x hx => dyadicAvg_of_mem hx
  have h2 : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos (by norm_num) k
  have hvol : (volume I).toReal = (2 : ℝ) ^ k := by
    rw [hI, volume_dyadicIco, ENNReal.toReal_ofReal h2.le]
  have hvolfin : volume I ≠ ∞ := by rw [hI, volume_dyadicIco]; exact ENNReal.ofReal_ne_top
  have hint : IntegrableOn f I := integrableOn_dyadicIco_of_memLp_two hf k m
  have hmean : ∫ x in I, f x = (volume I).toReal • c := by
    rw [hvol, hc, smul_smul, mul_inv_cancel₀ h2.ne', one_smul]
  have hfc : MemLp (fun x => f x - c) 2 (volume.restrict I) :=
    (hf.restrict I).sub (memLp_const c)
  have hs1 : IntegrableOn (fun x => ‖f x‖ ^ 2) I := integrableOn_sq_norm_of_memLp_two hf I
  have hs2 : IntegrableOn (fun x => ‖f x - c‖ ^ 2) I :=
    (memLp_two_iff_integrable_sq_norm hfc.aestronglyMeasurable).1 hfc
  have hs3 : IntegrableOn (fun _ : ℝ => ‖c‖ ^ 2) I := integrableOn_const hvolfin
  have hpt : ∀ x, ‖f x‖ ^ 2 =
      ‖c‖ ^ 2 + ‖f x - c‖ ^ 2 + 2 * ((f x - c) * (starRingEnd ℂ) c).re := by
    intro x
    have : f x = (f x - c) + c := by ring
    rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm]
    conv_lhs => rw [this]
    rw [Complex.normSq_add]
    ring
  have hcross_int : IntegrableOn (fun x => (f x - c) * (starRingEnd ℂ) c) I :=
    (hint.sub (integrableOn_const hvolfin)).mul_const _
  have hcross : ∫ x in I, ((f x - c) * (starRingEnd ℂ) c).re = 0 := by
    have h0 : ∫ x in I, (f x - c) * (starRingEnd ℂ) c = 0 := by
      rw [integral_mul_const, integral_sub hint (integrableOn_const hvolfin), setIntegral_const,
        hmean]
      simp [measureReal_def]
    have h1 := integral_re hcross_int
    rw [h0] at h1
    simpa using h1
  have hreal : ∫ x in I, ‖f x‖ ^ 2 =
      (volume I).toReal * ‖c‖ ^ 2 + ∫ x in I, ‖f x - c‖ ^ 2 := by
    have h1 : ∫ x in I, ‖f x‖ ^ 2 =
        ∫ x in I, (‖c‖ ^ 2 + ‖f x - c‖ ^ 2 + 2 * ((f x - c) * (starRingEnd ℂ) c).re) :=
      integral_congr_ae (Filter.Eventually.of_forall hpt)
    have h2' : IntegrableOn (fun x => 2 * ((f x - c) * (starRingEnd ℂ) c).re) I :=
      (hcross_int.re).const_mul 2
    have hs32 : IntegrableOn (fun x => ‖c‖ ^ 2 + ‖f x - c‖ ^ 2) I := hs3.add hs2
    rw [h1, integral_add hs32 h2', integral_add hs3 hs2, integral_const_mul, hcross]
    simp [measureReal_def]
  have e1 : ∫⁻ x in I, ‖dyadicAvg f k x‖ₑ ^ 2 = ∫⁻ x in I, ‖c‖ₑ ^ 2 :=
    setLIntegral_congr_fun hmeas (fun x hx => by rw [hav x hx])
  have e2 : ∫⁻ x in I, ‖f x - dyadicAvg f k x‖ₑ ^ 2 = ∫⁻ x in I, ‖f x - c‖ₑ ^ 2 :=
    setLIntegral_congr_fun hmeas (fun x hx => by rw [hav x hx])
  rw [e1, e2, lintegral_sq_eq_ofReal_integral hs1, lintegral_sq_eq_ofReal_integral hs2,
    lintegral_const, Measure.restrict_apply_univ, hreal,
    ENNReal.ofReal_add (mul_nonneg ENNReal.toReal_nonneg (by positivity))
      (integral_nonneg fun x => by positivity)]
  congr 1
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hvolfin,
    ENNReal.ofReal_pow (norm_nonneg c), ofReal_norm, mul_comm]

/-- **Pythagoras for the dyadic average**:
`∫ |f|² = ∫ |E_k f|² + ∫ |f - E_k f|²`. -/
theorem sqn_eq_add_dyadicAvg {f : ℝ → ℂ} (hf : MemLp f 2 volume) (k : ℤ) :
    ∫⁻ x, ‖f x‖ₑ ^ 2 = (∫⁻ x, ‖dyadicAvg f k x‖ₑ ^ 2) + ∫⁻ x, ‖f x - dyadicAvg f k x‖ₑ ^ 2 := by
  rw [lintegral_eq_tsum_dyadicIco k (fun x => ‖f x‖ₑ ^ 2),
    lintegral_eq_tsum_dyadicIco k (fun x => ‖dyadicAvg f k x‖ₑ ^ 2),
    lintegral_eq_tsum_dyadicIco k (fun x => ‖f x - dyadicAvg f k x‖ₑ ^ 2),
    ← ENNReal.tsum_add]
  exact tsum_congr fun m => setLIntegral_sq_eq_add_dyadicAvg hf k m

/-- `E_k` is a contraction on `L²`: `‖E_k f‖₂² ≤ ‖f‖₂²`. -/
theorem sqn_dyadicAvg_le {f : ℝ → ℂ} (hf : MemLp f 2 volume) (k : ℤ) :
    ∫⁻ x, ‖dyadicAvg f k x‖ₑ ^ 2 ≤ ∫⁻ x, ‖f x‖ₑ ^ 2 := by
  rw [sqn_eq_add_dyadicAvg hf k]
  exact le_self_add

/-! ### The tower property and the martingale differences -/

/-- A function constant on the intervals of length `2^k` is its own `k`-th dyadic average. -/
theorem dyadicAvg_eq_of_constOnDyadic {k : ℤ} {g : ℝ → ℂ} (hg : ConstOnDyadic k g) (x : ℝ) :
    dyadicAvg g k x = g x := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos (by norm_num) k
  simp only [dyadicAvg]
  rw [setIntegral_congr_fun (measurableSet_dyadicIco k _)
    (fun y hy => hg.eq_of_mem hy (mem_dyadicIco_dyadicIdx k x)), setIntegral_const,
    measureReal_def, volume_dyadicIco, ENNReal.toReal_ofReal h2.le, smul_smul,
    inv_mul_cancel₀ h2.ne', one_smul]

/-- `E_{k'} E_k f = E_{k'} f` for `k ≤ k'` (the tower property). -/
theorem dyadicAvg_dyadicAvg_of_ge {k k' : ℤ} (hk : k ≤ k') {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (x : ℝ) : dyadicAvg (dyadicAvg f k) k' x = dyadicAvg f k' x := by
  have hL : dyadicAvg (dyadicAvg f k) k' x =
      ((2 : ℝ) ^ k')⁻¹ • ∫ y in dyadicIco k' (dyadicIdx k' x), dyadicAvg f k y := rfl
  have hR : dyadicAvg f k' x =
      ((2 : ℝ) ^ k')⁻¹ • ∫ y in dyadicIco k' (dyadicIdx k' x), f y := rfl
  have := setIntegral_dyadicAvg (N := k') (k := k) (m₀ := dyadicIdx k' x) hk
    (integrableOn_dyadicIco_of_memLp_two hf k' _) Set.univ
  simp only [Set.preimage_univ, Set.inter_univ] at this
  rw [hL, hR, this]

/-- The martingale difference `D_j f = E_{j-1} f - E_j f`. -/
def dyadicDiff (f : ℝ → ℂ) (j : ℤ) : ℝ → ℂ := fun x => dyadicAvg f (j - 1) x - dyadicAvg f j x

/-- `D_j f` is constant on the dyadic intervals of length `2^{j-1}`. -/
theorem constOnDyadic_dyadicDiff (f : ℝ → ℂ) (j : ℤ) : ConstOnDyadic (j - 1) (dyadicDiff f j) :=
  (constOnDyadic_dyadicAvg f (j - 1)).sub
    ((constOnDyadic_dyadicAvg f j).mono (by omega))

/-- `D_j f` has zero mean on every dyadic interval of length `2^j`. -/
theorem setIntegral_dyadicIco_dyadicDiff {f : ℝ → ℂ} (hf : MemLp f 2 volume) (j m : ℤ) :
    ∫ x in dyadicIco j m, dyadicDiff f j x = 0 := by
  have h1 := setIntegral_dyadicAvg (N := j) (k := j - 1) (m₀ := m) (by omega)
    (integrableOn_dyadicIco_of_memLp_two hf j m) Set.univ
  simp only [Set.preimage_univ, Set.inter_univ] at h1
  have h2 := setIntegral_dyadicIco_dyadicAvg f j m
  simp only [dyadicDiff]
  rw [integral_sub (integrableOn_dyadicAvg_of_le (by omega) f) (integrableOn_dyadicAvg f j m),
    h1, h2, sub_self]

/-- `E_k D_j f = D_j f` for `j > k`. -/
theorem dyadicAvg_dyadicDiff_of_lt {f : ℝ → ℂ} {k j : ℤ} (hkj : k < j) (x : ℝ) :
    dyadicAvg (dyadicDiff f j) k x = dyadicDiff f j x :=
  dyadicAvg_eq_of_constOnDyadic ((constOnDyadic_dyadicDiff f j).mono (by omega)) x

end PrimeCarleson.Proof.Oplus
