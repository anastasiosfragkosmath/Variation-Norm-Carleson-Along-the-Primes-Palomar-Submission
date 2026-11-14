module

public import PrimeCarleson.Proof.Paper.P8.Levels
public import PrimeCarleson.Proof.Paper.P8.GeometricSum
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The entropy lemma `l:entest` (Theorem A)

Source: main paper `l:entest`, L1824–L1860, with `e:var-entropy-conclusion` (L1841–L1848),
proved here as Theorem A below by a self-contained chaining argument (the paper obtains it from
[ZK15, Lemma 2.6]), with the seminorm `V^s` and a base point in place of the norm `Ṽ^s`.

Setting: `T ⊆ ℝ` finite; `H = ℓ²(Ξ) = EuclideanSpace ℂ Ξ` with `Ξ` finite; `c : ℝ → H`; `(Y, ν)` a
measure space; `g : Y → H` with each coordinate measurable; the bilinear pairing `pairing`;
`2 < s < r` (`s` is the fixed exponent `s_e`). Hypotheses:

* (V) `∑_k ‖c_{t_k} - c_{t_{k+1}}‖^s ≤ λ^s` for every chain `t₀ < ⋯ < t_K` in `T`;
* (H1) `∫⁻ ‖⟨w, g⟩‖ₑ² dν ≤ ofReal (A₀² ‖w‖²)` for all `w`; (H2) `∫⁻ ‖g‖ₑ² dν ≤ ofReal (B₀²)`.

Results, with `γ = entropyGamma r s = r(s-2)/(s(r-2))` and
`E = entropyConst r s = 6 √(3/2) [(1 - 2^{-(s/2-1)})⁻¹ + (1 - 2^{-(1-s/r)})⁻¹]`:

* `entropy_variation_le` (a): `‖V^r(⟨c_t, g(·)⟩ : t ∈ T)‖_{L²(ν)} ≤ E A₀^{1-γ} B₀^γ λ`;
* `entropy_base_point` (b): `‖⟨c_{t₀}, g(·)⟩‖_{L²} ≤ A₀ ‖c_{t₀}‖`;
* `entropy_sup_le` (c): `‖sup_{t ∈ T} |⟨c_t, g⟩|‖_{L²} ≤ A₀ ‖c_{t₀}‖ + E A₀^{1-γ} B₀^γ λ`.

The proof uses time-ordered nets (`Nets.lean`), counting, level increments
and the chain bound (`Increments.lean`), Lemma S (`Chain.lean`), the level estimates
(`Levels.lean`), Lemma G (`GeometricSum.lean`) and Minkowski in `L²` over the finite sum of levels.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

/-- The exponent `γ(r, s) = r (s - 2) / (s (r - 2))` of `B₀ / A₀` in Theorem A (`γ(r, s_e)`). -/
def entropyGamma (r s : ℝ) : ℝ := r * (s - 2) / (s * (r - 2))

/-- The constant `E(r, s) = 6 √(3/2) [(1 - 2^{-(s-2)/2})⁻¹ + (1 - 2^{-(r-s)/r})⁻¹]` of Theorem A
(`E(r, s_e)`; the exponents are written `s/2 - 1` and `1 - s/r`). -/
def entropyConst (r s : ℝ) : ℝ :=
  6 * √(3 / 2) * ((1 - (2 : ℝ) ^ (-(s / 2 - 1)))⁻¹ + (1 - (2 : ℝ) ^ (-(1 - s / r)))⁻¹)

section Constants

variable {r s : ℝ}

/-- `γ = a / (a + b)` for `a = s/2 - 1`, `b = 1 - s/r`. -/
theorem entropyGamma_eq (hs : 2 < s) (hsr : s < r) :
    entropyGamma r s = (s / 2 - 1) / ((s / 2 - 1) + (1 - s / r)) := by
  have hr : 0 < r := by linarith
  have hs0 : 0 < s := by linarith
  have h1 : r - 2 ≠ 0 := by linarith
  have h2 : (s / 2 - 1) + (1 - s / r) = s * (r - 2) / (2 * r) := by
    field_simp
    ring
  rw [h2, entropyGamma]
  have h3 : s / 2 - 1 = (s - 2) / 2 := by ring
  rw [h3]
  field_simp

/-- `0 < γ`. -/
theorem entropyGamma_pos (hs : 2 < s) (hsr : s < r) : 0 < entropyGamma r s := by
  unfold entropyGamma
  have h1 : 0 < r - 2 := by linarith
  have h2 : 0 < s - 2 := by linarith
  have h3 : 0 < r := by linarith
  have h4 : 0 < s := by linarith
  exact div_pos (mul_pos h3 h2) (mul_pos h4 h1)

/-- `γ < 1`. -/
theorem entropyGamma_lt_one (hs : 2 < s) (hsr : s < r) : entropyGamma r s < 1 := by
  rw [entropyGamma, div_lt_one (by nlinarith)]
  nlinarith

/-- `E > 0`. -/
theorem entropyConst_pos (hs : 2 < s) (hsr : s < r) : 0 < entropyConst r s := by
  unfold entropyConst
  have h1 : (2 : ℝ) ^ (-(s / 2 - 1)) < 1 := two_rpow_neg_lt_one (by linarith)
  have hr : 0 < r := by linarith
  have h2 : (2 : ℝ) ^ (-(1 - s / r)) < 1 :=
    two_rpow_neg_lt_one (by rw [sub_pos, div_lt_one hr]; exact hsr)
  have h3 : 0 < (1 - (2 : ℝ) ^ (-(s / 2 - 1)))⁻¹ := inv_pos.2 (by linarith)
  have h4 : 0 < (1 - (2 : ℝ) ^ (-(1 - s / r)))⁻¹ := inv_pos.2 (by linarith)
  positivity

/-- The explicit bound `E(r, s) ≤ 7.35 (2 + 2.89/(s-2) + 1.45 r/(r-s))` from the second claim of
Lemma G. -/
theorem entropyConst_le (hs : 2 < s) (hsr : s < r) :
    entropyConst r s ≤ 7.35 * (2 + 2.89 / (s - 2) + 1.45 * r / (r - s)) := by
  have hr : 0 < r := by linarith
  have hx1 : 0 < s / 2 - 1 := by linarith
  have hx2 : 0 < 1 - s / r := by rw [sub_pos, div_lt_one hr]; exact hsr
  have hlog : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog0 : 0 < Real.log 2 := by linarith
  have hinv : 1 / Real.log 2 ≤ 1.443 := by
    rw [div_le_iff₀ hlog0]; nlinarith
  have hA := inv_one_sub_two_rpow_neg_le hx1
  have hB := inv_one_sub_two_rpow_neg_le hx2
  have hA' : 1 / ((s / 2 - 1) * Real.log 2) ≤ 2.886 / (s - 2) := by
    have : 1 / ((s / 2 - 1) * Real.log 2) = 2 / (s - 2) * (1 / Real.log 2) := by
      field_simp
    rw [this]
    have h2 : 0 < s - 2 := by linarith
    calc 2 / (s - 2) * (1 / Real.log 2) ≤ 2 / (s - 2) * 1.443 :=
          mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = 2.886 / (s - 2) := by ring
  have hB' : 1 / ((1 - s / r) * Real.log 2) ≤ 1.443 * r / (r - s) := by
    have : 1 / ((1 - s / r) * Real.log 2) = r / (r - s) * (1 / Real.log 2) := by
      have : r - s ≠ 0 := by linarith
      field_simp
    rw [this]
    have h2 : 0 < r - s := by linarith
    calc r / (r - s) * (1 / Real.log 2) ≤ r / (r - s) * 1.443 :=
          mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = 1.443 * r / (r - s) := by ring
  have hs2 : (0 : ℝ) < s - 2 := by linarith
  have hrs : (0 : ℝ) < r - s := by linarith
  have hc : 6 * √(3 / 2) ≤ 7.35 := by
    have : √(3 / 2) ≤ 1.225 := by
      rw [Real.sqrt_le_left (by norm_num)]
      norm_num
    linarith
  have hpos : 0 ≤ (1 - (2 : ℝ) ^ (-(s / 2 - 1)))⁻¹ + (1 - (2 : ℝ) ^ (-(1 - s / r)))⁻¹ := by
    have h1 : (2 : ℝ) ^ (-(s / 2 - 1)) < 1 := two_rpow_neg_lt_one hx1
    have h2 : (2 : ℝ) ^ (-(1 - s / r)) < 1 := two_rpow_neg_lt_one hx2
    have := inv_pos.2 (show 0 < 1 - (2 : ℝ) ^ (-(s / 2 - 1)) by linarith)
    have := inv_pos.2 (show 0 < 1 - (2 : ℝ) ^ (-(1 - s / r)) by linarith)
    linarith
  unfold entropyConst
  calc 6 * √(3 / 2) * ((1 - (2 : ℝ) ^ (-(s / 2 - 1)))⁻¹ + (1 - (2 : ℝ) ^ (-(1 - s / r)))⁻¹)
      ≤ 7.35 * ((1 - (2 : ℝ) ^ (-(s / 2 - 1)))⁻¹ + (1 - (2 : ℝ) ^ (-(1 - s / r)))⁻¹) :=
        mul_le_mul_of_nonneg_right hc hpos
    _ ≤ 7.35 * (2 + 2.89 / (s - 2) + 1.45 * r / (r - s)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        have h3 : 2.886 / (s - 2) ≤ 2.89 / (s - 2) :=
          div_le_div_of_nonneg_right (by norm_num) hs2.le
        have h4 : 1.443 * r / (r - s) ≤ 1.45 * r / (r - s) :=
          div_le_div_of_nonneg_right (by nlinarith) hrs.le
        linarith

end Constants

section Minkowski

variable {Y : Type*} [MeasurableSpace Y]

/-- Minkowski's inequality in `L^p(ν)` for a finite sum of `ℝ≥0∞`-valued functions. -/
theorem lintegral_Lp_sum_le {ι : Type*} (ν : Measure Y) (t : Finset ι) (F : ι → Y → ℝ≥0∞)
    (hF : ∀ i ∈ t, AEMeasurable (F i) ν) {p : ℝ} (hp : 1 ≤ p) :
    (∫⁻ y, (∑ i ∈ t, F i y) ^ p ∂ν) ^ (1 / p) ≤ ∑ i ∈ t, (∫⁻ y, F i y ^ p ∂ν) ^ (1 / p) := by
  classical
  have hp0 : 0 < p := by linarith
  induction t using Finset.induction_on with
  | empty => simp [ENNReal.zero_rpow_of_pos hp0, hp0]
  | insert i t hi ih =>
    simp only [Finset.sum_insert hi]
    have h1 : AEMeasurable (F i) ν := hF i (Finset.mem_insert_self _ _)
    have h2 : AEMeasurable (fun y => ∑ j ∈ t, F j y) ν :=
      Finset.aemeasurable_fun_sum _ fun j hj => hF j (Finset.mem_insert_of_mem hj)
    refine (ENNReal.lintegral_Lp_add_le h1 h2 hp).trans ?_
    exact add_le_add_right (ih fun j hj => hF j (Finset.mem_insert_of_mem hj)) _

/-- `‖2 f‖_{L²} = 2 ‖f‖_{L²}`. -/
theorem lintegral_two_mul_sq_rpow_half (ν : Measure Y) (f : Y → ℝ≥0∞) :
    (∫⁻ y, (2 * f y) ^ 2 ∂ν) ^ (1 / 2 : ℝ) = 2 * (∫⁻ y, f y ^ 2 ∂ν) ^ (1 / 2 : ℝ) := by
  have h1 : ∀ y, (2 * f y) ^ 2 = (2 : ℝ≥0∞) ^ 2 * f y ^ 2 := fun y => mul_pow _ _ _
  simp_rw [h1]
  rw [lintegral_const_mul' _ _ (by simp), ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
    ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- `levelNorm` is measurable in `w = g(y)`. -/
theorem measurable_levelNorm {Ξ : Type*} [Fintype Ξ] {g : Y → EuclideanSpace ℂ Ξ}
    (hg : ∀ ξ, Measurable fun y => g y ξ) (cc : ℕ → EuclideanSpace ℂ Ξ) (lam : ℝ) (N v : ℕ)
    (r : ℝ) : Measurable fun y => levelNorm cc lam N v r (g y) :=
  (Finset.measurable_sum _ fun _ _ =>
    ((measurable_pairing hg _).enorm).pow_const r).pow_const (1 / r)

end Minkowski

section Decomposition

variable {Ξ : Type*} [Fintype Ξ]

/-- **Pointwise decomposition**: under (V) for a finite nonempty `T ⊆ ℝ`, there
are an enumeration `cc` of `c` along `T`, a number of levels `V₀` (zero when `λ = 0`), such that for
every `w ∈ H`,
`V^r(⟨c_t, w⟩ : t ∈ T) ≤ 2 ∑_{v=1}^{V₀} F_v(w)` with `F_v = levelNorm cc λ N v r`. -/
theorem exists_level_decomposition {T : Set ℝ} (hT : T.Finite) (hTne : T.Nonempty)
    (c : ℝ → EuclideanSpace ℂ Ξ) {s lam r : ℝ} (hs : 0 < s) (hlam : 0 ≤ lam) (hr : 1 ≤ r)
    (hV : ∀ (J : ℕ) (t : Fin (J + 1) → ℝ), StrictMono t → (∀ i, t i ∈ T) →
      ∑ i : Fin J, ‖c (t i.castSucc) - c (t i.succ)‖ ^ s ≤ lam ^ s) :
    ∃ (N : ℕ) (cc : ℕ → EuclideanSpace ℂ Ξ) (V₀ : ℕ), 0 < N ∧ ChainBound cc N s lam ∧
      (lam = 0 → V₀ = 0) ∧ ∀ w : EuclideanSpace ℂ Ξ,
        PrimeCarleson.rVariationOn r T (fun t => pairing (c t) w) ≤
          2 * ∑ v ∈ Finset.Icc 1 V₀, levelNorm cc lam N v r w := by
  obtain ⟨N, u, hu, hTu⟩ := exists_enumeration hT
  have hN : 0 < N := by
    obtain ⟨t, ht⟩ := hTne
    rw [hTu] at ht
    obtain ⟨j, hj, _⟩ := ht
    exact lt_of_le_of_lt (Nat.zero_le j) hj
  set cc : ℕ → EuclideanSpace ℂ Ξ := fun j => c (u j) with hcc
  have hmem : ∀ j, j < N → u j ∈ T := fun j hj => by rw [hTu]; exact ⟨j, hj, rfl⟩
  have hVc : ChainBound cc N s lam := by
    intro K j hjm hjN
    exact hV K (fun k => u (j k)) (fun a b hab => hu (hjN a) (hjN b) (hjm hab))
      (fun k => hmem _ (hjN k))
  have hV0 : ∃ V₀ : ℕ, (∀ j < N, cc (net cc (lam / 2 ^ V₀) j) = cc j) ∧ (lam = 0 → V₀ = 0) := by
    rcases hlam.eq_or_lt with h0 | hpos
    · subst h0
      refine ⟨0, fun j hj => ?_, fun _ => rfl⟩
      have h1 : net cc (0 / 2 ^ 0) j = 0 := by
        simpa using net_eq_zero_of_chainBound hVc hs le_rfl hj
      have h2 := hVc.norm_sub_le hs le_rfl hN hj
      rw [h1]
      exact sub_eq_zero.1 (norm_le_zero_iff.1 h2)
    · obtain ⟨V₀, h⟩ := exists_exhaust (c := cc) hpos N
      exact ⟨V₀, h, fun h0 => absurd h0 hpos.ne'⟩
  obtain ⟨V₀, hex, hV0z⟩ := hV0
  refine ⟨N, cc, V₀, hN, hVc, hV0z, fun w => ?_⟩
  refine rVariationOnH_le_of_index (f := fun t => pairing (c t) w) hu hTu.le (r := r)
    (B := 2 * ∑ v ∈ Finset.Icc 1 V₀, levelNorm cc lam N v r w) ?_
  intro K j hjm hjN
  exact chain_variation_le_levels (pairingAddHom w) hVc hs hlam hex hr hjm hjN

end Decomposition

section TheoremA

variable {Ξ : Type*} [Fintype Ξ] {Y : Type*} [MeasurableSpace Y]

/-- **The `L²` majorant of Theorem A.** Under the hypotheses of Theorem A there is a measurable
`G : Y → ℝ≥0∞` with `V^r(⟨c_t, g(y)⟩ : t ∈ T) ≤ G(y)` for every `y` and
`‖G‖_{L²(ν)} ≤ E A₀^{1-γ} B₀^γ λ`. (Summation over levels by Minkowski in `L²` and Lemma G.)

Source: main paper `e:var-entropy-conclusion`, L1841–L1848. -/
theorem exists_majorant {r s : ℝ} (hs : 2 < s) (hsr : s < r) {T : Set ℝ} (hT : T.Finite)
    (hTne : T.Nonempty) (c : ℝ → EuclideanSpace ℂ Ξ) {lam : ℝ} (hlam : 0 ≤ lam)
    (hV : ∀ (J : ℕ) (t : Fin (J + 1) → ℝ), StrictMono t → (∀ i, t i ∈ T) →
      ∑ i : Fin J, ‖c (t i.castSucc) - c (t i.succ)‖ ^ s ≤ lam ^ s)
    (ν : Measure Y) (g : Y → EuclideanSpace ℂ Ξ) (hg : ∀ ξ, Measurable fun y => g y ξ)
    {A₀ B₀ : ℝ} (hA₀ : 0 ≤ A₀) (hB₀ : 0 ≤ B₀)
    (hH1 : ∀ w : EuclideanSpace ℂ Ξ,
      ∫⁻ y, ‖pairing w (g y)‖ₑ ^ 2 ∂ν ≤ ENNReal.ofReal (A₀ ^ 2 * ‖w‖ ^ 2))
    (hH2 : ∫⁻ y, ‖g y‖ₑ ^ 2 ∂ν ≤ ENNReal.ofReal (B₀ ^ 2)) :
    ∃ G : Y → ℝ≥0∞, Measurable G ∧
      (∀ y, PrimeCarleson.rVariationOn r T (fun t => pairing (c t) (g y)) ≤ G y) ∧
      (∫⁻ y, G y ^ 2 ∂ν) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal
        (entropyConst r s * A₀ ^ (1 - entropyGamma r s) * B₀ ^ entropyGamma r s * lam) := by
  have hs0 : 0 < s := by linarith
  have hr1 : 1 ≤ r := by linarith
  obtain ⟨N, cc, V₀, hN, hVc, hV0z, hdec⟩ :=
    exists_level_decomposition hT hTne c hs0 hlam hr1 hV
  refine ⟨fun y => 2 * ∑ v ∈ Finset.Icc 1 V₀, levelNorm cc lam N v r (g y),
    (Finset.measurable_sum _ fun v _ => measurable_levelNorm hg cc lam N v r).const_mul 2,
    fun y => hdec (g y), ?_⟩
  rcases hlam.eq_or_lt with h0 | hpos
  · -- `λ = 0`: no levels
    have hV00 : V₀ = 0 := hV0z h0.symm
    subst hV00
    simp [← h0]
  -- `λ > 0`
  have hγ0 := entropyGamma_pos hs hsr
  have hγ1 := entropyGamma_lt_one hs hsr
  have hr0 : 0 < r := by linarith
  have ha : 0 < s / 2 - 1 := by linarith
  have hb : 0 < 1 - s / r := by rw [sub_pos, div_lt_one hr0]; exact hsr
  rw [lintegral_two_mul_sq_rpow_half ν (fun y => ∑ v ∈ Finset.Icc 1 V₀,
    levelNorm cc lam N v r (g y))]
  -- Minkowski in `L²` over the levels
  have hmink := lintegral_Lp_sum_le ν (Finset.Icc 1 V₀)
    (fun v y => levelNorm cc lam N v r (g y))
    (fun v _ => (measurable_levelNorm hg cc lam N v r).aemeasurable) (p := 2) (by norm_num)
  simp only [ENNReal.rpow_two] at hmink
  have hlev : ∀ v ∈ Finset.Icc 1 V₀, (∫⁻ y, levelNorm cc lam N v r (g y) ^ 2 ∂ν) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (3 * √(3 / 2) * lam * min (A₀ * (2 : ℝ) ^ ((v : ℝ) * (s / 2 - 1)))
        (B₀ * (2 : ℝ) ^ (-((v : ℝ) * (1 - s / r))))) := fun v hv =>
    levelNorm_l2_le hg hVc hs hpos hN (Finset.mem_Icc.1 hv).1 hsr hA₀ hB₀ hH1 hH2
  have hsum := Finset.sum_le_sum hlev
  have hG := sum_min_geometric_le (A := A₀) (B := B₀) ha hb hA₀ hB₀ V₀
  have hc1 : 0 ≤ 3 * √(3 / 2) * lam := by positivity
  rw [← entropyGamma_eq hs hsr] at hG
  have hnn : ∀ v ∈ Finset.Icc 1 V₀, 0 ≤ 3 * √(3 / 2) * lam * min
      (A₀ * (2 : ℝ) ^ ((v : ℝ) * (s / 2 - 1))) (B₀ * (2 : ℝ) ^ (-((v : ℝ) * (1 - s / r)))) :=
    fun v _ => mul_nonneg hc1 (le_min (by positivity) (by positivity))
  calc 2 * (∫⁻ y, (∑ v ∈ Finset.Icc 1 V₀, levelNorm cc lam N v r (g y)) ^ 2 ∂ν) ^ (1 / 2 : ℝ)
      ≤ 2 * ∑ v ∈ Finset.Icc 1 V₀, (∫⁻ y, levelNorm cc lam N v r (g y) ^ 2 ∂ν) ^ (1 / 2 : ℝ) := by
        gcongr
    _ ≤ 2 * ∑ v ∈ Finset.Icc 1 V₀, ENNReal.ofReal (3 * √(3 / 2) * lam * min
          (A₀ * (2 : ℝ) ^ ((v : ℝ) * (s / 2 - 1)))
          (B₀ * (2 : ℝ) ^ (-((v : ℝ) * (1 - s / r))))) := by gcongr
    _ = ENNReal.ofReal (2 * ∑ v ∈ Finset.Icc 1 V₀, 3 * √(3 / 2) * lam * min
          (A₀ * (2 : ℝ) ^ ((v : ℝ) * (s / 2 - 1)))
          (B₀ * (2 : ℝ) ^ (-((v : ℝ) * (1 - s / r))))) := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_sum_of_nonneg hnn]
        simp
    _ ≤ ENNReal.ofReal (entropyConst r s * A₀ ^ (1 - entropyGamma r s) *
          B₀ ^ entropyGamma r s * lam) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [← Finset.mul_sum, entropyConst]
        calc 2 * (3 * √(3 / 2) * lam * ∑ v ∈ Finset.Icc 1 V₀,
              min (A₀ * (2 : ℝ) ^ ((v : ℝ) * (s / 2 - 1)))
                (B₀ * (2 : ℝ) ^ (-((v : ℝ) * (1 - s / r)))))
            ≤ 2 * (3 * √(3 / 2) * lam * (A₀ ^ (1 - entropyGamma r s) * B₀ ^ entropyGamma r s *
                ((1 - (2 : ℝ) ^ (-(s / 2 - 1)))⁻¹ + (1 - (2 : ℝ) ^ (-(1 - s / r)))⁻¹))) := by
              gcongr
          _ = _ := by ring

/-- **Theorem A(a)** (`l:entest`): for `2 < s < r`, a finite `T ⊆ ℝ`
and `c : ℝ → ℓ²(Ξ)` with (V) (every chain `t₀ < ⋯ < t_J` in `T` has
`∑ ‖c_{t_i} - c_{t_{i+1}}‖^s ≤ λ^s`), (H1) and (H2),

`‖ V^r(⟨c_t, g(·)⟩ : t ∈ T) ‖_{L²(ν)} ≤ E(r, s) A₀^{1-γ} B₀^γ λ`.

The `L²(ν)` norm is `(∫⁻ (V^r)² dν)^{1/2}` (the integrand is `ℝ≥0∞`-valued); `A₀ = 0` is allowed
(then the right side is `0`). Nothing depends on `T`, `|T|`, `Ξ`, `Y` or `g`.

Source: main paper `l:entest`, L1824–L1848, `e:var-entropy-conclusion`. -/
theorem entropy_variation_le {r s : ℝ} (hs : 2 < s) (hsr : s < r) {T : Set ℝ} (hT : T.Finite)
    (c : ℝ → EuclideanSpace ℂ Ξ) {lam : ℝ} (hlam : 0 ≤ lam)
    (hV : ∀ (J : ℕ) (t : Fin (J + 1) → ℝ), StrictMono t → (∀ i, t i ∈ T) →
      ∑ i : Fin J, ‖c (t i.castSucc) - c (t i.succ)‖ ^ s ≤ lam ^ s)
    (ν : Measure Y) (g : Y → EuclideanSpace ℂ Ξ) (hg : ∀ ξ, Measurable fun y => g y ξ)
    {A₀ B₀ : ℝ} (hA₀ : 0 ≤ A₀) (hB₀ : 0 ≤ B₀)
    (hH1 : ∀ w : EuclideanSpace ℂ Ξ,
      ∫⁻ y, ‖pairing w (g y)‖ₑ ^ 2 ∂ν ≤ ENNReal.ofReal (A₀ ^ 2 * ‖w‖ ^ 2))
    (hH2 : ∫⁻ y, ‖g y‖ₑ ^ 2 ∂ν ≤ ENNReal.ofReal (B₀ ^ 2)) :
    (∫⁻ y, PrimeCarleson.rVariationOn r T (fun t => pairing (c t) (g y)) ^ 2 ∂ν) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal
        (entropyConst r s * A₀ ^ (1 - entropyGamma r s) * B₀ ^ entropyGamma r s * lam) := by
  rcases T.eq_empty_or_nonempty with rfl | hTne
  · have h0 : ∀ y, PrimeCarleson.rVariationOn r (∅ : Set ℝ)
        (fun t => pairing (c t) (g y)) = 0 := fun y =>
      rVariationOnH_empty r (fun t : ℝ => pairing (c t) (g y))
    simp [h0]
  · obtain ⟨G, -, hVG, hG⟩ :=
      exists_majorant hs hsr hT hTne c hlam hV ν g hg hA₀ hB₀ hH1 hH2
    have h1 : ∫⁻ y, PrimeCarleson.rVariationOn r T (fun t => pairing (c t) (g y)) ^ 2 ∂ν ≤
        ∫⁻ y, G y ^ 2 ∂ν := lintegral_mono fun y => pow_le_pow_left' (hVG y) 2
    exact (ENNReal.rpow_le_rpow h1 (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans hG

/-- **Theorem A(a)** with (V) stated as the `ℓ²(Ξ)`-valued seminorm bound `V^s(c_t : t ∈ T) ≤ λ`
(`rVariationOnH`, equivalent to the chain-wise form by `rVariationOnH_le_ofReal_iff`). -/
theorem entropy_variation_le_of_rVariationOnH {r s : ℝ} (hs : 2 < s) (hsr : s < r) {T : Set ℝ}
    (hT : T.Finite) (c : ℝ → EuclideanSpace ℂ Ξ) {lam : ℝ} (hlam : 0 ≤ lam)
    (hV : rVariationOnH s T c ≤ ENNReal.ofReal lam)
    (ν : Measure Y) (g : Y → EuclideanSpace ℂ Ξ) (hg : ∀ ξ, Measurable fun y => g y ξ)
    {A₀ B₀ : ℝ} (hA₀ : 0 ≤ A₀) (hB₀ : 0 ≤ B₀)
    (hH1 : ∀ w : EuclideanSpace ℂ Ξ,
      ∫⁻ y, ‖pairing w (g y)‖ₑ ^ 2 ∂ν ≤ ENNReal.ofReal (A₀ ^ 2 * ‖w‖ ^ 2))
    (hH2 : ∫⁻ y, ‖g y‖ₑ ^ 2 ∂ν ≤ ENNReal.ofReal (B₀ ^ 2)) :
    (∫⁻ y, PrimeCarleson.rVariationOn r T (fun t => pairing (c t) (g y)) ^ 2 ∂ν) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal
        (entropyConst r s * A₀ ^ (1 - entropyGamma r s) * B₀ ^ entropyGamma r s * lam) :=
  entropy_variation_le hs hsr hT c hlam
    ((rVariationOnH_le_ofReal_iff (by linarith) hlam).1 hV) ν g hg hA₀ hB₀ hH1 hH2

/-- **Theorem A(b)** (base point): under (H1),
`‖⟨c_{t₀}, g(·)⟩‖_{L²(ν)} ≤ A₀ ‖c_{t₀}‖` (stated for any vector `w = c_{t₀}`); it is (H1). -/
theorem entropy_base_point (ν : Measure Y) (g : Y → EuclideanSpace ℂ Ξ) {A₀ : ℝ} (hA₀ : 0 ≤ A₀)
    (hH1 : ∀ w : EuclideanSpace ℂ Ξ,
      ∫⁻ y, ‖pairing w (g y)‖ₑ ^ 2 ∂ν ≤ ENNReal.ofReal (A₀ ^ 2 * ‖w‖ ^ 2))
    (w : EuclideanSpace ℂ Ξ) :
    (∫⁻ y, ‖pairing w (g y)‖ₑ ^ 2 ∂ν) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (A₀ * ‖w‖) :=
  rpow_half_le_ofReal (by positivity) ((hH1 w).trans (by rw [mul_pow]))

/-- **Theorem A(c)** (supremum): for `t₀ ∈ T`,
`‖ sup_{t∈T} |⟨c_t, g(·)⟩| ‖_{L²} ≤ A₀ ‖c_{t₀}‖ + E(r, s) A₀^{1-γ} B₀^γ λ`. Pointwise
`|⟨c_t, g⟩| ≤ |⟨c_{t₀}, g⟩| + V^r(⟨c_·, g⟩)` by the two-point chain `{t, t₀}`.

Source: main paper `l:entest`, L1824–L1860 (the supremum bound of its proof). -/
theorem entropy_sup_le {r s : ℝ} (hs : 2 < s) (hsr : s < r) {T : Set ℝ} (hT : T.Finite)
    (c : ℝ → EuclideanSpace ℂ Ξ) {lam : ℝ} (hlam : 0 ≤ lam)
    (hV : ∀ (J : ℕ) (t : Fin (J + 1) → ℝ), StrictMono t → (∀ i, t i ∈ T) →
      ∑ i : Fin J, ‖c (t i.castSucc) - c (t i.succ)‖ ^ s ≤ lam ^ s)
    (ν : Measure Y) (g : Y → EuclideanSpace ℂ Ξ) (hg : ∀ ξ, Measurable fun y => g y ξ)
    {A₀ B₀ : ℝ} (hA₀ : 0 ≤ A₀) (hB₀ : 0 ≤ B₀)
    (hH1 : ∀ w : EuclideanSpace ℂ Ξ,
      ∫⁻ y, ‖pairing w (g y)‖ₑ ^ 2 ∂ν ≤ ENNReal.ofReal (A₀ ^ 2 * ‖w‖ ^ 2))
    (hH2 : ∫⁻ y, ‖g y‖ₑ ^ 2 ∂ν ≤ ENNReal.ofReal (B₀ ^ 2)) {t₀ : ℝ} (ht₀ : t₀ ∈ T) :
    (∫⁻ y, (⨆ t ∈ T, ‖pairing (c t) (g y)‖ₑ) ^ 2 ∂ν) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (A₀ * ‖c t₀‖) + ENNReal.ofReal
        (entropyConst r s * A₀ ^ (1 - entropyGamma r s) * B₀ ^ entropyGamma r s * lam) := by
  obtain ⟨G, hGm, hVG, hG⟩ :=
    exists_majorant hs hsr hT ⟨t₀, ht₀⟩ c hlam hV ν g hg hA₀ hB₀ hH1 hH2
  have hr0 : 0 < r := by linarith
  have hpt : ∀ y, (⨆ t ∈ T, ‖pairing (c t) (g y)‖ₑ) ≤ ‖pairing (c t₀) (g y)‖ₑ + G y := by
    intro y
    refine iSup₂_le fun t ht => ?_
    exact (enorm_le_enorm_add_rVariationOnH (h := fun t => pairing (c t) (g y)) hr0 ht ht₀).trans
      (add_le_add_right (hVG y) _)
  have hf : AEMeasurable (fun y => ‖pairing (c t₀) (g y)‖ₑ) ν :=
    (measurable_pairing hg (c t₀)).enorm.aemeasurable
  calc (∫⁻ y, (⨆ t ∈ T, ‖pairing (c t) (g y)‖ₑ) ^ 2 ∂ν) ^ (1 / 2 : ℝ)
      ≤ (∫⁻ y, (‖pairing (c t₀) (g y)‖ₑ + G y) ^ 2 ∂ν) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow (lintegral_mono fun y => pow_le_pow_left' (hpt y) 2) (by norm_num)
    _ ≤ (∫⁻ y, ‖pairing (c t₀) (g y)‖ₑ ^ 2 ∂ν) ^ (1 / 2 : ℝ) +
          (∫⁻ y, G y ^ 2 ∂ν) ^ (1 / 2 : ℝ) := by
        have := ENNReal.lintegral_Lp_add_le (μ := ν) (p := 2)
          (f := fun y => ‖pairing (c t₀) (g y)‖ₑ) (g := G) hf hGm.aemeasurable (by norm_num)
        simpa [ENNReal.rpow_two] using this
    _ ≤ _ := add_le_add (entropy_base_point ν g hA₀ hH1 (c t₀)) hG

end TheoremA

end PrimeCarleson.Proof.Paper
