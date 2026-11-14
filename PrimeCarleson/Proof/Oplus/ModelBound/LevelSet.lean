module

public import PrimeCarleson.Proof.Oplus.ModelBound.Dilation
public import PrimeCarleson.Proof.Oplus.ModelBound.Separation
public import PrimeCarleson.Proof.Common.WeakLp

/-!
# The level set bound for every finite family ([O+] L1138-L1153, L1265-L1282)

Source: [O+] `halfgbound`, L1138–L1144; [O+] `halfgbound`, L1265–L1282; [O+] `csrhobound`,
L1134–L1137 (L1131-L1153, L1265-L1282), for `ρ` a `1`- or `2`-index with `m, n ∈ {1, …, 4}`, any
profile choice and any linearizing data (no hypothesis on `Ξ`).

* `levelSet_separated` (the level set reduction of [O+] L1134-L1153 for a separated family): for
  `|F| ∈ (0, ∞)`, `|f| ≤ 1_F`, `λ > 0`: `|{|𝒮^ρ f| > λ}| ≤ (C/λ)^p |F|`. This is the contradiction
  argument of L1145-L1153 applied to `halfgbound_separated`; the a priori finiteness of
  `|E_λ|` (L1145-L1147) is avoided by applying the half-measure bound to
  `E_λ ∩ [-n, n]` for `n` large;
* `levelSet_family` (the same for an arbitrary finite family, with `C' = N^{1+1/p} C`, `N` the
  number of colours of `exists_separated_colouring`): the finite family is split into `N`
  separated subfamilies and the level sets are combined by `Common.measure_norm_sum_gt_le` (the
  weak `L^p` quasi-triangle inequality).

The combination of the subfamilies is not additive at the level of (halfgbound) (the exceptional
measure `|E|/2` is not); it is done at the level of `|{|𝒮 f| > λ}|`, which is, and (halfgbound) for
the full family follows by Chebyshev.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

open PrimeCarleson.Proof.Common

/-- Real bookkeeping: `(C/λ)^p a < e` implies `C (a/e)^{1/p} < λ`. -/
theorem mul_rpow_lt_of_rpow_mul_lt {C lam p a e : ℝ} (hC : 0 < C) (hlam : 0 < lam) (hp : 0 < p)
    (ha : 0 < a) (he : 0 < e) (h : (C / lam) ^ p * a < e) : C * (a / e) ^ (1 / p) < lam := by
  have hu : 0 < (C / lam) ^ p := by positivity
  have h1 : a / e < (lam / C) ^ p := by
    rw [div_lt_iff₀ he]
    have : (lam / C) ^ p = ((C / lam) ^ p)⁻¹ := by
      rw [← Real.inv_rpow (by positivity), inv_div]
    rw [this, inv_mul_eq_div, lt_div_iff₀ hu]
    linarith
  have h2 : (a / e) ^ (1 / p) < lam / C := by
    calc (a / e) ^ (1 / p) < ((lam / C) ^ p) ^ (1 / p) :=
          Real.rpow_lt_rpow (by positivity) h1 (by positivity)
      _ = lam / C := by
          rw [← Real.rpow_mul (by positivity)]
          have : p * (1 / p) = 1 := by field_simp
          rw [this, Real.rpow_one]
  calc C * (a / e) ^ (1 / p) < C * (lam / C) := mul_lt_mul_of_pos_left h2 hC
    _ = lam := by field_simp

/-- **`csrhobound`** ([O+] L1134-L1153) for a separated family:
`|{|𝒮^ρ f| > λ}| ≤ C^p λ^{-p} |F|` for `|f| ≤ 1_F`, with `C = C(p, r)` the constant of
`halfgbound_separated`. -/
theorem levelSet_separated {r p : ℝ} (hr : 2 < r) (hp1 : Real.conjExponent r ≤ p)
    (hp2 : p < 2 * r / (r - 2)) {C₁ C₂ C₃ : ℝ} (hC : AdmissibleConstants C₁ C₂ C₃)
    (hC₂ : C₂ = 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ρ : Idx} [Fact ρ.IsOneOrTwo], ρ.IsStd → ∀ (ch : ProfileChoice)
      {f : ℝ → ℂ} {F : Set ℝ}, MeasurableSet F → volume F ≠ 0 → volume F ≠ ⊤ →
      AEStronglyMeasurable f volume → (∀ᵐ x, ‖f x‖ ≤ F.indicator (fun _ => (1 : ℝ)) x) →
      ∀ (L : Linearization r) (𝔓 : Finset (Multitile ρ)),
      Separated C₁ C₂ C₃ (𝔓 : Set (Multitile ρ)) → ∀ lam : ℝ, 0 < lam →
      volume {x | lam < ‖modelOp ch L 𝔓 f x‖} ≤ ENNReal.ofReal ((C / lam) ^ p) * volume F := by
  have hr1 : 1 < r := by linarith
  have hp0 : 0 < p := lt_of_lt_of_le (one_pos.trans (one_lt_conjExponent hr1)) hp1
  obtain ⟨C, hC0, hhalf⟩ := halfgbound_separated hr hp1 hp2 hC hC₂
  refine ⟨C, hC0, ?_⟩
  intro ρ _ hρ ch f F hF hF0 hFt hfm hfF L 𝔓 hsep lam hlam
  by_contra hcon
  push Not at hcon
  set T := modelOp ch L 𝔓 f with hT
  have hTm : Measurable T := measurable_modelOp ch L 𝔓 f
  have hU : {x | lam < ‖T x‖} = ⋃ n : ℕ, {x | lam < ‖T x‖} ∩ Icc (-(n : ℝ)) n := by
    ext x
    simp only [mem_iUnion, mem_inter_iff, mem_Icc, Set.mem_ofPred_eq]
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_ge |x|
      exact ⟨n, hx, abs_le.1 hn⟩
    · rintro ⟨n, hx, -⟩
      exact hx
  have hmono : Monotone fun n : ℕ => {x | lam < ‖T x‖} ∩ Icc (-(n : ℝ)) n := by
    intro m n hmn x hx
    have := (Nat.cast_le (α := ℝ)).2 hmn
    exact ⟨hx.1, by linarith [hx.2.1], by linarith [hx.2.2]⟩
  rw [hU, hmono.measure_iUnion] at hcon
  obtain ⟨n, hn⟩ := lt_iSup_iff.1 hcon
  set E' : Set ℝ := {x | lam < ‖T x‖} ∩ Icc (-(n : ℝ)) n with hE'
  have hE'm : MeasurableSet E' :=
    (measurableSet_lt measurable_const hTm.norm).inter measurableSet_Icc
  have hEt : volume E' ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := volume (Icc (-(n : ℝ)) n)) (by simp [Real.volume_Icc])
      (measure_mono inter_subset_right)
  have hE0 : volume E' ≠ 0 := (pos_of_gt hn).ne'
  have key := hhalf hρ ch hF hF0 hFt hfm hfF hE'm hE0 hEt L 𝔓 hsep
  have hae : 0 < (volume F).toReal := ENNReal.toReal_pos hF0 hFt
  have hee : 0 < (volume E').toReal := ENNReal.toReal_pos hE0 hEt
  have hlt : C * ((volume F).toReal / (volume E').toReal) ^ (1 / p) < lam := by
    refine mul_rpow_lt_of_rpow_mul_lt hC0 hlam hp0 hae hee ?_
    have := ENNReal.toReal_strict_mono hEt hn
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at this
  have hsub : E' ⊆ {x | x ∈ E' ∧ C * ((volume F).toReal / (volume E').toReal) ^ (1 / p) <
      ‖modelOp ch L 𝔓 f x‖} := fun x hx => ⟨hx, lt_trans hlt hx.1⟩
  exact absurd ((measure_mono hsub).trans key) (not_le.2 (ENNReal.half_lt_self hE0 hEt))

/-- Real bookkeeping for the combination of `N` separated subfamilies:
`N (C₀ N / λ)^p = (N^{1+1/p} C₀ / λ)^p`. -/
theorem nat_mul_rpow_eq {N : ℕ} (hN : 0 < N) {C₀ lam p : ℝ} (hC₀ : 0 < C₀) (hlam : 0 < lam)
    (hp : 0 < p) :
    (N : ℝ) * (C₀ / (lam / N)) ^ p = ((N : ℝ) ^ (1 + 1 / p) * C₀ / lam) ^ p := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have e1 : C₀ / (lam / N) = (N : ℝ) * (C₀ / lam) := by field_simp
  have e2 : (N : ℝ) ^ (1 + 1 / p) * C₀ / lam = (N : ℝ) ^ (1 + 1 / p) * (C₀ / lam) := by ring
  rw [e1, e2, Real.mul_rpow hN'.le (by positivity), Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_mul hN'.le]
  have : (1 + 1 / p) * p = p + 1 := by field_simp
  rw [this, Real.rpow_add hN', Real.rpow_one]
  ring

/-- **The separation reduction and the level set reduction for an
arbitrary finite family** of `ρ`-multitiles ([O+] L1265-L1282, L1134-L1153): the level set bound
`|{|𝒮^ρ f| > λ}| ≤ (C/λ)^p |F|` for every finite family (no separation assumption), with
`C = N^{1+1/p} C₀`, where `C₀` is the constant of `levelSet_separated` and `N` the number of
colours of `exists_separated_colouring` (`N = 60` for the constants `12, 2, 11/10`). -/
theorem levelSet_family {r p : ℝ} (hr : 2 < r) (hp1 : Real.conjExponent r ≤ p)
    (hp2 : p < 2 * r / (r - 2)) {C₁ C₂ C₃ : ℝ} (hC : AdmissibleConstants C₁ C₂ C₃)
    (hC₂ : C₂ = 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ρ : Idx} [Fact ρ.IsOneOrTwo], ρ.IsStd → ∀ (ch : ProfileChoice)
      {f : ℝ → ℂ} {F : Set ℝ}, MeasurableSet F → volume F ≠ 0 → volume F ≠ ⊤ →
      AEStronglyMeasurable f volume → (∀ᵐ x, ‖f x‖ ≤ F.indicator (fun _ => (1 : ℝ)) x) →
      ∀ (L : Linearization r) (𝔓 : Finset (Multitile ρ)), ∀ lam : ℝ, 0 < lam →
      volume {x | lam < ‖modelOp ch L 𝔓 f x‖} ≤ ENNReal.ofReal ((C / lam) ^ p) * volume F := by
  have hr1 : 1 < r := by linarith
  have hp0 : 0 < p := lt_of_lt_of_le (one_pos.trans (one_lt_conjExponent hr1)) hp1
  obtain ⟨C₀, hC₀, hsepset⟩ := levelSet_separated hr hp1 hp2 hC hC₂
  have hC₁0 : 0 < C₁ := by linarith [hC.one_le, hC.lt₁, hC.lt₂]
  obtain ⟨s, t, hs, ht, hcol⟩ := exists_separated_colouring hC₁0 hC.lt₁
  have hN : 0 < s * t := Nat.mul_pos hs ht
  generalize s * t = N at hN hcol
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨(N : ℝ) ^ (1 + 1 / p) * C₀, by positivity, ?_⟩
  intro ρ _ hρ ch f F hF hF0 hFt hfm hfF L 𝔓 lam hlam
  classical
  obtain ⟨col, hcolsep⟩ := hcol ρ
  set Tc : Fin N → ℝ → ℂ := fun c =>
    modelOp ch L (𝔓.filter fun P => col P = c) f with hTc
  have hsum : ∀ x, modelOp ch L 𝔓 f x = ∑ c : Fin N, Tc c x := by
    intro x
    simp only [hTc, modelOp]
    rw [Finset.sum_fiberwise]
  have e : {x | lam < ‖modelOp ch L 𝔓 f x‖} = {x | lam < ‖∑ c ∈ Finset.univ, Tc c x‖} := by
    ext x
    simp only [Set.mem_ofPred_eq, hsum]
  have h1 := measure_norm_sum_gt_le (μ := volume) (Finset.univ : Finset (Fin N)) Tc hlam.le
  rw [Finset.card_univ, Fintype.card_fin] at h1
  have hlamN : 0 < lam / N := div_pos hlam hN'
  have hterm : ∀ c : Fin N, volume {x | lam / N < ‖Tc c x‖} ≤
      ENNReal.ofReal ((C₀ / (lam / N)) ^ p) * volume F := by
    intro c
    exact hsepset hρ ch hF hF0 hFt hfm hfF L _
      ((hcolsep c).mono fun P hP => (Finset.mem_filter.1 hP).2) _ hlamN
  rw [e]
  refine h1.trans ?_
  calc ∑ c : Fin N, volume {x | lam / N < ‖Tc c x‖}
      ≤ ∑ _c : Fin N, ENNReal.ofReal ((C₀ / (lam / N)) ^ p) * volume F :=
        Finset.sum_le_sum fun c _ => hterm c
    _ = (N : ℝ≥0∞) * (ENNReal.ofReal ((C₀ / (lam / N)) ^ p) * volume F) := by
        simp [Finset.sum_const, nsmul_eq_mul]
    _ = ENNReal.ofReal ((N : ℝ) * (C₀ / (lam / N)) ^ p) * volume F := by
        rw [ENNReal.ofReal_mul hN'.le, ← mul_assoc]
        simp
    _ = ENNReal.ofReal (((N : ℝ) ^ (1 + 1 / p) * C₀ / lam) ^ p) * volume F := by
        rw [nat_mul_rpow_eq hN hC₀ hlam hp0]

end PrimeCarleson.Proof.Oplus
