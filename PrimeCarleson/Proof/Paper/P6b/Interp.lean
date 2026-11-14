module

public import PrimeCarleson.Proof.Paper.P6b.Crude
public import PrimeCarleson.Proof.Common.Interpolation

/-!
# Interpolating the `ℓ²` power saving with the crude `ℓ^s` bound

Source: main paper `l:red-var-l2`, L1546–L1564, L1566–L1573, L1717–L1728 and L1729–L1732. The
interpolation is the Marcinkiewicz theorem for subadditive operators on finitely supported sequences
(`Common.exists_eLpNorm_count_le_interpolation_finsupp_ofReal`), with free exponents `s` and `θ`,
`1/p = θ/2 + (1-θ)/s`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Common

/-- **Marcinkiewicz interpolation between `ℓ²` and `ℓ^s`** for a subadditive operator on
finitely supported sequences, with free exponents: if `1/p = θ/2 + (1-θ)/s`, `θ ∈ (0, 1)`,
`s ≠ 2`, there is an absolute `C` (depending on the exponents only) with
`‖T f‖_p ≤ C M₀^θ M₁^{1-θ} ‖f‖_p` whenever `‖T f‖₂ ≤ M₀ ‖f‖₂` and `‖T f‖_s ≤ M₁ ‖f‖_s`. -/
theorem interp_two_s {s p θ : ℝ} (hs : 0 < s) (hs2 : s ≠ 2) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hp : 1 / p = θ / 2 + (1 - θ) / s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : (ℤ →₀ ℂ) → ℤ → ℝ≥0∞) (M₀ M₁ : ℝ), 0 < M₀ → 0 < M₁ →
      (∀ f g : ℤ →₀ ℂ, ∀ x, T (f + g) x ≤ T f x + T g x) →
      (∀ f : ℤ →₀ ℂ, eLpNorm (T f) (ENNReal.ofReal 2) Measure.count ≤
        ENNReal.ofReal M₀ * eLpNorm (⇑f) (ENNReal.ofReal 2) Measure.count) →
      (∀ f : ℤ →₀ ℂ, eLpNorm (T f) (ENNReal.ofReal s) Measure.count ≤
        ENNReal.ofReal M₁ * eLpNorm (⇑f) (ENNReal.ofReal s) Measure.count) →
      ∀ f : ℤ →₀ ℂ, eLpNorm (T f) (ENNReal.ofReal p) Measure.count ≤
        ENNReal.ofReal (C * M₀ ^ θ * M₁ ^ (1 - θ)) *
          eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
  obtain ⟨Cint, hCint⟩ :=
    PrimeCarleson.Proof.Common.exists_eLpNorm_count_le_interpolation_finsupp_ofReal
      (α := ℤ) (β := ℤ) (E := ℂ) (ε := ℝ≥0∞) (p₀ := 2) (p₁ := s) (p := p) (θ := 1 - θ)
      (by norm_num) hs (Ne.symm hs2) (by linarith) (by linarith) (by rw [hp]; ring_nf)
  refine ⟨Cint, Cint.2, fun T M₀ M₁ hM₀ hM₁ hsub h₀ h₁ f => ?_⟩
  have key := hCint T M₀.toNNReal M₁.toNNReal (by simpa using hM₀) (by simpa using hM₁)
    (fun g g' x => by simpa using hsub g g' x)
    (fun g => by simpa [ENNReal.ofReal] using h₀ g)
    (fun g => by simpa [ENNReal.ofReal] using h₁ g) f
  refine key.trans (le_of_eq ?_)
  rw [show 1 - (1 - θ) = θ by ring]
  congr 1
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_rpow_of_nonneg hM₀.le hθ0.le,
    ← ENNReal.ofReal_rpow_of_nonneg hM₁.le (by linarith), ENNReal.ofReal_coe_nnreal]
  rfl

/-- The exponent bookkeeping of the interpolation: `(A Q^{-σ})^θ (B Q^τ)^{1-θ} =
A^θ B^{1-θ} Q^{-c}` when `-σθ + τ(1-θ) = -c`. -/
theorem rpow_combo {A B Q σ τ θ c : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hQ : 0 < Q)
    (hexp : -(σ * θ) + τ * (1 - θ) = -c) :
    (A * Q ^ (-σ)) ^ θ * (B * Q ^ τ) ^ (1 - θ) = A ^ θ * B ^ (1 - θ) * Q ^ (-c) := by
  rw [Real.mul_rpow hA (Real.rpow_nonneg hQ.le _), Real.mul_rpow hB (Real.rpow_nonneg hQ.le _),
    ← Real.rpow_mul hQ.le, ← Real.rpow_mul hQ.le]
  have h : Q ^ (-σ * θ) * Q ^ (τ * (1 - θ)) = Q ^ (-c) := by
    rw [← Real.rpow_add hQ]
    congr 1
    linarith
  calc A ^ θ * Q ^ (-σ * θ) * (B ^ (1 - θ) * Q ^ (τ * (1 - θ)))
      = A ^ θ * B ^ (1 - θ) * (Q ^ (-σ * θ) * Q ^ (τ * (1 - θ))) := by ring
    _ = A ^ θ * B ^ (1 - θ) * Q ^ (-c) := by rw [h]

/-- `C^Q` is subadditive in `f`. -/
theorem CQ_add_le (S : KQSetup) (Q : ℕ) (f g : ℤ →₀ ℂ) (x : ℤ) :
    S.CQ Q (⇑(f + g)) x ≤ S.CQ Q (⇑f) x + S.CQ Q (⇑g) x := by
  unfold KQSetup.CQ
  refine iSup₂_le fun lam hlam => ?_
  have h : S.TQ Q lam (⇑(f + g)) x = S.TQ Q lam (⇑f) x + S.TQ Q lam (⇑g) x :=
    weightedModSum_add_left _ f g lam x
  rw [h]
  exact (enorm_add_le _ _).trans
    (add_le_add (le_iSup₂_of_le lam hlam le_rfl) (le_iSup₂_of_le lam hlam le_rfl))

/-- `V^{Q,r}` is subadditive in `f`. -/
theorem VQr_add_le (S : KQSetup) {r : ℝ} (hr : 1 ≤ r) (Q : ℕ) (f g : ℤ →₀ ℂ) (x : ℤ) :
    S.VQr r Q (⇑(f + g)) x ≤ S.VQr r Q (⇑f) x + S.VQr r Q (⇑g) x :=
  varOp_add_left_le hr (fun n => wQ Q n * S.KQz Q n) f g x

/-- **Interpolation for `V^{Q,r}`** (Source: main paper `l:red-var-l2`, L1717–L1728): let `r > 2`,
`s > r'`, `θ ∈ (0, 1)`, `1/p = θ/2 + (1-θ)/s`, `p ≠ 2`. If `‖V^{Q,r} f‖₂ ≤ C₂ Q^{-σ} ‖f‖₂` for all
dyadic
`Q`, then for every `c < θσ - (1-θ)/r` there is `C` with
`‖V^{Q,r} f‖_p ≤ C Q^{-c} ‖f‖_p` (conditional on `hO`; the `o(1)` of the crude bound is absorbed
into the gap between `c` and `θσ - (1-θ)/r`). -/
theorem variational_interpolation (hO : OplusVariationBound) (S : KQSetup)
    (hS : S.P.SupportBlock S.δ) {r s p θ σ C₂ : ℝ} (hr : 2 < r) (hs : r / (r - 1) < s)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hp : 1 / p = θ / 2 + (1 - θ) / s) (hp2 : p ≠ 2)
    (h2 : ∀ (j : ℕ) (f : ℤ →₀ ℂ),
      eLpNorm (S.VQr r (2 ^ j) (⇑f)) (ENNReal.ofReal 2) Measure.count ≤
        ENNReal.ofReal (C₂ * ((2 : ℝ) ^ j) ^ (-σ)) *
          eLpNorm (⇑f) (ENNReal.ofReal 2) Measure.count)
    {c : ℝ} (hcσ : c < θ * σ - (1 - θ) / r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : ℕ) (f : ℤ →₀ ℂ),
      eLpNorm (S.VQr r (2 ^ j) (⇑f)) (ENNReal.ofReal p) Measure.count ≤
        ENNReal.ofReal (C * ((2 : ℝ) ^ j) ^ (-c)) *
          eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
  have hr1 : 0 < r - 1 := by linarith
  have hr'0 : 0 < r / (r - 1) := div_pos (by linarith) hr1
  have hs0 : 0 < s := hr'0.trans hs
  have hs2 : s ≠ 2 := by
    rintro rfl
    have : 1 / p = 1 / 2 := by rw [hp]; ring
    exact hp2 (by simpa using this)
  obtain ⟨Cint, hCint0, hint⟩ := interp_two_s hs0 hs2 hθ0 hθ1 hp
  have h1θ : 0 < 1 - θ := by linarith
  set δ : ℝ := (θ * σ - (1 - θ) / r - c) / (1 - θ) with hδ
  have hδ0 : 0 < δ := div_pos (by linarith) h1θ
  obtain ⟨C₁, hC₁0, h₁⟩ := crude_var_Q_bound hO S hS hr hs hδ0
  have hA : 0 < |C₂| + 1 := by positivity
  have hB : 0 < C₁ + 1 := by linarith
  refine ⟨Cint * (|C₂| + 1) ^ θ * (C₁ + 1) ^ (1 - θ), by positivity, fun j f => ?_⟩
  have hQ : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  have hM₀ : 0 < (|C₂| + 1) * ((2 : ℝ) ^ j) ^ (-σ) := by positivity
  have hM₁ : 0 < (C₁ + 1) * ((2 : ℝ) ^ j) ^ (1 / r + δ) := by positivity
  have key := hint (fun g => S.VQr r (2 ^ j) (⇑g)) _ _ hM₀ hM₁
    (fun g g' x => VQr_add_le S (by linarith) _ g g' x)
    (fun g => (h2 j g).trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal (by
      have := Real.rpow_nonneg hQ.le (-σ)
      have h3 : C₂ ≤ |C₂| + 1 := by linarith [le_abs_self C₂]
      nlinarith)) _))
    (fun g => (h₁ j g).trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal (by
      have := Real.rpow_nonneg hQ.le (1 / r + δ)
      nlinarith)) _)) f
  refine key.trans (le_of_eq ?_)
  congr 2
  have hexp : -(σ * θ) + (1 / r + δ) * (1 - θ) = -c := by
    rw [hδ]
    field_simp
    ring
  rw [mul_assoc Cint, rpow_combo hA.le hB.le hQ hexp]
  ring

/-- **Interpolation for `C^Q`** (Source: main paper `l:red-var-l2`, L1729–L1732): if
`‖C^Q f‖₂ ≤ C₂ Q^{-σ} ‖f‖₂`
for all dyadic `Q`, `s > 1`, `θ ∈ (0, 1)`, `1/p = θ/2 + (1-θ)/s`, `p ≠ 2`, then for every
`c < θσ` there is `C` with `‖C^Q f‖_p ≤ C Q^{-c} ‖f‖_p` (conditional on `hO`). -/
theorem maximal_interpolation (hO : OplusVariationBound) (S : KQSetup)
    (hS : S.P.SupportBlock S.δ) {s p θ σ C₂ : ℝ} (hs : 1 < s)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hp : 1 / p = θ / 2 + (1 - θ) / s) (hp2 : p ≠ 2)
    (h2 : ∀ (j : ℕ) (f : ℤ →₀ ℂ),
      eLpNorm (S.CQ (2 ^ j) (⇑f)) (ENNReal.ofReal 2) Measure.count ≤
        ENNReal.ofReal (C₂ * ((2 : ℝ) ^ j) ^ (-σ)) *
          eLpNorm (⇑f) (ENNReal.ofReal 2) Measure.count)
    {c : ℝ} (hcσ : c < θ * σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : ℕ) (f : ℤ →₀ ℂ),
      eLpNorm (S.CQ (2 ^ j) (⇑f)) (ENNReal.ofReal p) Measure.count ≤
        ENNReal.ofReal (C * ((2 : ℝ) ^ j) ^ (-c)) *
          eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
  have hs0 : 0 < s := by linarith
  have hs2 : s ≠ 2 := by
    rintro rfl
    have : 1 / p = 1 / 2 := by rw [hp]; ring
    exact hp2 (by simpa using this)
  obtain ⟨Cint, hCint0, hint⟩ := interp_two_s hs0 hs2 hθ0 hθ1 hp
  have h1θ : 0 < 1 - θ := by linarith
  set δ : ℝ := (θ * σ - c) / (1 - θ) with hδ
  have hδ0 : 0 < δ := div_pos (by linarith) h1θ
  obtain ⟨C₁, hC₁0, h₁⟩ := maximal_crude_bound hO S hS hs hδ0
  have hA : 0 < |C₂| + 1 := by positivity
  have hB : 0 < C₁ + 1 := by linarith
  refine ⟨Cint * (|C₂| + 1) ^ θ * (C₁ + 1) ^ (1 - θ), by positivity, fun j f => ?_⟩
  have hQ : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  have hM₀ : 0 < (|C₂| + 1) * ((2 : ℝ) ^ j) ^ (-σ) := by positivity
  have hM₁ : 0 < (C₁ + 1) * ((2 : ℝ) ^ j) ^ δ := by positivity
  have key := hint (fun g => S.CQ (2 ^ j) (⇑g)) _ _ hM₀ hM₁
    (fun g g' x => CQ_add_le S _ g g' x)
    (fun g => (h2 j g).trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal (by
      have := Real.rpow_nonneg hQ.le (-σ)
      have h3 : C₂ ≤ |C₂| + 1 := by linarith [le_abs_self C₂]
      nlinarith)) _))
    (fun g => (h₁ j g).trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal (by
      have := Real.rpow_nonneg hQ.le δ
      nlinarith)) _)) f
  refine key.trans (le_of_eq ?_)
  congr 2
  have hexp : -(σ * θ) + δ * (1 - θ) = -c := by
    rw [hδ]
    field_simp
    ring
  rw [mul_assoc Cint, rpow_combo hA.le hB.le hQ hexp]
  ring

/-- **`l:red-var-l2`** (L1546–L1564, variational half), the case `p ≠ 2`: let `r > 2`,
`s > r'`, `θ ∈ (0, 1)` with `1/p = θ/2 + (1-θ)/s`, `p ≠ 2`. If `‖V^{Q,r} f‖₂ ≤ C₂ Q^{-σ} ‖f‖₂` for
all dyadic `Q` and `θσ > (1-θ)/r`, then there is `c` with `0 < c < θσ - (1-θ)/r` and `C` with
`‖V^{Q,r} f‖_p ≤ C Q^{-c} ‖f‖_p` for all dyadic `Q` (conditional on `hO`). -/
theorem red_var_l2 (hO : OplusVariationBound) (S : KQSetup) (hS : S.P.SupportBlock S.δ)
    {r s p θ σ C₂ : ℝ} (hr : 2 < r) (hs : r / (r - 1) < s)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hp : 1 / p = θ / 2 + (1 - θ) / s) (hp2 : p ≠ 2)
    (h2 : ∀ (j : ℕ) (f : ℤ →₀ ℂ),
      eLpNorm (S.VQr r (2 ^ j) (⇑f)) (ENNReal.ofReal 2) Measure.count ≤
        ENNReal.ofReal (C₂ * ((2 : ℝ) ^ j) ^ (-σ)) *
          eLpNorm (⇑f) (ENNReal.ofReal 2) Measure.count)
    (hcond : (1 - θ) / r < θ * σ) :
    ∃ c : ℝ, 0 < c ∧ c < θ * σ - (1 - θ) / r ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : ℕ) (f : ℤ →₀ ℂ),
      eLpNorm (S.VQr r (2 ^ j) (⇑f)) (ENNReal.ofReal p) Measure.count ≤
        ENNReal.ofReal (C * ((2 : ℝ) ^ j) ^ (-c)) *
          eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
  have hgap : 0 < θ * σ - (1 - θ) / r := by linarith
  refine ⟨(θ * σ - (1 - θ) / r) / 2, by positivity, by linarith, ?_⟩
  exact variational_interpolation hO S hS hr hs hθ0 hθ1 hp hp2 h2 (by linarith)

/-- **`l:red-var-l2`, the maximal part** (L1566–L1573, L1729–L1732): if
`‖C^Q f‖₂ ≤ C₂ Q^{-σ} ‖f‖₂` for all dyadic `Q`, some `σ > 0`, then for every `1 < p < ∞` there are
`c_p > 0` and `C` with `‖C^Q f‖_p ≤ C Q^{-c_p} ‖f‖_p` for all dyadic `Q` (conditional on `hO`). -/
theorem maximal_part (hO : OplusVariationBound) (S : KQSetup) (hS : S.P.SupportBlock S.δ)
    {σ C₂ : ℝ} (hσ : 0 < σ)
    (h2 : ∀ (j : ℕ) (f : ℤ →₀ ℂ),
      eLpNorm (S.CQ (2 ^ j) (⇑f)) (ENNReal.ofReal 2) Measure.count ≤
        ENNReal.ofReal (C₂ * ((2 : ℝ) ^ j) ^ (-σ)) *
          eLpNorm (⇑f) (ENNReal.ofReal 2) Measure.count)
    {p : ℝ} (hp : 1 < p) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : ℕ) (f : ℤ →₀ ℂ),
      eLpNorm (S.CQ (2 ^ j) (⇑f)) (ENNReal.ofReal p) Measure.count ≤
        ENNReal.ofReal (C * ((2 : ℝ) ^ j) ^ (-c)) *
          eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
  by_cases hp2 : p = 2
  · subst hp2
    exact ⟨σ, hσ, |C₂|, abs_nonneg _, fun j f => (h2 j f).trans (mul_le_mul_left
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_abs_self C₂)
        (Real.rpow_nonneg (by positivity) _))) _)⟩
  · have hp0 : 0 < p := by linarith
    obtain ⟨s, hsp⟩ : ∃ s : ℝ, 1 < s ∧ ((p < 2 ∧ s < p) ∨ (2 < p ∧ p < s)) := by
      rcases lt_or_gt_of_ne hp2 with hlt | hgt
      · exact ⟨(1 + p) / 2, by linarith, Or.inl ⟨hlt, by linarith⟩⟩
      · exact ⟨p + 1, by linarith, Or.inr ⟨hgt, by linarith⟩⟩
    obtain ⟨hs1, hsp⟩ := hsp
    obtain ⟨θ, hθ0, hθ1, hθ⟩ := exists_interp_theta hp0 (by linarith) hsp
    have hθσ : 0 < θ * σ := mul_pos hθ0 hσ
    obtain ⟨C, hC0, hC⟩ := maximal_interpolation hO S hS hs1 hθ0 hθ1 hθ hp2 h2
      (c := θ * σ / 2) (by linarith)
    exact ⟨θ * σ / 2, by positivity, C, hC0, hC⟩

end PrimeCarleson.Proof.Paper
