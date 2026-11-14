module

public import PrimeCarleson.Proof.Paper.P10.Selector
public import PrimeCarleson.Proof.Paper.P9.GlobalShell
public import PrimeCarleson.Proof.Paper.P2.Weights

/-!
# The transference estimate `‖C^Q_B f‖_{ℓ²} ≲ Q^{ε/10} 𝔪_B ‖f‖_{ℓ²}` (`p:transferprop`)

Source: main paper `p:transferprop`, L2133–L2138 and L2260–L2264, with the loss `log²(2+Q)`
replaced by `Q^{ε/10}`.

* `sum_inv_totient_le` (the last step of the bound for `B₁` in `l:A1B1`, L2208–L2212):
  `∑_{q ∈ B} 1/φ(q) ≤ Φ₀` for the blocks of size `|B| ≤ 100 Q^κ` (`κ < 1`; `e:totientbound`);
* `window_bound` (the final conversion, Source: main paper `p:transferprop`, L2262–L2264): the
  conversion of `A₁, B₁` and `∑_R ‖F_R‖²` into `K 𝔪_B Q^{ε/10} ‖f‖`, via `A₁ ≲ N^{1/2} 𝔪_B`,
  `‖χ_I‖ ≲ N^{-1/2}`, `B₁/A₁ ≲ Q` (`𝔪_B ≥ Q^{-1}`);
* `transferprop` (`p:transferprop`): `‖C^Q_B f‖_{ℓ²} ≤ C_ε Q^{ε/10} 𝔪_B ‖f‖_{ℓ²}` for every dyadic
  `Q`, block `B` and finitely supported `f`, conditional on `[O+]` through `l:varcarZ`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Goal0 PrimeCarleson.Proof.Common

/-! ### `∑_{q ∈ B} 1/φ(q) ≲ 1` -/

theorem one_lt_log_ten_add {x : ℝ} (hx : 1 ≤ x) : 1 < Real.log (10 + x) := by
  rw [Real.lt_log_iff_exp_lt (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

/-- **The last step of the bound for `B₁` in `l:A1B1`** (L2208–L2212): for `κ < 1` there is `Φ₀`
with `∑_{q ∈ B} 1/φ(q) ≤ Φ₀` for every `B ⊆ sqfreeSet j` with `|B| ≤ 100 Q^κ`
(`1/φ(q) ≲ log log (10+Q) / Q` for `q > Q/2`). -/
theorem sum_inv_totient_le {κ : ℝ} (hκ : κ < 1) :
    ∃ Φ₀ : ℝ, 0 ≤ Φ₀ ∧ ∀ (j : ℕ) (B : Finset ℕ), B ⊆ sqfreeSet j →
      (B.card : ℝ) ≤ 100 * ((2 : ℝ) ^ j) ^ κ → ∑ q ∈ B, ((Nat.totient q : ℝ))⁻¹ ≤ Φ₀ := by
  obtain ⟨C₁, hC₁, h1⟩ := inv_totient_le_loglog
  obtain ⟨C₂, hC₂, h2⟩ := loglog_le_rpow (ε := 1 - κ) (by linarith)
  refine ⟨200 * C₁ * C₂, by positivity, fun j B hB hcard => ?_⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = (2 : ℝ) ^ j := ⟨_, rfl⟩
  rw [← hQ] at hcard
  have hQ1 : 1 ≤ Q := by rw [hQ]; exact one_le_pow₀ (by norm_num)
  have hQ0 : 0 < Q := by linarith
  have hterm : ∀ q ∈ B, ((Nat.totient q : ℝ))⁻¹ ≤ 2 * C₁ * C₂ * Q ^ (1 - κ) / Q := by
    intro q hq
    have hmem := mem_sqfreeSet.1 (hB hq)
    have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.2 hmem.2.2.ne_zero
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
    have hqQ : (q : ℝ) ≤ Q := by rw [hQ]; exact_mod_cast hmem.2.1
    have hQq : Q / 2 < q := by
      have := nat_div_two_lt_iff.1 hmem.1
      rw [hQ]
      push_cast at this
      exact this
    have h3 := h1 q hq1
    rw [one_div] at h3
    refine h3.trans ?_
    have hll : Real.log (Real.log (10 + (q : ℝ))) ≤ Real.log (Real.log (10 + Q)) :=
      Real.log_le_log (by linarith [one_lt_log_ten_add (x := (q : ℝ)) (by exact_mod_cast hq1)])
        (Real.log_le_log (by linarith) (by linarith))
    have hll0 : 0 ≤ Real.log (Real.log (10 + (q : ℝ))) :=
      (Real.log_pos (one_lt_log_ten_add (x := (q : ℝ)) (by exact_mod_cast hq1))).le
    have h4 := h2 Q hQ1
    calc C₁ * Real.log (Real.log (10 + (q : ℝ))) / q
        ≤ C₁ * (C₂ * Q ^ (1 - κ)) / (Q / 2) := by
          rw [div_le_div_iff₀ hq0 (by positivity)]
          have h5 : C₁ * Real.log (Real.log (10 + (q : ℝ))) ≤ C₁ * (C₂ * Q ^ (1 - κ)) :=
            mul_le_mul_of_nonneg_left (hll.trans h4) hC₁.le
          have h6 : 0 ≤ C₁ * (C₂ * Q ^ (1 - κ)) := by positivity
          nlinarith
      _ = 2 * C₁ * C₂ * Q ^ (1 - κ) / Q := by field_simp
  have hsum : ∑ q ∈ B, ((Nat.totient q : ℝ))⁻¹ ≤
      (B.card : ℝ) * (2 * C₁ * C₂ * Q ^ (1 - κ) / Q) := by
    calc _ ≤ ∑ _q ∈ B, 2 * C₁ * C₂ * Q ^ (1 - κ) / Q := Finset.sum_le_sum hterm
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  refine hsum.trans ?_
  have hpow : Q ^ κ * Q ^ (1 - κ) = Q := by
    rw [← Real.rpow_add hQ0]; simp
  have hnn : 0 ≤ 2 * C₁ * C₂ * Q ^ (1 - κ) / Q := by positivity
  calc (B.card : ℝ) * (2 * C₁ * C₂ * Q ^ (1 - κ) / Q)
      ≤ (100 * Q ^ κ) * (2 * C₁ * C₂ * Q ^ (1 - κ) / Q) := mul_le_mul_of_nonneg_right hcard hnn
    _ = 200 * C₁ * C₂ * (Q ^ κ * Q ^ (1 - κ)) / Q := by ring
    _ = 200 * C₁ * C₂ := by rw [hpow]; field_simp

/-! ### The monotone convergence over finite sets -/

/-- `ℓ²` norm as a supremum over finite sets: if `(∑_{x ∈ X} F(x)²)^{1/2} ≤ M` for every finite
`X ⊂ ℤ`, then `(∑'_x F(x)²)^{1/2} ≤ M`. -/
theorem tsum_sq_le_of_finite {F : ℤ → ℝ≥0∞} {M : ℝ≥0∞}
    (h : ∀ X : Finset ℤ, (∑ x ∈ X, F x ^ 2) ^ (1 / 2 : ℝ) ≤ M) :
    (∑' x : ℤ, F x ^ 2) ^ (1 / 2 : ℝ) ≤ M := by
  have hX : ∀ X : Finset ℤ, ∑ x ∈ X, F x ^ 2 ≤ M ^ 2 := fun X => by
    calc ∑ x ∈ X, F x ^ 2 = ((∑ x ∈ X, F x ^ 2) ^ (1 / 2 : ℝ)) ^ 2 := (enorm_rpow_half_sq _).symm
      _ ≤ M ^ 2 := by gcongr; exact h X
  rw [ENNReal.tsum_eq_iSup_sum]
  calc (⨆ X : Finset ℤ, ∑ x ∈ X, F x ^ 2) ^ (1 / 2 : ℝ) ≤ (M ^ 2) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow (iSup_le hX) (by norm_num)
    _ = M := enorm_sq_rpow_half M

/-! ### The conversion (Source: main paper `p:transferprop`, L2262–L2264) -/

/-- The constant `K = 15 C₀ (1 + E(4, s_e) Cv Φ₀^{ε/20})` of `window_bound`, `s_e = 40/(20 - ε)`. -/
def transferConst (ε Cv C₀ Φ₀ : ℝ) : ℝ :=
  15 * C₀ * (1 + entropyConst 4 (40 / (20 - ε)) * Cv * Φ₀ ^ (ε / 20))

theorem transferConst_nonneg {ε Cv C₀ Φ₀ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 100) (hCv : 0 ≤ Cv)
    (hC₀ : 0 ≤ C₀) (hΦ₀ : 0 ≤ Φ₀) : 0 ≤ transferConst ε Cv C₀ Φ₀ := by
  obtain ⟨hs2, hs4, -, -, -⟩ := transfer_exponent_choice hε hε1
  have := entropyConst_pos hs2 hs4
  unfold transferConst
  positivity

/-- `‖χ_I‖ √(2/c) ≤ 15` for the cutoff data of a window (`‖χ_I‖² ≤ (53/50)|I|`,
`|I| = 13/(25 N)`, `2/c = 5000 N/13`): the paper's `‖χ_I‖_{ℓ²} ≲ N^{-1/2}` against
`A₁ ≈ N^{1/2} 𝔪_B` (Source: main paper `p:transferprop`, L2164–L2170). -/
theorem chiNorm_mul_sqrt_le {N : ℕ} (hN : 0 < N) {u : ℝ}
    (D : CutoffData (winChart u) (winLo N u) (winHi N u) (winScale N)) :
    D.chiNorm * Real.sqrt (2 / winScale N) ≤ 15 := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have h2c : 0 ≤ 2 / winScale N := by have := winScale_pos hN; positivity
  have h1 : D.chiNorm ^ 2 ≤ 53 / 50 * (winHi N u - winLo N u) := by
    have := D.sum_norm_sq_chi_le'
    rw [CutoffData.chiNorm, Real.sq_sqrt (tsum_nonneg fun _ => by positivity)]
    exact this
  rw [winHi_sub_winLo hN u] at h1
  have h2 : (D.chiNorm * Real.sqrt (2 / winScale N)) ^ 2 ≤ 15 ^ 2 := by
    rw [mul_pow, Real.sq_sqrt h2c]
    have h3 : 2 / winScale N = 5000 * (N : ℝ) / 13 := by
      unfold winScale; field_simp; ring
    rw [h3]
    calc D.chiNorm ^ 2 * (5000 * (N : ℝ) / 13)
        ≤ 53 / 50 * (13 / (25 * (N : ℝ))) * (5000 * (N : ℝ) / 13) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = 212 := by field_simp; norm_num
      _ ≤ 15 ^ 2 := by norm_num
  by_contra hlt
  push Not at hlt
  have := pow_lt_pow_left₀ hlt (by norm_num) (two_ne_zero)
  linarith

/-- The real-number bookkeeping of `window_bound`. -/
theorem window_real_bound {chi sq a C₀ E Cv P Qg : ℝ} (hchi : chi * sq ≤ 15) (ha : 0 ≤ a)
    (hC₀ : 0 ≤ C₀) (hE : 0 ≤ E) (hCv : 0 ≤ Cv) (hP : 0 ≤ P) (hQg : 1 ≤ Qg) :
    chi * (sq * a * C₀ + E * (Cv * C₀) * (sq * a * (P * Qg))) ≤
      15 * C₀ * (1 + E * Cv * P) * a * Qg := by
  have hQg0 : 0 ≤ Qg := by linarith
  have hkey : chi * (sq * a * C₀ + E * (Cv * C₀) * (sq * a * (P * Qg))) =
      (chi * sq) * (a * C₀) * (1 + E * Cv * (P * Qg)) := by ring
  rw [hkey]
  have hpos : 0 ≤ a * C₀ := mul_nonneg ha hC₀
  have hfac : 1 + E * Cv * (P * Qg) ≤ (1 + E * Cv * P) * Qg := by
    have : 0 ≤ E * Cv * P := by positivity
    nlinarith
  have h0 : 0 ≤ 1 + E * Cv * (P * Qg) := by positivity
  calc (chi * sq) * (a * C₀) * (1 + E * Cv * (P * Qg))
      ≤ 15 * (a * C₀) * (1 + E * Cv * (P * Qg)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hchi hpos) h0
    _ ≤ 15 * (a * C₀) * ((1 + E * Cv * P) * Qg) :=
        mul_le_mul_of_nonneg_left hfac (by positivity)
    _ = 15 * C₀ * (1 + E * Cv * P) * a * Qg := by ring

/-- `A^{1-γ} (A ρ)^γ = A ρ^γ` with `ρ = √Φ₀ Q`, `ρ^γ = Φ₀^{γ/2} Q^γ`. -/
theorem transfer_rpow_combo {A Φ₀ Q γ : ℝ} (hA : 0 < A) (hΦ₀ : 0 ≤ Φ₀) (hQ : 0 ≤ Q) :
    A ^ (1 - γ) * (A * (Real.sqrt Φ₀ * Q)) ^ γ = A * (Φ₀ ^ (γ / 2) * Q ^ γ) := by
  rw [Real.mul_rpow hA.le (by positivity), ← mul_assoc, ← Real.rpow_add hA, sub_add_cancel,
    Real.rpow_one, Real.mul_rpow (Real.sqrt_nonneg _) hQ, Real.sqrt_eq_rpow,
    ← Real.rpow_mul hΦ₀]
  congr 3
  ring

/-- The final real bound of `window_bound`: with `A₁ = √(2/c) 𝔪_B`, `B₁ = A₁ √Φ₀ Q`. -/
theorem window_final {chi sq a C₀ E Cv Φ₀ Q γ : ℝ} (hchi : chi * sq ≤ 15) (ha : 0 < a)
    (hCv : 0 ≤ Cv) (hC₀ : 0 ≤ C₀) (hE : 0 ≤ E) (hΦ₀ : 0 ≤ Φ₀) (hQ : 1 ≤ Q) (hγ : 0 ≤ γ)
    (hsq : 0 < sq) :
    chi * (sq * a * C₀ + E * (Cv * C₀) * (sq * a) ^ (1 - γ) *
        ((sq * a) * (Real.sqrt Φ₀ * Q)) ^ γ) ≤
      15 * C₀ * (1 + E * Cv * Φ₀ ^ (γ / 2)) * a * Q ^ γ := by
  have hA : 0 < sq * a := mul_pos hsq ha
  have hQ0 : 0 ≤ Q := by linarith
  have hexp : E * (Cv * C₀) * (sq * a) ^ (1 - γ) * ((sq * a) * (Real.sqrt Φ₀ * Q)) ^ γ =
      E * (Cv * C₀) * ((sq * a) ^ (1 - γ) * ((sq * a) * (Real.sqrt Φ₀ * Q)) ^ γ) := by ring
  rw [hexp, transfer_rpow_combo hA hΦ₀ hQ0]
  exact window_real_bound hchi ha.le hC₀ hE hCv (Real.rpow_nonneg hΦ₀ _)
    (Real.one_le_rpow hQ hγ)

/-- **The final bound of `p:transferprop` for one window** (L2262–L2264) for a block
`B ⊆ sqfreeSet j` with `|B| ≤ 100 Q^κ`, `∑_{q ∈ B} 1/φ(q) ≤ Φ₀`, a window `u ∈ [0, 1)` and
`ω(x) ∈ [u, u + 1/(2N)]`,
`(∑_{x ∈ X} |T^{Q,B}_{ϑ(x)/N + ω(x)} f(x)|²)^{1/2} ≤ K 𝔪_B Q^{ε/10} ‖f‖_{ℓ²}`. -/
theorem window_bound (S : KQSetup) (hS : S.P.SupportBlock S.δ) {j : ℕ} {B : Finset ℕ}
    (hBsub : B ⊆ sqfreeSet j) (hBne : B.Nonempty)
    (hcard : (B.card : ℝ) ≤ 100 * ((2 : ℝ) ^ j) ^ S.P.kappa) (hε1 : S.P.ε ≤ 1 / 100)
    {Cv C₀ Φ₀ : ℝ} (hCv : 0 ≤ Cv) (hv : LVarCarZ (40 / (20 - S.P.ε)) Cv) (hC₀ : 0 ≤ C₀)
    (hKb : ∀ β : ℝ, ‖S.KQhat (2 ^ j) β‖ ≤ C₀)
    (hbv : eVariationOn (S.KQhat (2 ^ j)) Set.univ ≤ ENNReal.ofReal C₀) (hΦ₀ : 0 ≤ Φ₀)
    (hΦ : ∑ q ∈ B, ((Nat.totient q : ℝ))⁻¹ ≤ Φ₀) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (f : ℤ →₀ ℂ) (X : Finset ℤ) (ϑ : ℤ → ℤ) (ω : ℤ → ℝ)
    (hω : ∀ x ∈ X, u ≤ ω x ∧ ω x ≤ u + 1 / (2 * (lcmQ B : ℝ)) ∧ ω x < 1) :
    (∑ x ∈ X, ‖S.TQB (2 ^ j) B ((ϑ x : ℝ) / (lcmQ B : ℝ) + ω x) f x‖ₑ ^ 2) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (transferConst S.P.ε Cv C₀ Φ₀ * mB B * ((2 : ℝ) ^ j) ^ (S.P.ε / 10)) *
        l2enorm (⇑f) := by
  classical
  have hε := S.P.ε_pos
  obtain ⟨hs2, hs4, -, hγ, -⟩ := transfer_exponent_choice hε hε1
  have hQ1 : 1 ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
  have hQ0 : 0 < (2 : ℝ) ^ j := by linarith
  have hB : ∀ q ∈ B, 0 < q := fun q hq =>
    Nat.pos_of_ne_zero (mem_sqfreeSet.1 (hBsub hq)).2.2.ne_zero
  have hN : 0 < lcmQ B := lcmQ_pos hB
  have hmB : ((2 : ℝ) ^ j)⁻¹ ≤ mB B := inv_le_mB hBsub hBne
  have hmB0 : 0 < mB B := lt_of_lt_of_le (inv_pos.2 hQ0) hmB
  obtain ⟨D⟩ := window_cutoff hN u
  have hc0 : 0 < winScale (lcmQ B) := winScale_pos hN
  have h2c : 0 ≤ 2 / winScale (lcmQ B) := by positivity
  have hA₁0 : 0 < Real.sqrt (2 / winScale (lcmQ B)) * mB B :=
    mul_pos (Real.sqrt_pos.2 (by positivity)) hmB0
  have hA₁sq : (Real.sqrt (2 / winScale (lcmQ B)) * mB B) ^ 2 =
      2 / winScale (lcmQ B) * mB B ^ 2 := by
    rw [mul_pow, Real.sq_sqrt h2c]
  have hρ0 : 0 ≤ Real.sqrt Φ₀ * (2 : ℝ) ^ j := by positivity
  have hB₁sq : ((Real.sqrt (2 / winScale (lcmQ B)) * mB B) * (Real.sqrt Φ₀ * (2 : ℝ) ^ j)) ^ 2 =
      2 / winScale (lcmQ B) * mB B ^ 2 * (Φ₀ * ((2 : ℝ) ^ j) ^ 2) := by
    rw [mul_pow, hA₁sq, mul_pow, Real.sq_sqrt hΦ₀]
  have hmQ : 1 ≤ mB B * (2 : ℝ) ^ j := by
    have := mul_le_mul_of_nonneg_right hmB hQ0.le
    rwa [inv_mul_cancel₀ hQ0.ne'] at this
  have hB₁' : 2 / winScale (lcmQ B) * ∑ q ∈ B, ((Nat.totient q : ℝ))⁻¹ ≤
      ((Real.sqrt (2 / winScale (lcmQ B)) * mB B) * (Real.sqrt Φ₀ * (2 : ℝ) ^ j)) ^ 2 := by
    rw [hB₁sq]
    have h1 : Φ₀ ≤ mB B ^ 2 * (Φ₀ * ((2 : ℝ) ^ j) ^ 2) := by
      have : (1 : ℝ) ≤ (mB B * (2 : ℝ) ^ j) ^ 2 := by nlinarith
      calc Φ₀ = 1 * Φ₀ := (one_mul _).symm
        _ ≤ (mB B * (2 : ℝ) ^ j) ^ 2 * Φ₀ := mul_le_mul_of_nonneg_right this hΦ₀
        _ = mB B ^ 2 * (Φ₀ * ((2 : ℝ) ^ j) ^ 2) := by ring
    calc 2 / winScale (lcmQ B) * ∑ q ∈ B, ((Nat.totient q : ℝ))⁻¹
        ≤ 2 / winScale (lcmQ B) * Φ₀ := mul_le_mul_of_nonneg_left hΦ h2c
      _ ≤ 2 / winScale (lcmQ B) * (mB B ^ 2 * (Φ₀ * ((2 : ℝ) ^ j) ^ 2)) :=
          mul_le_mul_of_nonneg_left h1 h2c
      _ = 2 / winScale (lcmQ B) * mB B ^ 2 * (Φ₀ * ((2 : ℝ) ^ j) ^ 2) := by ring
  have happly := apply_variable S hS hBsub hcard hu0 hs2 hs4 hCv hv hC₀ hKb hbv D hA₁0.le
    (mul_nonneg hA₁0.le hρ0) (le_of_eq hA₁sq.symm) hB₁' f X ϑ ω hω hu1 (by
      have : (0 : ℝ) ≤ 1 / (2 * (lcmQ B : ℝ)) := by positivity
      linarith)
  rw [hγ] at happly
  refine happly.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _)
  have hchi := chiNorm_mul_sqrt_le hN D
  have hE0 : 0 < entropyConst 4 (40 / (20 - S.P.ε)) := entropyConst_pos hs2 hs4
  have hfin := window_final (E := entropyConst 4 (40 / (20 - S.P.ε))) (Cv := Cv) (C₀ := C₀)
    (γ := S.P.ε / 10) hchi hmB0 hCv hC₀ hE0.le hΦ₀ hQ1 (by positivity)
    (Real.sqrt_pos.2 (div_pos two_pos hc0))
  have hε20 : S.P.ε / 10 / 2 = S.P.ε / 20 := by ring
  rw [hε20] at hfin
  unfold transferConst
  exact hfin

/-- **`p:transferprop`** (Source: main paper `p:transferprop`, L2133–L2138, with the loss
`Q^{ε/10}`): conditional on `[O+]` (`hO`, through `l:varcarZ`), under (C1) `SupportBlock` and
`κ < 1`, there is `C = C_ε` with `‖C^Q_B f‖_{ℓ²} ≤ C Q^{ε/10} 𝔪_B ‖f‖_{ℓ²}` for every dyadic
`Q = 2^j`, every block `B` (`B ⊆ sqfreeSet j` nonempty, `|B| ≤ 100 Q^κ`; the blocks of `e:kappa`
have `|B| ≤ A Q^κ`) and every finitely supported `f`. -/
theorem transferprop (hO : OplusVariationBound) (S : KQSetup) (hS : S.P.SupportBlock S.δ)
    (hκ1 : S.P.kappa < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : ℕ) (B : Finset ℕ), B ⊆ sqfreeSet j → B.Nonempty →
      (B.card : ℝ) ≤ 100 * ((2 : ℝ) ^ j) ^ S.P.kappa → ∀ f : ℤ →₀ ℂ,
      eLpNorm (S.CQB (2 ^ j) B (⇑f)) (ENNReal.ofReal 2) Measure.count ≤
        ENNReal.ofReal (C * ((2 : ℝ) ^ j) ^ (S.P.ε / 10) * mB B) *
          eLpNorm (⇑f) (ENNReal.ofReal 2) Measure.count := by
  classical
  have hε := S.P.ε_pos
  have hε1 : S.P.ε ≤ 1 / 100 := by
    have := S.P.hundred_eps_le_kappa
    linarith
  obtain ⟨hs2, hs4, -, -, -⟩ := transfer_exponent_choice hε hε1
  obtain ⟨Cv, hCv, hv⟩ := lVarCarZ_of_oplus hO _ hs2
  obtain ⟨C₀, hC₀, hC₀j⟩ := KQ_hat_sup S
  obtain ⟨Φ₀, hΦ₀, hΦ⟩ := sum_inv_totient_le hκ1
  have hK := transferConst_nonneg hε hε1 hCv hC₀ hΦ₀
  refine ⟨2 * transferConst S.P.ε Cv C₀ Φ₀, by positivity, fun j B hBsub hBne hcard f => ?_⟩
  have hB : ∀ q ∈ B, 0 < q := fun q hq =>
    Nat.pos_of_ne_zero (mem_sqfreeSet.1 (hBsub hq)).2.2.ne_zero
  have hN : 0 < lcmQ B := lcmQ_pos hB
  have hNR : (1 : ℝ) ≤ lcmQ B := by exact_mod_cast hN
  obtain ⟨ϑ, ω, hω, hCQ⟩ := S.exists_selector (2 ^ j) B hN f
  have h1N : 1 / (lcmQ B : ℝ) ≤ 1 := by
    rw [div_le_one (by linarith)]; exact hNR
  have h12 : 1 / (2 * (lcmQ B : ℝ)) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  set M : ℝ≥0∞ := ENNReal.ofReal (transferConst S.P.ε Cv C₀ Φ₀ * mB B *
    ((2 : ℝ) ^ j) ^ (S.P.ε / 10)) * l2enorm (⇑f) with hM
  rw [eLpNorm_two_eq_tsum_sq, eLpNorm_two_eq_tsum_sq']
  have hfin : ∀ X : Finset ℤ, (∑ x ∈ X, (S.CQB (2 ^ j) B (⇑f) x) ^ 2) ^ (1 / 2 : ℝ) ≤ M + M := by
    intro X
    simp_rw [hCQ]
    rw [← Finset.sum_filter_add_sum_filter_not X (fun x => ω x ≤ 1 / (2 * (lcmQ B : ℝ)))]
    refine (ENNReal.rpow_add_le_add_rpow _ _ (by norm_num) (by norm_num)).trans
      (add_le_add ?_ ?_)
    · refine window_bound S hS hBsub hBne hcard hε1 hCv hv hC₀ (hC₀j j).1 (hC₀j j).2 hΦ₀
        (hΦ j B hBsub hcard) (u := 0) le_rfl zero_lt_one f _ ϑ ω fun x hx => ?_
      have hx' := (Finset.mem_filter.1 hx).2
      refine ⟨(hω x).1, by rw [zero_add]; exact hx', ?_⟩
      have := (hω x).2
      linarith
    · refine window_bound S hS hBsub hBne hcard hε1 hCv hv hC₀ (hC₀j j).1 (hC₀j j).2 hΦ₀
        (hΦ j B hBsub hcard) (u := 1 / (2 * (lcmQ B : ℝ))) (by positivity) (by linarith) f _ ϑ ω
        fun x hx => ?_
      have hx' := (Finset.mem_filter.1 hx).2
      have hlt := (hω x).2
      refine ⟨le_of_lt (not_le.1 hx'), ?_, by linarith [hlt]⟩
      have : 1 / (lcmQ B : ℝ) = 1 / (2 * (lcmQ B : ℝ)) + 1 / (2 * (lcmQ B : ℝ)) := by
        field_simp; ring
      linarith [hlt]
  have hmain := tsum_sq_le_of_finite hfin
  refine hmain.trans (le_of_eq ?_)
  rw [hM, ← two_mul, ← mul_assoc, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
  congr 2
  ring

end PrimeCarleson.Proof.Paper
