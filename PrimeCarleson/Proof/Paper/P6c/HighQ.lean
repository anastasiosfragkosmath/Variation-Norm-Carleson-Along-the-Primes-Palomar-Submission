module

public import PrimeCarleson.Proof.Paper.P6c.Pieces
public import PrimeCarleson.Proof.Paper.P6c.Interp
public import PrimeCarleson.Proof.Paper.P6a.HighQ
public import PrimeCarleson.Proof.Paper.P6a.Leftover

/-!
# The high-denominator term and the leftover pairs of the maximal operator

Source: main paper `s:red`, L1525–L1527, and the leftover pairs. The maximal counterpart of
`highQ_var_L2_red`, `highQ_crude`, `highQ_sum_param` and `leftover_pairs` of `Main/Interp.lean`,
`P6a/HighQ.lean` and `P6a/Leftover.lean`:

* `highQ_L2_sup`: `‖sup_λ|∑_n f(x-n) w_Q(n) ψ_k(n) e(λ n)|‖_{ℓ²} ≲_ε Q^{-3/8+ε} ‖f‖_{ℓ²}` for
  `Q = 2^j ≤ M(k)` (`e:U3maxmod` and the application of [F+, Proposition 2.1]);
* `highQ_crude_sup`: the `ℓ^s` bound `≲ (1 + log Q)^3` for every `s ≥ 1`;
* `highQ_sum_sup`: for `1 < p < ∞` there is `D₁ = D₁(p)` such that for `D₀ ≥ D₁` the sum over
  `k ≥ 1` and the dyadic `Q = 2^j`, `k^{D₀} < Q ≤ M(k)`, of the `ℓ^p` norms is `≲_p ‖f‖_{ℓ^p}`;
* `leftover_pairs_sup`: the finitely many leftover pairs `M(k) < Q ≤ k^{D₀}`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson

/-- **The high-`Q` `ℓ²` bound** (Source: main paper `s:red`, L1525–L1527): for every `ε > 0` and
`Q = 2^j ≤ M(k)`, `‖sup_λ|∑_n f(x-n) w_Q(n) ψ_k(n) e(λ n)|‖_{ℓ²} ≤ C_ε Q^{-3/8+ε} ‖f‖_{ℓ²}`. -/
theorem highQ_L2_sup (ψ : PsiData) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k j : ℕ), (2 : ℝ) ^ j ≤ cutoffM k → ∀ f : ℤ →₀ ℂ,
      eLpNorm (supOp (pairW ψ k j) (⇑f)) (ENNReal.ofReal 2) Measure.count ≤
        ENNReal.ofReal (C * ((2 : ℝ) ^ j) ^ (-(3 : ℝ) / 8 + ε)) *
          eLpNorm (⇑f) (ENNReal.ofReal 2) Measure.count := by
  obtain ⟨C_L, hCL0, hL⟩ := sup_L2_piece ψ
  obtain ⟨C_U, hU⟩ := FplusProp21.exists_gowersNormInterval_blockWeight_Ioc_two_pow_le hε
  refine ⟨C_L * |C_U|, by positivity, fun k j hj f => ?_⟩
  set N : ℕ+ := ⟨2 ^ k, by positivity⟩ with hNdef
  have hN : (N : ℕ) = 2 ^ k := rfl
  refine (hL k N hN (wQ (2 ^ j)) (fun n => wQ_neg _ n) ⇑f).trans ?_
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  have hQ : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  have hU1 : gowersNormInterval 3 N (wQ (2 ^ j)) ≤
      |C_U| * ((2 : ℝ) ^ j) ^ (-(3 : ℝ) / 8 + ε) :=
    (hU k N hN j hj).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  calc C_L * gowersNormInterval 3 N (wQ (2 ^ j))
      ≤ C_L * (|C_U| * ((2 : ℝ) ^ j) ^ (-(3 : ℝ) / 8 + ε)) :=
        mul_le_mul_of_nonneg_left hU1 hCL0
    _ = C_L * |C_U| * ((2 : ℝ) ^ j) ^ (-(3 : ℝ) / 8 + ε) := by ring

/-- **The high-`Q` crude bound**: for every `s ≥ 1`, `k` and
`Q = 2^j`, `‖sup_λ|∑_n f(x-n) w_Q(n) ψ_k(n) e(λ n)|‖_{ℓ^s} ≤ C (1 + log Q)^3 ‖f‖_{ℓ^s}`. -/
theorem highQ_crude_sup (ψ : PsiData) {s : ℝ} (hs : 1 ≤ s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k j : ℕ) (f : ℤ →₀ ℂ),
      eLpNorm (supOp (pairW ψ k j) (⇑f)) (ENNReal.ofReal s) Measure.count ≤
        ENNReal.ofReal (C * (1 + Real.log ((2 : ℝ) ^ j)) ^ 3) *
          eLpNorm (⇑f) (ENNReal.ofReal s) Measure.count := by
  obtain ⟨C_c, hCc0, hc⟩ := crude_sup_piece ψ
  obtain ⟨C₂, hC₂0, hC₂⟩ := wQ_moment_L2
  refine ⟨C_c * C₂, by positivity, fun k j f => ?_⟩
  set N : ℕ+ := ⟨2 ^ k, by positivity⟩ with hNdef
  have hN : (N : ℕ) = 2 ^ k := rfl
  refine (hc k N hN (wQ (2 ^ j)) (fun n => wQ_neg _ n) s hs ⇑f).trans ?_
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  have h2 := hC₂ (2 ^ j) N Nat.one_le_two_pow
  have hc2 : ((2 ^ j : ℕ) : ℝ) = (2 : ℝ) ^ j := by push_cast; rfl
  rw [hc2] at h2
  calc C_c * lpNormOn 2 (bracket N) (wQ (2 ^ j))
      ≤ C_c * (C₂ * (1 + Real.log ((2 : ℝ) ^ j)) ^ 3) :=
        mul_le_mul_of_nonneg_left h2 hCc0
    _ = C_c * C₂ * (1 + Real.log ((2 : ℝ) ^ j)) ^ 3 := by ring

/-- **The high-`Q` sum**: for `1 < p < ∞` there is `D₁ = D₁(p)`
such that for every `D₀ ≥ D₁` the sum over `k ≥ 1` and the dyadic `Q = 2^j` with
`k^{D₀} < Q ≤ M(k)` of `‖sup_λ|∑_n f(x-n) w_Q(n) ψ_k(n) e(λ n)|‖_{ℓ^p}` is `≲_p ‖f‖_{ℓ^p}`. -/
theorem highQ_sum_sup {p : ℝ} (hp : 1 < p) :
    ∃ D₁ : ℝ, ∀ ψ : PsiData, ∀ D₀ : ℝ, D₁ ≤ D₀ → ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℤ →₀ ℂ,
      ∑' k : ℕ, ∑ j ∈ highJ D₀ (k + 1),
          eLpNorm (supOp (pairW ψ (k + 1) j) (⇑f)) (ENNReal.ofReal p) Measure.count ≤
        ENNReal.ofReal C * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
  obtain ⟨s, ϑ, Cint, hs, hϑ0, hϑ1, hCint0, hint⟩ := supOp_interp hp
  set η : ℝ := ϑ * (3 / 8) / 2 with hη
  have hη0 : 0 < η := by positivity
  refine ⟨4 / η, fun ψ D₀ hD₀ => ?_⟩
  obtain ⟨C₀, hC₀, h₀⟩ := highQ_L2_sup ψ hη0
  obtain ⟨C₁, hC₁, h₁⟩ := highQ_crude_sup ψ hs.le
  obtain ⟨Cη, hCη0, hCη⟩ := KMTT.exists_pow_log_le_rpow hη0
  set C₀' : ℝ := max C₀ 1 with hC₀'
  set C₁' : ℝ := max (C₁ * Cη) 1 with hC₁'
  have hC₀'0 : 0 < C₀' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hC₁'0 : 0 < C₁' := lt_of_lt_of_le one_pos (le_max_right _ _)
  set q : ℝ := (2 : ℝ) ^ (-(η / 2)) with hq
  have hq0 : 0 < q := by positivity
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  set K : ℝ := Cint * C₀' ^ ϑ * C₁' ^ (1 - ϑ) with hK
  have hK0 : 0 ≤ K := by positivity
  -- the bound for a single pair
  have hpair : ∀ (k j : ℕ), (2 : ℝ) ^ j ≤ cutoffM k → ∀ f : ℤ →₀ ℂ,
      eLpNorm (supOp (pairW ψ k j) (⇑f)) (ENNReal.ofReal p) Measure.count ≤
        ENNReal.ofReal (K * ((2 : ℝ) ^ j) ^ (-η)) *
          eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
    intro k j hj f
    have hQ : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
    have hQ1 : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
    have hX₀ : 0 < C₀' * ((2 : ℝ) ^ j) ^ (-(3 : ℝ) / 8 + η) := by positivity
    have hX₁ : 0 < C₁' * ((2 : ℝ) ^ j) ^ η := by positivity
    have h := hint (pairW ψ k j) _ _ hX₀ hX₁
      (fun g => (h₀ k j hj g).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))) le_rfl))
      (fun g => (h₁ k j g).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (by
        have h2 := hCη ((2 : ℝ) ^ j) hQ1
        calc C₁ * (1 + Real.log ((2 : ℝ) ^ j)) ^ 3 ≤ C₁ * (Cη * ((2 : ℝ) ^ j) ^ η) :=
              mul_le_mul_of_nonneg_left h2 hC₁
          _ = (C₁ * Cη) * ((2 : ℝ) ^ j) ^ η := by ring
          _ ≤ C₁' * ((2 : ℝ) ^ j) ^ η :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))) le_rfl)) f
    refine h.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (le_of_eq ?_)) le_rfl)
    rw [Real.mul_rpow hC₀'0.le (by positivity), Real.mul_rpow hC₁'0.le (by positivity),
      ← Real.rpow_mul hQ.le, ← Real.rpow_mul hQ.le]
    have e1 : ((2 : ℝ) ^ j) ^ ((-(3 : ℝ) / 8 + η) * ϑ) * ((2 : ℝ) ^ j) ^ (η * (1 - ϑ)) =
        ((2 : ℝ) ^ j) ^ (-η) := by
      rw [← Real.rpow_add hQ]; congr 1
      simp only [hη]; ring
    calc Cint * (C₀' ^ ϑ * ((2 : ℝ) ^ j) ^ ((-(3 : ℝ) / 8 + η) * ϑ)) *
          (C₁' ^ (1 - ϑ) * ((2 : ℝ) ^ j) ^ (η * (1 - ϑ)))
        = K * (((2 : ℝ) ^ j) ^ ((-(3 : ℝ) / 8 + η) * ϑ) *
            ((2 : ℝ) ^ j) ^ (η * (1 - ϑ))) := by rw [hK]; ring
      _ = _ := by rw [e1]
  -- the sum over `j` for fixed `k`
  have hjsum : ∀ (k : ℕ), 1 ≤ k → ∀ f : ℤ →₀ ℂ,
      ∑ j ∈ highJ D₀ k, eLpNorm (supOp (pairW ψ k j) (⇑f)) (ENNReal.ofReal p) Measure.count ≤
        ENNReal.ofReal (K * (1 - q)⁻¹ * (k : ℝ) ^ (-(D₀ * (η / 2)))) *
          eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
    intro k hk f
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have hmem : ∀ j ∈ highJ D₀ k, (2 : ℝ) ^ j ≤ cutoffM k ∧ (k : ℝ) ^ D₀ < (2 : ℝ) ^ j := by
      intro j hj
      unfold highJ at hj
      rw [Finset.mem_filter, mem_jSet_iff] at hj
      exact ⟨hj.1, not_le.1 hj.2⟩
    have hb : ∀ j ∈ highJ D₀ k,
        K * ((2 : ℝ) ^ j) ^ (-η) ≤ K * ((k : ℝ) ^ D₀) ^ (-(η / 2)) * q ^ j := by
      intro j hj
      obtain ⟨-, hj2⟩ := hmem j hj
      have hQ : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
      have hkD : (0 : ℝ) < (k : ℝ) ^ D₀ := Real.rpow_pos_of_pos hk0 _
      have e1 : ((2 : ℝ) ^ j) ^ (-η) =
          ((2 : ℝ) ^ j) ^ (-(η / 2)) * ((2 : ℝ) ^ j) ^ (-(η / 2)) := by
        rw [← Real.rpow_add hQ]; congr 1; ring
      have e2 : ((2 : ℝ) ^ j) ^ (-(η / 2)) = q ^ j := by
        rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast,
          ← Real.rpow_mul (by norm_num)]
        congr 1; ring
      have e3 : ((2 : ℝ) ^ j) ^ (-(η / 2)) ≤ ((k : ℝ) ^ D₀) ^ (-(η / 2)) :=
        Real.rpow_le_rpow_of_nonpos hkD hj2.le (by linarith)
      rw [e1]
      calc K * (((2 : ℝ) ^ j) ^ (-(η / 2)) * ((2 : ℝ) ^ j) ^ (-(η / 2)))
          ≤ K * (((k : ℝ) ^ D₀) ^ (-(η / 2)) * q ^ j) := by
            refine mul_le_mul_of_nonneg_left ?_ hK0
            rw [e2] at e3 ⊢
            exact mul_le_mul e3 le_rfl (by positivity) (by positivity)
        _ = _ := by ring
    have hgeo : ∑ j ∈ highJ D₀ k, q ^ j ≤ (1 - q)⁻¹ := by
      refine ((summable_geometric_of_lt_one hq0.le hq1).sum_le_tsum _
        (fun j _ => by positivity)).trans ?_
      rw [tsum_geometric_of_lt_one hq0.le hq1]
    have hreal : ∑ j ∈ highJ D₀ k, K * ((2 : ℝ) ^ j) ^ (-η) ≤
        K * (1 - q)⁻¹ * (k : ℝ) ^ (-(D₀ * (η / 2))) := by
      calc _ ≤ ∑ j ∈ highJ D₀ k, K * ((k : ℝ) ^ D₀) ^ (-(η / 2)) * q ^ j :=
            Finset.sum_le_sum hb
        _ = K * ((k : ℝ) ^ D₀) ^ (-(η / 2)) * ∑ j ∈ highJ D₀ k, q ^ j := by
            rw [← Finset.mul_sum]
        _ ≤ K * ((k : ℝ) ^ D₀) ^ (-(η / 2)) * (1 - q)⁻¹ :=
            mul_le_mul_of_nonneg_left hgeo (by positivity)
        _ = K * (1 - q)⁻¹ * (k : ℝ) ^ (-(D₀ * (η / 2))) := by
            have e : (k : ℝ) ^ (-(D₀ * (η / 2))) = ((k : ℝ) ^ D₀) ^ (-(η / 2)) := by
              rw [← Real.rpow_mul hk0.le]; congr 1; ring
            rw [e]; ring
    calc ∑ j ∈ highJ D₀ k, eLpNorm (supOp (pairW ψ k j) (⇑f)) (ENNReal.ofReal p) Measure.count
        ≤ ∑ j ∈ highJ D₀ k, ENNReal.ofReal (K * ((2 : ℝ) ^ j) ^ (-η)) *
            eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count :=
          Finset.sum_le_sum fun j hj => hpair k j (hmem j hj).1 f
      _ = (∑ j ∈ highJ D₀ k, ENNReal.ofReal (K * ((2 : ℝ) ^ j) ^ (-η))) *
            eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
          rw [Finset.sum_mul]
      _ = ENNReal.ofReal (∑ j ∈ highJ D₀ k, K * ((2 : ℝ) ^ j) ^ (-η)) *
            eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => by positivity)]
      _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal hreal) le_rfl
  -- summation over `k`
  have hexp : ∀ k : ℕ, 1 ≤ k →
      (k : ℝ) ^ (-(D₀ * (η / 2))) ≤ (k : ℝ) ^ (-2 : ℝ) := by
    intro k hk
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    refine Real.rpow_le_rpow_of_exponent_le hk1 ?_
    have h2 : (2 : ℝ) ≤ D₀ * (η / 2) := by
      have h3 : (2 : ℝ) = (4 / η) * (η / 2) := by field_simp; norm_num
      calc (2 : ℝ) = (4 / η) * (η / 2) := h3
        _ ≤ D₀ * (η / 2) := mul_le_mul_of_nonneg_right hD₀ (by positivity)
    linarith
  have hq1' : 0 ≤ (1 - q)⁻¹ := inv_nonneg.2 (by linarith)
  refine ⟨K * (1 - q)⁻¹ * ∑' k : ℕ, (((k + 1 : ℕ) : ℝ)) ^ (-2 : ℝ), by positivity, fun f => ?_⟩
  calc ∑' k : ℕ, ∑ j ∈ highJ D₀ (k + 1),
        eLpNorm (supOp (pairW ψ (k + 1) j) (⇑f)) (ENNReal.ofReal p) Measure.count
      ≤ ∑' k : ℕ, ENNReal.ofReal (K * (1 - q)⁻¹ * (((k + 1 : ℕ) : ℝ)) ^ (-2 : ℝ)) *
          eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
        refine ENNReal.tsum_le_tsum fun k => (hjsum (k + 1) (by omega) f).trans ?_
        refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
        exact mul_le_mul_of_nonneg_left (hexp (k + 1) (by omega)) (mul_nonneg hK0 hq1')
    _ = _ := tsum_ofReal_shift_sq_mul _ (mul_nonneg hK0 hq1') _

/-- **The leftover pairs for the maximal operator**: for `p ≥ 1` and every `D₀`, the finite set
`{(k, 2^j) : k ≥ 1, M(k) < 2^j ≤ k^{D₀}}` of leftover pairs contributes
`∑ ‖sup_λ|∑_n f(x-n) w_Q(n) ψ_k(n) e(λ n)|‖_{ℓ^p} ≤ C(D₀, p) ‖f‖_{ℓ^p}`. -/
theorem leftover_pairs_sup (ψ : PsiData) {p : ℝ} (hp : 1 ≤ p) (D₀ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℤ →₀ ℂ,
      ∑ q ∈ (leftoverSet_finite D₀).toFinset,
          eLpNorm (supOp (pairW ψ q.1 q.2) (⇑f)) (ENNReal.ofReal p) Measure.count ≤
        ENNReal.ofReal C * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
  set c : ℕ × ℕ → ℝ≥0∞ := fun q => ∑' n : ℤ, ‖pairW ψ q.1 q.2 n‖ₑ with hc
  have hfin : ∀ q : ℕ × ℕ, c q ≠ ⊤ := by
    intro q
    obtain ⟨M, hM⟩ : ∃ M : ℕ, M = 2 ^ q.1 := ⟨_, rfl⟩
    have hS : ∀ n ∉ Finset.Ioo (-(M : ℤ)) (M : ℤ), ‖pairW ψ q.1 q.2 n‖ₑ = 0 := by
      intro n hn
      by_contra h
      have h0 : pairW ψ q.1 q.2 n ≠ 0 := fun h0 => h (by simp [h0])
      have hne : psiKz ψ q.1 n ≠ 0 := fun h1 => h0 (by simp [pairW, h1])
      have h2 : n.natAbs < M := by rw [hM]; exact_mod_cast (psiKz_ne_zero ψ hne).2
      apply hn
      rw [Finset.mem_Ioo]
      omega
    rw [hc]
    simp only
    rw [tsum_eq_sum hS]
    exact (ENNReal.sum_lt_top.2 fun n _ => enorm_lt_top).ne
  have hsum : ∑ q ∈ (leftoverSet_finite D₀).toFinset, c q ≠ ⊤ :=
    (ENNReal.sum_lt_top.2 fun q _ => (hfin q).lt_top).ne
  refine ⟨(∑ q ∈ (leftoverSet_finite D₀).toFinset, c q).toReal, ENNReal.toReal_nonneg,
    fun f => ?_⟩
  rw [ENNReal.ofReal_toReal hsum, Finset.sum_mul]
  exact Finset.sum_le_sum fun q _ => eLpNorm_supOp_le hp _ _

end PrimeCarleson.Proof.Paper
