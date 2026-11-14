module

public import PrimeCarleson.Proof.FplusProp21.DiagSum
public import PrimeCarleson.Proof.FplusProp21.ExpSum

/-!
# [F+] Proposition 2.1: `‖Λ_Q‖_{U³[M]} ≲_ε Q^{ε - 3/8}` for `M ≥ Q^{20}`

[F+] TeX L714–L791. The steps, with their sources:

* [F+] L781–L791 (the diagonal reduction) and `expansion-non-diagonal`, L758–L776, combined
  (`gowersNorm_blockWeight_pow_eight_le`): splitting the expansion [F+] `expansion-u3-norm`
  (L738–L748) into the tuples with every `L_j ∈ ℤ` (where `W_M(L) = ‖1_{[M]}‖⁸`) and the others
  (where `|W_M(L)| ≤ (2M + 1)³ ∏ q_ω ≤ (2M+1)³ Q⁸`, the denominator of every `L_j` dividing
  `∏ q_ω`), and summing `|∏ μ(q_ω)/φ(q_ω)|` over all tuples (at most `|B|⁸`),
  `‖w_B 1_{[M]}‖⁸ ≤ S_0 ‖1_{[M]}‖⁸ + |B|⁸ (2M + 1)³ Q⁸`;
* [F+] L549 (the norm of the indicator of an interval), upper side
  (`gowersNorm_indicator_pow_eight_le`): `‖1_{[M]}‖_{U³(ℤ)}⁸ ≤ (2M + 1)⁴`; the lower side
  `M⁴ ≤ 256 ‖1_{[M]}‖⁸` is `Common.gowersNorm_three_indicator_ge`;
* [F+] `e;fixedScaleToProve`, L733–L737 (`exists_gowersNorm_blockWeight_pow_eight_le`):
  `‖w_B 1_{[M]}‖_{U³(ℤ)}⁸ ≤ C_ε M⁴ Q^{-3+ε}` for `M ≥ Q^{20}` (the source prints `M > Q^{20}`);
* [F+] `p:Jan`, L714–L721 (`exists_gowersNormInterval_blockWeight_le`, for every finite set
  `B ⊆ [Q/2, Q]` of denominators): `‖w_B‖_{U³[M]} ≤ C_ε Q^{ε - 3/8}` for all real `Q ≥ 1` and all
  `M ≥ Q^{20}`.

Here `w_B = PrimeCarleson.blockWeight B = ∑_{q ∈ B} μ(q)/φ(q) c_q` and the norm is the
`PrimeCarleson.gowersNormInterval 3 M`, `‖g 1_{[M]}‖_{U³(ℤ)} / ‖1_{[M]}‖_{U³(ℤ)}`. No condition
"`Q` large" is needed: every estimate above holds for all `Q ≥ 1`.
-/

@[expose] public noncomputable section

open Finset

set_option autoImplicit false

namespace PrimeCarleson.Proof.FplusProp21

/-- `|μ(q)/φ(q)| = μ²(q)/φ(q)`. -/
theorem abs_qaCoef (t : Σ _ : ℕ, ℕ) : |qaCoef t| = muSqDivTotient t.1 := by
  unfold qaCoef muSqDivTotient
  rw [abs_div, Nat.abs_cast]
  congr 1
  have h := ArithmeticFunction.abs_moebius_le_one (n := t.1)
  rcases (abs_le.1 h) with ⟨h1, h2⟩
  have : ArithmeticFunction.moebius t.1 = -1 ∨ ArithmeticFunction.moebius t.1 = 0 ∨
      ArithmeticFunction.moebius t.1 = 1 := by omega
  rcases this with h | h | h <;> simp [h]

/-- `‖∏_ω μ(q_ω)/φ(q_ω)‖ = ∏_ω μ²(q_ω)/φ(q_ω)`. -/
theorem norm_prod_qaCoef (τ : Cube → Σ _ : ℕ, ℕ) :
    ‖∏ ω, (qaCoef (τ ω) : ℂ)‖ = ∏ ω, muSqDivTotient (τ ω).1 := by
  rw [norm_prod]
  refine prod_congr rfl fun ω _ => ?_
  rw [Complex.norm_real, Real.norm_eq_abs, abs_qaCoef]

/-- `#{1 ≤ a ≤ q : (a, q) = 1} = φ(q)`. -/
theorem card_filter_coprime_Icc (q : ℕ) :
    ((Icc 1 q).filter (fun a => Nat.Coprime a q)).card = q.totient := by
  have := Nat.filter_coprime_Ico_eq_totient q 1
  rw [show Ico 1 (1 + q) = Icc 1 q by ext; simp; omega] at this
  rw [← this]
  congr 1
  ext a
  simp [Nat.coprime_comm]

/-- Summing the coefficients over all tuples: `∑_{(q_ω, a_ω)} ∏ μ²(q_ω)/φ(q_ω) ≤ |B|⁸`
("summing all `a_ω` coprime to `q_ω` cancels the totient", [F+] L771-L775). -/
theorem sum_prod_muSqDivTotient_le (B : Finset ℕ) (hB : ∀ q ∈ B, q ≠ 0) :
    ∑ τ ∈ Fintype.piFinset (fun _ : Cube => qaPairs B), ∏ ω, muSqDivTotient (τ ω).1 ≤
      (B.card : ℝ) ^ 8 := by
  classical
  rw [← prod_univ_sum (fun _ : Cube => qaPairs B) (fun _ t => muSqDivTotient t.1), prod_const]
  have hcard : (univ : Finset Cube).card = 8 := by simp
  rw [hcard]
  refine pow_le_pow_left₀ (sum_nonneg fun t _ => muSqDivTotient_nonneg _) ?_ 8
  rw [qaPairs, sum_sigma]
  calc ∑ q ∈ B, ∑ _a ∈ (Icc 1 q).filter (fun a => Nat.Coprime a q), muSqDivTotient q
      ≤ ∑ _q ∈ B, (1 : ℝ) := by
        refine sum_le_sum fun q hq => ?_
        rw [sum_const, nsmul_eq_mul]
        rw [card_filter_coprime_Icc]
        have hφ0 : (q.totient : ℝ) ≠ 0 := by
          exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero (hB q hq))).ne'
        unfold muSqDivTotient
        rw [mul_div_cancel₀ _ hφ0]
        have h := ArithmeticFunction.abs_moebius_le_one (n := q)
        have h' : |((ArithmeticFunction.moebius q : ℤ) : ℝ)| ≤ 1 := by exact_mod_cast h
        nlinarith [abs_nonneg ((ArithmeticFunction.moebius q : ℤ) : ℝ), sq_abs
          ((ArithmeticFunction.moebius q : ℤ) : ℝ)]
    _ = B.card := by simp

/-- `∏ q_ω · θ_ω ∈ ℤ`: the denominator of every `θ_ω` divides `∏ q_ω`. -/
theorem isInt_prod_mul_tupleTheta (τ : Cube → Σ _ : ℕ, ℕ) (hq : ∀ ω, (τ ω).1 ≠ 0) (ω : Cube) :
    IsInt (((∏ ν, (τ ν).1 : ℕ) : ℝ) * tupleTheta τ ω) := by
  have hdvd : (τ ω).1 ∣ ∏ ν, (τ ν).1 := dvd_prod_of_mem _ (mem_univ ω)
  refine ⟨cubeSign ω * (((τ ω).2 * ((∏ ν, (τ ν).1) / (τ ω).1) : ℕ) : ℤ), ?_⟩
  have hqω : ((τ ω).1 : ℝ) ≠ 0 := by exact_mod_cast hq ω
  simp only [tupleTheta, cubeTheta]
  rw [Int.cast_mul, Int.cast_natCast, Nat.cast_mul, Nat.cast_div hdvd hqω]
  field_simp

/-- The linear forms of a tuple have denominators dividing `∏ q_ω`. -/
theorem isInt_prod_mul_cubeL (τ : Cube → Σ _ : ℕ, ℕ) (hq : ∀ ω, (τ ω).1 ≠ 0) :
    IsInt (((∏ ν, (τ ν).1 : ℕ) : ℝ) * cubeL0 (tupleTheta τ)) ∧
      ∀ i, IsInt (((∏ ν, (τ ν).1 : ℕ) : ℝ) * cubeLi (tupleTheta τ) i) := by
  refine ⟨?_, fun i => ?_⟩
  · rw [cubeL0, mul_sum]
    exact IsInt.sum _ fun ω _ => isInt_prod_mul_tupleTheta τ hq ω
  · rw [cubeLi, mul_sum]
    refine IsInt.sum _ fun ω _ => ?_
    have := (isInt_prod_mul_tupleTheta τ hq ω).intCast_mul ((ω i : ℕ) : ℤ)
    convert this using 1
    push_cast
    ring

/-- **`‖1_{[M]}‖_{U³(ℤ)}⁸ ≤ (2M + 1)⁴`** (Source: [F+] L549, upper side): the parallelepipeds inside
`[M]` have `x, h_i ∈ [-M, M]`. -/
theorem gowersNorm_indicator_pow_eight_le (M : ℕ+) :
    gowersNorm 3 (restrictInterval M 1) ^ 8 ≤ (2 * (M : ℝ) + 1) ^ 4 := by
  have h := gowersNorm_indicator_pow_eight M
  have h0 : 0 ≤ gowersNorm 3 (restrictInterval M 1) :=
    (PrimeCarleson.gowersNorm_spec 3 _).2.1
  have hn : gowersNorm 3 (restrictInterval M 1) ^ 8 = ‖cubeW M 0 0 0 0‖ := by
    rw [← h, norm_pow, Complex.norm_of_nonneg h0]
  rw [hn]
  have hJc : ((Icc (-((M : ℕ) : ℤ)) (M : ℕ)).card : ℝ) = 2 * M + 1 := by
    rw [Int.card_Icc]
    have : ((M : ℕ) + 1 - -((M : ℕ) : ℤ)).toNat = 2 * (M : ℕ) + 1 := by omega
    rw [this]
    push_cast
    ring
  unfold cubeW
  calc ‖∑ x ∈ Icc (-((M : ℕ) : ℤ)) (M : ℕ), ∑ a ∈ Icc (-((M : ℕ) : ℤ)) (M : ℕ),
        ∑ b ∈ Icc (-((M : ℕ) : ℤ)) (M : ℕ), ∑ k ∈ Icc (-((M : ℕ) : ℤ)) (M : ℕ),
          if CubeIn M x a b k then e (x * 0 + a * 0 + b * 0 + k * 0) else 0‖
      ≤ ∑ x ∈ Icc (-((M : ℕ) : ℤ)) (M : ℕ), ∑ a ∈ Icc (-((M : ℕ) : ℤ)) (M : ℕ),
        ∑ b ∈ Icc (-((M : ℕ) : ℤ)) (M : ℕ), ∑ k ∈ Icc (-((M : ℕ) : ℤ)) (M : ℕ), (1 : ℝ) :=
        norm_sum_le_of_le _ fun x _ => norm_sum_le_of_le _ fun a _ =>
          norm_sum_le_of_le _ fun b _ => norm_sum_le_of_le _ fun k _ => by
            split_ifs
            · rw [Goal0.norm_e]
            · simp
    _ = (2 * (M : ℝ) + 1) ^ 4 := by
        simp only [sum_const, nsmul_eq_mul, mul_one]
        rw [hJc]
        ring

/-- **Diagonal and off-diagonal parts together** (Source: [F+] L758–L787): for denominators
`1 ≤ q ≤ Q`, `‖w_B 1_{[M]}‖⁸ ≤ S_0 ‖1_{[M]}‖⁸ + |B|⁸ (2M + 1)³ Q⁸`. -/
theorem gowersNorm_blockWeight_pow_eight_le (B : Finset ℕ) (Q : ℝ)
    (hB : ∀ q ∈ B, 1 ≤ q ∧ (q : ℝ) ≤ Q) (M : ℕ+) :
    gowersNorm 3 (restrictInterval M (blockWeight B)) ^ 8 ≤
      diagSum B * gowersNorm 3 (restrictInterval M 1) ^ 8 +
        (B.card : ℝ) ^ 8 * ((2 * (M : ℝ) + 1) ^ 3 * Q ^ 8) := by
  classical
  set T := Fintype.piFinset (fun _ : Cube => qaPairs B) with hT
  set C : (Cube → Σ _ : ℕ, ℕ) → ℂ := fun τ => ∏ ω, (qaCoef (τ ω) : ℂ) with hC
  set L : (Cube → Σ _ : ℕ, ℕ) → ℂ := fun τ => cubeW M (cubeL0 (tupleTheta τ))
    (cubeLi (tupleTheta τ) 0) (cubeLi (tupleTheta τ) 1) (cubeLi (tupleTheta τ) 2) with hL
  set V8 : ℝ := gowersNorm 3 (restrictInterval M 1) ^ 8 with hV8
  have hB0 : ∀ q ∈ B, q ≠ 0 := fun q hq => by have := (hB q hq).1; omega
  have hτq : ∀ τ ∈ T, ∀ ω, (τ ω).1 ∈ B := by
    intro τ hτ ω
    have := Fintype.mem_piFinset.1 hτ ω
    simp only [qaPairs, mem_sigma] at this
    exact this.1
  have hF0 : 0 ≤ gowersNorm 3 (restrictInterval M (blockWeight B)) :=
    (PrimeCarleson.gowersNorm_spec 3 _).2.1
  have hV0 : 0 ≤ gowersNorm 3 (restrictInterval M 1) := (PrimeCarleson.gowersNorm_spec 3 _).2.1
  have hexp := gowersNorm_blockWeight_pow_eight B M
  have hnorm : gowersNorm 3 (restrictInterval M (blockWeight B)) ^ 8 =
      ‖∑ τ ∈ T, C τ * L τ‖ := by
    rw [← hexp, norm_pow, Complex.norm_of_nonneg hF0]
  rw [hnorm, ← sum_filter_add_sum_filter_not T (fun τ => CubeDiag (tupleTheta τ))]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · -- the diagonal tuples
    have hdiag : ∀ τ ∈ T.filter (fun τ => CubeDiag (tupleTheta τ)),
        C τ * L τ = C τ * ((V8 : ℝ) : ℂ) := by
      intro τ hτ
      have hd := (mem_filter.1 hτ).2
      simp only [hL, hV8]
      rw [cubeW_eq_of_isInt M hd.1 (hd.2 0) (hd.2 1) (hd.2 2), ← gowersNorm_indicator_pow_eight]
      push_cast
      rfl
    rw [sum_congr rfl hdiag, ← sum_mul, norm_mul, Complex.norm_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_right ((norm_sum_le _ _).trans (le_of_eq ?_)) (by positivity)
    unfold diagSum
    refine sum_congr rfl fun τ _ => ?_
    exact norm_prod_qaCoef τ
  · -- the off-diagonal tuples
    calc ‖∑ τ ∈ T.filter (fun τ => ¬ CubeDiag (tupleTheta τ)), C τ * L τ‖
        ≤ ∑ τ ∈ T.filter (fun τ => ¬ CubeDiag (tupleTheta τ)),
            (∏ ω, muSqDivTotient (τ ω).1) * ((2 * (M : ℝ) + 1) ^ 3 * Q ^ 8) := by
          refine norm_sum_le_of_le _ fun τ hτ => ?_
          rw [mem_filter] at hτ
          have hq : ∀ ω, (τ ω).1 ≠ 0 := fun ω => hB0 _ (hτq τ hτ.1 ω)
          rw [norm_mul, norm_prod_qaCoef]
          refine mul_le_mul_of_nonneg_left ?_ (prod_nonneg fun ω _ => muSqDivTotient_nonneg _)
          obtain ⟨h0, hi⟩ := isInt_prod_mul_cubeL τ hq
          have hD : 0 < ∏ ν, (τ ν).1 := prod_pos fun ν _ => Nat.pos_of_ne_zero (hq ν)
          have hnd : ¬ (IsInt (cubeL0 (tupleTheta τ)) ∧ IsInt (cubeLi (tupleTheta τ) 0) ∧
              IsInt (cubeLi (tupleTheta τ) 1) ∧ IsInt (cubeLi (tupleTheta τ) 2)) := by
            rintro ⟨a0, a1, a2, a3⟩
            refine hτ.2 ⟨a0, fun i => ?_⟩
            fin_cases i
            · exact a1
            · exact a2
            · exact a3
          refine (norm_cubeW_le M hD h0 (hi 0) (hi 1) (hi 2) hnd).trans ?_
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          push_cast
          calc ∏ ν, ((τ ν).1 : ℝ) ≤ ∏ _ν : Cube, Q :=
                prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun ν _ => (hB _ (hτq τ hτ.1 ν)).2)
            _ = Q ^ 8 := by simp
      _ ≤ ∑ τ ∈ T, (∏ ω, muSqDivTotient (τ ω).1) * ((2 * (M : ℝ) + 1) ^ 3 * Q ^ 8) :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun τ _ _ =>
            mul_nonneg (prod_nonneg fun ω _ => muSqDivTotient_nonneg _) (by positivity)
      _ ≤ (B.card : ℝ) ^ 8 * ((2 * (M : ℝ) + 1) ^ 3 * Q ^ 8) := by
          rw [← sum_mul]
          exact mul_le_mul_of_nonneg_right (sum_prod_muSqDivTotient_le B hB0) (by positivity)

/-- **`‖1_{[M]}‖_{U³(ℤ)}⁸ ≥ M⁴ / 256`** (Source: [F+] L549, lower side, from
`Common.gowersNorm_three_indicator_ge`). -/
theorem gowersNorm_indicator_pow_eight_ge (M : ℕ+) :
    (M : ℝ) ^ 4 ≤ 256 * gowersNorm 3 (restrictInterval M 1) ^ 8 := by
  have h := Common.gowersNorm_three_indicator_ge 1 M
  have hI : Icc (1 : ℤ) (1 + ((M : ℕ) : ℤ) - 1) = Icc (1 : ℤ) (M : ℕ) := by
    ext x
    simp only [mem_Icc]
    omega
  rw [hI] at h
  exact h

/-- The denominators of a block in `[Q/2, Q]` are positive and there are at most `Q` of them. -/
theorem card_le_of_subset_Icc {Q : ℝ} (hQ : 1 ≤ Q) {B : Finset ℕ}
    (hB : ∀ q ∈ B, Q / 2 ≤ (q : ℝ) ∧ (q : ℝ) ≤ Q) :
    (∀ q ∈ B, 1 ≤ q ∧ (q : ℝ) ≤ Q) ∧ (B.card : ℝ) ≤ Q := by
  have h1 : ∀ q ∈ B, 1 ≤ q ∧ (q : ℝ) ≤ Q := by
    intro q hq
    refine ⟨Nat.one_le_iff_ne_zero.2 fun h => ?_, (hB q hq).2⟩
    have := (hB q hq).1
    rw [h, Nat.cast_zero] at this
    linarith
  refine ⟨h1, ?_⟩
  have hsub : B ⊆ Icc 1 ⌊Q⌋₊ := fun q hq =>
    mem_Icc.2 ⟨(h1 q hq).1, Nat.le_floor (h1 q hq).2⟩
  calc (B.card : ℝ) ≤ ((Icc 1 ⌊Q⌋₊).card : ℝ) := by exact_mod_cast card_le_card hsub
    _ = ⌊Q⌋₊ := by simp
    _ ≤ Q := Nat.floor_le (by linarith)

/-- **(e;fixedScaleToProve)** (Source: [F+] `e;fixedScaleToProve`, L733–L737): for every `ε > 0`
there is `C_ε` with `‖w_B 1_{[M]}‖_{U³(ℤ)}⁸ ≤ C_ε M⁴ Q^{-3+ε}` for all `Q ≥ 1`, all finite
`B ⊆ [Q/2, Q]` and all `M ≥ Q^{20}`. -/
theorem exists_gowersNorm_blockWeight_pow_eight_le {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Q : ℝ, 1 ≤ Q → ∀ B : Finset ℕ,
      (∀ q ∈ B, Q / 2 ≤ (q : ℝ) ∧ (q : ℝ) ≤ Q) → ∀ M : ℕ+, Q ^ 20 ≤ (M : ℝ) →
        gowersNorm 3 (restrictInterval M (blockWeight B)) ^ 8 ≤
          C * (M : ℝ) ^ 4 * Q ^ (-3 + ε) := by
  obtain ⟨C₁, hC₁, hdiag⟩ := exists_diagSum_le hε
  refine ⟨81 * C₁ + 27, by positivity, fun Q hQ B hB M hM => ?_⟩
  obtain ⟨hB1, hcard⟩ := card_le_of_subset_Icc hQ hB
  have hQpos : 0 < Q := by linarith
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast M.pos
  have hmain := gowersNorm_blockWeight_pow_eight_le B Q hB1 M
  have hV := gowersNorm_indicator_pow_eight_le M
  have hV0 : 0 ≤ gowersNorm 3 (restrictInterval M 1) ^ 8 := by
    have := (PrimeCarleson.gowersNorm_spec 3 (restrictInterval M 1)).2.1
    positivity
  have hD := hdiag Q hQ B hB
  have hD0 : 0 ≤ diagSum B := by
    unfold diagSum
    exact sum_nonneg fun τ _ => prod_nonneg fun ω _ => muSqDivTotient_nonneg _
  have hrpow0 : 0 < Q ^ (-3 + ε) := Real.rpow_pos_of_pos hQpos _
  have hQ3 : (Q ^ 3)⁻¹ ≤ Q ^ (-3 + ε) := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg hQpos.le]
    exact Real.rpow_le_rpow_of_exponent_le hQ (by push_cast; linarith)
  -- the diagonal part
  have h1 : diagSum B * gowersNorm 3 (restrictInterval M 1) ^ 8 ≤
      81 * C₁ * (M : ℝ) ^ 4 * Q ^ (-3 + ε) := by
    calc diagSum B * gowersNorm 3 (restrictInterval M 1) ^ 8
        ≤ (C₁ * Q ^ (-3 + ε)) * (81 * (M : ℝ) ^ 4) := by
          refine mul_le_mul hD (hV.trans ?_) hV0 (by positivity)
          nlinarith [pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 2 * M + 1)
            (by linarith : 2 * (M : ℝ) + 1 ≤ 3 * M) 4]
      _ = 81 * C₁ * (M : ℝ) ^ 4 * Q ^ (-3 + ε) := by ring
  -- the off-diagonal part
  have h2 : (B.card : ℝ) ^ 8 * ((2 * (M : ℝ) + 1) ^ 3 * Q ^ 8) ≤
      27 * (M : ℝ) ^ 4 * Q ^ (-3 + ε) := by
    have hc8 : (B.card : ℝ) ^ 8 ≤ Q ^ 8 := pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 8
    have hM3 : (2 * (M : ℝ) + 1) ^ 3 ≤ 27 * (M : ℝ) ^ 3 := by
      have := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 2 * M + 1)
        (by linarith : 2 * (M : ℝ) + 1 ≤ 3 * M) 3
      nlinarith
    have hQ17 : Q ^ 16 ≤ Q ^ 17 := pow_le_pow_right₀ hQ (by norm_num)
    calc (B.card : ℝ) ^ 8 * ((2 * (M : ℝ) + 1) ^ 3 * Q ^ 8)
        ≤ Q ^ 8 * (27 * (M : ℝ) ^ 3 * Q ^ 8) :=
          mul_le_mul hc8 (mul_le_mul_of_nonneg_right hM3 (by positivity)) (by positivity)
            (by positivity)
      _ = 27 * (M : ℝ) ^ 3 * Q ^ 16 := by ring
      _ ≤ 27 * (M : ℝ) ^ 3 * (Q ^ 20 * (Q ^ 3)⁻¹) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [show Q ^ 20 = Q ^ 17 * Q ^ 3 by ring, mul_inv_cancel_right₀ (by positivity)]
          exact hQ17
      _ ≤ 27 * (M : ℝ) ^ 3 * ((M : ℝ) * Q ^ (-3 + ε)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hM hQ3 (by positivity) (by positivity))
            (by positivity)
      _ = 27 * (M : ℝ) ^ 4 * Q ^ (-3 + ε) := by ring
  calc gowersNorm 3 (restrictInterval M (blockWeight B)) ^ 8
      ≤ diagSum B * gowersNorm 3 (restrictInterval M 1) ^ 8 +
          (B.card : ℝ) ^ 8 * ((2 * (M : ℝ) + 1) ^ 3 * Q ^ 8) := hmain
    _ ≤ 81 * C₁ * (M : ℝ) ^ 4 * Q ^ (-3 + ε) + 27 * (M : ℝ) ^ 4 * Q ^ (-3 + ε) :=
        add_le_add h1 h2
    _ = (81 * C₁ + 27) * (M : ℝ) ^ 4 * Q ^ (-3 + ε) := by ring

/-- **[F+] Proposition 2.1 for every block in `[Q/2, Q]`**: for every `ε > 0` there is `C_ε`
with `‖w_B‖_{U³[M]} ≤ C_ε Q^{ε - 3/8}` for all real `Q ≥ 1`, every finite set `B` of
denominators `Q/2 ≤ q ≤ Q`, and every `M ≥ Q^{20}`. -/
theorem exists_gowersNormInterval_blockWeight_le {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ Q : ℝ, 1 ≤ Q → ∀ B : Finset ℕ,
      (∀ q ∈ B, Q / 2 ≤ (q : ℝ) ∧ (q : ℝ) ≤ Q) → ∀ M : ℕ+, Q ^ 20 ≤ (M : ℝ) →
        gowersNormInterval 3 M (blockWeight B) ≤ C * Q ^ (ε - 3 / 8) := by
  obtain ⟨C, hC0, hC⟩ := exists_gowersNorm_blockWeight_pow_eight_le (ε := 8 * ε) (by positivity)
  refine ⟨(256 * C) ^ ((1 : ℝ) / 8), fun Q hQ B hB M hM => ?_⟩
  have hQpos : 0 < Q := by linarith
  set F := gowersNorm 3 (restrictInterval M (blockWeight B)) with hF
  set V := gowersNorm 3 (restrictInterval M 1) with hVdef
  have hF0 : 0 ≤ F := (PrimeCarleson.gowersNorm_spec 3 _).2.1
  have hV0 : 0 ≤ V := (PrimeCarleson.gowersNorm_spec 3 _).2.1
  have hlow := gowersNorm_indicator_pow_eight_ge M
  have hMpos : (0 : ℝ) < M := by exact_mod_cast M.pos
  have hV8 : 0 < V ^ 8 := by
    have : (0 : ℝ) < (M : ℝ) ^ 4 := by positivity
    linarith
  have hx0 : 0 ≤ F / V := div_nonneg hF0 hV0
  have hx8 : (F / V) ^ 8 ≤ 256 * C * Q ^ (-3 + 8 * ε) := by
    rw [div_pow, div_le_iff₀ hV8]
    calc F ^ 8 ≤ C * (M : ℝ) ^ 4 * Q ^ (-3 + 8 * ε) := hC Q hQ B hB M hM
      _ ≤ C * (256 * V ^ 8) * Q ^ (-3 + 8 * ε) := by
          gcongr
      _ = 256 * C * Q ^ (-3 + 8 * ε) * V ^ 8 := by ring
  have hroot : F / V = ((F / V) ^ 8) ^ ((1 : ℝ) / 8) := by
    have := Real.pow_rpow_inv_natCast hx0 (n := 8) (by norm_num)
    rw [show ((8 : ℕ) : ℝ)⁻¹ = (1 : ℝ) / 8 by norm_num] at this
    exact this.symm
  unfold gowersNormInterval
  rw [← hF, ← hVdef, hroot]
  calc ((F / V) ^ 8) ^ ((1 : ℝ) / 8) ≤ (256 * C * Q ^ (-3 + 8 * ε)) ^ ((1 : ℝ) / 8) :=
        Real.rpow_le_rpow (by positivity) hx8 (by norm_num)
    _ = (256 * C) ^ ((1 : ℝ) / 8) * Q ^ (ε - 3 / 8) := by
        rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hQpos.le _), ← Real.rpow_mul hQpos.le]
        congr 2
        ring

end PrimeCarleson.Proof.FplusProp21
