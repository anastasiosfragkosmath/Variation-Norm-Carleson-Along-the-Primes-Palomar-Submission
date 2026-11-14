module

public import PrimeCarleson.Proof.Paper.P6a.Hyps
public import PrimeCarleson.Proof.FplusProp21.Application
public import PrimeCarleson.Proof.Paper.Defs.Gowers

/-!
# `U³` decay of the residual `w - w_{≤ M(k)}` on `[2^k]`

Source: main paper `e:minor-U3-var-red`, L1283–L1287, and the cutoff bridge: `[F+, Proposition 3.1]`
uses the cutoff `Q_N = exp((log N)^{1/10})`, which at `N = 2^k` is below `M(k) = exp(k^{1/10})`; the
dyadic blocks `Q_N < L ≤ M(k)` are controlled by `[F+, Proposition 2.1]`
(`FplusProp21.exists_gowersNormInterval_blockWeight_Ioc_two_pow_le`) and the triangle inequality for
`U³`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson

/-- Triangle inequality for finite sums in `gowersNormOn`. -/
theorem gowersNormOn_sum_le {ι : Type*} (s : ℕ+) (I : Finset ℤ) (t : Finset ι) (g : ι → ℤ → ℂ) :
    gowersNormOn s I (fun n => ∑ j ∈ t, g j n) ≤ ∑ j ∈ t, gowersNormOn s I (g j) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    have h0 : (fun n => ∑ j ∈ (∅ : Finset ι), g j n) = (0 : ℂ) • (fun _ : ℤ => (1 : ℂ)) := by
      funext n; simp
    rw [h0, gowersNormOn_smul]; simp
  | insert j t hj ih =>
    have : (fun n => ∑ i ∈ insert j t, g i n) = g j + fun n => ∑ i ∈ t, g i n := by
      funext n
      simp [Finset.sum_insert hj]
    rw [this, Finset.sum_insert hj]
    exact (gowersNormOn_add_le s I _ _).trans (add_le_add_right ih _)

/-- `‖-g‖_{U^s(I)} = ‖g‖_{U^s(I)}`. -/
theorem gowersNormOn_neg' (s : ℕ+) (I : Finset ℤ) (g : ℤ → ℂ) :
    gowersNormOn s I (fun n => -g n) = gowersNormOn s I g := by
  have : (fun n => -g n) = (-1 : ℂ) • g := by funext n; simp
  rw [this, gowersNormOn_smul]; simp

/-- **The cutoff bridge, the triangle step**: for `k ≥ 1`, `N = 2^k` and
`Q_N = exp((log N)^{1/10})`,
`‖w - w_{≤ M(k)}‖_{U³([N])} ≤ ‖Λ - Λ_{≤ Q_N}‖_{U³([N])}
  + ∑_{j : Q_N < 2^j ≤ M(k)} ‖w_{2^j}‖_{U³([N])}`. -/
theorem cutoff_bridge_triangle (k : ℕ) (N : ℕ+) (hk : 1 ≤ k) (hN : (N : ℕ) = 2 ^ k) :
    gowersNormInterval 3 N (resWeight k) ≤
      gowersNormInterval 3 N
          (fun n => ((ArithmeticFunction.vonMangoldt n.toNat : ℝ) : ℂ) -
            heathBrownModel (Real.exp (Real.log N ^ ((1 : ℝ) / 10))) n) +
        ∑ j ∈ (jSet k).filter (fun j => Real.exp (Real.log N ^ ((1 : ℝ) / 10)) < (2 : ℝ) ^ j),
          gowersNormInterval 3 N (wQ (2 ^ j)) := by
  set QN : ℝ := Real.exp (Real.log N ^ ((1 : ℝ) / 10)) with hQN
  have hNr : ((N : ℕ+) : ℝ) = (2 : ℝ) ^ k := by
    have : ((N : ℕ+) : ℝ) = ((N : ℕ) : ℝ) := rfl
    rw [this, hN]; push_cast; rfl
  have hlogN : Real.log ((N : ℕ+) : ℝ) = k * Real.log 2 := by rw [hNr, Real.log_pow]
  have hlog2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hlog2' : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hQM : QN ≤ cutoffM k := by
    unfold cutoffM
    refine Real.exp_le_exp.2 (Real.rpow_le_rpow ?_ ?_ (by norm_num))
    · rw [hlogN]; positivity
    · rw [hlogN]; nlinarith [(by exact_mod_cast hk : (1 : ℝ) ≤ k)]
  have hjQ : ∀ j, j ∈ (jSet k).filter (fun j => (2 : ℝ) ^ j ≤ QN) ↔ (2 : ℝ) ^ j ≤ QN := by
    intro j
    rw [Finset.mem_filter, mem_jSet_iff]
    exact ⟨fun h => h.2, fun h => ⟨h.trans hQM, h⟩⟩
  have hHB : ∀ n, heathBrownModel QN n =
      ∑ j ∈ (jSet k).filter (fun j => (2 : ℝ) ^ j ≤ QN), wQ (2 ^ j) n :=
    fun n => heathBrownModel_eq_sum_of_mem_iff QN _ hjQ n
  have hsplit : ∀ n, wLeM k n = heathBrownModel QN n +
      ∑ j ∈ (jSet k).filter (fun j => QN < (2 : ℝ) ^ j), wQ (2 ^ j) n := by
    intro n
    have h1 : wLeM k n = ∑ j ∈ jSet k, wQ (2 ^ j) n := wLeM_eq_sum k n
    rw [hHB, h1, ← Finset.sum_filter_add_sum_filter_not (jSet k) (fun j => (2 : ℝ) ^ j ≤ QN)]
    congr 1
    exact Finset.sum_congr (Finset.filter_congr fun j _ => not_le) fun _ _ => rfl
  set F := (jSet k).filter (fun j => QN < (2 : ℝ) ^ j) with hF
  set I : Finset ℤ := Finset.Icc (1 : ℤ) N with hI
  have hcongr : ∀ n ∈ I, resWeight k n =
      ((fun n : ℤ => ((ArithmeticFunction.vonMangoldt n.toNat : ℝ) : ℂ) -
          heathBrownModel QN n) + fun n => -∑ j ∈ F, wQ (2 ^ j) n) n := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.1 hn).1
    have : wFun n = ((ArithmeticFunction.vonMangoldt n.toNat : ℝ) : ℂ) := by
      unfold wFun
      congr 3
      omega
    simp only [resWeight, Pi.add_apply, this, hsplit n]
    ring
  rw [gowersNormInterval_eq_gowersNormOn]
  simp only [gowersNormInterval_eq_gowersNormOn]
  calc gowersNormOn 3 I (resWeight k)
      = gowersNormOn 3 I ((fun n : ℤ => ((ArithmeticFunction.vonMangoldt n.toNat : ℝ) : ℂ) -
          heathBrownModel QN n) + fun n => -∑ j ∈ F, wQ (2 ^ j) n) :=
        gowersNormOn_congr 3 I hcongr
    _ ≤ _ + gowersNormOn 3 I (fun n => -∑ j ∈ F, wQ (2 ^ j) n) := gowersNormOn_add_le 3 I _ _
    _ ≤ _ := by
        rw [gowersNormOn_neg']
        exact add_le_add le_rfl (gowersNormOn_sum_le 3 I F (fun j n => wQ (2 ^ j) n))

/-- `exp(-(k log 2)^{1/10} / 8) ≤ C_A k^{-A}`: stretched-exponential decay beats every power. -/
theorem exp_neg_rpow_tenth_le (A : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 1 ≤ k →
      Real.exp (-((k * Real.log 2) ^ ((1 : ℝ) / 10)) / 8) ≤ C * (k : ℝ) ^ (-A) := by
  set m : ℕ := ⌈10 * max A 0⌉₊ with hm
  have hlog2' : 0 < Real.log 2 := Real.log_pos one_lt_two
  refine ⟨(m.factorial : ℝ) * 8 ^ m * (Real.log 2) ^ (-(m : ℝ) / 10), by positivity, fun k hk => ?_⟩
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set y : ℝ := (k * Real.log 2) ^ ((1 : ℝ) / 10) with hy
  have hy0 : 0 < y := by positivity
  have h1 := Real.pow_div_factorial_le_exp (y / 8) (by positivity) m
  have h2 : Real.exp (-y / 8) = (Real.exp (y / 8))⁻¹ := by rw [← Real.exp_neg]; ring_nf
  have h3 : (Real.exp (y / 8))⁻¹ ≤ (m.factorial : ℝ) * 8 ^ m * (y ^ m)⁻¹ := by
    have hpos : 0 < (y / 8) ^ m / m.factorial := by positivity
    calc (Real.exp (y / 8))⁻¹ ≤ ((y / 8) ^ m / m.factorial)⁻¹ := inv_anti₀ hpos h1
      _ = (m.factorial : ℝ) * 8 ^ m * (y ^ m)⁻¹ := by
          rw [div_pow]; field_simp
  have h4 : (y ^ m)⁻¹ = (k * Real.log 2) ^ (-(m : ℝ) / 10) := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity), ← Real.rpow_neg (by positivity)]
    congr 1; ring
  have h5 : (k * Real.log 2) ^ (-(m : ℝ) / 10) ≤
      (Real.log 2) ^ (-(m : ℝ) / 10) * (k : ℝ) ^ (-A) := by
    rw [Real.mul_rpow (by positivity) hlog2'.le, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hmA : A ≤ (m : ℝ) / 10 := by
      have : 10 * max A 0 ≤ m := Nat.le_ceil _
      have := le_max_left A 0
      linarith
    exact Real.rpow_le_rpow_of_exponent_le hk1 (by linarith)
  calc Real.exp (-y / 8) = (Real.exp (y / 8))⁻¹ := h2
    _ ≤ (m.factorial : ℝ) * 8 ^ m * (y ^ m)⁻¹ := h3
    _ ≤ (m.factorial : ℝ) * 8 ^ m * ((Real.log 2) ^ (-(m : ℝ) / 10) * (k : ℝ) ^ (-A)) := by
        rw [h4]; exact mul_le_mul_of_nonneg_left h5 (by positivity)
    _ = _ := by ring

/-- **The cutoff bridge**: for every `A` there is `C_A` with
`‖w - w_{≤ M(k)}‖_{U³([2^k])} ≤ C_A k^{-A}` for all `k ≥ 1` (from `[F+, Proposition 3.1]` and
`[F+, Proposition 2.1]`). -/
theorem cutoff_bridge (hF : FplusProp31) (A : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (N : ℕ+), 1 ≤ k → (N : ℕ) = 2 ^ k →
      gowersNormInterval 3 N (resWeight k) ≤ C * (k : ℝ) ^ (-A) := by
  obtain ⟨C₁, hC₁⟩ := hF (max A 1) (le_max_right _ _)
  obtain ⟨Cp, hCp⟩ := FplusProp21.exists_gowersNormInterval_blockWeight_Ioc_two_pow_le
    (ε := 1 / 8) (by norm_num)
  obtain ⟨Ce, hCe0, hCe⟩ := exp_neg_rpow_tenth_le A
  have hlog2' : 0 < Real.log 2 := Real.log_pos one_lt_two
  set q : ℝ := (2 : ℝ) ^ (-(1 / 8 : ℝ)) with hq
  have hq0 : 0 < q := by positivity
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  set c8 : ℝ := (1 - q)⁻¹ with hc8
  have hc80 : 0 ≤ c8 := inv_nonneg.2 (by linarith)
  refine ⟨|C₁| * (Real.log 2) ^ (-(max A 1)) + |Cp| * c8 * Ce, by positivity, fun k N hk hN => ?_⟩
  refine (cutoff_bridge_triangle k N hk hN).trans ?_
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hNr : ((N : ℕ+) : ℝ) = (2 : ℝ) ^ k := by
    have : ((N : ℕ+) : ℝ) = ((N : ℕ) : ℝ) := rfl
    rw [this, hN]; push_cast; rfl
  have hlogN : Real.log ((N : ℕ+) : ℝ) = k * Real.log 2 := by rw [hNr, Real.log_pow]
  -- the first term
  have hN2 : (2 : ℕ+) ≤ N := by
    have : (2 : ℕ) ≤ (N : ℕ) := by
      rw [hN]
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    exact_mod_cast this
  have h1 : gowersNormInterval 3 N
      (fun n => ((ArithmeticFunction.vonMangoldt n.toNat : ℝ) : ℂ) -
        heathBrownModel (Real.exp (Real.log N ^ ((1 : ℝ) / 10))) n) ≤
      |C₁| * (Real.log 2) ^ (-(max A 1)) * (k : ℝ) ^ (-A) := by
    refine (hC₁ N hN2).trans ?_
    rw [hlogN, Real.mul_rpow hk0.le hlog2'.le]
    have hpow : (k : ℝ) ^ (-(max A 1)) ≤ (k : ℝ) ^ (-A) :=
      Real.rpow_le_rpow_of_exponent_le hk1 (by linarith [le_max_left A 1])
    have hx : 0 ≤ (Real.log 2) ^ (-(max A 1)) := by positivity
    calc C₁ * ((k : ℝ) ^ (-(max A 1)) * (Real.log 2) ^ (-(max A 1)))
        ≤ |C₁| * ((k : ℝ) ^ (-A) * (Real.log 2) ^ (-(max A 1))) :=
          mul_le_mul (le_abs_self _) (mul_le_mul_of_nonneg_right hpow hx) (by positivity)
            (abs_nonneg _)
      _ = _ := by ring
  -- the second term
  set QN : ℝ := Real.exp (Real.log ((N : ℕ+) : ℝ) ^ ((1 : ℝ) / 10)) with hQN
  have hQN0 : 0 < QN := Real.exp_pos _
  have hterm : ∀ j ∈ (jSet k).filter (fun j => QN < (2 : ℝ) ^ j),
      gowersNormInterval 3 N (wQ (2 ^ j)) ≤ |Cp| * (QN ^ (-(1 / 8 : ℝ)) * q ^ j) := by
    intro j hj
    rw [Finset.mem_filter, mem_jSet_iff] at hj
    have h := hCp k N hN j hj.1
    have hw : gowersNormInterval 3 N (wQ (2 ^ j)) =
        gowersNormInterval 3 N (blockWeight (Finset.Ioc (2 ^ j / 2) (2 ^ j))) := rfl
    rw [hw]
    refine h.trans ?_
    have h2j : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
    have e1 : ((2 : ℝ) ^ j) ^ (-(3 : ℝ) / 8 + 1 / 8) =
        ((2 : ℝ) ^ j) ^ (-(1 / 8 : ℝ)) * ((2 : ℝ) ^ j) ^ (-(1 / 8 : ℝ)) := by
      rw [← Real.rpow_add h2j]; norm_num
    have e2 : ((2 : ℝ) ^ j) ^ (-(1 / 8 : ℝ)) = q ^ j := by
      rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num)]
      congr 1; ring
    have e3 : ((2 : ℝ) ^ j) ^ (-(1 / 8 : ℝ)) ≤ QN ^ (-(1 / 8 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hQN0 hj.2.le (by norm_num)
    rw [e1]
    calc Cp * (((2 : ℝ) ^ j) ^ (-(1 / 8 : ℝ)) * ((2 : ℝ) ^ j) ^ (-(1 / 8 : ℝ)))
        ≤ |Cp| * (((2 : ℝ) ^ j) ^ (-(1 / 8 : ℝ)) * ((2 : ℝ) ^ j) ^ (-(1 / 8 : ℝ))) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ |Cp| * (QN ^ (-(1 / 8 : ℝ)) * q ^ j) := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          rw [e2] at e3 ⊢
          exact mul_le_mul e3 le_rfl (by positivity) (by positivity)
  have hgeo : ∑ j ∈ (jSet k).filter (fun j => QN < (2 : ℝ) ^ j), q ^ j ≤ c8 := by
    refine ((summable_geometric_of_lt_one hq0.le hq1).sum_le_tsum _
      (fun j _ => by positivity)).trans ?_
    rw [tsum_geometric_of_lt_one hq0.le hq1]
  have hQexp : QN ^ (-(1 / 8 : ℝ)) = Real.exp (-((k * Real.log 2) ^ ((1 : ℝ) / 10)) / 8) := by
    rw [hQN, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, hlogN]
    congr 1; ring
  have h2 : ∑ j ∈ (jSet k).filter (fun j => QN < (2 : ℝ) ^ j),
      gowersNormInterval 3 N (wQ (2 ^ j)) ≤ |Cp| * c8 * Ce * (k : ℝ) ^ (-A) := by
    calc _ ≤ ∑ j ∈ (jSet k).filter (fun j => QN < (2 : ℝ) ^ j),
          |Cp| * (QN ^ (-(1 / 8 : ℝ)) * q ^ j) := Finset.sum_le_sum hterm
      _ = |Cp| * QN ^ (-(1 / 8 : ℝ)) *
          ∑ j ∈ (jSet k).filter (fun j => QN < (2 : ℝ) ^ j), q ^ j := by
          rw [← Finset.mul_sum, ← Finset.mul_sum]; ring
      _ ≤ |Cp| * QN ^ (-(1 / 8 : ℝ)) * c8 :=
          mul_le_mul_of_nonneg_left hgeo (by positivity)
      _ ≤ |Cp| * (Ce * (k : ℝ) ^ (-A)) * c8 := by
          rw [hQexp]
          gcongr
          exact hCe k hk
      _ = _ := by ring
  calc _ ≤ |C₁| * (Real.log 2) ^ (-(max A 1)) * (k : ℝ) ^ (-A) + |Cp| * c8 * Ce * (k : ℝ) ^ (-A) :=
        add_le_add h1 h2
    _ = _ := by ring

/-- **`e:minor-U3-var-red`** (L1283-L1287): `‖w - w_{≤ M(k)}‖_{U³([2^k])} ≲_A k^{-A}` for every
`A < ∞`. -/
theorem minor_U3_var_red (hF : FplusProp31) (A : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (N : ℕ+), 1 ≤ k → (N : ℕ) = 2 ^ k →
      gowersNormInterval 3 N (resWeight k) ≤ C * (k : ℝ) ^ (-A) :=
  cutoff_bridge hF A

end PrimeCarleson.Proof.Paper
