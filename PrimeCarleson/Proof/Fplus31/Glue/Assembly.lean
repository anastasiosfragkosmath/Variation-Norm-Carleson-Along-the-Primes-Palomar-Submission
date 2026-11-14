module

public import PrimeCarleson.Proof.Fplus31.Comparison.Main
public import PrimeCarleson.Proof.Paper.P2.NormProperties

/-!
# The conditional final assembly of `[F+]` Proposition 3.1

Source: [F+] `p:logsavings`, L1056–L1062 (the `PrimeCarleson.vonMangoldt_sub_heathBrown_U3`,
`‖Λ - Λ_{≤ Q_N}‖_{U³[N]} ≤ C_A (log N)^{-A}`).

The two halves of the proof are:
* **The comparison of the Cramér model with the Heath-Brown model** (`Comparison/Main.lean`,
  `cramer_heathBrown_U3`): the Cramér model `Λ_{C,w}` (`cramerModel (cramerLevel N)`) is close to
  the Heath-Brown model, `‖Λ_{C,w} - Λ_{≤T}‖_{U³[N]} ≤ C exp(-c (log N)^{1/10})`;
* **The comparison of `Λ` with the Cramér model** (Leng23 `t:mobiusuniformity`, with `s = 2` and
  without Siegel zeros): `‖Λ - Λ_{C,w}‖_{U³[N]} ≤ C exp(-(log N)^c)` in that form. The iteration
  of `C2/`, with the Vaughan decomposition of `TypeIII/` and the prime number theorem in
  progressions of `PNTSW/`, proves the weaker form `CMainBoundPoly` (`C2/CMain.lean`), which is the
  one the statement uses.

This file is the glue. The Prop `CMainBound` states this comparison, in the form of Leng23's theorem
(arXiv:2312.10772v5 TeX L1069-L1073: `≪ exp(-log(N)^{c_s})`, proved in
L1185 ff. by "optimising in `δ`" with `δ ≥ exp(-log(N)^{c_k})`). The weaker `CMainBoundPoly` is the
same statement with `(log N)^{-A}` for every fixed `A ≥ 1` (what an iteration run with the threshold
`δ = (log N)^{-A}` delivers). The conclusion from `CMainBoundPoly` is proved here:

* `exists_exp_neg_mul_rpow_le`: a stretched exponential beats every power of `log N`
  (`exp(-κ L^c) ≤ K L^{-A}` for all `L > 0`), the only analysis of the glue;
* `vonMangoldt_sub_heathBrown_U3_of_cmainPoly`: the statement, verbatim. Proof: the
  triangle inequality for `‖·‖_{U³[N]}` (`Paper.gowersNormInterval_three_norm_properties`) with the
  comparison with the Heath-Brown model, and the exponential beats the power; small `N` costs
  nothing, since the bound for the stretched exponential holds for every `L = log N > 0`, so the
  constant `C_A` absorbs them.
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

open PrimeCarleson

/-! ### A stretched exponential beats every power -/

/-- `u^a ≤ a^a e^u` for `a > 0` and `u ≥ 0`. -/
theorem rpow_le_rpow_self_mul_exp {a : ℝ} (ha : 0 < a) {u : ℝ} (hu : 0 ≤ u) :
    u ^ a ≤ a ^ a * Real.exp u := by
  have h1 : u / a ≤ Real.exp (u / a - 1) := by linarith [Real.add_one_le_exp (u / a - 1)]
  have h2 : (u / a) ^ a ≤ Real.exp (u / a - 1) ^ a :=
    Real.rpow_le_rpow (by positivity) h1 ha.le
  rw [← Real.exp_mul, Real.div_rpow hu ha.le] at h2
  have h3 : Real.exp ((u / a - 1) * a) ≤ Real.exp u := by
    refine Real.exp_le_exp.2 ?_
    have : (u / a - 1) * a = u - a := by field_simp
    linarith
  have hpos : 0 < a ^ a := Real.rpow_pos_of_pos ha a
  rw [div_le_iff₀ hpos] at h2
  calc u ^ a ≤ Real.exp ((u / a - 1) * a) * a ^ a := h2
    _ ≤ Real.exp u * a ^ a := mul_le_mul_of_nonneg_right h3 hpos.le
    _ = a ^ a * Real.exp u := mul_comm _ _

/-- **A stretched exponential beats every power**: for `κ, c, A > 0` there is `K ≥ 0` with
`exp(-κ L^c) ≤ K L^{-A}` for every `L > 0` (so no lower bound on `L = log N` is needed). -/
theorem exists_exp_neg_mul_rpow_le {κ c A : ℝ} (hκ : 0 < κ) (hc : 0 < c) (hA : 0 < A) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ L : ℝ, 0 < L → Real.exp (-(κ * L ^ c)) ≤ K * L ^ (-A) := by
  set a : ℝ := A / c with ha
  have ha0 : 0 < a := div_pos hA hc
  refine ⟨a ^ a / κ ^ a, by positivity, fun L hL => ?_⟩
  have hLc : 0 < L ^ c := Real.rpow_pos_of_pos hL c
  have hLA : 0 < L ^ A := Real.rpow_pos_of_pos hL A
  have hu : 0 ≤ κ * L ^ c := by positivity
  have h1 := rpow_le_rpow_self_mul_exp ha0 hu
  have h2 : (κ * L ^ c) ^ a = κ ^ a * L ^ A := by
    rw [Real.mul_rpow hκ.le hLc.le, ← Real.rpow_mul hL.le, ha, mul_div_cancel₀ _ hc.ne']
  rw [h2] at h1
  have hκa : 0 < κ ^ a := Real.rpow_pos_of_pos hκ a
  have h3 : L ^ A ≤ a ^ a / κ ^ a * Real.exp (κ * L ^ c) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hκa]
    linarith
  rw [Real.rpow_neg hL.le, Real.exp_neg, ← div_eq_mul_inv, inv_eq_one_div,
    div_le_div_iff₀ (Real.exp_pos _) hLA, one_mul]
  exact h3

/-! ### The two forms of the comparison with the Cramér model -/

/-- **The comparison with the Cramér model** (Leng23 `t:mobiusuniformity` for `s = 2`, in the proof
of `[F+]` Proposition 3.1): with `Λ_{C,w}` the Cramér model of level `w = cramerLevel N`, there are
`c > 0` and `C` with `‖Λ - Λ_{C,w}‖_{U³[N]} ≤ C exp(-(log N)^c)` for all `N ≥ 2`. Not proved here:
it is the output of the iteration of `C2/`, the Vaughan decomposition of `TypeIII/` and the prime
number theorem in progressions of `PNTSW/`. -/
def CMainBound : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∃ C : ℝ, ∀ N : ℕ+, 2 ≤ N →
    gowersNormInterval 3 N
        (fun n => ((ArithmeticFunction.vonMangoldt n.toNat : ℝ) : ℂ) -
          ((cramerModel (cramerLevel N) n : ℝ) : ℂ)) ≤
      C * Real.exp (-(Real.log N ^ c))

/-- **The comparison with the Cramér model, polylog form**: for every `A ≥ 1` there is `C_A` with
`‖Λ - Λ_{C,w}‖_{U³[N]} ≤ C_A (log N)^{-A}` for all `N ≥ 2`. -/
def CMainBoundPoly : Prop :=
  ∀ A : ℝ, 1 ≤ A → ∃ C : ℝ, ∀ N : ℕ+, 2 ≤ N →
    gowersNormInterval 3 N
        (fun n => ((ArithmeticFunction.vonMangoldt n.toNat : ℝ) : ℂ) -
          ((cramerModel (cramerLevel N) n : ℝ) : ℂ)) ≤
      C * Real.log N ^ (-A)

/-- For `N ≥ 2`, `log N > 0`. -/
theorem log_pos_of_two_le {N : ℕ+} (hN : 2 ≤ N) : 0 < Real.log N := by
  apply Real.log_pos
  have : (2 : ℕ) ≤ (N : ℕ) := by exact_mod_cast hN
  exact_mod_cast (by omega : 1 < (N : ℕ))

/-! ### The statement -/

/-- **The statement from the comparison with the Cramér model, polylog form.**
`‖Λ - Λ_{C,w}‖_{U³[N]} ≤ C_A (log N)^{-A}` with the comparison
`‖Λ_{C,w} - Λ_{≤T}‖_{U³[N]} ≤ C exp(-c (log N)^{1/10})` (the `heathBrownModel` with
`T = exp((log N)^{1/10})`) and the triangle inequality for `‖·‖_{U³[N]}` give the statement of
`PrimeCarleson.vonMangoldt_sub_heathBrown_U3`. -/
theorem vonMangoldt_sub_heathBrown_U3_of_cmainPoly (h : CMainBoundPoly) :
    ∀ A : ℝ, 1 ≤ A → ∃ C : ℝ, ∀ N : ℕ+, 2 ≤ N →
      gowersNormInterval 3 N
          (fun n => ((ArithmeticFunction.vonMangoldt n.toNat : ℝ) : ℂ) -
            heathBrownModel (Real.exp (Real.log N ^ ((1 : ℝ) / 10))) n) ≤
        C * Real.log N ^ (-A) := by
  intro A hA
  obtain ⟨C₁, h₁⟩ := h A hA
  obtain ⟨c, hc, C₂, h₂⟩ := cramer_heathBrown_U3
  obtain ⟨K, hK0, hK⟩ := exists_exp_neg_mul_rpow_le (κ := c) (c := (1 : ℝ) / 10) hc
    (by norm_num) (by linarith : 0 < A)
  refine ⟨C₁ + max C₂ 0 * K, fun N hN => ?_⟩
  obtain ⟨hadd, -, -⟩ := Paper.gowersNormInterval_three_norm_properties N
  have hL := log_pos_of_two_le hN
  have hfun : (fun n : ℤ => ((ArithmeticFunction.vonMangoldt n.toNat : ℝ) : ℂ) -
        heathBrownModel (Real.exp (Real.log N ^ ((1 : ℝ) / 10))) n) =
      (fun n : ℤ => ((ArithmeticFunction.vonMangoldt n.toNat : ℝ) : ℂ) -
          ((cramerModel (cramerLevel N) n : ℝ) : ℂ)) +
        (fun n : ℤ => ((cramerModel (cramerLevel N) n : ℝ) : ℂ) -
          heathBrownModel (Real.exp (Real.log N ^ ((1 : ℝ) / 10))) n) := by
    funext n
    exact (sub_add_sub_cancel _ _ _).symm
  have h3 := h₁ N hN
  have h4 := h₂ N hN
  have h5 := hK (Real.log N) hL
  rw [neg_mul] at h4
  rw [hfun]
  calc _ ≤ _ := hadd _ _
    _ ≤ C₁ * Real.log N ^ (-A) + C₂ * Real.exp (-(c * Real.log N ^ ((1 : ℝ) / 10))) :=
        add_le_add h3 h4
    _ ≤ C₁ * Real.log N ^ (-A) + max C₂ 0 * (K * Real.log N ^ (-A)) := by
        refine add_le_add le_rfl ?_
        calc C₂ * Real.exp (-(c * Real.log N ^ ((1 : ℝ) / 10)))
            ≤ max C₂ 0 * Real.exp (-(c * Real.log N ^ ((1 : ℝ) / 10))) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
          _ ≤ max C₂ 0 * (K * Real.log N ^ (-A)) :=
              mul_le_mul_of_nonneg_left h5 (le_max_right _ _)
    _ = (C₁ + max C₂ 0 * K) * Real.log N ^ (-A) := by ring

end PrimeCarleson.Proof.Fplus31
