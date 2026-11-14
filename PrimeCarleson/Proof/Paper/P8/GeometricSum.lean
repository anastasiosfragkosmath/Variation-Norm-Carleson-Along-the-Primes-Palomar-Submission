module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Lemma G: the sum over levels of the minimum of a growing and a decaying geometric term

Part of the chaining proof of main paper `l:entest` (L1824–L1860): the summation over the levels.

For `a, b > 0` and `A, B ≥ 0`, with `θ = a / (a + b)`,

  `∑_{v=1}^V min {A 2^{v a}, B 2^{-v b}} ≤ A^{1-θ} B^θ [(1 - 2^{-a})^{-1} + (1 - 2^{-b})^{-1}]`

for every `V` (`sum_min_geometric_le`), and `(1 - 2^{-x})^{-1} ≤ 1 + 1/(x log 2)` for `x > 0`
(`inv_one_sub_two_rpow_neg_le`).

The proof splits the levels at `x* = log₂(B/A)/(a+b)`: with `M = A 2^{x* a} = B 2^{-x* b}`, for
`v ≤ x*` the term is at most `M 2^{-(x*-v)a}` and for `v > x*` at most `M 2^{-(v-x*)b}`; in each
range the exponents are distinct integers apart from a fixed shift, so the sum is dominated by a
geometric series.
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

/-- A sum of `ρ^{i(v)}` over a finite set on which `i` is injective is at most `(1 - ρ)⁻¹`. -/
theorem sum_geom_le_of_injOn {ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ < 1) (S : Finset ℕ) (i : ℕ → ℕ)
    (hi : Set.InjOn i S) : ∑ v ∈ S, ρ ^ i v ≤ (1 - ρ)⁻¹ := by
  classical
  rw [← Finset.sum_image (f := fun k => ρ ^ k) hi]
  exact sum_le_hasSum _ (fun k _ => by positivity) (hasSum_geometric_of_lt_one h0.le h1)

/-- `2^{-x} < 1` for `x > 0`. -/
theorem two_rpow_neg_lt_one {x : ℝ} (hx : 0 < x) : (2 : ℝ) ^ (-x) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)

/-- `(1 - 2^{-x})⁻¹ ≤ 1 + 1/(x log 2)` for `x > 0`. -/
theorem inv_one_sub_two_rpow_neg_le {x : ℝ} (hx : 0 < x) :
    (1 - (2 : ℝ) ^ (-x))⁻¹ ≤ 1 + 1 / (x * Real.log 2) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set u : ℝ := x * Real.log 2 with hu
  have hu0 : 0 < u := mul_pos hx hlog
  have h2 : (2 : ℝ) ^ (-x) = Real.exp (-u) := by
    rw [Real.rpow_def_of_pos (by norm_num), hu]; congr 1; ring
  rw [h2]
  have h3 : 1 + u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
  have h4 : Real.exp (-u) ≤ (1 + u)⁻¹ := by
    rw [Real.exp_neg]
    exact inv_anti₀ (by linarith) h3
  have h5 : u / (1 + u) ≤ 1 - Real.exp (-u) := by
    have : 1 - (1 + u)⁻¹ = u / (1 + u) := by field_simp; ring
    linarith
  have h6 : 0 < u / (1 + u) := by positivity
  calc (1 - Real.exp (-u))⁻¹ ≤ (u / (1 + u))⁻¹ := inv_anti₀ h6 h5
    _ = 1 + 1 / u := by field_simp; ring

/-- **Lemma G.** For `a, b > 0`, `A, B ≥ 0` and every `V`, with `θ = a/(a+b)`,
`∑_{v=1}^V min {A 2^{v a}, B 2^{-v b}} ≤ A^{1-θ} B^θ [(1 - 2^{-a})⁻¹ + (1 - 2^{-b})⁻¹]`. -/
theorem sum_min_geometric_le {a b A B : ℝ} (ha : 0 < a) (hb : 0 < b) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (V : ℕ) :
    ∑ v ∈ Finset.Icc 1 V, min (A * (2 : ℝ) ^ ((v : ℝ) * a)) (B * (2 : ℝ) ^ (-((v : ℝ) * b))) ≤
      A ^ (1 - a / (a + b)) * B ^ (a / (a + b)) *
        ((1 - (2 : ℝ) ^ (-a))⁻¹ + (1 - (2 : ℝ) ^ (-b))⁻¹) := by
  have hab : 0 < a + b := by linarith
  have hθ0 : 0 < a / (a + b) := by positivity
  have hθ1 : 0 < 1 - a / (a + b) := by
    rw [sub_pos, div_lt_one hab]; linarith
  have hρa : (2 : ℝ) ^ (-a) < 1 := two_rpow_neg_lt_one ha
  have hρb : (2 : ℝ) ^ (-b) < 1 := two_rpow_neg_lt_one hb
  have hρa0 : (0 : ℝ) < 2 ^ (-a) := Real.rpow_pos_of_pos (by norm_num) _
  have hρb0 : (0 : ℝ) < 2 ^ (-b) := Real.rpow_pos_of_pos (by norm_num) _
  have hinva : 0 < (1 - (2 : ℝ) ^ (-a))⁻¹ := inv_pos.2 (by linarith)
  have hinvb : 0 < (1 - (2 : ℝ) ^ (-b))⁻¹ := inv_pos.2 (by linarith)
  rcases hA.eq_or_lt with hA0 | hApos
  · subst hA0
    have : ∀ v ∈ Finset.Icc 1 V, min (0 * (2 : ℝ) ^ ((v : ℝ) * a))
        (B * (2 : ℝ) ^ (-((v : ℝ) * b))) ≤ 0 := fun v _ => by simp
    refine (Finset.sum_nonpos this).trans ?_
    positivity
  rcases hB.eq_or_lt with hB0 | hBpos
  · subst hB0
    have : ∀ v ∈ Finset.Icc 1 V, min (A * (2 : ℝ) ^ ((v : ℝ) * a))
        (0 * (2 : ℝ) ^ (-((v : ℝ) * b))) ≤ 0 := fun v _ => by simp
    refine (Finset.sum_nonpos this).trans ?_
    positivity
  -- the case `A > 0`, `B > 0`
  set x : ℝ := Real.logb 2 (B / A) / (a + b) with hx
  set M : ℝ := A * (2 : ℝ) ^ (x * a) with hM
  have hM0 : 0 < M := by positivity
  have hx2 : (2 : ℝ) ^ (x * (a + b)) = B / A := by
    rw [hx, div_mul_cancel₀ _ hab.ne']
    exact Real.rpow_logb (by norm_num) (by norm_num) (div_pos hBpos hApos)
  have hMeq : M = A ^ (1 - a / (a + b)) * B ^ (a / (a + b)) := by
    have hBA : B = A * (2 : ℝ) ^ (x * (a + b)) := by rw [hx2]; field_simp
    have h1 : B ^ (a / (a + b)) = A ^ (a / (a + b)) * (2 : ℝ) ^ (x * a) := by
      conv_lhs => rw [hBA]
      rw [Real.mul_rpow hApos.le (by positivity), ← Real.rpow_mul (by norm_num)]
      congr 2
      field_simp
    rw [h1, ← mul_assoc, ← Real.rpow_add hApos]
    simp [hM]
  have hterm1 : ∀ v : ℕ, A * (2 : ℝ) ^ ((v : ℝ) * a) = M * (2 : ℝ) ^ (((v : ℝ) - x) * a) := by
    intro v
    rw [hM, mul_assoc, ← Real.rpow_add (by norm_num)]
    congr 2
    ring
  have hterm2 : ∀ v : ℕ,
      B * (2 : ℝ) ^ (-((v : ℝ) * b)) = M * (2 : ℝ) ^ (-(((v : ℝ) - x) * b)) := by
    intro v
    have hBA : B = A * (2 : ℝ) ^ (x * (a + b)) := by rw [hx2]; field_simp
    rw [hM, mul_assoc, ← Real.rpow_add (by norm_num), hBA, mul_assoc,
      ← Real.rpow_add (by norm_num)]
    congr 2
    ring
  set n : ℕ := ⌊x⌋₊ with hn
  rw [← hMeq]
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 V) (fun v : ℕ => (v : ℝ) ≤ x)
    (fun v => min (A * (2 : ℝ) ^ ((v : ℝ) * a)) (B * (2 : ℝ) ^ (-((v : ℝ) * b))))
  rw [← hsplit]
  rw [mul_add]
  refine add_le_add ?_ ?_
  · -- levels `v ≤ x`
    calc ∑ v ∈ (Finset.Icc 1 V).filter (fun v : ℕ => (v : ℝ) ≤ x),
          min (A * (2 : ℝ) ^ ((v : ℝ) * a)) (B * (2 : ℝ) ^ (-((v : ℝ) * b)))
        ≤ ∑ v ∈ (Finset.Icc 1 V).filter (fun v : ℕ => (v : ℝ) ≤ x),
            M * ((2 : ℝ) ^ (-a)) ^ (n - v) := by
          refine Finset.sum_le_sum fun v hv => ?_
          have hvx : (v : ℝ) ≤ x := (Finset.mem_filter.1 hv).2
          have hvn : v ≤ n := Nat.le_floor hvx
          refine (min_le_left _ _).trans ?_
          rw [hterm1]
          refine mul_le_mul_of_nonneg_left ?_ hM0.le
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
          refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
          have hnx : (n : ℝ) ≤ x := Nat.floor_le (le_trans (Nat.cast_nonneg v) hvx)
          rw [Nat.cast_sub hvn]
          nlinarith
      _ = M * ∑ v ∈ (Finset.Icc 1 V).filter (fun v : ℕ => (v : ℝ) ≤ x),
            ((2 : ℝ) ^ (-a)) ^ (n - v) := by rw [Finset.mul_sum]
      _ ≤ M * (1 - (2 : ℝ) ^ (-a))⁻¹ := by
          refine mul_le_mul_of_nonneg_left (sum_geom_le_of_injOn hρa0 hρa _ (fun v => n - v) ?_)
            hM0.le
          intro v hv w hw hvw
          have hv' : v ≤ n := Nat.le_floor (Finset.mem_filter.1 hv).2
          have hw' : w ≤ n := Nat.le_floor (Finset.mem_filter.1 hw).2
          simp only at hvw
          omega
  · -- levels `v > x`
    calc ∑ v ∈ (Finset.Icc 1 V).filter (fun v : ℕ => ¬ (v : ℝ) ≤ x),
          min (A * (2 : ℝ) ^ ((v : ℝ) * a)) (B * (2 : ℝ) ^ (-((v : ℝ) * b)))
        ≤ ∑ v ∈ (Finset.Icc 1 V).filter (fun v : ℕ => ¬ (v : ℝ) ≤ x),
            M * ((2 : ℝ) ^ (-b)) ^ (v - (n + 1)) := by
          refine Finset.sum_le_sum fun v hv => ?_
          obtain ⟨hvI, hvx⟩ := Finset.mem_filter.1 hv
          have hxv : x < v := not_le.1 hvx
          have hv1 : 1 ≤ v := (Finset.mem_Icc.1 hvI).1
          have hvn : n + 1 ≤ v := by
            have : n < v := (Nat.floor_lt' (by omega)).2 hxv
            omega
          refine (min_le_right _ _).trans ?_
          rw [hterm2]
          refine mul_le_mul_of_nonneg_left ?_ hM0.le
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
          refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
          have hxn : x < (n : ℝ) + 1 := Nat.lt_floor_add_one x
          rw [Nat.cast_sub hvn]
          push_cast
          nlinarith
      _ = M * ∑ v ∈ (Finset.Icc 1 V).filter (fun v : ℕ => ¬ (v : ℝ) ≤ x),
            ((2 : ℝ) ^ (-b)) ^ (v - (n + 1)) := by rw [Finset.mul_sum]
      _ ≤ M * (1 - (2 : ℝ) ^ (-b))⁻¹ := by
          refine mul_le_mul_of_nonneg_left (sum_geom_le_of_injOn hρb0 hρb _ (fun v => v - (n + 1))
            ?_) hM0.le
          intro v hv w hw hvw
          have hv' : n + 1 ≤ v := by
            obtain ⟨hvI, hvx⟩ := Finset.mem_filter.1 hv
            have : n < v := (Nat.floor_lt' (by have := (Finset.mem_Icc.1 hvI).1; omega)).2
              (not_le.1 hvx)
            omega
          have hw' : n + 1 ≤ w := by
            obtain ⟨hwI, hwx⟩ := Finset.mem_filter.1 hw
            have : n < w := (Nat.floor_lt' (by have := (Finset.mem_Icc.1 hwI).1; omega)).2
              (not_le.1 hwx)
            omega
          simp only at hvw
          omega

end PrimeCarleson.Proof.Paper
