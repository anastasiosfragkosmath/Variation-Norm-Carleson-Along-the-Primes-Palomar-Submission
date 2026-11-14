module

public import PrimeCarleson.Proof.Paper.P10.Coef
public import PrimeCarleson.Proof.Paper.P9.ScaleN

/-!
# The statistics `A₁` and `B₁` for the coefficients `g_R`

Source: main paper `p:transferprop`, L2153–L2163; main paper `l:A1B1`, L2172–L2183 (the two bounds
at L2180 and L2181).

`gcoefR B ϑ R z = g_R(z) = b(R - ϑ(z)) e_N(R z)` for `R ∈ ℤ/N` (`Fin N`, `N = 𝒬_B`) and an
arbitrary selector `ϑ : ℤ → ℤ` (`θ(x) ∈ ℤ/N`). For a cutoff `φ_I` of scale `c` with `2 c N < 1`
(the cutoff data of the window, Source: main paper `p:transferprop`, L2164–L2170, from `P9/`):

* `norm_sum_gcoefR_le` (the bound for `A₁` of `l:A1B1`, first part):
  `|∑_R g_R(z) w_R| = |L_θ C(z)| ≤ M_B C(z)` for `C(s) = ∑_R w_R e_N(R s)`;
* `A1_bound` (`l:A1B1`, first display): `∑_y |φ_I(y) ∑_R w_R g_R(x + y)|² ≤ A₁² ∑_R |w_R|²` with
  `A₁² = 2 𝔪_B² / c` (so `A₁ ≈ N^{1/2} 𝔪_B` when `c ≈ 1/N`);
* `B1_bound` (`l:A1B1`, second display): `∑_y ∑_R |φ_I(y) g_R(x + y)|² ≤ (2/c) ∑_{q ∈ B} 1/φ(q)`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal ComplexConjugate

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Goal0 PrimeCarleson.Proof.Common

/-- **The coefficients `g_R`** (Source: main paper `p:transferprop`, L2153–L2163):
`g_R(z) = b(R - ϑ(z)) e_N(R z)`, `R ∈ ℤ/N` (`N = 𝒬_B`), for the selector `ϑ : ℤ → ℤ` (`θ(z) ∈ ℤ/N`).
-/
def gcoefR (B : Finset ℕ) (ϑ : ℤ → ℤ) (R : Fin (lcmQ B)) (z : ℤ) : ℂ :=
  bcoef B ((R : ℕ) - ϑ z) * e ((z : ℝ) * (R : ℕ) / (lcmQ B : ℝ))

/-! ### `L_θ C = ∑_R b(R - θ) c_R e_N(R ·)` -/

/-- `L_θ C(z) = N⁻¹ ∑_{r<N} C(z - r) w_{Q,B}(r) e_N(θ r) = ∑_R b(R - θ) c_R e_N(R z)` for
`C(s) = ∑_R c_R e_N(R s)` (L2193-L2197). -/
theorem avg_conv_eq {B : Finset ℕ} (hB : ∀ q ∈ B, 0 < q) (w : ℕ → ℂ) (θ₀ : ℕ) (z : ℤ) :
    ((lcmQ B : ℕ) : ℂ)⁻¹ * ∑ r ∈ Finset.range (lcmQ B),
        (∑ R ∈ Finset.range (lcmQ B), w R * e (((z - (r : ℤ) : ℤ) : ℝ) * R / (lcmQ B : ℝ))) *
          blockWeight B (r : ℤ) * e ((r : ℝ) * θ₀ / (lcmQ B : ℝ)) =
      ∑ R ∈ Finset.range (lcmQ B),
        w R * (bcoef B ((R : ℤ) - θ₀) * e ((z : ℝ) * R / (lcmQ B : ℝ))) := by
  have h1 : ∀ r ∈ Finset.range (lcmQ B),
      (∑ R ∈ Finset.range (lcmQ B), w R * e (((z - (r : ℤ) : ℤ) : ℝ) * R / (lcmQ B : ℝ))) *
          blockWeight B (r : ℤ) * e ((r : ℝ) * θ₀ / (lcmQ B : ℝ)) =
      ∑ R ∈ Finset.range (lcmQ B), (w R * e ((z : ℝ) * R / (lcmQ B : ℝ))) *
        (blockWeight B (r : ℤ) * e ((r : ℝ) * (((θ₀ : ℤ) - R : ℤ) : ℝ) / (lcmQ B : ℝ))) := by
    intro r _
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun R _ => ?_
    have : e (((z - (r : ℤ) : ℤ) : ℝ) * R / (lcmQ B : ℝ)) * e ((r : ℝ) * θ₀ / (lcmQ B : ℝ)) =
        e ((z : ℝ) * R / (lcmQ B : ℝ)) * e ((r : ℝ) * (((θ₀ : ℤ) - R : ℤ) : ℝ) / (lcmQ B : ℝ)) := by
      rw [← e_add, ← e_add]
      congr 1
      push_cast
      ring
    calc w R * e (((z - (r : ℤ) : ℤ) : ℝ) * R / (lcmQ B : ℝ)) * blockWeight B (r : ℤ) *
          e ((r : ℝ) * θ₀ / (lcmQ B : ℝ))
        = w R * blockWeight B (r : ℤ) *
            (e (((z - (r : ℤ) : ℤ) : ℝ) * R / (lcmQ B : ℝ)) * e ((r : ℝ) * θ₀ / (lcmQ B : ℝ))) := by
          ring
      _ = _ := by rw [this]; ring
  rw [Finset.sum_congr rfl h1, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun R _ => ?_
  have h2 := avg_blockWeight_mul_e hB ((θ₀ : ℤ) - R)
  rw [neg_sub] at h2
  rw [← Finset.mul_sum, ← h2]
  ring

/-- The extension of `w : Fin N → ℂ` by zero to `ℕ`. -/
def extFin {N : ℕ} (w : Fin N → ℂ) (n : ℕ) : ℂ := if h : n < N then w ⟨n, h⟩ else 0

theorem extFin_fin {N : ℕ} (w : Fin N → ℂ) (R : Fin N) : extFin w (R : ℕ) = w R := by
  simp [extFin, R.2]

/-- `C(s) = ∑_R w_R e_N(R s)` is `N`-periodic in `s`. -/
theorem cfun_periodic {N : ℕ} (hN : 0 < N) (w : Fin N → ℂ) :
    Function.Periodic
      (fun s : ℤ => ∑ R : Fin N, w R * e ((s : ℝ) * (R : ℕ) / (N : ℝ))) (N : ℤ) := by
  intro s
  refine Finset.sum_congr rfl fun R _ => ?_
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have : (((s + (N : ℤ) : ℤ) : ℝ) * (R : ℕ) / (N : ℝ)) =
      (s : ℝ) * (R : ℕ) / (N : ℝ) + (((R : ℕ) : ℤ) : ℝ) := by
    push_cast
    field_simp
  rw [this, e_add_intCast]

/-- **The bound for `A₁` of `l:A1B1`, pointwise part** (L2193–L2206):
`|∑_R g_R(z) w_R| = |L_{θ(z)} C(z)| ≤ M_B C(z)` for `C(s) = ∑_R w_R e_N(R s)`. -/
theorem norm_sum_gcoefR_le {B : Finset ℕ} (hB : ∀ q ∈ B, 0 < q) (ϑ : ℤ → ℤ)
    (w : Fin (lcmQ B) → ℂ) (z : ℤ) :
    ‖∑ R : Fin (lcmQ B), w R * gcoefR B ϑ R z‖ ≤
      periodicBlockMax B (fun s : ℤ =>
        ∑ R : Fin (lcmQ B), w R * e ((s : ℝ) * (R : ℕ) / (lcmQ B : ℝ))) z := by
  classical
  have hN : 0 < lcmQ B := lcmQ_pos hB
  have hN' : (0 : ℤ) < (lcmQ B : ℤ) := by exact_mod_cast hN
  set w' : ℕ → ℂ := extFin w with hw'
  set θ₀ : ℕ := (ϑ z % (lcmQ B : ℤ)).toNat with hθ₀def
  have hθ₀ : θ₀ < lcmQ B := by
    have h0 : 0 ≤ ϑ z % (lcmQ B : ℤ) := Int.emod_nonneg _ hN'.ne'
    have h1 : ϑ z % (lcmQ B : ℤ) < lcmQ B := Int.emod_lt_of_pos _ hN'
    omega
  have hper : ∀ R : ℕ, bcoef B ((R : ℤ) - ϑ z) = bcoef B ((R : ℤ) - θ₀) := by
    intro R
    have h0 : 0 ≤ ϑ z % (lcmQ B : ℤ) := Int.emod_nonneg _ hN'.ne'
    have : (R : ℤ) - ϑ z = ((R : ℤ) - θ₀) - (ϑ z / (lcmQ B : ℤ)) * (lcmQ B : ℤ) := by
      rw [hθ₀def, Int.toNat_of_nonneg h0, Int.emod_def]
      ring
    rw [this]
    exact (bcoef_periodic B).sub_int_mul_eq _
  have hC : ∀ s : ℤ, ∑ R : Fin (lcmQ B), w R * e ((s : ℝ) * (R : ℕ) / (lcmQ B : ℝ)) =
      ∑ R ∈ Finset.range (lcmQ B), w' R * e ((s : ℝ) * R / (lcmQ B : ℝ)) := by
    intro s
    have := Fin.sum_univ_eq_sum_range (fun R : ℕ => w' R * e ((s : ℝ) * R / (lcmQ B : ℝ)))
      (lcmQ B)
    rw [← this]
    exact Finset.sum_congr rfl fun R _ => by rw [hw', extFin_fin]
  have hL : ∑ R : Fin (lcmQ B), w R * gcoefR B ϑ R z =
      ∑ R ∈ Finset.range (lcmQ B),
        w' R * (bcoef B ((R : ℤ) - θ₀) * e ((z : ℝ) * R / (lcmQ B : ℝ))) := by
    have := Fin.sum_univ_eq_sum_range
      (fun R : ℕ => w' R * (bcoef B ((R : ℤ) - θ₀) * e ((z : ℝ) * R / (lcmQ B : ℝ)))) (lcmQ B)
    rw [← this]
    refine Finset.sum_congr rfl fun R _ => ?_
    rw [hw', extFin_fin, gcoefR, hper]
  have hmax : ‖((lcmQ B : ℕ) : ℂ)⁻¹ * ∑ r : Fin (lcmQ B),
      (∑ R : Fin (lcmQ B), w R * e (((z - ((r : ℕ) : ℤ) : ℤ) : ℝ) * (R : ℕ) / (lcmQ B : ℝ))) *
        blockWeight B ((r : ℕ) : ℤ) * e (((r : ℕ) : ℝ) * (θ₀ : ℝ) / (lcmQ B : ℝ))‖ ≤
      periodicBlockMax B (fun s : ℤ =>
        ∑ R : Fin (lcmQ B), w R * e ((s : ℝ) * (R : ℕ) / (lcmQ B : ℝ))) z :=
    norm_le_periodicBlockMax B (fun s : ℤ =>
        ∑ R : Fin (lcmQ B), w R * e ((s : ℝ) * (R : ℕ) / (lcmQ B : ℝ))) z ⟨θ₀, hθ₀⟩
  refine le_trans (le_of_eq ?_) hmax
  congr 1
  rw [hL, ← avg_conv_eq hB w' θ₀ z]
  have := Fin.sum_univ_eq_sum_range (fun r : ℕ =>
      (∑ R : Fin (lcmQ B), w R * e (((z - (r : ℤ) : ℤ) : ℝ) * (R : ℕ) / (lcmQ B : ℝ))) *
        blockWeight B (r : ℤ) * e ((r : ℝ) * θ₀ / (lcmQ B : ℝ))) (lcmQ B)
  rw [this]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [hC]

/-! ### Regrouping a periodic weight over residue classes -/

/-- If `∑_{y ≡ s (N)} a(y) ≤ L` for every residue `s`, then `∑_y a(y) F(y) ≤ L ∑_{s<N} F(s)` for
`N`-periodic `F` (the periodic-sum use of `sup_s ∑_{y = s mod N} φ_I(y)² ≲ 1`, L2202-L2204). -/
theorem tsum_mul_periodic_le {N : ℕ} (hN : 0 < N) (a F : ℤ → ℝ≥0∞)
    (hF : Function.Periodic F (N : ℤ)) {L : ℝ≥0∞}
    (ha : ∀ s : ℤ, ∑' y : ℤ, (if (N : ℤ) ∣ y - s then a y else 0) ≤ L) :
    ∑' y : ℤ, a y * F y ≤ L * ∑ s ∈ Finset.range N, F s := by
  have hN' : (0 : ℤ) < N := by exact_mod_cast hN
  have hFy : ∀ y : ℤ, F y = F ((y % (N : ℤ)).toNat) := by
    intro y
    have h0 : 0 ≤ y % (N : ℤ) := Int.emod_nonneg _ hN'.ne'
    have : y = (y % (N : ℤ)) + (y / (N : ℤ)) * (N : ℤ) := by
      rw [Int.emod_def]; ring
    have h2 := (hF.int_mul (y / (N : ℤ))) (y % (N : ℤ))
    simp only [Int.cast_id] at h2
    conv_lhs => rw [this]
    rw [h2, Int.toNat_of_nonneg h0]
  have h1 : ∀ y : ℤ, a y * F y =
      ∑ s ∈ Finset.range N, (if (N : ℤ) ∣ y - (s : ℤ) then a y else 0) * F s := by
    intro y
    have := sum_range_dvd hN y (fun s => a y * F s)
    rw [hFy y, ← this]
    refine Finset.sum_congr rfl fun s _ => ?_
    split_ifs <;> simp
  simp_rw [h1]
  rw [Summable.tsum_finsetSum (fun s _ => ENNReal.summable)]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun s _ => ?_
  rw [ENNReal.tsum_mul_right]
  exact mul_le_mul_left (ha s) _

/-- The residue-class sums of `‖φ_I(y)‖ₑ²` (`sum_phi_sq_residue_le` of `P9/ScaleN.lean`) in `ℝ≥0∞`.
-/
theorem tsum_residue_phi_le {θc a b c : ℝ} (D : CutoffData θc a b c) {N : ℕ} (hN : 0 < N)
    (hcN : 2 * c * N < 1) (s : ℤ) :
    ∑' y : ℤ, (if (N : ℤ) ∣ y - s then ‖D.φ y‖ₑ ^ 2 else 0) ≤ ENNReal.ofReal (2 / (N * c)) := by
  have hsum : Summable fun y : ℤ => (if (N : ℤ) ∣ y - s then ‖D.φ y‖ ^ 2 else 0) :=
    D.hasSum_norm_sq_phi.summable.of_nonneg_of_le
      (fun y => by split_ifs <;> positivity) (fun y => by split_ifs <;> simp)
  have h1 : ∀ y : ℤ, (if (N : ℤ) ∣ y - s then ‖D.φ y‖ₑ ^ 2 else 0) =
      ENNReal.ofReal (if (N : ℤ) ∣ y - s then ‖D.φ y‖ ^ 2 else 0) := by
    intro y
    split_ifs
    · rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    · simp
  simp_rw [h1]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun y => by split_ifs <;> positivity) hsum]
  exact ENNReal.ofReal_le_ofReal (D.sum_phi_sq_residue_le N hN hcN s)

/-- `∑_{s<N} M_B C(s)² ≤ 𝔪_B² ∑_{s<N} |C(s)|²` for `N`-periodic `C`. -/
theorem sum_sq_periodicBlockMax_le {B : Finset ℕ} (hB : ∀ q ∈ B, 0 < q) (C : ℤ → ℂ)
    (hC : Function.Periodic C (lcmQ B : ℤ)) :
    ∑ s ∈ Finset.range (lcmQ B), periodicBlockMax B C s ^ 2 ≤
      mB B ^ 2 * ∑ s ∈ Finset.range (lcmQ B), ‖C s‖ ^ 2 := by
  have h := l2_MB_le_mB_mul hB hC
  have h2 := pow_le_pow_left₀ (l2_nonneg _ _) h 2
  rw [l2_sq, mul_pow, l2_sq] at h2
  exact h2

/-- **`l:A1B1`, first display (`A₁ ≲ N^{1/2} 𝔪_B`)** (L2180, L2185-L2206): for a cutoff `φ_I` of
scale `c` with `2 c N < 1` (`N = 𝒬_B`), every selector `ϑ`, every `x` and every `w ∈ ℂ^{ℤ/N}`,
`∑_y |φ_I(y) ∑_R w_R g_R(x + y)|² ≤ A₁² ∑_R |w_R|²` for every `A₁² ≥ 2 𝔪_B²/c`. -/
theorem A1_bound {θc a b c : ℝ} (D : CutoffData θc a b c) {B : Finset ℕ} (hB : ∀ q ∈ B, 0 < q)
    (hcN : 2 * c * (lcmQ B : ℝ) < 1) (ϑ : ℤ → ℤ) {A₁ : ℝ} (hA₁ : 2 / c * mB B ^ 2 ≤ A₁ ^ 2)
    (x : ℤ) (w : Fin (lcmQ B) → ℂ) :
    ∑' y : ℤ, ‖D.φ y * ∑ R : Fin (lcmQ B), w R * gcoefR B ϑ R (x + y)‖ₑ ^ 2 ≤
      ENNReal.ofReal (A₁ ^ 2 * ∑ R, ‖w R‖ ^ 2) := by
  classical
  have hN : 0 < lcmQ B := lcmQ_pos hB
  have hNR : (0 : ℝ) < lcmQ B := by exact_mod_cast hN
  set Cf : ℤ → ℂ := fun s : ℤ => ∑ R : Fin (lcmQ B), w R * e ((s : ℝ) * (R : ℕ) / (lcmQ B : ℝ))
    with hCf
  set M : ℤ → ℝ := periodicBlockMax B Cf with hM
  have hCper : Function.Periodic Cf (lcmQ B : ℤ) := cfun_periodic hN w
  have hMper : Function.Periodic M (lcmQ B : ℤ) := MB_periodic B hCper
  have hpt : ∀ y : ℤ, ‖D.φ y * ∑ R : Fin (lcmQ B), w R * gcoefR B ϑ R (x + y)‖ₑ ^ 2 ≤
      ‖D.φ y‖ₑ ^ 2 * ENNReal.ofReal (M (x + y)) ^ 2 := by
    intro y
    rw [enorm_mul, mul_pow]
    refine mul_le_mul_right ?_ _
    refine pow_le_pow_left₀ zero_le ?_ 2
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (norm_sum_gcoefR_le hB ϑ w (x + y))
  have hFper : Function.Periodic (fun y : ℤ => ENNReal.ofReal (M (x + y)) ^ 2) (lcmQ B : ℤ) := by
    intro y
    simp only
    rw [← add_assoc, hMper (x + y)]
  refine (ENNReal.tsum_le_tsum hpt).trans ?_
  refine (tsum_mul_periodic_le hN (fun y => ‖D.φ y‖ₑ ^ 2) _ hFper
    (L := ENNReal.ofReal (2 / (lcmQ B * c)))
    (fun s => tsum_residue_phi_le D hN hcN s)).trans ?_
  have hsum1 : ∑ s ∈ Finset.range (lcmQ B), ENNReal.ofReal (M (x + (s : ℤ))) ^ 2 =
      ENNReal.ofReal (∑ s ∈ Finset.range (lcmQ B), M (s : ℤ) ^ 2) := by
    have hnn : ∀ s : ℤ, 0 ≤ M s := fun s => periodicBlockMax_nonneg B Cf s
    simp_rw [← ENNReal.ofReal_pow (hnn _)]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun s _ => by positivity)]
    congr 1
    have := sum_range_add_of_periodic (F := fun s : ℤ => M s ^ 2) (D := lcmQ B)
      (by intro s; simp only [hMper s]) x
    rw [← this]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [add_comm]
  rw [hsum1]
  have hpl : ∑ s ∈ Finset.range (lcmQ B), ‖Cf s‖ ^ 2 = lcmQ B * ∑ R : Fin (lcmQ B), ‖w R‖ ^ 2 := by
    have h := sum_norm_sq_cyclic hN (extFin w)
    have h1 : ∀ s : ℕ, Cf (s : ℤ) = ∑ l ∈ Finset.range (lcmQ B),
        extFin w l * e ((s : ℝ) * l / (lcmQ B : ℝ)) := by
      intro s
      simp only [hCf, Int.cast_natCast]
      rw [← Fin.sum_univ_eq_sum_range (fun l : ℕ => extFin w l * e ((s : ℝ) * l / (lcmQ B : ℝ)))]
      exact Finset.sum_congr rfl fun R _ => by rw [extFin_fin]
    simp_rw [h1] at *
    rw [h, ← Fin.sum_univ_eq_sum_range (fun l : ℕ => ‖extFin w l‖ ^ 2)]
    simp_rw [extFin_fin]
  have hbound : ∑ s ∈ Finset.range (lcmQ B), M (s : ℤ) ^ 2 ≤
      mB B ^ 2 * (lcmQ B * ∑ R : Fin (lcmQ B), ‖w R‖ ^ 2) := by
    rw [← hpl]
    exact sum_sq_periodicBlockMax_le hB Cf hCper
  refine (mul_le_mul_right (ENNReal.ofReal_le_ofReal hbound) _).trans ?_
  rw [← ENNReal.ofReal_mul (div_nonneg (by norm_num) (mul_nonneg (Nat.cast_nonneg _) D.c_pos.le))]
  refine ENNReal.ofReal_le_ofReal ?_
  have hW : 0 ≤ ∑ R : Fin (lcmQ B), ‖w R‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  calc 2 / ((lcmQ B : ℝ) * c) * (mB B ^ 2 * ((lcmQ B : ℝ) * ∑ R : Fin (lcmQ B), ‖w R‖ ^ 2))
      = (2 / c * mB B ^ 2) * ∑ R : Fin (lcmQ B), ‖w R‖ ^ 2 := by
        have hc : c ≠ 0 := D.c_pos.ne'
        field_simp
    _ ≤ A₁ ^ 2 * ∑ R : Fin (lcmQ B), ‖w R‖ ^ 2 := mul_le_mul_of_nonneg_right hA₁ hW

/-- **`l:A1B1`, second display (`B₁`)** (L2181, L2208-L2212): for `B₁² ≥ (2/c) ∑_{q ∈ B} 1/φ(q)`,
`∑_y ∑_R |φ_I(y) g_R(x + y)|² ≤ B₁²`. -/
theorem B1_bound {θc a b c : ℝ} (D : CutoffData θc a b c) {B : Finset ℕ} (hB : ∀ q ∈ B, 0 < q)
    (ϑ : ℤ → ℤ) {B₁ : ℝ} (hB₁ : 2 / c * ∑ q ∈ B, ((Nat.totient q : ℝ))⁻¹ ≤ B₁ ^ 2) (x : ℤ) :
    ∑' y : ℤ, ∑ R : Fin (lcmQ B), ‖D.φ y * gcoefR B ϑ R (x + y)‖ₑ ^ 2 ≤
      ENNReal.ofReal (B₁ ^ 2) := by
  classical
  have hN : 0 < lcmQ B := lcmQ_pos hB
  set Φ : ℝ := ∑ q ∈ B, ((Nat.totient q : ℝ))⁻¹ with hΦ
  have hΦ0 : 0 ≤ Φ := Finset.sum_nonneg fun q _ => inv_nonneg.2 (Nat.cast_nonneg _)
  have hnorm : ∀ t : ℤ, ∑ R : Fin (lcmQ B), ‖bcoef B ((R : ℕ) - t)‖ ^ 2 ≤ Φ := by
    intro t
    rw [Fin.sum_univ_eq_sum_range (fun R : ℕ => ‖bcoef B ((R : ℤ) - t)‖ ^ 2) (lcmQ B)]
    have := sum_range_add_of_periodic (F := fun l : ℤ => ‖bcoef B l‖ ^ 2) (D := lcmQ B)
      (by intro s; simp only [bcoef_periodic B s]) (-t)
    simp only [← sub_eq_add_neg] at this
    rw [this]
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun l hl => ?_)) (sum_norm_sq_bnat_le hB)
    rw [bcoef_natCast B (Finset.mem_range.1 hl)]
  have hpt : ∀ y : ℤ, ∑ R : Fin (lcmQ B), ‖D.φ y * gcoefR B ϑ R (x + y)‖ₑ ^ 2 ≤
      ‖D.φ y‖ₑ ^ 2 * ENNReal.ofReal Φ := by
    intro y
    have he : ∀ t : ℝ, ‖e t‖ₑ = 1 := fun t => by rw [← ofReal_norm, norm_e]; simp
    have h1 : ∀ R : Fin (lcmQ B), ‖D.φ y * gcoefR B ϑ R (x + y)‖ₑ ^ 2 =
        ‖D.φ y‖ₑ ^ 2 * ENNReal.ofReal (‖bcoef B ((R : ℕ) - ϑ (x + y))‖ ^ 2) := by
      intro R
      simp only [gcoefR, enorm_mul, he, mul_one, mul_pow]
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    simp_rw [h1]
    rw [← Finset.mul_sum, ← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
    exact mul_le_mul_right (ENNReal.ofReal_le_ofReal (hnorm _)) _
  refine (ENNReal.tsum_le_tsum hpt).trans ?_
  rw [ENNReal.tsum_mul_right]
  have h2 : ∑' y : ℤ, ‖D.φ y‖ₑ ^ 2 = ENNReal.ofReal (∑' y : ℤ, ‖D.φ y‖ ^ 2) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (fun y => by positivity) D.hasSum_norm_sq_phi.summable]
    refine tsum_congr fun y => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rw [h2, ← ENNReal.ofReal_mul (tsum_nonneg fun y => by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  calc (∑' y : ℤ, ‖D.φ y‖ ^ 2) * Φ ≤ (2 / c) * Φ :=
        mul_le_mul_of_nonneg_right D.sum_norm_sq_phi_le hΦ0
    _ ≤ B₁ ^ 2 := hB₁

end PrimeCarleson.Proof.Paper
