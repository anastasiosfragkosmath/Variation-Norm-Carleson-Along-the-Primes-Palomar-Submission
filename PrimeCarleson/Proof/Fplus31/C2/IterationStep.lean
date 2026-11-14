module

public import PrimeCarleson.Proof.Fplus31.C2.IterationPigeon
public import PrimeCarleson.Proof.Fplus31.C2.IterationTranslate

/-!
# The iteration, from a sub-step to the next progression

Part of the type I / type II iteration of `C2/CMain.lean` (proof of [F+] Proposition 3.1).
`APInv N p q r lo hi` are the invariants of the progression of a stage; `exists_next_ap` is the
numerical form of the pigeonhole of `IterationPigeon.lean`: from the cell approximations of the
sub-step (a period `P ≤ e^b` and a test for every base point of the window of radius `A ≥ N e^{-b}`,
for every shift `z` of the window) and a correlation `N e^{-p} ≤ ‖∑_P F · star e‖`, a new
progression inside `P`, with modulus `≤ e^{3p + 3b + 4}`, and a test correlating with it at the
level `N e^{-(3p + 3b + 4)}`. The block length is `B = q M T` with `M = ⌈e^b⌉`, and the cell error
is `ε = e^{-p} / 4`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

open Finset
open scoped BigOperators

/-- The invariants of the progression of a stage: modulus in `[1, e^p]`, inside `[1, N]`. -/
structure APInv (N : ℕ) (p : ℝ) (q : ℕ) (r lo hi : ℤ) : Prop where
  one_le_q : 1 ≤ q
  q_le : (q : ℝ) ≤ Real.exp p
  one_le_lo : 1 ≤ lo
  hi_le : hi ≤ N

/-- `APInv` is monotone in the level `p`. -/
theorem APInv.mono {N : ℕ} {p p' : ℝ} {q : ℕ} {r lo hi : ℤ} (h : APInv N p q r lo hi)
    (hp : p ≤ p') : APInv N p' q r lo hi :=
  ⟨h.one_le_q, h.q_le.trans (Real.exp_le_exp.mpr hp), h.one_le_lo, h.hi_le⟩

/-- **The block parameters**: for `M = ⌈e^b⌉` and `q ≤ e^p`, `N e^{-(2p + 3b)} ≥ 16`, the block
multiplicity `T = ⌊N e^{-p} e^{-2b} / (4 q M)⌋` satisfies `T ≥ N e^{-(2p+3b)} / 16 ≥ 1` and
`q M T ≤ N e^{-p} e^{-2b} / 4`, and `M ≤ 2 e^b`. -/
theorem block_params {N q : ℕ} {p b : ℝ} (hp : 0 ≤ p) (hb : 0 ≤ b) (hq : 1 ≤ q)
    (hqp : (q : ℝ) ≤ Real.exp p) (hreg : 16 ≤ (N : ℝ) * Real.exp (-(2 * p + 3 * b))) :
    ∃ M T : ℕ, 0 < M ∧ 0 < T ∧ (M : ℝ) ≤ 2 * Real.exp b ∧ Real.exp b ≤ M ∧
      (N : ℝ) * Real.exp (-(2 * p + 3 * b)) / 16 ≤ T ∧
      (q : ℝ) * M * T ≤ N * (Real.exp (-p) * Real.exp (-(2 * b))) / 4 := by
  have hE1 : Real.exp (-(2 * p + 3 * b)) = (Real.exp p)⁻¹ ^ 2 * (Real.exp b)⁻¹ ^ 3 := by
    rw [Real.exp_neg, show 2 * p + 3 * b = p + p + (b + b + b) by ring, Real.exp_add,
      Real.exp_add, Real.exp_add, Real.exp_add]
    field_simp
  have hE2 : Real.exp (-p) * Real.exp (-(2 * b)) = (Real.exp p)⁻¹ * (Real.exp b)⁻¹ ^ 2 := by
    rw [Real.exp_neg, Real.exp_neg, show 2 * b = b + b by ring, Real.exp_add]
    field_simp
  rw [hE1] at hreg ⊢
  rw [hE2]
  have hb1 : 1 ≤ Real.exp b := Real.one_le_exp hb
  have hp1 : 1 ≤ Real.exp p := Real.one_le_exp hp
  generalize Real.exp p = X at *
  generalize Real.exp b = Y at *
  set M : ℕ := ⌈Y⌉₊ with hM
  have hMge : Y ≤ M := Nat.le_ceil _
  have hMlt : (M : ℝ) < Y + 1 := Nat.ceil_lt_add_one (by linarith)
  have hMR : (0 : ℝ) < M := lt_of_lt_of_le (by linarith) hMge
  have hMpos : 0 < M := by exact_mod_cast hMR
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hX0 : 0 < X := by linarith
  have hY0 : 0 < Y := by linarith
  set x : ℝ := N * (X⁻¹ * Y⁻¹ ^ 2) / (4 * q * M) with hx
  have hden : 0 < 4 * (q : ℝ) * M := by positivity
  have hx0 : 0 ≤ x := by positivity
  have hxlow : (N : ℝ) * (X⁻¹ ^ 2 * Y⁻¹ ^ 3) / 8 ≤ x := by
    rw [hx, div_le_div_iff₀ (by norm_num) hden]
    have h1 : (q : ℝ) * M ≤ X * (2 * Y) := mul_le_mul hqp (by linarith) hMR.le hX0.le
    have h2 : (N : ℝ) * (X⁻¹ ^ 2 * Y⁻¹ ^ 3) * (4 * q * M) ≤
        N * (X⁻¹ ^ 2 * Y⁻¹ ^ 3) * (4 * (X * (2 * Y))) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      linarith
    refine h2.trans (le_of_eq ?_)
    field_simp
    ring
  refine ⟨M, ⌊x⌋₊, hMpos, ?_, by linarith, hMge, ?_, ?_⟩
  · have : (1 : ℝ) ≤ x := by
      have h16 : (2 : ℝ) ≤ (N : ℝ) * (X⁻¹ ^ 2 * Y⁻¹ ^ 3) / 8 := by linarith
      linarith
    exact Nat.floor_pos.mpr this
  · have h1 := Nat.lt_floor_add_one x
    have h16 : (2 : ℝ) ≤ (N : ℝ) * (X⁻¹ ^ 2 * Y⁻¹ ^ 3) / 8 := by linarith
    linarith
  · have h1 : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le hx0
    calc (q : ℝ) * M * ⌊x⌋₊ ≤ q * M * x := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = N * (X⁻¹ * Y⁻¹ ^ 2) / 4 := by rw [hx]; field_simp

/-- `e^4 ≥ 32`. -/
theorem thirty_two_le_exp_four : (32 : ℝ) ≤ Real.exp 4 := by
  have h := Real.exp_one_gt_d9
  calc (32 : ℝ) ≤ (2.7182818283 : ℝ) ^ 4 := by norm_num
    _ ≤ (Real.exp 1) ^ 4 := pow_le_pow_left₀ (by norm_num) h.le 4
    _ = Real.exp 4 := by rw [← Real.exp_nat_mul]; norm_num

/-- **The next progression.**  See the module docstring. -/
theorem exists_next_ap {V : Type*} (ev' : V → ℤ → ℂ) {N : ℕ} (F e : ℤ → ℂ)
    (hF : ∀ n ∈ Finset.Icc (1 : ℤ) N, ‖F n‖ ≤ 1) (he : ∀ n, ‖e n‖ ≤ 1)
    {p b A : ℝ} (hp : 0 ≤ p) (hb : 0 ≤ b) {q : ℕ} {r lo hi : ℤ} (hAP : APInv N p q r lo hi)
    (hΘ : (N : ℝ) * Real.exp (-p) ≤ ‖∑ n ∈ apInt q r lo hi, F n * star (e n)‖)
    (hA1 : (N : ℝ) ≤ A * Real.exp b)
    (hreg : 16 ≤ (N : ℝ) * Real.exp (-(2 * p + 3 * b)))
    (hcell : ∀ z : ℤ, ∃ P : ℕ, 0 < P ∧ (P : ℝ) ≤ Real.exp b ∧ ∀ y : ℤ, |(y : ℝ)| ≤ A →
      ∃ v : V, ∀ (x : ℤ) (δ : ℝ), 0 ≤ δ → |(x : ℝ)| ≤ A → (P : ℤ) ∣ x - y →
        |(x : ℝ) - y| ≤ A * δ → ‖e (x + z) - ev' v x‖ ≤ Real.exp b * δ) :
    ∃ (q' : ℕ) (r' lo' hi' z : ℤ) (v : V), APInv N (3 * p + 3 * b + 4) q' r' lo' hi' ∧
      (N : ℝ) * Real.exp (-(3 * p + 3 * b + 4)) ≤
        ‖∑ n ∈ apInt q' r' lo' hi', F n * star (ev' v (n - z))‖ := by
  obtain ⟨M, T, hM, hT, hM2, hMb, hTlow, hBle⟩ :=
    block_params hp hb hAP.one_le_q hAP.q_le hreg
  have hq0 : 0 < q := hAP.one_le_q
  set θ : ℝ := Real.exp (-p) with hθ
  have hθ0 : 0 < θ := Real.exp_pos _
  have hθ1 : θ ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  set B : ℕ := q * M * T with hBdef
  have hBR : (B : ℝ) = q * M * T := by rw [hBdef]; push_cast; ring
  have hNR : (0 : ℝ) < N := by
    have h16 : (0 : ℝ) < (N : ℝ) * Real.exp (-(2 * p + 3 * b)) := by linarith
    exact pos_of_mul_pos_left h16 (Real.exp_pos _).le
  have hexpb : 1 ≤ Real.exp b := Real.one_le_exp hb
  have hexpb' : Real.exp (-b) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hexp2b : Real.exp (-(2 * b)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hApos : 0 < A := by
    by_contra h
    push Not at h
    have : A * Real.exp b ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h (Real.exp_pos _).le
    linarith
  set δ : ℝ := θ * Real.exp (-b) / 4 with hδ
  have hδ0 : 0 ≤ δ := by positivity
  have hδ1 : δ ≤ 1 := by
    have : θ * Real.exp (-b) ≤ 1 := by
      calc θ * Real.exp (-b) ≤ 1 * 1 := mul_le_mul hθ1 hexpb' (Real.exp_pos _).le zero_le_one
        _ = 1 := one_mul 1
    rw [hδ]; linarith
  have hεδ : Real.exp b * δ = θ / 4 := by
    rw [hδ]
    have : Real.exp b * Real.exp (-b) = 1 := by rw [← Real.exp_add]; simp
    calc Real.exp b * (θ * Real.exp (-b) / 4) = θ * (Real.exp b * Real.exp (-b)) / 4 := by ring
      _ = θ / 4 := by rw [this]; ring
  have hBθ : (B : ℝ) ≤ N * θ / 4 := by
    rw [hBR]
    refine hBle.trans ?_
    have : (N : ℝ) * (θ * Real.exp (-(2 * b))) ≤ N * θ :=
      mul_le_mul_of_nonneg_left (mul_le_of_le_one_right hθ0.le hexp2b) hNR.le
    linarith
  have hBA : (B : ℝ) ≤ A * δ := by
    rw [hBR]
    refine hBle.trans ?_
    have h1 : (N : ℝ) * (θ * Real.exp (-(2 * b))) ≤ A * Real.exp b * (θ * Real.exp (-(2 * b))) :=
      mul_le_mul_of_nonneg_right hA1 (by positivity)
    have h2 : A * Real.exp b * (θ * Real.exp (-(2 * b))) = A * (θ * Real.exp (-b)) := by
      have : Real.exp b * Real.exp (-(2 * b)) = Real.exp (-b) := by
        rw [← Real.exp_add]; congr 1; ring
      calc A * Real.exp b * (θ * Real.exp (-(2 * b))) =
          A * θ * (Real.exp b * Real.exp (-(2 * b))) := by ring
        _ = A * (θ * Real.exp (-b)) := by rw [this]; ring
    rw [hδ]
    linarith
  have hBAA : (B : ℝ) ≤ A := hBA.trans (mul_le_of_le_one_right hApos.le hδ1)
  have hF' : ∀ n ∈ apInt q r lo hi, ‖F n‖ ≤ 1 := fun n hn => by
    obtain ⟨h1, h2, -⟩ := mem_apInt.mp hn
    exact hF n (Finset.mem_Icc.mpr ⟨hAP.one_le_lo.trans h1, h2.trans (by exact_mod_cast hAP.hi_le)⟩)
  have hcell' : ∀ a : ℕ, ∃ P : ℕ, 0 < P ∧ P ≤ M ∧ ∀ y : ℤ, 0 ≤ y → y < B → ∃ w : ℤ × V,
      ∀ n : ℤ, lo + a * B ≤ n → n < lo + a * B + B → (P : ℤ) ∣ (n - (lo + a * B)) - y →
        ‖e n - ev' w.2 (n - w.1)‖ ≤ θ / 4 := by
    intro a
    obtain ⟨P, hP, hPb, hy⟩ := hcell (lo + a * B)
    refine ⟨P, hP, ?_, fun y hy0 hyB => ?_⟩
    · have : (P : ℝ) ≤ M := hPb.trans hMb
      exact_mod_cast this
    · have hyA : |(y : ℝ)| ≤ A := by
        rw [abs_of_nonneg (by exact_mod_cast hy0)]
        have : (y : ℝ) ≤ B := by exact_mod_cast hyB.le
        linarith
      obtain ⟨v, hv⟩ := hy y hyA
      refine ⟨(lo + a * B, v), fun n hn1 hn2 hdvd => ?_⟩
      have hx0 : 0 ≤ n - (lo + a * B) := by omega
      have hxB : n - (lo + a * B) < B := by omega
      have hxA : |((n - (lo + a * B) : ℤ) : ℝ)| ≤ A := by
        rw [abs_of_nonneg (by exact_mod_cast hx0)]
        have : ((n - (lo + a * B) : ℤ) : ℝ) ≤ B := by exact_mod_cast hxB.le
        linarith
      have hxy : |(((n - (lo + a * B) : ℤ) : ℝ)) - y| ≤ A * δ := by
        have h1 : ((n - (lo + a * B) : ℤ) : ℝ) - y ≤ B := by
          have : (n - (lo + a * B) : ℤ) - y ≤ B := by omega
          exact_mod_cast this
        have h2 : -(B : ℝ) ≤ ((n - (lo + a * B) : ℤ) : ℝ) - y := by
          have : -(B : ℤ) ≤ (n - (lo + a * B) : ℤ) - y := by omega
          exact_mod_cast this
        rw [abs_le]
        constructor <;> linarith
      have := hv (n - (lo + a * B)) δ hδ0 hxA hdvd hxy
      rw [sub_add_cancel, hεδ] at this
      exact this
  have hN' : (apInt q r lo hi).card ≤ N := card_apInt_le hAP.one_le_lo hAP.hi_le
  have hΘpos : (B : ℝ) + θ / 4 * N < N * θ := by
    linarith only [hBθ, mul_pos hNR hθ0]
  obtain ⟨m, ρ, u, w, hm0, hmle, -, hlou, hhiu, hcard, -, hcorr⟩ :=
    exists_cell_correlation (fun (w : ℤ × V) n => ev' w.2 (n - w.1)) hq0 F e hF' he
      (Θ := N * θ) (ε := θ / 4) (by positivity) hΘ hN' hT hM hBdef hcell' hΘpos
  refine ⟨m, ρ, u, u + B - 1, w.1, w.2, ⟨hm0, ?_, hAP.one_le_lo.trans hlou, ?_⟩, ?_⟩
  · have h1 : (m : ℝ) ≤ q * M := by exact_mod_cast hmle
    have h2 : (q : ℝ) * M ≤ Real.exp p * (2 * Real.exp b) :=
      mul_le_mul hAP.q_le hM2 (Nat.cast_nonneg _) (Real.exp_pos _).le
    have h3 : Real.exp p * (2 * Real.exp b) ≤ Real.exp (3 * p + 3 * b + 4) := by
      have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      calc Real.exp p * (2 * Real.exp b) ≤ Real.exp p * (Real.exp 1 * Real.exp b) := by
            gcongr
        _ = Real.exp (p + b + 1) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
        _ ≤ Real.exp (3 * p + 3 * b + 4) := Real.exp_le_exp.mpr (by linarith)
    linarith
  · exact hhiu.trans hAP.hi_le
  · have hc : θ / 2 ≤ (N * θ - B - θ / 4 * N) / N := by
      rw [le_div_iff₀ hNR]
      linarith only [hBθ]
    have hTR : (T : ℝ) ≤ (apInt m ρ u (u + B - 1)).card := by exact_mod_cast hcard
    have hlow : (N : ℝ) * Real.exp (-(2 * p + 3 * b)) / 16 ≤ (apInt m ρ u (u + B - 1)).card :=
      hTlow.trans hTR
    have h1 : θ / 2 * ((N : ℝ) * Real.exp (-(2 * p + 3 * b)) / 16) ≤
        (N * θ - B - θ / 4 * N) / N * (apInt m ρ u (u + B - 1)).card :=
      mul_le_mul hc hlow (by positivity) (by linarith)
    refine le_trans ?_ (h1.trans hcorr)
    have he4 : Real.exp (-(3 * p + 3 * b + 4)) =
        Real.exp (-(3 * p + 3 * b)) * Real.exp (-4) := by
      rw [← Real.exp_add]; congr 1; ring
    have he5 : Real.exp (-4) ≤ 1 / 32 := by
      rw [Real.exp_neg]
      have := thirty_two_le_exp_four
      rw [inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) this
    have he6 : θ * Real.exp (-(2 * p + 3 * b)) = Real.exp (-(3 * p + 3 * b)) := by
      rw [hθ, ← Real.exp_add]; congr 1; ring
    have hpos : 0 < Real.exp (-(3 * p + 3 * b)) := Real.exp_pos _
    calc (N : ℝ) * Real.exp (-(3 * p + 3 * b + 4)) =
        N * (Real.exp (-(3 * p + 3 * b)) * Real.exp (-4)) := by rw [he4]
      _ ≤ N * (Real.exp (-(3 * p + 3 * b)) * (1 / 32)) := by gcongr
      _ = θ / 2 * ((N : ℝ) * Real.exp (-(2 * p + 3 * b)) / 16) := by
        rw [← he6]; ring

end PrimeCarleson.Proof.Fplus31
