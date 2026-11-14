module

public import PrimeCarleson.Proof.Fplus31.C2.IterationPieces

/-!
# The iteration, the pigeonhole over the cells

Part of the type I / type II iteration of `C2/CMain.lean` (proof of [F+] Proposition 3.1). A
progression `P = apInt q r lo hi` correlates with a function `e` (the niltest of the stage) in the
sense `Θ ≤ ‖∑_{n ∈ P} F n · star (e n)‖`. In each block `[lo + a B, lo + (a+1) B)` of length
`B = q M T` the function `e` is approximated, on each cell `x ≡ y (P_a)`, to within `ε` by a test
`ev w` (`hcell`, the output of the sub-step for the window centre `lo + a B`). Then some cell, which
is a progression of modulus `m = q P_a ≤ q M` and length at least `T`, correlates with its test
`ev w` at the density `(Θ - B - ε N) / N`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

open Finset
open scoped BigOperators

/-- **The pigeonhole over the cells.**  See the module docstring. -/
theorem exists_cell_correlation {W : Type*} (ev : W → ℤ → ℂ) {q : ℕ} (hq : 0 < q) {r lo hi : ℤ}
    {N : ℕ} (F e : ℤ → ℂ) (hF : ∀ n ∈ apInt q r lo hi, ‖F n‖ ≤ 1) (he : ∀ n, ‖e n‖ ≤ 1)
    {Θ ε : ℝ} (hε : 0 ≤ ε) (hΘ : Θ ≤ ‖∑ n ∈ apInt q r lo hi, F n * star (e n)‖)
    (hN : (apInt q r lo hi).card ≤ N) {B M T : ℕ} (hT : 0 < T) (hM : 0 < M)
    (hB : B = q * M * T)
    (hcell : ∀ a : ℕ, ∃ P : ℕ, 0 < P ∧ P ≤ M ∧ ∀ y : ℤ, 0 ≤ y → y < B → ∃ w : W,
      ∀ n : ℤ, lo + a * B ≤ n → n < lo + a * B + B → (P : ℤ) ∣ (n - (lo + a * B)) - y →
        ‖e n - ev w n‖ ≤ ε)
    (hΘpos : (B : ℝ) + ε * N < Θ) :
    ∃ (m : ℕ) (ρ u : ℤ) (w : W), 0 < m ∧ m ≤ q * M ∧ q ∣ m ∧ lo ≤ u ∧ u + B - 1 ≤ hi ∧
      T ≤ (apInt m ρ u (u + B - 1)).card ∧ apInt m ρ u (u + B - 1) ⊆ apInt q r lo hi ∧
      (Θ - B - ε * N) / N * ((apInt m ρ u (u + B - 1)).card : ℝ) ≤
        ‖∑ n ∈ apInt m ρ u (u + B - 1), F n * star (ev w n)‖ := by
  have hB0 : 0 < B := by rw [hB]; positivity
  have hM_le_B : M ≤ B := by
    rw [hB]
    calc M = 1 * M * 1 := by ring
      _ ≤ q * M * T := Nat.mul_le_mul (Nat.mul_le_mul hq le_rfl) hT
  have hBR : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have hεN : 0 ≤ ε * N := by positivity
  have hΘ0 : 0 < Θ := lt_of_le_of_lt (by positivity) hΘpos
  have hNpos : 0 < N := by
    by_contra h
    have hN0 : N = 0 := by omega
    rw [hN0] at hN
    have hemp : apInt q r lo hi = ∅ := Finset.card_eq_zero.mp (by omega)
    rw [hemp] at hΘ
    simp only [Finset.sum_empty, norm_zero] at hΘ
    linarith
  -- the main part `P'` of the progression
  have hnonempty : lo ≤ hi := by
    by_contra h
    have hemp : apInt q r lo hi = ∅ := by
      ext n
      simp only [mem_apInt, Finset.notMem_empty, iff_false]
      omega
    rw [hemp] at hΘ
    simp only [Finset.sum_empty, norm_zero] at hΘ
    linarith
  set Ln : ℕ := (hi + 1 - lo).toNat with hLn
  set K : ℕ := Ln / B with hK
  have hKB : K * B ≤ Ln := Nat.div_mul_le_self Ln B
  have hLnB : Ln < K * B + B := by
    have := Nat.lt_div_mul_add (a := Ln) hB0
    simpa [hK, mul_comm] using this
  have hLnZ : (Ln : ℤ) = hi + 1 - lo := by
    rw [hLn]
    exact Int.toNat_of_nonneg (by omega)
  set hi' : ℤ := lo + (K : ℤ) * B - 1 with hhi'
  have hhi'le : hi' ≤ hi := by
    have : ((K * B : ℕ) : ℤ) ≤ Ln := by exact_mod_cast hKB
    push_cast at this
    omega
  have hsubP : apInt q r lo hi' ⊆ apInt q r lo hi := fun n hn => by
    obtain ⟨h1, h2, h3⟩ := mem_apInt.mp hn
    exact mem_apInt.mpr ⟨h1, h2.trans hhi'le, h3⟩
  -- the tail
  have hcardtail : ((apInt q r lo hi) \ (apInt q r lo hi')).card ≤ B := by
    have hsub : (apInt q r lo hi) \ (apInt q r lo hi') ⊆ Finset.Icc (hi' + 1) hi := by
      intro n hn
      obtain ⟨hn1, hn2⟩ := Finset.mem_sdiff.mp hn
      obtain ⟨h1, h2, h3⟩ := mem_apInt.mp hn1
      refine Finset.mem_Icc.mpr ⟨?_, h2⟩
      by_contra hlt
      exact hn2 (mem_apInt.mpr ⟨h1, by omega, h3⟩)
    refine (Finset.card_le_card hsub).trans ?_
    rw [Int.card_Icc]
    have : ((K * B : ℕ) : ℤ) + B > Ln := by exact_mod_cast hLnB
    push_cast at this
    omega
  have hsumtail : ‖∑ n ∈ (apInt q r lo hi) \ (apInt q r lo hi'), F n * star (e n)‖ ≤ B := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ n ∈ (apInt q r lo hi) \ (apInt q r lo hi'), ‖F n * star (e n)‖
        ≤ ∑ n ∈ (apInt q r lo hi) \ (apInt q r lo hi'), (1 : ℝ) := by
          refine Finset.sum_le_sum fun n hn => ?_
          rw [norm_mul, norm_star]
          have h1 := hF n (Finset.mem_sdiff.mp hn).1
          have h2 := he n
          calc ‖F n‖ * ‖e n‖ ≤ 1 * 1 := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
            _ = 1 := one_mul 1
      _ = (((apInt q r lo hi) \ (apInt q r lo hi')).card : ℝ) := by simp
      _ ≤ B := by exact_mod_cast hcardtail
  have hmain : Θ - B ≤ ‖∑ n ∈ apInt q r lo hi', F n * star (e n)‖ := by
    have hsplit := Finset.sum_sdiff hsubP (f := fun n => F n * star (e n))
    have h1 : ‖∑ n ∈ apInt q r lo hi, F n * star (e n)‖ ≤
        ‖∑ n ∈ (apInt q r lo hi) \ (apInt q r lo hi'), F n * star (e n)‖ +
          ‖∑ n ∈ apInt q r lo hi', F n * star (e n)‖ := by
      rw [← hsplit]
      exact norm_add_le _ _
    linarith
  -- the choice of the periods and tests
  have hne : Nonempty W := by
    obtain ⟨P, -, -, hy⟩ := hcell 0
    obtain ⟨w, -⟩ := hy 0 le_rfl (by exact_mod_cast hB0)
    exact ⟨w⟩
  have hcell' : ∀ a : ℕ, ∃ P : ℕ, 0 < P ∧ P ≤ M ∧ ∀ y : ℤ, ∃ w : W, 0 ≤ y → y < B →
      ∀ n : ℤ, lo + a * B ≤ n → n < lo + a * B + B → (P : ℤ) ∣ (n - (lo + a * B)) - y →
        ‖e n - ev w n‖ ≤ ε := by
    intro a
    obtain ⟨P, hP, hPM, hy⟩ := hcell a
    refine ⟨P, hP, hPM, fun y => ?_⟩
    by_cases h : 0 ≤ y ∧ y < B
    · obtain ⟨w, hw⟩ := hy y h.1 h.2
      exact ⟨w, fun _ _ => hw⟩
    · obtain ⟨w⟩ := hne
      exact ⟨w, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose Pa hPa0 hPaM Wt hWt using hcell'
  set m : ℕ → ℕ := fun a => q * Pa a with hm
  have hmq : ∀ a, 0 < m a ∧ q ∣ m a := fun a => ⟨Nat.mul_pos hq (hPa0 a), dvd_mul_right _ _⟩
  have hmle : ∀ a, m a ≤ q * M := fun a => Nat.mul_le_mul_left _ (hPaM a)
  let wsel : ℕ × ℤ → W := fun k =>
    Wt k.1 ((k.2 - (lo + (k.1 : ℤ) * B)) % (Pa k.1 : ℤ))
  let g : ℤ → ℂ := fun n => ev (wsel (cellOf lo B m n)) n
  -- the approximation on `P'`
  have happrox : ∀ n ∈ apInt q r lo hi', ‖e n - g n‖ ≤ ε := by
    intro n hn
    obtain ⟨hn1, -, -⟩ := mem_apInt.mp hn
    set a := blkIdx lo B n with ha
    obtain ⟨hb1, hb2⟩ := blkIdx_spec hB0 hn1
    have hPaZ : (0 : ℤ) < Pa a := by exact_mod_cast hPa0 a
    set c : ℤ := n % (m a : ℤ) - (lo + (a : ℤ) * B) with hc
    have hy0 : 0 ≤ c % (Pa a : ℤ) := Int.emod_nonneg _ hPaZ.ne'
    have hy1 : c % (Pa a : ℤ) < B := by
      have h1 := Int.emod_lt_of_pos c hPaZ
      have h2 : (Pa a : ℤ) ≤ B := by exact_mod_cast (hPaM a).trans hM_le_B
      omega
    have hdvd : (Pa a : ℤ) ∣ (n - (lo + (a : ℤ) * B)) - c % (Pa a : ℤ) := by
      have e1 : (n - (lo + (a : ℤ) * B)) - c % (Pa a : ℤ) =
          (m a : ℤ) * (n / (m a : ℤ)) + (Pa a : ℤ) * (c / (Pa a : ℤ)) := by
        have h1 := Int.mul_ediv_add_emod n (m a : ℤ)
        have h2 := Int.mul_ediv_add_emod c (Pa a : ℤ)
        linarith
      rw [e1]
      refine dvd_add ?_ (dvd_mul_right _ _)
      exact Dvd.dvd.mul_right (by simp [hm]) _
    have := hWt a ((n % (m a : ℤ) - (lo + (a : ℤ) * B)) % (Pa a : ℤ)) hy0 hy1 n hb1
      (by linarith) hdvd
    exact this
  have hcardP' : (apInt q r lo hi').card ≤ N := (Finset.card_le_card hsubP).trans hN
  have hdiff : ‖∑ n ∈ apInt q r lo hi', F n * star (e n) -
      ∑ n ∈ apInt q r lo hi', F n * star (g n)‖ ≤ ε * N := by
    rw [← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ n ∈ apInt q r lo hi', ‖F n * star (e n) - F n * star (g n)‖
        ≤ ∑ n ∈ apInt q r lo hi', ε := by
          refine Finset.sum_le_sum fun n hn => ?_
          rw [← mul_sub, norm_mul, ← star_sub, norm_star]
          calc ‖F n‖ * ‖e n - g n‖ ≤ 1 * ε :=
                mul_le_mul (hF n (hsubP hn)) (happrox n hn) (norm_nonneg _) zero_le_one
            _ = ε := one_mul _
      _ = ((apInt q r lo hi').card : ℝ) * ε := by simp
      _ ≤ N * ε := mul_le_mul_of_nonneg_right (by exact_mod_cast hcardP') hε
      _ = ε * N := mul_comm _ _
  have hg : Θ - B - ε * N ≤ ‖∑ n ∈ apInt q r lo hi', F n * star (g n)‖ := by
    have := norm_sub_norm_le (∑ n ∈ apInt q r lo hi', F n * star (e n))
      (∑ n ∈ apInt q r lo hi', F n * star (g n))
    linarith
  set t := (apInt q r lo hi').image (cellOf lo B m) with ht
  have hmaps : ∀ n ∈ apInt q r lo hi', cellOf lo B m n ∈ t := fun n hn =>
    Finset.mem_image_of_mem _ hn
  have hfib := Finset.sum_fiberwise_of_maps_to (s := apInt q r lo hi') (t := t)
    (g := cellOf lo B m) hmaps (fun n => F n * star (g n))
  set Sk : ℕ × ℤ → ℂ := fun k => ∑ n ∈ (apInt q r lo hi').filter
    (fun n => cellOf lo B m n = k), F n * star (ev (wsel k) n) with hSk
  have hSk' : ∀ k ∈ t, ∑ n ∈ (apInt q r lo hi').filter (fun n => cellOf lo B m n = k),
      F n * star (g n) = Sk k := by
    intro k _
    refine Finset.sum_congr rfl fun n hn => ?_
    have := (Finset.mem_filter.mp hn).2
    simp only [g, this]
  have hsumk : Θ - B - ε * N ≤ ∑ k ∈ t, ‖Sk k‖ := by
    refine hg.trans ?_
    rw [← hfib]
    refine (norm_sum_le _ _).trans ?_
    exact Finset.sum_le_sum fun k hk => by rw [hSk' k hk]
  set c : ℝ := (Θ - B - ε * N) / N with hc
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hΘ' : 0 < Θ - B - ε * N := by linarith
  have hcard_fib : ∑ k ∈ t, (((apInt q r lo hi').filter
      (fun n => cellOf lo B m n = k)).card : ℝ) = (apInt q r lo hi').card := by
    have := Finset.card_eq_sum_card_fiberwise (s := apInt q r lo hi') (t := t)
      (f := cellOf lo B m) hmaps
    exact_mod_cast this.symm
  have hlow : ∑ k ∈ t, c * (((apInt q r lo hi').filter
      (fun n => cellOf lo B m n = k)).card : ℝ) ≤ ∑ k ∈ t, ‖Sk k‖ := by
    rw [← Finset.mul_sum, hcard_fib]
    refine le_trans ?_ hsumk
    calc c * ((apInt q r lo hi').card : ℝ) ≤ c * N :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast hcardP') (by positivity)
      _ = Θ - B - ε * N := by rw [hc]; field_simp
  have htne : t.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h] at hsumk
    simp only [Finset.sum_empty] at hsumk
    linarith
  obtain ⟨k, hk, hkle⟩ := Finset.exists_le_of_sum_le htne hlow
  obtain ⟨n₀, hn₀, rfl⟩ := Finset.mem_image.mp hk
  have hfe := fibre_eq_apInt (q := q) (r := r) (lo := lo) (B := B) (K := K) hB0 hmq hn₀
  set a := blkIdx lo B n₀ with ha
  have haK : a < K := blkIdx_lt hB0 hn₀
  have hKa : ((a : ℤ) + 1) * B ≤ K * B := by
    have : (a : ℤ) + 1 ≤ K := by exact_mod_cast haK
    exact mul_le_mul_of_nonneg_right this (by positivity)
  refine ⟨m a, n₀ % (m a : ℤ), lo + (a : ℤ) * B, wsel (cellOf lo B m n₀), (hmq a).1, hmle a,
    (hmq a).2, by linarith only [(by positivity : (0 : ℤ) ≤ (a : ℤ) * B)], ?_, ?_, ?_, ?_⟩
  · have : (lo + (a : ℤ) * B + B - 1) ≤ hi' := by
      have h1 : lo + ((a : ℤ) + 1) * B - 1 ≤ lo + K * B - 1 := by linarith
      linarith only [h1, hhi']
    omega
  · refine le_trans ?_ (card_apInt_block_ge (hmq a).1 _ _ B)
    rw [Nat.le_div_iff_mul_le (hmq a).1]
    calc T * m a ≤ T * (q * M) := Nat.mul_le_mul_left _ (hmle a)
      _ = B := by rw [hB]; ring
  · rw [← hfe]
    exact (Finset.filter_subset _ _).trans hsubP
  · rw [← hfe]
    exact hkle

end PrimeCarleson.Proof.Fplus31
