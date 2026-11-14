module

public import PrimeCarleson.Proof.Paper.Defs.Gowers

/-!
# The size of the normalizing constant `‖1_{[N]}‖_{U^s(ℤ)} ≈ N^{(s+1)/2^s}`

The comparison `‖1_{[N]}‖_{U^s(ℤ)} ≈ N^{(s+1)/2^s}` printed inside the definition of the normalized
`U^s([N])` norm (`sources/Variational_Carleson.tex` L702-L707; Source: main paper `s:Prelim`, L706;
consumers `e:U2-conv` (L836–L837, `s = 2`) and
`e:U3maxmod` (L877–L883, `s = 2, 3`)), proved for **every** `s ≥ 1` and for
every interval `I = {a, …, a + L - 1}` of `L` consecutive integers (this covers `[N]`,
`[-N, 2N]`, `[2^k]` and `[-2^k, 2^k]`).

With `g = ‖1_I‖_{U^s(ℤ)}`:

* `gowersNorm_indicator_pow_le`: `g^{2^s} ≤ 3^s L^{s+1}`; the Gowers sum
  `∑_{x, h₁, …, h_s} Δ_{h₁,…,h_s} 1_I(x)` has at most `L (2L + 1)^s` nonzero terms, each of size at
  most `1` (the finite box form `gowersNorm_pow_eq_sum_box`);
* `pow_le_gowersNorm_indicator_pow`: `L^{s+1} ≤ 2 (2s)^s g^{2^s}`; all terms are nonnegative
  reals and at least `(L - ⌊L/2⌋) (⌊L/(2s)⌋ + 1)^s` of them equal `1`: those with
  `x` in the first `L - ⌊L/2⌋` points of `I` and all `h_i ∈ [0, ⌊L/(2s)⌋]`, for which the whole
  cube `x + {0,1}·h` lies in `I` (`multDiff_indicator_eq_one`);
* `gowersNorm_Icc_indicator_approx`: the two-sided estimate
  `c_s L^{(s+1)/2^s} ≤ ‖1_I‖_{U^s(ℤ)} ≤ C_s L^{(s+1)/2^s}` for an arbitrary interval `I` of `L`
  consecutive integers (in particular `I = [N]`), with `c_s, C_s > 0` depending only on `s`.
-/

@[expose] public noncomputable section

open scoped ComplexConjugate

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson

/-- Every term of the Gowers sum of an indicator function has norm at most `1`. -/
theorem norm_multDiff_indicator_le_one (I : Finset ℤ) :
    ∀ (s : ℕ) (h : Fin s → ℤ) (x : ℤ), ‖multDiff s h (restrictFinset I 1) x‖ ≤ 1 := by
  intro s
  induction s with
  | zero =>
    intro h x
    rw [multDiff_zero, restrictFinset_apply]
    by_cases hx : x ∈ I <;> simp [hx]
  | succ s ih =>
    intro h x
    rw [multDiff_succ, conjDiff_apply, norm_mul, RCLike.norm_conj]
    calc ‖multDiff s (Fin.init h) (restrictFinset I 1) x‖ *
          ‖multDiff s (Fin.init h) (restrictFinset I 1) (x + h (Fin.last s))‖ ≤ 1 * 1 :=
          mul_le_mul (ih _ _) (ih _ _) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1

/-- If the base point is `≥ a₀` and `x + ∑ h_i ≤ b₀` for nonnegative steps `h_i`, then the whole
cube `x + {0,1}·h` lies in `[a₀, b₀]` and the term `Δ_{h₁,…,h_s} 1_{[a₀, b₀]}(x)` equals `1`. -/
theorem multDiff_indicator_eq_one (a₀ b₀ : ℤ) :
    ∀ (s : ℕ) (h : Fin s → ℤ), (∀ i, 0 ≤ h i) → ∀ x : ℤ, a₀ ≤ x → x + ∑ i, h i ≤ b₀ →
      multDiff s h (restrictFinset (Finset.Icc a₀ b₀) 1) x = 1 := by
  intro s
  induction s with
  | zero =>
    intro h _ x hx0 hx1
    rw [multDiff_zero, restrictFinset_apply]
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero] at hx1
    simp [hx0, hx1]
  | succ s ih =>
    intro h hh x hx0 hx1
    have hsum : ∑ i : Fin (s + 1), h i = ∑ i : Fin s, h (Fin.castSucc i) + h (Fin.last s) :=
      Fin.sum_univ_castSucc h
    have hinit : ∀ i, 0 ≤ Fin.init h i := fun i => hh _
    have hl : 0 ≤ h (Fin.last s) := hh _
    have hs0 : 0 ≤ ∑ i : Fin s, h (Fin.castSucc i) := Finset.sum_nonneg fun i _ => hh _
    rw [multDiff_succ, conjDiff_apply]
    have e1 := ih (Fin.init h) hinit x hx0 (by
      change x + ∑ i : Fin s, h (Fin.castSucc i) ≤ b₀
      linarith)
    have e2 := ih (Fin.init h) hinit (x + h (Fin.last s)) (by linarith) (by
      change x + h (Fin.last s) + ∑ i : Fin s, h (Fin.castSucc i) ≤ b₀
      linarith)
    rw [e1, e2]
    simp

/-- The `2^s`-th power of the `U^s(ℤ)` norm of the indicator of `I = {a, …, a + L - 1}` is at most
`3^s L^{s+1}`. -/
theorem gowersNorm_indicator_pow_le (s : ℕ+) (a : ℤ) (L : ℕ) :
    gowersNorm s (restrictFinset (Finset.Icc a (a + L - 1)) 1) ^ 2 ^ (s : ℕ) ≤
      3 ^ (s : ℕ) * (L : ℝ) ^ ((s : ℕ) + 1) := by
  classical
  set I : Finset ℤ := Finset.Icc a (a + L - 1) with hI
  set B : Finset ℤ := Finset.Icc (-(L : ℤ)) L with hB
  have hIsupp : ∀ x, restrictFinset I 1 x ≠ 0 → x ∈ I := fun x hx => by
    by_contra hxI
    exact hx (by simp [restrictFinset_apply, hxI])
  have hBd : ∀ x ∈ I, ∀ y ∈ I, y - x ∈ B := fun x hx y hy => by
    simp only [hI, hB, Finset.mem_Icc] at hx hy ⊢
    omega
  have h0 := gowersNorm_pow_eq_sum_box s (restrictFinset I 1) I B hIsupp hBd
  have hnorm : gowersNorm s (restrictFinset I 1) ^ 2 ^ (s : ℕ) ≤
      ∑ x ∈ I, ∑ h ∈ Fintype.piFinset (fun _ : Fin s => B), 1 := by
    have h1 : ‖((gowersNorm s (restrictFinset I 1) : ℝ) : ℂ) ^ 2 ^ (s : ℕ)‖ ≤
        ∑ x ∈ I, ∑ h ∈ Fintype.piFinset (fun _ : Fin s => B), (1 : ℝ) := by
      rw [h0]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun h _ => ?_)
      exact norm_multDiff_indicator_le_one I s h x
    rwa [norm_pow, Complex.norm_real, Real.norm_of_nonneg (gowersNorm_nonneg _ _)] at h1
  refine hnorm.trans ?_
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, Fintype.card_piFinset,
    Finset.prod_const, Fintype.card_fin, Nat.cast_pow]
  have hIc : (I.card : ℝ) = L := by simp [hI, Int.card_Icc]
  have hBc : (B.card : ℝ) = 2 * L + 1 := by
    simp only [hB, Int.card_Icc]
    have : ((L : ℤ) + 1 - -(L : ℤ)).toNat = 2 * L + 1 := by omega
    rw [this]
    push_cast
    ring
  rw [hIc, hBc]
  rcases Nat.eq_zero_or_pos L with hL | hL
  · subst hL
    simp
  · have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
    have : 2 * (L : ℝ) + 1 ≤ 3 * L := by linarith
    calc (L : ℝ) * (2 * L + 1) ^ (s : ℕ) ≤ L * (3 * L) ^ (s : ℕ) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) this _) (by positivity)
      _ = 3 ^ (s : ℕ) * (L : ℝ) ^ ((s : ℕ) + 1) := by ring

/-- The number of terms of the Gowers sum of the indicator of `I = {a, …, a + L - 1}` that are
equal to `1` is at least `L^{s+1} / (2 (2s)^s)`: `L^{s+1} ≤ 2 (2s)^s ‖1_I‖_{U^s(ℤ)}^{2^s}`. -/
theorem pow_le_gowersNorm_indicator_pow (s : ℕ+) (a : ℤ) (L : ℕ) :
    (L : ℝ) ^ ((s : ℕ) + 1) ≤
      2 * (2 * (s : ℝ)) ^ (s : ℕ) *
        gowersNorm s (restrictFinset (Finset.Icc a (a + L - 1)) 1) ^ 2 ^ (s : ℕ) := by
  classical
  set I : Finset ℤ := Finset.Icc a (a + L - 1) with hI
  set B : Finset ℤ := Finset.Icc (-(L : ℤ)) L with hB
  set F : ℤ →₀ ℂ := restrictFinset I 1 with hF
  have hIsupp : ∀ x, F x ≠ 0 → x ∈ I := fun x hx => by
    by_contra hxI
    exact hx (by simp [hF, restrictFinset_apply, hxI])
  have hBd : ∀ x ∈ I, ∀ y ∈ I, y - x ∈ B := fun x hx y hy => by
    simp only [hI, hB, Finset.mem_Icc] at hx hy ⊢
    omega
  have h0 := gowersNorm_pow_eq_sum_box s F I B hIsupp hBd
  have hre : gowersNorm s F ^ 2 ^ (s : ℕ) =
      ∑ x ∈ I, ∑ h ∈ Fintype.piFinset (fun _ : Fin s => B), (multDiff s h F x).re := by
    have := congrArg Complex.re h0
    rw [← Complex.ofReal_pow, Complex.ofReal_re, Complex.re_sum] at this
    rw [this]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Complex.re_sum]
  have hnonneg : ∀ x h, 0 ≤ (multDiff s h F x).re := fun x h => by
    obtain ⟨r, hr, hr'⟩ := multDiff_indicator_nonneg I s h x
    rw [hr', Complex.ofReal_re]
    exact hr
  -- the parameters of the sub-box
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = L / (2 * (s : ℕ)) := ⟨_, rfl⟩
  obtain ⟨a', ha'⟩ : ∃ a' : ℕ, a' = L - L / 2 := ⟨_, rfl⟩
  set I' : Finset ℤ := Finset.Icc a (a + a' - 1) with hI'
  set B' : Finset ℤ := Finset.Icc 0 (M : ℤ) with hB'
  have hsM : (s : ℕ) * M ≤ L / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    have h1 : 2 * (s : ℕ) * M ≤ L := by rw [hM]; exact Nat.mul_div_le L (2 * (s : ℕ))
    nlinarith
  have hI'I : I' ⊆ I := fun x hx => by
    simp only [hI', hI, Finset.mem_Icc] at hx ⊢
    omega
  have hML : M ≤ L := by rw [hM]; exact Nat.div_le_self _ _
  have hB'B : B' ⊆ B := fun x hx => by
    simp only [hB', hB, Finset.mem_Icc] at hx ⊢
    omega
  have hone : ∀ x ∈ I', ∀ h ∈ Fintype.piFinset (fun _ : Fin s => B'),
      (multDiff s h F x).re = 1 := by
    intro x hx h hh
    have hxi : a ≤ x ∧ x ≤ a + a' - 1 := Finset.mem_Icc.1 hx
    have hhi : ∀ i, 0 ≤ h i ∧ h i ≤ (M : ℤ) := fun i =>
      Finset.mem_Icc.1 (Fintype.mem_piFinset.1 hh i)
    have hsum : ∑ i, h i ≤ ∑ _i : Fin s, (M : ℤ) := Finset.sum_le_sum fun i _ => (hhi i).2
    have hsum' : ∑ _i : Fin s, (M : ℤ) = (s : ℕ) * M := by simp
    have hcast : (((s : ℕ) * M : ℕ) : ℤ) ≤ ((L / 2 : ℕ) : ℤ) := by exact_mod_cast hsM
    have hcast' : (((s : ℕ) * M : ℕ) : ℤ) = (s : ℕ) * (M : ℤ) := by push_cast; ring
    have e := multDiff_indicator_eq_one a (a + L - 1) s h (fun i => (hhi i).1) x hxi.1 (by
      have : (a' : ℤ) = L - ((L / 2 : ℕ) : ℤ) := by omega
      omega)
    rw [hF, hI]
    rw [e]
    simp
  -- count
  have hcount : ∑ x ∈ I', ∑ h ∈ Fintype.piFinset (fun _ : Fin s => B'), (1 : ℝ) ≤
      gowersNorm s F ^ 2 ^ (s : ℕ) := by
    rw [hre]
    calc ∑ x ∈ I', ∑ h ∈ Fintype.piFinset (fun _ : Fin s => B'), (1 : ℝ)
        = ∑ x ∈ I', ∑ h ∈ Fintype.piFinset (fun _ : Fin s => B'), (multDiff s h F x).re :=
          Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun h hh => (hone x hx h hh).symm
      _ ≤ ∑ x ∈ I', ∑ h ∈ Fintype.piFinset (fun _ : Fin s => B), (multDiff s h F x).re := by
          refine Finset.sum_le_sum fun x _ => ?_
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun h _ _ => hnonneg x h
          intro h hh
          exact Fintype.mem_piFinset.2 fun i => hB'B (Fintype.mem_piFinset.1 hh i)
      _ ≤ ∑ x ∈ I, ∑ h ∈ Fintype.piFinset (fun _ : Fin s => B), (multDiff s h F x).re :=
          Finset.sum_le_sum_of_subset_of_nonneg hI'I fun x _ _ =>
            Finset.sum_nonneg fun h _ => hnonneg x h
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, Fintype.card_piFinset,
    Finset.prod_const, Fintype.card_fin, Nat.cast_pow] at hcount
  have hI'c : (I'.card : ℝ) = a' := by simp [hI', Int.card_Icc]
  have hB'c : (B'.card : ℝ) = M + 1 := by
    simp only [hB', Int.card_Icc]
    have : ((M : ℤ) + 1 - 0).toNat = M + 1 := by omega
    rw [this]
    push_cast
    ring
  rw [hI'c, hB'c] at hcount
  -- the real inequality `a' (M + 1)^s ≥ L^{s+1} / (2 (2s)^s)`
  have hs0 : (0 : ℝ) < s := by exact_mod_cast s.pos
  have ha'ge : (L : ℝ) / 2 ≤ a' := by
    have : L ≤ 2 * a' := by omega
    have h' : (L : ℝ) ≤ 2 * a' := by exact_mod_cast this
    linarith
  have hMge : (L : ℝ) / (2 * s) ≤ M + 1 := by
    have h1 : L ≤ 2 * (s : ℕ) * (M + 1) := by
      rw [hM]
      exact (Nat.lt_mul_div_succ L (by have := s.pos; omega : 0 < 2 * (s : ℕ))).le
    have h' : (L : ℝ) ≤ 2 * s * (M + 1) := by exact_mod_cast h1
    rw [div_le_iff₀ (by positivity)]
    linarith
  have key : (L : ℝ) ^ ((s : ℕ) + 1) ≤ 2 * (2 * (s : ℝ)) ^ (s : ℕ) * (a' * (M + 1) ^ (s : ℕ)) := by
    have h1 : ((L : ℝ) / (2 * s)) ^ (s : ℕ) ≤ (M + 1) ^ (s : ℕ) :=
      pow_le_pow_left₀ (by positivity) hMge _
    have h2 : (L : ℝ) / 2 * ((L : ℝ) / (2 * s)) ^ (s : ℕ) ≤ a' * (M + 1) ^ (s : ℕ) :=
      mul_le_mul ha'ge h1 (by positivity) (by positivity)
    have h3 : 2 * (2 * (s : ℝ)) ^ (s : ℕ) * ((L : ℝ) / 2 * ((L : ℝ) / (2 * s)) ^ (s : ℕ)) =
        (L : ℝ) ^ ((s : ℕ) + 1) := by
      rw [div_pow, pow_succ]
      field_simp
    calc (L : ℝ) ^ ((s : ℕ) + 1) = _ := h3.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by positivity)
  calc (L : ℝ) ^ ((s : ℕ) + 1) ≤ 2 * (2 * (s : ℝ)) ^ (s : ℕ) * (a' * (M + 1) ^ (s : ℕ)) := key
    _ ≤ 2 * (2 * (s : ℝ)) ^ (s : ℕ) * gowersNorm s F ^ 2 ^ (s : ℕ) :=
        mul_le_mul_of_nonneg_left hcount (by positivity)


/-- The exponent identity `(L^{(s+1)/2^s})^{2^s} = L^{s+1}`. -/
theorem rpow_div_pow_two_pow (s : ℕ+) (L : ℝ) (hL : 0 ≤ L) :
    (L ^ (((s : ℝ) + 1) / 2 ^ (s : ℕ))) ^ 2 ^ (s : ℕ) = L ^ ((s : ℕ) + 1) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hL, ← Real.rpow_natCast L]
  congr 1
  push_cast
  field_simp

/-- **The size of the normalizing constant, for an arbitrary interval** (Source: main paper
`s:Prelim`, L706): for every `s ≥ 1` there are constants
`0 < c_s, C_s` (explicitly `c_s = 1 / (2 (2s)^s)`, `C_s = 3^s`) such that for every interval
`I = {a, …, a + L - 1}` of `L` consecutive integers,
`c_s L^{(s+1)/2^s} ≤ ‖1_I‖_{U^s(ℤ)} ≤ C_s L^{(s+1)/2^s}`. -/
theorem gowersNorm_Icc_indicator_approx (s : ℕ+) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (a : ℤ) (L : ℕ),
      c * (L : ℝ) ^ (((s : ℝ) + 1) / 2 ^ (s : ℕ)) ≤
          gowersNorm s (restrictFinset (Finset.Icc a (a + L - 1)) 1) ∧
        gowersNorm s (restrictFinset (Finset.Icc a (a + L - 1)) 1) ≤
          C * (L : ℝ) ^ (((s : ℝ) + 1) / 2 ^ (s : ℕ)) := by
  have hs0 : (0 : ℝ) < s := by exact_mod_cast s.pos
  have hK1 : (1 : ℝ) ≤ 2 * (2 * (s : ℝ)) ^ (s : ℕ) := by
    have h1 : (1 : ℝ) ≤ s := by exact_mod_cast s.pos
    have : (1 : ℝ) ≤ (2 * (s : ℝ)) ^ (s : ℕ) := one_le_pow₀ (by linarith)
    linarith
  have hC1 : (1 : ℝ) ≤ 3 ^ (s : ℕ) := one_le_pow₀ (by norm_num)
  have hn : (2 : ℕ) ^ (s : ℕ) ≠ 0 := by positivity
  refine ⟨1 / (2 * (2 * (s : ℝ)) ^ (s : ℕ)), 3 ^ (s : ℕ), by positivity, by positivity,
    fun a L => ?_⟩
  set g : ℝ := gowersNorm s (restrictFinset (Finset.Icc a (a + L - 1)) 1) with hg
  set P : ℝ := (L : ℝ) ^ (((s : ℝ) + 1) / 2 ^ (s : ℕ)) with hP
  have hg0 : 0 ≤ g := gowersNorm_nonneg _ _
  have hP0 : 0 ≤ P := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hPn : P ^ 2 ^ (s : ℕ) = (L : ℝ) ^ ((s : ℕ) + 1) :=
    rpow_div_pow_two_pow s L (Nat.cast_nonneg _)
  have hup := gowersNorm_indicator_pow_le s a L
  have hlow := pow_le_gowersNorm_indicator_pow s a L
  rw [← hg, ← hPn] at hup hlow
  constructor
  · rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    have : P ^ 2 ^ (s : ℕ) ≤ (2 * (2 * (s : ℝ)) ^ (s : ℕ) * g) ^ 2 ^ (s : ℕ) := by
      calc P ^ 2 ^ (s : ℕ) ≤ 2 * (2 * (s : ℝ)) ^ (s : ℕ) * g ^ 2 ^ (s : ℕ) := hlow
        _ ≤ (2 * (2 * (s : ℝ)) ^ (s : ℕ)) ^ 2 ^ (s : ℕ) * g ^ 2 ^ (s : ℕ) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact le_self_pow₀ hK1 hn
        _ = _ := (mul_pow _ _ _).symm
    have := (pow_le_pow_iff_left₀ hP0 (by positivity) hn).1 this
    linarith
  · have : g ^ 2 ^ (s : ℕ) ≤ (3 ^ (s : ℕ) * P) ^ 2 ^ (s : ℕ) := by
      calc g ^ 2 ^ (s : ℕ) ≤ 3 ^ (s : ℕ) * P ^ 2 ^ (s : ℕ) := hup
        _ ≤ (3 ^ (s : ℕ)) ^ 2 ^ (s : ℕ) * P ^ 2 ^ (s : ℕ) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact le_self_pow₀ hC1 hn
        _ = _ := (mul_pow _ _ _).symm
    exact (pow_le_pow_iff_left₀ hg0 (by positivity) hn).1 this

end PrimeCarleson.Proof.Paper
