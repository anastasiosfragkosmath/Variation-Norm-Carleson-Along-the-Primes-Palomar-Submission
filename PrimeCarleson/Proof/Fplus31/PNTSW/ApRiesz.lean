module

public import PrimeCarleson.Proof.Fplus31.PNTSW.Principal
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

/-!
# From characters to progressions: the Riesz mean of `Λ` over `n ≡ a (mod q)`

Part of the prime number theorem in progressions on the classical zero-free region
(`PNTSW/Main.lean`). For `gcd(a, q) = 1` the orthogonality relation
(`DirichletCharacter.sum_char_inv_mul_char_eq`) gives

`∑_{n ≤ y, n ≡ a (q)} Λ(n)(y - n) = (1/φ(q)) ∑_χ χ(a⁻¹) ∑_{n ≤ y} χ(n)Λ(n)(y - n)`,

and `riesz_principal_sw` (for `χ₀`) with `riesz_nonprincipal_sw` (for the `φ(q) - 1` other
characters, no `φ(q)` loss) give `riesz_ap_sw`: for `y ≥ y₀` and `log q ≤ √(log y)`,

`|∑_{n ≤ y, n ≡ a (q)} Λ(n)(y - n) - y²/(2φ(q))| ≤ 4 y² exp (-c₁ √(log y))`.
-/

@[expose] public noncomputable section

open Complex ArithmeticFunction Filter
open scoped Real

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31.PNTSW

/-- An integer coprime to `q` is a unit of `ZMod q`. -/
theorem isUnit_intCast_of_isCoprime {q : ℕ} {a : ℤ} (ha : IsCoprime a (q : ℤ)) :
    IsUnit (a : ZMod q) := by
  obtain ⟨u, v, huv⟩ := ha
  have h := congrArg (Int.cast : ℤ → ZMod q) huv
  push_cast at h
  rw [ZMod.natCast_self, mul_zero, add_zero] at h
  have h' : (a : ZMod q) * (u : ZMod q) = 1 := by rw [mul_comm]; exact h
  exact Units.isUnit ⟨(a : ZMod q), (u : ZMod q), h', h⟩

/-- The orthogonality relation for one `n`. -/
theorem orthogonality_term {q : ℕ} [NeZero q] {a : ℤ} (ha : IsUnit (a : ZMod q)) (n : ℕ) (c : ℂ) :
    (if (n : ℤ) ≡ a [ZMOD q] then c else 0) =
      (1 / (Nat.totient q : ℂ)) *
        ∑ χ : DirichletCharacter ℂ q, χ (a : ZMod q)⁻¹ * (χ n * c) := by
  have h := DirichletCharacter.sum_char_inv_mul_char_eq ℂ ha (n : ZMod q)
  have hφ : (Nat.totient q : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  have e : ∑ χ : DirichletCharacter ℂ q, χ (a : ZMod q)⁻¹ * (χ n * c) =
      (∑ χ : DirichletCharacter ℂ q, χ (a : ZMod q)⁻¹ * χ n) * c := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun χ _ => by ring
  rw [e, h]
  have hiff : ((a : ZMod q) = (n : ZMod q)) ↔ (n : ℤ) ≡ a [ZMOD q] := by
    rw [← ZMod.intCast_eq_intCast_iff]
    simp only [Int.cast_natCast]
    exact eq_comm
  by_cases hn : (n : ℤ) ≡ a [ZMOD q]
  · simp only [hn, hiff.mpr hn, ↓reduceIte]
    field_simp
  · have h2 : ¬ ((a : ZMod q) = (n : ZMod q)) := fun h' => hn (hiff.mp h')
    simp only [hn, h2, ↓reduceIte]
    simp

/-- `∑_{n ≤ M, n ≡ a} c_n = (1/φ(q)) ∑_χ χ(a⁻¹) ∑_{n ≤ M} χ(n) c_n`. -/
theorem sum_ap_eq_sum_chars {q : ℕ} [NeZero q] {a : ℤ} (ha : IsUnit (a : ZMod q)) (M : ℕ)
    (c : ℕ → ℂ) :
    ∑ n ∈ (Finset.Icc 1 M).filter (fun n : ℕ => (n : ℤ) ≡ a [ZMOD q]), c n =
      (1 / (Nat.totient q : ℂ)) * ∑ χ : DirichletCharacter ℂ q,
        χ (a : ZMod q)⁻¹ * ∑ n ∈ Finset.Icc 1 M, χ n * c n := by
  rw [Finset.sum_filter]
  simp_rw [orthogonality_term ha]
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [Finset.mul_sum]

/-- The inverse of a unit of `ZMod q` is a unit. -/
theorem isUnit_inv_zmod {q : ℕ} {a : ZMod q} (ha : IsUnit a) : IsUnit a⁻¹ := by
  obtain ⟨u, hu⟩ := ha
  rw [← hu, ZMod.inv_coe_unit]
  exact Units.isUnit _

/-- The error of the progression sum from the errors of the characters (abstract form):
the principal character carries the main term `m`, each of the `φ(q) - 1` others contributes at
most `Nb`, and `1/φ(q) ≤ 1`. -/
theorem ap_error_le {q : ℕ} [NeZero q] {a : ℤ} (ha : IsUnit (a : ZMod q)) (M : ℕ) (c : ℕ → ℂ)
    (P Nb : ℝ) (m : ℂ) (hNb : 0 ≤ Nb)
    (hP : ‖∑ n ∈ Finset.Icc 1 M, (1 : DirichletCharacter ℂ q) n * c n - m‖ ≤ P)
    (hN : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ‖∑ n ∈ Finset.Icc 1 M, χ n * c n‖ ≤ Nb) :
    ‖∑ n ∈ (Finset.Icc 1 M).filter (fun n : ℕ => (n : ℤ) ≡ a [ZMOD q]), c n -
        m / (Nat.totient q : ℂ)‖ ≤ P + Nb := by
  classical
  have hφ1 : (1 : ℝ) ≤ (Nat.totient q : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hφ : (Nat.totient q : ℂ) ≠ 0 := by
    have : (Nat.totient q : ℝ) ≠ 0 := (zero_lt_one.trans_le hφ1).ne'
    exact_mod_cast this
  have hcard : (Finset.univ.erase (1 : DirichletCharacter ℂ q)).card + 1 = Nat.totient q := by
    rw [Finset.card_erase_add_one (Finset.mem_univ _), Finset.card_univ,
      ← Nat.card_eq_fintype_card]
    exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  have hP0 : 0 ≤ P := (norm_nonneg _).trans hP
  rw [sum_ap_eq_sum_chars ha M c,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : DirichletCharacter ℂ q)),
    MulChar.one_apply (isUnit_inv_zmod ha), one_mul]
  have e : 1 / (Nat.totient q : ℂ) * ((∑ n ∈ Finset.Icc 1 M, (1 : DirichletCharacter ℂ q) n * c n) +
      ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
        χ (a : ZMod q)⁻¹ * ∑ n ∈ Finset.Icc 1 M, χ n * c n) - m / (Nat.totient q : ℂ) =
      1 / (Nat.totient q : ℂ) * ((∑ n ∈ Finset.Icc 1 M, (1 : DirichletCharacter ℂ q) n * c n - m) +
      ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
        χ (a : ZMod q)⁻¹ * ∑ n ∈ Finset.Icc 1 M, χ n * c n) := by
    field_simp
    ring
  rw [e, norm_mul, norm_div, norm_one]
  have hn : ‖(Nat.totient q : ℂ)‖ = (Nat.totient q : ℝ) := by simp
  rw [hn]
  have hsum : ‖∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
      χ (a : ZMod q)⁻¹ * ∑ n ∈ Finset.Icc 1 M, χ n * c n‖ ≤
      ((Finset.univ.erase (1 : DirichletCharacter ℂ q)).card : ℝ) * Nb := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          ‖χ (a : ZMod q)⁻¹ * ∑ n ∈ Finset.Icc 1 M, χ n * c n‖
        ≤ ∑ _χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), Nb := by
          refine Finset.sum_le_sum fun χ hχ => ?_
          rw [norm_mul]
          have hχ1 : χ ≠ 1 := Finset.ne_of_mem_erase hχ
          calc ‖χ (a : ZMod q)⁻¹‖ * ‖∑ n ∈ Finset.Icc 1 M, χ n * c n‖
              ≤ 1 * Nb := mul_le_mul (DirichletCharacter.norm_le_one _ _) (hN χ hχ1)
                (norm_nonneg _) zero_le_one
            _ = Nb := one_mul _
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hc' : ((Finset.univ.erase (1 : DirichletCharacter ℂ q)).card : ℝ) + 1 =
      (Nat.totient q : ℝ) := by exact_mod_cast hcard
  have hbd : ‖(∑ n ∈ Finset.Icc 1 M, (1 : DirichletCharacter ℂ q) n * c n - m) +
      ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
        χ (a : ZMod q)⁻¹ * ∑ n ∈ Finset.Icc 1 M, χ n * c n‖ ≤
      P + ((Finset.univ.erase (1 : DirichletCharacter ℂ q)).card : ℝ) * Nb :=
    (norm_add_le _ _).trans (add_le_add hP hsum)
  have hφpos : 0 < (Nat.totient q : ℝ) := zero_lt_one.trans_le hφ1
  rw [one_div, inv_mul_eq_div, div_le_iff₀ hφpos]
  refine hbd.trans ?_
  rw [← hc']
  linarith only [mul_nonneg hP0
    (Nat.cast_nonneg ((Finset.univ.erase (1 : DirichletCharacter ℂ q)).card)), hNb]

/-- **The Riesz mean over a progression**, uniformly for `log q ≤ √(log y)`. -/
theorem riesz_ap_sw (hZ : ClassicalZeroFreeRegion) (hS : NoSiegelZero) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ y₀ : ℝ, 1 ≤ y₀ ∧ ∀ y : ℝ, y₀ ≤ y → ∀ (q : ℕ), 1 ≤ q →
      Real.log q ≤ √(Real.log y) → ∀ (a : ℤ), IsCoprime a (q : ℤ) →
      |∑ n ∈ (Finset.Icc 1 ⌊y⌋₊).filter (fun n : ℕ => (n : ℤ) ≡ a [ZMOD q]), Λ n * (y - n) -
          y ^ 2 / (2 * (Nat.totient q : ℝ))| ≤ 4 * (y ^ 2 * Real.exp (-(c₁ * √(Real.log y)))) := by
  obtain ⟨c₁, hc₁, y₁, hy₁, hn⟩ := riesz_nonprincipal_sw hZ hS
  obtain ⟨c₂, hc₂, y₂, hy₂, hp⟩ := riesz_principal_sw hZ
  set c : ℝ := min c₁ (min c₂ 1) with hc
  have hc0 : 0 < c := lt_min hc₁ (lt_min hc₂ one_pos)
  have hcc₁ : c ≤ c₁ := min_le_left _ _
  have hcc₂ : c ≤ c₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hc1 : c ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨c, hc0, max y₁ (max y₂ (Real.exp 4)), le_trans hy₁ (le_max_left _ _), ?_⟩
  intro y hy q hq hqy a ha
  have hyy₁ : y₁ ≤ y := le_trans (le_max_left _ _) hy
  have hyy₂ : y₂ ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hy
  have hy4 : Real.exp 4 ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hy
  have hy1 : 1 ≤ y := le_trans (Real.one_le_exp (by norm_num)) hy4
  have hy0 : 0 < y := lt_of_lt_of_le one_pos hy1
  have : NeZero q := ⟨by omega⟩
  have hu := isUnit_intCast_of_isCoprime ha
  have hlogy : (4 : ℝ) ≤ Real.log y := by
    have := Real.log_le_log (Real.exp_pos _) hy4
    rwa [Real.log_exp] at this
  set u : ℝ := √(Real.log y) with hu_def
  have hu2 : 2 ≤ u := by
    rw [hu_def]
    exact Real.le_sqrt_of_sq_le ((by norm_num : (2 : ℝ) ^ 2 ≤ 4).trans hlogy)
  have hlog : Real.log y = u ^ 2 := by
    rw [hu_def, Real.sq_sqrt ((by norm_num : (0 : ℝ) ≤ 4).trans hlogy)]
  have hu0 : 0 ≤ u := zero_le_two.trans hu2
  set Y : ℝ := y ^ 2 * Real.exp (-(c * u)) with hY
  have hY1 : y ^ 2 * Real.exp (-(c₁ * u)) ≤ Y := by
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
    exact neg_le_neg (mul_le_mul_of_nonneg_right hcc₁ hu0)
  have hY2 : y ^ 2 * Real.exp (-(c₂ * u)) ≤ Y := by
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
    exact neg_le_neg (mul_le_mul_of_nonneg_right hcc₂ hu0)
  have hY0 : 0 ≤ Y := by positivity
  have hyY : y ≤ Y := by
    have hyexp : y = Real.exp (u ^ 2) := by rw [← hlog, Real.exp_log hy0]
    have h1 : Real.exp (c * u) ≤ y := by
      rw [hyexp]
      refine Real.exp_le_exp.mpr ?_
      calc c * u ≤ 1 * u := mul_le_mul_of_nonneg_right hc1 hu0
        _ = u := one_mul u
        _ ≤ u * u := le_mul_of_one_le_left hu0 (one_le_two.trans hu2)
        _ = u ^ 2 := (sq u).symm
    have h2 : Real.exp (c * u) * Real.exp (-(c * u)) = 1 := by
      rw [← Real.exp_add]; simp
    calc y = y * (Real.exp (c * u) * Real.exp (-(c * u))) := by rw [h2]; ring
      _ = (y * Real.exp (c * u)) * Real.exp (-(c * u)) := by ring
      _ ≤ (y * y) * Real.exp (-(c * u)) := by gcongr
      _ = Y := by rw [hY]; ring
  have hP : ‖∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (1 : DirichletCharacter ℂ q) n *
      ((Λ n : ℂ) * ((y : ℂ) - n)) - ((y ^ 2 / 2 : ℝ) : ℂ)‖ ≤ 3 * Y := by
    have h1 := hp y hyy₂ q hqy
    have e : ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (1 : DirichletCharacter ℂ q) n *
        ((Λ n : ℂ) * ((y : ℂ) - n)) - ((y ^ 2 / 2 : ℝ) : ℂ) =
        (∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (1 : DirichletCharacter ℂ q) n * (Λ n : ℂ) * ((y : ℂ) - n) -
          (((y - 1) ^ 2 / 2 : ℝ) : ℂ)) + ((((y - 1) ^ 2 / 2 - y ^ 2 / 2 : ℝ)) : ℂ) := by
      push_cast
      simp_rw [mul_assoc]
      ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have h3 : ‖((((y - 1) ^ 2 / 2 - y ^ 2 / 2 : ℝ)) : ℂ)‖ ≤ y := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith only [hy1]
    linarith only [h1, h3, hY2, hyY]
  have hN : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ‖∑ n ∈ Finset.Icc 1 ⌊y⌋₊, χ n * ((Λ n : ℂ) * ((y : ℂ) - n))‖ ≤ Y := by
    intro χ hχ
    have := hn y hyy₁ q hqy χ hχ
    simp_rw [← mul_assoc]
    exact this.trans hY1
  have hmain := ap_error_le hu ⌊y⌋₊ (fun n => (Λ n : ℂ) * ((y : ℂ) - n)) (3 * Y) Y
    ((y ^ 2 / 2 : ℝ) : ℂ) hY0 hP hN
  have hcast : ∑ n ∈ (Finset.Icc 1 ⌊y⌋₊).filter (fun n : ℕ => (n : ℤ) ≡ a [ZMOD q]),
      (Λ n : ℂ) * ((y : ℂ) - n) - ((y ^ 2 / 2 : ℝ) : ℂ) / (Nat.totient q : ℂ) =
      ((∑ n ∈ (Finset.Icc 1 ⌊y⌋₊).filter (fun n : ℕ => (n : ℤ) ≡ a [ZMOD q]), Λ n * (y - n) -
          y ^ 2 / (2 * (Nat.totient q : ℝ)) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hcast, Complex.norm_real, Real.norm_eq_abs] at hmain
  linarith

end PrimeCarleson.Proof.Fplus31.PNTSW
