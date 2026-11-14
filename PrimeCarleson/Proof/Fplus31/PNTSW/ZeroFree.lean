module

public import PrimeCarleson.Proof.Fplus31.PNTSW.Inputs
public import PrimeCarleson.Proof.Fplus31.PNTSW.Bounds
public import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# The zero-free region for every nonprincipal character and for `L₁ = (s-1) ζ`

Part of the prime number theorem in progressions on the classical zero-free region
(`PNTSW/Main.lean`). From `ClassicalZeroFreeRegion` (primitive characters, exceptional real zero
allowed) and `NoSiegelZero` (no exceptional zero below `1 - c / log q`):

* `zeroFree_nonprincipal`: there is `c ∈ (0, 1/2]` such that `L(s, χ) ≠ 0` for every nonprincipal
  character `χ` modulo every `q` and every `s` with `re s ≥ 1 - c / log (q (|im s| + 3))` (the
  imprimitive case is reduced to the primitive one with
  `DirichletCharacter.LFunction_changeLevel`);
* `zeroFree_zetaL1`: the same for `L₁ = (s-1) ζ(s)` with `q = 1`.
-/

@[expose] public noncomputable section

open Complex

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31.PNTSW

/-- **The zero-free region for every nonprincipal character**, from `ClassicalZeroFreeRegion` and
`NoSiegelZero`. -/
theorem zeroFree_nonprincipal (hZ : ClassicalZeroFreeRegion) (hS : NoSiegelZero) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 / 2 ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ s : ℂ, 1 - c / Real.log (q * (|s.im| + 3)) ≤ s.re → χ.LFunction s ≠ 0 := by
  obtain ⟨cZ, hcZ, hZ'⟩ := hZ
  obtain ⟨cS, hcS, hS'⟩ := hS
  set c : ℝ := min cZ (min (cS / 2) (1 / 2)) with hc
  have hc0 : 0 < c := lt_min hcZ (lt_min (by positivity) (by norm_num))
  have hcZ' : c ≤ cZ := min_le_left _ _
  have hcS' : c ≤ cS / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hc2 : c ≤ 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨c, hc0, hc2, ?_⟩
  intro q _ χ hχ s hs hzero
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hH := log_mul_abs_add_three_gt_one hq1 s.im
  set Hq : ℝ := Real.log (q * (|s.im| + 3)) with hHq
  have hHpos : 0 < Hq := by linarith
  have hre : 1 / 2 ≤ s.re := by
    have : c / Hq ≤ 1 / 2 := by
      rw [div_le_iff₀ hHpos]; nlinarith
    linarith
  have hre0 : 0 < s.re := by linarith
  -- the primitive character inducing `χ`
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  set m : ℕ := χ.conductor with hm
  set χ' : DirichletCharacter ℂ m := χ.primitiveCharacter with hχ'
  have hprim : χ'.IsPrimitive := χ.primitiveCharacter_isPrimitive
  have hchange : DirichletCharacter.changeLevel χ.conductor_dvd_level χ' = χ :=
    χ.changeLevel_primitiveCharacter
  have hχ'1 : χ' ≠ 1 := by
    intro h
    apply hχ
    rw [← hchange, h, DirichletCharacter.changeLevel_one]
  have hmq : m ≤ q := Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)
  -- zeros of `L(s, χ)` are zeros of `L(s, χ')`
  have hzero' : χ'.LFunction s = 0 := by
    have h := DirichletCharacter.LFunction_changeLevel χ.conductor_dvd_level χ' (s := s)
      (Or.inl hχ'1)
    rw [hchange] at h
    rw [h] at hzero
    rcases mul_eq_zero.mp hzero with h1 | h1
    · exact h1
    · exfalso
      obtain ⟨p, hp, hp0⟩ := Finset.prod_eq_zero_iff.mp h1
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hpR : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
      have hpow : ‖(p : ℂ) ^ (-s)‖ < 1 := by
        rw [Complex.norm_natCast_cpow_of_pos hpp.pos, Complex.neg_re]
        calc (p : ℝ) ^ (-s.re) < (p : ℝ) ^ (0 : ℝ) :=
              Real.rpow_lt_rpow_of_exponent_lt hpR (by linarith)
          _ = 1 := Real.rpow_zero _
      have hu : ‖χ' p * (p : ℂ) ^ (-s)‖ < 1 := by
        rw [norm_mul]
        exact (mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one χ' _)
          (norm_nonneg _)).trans_lt (by simpa using hpow)
      have he : χ' p * (p : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp hp0).symm
      rw [he, norm_one] at hu
      exact lt_irrefl 1 hu
  -- the region for `χ'`
  have hsne : s ≠ 1 ∨ χ' ≠ 1 := Or.inr hχ'1
  have hlogm : Real.log m ≤ Real.log q := Real.log_le_log (by exact_mod_cast hm1)
    (by exact_mod_cast hmq)
  have hlogmt : Real.log (m * (|s.im| + 3)) ≤ Hq := by
    rw [hHq]
    exact Real.log_le_log (by positivity) (by
      have := abs_nonneg s.im
      have h' : (m : ℝ) ≤ q := by exact_mod_cast hmq
      nlinarith)
  have hHm := log_mul_abs_add_three_gt_one hm1 s.im
  have hregion : 1 - cZ / Real.log (m * (|s.im| + 3)) ≤ s.re := by
    have h1 : c / Hq ≤ cZ / Real.log (m * (|s.im| + 3)) := by
      calc c / Hq ≤ cZ / Hq := div_le_div_of_nonneg_right hcZ' hHpos.le
        _ ≤ cZ / Real.log (m * (|s.im| + 3)) :=
            div_le_div_of_nonneg_left hcZ.le (by linarith) hlogmt
    linarith
  have hs1' : s ≠ 1 := by
    intro h
    rw [h] at hzero'
    exact DirichletCharacter.LFunction_apply_one_ne_zero hχ'1 hzero'
  obtain ⟨hm3, hreal, him⟩ := hZ' m χ' hprim s hs1' hregion hzero'
  -- the exceptional zero is excluded by `NoSiegelZero`
  have hsreal : s = (s.re : ℂ) := by
    apply Complex.ext <;> simp [him]
  have hlt1 : s.re < 1 := by
    by_contra hge
    push Not at hge
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ' (Or.inl hχ'1) hge hzero'
  have hzeroR : χ'.LFunction (s.re : ℂ) = 0 := by rw [← hsreal]; exact hzero'
  have hgap := hS' m hm3 χ' hprim hχ'1 hreal s.re hre0 hlt1 hzeroR
  have hupper : (1 - s.re) * Real.log m ≤ c := by
    have h1 : 1 - s.re ≤ c / Hq := by linarith
    have hm0 : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm1)
    calc (1 - s.re) * Real.log m ≤ c / Hq * Hq := by
          refine mul_le_mul h1 ?_ hm0 (by positivity)
          refine hlogm.trans ?_
          rw [hHq]
          refine Real.log_le_log (by positivity) ?_
          have := abs_nonneg s.im
          nlinarith
      _ = c := by field_simp
  linarith

/-- The zero-free region of `L₁ = (s-1) ζ(s)`. -/
theorem zeroFree_zetaL1 (hZ : ClassicalZeroFreeRegion) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 / 2 ∧ ∀ s : ℂ, 1 - c / Real.log (|s.im| + 3) ≤ s.re → zetaL1 s ≠ 0 := by
  obtain ⟨cZ, hcZ, hZ'⟩ := hZ
  refine ⟨min cZ (1 / 2), lt_min hcZ (by norm_num), min_le_right _ _, ?_⟩
  intro s hs
  by_cases h1 : s = 1
  · rw [h1]
    exact DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero 1
  · rw [zetaL1_apply h1]
    refine mul_ne_zero (sub_ne_zero.mpr h1) fun hz => ?_
    have hprim : (1 : DirichletCharacter ℂ 1).IsPrimitive :=
      DirichletCharacter.isPrimitive_one_level_one
    have hz' : (1 : DirichletCharacter ℂ 1).LFunction s = 0 := by
      rw [DirichletCharacter.LFunction_modOne_eq]; exact hz
    have hH := log_mul_abs_add_three_gt_one (le_refl 1) s.im
    have hreg : 1 - cZ / Real.log (((1 : ℕ) : ℝ) * (|s.im| + 3)) ≤ s.re := by
      have h2 : min cZ (1 / 2) / Real.log (|s.im| + 3) ≤ cZ / Real.log (|s.im| + 3) := by
        refine div_le_div_of_nonneg_right (min_le_left _ _) ?_
        simpa using (by linarith : (0 : ℝ) ≤ Real.log (((1 : ℕ) : ℝ) * (|s.im| + 3)))
      simp only [Nat.cast_one, one_mul]
      linarith
    obtain ⟨h3, _, _⟩ := hZ' 1 1 hprim s h1 hreg hz'
    omega

end PrimeCarleson.Proof.Fplus31.PNTSW
