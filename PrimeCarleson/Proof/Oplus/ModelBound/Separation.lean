module

public import PrimeCarleson.Proof.Oplus.Conclusion.Main

/-!
# The separation reduction ([O+] L1265-L1282)

Source: [O+] `halfgbound`, L1265–L1282: "We split our
finite collection of multitiles into a bounded number of subcollections satisfying certain
separation conditions" (L1265-L1270), the conditions
being
(separationofscales) `|ω_u'| < |ω_u| → |ω_u'| ≤ ((C₂ - C₃)/(2C₁)) |ω_u|` and (separationprop2)
`C₁ω_u ∩ C₁ω_u' ≠ ∅, |ω_u| = |ω_u'| → ω_u = ω_u'` (`Separated`, `Defs/Tree.lean`).

The source gives no construction. Here it is, for arbitrary constants `C₁ > 0`, `C₃ < C₂`:
colour a `ρ`-multitile `P` by `(k mod s, m mod t)` where `ω_u = [2^k m, 2^k (m+1))`, `s` is the
least integer with `2^{-s} ≤ (C₂ - C₃)/(2C₁)` and `t = ⌈C₁⌉`. Two multitiles of the same colour
whose frequency intervals have different lengths have scales at least `s` apart, hence the ratio
of lengths is at most `2^{-s}`; with equal lengths, `C₁ω_u ∩ C₁ω_u' ≠ ∅` forces
`|m - m'| < C₁ ≤ t`, hence `m = m'` (the dilates are half-open, as in `Dyadic.dilate`). The number
of colours is `N = s t` (`60 = 5 · 12` for `C₁ = 12`, `C₂ = 2`, `C₃ = 11/10`, where
`(C₂-C₃)/(2C₁) = 3/80 ≥ 2^{-5} > 2^{-4}`), independent of `ρ`, and the colouring is a function of
`P` alone, not of the finite family.

* `exists_separated_colouring_of`: the colouring with explicit `s, t`;
* `exists_separated_colouring`: arbitrary constants.
-/

@[expose] public noncomputable section

open MeasureTheory Set

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

/-- Two integers congruent modulo `t ≥ C₁` whose difference is `< C₁` in absolute value are
equal. -/
theorem eq_of_dvd_of_abs_lt {t : ℕ} {C₁ : ℝ} (hC₁t : C₁ ≤ t) {a b : ℤ} (hd : (t : ℤ) ∣ b - a)
    (h1 : ((b - a : ℤ) : ℝ) < C₁) (h2 : ((a - b : ℤ) : ℝ) < C₁) : a = b := by
  by_contra hne
  have hne' : b - a ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
  have hle : (t : ℤ) ≤ |b - a| := Int.le_of_dvd (abs_pos.2 hne') ((dvd_abs _ _).2 hd)
  have hle' : (t : ℝ) ≤ ((|b - a| : ℤ) : ℝ) := by exact_mod_cast hle
  have : ((|b - a| : ℤ) : ℝ) < C₁ := by
    rw [Int.cast_abs]
    exact abs_lt.2 ⟨by push_cast at h2 ⊢; linarith, h1⟩
  linarith

/-- **The colouring with explicit parameters** (combinatorial part of the separation reduction,
[O+] L1265-L1282): colour a `ρ`-multitile `P` by `(k mod s, m mod t)`, where
`ω_u = [2^k m, 2^k (m+1))`. If `(1/2)^s ≤ (C₂ - C₃)/(2 C₁)` and `C₁ ≤ t`, every colour class
satisfies (separationofscales) and (separationprop2). The colour set is `Fin (s * t)`. -/
theorem exists_separated_colouring_of {C₁ C₂ C₃ : ℝ} {s t : ℕ} (hs0 : 0 < s) (ht0 : 0 < t)
    (hsc : (1 / 2 : ℝ) ^ s ≤ (C₂ - C₃) / (2 * C₁)) (hCt : C₁ ≤ t) (ρ : Idx) :
    ∃ col : Multitile ρ → Fin (s * t), ∀ c : Fin (s * t), Separated C₁ C₂ C₃ {P | col P = c} := by
  have : NeZero s := ⟨hs0.ne'⟩
  have : NeZero t := ⟨ht0.ne'⟩
  set e : ZMod s × ZMod t ≃ Fin (s * t) :=
    Fintype.equivFinOfCardEq (by simp [ZMod.card]) with he
  refine ⟨fun P => e (((P.ωu.k : ℤ) : ZMod s), ((P.ωu.m : ℤ) : ZMod t)), fun c => ?_⟩
  have hcol : ∀ P Q : Multitile ρ, e (((P.ωu.k : ℤ) : ZMod s), ((P.ωu.m : ℤ) : ZMod t)) =
      e (((Q.ωu.k : ℤ) : ZMod s), ((Q.ωu.m : ℤ) : ZMod t)) →
      (s : ℤ) ∣ Q.ωu.k - P.ωu.k ∧ (t : ℤ) ∣ Q.ωu.m - P.ωu.m := by
    intro P Q h
    have h' := e.injective h
    rw [Prod.mk.injEq] at h'
    exact ⟨(ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h'.1,
      (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h'.2⟩
  refine ⟨?_, ?_⟩
  · intro P hP Q hQ hlt
    have hPQ := hcol P Q (hP.trans hQ.symm)
    have hk : Q.ωu.k < P.ωu.k :=
      (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 hlt
    obtain ⟨d, hd⟩ := hPQ.1
    have hd0 : d < 0 := by
      by_contra hd0
      push Not at hd0
      have : (0 : ℤ) ≤ s * d := mul_nonneg (by positivity) hd0
      omega
    have hks : Q.ωu.k - P.ωu.k ≤ -(s : ℤ) := by
      have : (s : ℤ) * d ≤ (s : ℤ) * (-1) := mul_le_mul_of_nonneg_left (by omega) (by positivity)
      omega
    have hpow : (2 : ℝ) ^ (Q.ωu.k - P.ωu.k) ≤ (1 / 2 : ℝ) ^ s := by
      calc (2 : ℝ) ^ (Q.ωu.k - P.ωu.k) ≤ (2 : ℝ) ^ (-(s : ℤ)) :=
            zpow_le_zpow_right₀ (by norm_num) hks
        _ = (1 / 2 : ℝ) ^ s := by rw [zpow_neg, zpow_natCast, one_div, inv_pow]
    have hlen : Q.ωu.length = P.ωu.length * (2 : ℝ) ^ (Q.ωu.k - P.ωu.k) := by
      unfold Dyadic.length
      rw [← zpow_add₀ (by norm_num)]
      congr 1; ring
    rw [hlen]
    have hL := P.ωu.length_pos
    calc P.ωu.length * (2 : ℝ) ^ (Q.ωu.k - P.ωu.k) ≤ P.ωu.length * (1 / 2 : ℝ) ^ s :=
          mul_le_mul_of_nonneg_left hpow hL.le
      _ ≤ P.ωu.length * ((C₂ - C₃) / (2 * C₁)) := mul_le_mul_of_nonneg_left hsc hL.le
      _ = (C₂ - C₃) / (2 * C₁) * P.ωu.length := by ring
  · intro P hP Q hQ hint hlen
    have hPQ := hcol P Q (hP.trans hQ.symm)
    have hk : P.ωu.k = Q.ωu.k :=
      (zpow_right_injective₀ (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)) hlen
    obtain ⟨x, hx1, hx2⟩ := hint
    have hL : 0 < P.ωu.length := P.ωu.length_pos
    have hLQ : Q.ωu.length = P.ωu.length := hlen.symm
    simp only [Multitile.ωuDil, Dyadic.dilate, Set.mem_Ico, Dyadic.center, Dyadic.length] at hx1 hx2
    rw [← hk] at hx2
    have hPm : (P.ωu.m : ℝ) - Q.ωu.m < C₁ := by
      have : (2 : ℝ) ^ P.ωu.k * ((P.ωu.m : ℝ) - Q.ωu.m) < (2 : ℝ) ^ P.ωu.k * C₁ := by
        nlinarith [hx1.1, hx2.2]
      exact lt_of_mul_lt_mul_left this (zpow_pos (by norm_num) _).le
    have hQm : (Q.ωu.m : ℝ) - P.ωu.m < C₁ := by
      have : (2 : ℝ) ^ P.ωu.k * ((Q.ωu.m : ℝ) - P.ωu.m) < (2 : ℝ) ^ P.ωu.k * C₁ := by
        nlinarith [hx1.2, hx2.1]
      exact lt_of_mul_lt_mul_left this (zpow_pos (by norm_num) _).le
    have hm := eq_of_dvd_of_abs_lt hCt hPQ.2 (by exact_mod_cast hQm) (by exact_mod_cast hPm)
    exact Dyadic.ext hk hm

/-- **The separation reduction, combinatorial part** ([O+] L1265-L1282), for
arbitrary constants `C₁ > 0`, `C₃ < C₂`: there are `s, t` with `(1/2)^s ≤ (C₂ - C₃)/(2 C₁)`,
`C₁ ≤ t` (one may take `s` least and `t = ⌈C₁⌉`), and for every index `ρ` a colouring
`col : Multitile ρ → Fin (s * t)` of all `ρ`-multitiles, depending only on `C₁, C₂, C₃` and not
on any family, each of whose colour classes is separated. Every finite family `𝔓` is thus the
disjoint union of the `s t` separated subfamilies `𝔓 ∩ {col = c}`. -/
theorem exists_separated_colouring {C₁ C₂ C₃ : ℝ} (hC₁ : 0 < C₁) (hC : C₃ < C₂) :
    ∃ s t : ℕ, 0 < s ∧ 0 < t ∧ ∀ ρ : Idx, ∃ col : Multitile ρ → Fin (s * t),
      ∀ c : Fin (s * t), Separated C₁ C₂ C₃ {P | col P = c} := by
  have hc : 0 < (C₂ - C₃) / (2 * C₁) := div_pos (by linarith) (by linarith)
  obtain ⟨s₀, hs₀⟩ := exists_pow_lt_of_lt_one hc (by norm_num : (1 / 2 : ℝ) < 1)
  have hsc : (1 / 2 : ℝ) ^ (s₀ + 1) ≤ (C₂ - C₃) / (2 * C₁) := by
    refine le_trans ?_ hs₀.le
    rw [pow_succ]
    have : (0 : ℝ) ≤ (1 / 2) ^ s₀ := by positivity
    nlinarith
  exact ⟨s₀ + 1, ⌈C₁⌉₊, Nat.succ_pos _, Nat.ceil_pos.2 hC₁, fun ρ =>
    exists_separated_colouring_of (Nat.succ_pos _) (Nat.ceil_pos.2 hC₁) hsc (Nat.le_ceil C₁) ρ⟩

end PrimeCarleson.Proof.Oplus
