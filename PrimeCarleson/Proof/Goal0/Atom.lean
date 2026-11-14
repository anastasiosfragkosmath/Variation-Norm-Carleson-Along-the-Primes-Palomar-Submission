module

public import PrimeCarleson.Proof.Goal0.Basic

/-!
# Structured atoms

The structured atoms of `sources/Variational_Carleson.tex` (Source: main paper `s:per`,
L2395–L2402): for a divisor `d` of `N` and `D = N / d`, writing `x = a + d s` with
`a = x mod d` and `s = x div d`,
`Φ(a + d s) = h(a) e(ϑ(a) s / D)`.
The paper normalises `𝔼_{a ∈ [d]} |h(a)|² = 1`; the proof formalized here keeps `h` arbitrary and
normalises the `ℓ²` norm over one period instead.
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PrimeCarleson.Proof.Goal0

/-- The structured atom `Φ(a + d s) = h(a) e(ϑ(a) s / D)`, `D = N / d`, `a = x mod d`,
`s = x div d` (L2395–L2402). -/
def atom (N d : ℕ) (h : ℤ → ℂ) (ϑ : ℤ → ℤ) (x : ℤ) : ℂ :=
  h (x % d) * e ((ϑ (x % d) : ℝ) * ((x / d : ℤ) : ℝ) / ((N / d : ℕ) : ℝ))

theorem norm_atom (N d : ℕ) (h : ℤ → ℂ) (ϑ : ℤ → ℤ) (x : ℤ) :
    ‖atom N d h ϑ x‖ = ‖h (x % d)‖ := by
  rw [atom, norm_mul, norm_e, mul_one]

/-- `Φ(a + d s) = h(a) e(ϑ(a) s / D)` for `0 ≤ a < d`. -/
theorem atom_add_mul {N d : ℕ} (hd : 0 < d) (h : ℤ → ℂ) (ϑ : ℤ → ℤ) {a : ℤ} (ha0 : 0 ≤ a)
    (had : a < d) (s : ℤ) :
    atom N d h ϑ (a + d * s) = h a * e ((ϑ a : ℝ) * (s : ℝ) / ((N / d : ℕ) : ℝ)) := by
  have hd' : (d : ℤ) ≠ 0 := by exact_mod_cast hd.ne'
  have hmod : (a + d * s) % (d : ℤ) = a := by
    rw [Int.add_mul_emod_self_left, Int.emod_eq_of_lt ha0 had]
  have hdiv : (a + d * s) / (d : ℤ) = s := by
    rw [Int.add_mul_ediv_left _ _ hd', Int.ediv_eq_zero_of_lt ha0 had, zero_add]
  rw [atom, hmod, hdiv]

/-- Atoms are `N`-periodic. -/
theorem atom_periodic {N d : ℕ} (hdN : d ∣ N) (h : ℤ → ℂ) (ϑ : ℤ → ℤ) :
    Function.Periodic (atom N d h ϑ) N := by
  intro x
  rcases Nat.eq_zero_or_pos N with hN | hN
  · simp [hN]
  obtain ⟨D, rfl⟩ := hdN
  have hd : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hN)
  have hD : 0 < D := Nat.pos_of_ne_zero (by rintro rfl; simp at hN)
  have hd' : (d : ℤ) ≠ 0 := by exact_mod_cast hd.ne'
  have hND : d * D / d = D := Nat.mul_div_cancel_left D hd
  have hmod : (x + ((d * D : ℕ) : ℤ)) % (d : ℤ) = x % d := by
    push_cast; exact Int.add_mul_emod_self_left x d D
  have hdiv : (x + ((d * D : ℕ) : ℤ)) / (d : ℤ) = x / d + D := by
    push_cast; exact Int.add_mul_ediv_left x D hd'
  rw [atom, atom, hmod, hdiv, hND]
  congr 1
  have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  rw [show (ϑ (x % d) : ℝ) * (((x / d + D : ℤ)) : ℝ) / (D : ℝ) =
      (ϑ (x % d) : ℝ) * ((x / d : ℤ) : ℝ) / (D : ℝ) + ((ϑ (x % d) : ℤ) : ℝ) by
    push_cast; field_simp]
  exact e_add_intCast _ _

end PrimeCarleson.Proof.Goal0
