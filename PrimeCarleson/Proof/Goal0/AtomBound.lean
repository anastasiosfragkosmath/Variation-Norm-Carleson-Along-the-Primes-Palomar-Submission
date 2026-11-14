module

public import PrimeCarleson.Proof.Goal0.Atom
public import PrimeCarleson.Proof.Goal0.Operators
public import PrimeCarleson.Proof.Goal0.Fiber

/-!
# The bound for `M_B` on a structured atom

Proposition `p:structuredatom` of `sources/Variational_Carleson.tex` (L2747-L2801), Source: main
paper `p:structuredatom`, L2747–L2754, for Proposition `p:goal0`. For `N = lcm B`, `d ∣ N` with
`(d, N / d) = 1`, and
a structured atom `Φ(a + d s) = h(a) e(ϑ(a) s / D)`, `D = N / d`:

* `norm_avg_atom_le`: splitting `x - r = a_u + d (s_u - ℓ)` with `r = u + d ℓ` and applying the
  fibre envelope `norm_avg_blockWeight_le_card`, the weighted average satisfies
  `|𝔼_{r < N} Φ(x - r) w_B(r) e(r θ / N)| ≤ d⁻¹ ∑_{u < d} G(u) |Φ(x - u)|` with
  `G(u) = τ(d) M ∑_{r ∣ d} |c_r(u)|`;
* `l2_periodicBlockMax_atom_le`: Minkowski's inequality in place of Young's inequality, the
  translation invariance of `‖Φ‖₂` over one period, and `sum_norm_ramanujanSum_le` give
  `‖M_B Φ‖₂ ≤ τ(d) M (∑_{r ∣ d} τ(r)) ‖Φ‖₂`.
-/

@[expose] public noncomputable section

open Finset

set_option autoImplicit false

namespace PrimeCarleson.Proof.Goal0

/-- The `u`-th term of the fibre decomposition of the weighted average of a structured atom:
with `x - u = a + d s`, `a = (x - u) mod d`, `s = (x - u) div d`, `r = u + d ℓ`,
`Φ(x - r) w_B(r) e(r θ / N) = h(a) e(ϑ(a) s / D) e(u θ / N) · w_B(u + d ℓ) e(ℓ (θ - ϑ(a)) / D)`. -/
theorem atom_mul_blockWeight_mul_e_eq {N d D : ℕ} (hd : 0 < d) (hD : 0 < D) (hN : N = d * D)
    (B : Finset ℕ) (h : ℤ → ℂ) (ϑ : ℤ → ℤ) (x θ : ℤ) (u ℓ : ℕ) :
    atom N d h ϑ (x - ((u + d * ℓ : ℕ) : ℤ)) * blockWeight B ((u + d * ℓ : ℕ) : ℤ) *
        e (((u + d * ℓ : ℕ) : ℝ) * (θ : ℝ) / (N : ℝ)) =
      h ((x - u) % d) * e ((ϑ ((x - u) % d) : ℝ) * (((x - u) / d : ℤ) : ℝ) / (D : ℝ)) *
        e ((u : ℝ) * (θ : ℝ) / (N : ℝ)) *
        (blockWeight B ((u : ℤ) + d * ℓ) *
          e ((ℓ : ℝ) * ((θ - ϑ ((x - u) % d) : ℤ) : ℝ) / (D : ℝ))) := by
  subst hN
  have hd' : (d : ℤ) ≠ 0 := by exact_mod_cast hd.ne'
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hDR : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  set a : ℤ := (x - u) % d with ha
  set s : ℤ := (x - u) / d with hs
  have ha0 : 0 ≤ a := Int.emod_nonneg _ hd'
  have had : a < d := Int.emod_lt_of_pos _ (by exact_mod_cast hd)
  have hax : a + d * s = x - u := Int.emod_add_mul_ediv (x - u) d
  have hx : x - ((u + d * ℓ : ℕ) : ℤ) = a + d * (s - ℓ) := by
    push_cast
    linarith
  rw [hx, atom_add_mul hd h ϑ ha0 had, Nat.mul_div_cancel_left D hd]
  have e1 : e ((ϑ a : ℝ) * ((s - ℓ : ℤ) : ℝ) / (D : ℝ)) =
      e ((ϑ a : ℝ) * (s : ℝ) / (D : ℝ)) * e (-((ℓ : ℝ) * (ϑ a : ℝ) / (D : ℝ))) := by
    rw [← e_add]
    congr 1
    push_cast
    ring
  have e2 : e (((u + d * ℓ : ℕ) : ℝ) * (θ : ℝ) / ((d * D : ℕ) : ℝ)) =
      e ((u : ℝ) * (θ : ℝ) / ((d * D : ℕ) : ℝ)) * e ((ℓ : ℝ) * (θ : ℝ) / (D : ℝ)) := by
    rw [← e_add]
    congr 1
    push_cast
    field_simp
  have e3 : e ((ℓ : ℝ) * ((θ - ϑ a : ℤ) : ℝ) / (D : ℝ)) =
      e ((ℓ : ℝ) * (θ : ℝ) / (D : ℝ)) * e (-((ℓ : ℝ) * (ϑ a : ℝ) / (D : ℝ))) := by
    rw [← e_add]
    congr 1
    push_cast
    ring
  rw [e1, e2, e3]
  push_cast
  ring

/-- The pointwise bound for the weighted average of a structured atom
(`sources/Variational_Carleson.tex` L2764–L2786):
`|𝔼_{r < N} Φ(x - r) w_B(r) e(r θ / N)| ≤ d⁻¹ ∑_{u < d} G(u) |Φ(x - u)|`,
`G(u) = τ(d) M ∑_{r ∣ d} |c_r(u)|`. -/
theorem norm_avg_atom_le {B : Finset ℕ} {N d D : ℕ} (hd : 0 < d) (hD : 0 < D) (hN : N = d * D)
    (hdD : d.Coprime D) (hB : ∀ q ∈ B, q ∣ N) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ q ∈ B, ((q.totient : ℝ))⁻¹ ≤ M) (h : ℤ → ℂ) (ϑ : ℤ → ℤ) (x θ : ℤ) :
    ‖(N : ℂ)⁻¹ * ∑ r ∈ range N, atom N d h ϑ (x - (r : ℤ)) * blockWeight B (r : ℤ) *
        e ((r : ℝ) * (θ : ℝ) / (N : ℝ))‖ ≤
      (d : ℝ)⁻¹ * ∑ u ∈ range d,
        (d.divisors.card * M * ∑ r ∈ d.divisors, ‖ramanujanSum r (u : ℤ)‖) *
          ‖atom N d h ϑ (x - (u : ℤ))‖ := by
  have hdR : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hDR : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  have hB' : ∀ q ∈ B, q ∣ d * D := hN ▸ hB
  subst hN
  rw [sum_range_mul_eq d D (fun r => atom (d * D) d h ϑ (x - (r : ℤ)) * blockWeight B (r : ℤ) *
    e ((r : ℝ) * (θ : ℝ) / ((d * D : ℕ) : ℝ)))]
  set c : ℕ → ℂ := fun u => h ((x - u) % d) *
    e ((ϑ ((x - u) % d) : ℝ) * (((x - u) / d : ℤ) : ℝ) / (D : ℝ)) *
      e ((u : ℝ) * (θ : ℝ) / ((d * D : ℕ) : ℝ)) with hc
  set K : ℕ → ℂ := fun u => (D : ℂ)⁻¹ * ∑ ℓ ∈ range D, blockWeight B ((u : ℤ) + d * ℓ) *
    e ((ℓ : ℝ) * ((θ - ϑ ((x - u) % d) : ℤ) : ℝ) / (D : ℝ)) with hK
  have hsum : ∀ u ∈ range d,
      ∑ ℓ ∈ range D, atom (d * D) d h ϑ (x - ((u + d * ℓ : ℕ) : ℤ)) *
          blockWeight B ((u + d * ℓ : ℕ) : ℤ) *
          e (((u + d * ℓ : ℕ) : ℝ) * (θ : ℝ) / ((d * D : ℕ) : ℝ)) = c u * ((D : ℂ) * K u) := by
    intro u _
    simp_rw [atom_mul_blockWeight_mul_e_eq hd hD rfl B h ϑ x θ u]
    rw [hK]
    simp only
    rw [← mul_assoc (D : ℂ), mul_inv_cancel₀ hDR, one_mul, ← mul_sum]
  rw [sum_congr rfl hsum]
  have hrw : ((d * D : ℕ) : ℂ)⁻¹ * ∑ u ∈ range d, c u * ((D : ℂ) * K u) =
      (d : ℂ)⁻¹ * ∑ u ∈ range d, c u * K u := by
    push_cast
    rw [mul_sum, mul_sum]
    refine sum_congr rfl fun u _ => ?_
    field_simp
  rw [hrw, norm_mul, norm_inv, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (Nat.cast_nonneg _))
  refine (norm_sum_le _ _).trans (sum_le_sum fun u hu => ?_)
  rw [mem_range] at hu
  rw [norm_mul, mul_comm, norm_atom]
  have hcn : ‖c u‖ = ‖h ((x - u) % d)‖ := by
    simp only [hc, norm_mul, norm_e, mul_one]
  rw [hcn]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  have hK' := norm_avg_blockWeight_le_card hd hD hdD hB' hM0 hM (θ - ϑ ((x - u) % d)) u
  exact hK'

/-- The averaged envelope: `d⁻¹ ∑_{u < d} G(u) ≤ τ(d) M ∑_{r ∣ d} τ(r)`
(from `sum_norm_ramanujanSum_le`). -/
theorem inv_mul_sum_envelope_le {d : ℕ} (hd : 0 < d) {M : ℝ} (hM0 : 0 ≤ M) :
    (d : ℝ)⁻¹ * ∑ u ∈ range d,
        (d.divisors.card * M * ∑ r ∈ d.divisors, ‖ramanujanSum r (u : ℤ)‖) ≤
      d.divisors.card * M * ∑ r ∈ d.divisors, (r.divisors.card : ℝ) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hc : 0 ≤ (d.divisors.card : ℝ) * M := mul_nonneg (Nat.cast_nonneg _) hM0
  rw [← Finset.mul_sum, Finset.sum_comm]
  have h1 : ∑ r ∈ d.divisors, ∑ u ∈ range d, ‖ramanujanSum r (u : ℤ)‖ ≤
      ∑ r ∈ d.divisors, (d : ℝ) * r.divisors.card :=
    sum_le_sum fun r hr => sum_norm_ramanujanSum_le hd (Nat.dvd_of_mem_divisors hr)
  rw [← Finset.mul_sum] at h1
  calc (d : ℝ)⁻¹ * ((d.divisors.card : ℝ) * M * ∑ r ∈ d.divisors, ∑ u ∈ range d,
          ‖ramanujanSum r (u : ℤ)‖)
      ≤ (d : ℝ)⁻¹ * ((d.divisors.card : ℝ) * M * ((d : ℝ) *
          ∑ r ∈ d.divisors, (r.divisors.card : ℝ))) := by
        gcongr
    _ = d.divisors.card * M * ∑ r ∈ d.divisors, (r.divisors.card : ℝ) := by
        field_simp

/-- Translating `‖Φ‖` does not change its `ℓ²` norm over one period. -/
theorem l2_norm_atom_sub {N d : ℕ} (hdN : d ∣ N) (h : ℤ → ℂ) (ϑ : ℤ → ℤ) (u : ℕ) :
    l2 N (fun x => ‖atom N d h ϑ (x - (u : ℤ))‖) = l2 N (fun x => ‖atom N d h ϑ x‖) := by
  unfold l2
  congr 1
  have hper : Function.Periodic (fun x : ℤ => ‖atom N d h ϑ x‖ ^ 2) (N : ℤ) := by
    intro x
    simp only
    rw [atom_periodic hdN h ϑ x]
  have := sum_range_add_of_periodic hper (-(u : ℤ))
  simpa only [sub_eq_add_neg] using this

/-- `M_B` on a structured atom (Proposition p:structuredatom): with `1/φ(q) ≤ M` on `B`,
`‖M_B Φ‖ ≤ τ(d) M (∑_{r ∣ d} τ(r)) ‖Φ‖`. -/
theorem l2_periodicBlockMax_atom_le {B : Finset ℕ} (hB : ∀ q ∈ B, 0 < q) {d : ℕ} (hd : 0 < d)
    (hdN : d ∣ B.lcm id) (hcop : d.Coprime (B.lcm id / d)) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ q ∈ B, ((q.totient : ℝ))⁻¹ ≤ M) (h : ℤ → ℂ) (ϑ : ℤ → ℤ) :
    l2 (B.lcm id) (periodicBlockMax B (atom (B.lcm id) d h ϑ)) ≤
      d.divisors.card * M * (∑ r ∈ d.divisors, (r.divisors.card : ℝ)) *
        l2 (B.lcm id) (fun x => ‖atom (B.lcm id) d h ϑ x‖) := by
  have hN : 0 < B.lcm id := by
    rcases Nat.eq_zero_or_pos (B.lcm id) with h0 | h0
    · exfalso
      rw [Finset.lcm_eq_zero_iff] at h0
      obtain ⟨q, hq, hq0⟩ := h0
      exact (hB q hq).ne' (by simpa using hq0)
    · exact h0
  set N := B.lcm id with hNdef
  set D := N / d with hDdef
  have hND : N = d * D := (Nat.mul_div_cancel' hdN).symm
  have hD : 0 < D := Nat.div_pos (Nat.le_of_dvd hN hdN) hd
  have hBN : ∀ q ∈ B, q ∣ N := fun q hq => Finset.dvd_lcm hq
  set G : ℕ → ℝ := fun u =>
    d.divisors.card * M * ∑ r ∈ d.divisors, ‖ramanujanSum r (u : ℤ)‖ with hG
  have hG0 : ∀ u, 0 ≤ G u := fun u =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hM0) (sum_nonneg fun r _ => norm_nonneg _)
  set Φ : ℤ → ℂ := atom N d h ϑ with hΦ
  -- Step 1: the pointwise bound.
  have hpt : ∀ x, periodicBlockMax B Φ x ≤
      (d : ℝ)⁻¹ * ∑ u ∈ range d, G u * ‖Φ (x - (u : ℤ))‖ := by
    intro x
    refine Real.iSup_le (fun θ => ?_) ?_
    · rw [Fin.sum_univ_eq_sum_range (fun r : ℕ => Φ (x - (r : ℤ)) * blockWeight B (r : ℤ) *
        e (((r : ℕ) : ℝ) * ((θ : ℕ) : ℝ) / (N : ℝ))) N]
      have := norm_avg_atom_le (B := B) hd hD hND hcop hBN hM0 hM h ϑ x ((θ : ℕ) : ℤ)
      simpa only [Int.cast_natCast] using this
    · exact mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))
        (sum_nonneg fun u _ => mul_nonneg (hG0 u) (norm_nonneg _))
  -- Step 2: the `ℓ²` bound.
  calc l2 N (periodicBlockMax B Φ)
      ≤ l2 N (fun x => (d : ℝ)⁻¹ * ∑ u ∈ range d, G u * ‖Φ (x - (u : ℤ))‖) :=
        l2_mono (periodicBlockMax_nonneg B Φ) hpt
    _ = (d : ℝ)⁻¹ * l2 N (fun x => ∑ u ∈ range d, G u * ‖Φ (x - (u : ℤ))‖) :=
        l2_const_mul N (inv_nonneg.2 (Nat.cast_nonneg _)) _
    _ ≤ (d : ℝ)⁻¹ * ∑ u ∈ range d, l2 N (fun x => G u * ‖Φ (x - (u : ℤ))‖) :=
        mul_le_mul_of_nonneg_left (l2_sum_le N (range d) fun u x => G u * ‖Φ (x - (u : ℤ))‖)
          (inv_nonneg.2 (Nat.cast_nonneg _))
    _ = (d : ℝ)⁻¹ * ∑ u ∈ range d, G u * l2 N (fun x => ‖Φ x‖) := by
        congr 1
        refine sum_congr rfl fun u _ => ?_
        rw [l2_const_mul N (hG0 u), hΦ, l2_norm_atom_sub hdN h ϑ u]
    _ = (d : ℝ)⁻¹ * (∑ u ∈ range d, G u) * l2 N (fun x => ‖Φ x‖) := by
        rw [← Finset.sum_mul, mul_assoc]
    _ ≤ d.divisors.card * M * (∑ r ∈ d.divisors, (r.divisors.card : ℝ)) *
          l2 N (fun x => ‖Φ x‖) := by
        refine mul_le_mul_of_nonneg_right ?_ (l2_nonneg _ _)
        exact inv_mul_sum_envelope_le hd hM0

end PrimeCarleson.Proof.Goal0
