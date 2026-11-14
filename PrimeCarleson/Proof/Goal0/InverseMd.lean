module

public import PrimeCarleson.Proof.Goal0.Atom
public import PrimeCarleson.Proof.Goal0.Operators

/-!
# The inverse theorem for the fibre maximal operator `M_d`

Lemma `l:invMd` of `sources/Variational_Carleson.tex` (L2404–L2454), with the representation
lemma of L2371–L2391 (Source: main paper `l:invMd`, L2404–L2417), in the proof of Proposition
`p:goal0` formalized here. For a divisor `d` of `N`, `D = N / d` and `f` `N`-periodic, write
`x = a + d s` with `a = x mod d`:

* `fiberAvg_eq`, `fiberMax_eq_fiberSup`: the average
  `D⁻¹ ∑_{l < D} f(x - l d) e(l θ / D)` equals `e(s θ / D)` times the Fourier coefficient
  `fiberCoeff` of the fibre `t ↦ f(a + d t)`, hence `M_d f(x) = sup_θ |F̂_a(θ)|` depends on
  `x mod d` only;
* `exists_atom_inner_eq`: there are a structured atom `Φ(a + d s) = h(a) e(ϑ(a) s / D)` of unit
  `ℓ²` norm over one period and `⟨Φ, f⟩ = ‖M_d f‖`;
* `l2_fiberMax_le`: `‖M_d f‖ ≤ ‖f‖` over one period (L2291), by Cauchy–Schwarz against that
  atom.

The paper normalises `𝔼_{a ∈ [d]} |h(a)|² = 1` and uses the inner product over `(-N, 2N]`; here
the `ℓ²` norm of `Φ` over one period is `1`, which is the normalisation of `Atom.lean`.
-/

@[expose] public noncomputable section

open Finset
open scoped ComplexConjugate

set_option autoImplicit false

namespace PrimeCarleson.Proof.Goal0

/-- The Fourier coefficient `F̂_a(θ) = D⁻¹ ∑_{t < D} f(a + d t) e(-t θ / D)` of the fibre
`F_a(t) = f(a + d t)` (L2365–L2369). -/
def fiberCoeff (D d : ℕ) (f : ℤ → ℂ) (a θ : ℤ) : ℂ :=
  (D : ℂ)⁻¹ * ∑ t ∈ range D, f (a + d * t) * e (-((t : ℝ) * (θ : ℝ) / (D : ℝ)))

/-- `M(a) = sup_{θ ∈ ℤ / N} |F̂_a(θ)|` (L2419–L2421). -/
def fiberSup (N d : ℕ) (f : ℤ → ℂ) (a : ℤ) : ℝ :=
  ⨆ θ : Fin N, ‖fiberCoeff (N / d) d f a ((θ : ℕ) : ℤ)‖

/-- Representation lemma (L2371–L2391): for `x = a + d s`,
`D⁻¹ ∑_{l < D} f(x - l d) e(l θ / D) = e(s θ / D) F̂_a(θ)`, `θ ∈ ℤ`. -/
theorem fiberAvg_eq {N d : ℕ} (hd : 0 < d) (hdN : d ∣ N) {f : ℤ → ℂ}
    (hf : Function.Periodic f (N : ℤ)) (x θ : ℤ) :
    ((N / d : ℕ) : ℂ)⁻¹ * ∑ l ∈ range (N / d),
        f (x - l * d) * e ((l : ℝ) * (θ : ℝ) / ((N / d : ℕ) : ℝ)) =
      e (((x / d : ℤ) : ℝ) * (θ : ℝ) / ((N / d : ℕ) : ℝ)) *
        fiberCoeff (N / d) d f (x % d) θ := by
  obtain ⟨D, rfl⟩ := hdN
  rw [Nat.mul_div_cancel_left D hd]
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · simp [fiberCoeff]
  have hDR : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hx : x = x % (d : ℤ) + d * (x / (d : ℤ)) := (Int.emod_add_mul_ediv x d).symm
  set a : ℤ := x % (d : ℤ) with ha
  set s : ℤ := x / (d : ℤ) with hs
  have hper : Function.Periodic
      (fun t : ℤ => f (a + d * t) * e (((s - t : ℤ) : ℝ) * (θ : ℝ) / (D : ℝ))) (D : ℤ) := by
    intro t
    have h1 : f (a + d * (t + D)) = f (a + d * t) := by
      rw [show a + d * (t + D) = a + d * t + ((d * D : ℕ) : ℤ) by push_cast; ring]
      exact hf _
    have h2 : ((s - (t + D) : ℤ) : ℝ) * (θ : ℝ) / (D : ℝ) =
        ((s - t : ℤ) : ℝ) * (θ : ℝ) / (D : ℝ) + ((-θ : ℤ) : ℝ) := by
      push_cast
      field_simp
      ring
    simp only [h1, h2, e_add_intCast]
  have hsum := sum_range_sub_of_periodic hper s
  have hL : ∑ l ∈ range D, f (x - l * d) * e ((l : ℝ) * (θ : ℝ) / (D : ℝ)) =
      ∑ l ∈ range D, f (a + d * (s - (l : ℤ))) *
        e (((s - (s - (l : ℤ)) : ℤ) : ℝ) * (θ : ℝ) / (D : ℝ)) := by
    refine sum_congr rfl fun l _ => ?_
    have h1 : x - (l : ℤ) * d = a + d * (s - (l : ℤ)) := by linear_combination hx
    have h2 : (((s - (s - (l : ℤ)) : ℤ)) : ℝ) = (l : ℝ) := by push_cast; ring
    rw [h1, h2]
  have hR : ∑ t ∈ range D, f (a + d * (t : ℤ)) *
        e (((s - (t : ℤ) : ℤ) : ℝ) * (θ : ℝ) / (D : ℝ)) =
      e ((s : ℝ) * (θ : ℝ) / (D : ℝ)) *
        ∑ t ∈ range D, f (a + d * (t : ℤ)) * e (-((t : ℝ) * (θ : ℝ) / (D : ℝ))) := by
    rw [mul_sum]
    refine sum_congr rfl fun t _ => ?_
    have : (((s - (t : ℤ) : ℤ)) : ℝ) * (θ : ℝ) / (D : ℝ) =
        (s : ℝ) * (θ : ℝ) / (D : ℝ) + -((t : ℝ) * (θ : ℝ) / (D : ℝ)) := by
      push_cast; ring
    rw [this, e_add]
    ring
  unfold fiberCoeff
  rw [hL]
  rw [hsum, hR]
  ring

/-- `M_d f(x) = M(x mod d)` (L2391). -/
theorem fiberMax_eq_fiberSup {N d : ℕ} (hd : 0 < d) (hdN : d ∣ N) {f : ℤ → ℂ}
    (hf : Function.Periodic f (N : ℤ)) (x : ℤ) :
    fiberMax N d f x = fiberSup N d f (x % d) := by
  unfold fiberMax fiberSup
  refine iSup_congr fun θ => ?_
  have := fiberAvg_eq hd hdN hf x ((θ : ℕ) : ℤ)
  simp only [Int.cast_natCast] at this
  rw [this, norm_mul, norm_e, one_mul]

/-- The supremum defining `M(a)` is attained, by a choice `ϑ(a)` independent of the other
fibres (L2423–L2426). -/
theorem exists_fiberSup_attained {N : ℕ} (d : ℕ) (hN : 0 < N) (f : ℤ → ℂ) :
    ∃ ϑ : ℤ → ℤ, ∀ a, ‖fiberCoeff (N / d) d f a (ϑ a)‖ = fiberSup N d f a := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have key : ∀ a : ℤ, ∃ θ : Fin N,
      ‖fiberCoeff (N / d) d f a ((θ : ℕ) : ℤ)‖ = fiberSup N d f a := by
    intro a
    obtain ⟨θ, hθ⟩ := Finite.exists_max
      (fun θ : Fin N => ‖fiberCoeff (N / d) d f a ((θ : ℕ) : ℤ)‖)
    refine ⟨θ, le_antisymm ?_ (ciSup_le hθ)⟩
    exact le_ciSup (f := fun θ : Fin N => ‖fiberCoeff (N / d) d f a ((θ : ℕ) : ℤ)‖)
      (Set.finite_range _).bddAbove θ
  choose θ hθ using key
  exact ⟨fun a => ((θ a : ℕ) : ℤ), hθ⟩

/-- Splitting `⟨Φ, f⟩` over the fibres `x = a + d s`: it equals
`∑_{a < d} conj(h a) D F̂_a(ϑ a)` (L2441–L2448). -/
theorem sum_conj_atom_mul {N d : ℕ} (hd : 0 < d) (hdN : d ∣ N) (f : ℤ → ℂ) (h : ℤ → ℂ)
    (ϑ : ℤ → ℤ) :
    ∑ x ∈ range N, conj (atom N d h ϑ x) * f x =
      ∑ a ∈ range d, conj (h a) * (((N / d : ℕ) : ℂ) * fiberCoeff (N / d) d f a (ϑ a)) := by
  obtain ⟨D, rfl⟩ := hdN
  have hND : d * D / d = D := Nat.mul_div_cancel_left D hd
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · simp
  have hDC : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  rw [sum_range_mul_eq d D (fun x : ℕ => conj (atom (d * D) d h ϑ x) * f x), hND]
  refine sum_congr rfl fun a ha => ?_
  rw [mem_range] at ha
  have ha0 : (0 : ℤ) ≤ (a : ℤ) := Int.natCast_nonneg a
  have had : (a : ℤ) < d := by exact_mod_cast ha
  unfold fiberCoeff
  rw [mul_inv_cancel_left₀ hDC, mul_sum]
  refine sum_congr rfl fun s _ => ?_
  have hcast : (((a + d * s : ℕ)) : ℤ) = (a : ℤ) + d * (s : ℤ) := by push_cast; ring
  rw [hcast, atom_add_mul hd h ϑ ha0 had, hND, map_mul, ← e_neg]
  have : -((ϑ a : ℝ) * ((s : ℤ) : ℝ) / (D : ℝ)) = -((s : ℝ) * (ϑ a : ℝ) / (D : ℝ)) := by
    push_cast; ring
  rw [this]
  ring

/-- If `F x` depends only on `x mod d`, then `∑_{x < N} F(x)² = D ∑_{a < d} F_a²`. -/
theorem sum_sq_of_emod {N d : ℕ} (hd : 0 < d) (hdN : d ∣ N) {F : ℤ → ℝ} {Fa : ℤ → ℝ}
    (hF : ∀ x, F x = Fa (x % d)) :
    ∑ x ∈ range N, F x ^ 2 = ((N / d : ℕ) : ℝ) * ∑ a ∈ range d, Fa a ^ 2 := by
  obtain ⟨D, rfl⟩ := hdN
  rw [Nat.mul_div_cancel_left D hd, sum_range_mul_eq d D (fun x : ℕ => F x ^ 2)]
  rw [mul_sum]
  refine sum_congr rfl fun a ha => ?_
  rw [mem_range] at ha
  have ha0 : (0 : ℤ) ≤ (a : ℤ) := Int.natCast_nonneg a
  have had : (a : ℤ) < d := by exact_mod_cast ha
  have : ∀ s ∈ range D, F (((a + d * s : ℕ)) : ℤ) ^ 2 = Fa a ^ 2 := by
    intro s _
    have hcast : (((a + d * s : ℕ)) : ℤ) = (a : ℤ) + d * (s : ℤ) := by push_cast; ring
    rw [hF, hcast, Int.add_mul_emod_self_left, Int.emod_eq_of_lt ha0 had]
  rw [sum_congr rfl this, sum_const, card_range, nsmul_eq_mul]

/-- Inverse theorem for `M_d` (Lemma l:invMd): `‖M_d f‖` is attained as `⟨Φ, f⟩` by a unit atom. -/
theorem exists_atom_inner_eq {N d : ℕ} (hd : 0 < d) (hdN : d ∣ N) {f : ℤ → ℂ}
    (hf : Function.Periodic f (N : ℤ)) (hpos : 0 < l2 N (fiberMax N d f)) :
    ∃ (h : ℤ → ℂ) (ϑ : ℤ → ℤ), l2 N (fun x => ‖atom N d h ϑ x‖) = 1 ∧
      ∑ x ∈ Finset.range N, (starRingEnd ℂ) (atom N d h ϑ x) * f x =
        ((l2 N (fiberMax N d f) : ℝ) : ℂ) := by
  have hN : 0 < N := Nat.pos_of_ne_zero (by rintro rfl; simp [l2] at hpos)
  have hDpos : 0 < N / d := Nat.div_pos (Nat.le_of_dvd hN hdN) hd
  obtain ⟨ϑ, hϑ⟩ := exists_fiberSup_attained d hN f
  set Z : ℝ := l2 N (fiberMax N d f) with hZ
  have hZ0 : Z ≠ 0 := hpos.ne'
  have hZC : (Z : ℂ) ≠ 0 := by exact_mod_cast hZ0
  have hDC : ((N / d : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hDpos.ne'
  set h : ℤ → ℂ := fun a => fiberCoeff (N / d) d f a (ϑ a) / (Z : ℂ) with hh
  refine ⟨h, ϑ, ?_, ?_⟩
  · have hfun : (fun x => ‖atom N d h ϑ x‖) = fun x => Z⁻¹ * fiberMax N d f x := by
      funext x
      rw [norm_atom, hh, norm_div, hϑ, ← fiberMax_eq_fiberSup hd hdN hf, Complex.norm_real,
        Real.norm_of_nonneg hpos.le, div_eq_inv_mul]
    rw [hfun, l2_const_mul N (inv_nonneg.2 hpos.le)]
    exact inv_mul_cancel₀ hZ0
  · rw [sum_conj_atom_mul hd hdN]
    have hsq : Z ^ 2 = ((N / d : ℕ) : ℝ) * ∑ a ∈ range d, fiberSup N d f a ^ 2 := by
      rw [hZ, l2_sq]
      exact sum_sq_of_emod hd hdN (fun x => fiberMax_eq_fiberSup hd hdN hf x)
    have hterm : ∀ a ∈ range d,
        conj (h a) * (((N / d : ℕ) : ℂ) * fiberCoeff (N / d) d f a (ϑ a)) =
          ((((N / d : ℕ) : ℝ) * fiberSup N d f a ^ 2 / Z : ℝ) : ℂ) := by
      intro a _
      have hmul : conj (fiberCoeff (N / d) d f a (ϑ a)) * fiberCoeff (N / d) d f a (ϑ a) =
          ((fiberSup N d f a ^ 2 : ℝ) : ℂ) := by
        rw [Complex.conj_mul', ← hϑ a]
        push_cast
        rfl
      simp only [hh, map_div₀, Complex.conj_ofReal]
      push_cast
      calc conj (fiberCoeff (N / d) d f a (ϑ a)) / (Z : ℂ) *
            (((N / d : ℕ) : ℂ) * fiberCoeff (N / d) d f a (ϑ a))
          = ((N / d : ℕ) : ℂ) / (Z : ℂ) *
            (conj (fiberCoeff (N / d) d f a (ϑ a)) * fiberCoeff (N / d) d f a (ϑ a)) := by ring
        _ = _ := by rw [hmul]; push_cast; ring
    rw [sum_congr rfl hterm, ← Complex.ofReal_sum]
    congr 1
    rw [← sum_div, ← mul_sum, ← hsq, pow_two, mul_self_div_self]

/-- `M_d` is a contraction on `ℓ²` of one period (L2291). -/
theorem l2_fiberMax_le {N d : ℕ} (hd : 0 < d) (hdN : d ∣ N) {f : ℤ → ℂ}
    (hf : Function.Periodic f (N : ℤ)) : l2 N (fiberMax N d f) ≤ l2 N (fun x => ‖f x‖) := by
  rcases (l2_nonneg N (fiberMax N d f)).eq_or_lt with h0 | hpos
  · rw [← h0]
    exact l2_nonneg _ _
  obtain ⟨h, ϑ, hnorm, hinner⟩ := exists_atom_inner_eq hd hdN hf hpos
  have h1 : l2 N (fiberMax N d f) ≤ ∑ x ∈ range N, ‖atom N d h ϑ x‖ * ‖f x‖ :=
    calc l2 N (fiberMax N d f) = ‖((l2 N (fiberMax N d f) : ℝ) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_of_nonneg hpos.le]
      _ = ‖∑ x ∈ range N, conj (atom N d h ϑ x) * f x‖ := by rw [hinner]
      _ ≤ ∑ x ∈ range N, ‖conj (atom N d h ϑ x) * f x‖ := norm_sum_le _ _
      _ = ∑ x ∈ range N, ‖atom N d h ϑ x‖ * ‖f x‖ := by
          simp only [norm_mul, RCLike.norm_conj]
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq (range N) (fun x : ℕ => ‖atom N d h ϑ (x : ℤ)‖)
    (fun x : ℕ => ‖f (x : ℤ)‖)
  have hA := l2_sq N (fun x => ‖atom N d h ϑ x‖)
  have hB := l2_sq N (fun x => ‖f x‖)
  rw [hnorm] at hA
  have h3 : l2 N (fiberMax N d f) ^ 2 ≤ l2 N (fun x => ‖f x‖) ^ 2 := by
    calc l2 N (fiberMax N d f) ^ 2 ≤ (∑ x ∈ range N, ‖atom N d h ϑ x‖ * ‖f x‖) ^ 2 :=
          pow_le_pow_left₀ hpos.le h1 2
      _ ≤ _ := h2
      _ = l2 N (fun x => ‖f x‖) ^ 2 := by rw [hB, ← hA]; simp
  exact (pow_le_pow_iff_left₀ hpos.le (l2_nonneg _ _) two_ne_zero).1 h3

end PrimeCarleson.Proof.Goal0
