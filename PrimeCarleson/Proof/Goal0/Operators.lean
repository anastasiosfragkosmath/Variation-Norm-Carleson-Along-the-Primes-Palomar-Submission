module

public import PrimeCarleson.Proof.Goal0.Space
public import PrimeCarleson.Proof.Goal0.Ramanujan
public import PrimeCarleson.Frozen.PeriodicBlockMax

/-!
# The fibre maximal operators `M_d` and the pointwise bound of `M_B`

The unweighted fibre maximal operators `M_d` of `sources/Variational_Carleson.tex`
(L2287-L2289) and Lemma `l:MdMB` (L2291-L2358), Source: main paper, L2340–L2350, for Proposition
`p:goal0`:

* `fiberMax N d f x`: `M_d f(x) = sup_θ |D⁻¹ ∑_{l < D} f(x - l d) e(l θ / D)|`, `D = N / d`;
* `periodicBlockMax_le_sum_fiberMax`: for `N = lcm B` and `B` consisting of positive integers,
  `M_B f(x) ≤ ∑_{q ∈ B} φ(q)⁻¹ ∑_{d ∣ q} M_d f(x)`. Here the Möbius inversion
  `w_B(r) = ∑_{q ∈ B} (μ(q) / φ(q)) ∑_{d ∣ q} d μ(q / d) 1_{d ∣ r}` (from
  `ramanujanSum_eq_sum_divisors`) is used directly, with `|μ| ≤ 1`, instead of the
  simplification `μ(q) μ(q / d) = μ(d)` of the paper;
* `l2_periodicBlockMax_le_sum`: the same bound for the `ℓ²` norms over one period (Minkowski);
* the elementary lattice properties `fiberMax_nonneg`, `norm_le_fiberMax`,
  `periodicBlockMax_nonneg`, `periodicBlockMax_add_le`, `periodicBlockMax_smul`.
-/

@[expose] public noncomputable section

open Finset

set_option autoImplicit false

namespace PrimeCarleson.Proof.Goal0

/-- `M_d f(x) = sup_{θ ∈ ℤ/N} |D⁻¹ ∑_{l < D} f(x - l d) e(l θ / D)|`, `D = N / d`
(`sources/Variational_Carleson.tex` L2287-L2289). The supremum runs over `θ ∈ ℤ/N`, which gives
the same value as the supremum over `ξ ∈ ℤ/D` of the paper, because the average is `D`-periodic
in `θ`. -/
def fiberMax (N d : ℕ) (f : ℤ → ℂ) (x : ℤ) : ℝ :=
  ⨆ θ : Fin N, ‖((N / d : ℕ) : ℂ)⁻¹ *
    ∑ l ∈ Finset.range (N / d), f (x - l * d) * e ((l : ℝ) * (θ : ℕ) / (N / d : ℕ))‖

/-- `M_d f(x) ≥ 0`. -/
theorem fiberMax_nonneg (N d : ℕ) (f : ℤ → ℂ) (x : ℤ) : 0 ≤ fiberMax N d f x :=
  Real.iSup_nonneg fun _ => norm_nonneg _

/-- Each term of the supremum defining `M_d f(x)` is at most `M_d f(x)`. -/
theorem norm_le_fiberMax {N : ℕ} (d : ℕ) (f : ℤ → ℂ) (x : ℤ) (θ : Fin N) :
    ‖((N / d : ℕ) : ℂ)⁻¹ * ∑ l ∈ Finset.range (N / d),
      f (x - l * d) * e ((l : ℝ) * (θ : ℕ) / (N / d : ℕ))‖ ≤ fiberMax N d f x :=
  le_ciSup (f := fun θ : Fin N => ‖((N / d : ℕ) : ℂ)⁻¹ * ∑ l ∈ Finset.range (N / d),
      f (x - l * d) * e ((l : ℝ) * (θ : ℕ) / (N / d : ℕ))‖) (Set.finite_range _).bddAbove θ

/-- `M_B f(x) ≥ 0`. -/
theorem periodicBlockMax_nonneg (B : Finset ℕ) (f : ℤ → ℂ) (x : ℤ) :
    0 ≤ periodicBlockMax B f x :=
  Real.iSup_nonneg fun _ => norm_nonneg _

/-- Each term of the supremum defining `M_B f(x)` is at most `M_B f(x)`. -/
theorem norm_le_periodicBlockMax (B : Finset ℕ) (f : ℤ → ℂ) (x : ℤ) (θ : Fin (B.lcm id)) :
    ‖((B.lcm id : ℕ) : ℂ)⁻¹ * ∑ r : Fin (B.lcm id),
        f (x - (r : ℕ)) * blockWeight B (r : ℕ) *
          e (((r : ℕ) : ℝ) * ((θ : ℕ) : ℝ) / ((B.lcm id : ℕ) : ℝ))‖ ≤ periodicBlockMax B f x :=
  le_ciSup (f := fun θ : Fin (B.lcm id) => ‖((B.lcm id : ℕ) : ℂ)⁻¹ * ∑ r : Fin (B.lcm id),
        f (x - (r : ℕ)) * blockWeight B (r : ℕ) *
          e (((r : ℕ) : ℝ) * ((θ : ℕ) : ℝ) / ((B.lcm id : ℕ) : ℝ))‖)
    (Set.finite_range _).bddAbove θ

/-- `M_B` is subadditive. -/
theorem periodicBlockMax_add_le (B : Finset ℕ) (f g : ℤ → ℂ) (x : ℤ) :
    periodicBlockMax B (f + g) x ≤ periodicBlockMax B f x + periodicBlockMax B g x := by
  refine Real.iSup_le (fun θ => ?_)
    (add_nonneg (periodicBlockMax_nonneg B f x) (periodicBlockMax_nonneg B g x))
  have h : ((B.lcm id : ℕ) : ℂ)⁻¹ * ∑ r : Fin (B.lcm id),
        (f + g) (x - (r : ℕ)) * blockWeight B (r : ℕ) *
          e (((r : ℕ) : ℝ) * ((θ : ℕ) : ℝ) / ((B.lcm id : ℕ) : ℝ)) =
      ((B.lcm id : ℕ) : ℂ)⁻¹ * ∑ r : Fin (B.lcm id),
        f (x - (r : ℕ)) * blockWeight B (r : ℕ) *
          e (((r : ℕ) : ℝ) * ((θ : ℕ) : ℝ) / ((B.lcm id : ℕ) : ℝ)) +
      ((B.lcm id : ℕ) : ℂ)⁻¹ * ∑ r : Fin (B.lcm id),
        g (x - (r : ℕ)) * blockWeight B (r : ℕ) *
          e (((r : ℕ) : ℝ) * ((θ : ℕ) : ℝ) / ((B.lcm id : ℕ) : ℝ)) := by
    rw [← mul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [Pi.add_apply]
    ring
  rw [h]
  exact (norm_add_le _ _).trans
    (add_le_add (norm_le_periodicBlockMax B f x θ) (norm_le_periodicBlockMax B g x θ))

/-- `M_B (c f) = |c| M_B f`. -/
theorem periodicBlockMax_smul (B : Finset ℕ) (c : ℂ) (f : ℤ → ℂ) (x : ℤ) :
    periodicBlockMax B (c • f) x = ‖c‖ * periodicBlockMax B f x := by
  unfold periodicBlockMax
  rw [Real.mul_iSup_of_nonneg (norm_nonneg c)]
  refine iSup_congr fun θ => ?_
  have h : ((B.lcm id : ℕ) : ℂ)⁻¹ * ∑ r : Fin (B.lcm id),
        (c • f) (x - (r : ℕ)) * blockWeight B (r : ℕ) *
          e (((r : ℕ) : ℝ) * ((θ : ℕ) : ℝ) / ((B.lcm id : ℕ) : ℝ)) =
      c * (((B.lcm id : ℕ) : ℂ)⁻¹ * ∑ r : Fin (B.lcm id),
        f (x - (r : ℕ)) * blockWeight B (r : ℕ) *
          e (((r : ℕ) : ℝ) * ((θ : ℕ) : ℝ) / ((B.lcm id : ℕ) : ℝ))) := by
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    ring
  rw [h, norm_mul]

/-- The multiples of `d` in `[0, d D)` are `l d`, `l < D`:
`D⁻¹ ∑_{l < D} G(l d) = (d D)⁻¹ ∑_{r < d D, d ∣ r} d G(r)`. -/
theorem inv_mul_sum_ite_dvd {N d : ℕ} (hd : 0 < d) (hdN : d ∣ N) (G : ℕ → ℂ) :
    (N : ℂ)⁻¹ * ∑ r ∈ range N, (if d ∣ r then (d : ℂ) * G r else 0) =
      ((N / d : ℕ) : ℂ)⁻¹ * ∑ l ∈ range (N / d), G (l * d) := by
  obtain ⟨D, rfl⟩ := hdN
  rw [Nat.mul_div_cancel_left D hd,
    sum_range_mul_eq d D (fun r => if d ∣ r then (d : ℂ) * G r else 0)]
  rw [Finset.sum_eq_single 0]
  · have hdR : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    have : ∀ s ∈ range D, (if d ∣ 0 + d * s then (d : ℂ) * G (0 + d * s) else 0) =
        (d : ℂ) * G (s * d) := by
      intro s _
      simp [mul_comm d s]
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum]
    push_cast
    field_simp
  · intro a ha ha0
    rw [mem_range] at ha
    refine Finset.sum_eq_zero fun s _ => ?_
    have hnd : ¬ d ∣ a + d * s := by
      intro hdiv
      have : d ∣ a := (Nat.dvd_add_left (dvd_mul_right d s)).1 hdiv
      exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero ha0) this) (by omega)
    simp [hnd]
  · intro h0
    exact absurd (mem_range.2 hd) h0

/-- Möbius inversion for the weighted average: if `q ∣ N` for all `q ∈ B`, the weighted
average `N⁻¹ ∑_{r < N} f(x - r) w_B(r) e(r t / N)` equals
`∑_{q ∈ B} (μ(q) / φ(q)) ∑_{d ∣ q} μ(q / d) 𝔼_{l < N / d} f(x - l d) e(l t / (N / d))`. -/
theorem blockWeight_average_eq {B : Finset ℕ} {N : ℕ} (hBN : ∀ q ∈ B, q ∣ N) (f : ℤ → ℂ)
    (x : ℤ) (t : ℝ) :
    (N : ℂ)⁻¹ * ∑ r ∈ range N,
        f (x - (r : ℕ)) * blockWeight B (r : ℕ) * e (((r : ℕ) : ℝ) * t / (N : ℝ)) =
      ∑ q ∈ B, (((ArithmeticFunction.moebius q : ℤ) : ℝ) / (Nat.totient q : ℝ) : ℂ) *
        ∑ d ∈ q.divisors, ((ArithmeticFunction.moebius (q / d) : ℤ) : ℂ) *
          (((N / d : ℕ) : ℂ)⁻¹ * ∑ l ∈ range (N / d),
            f (x - l * d) * e ((l : ℝ) * t / (N / d : ℕ))) := by
  set G : ℕ → ℂ := fun r => f (x - (r : ℕ)) * e (((r : ℕ) : ℝ) * t / (N : ℝ)) with hG
  have key : ∀ r : ℕ, f (x - (r : ℕ)) * blockWeight B (r : ℕ) *
      e (((r : ℕ) : ℝ) * t / (N : ℝ)) =
      ∑ q ∈ B, (((ArithmeticFunction.moebius q : ℤ) : ℝ) / (Nat.totient q : ℝ) : ℂ) *
        ∑ d ∈ q.divisors, ((ArithmeticFunction.moebius (q / d) : ℤ) : ℂ) *
          (if d ∣ r then (d : ℂ) * G r else 0) := by
    intro r
    unfold blockWeight
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [ramanujanSum_eq_sum_divisors, Finset.sum_filter]
    simp only [Int.natCast_dvd_natCast]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp only [hG]
    split_ifs <;> ring
  have step : ∀ q ∈ B, ∀ d ∈ q.divisors,
      (N : ℂ)⁻¹ * ∑ r ∈ range N, (if d ∣ r then (d : ℂ) * G r else 0) =
        ((N / d : ℕ) : ℂ)⁻¹ * ∑ l ∈ range (N / d),
          f (x - l * d) * e ((l : ℝ) * t / (N / d : ℕ)) := by
    intro q hq d hd
    have hdq : d ∣ q := Nat.dvd_of_mem_divisors hd
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
    have hdN : d ∣ N := hdq.trans (hBN q hq)
    rw [inv_mul_sum_ite_dvd hdpos hdN G]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    obtain ⟨D, hD⟩ := hdN
    have hDd : N / d = D := by rw [hD, Nat.mul_div_cancel_left D hdpos]
    have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hdpos.ne'
    simp only [hG, Nat.cast_mul]
    congr 2
    rw [hDd, hD]
    push_cast
    field_simp
  simp only [key]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [← Finset.mul_sum, Finset.sum_comm, mul_left_comm]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [← step q hq d hd, ← Finset.mul_sum, mul_left_comm]

/-- `|μ(n)| ≤ 1`, as a complex norm. -/
theorem norm_moebius_le_one (n : ℕ) : ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_intCast]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one

/-- `|μ(q) / φ(q)| ≤ φ(q)⁻¹` for `q > 0`, as a complex norm. -/
theorem norm_moebius_div_totient_le_of_pos {q : ℕ} (hq : 0 < q) :
    ‖(((ArithmeticFunction.moebius q : ℤ) : ℝ) / (Nat.totient q : ℝ) : ℂ)‖ ≤
      ((q.totient : ℝ))⁻¹ := by
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 hq
  have hμ : |((ArithmeticFunction.moebius q : ℤ) : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  rw [← Complex.ofReal_div, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hφ,
    ← one_div]
  gcongr

/-- Pointwise `M_B f ≤ ∑_{q ∈ B} φ(q)⁻¹ ∑_{d ∣ q} M_d f`
(`sources/Variational_Carleson.tex` L2291-L2358, Lemma `l:MdMB`; Source: main paper, L2340–L2350).
-/
theorem periodicBlockMax_le_sum_fiberMax {B : Finset ℕ} (hB : ∀ q ∈ B, 0 < q) (f : ℤ → ℂ)
    (x : ℤ) :
    periodicBlockMax B f x ≤
      ∑ q ∈ B, ((q.totient : ℝ))⁻¹ * ∑ d ∈ q.divisors, fiberMax (B.lcm id) d f x := by
  have hBN : ∀ q ∈ B, q ∣ B.lcm id := fun q hq => Finset.dvd_lcm hq
  refine Real.iSup_le (fun θ => ?_) ?_
  · rw [Fin.sum_univ_eq_sum_range (fun r : ℕ => f (x - (r : ℕ)) * blockWeight B (r : ℕ) *
      e (((r : ℕ) : ℝ) * ((θ : ℕ) : ℝ) / ((B.lcm id : ℕ) : ℝ))) (B.lcm id)]
    rw [blockWeight_average_eq hBN f x ((θ : ℕ) : ℝ)]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q hq => ?_)
    have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 (hB q hq)
    rw [norm_mul]
    refine mul_le_mul (norm_moebius_div_totient_le_of_pos (hB q hq)) ?_ (norm_nonneg _)
      (inv_nonneg.2 hφ.le)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d _ => ?_)
    rw [norm_mul]
    calc ‖((ArithmeticFunction.moebius (q / d) : ℤ) : ℂ)‖ * _
        ≤ 1 * fiberMax (B.lcm id) d f x :=
          mul_le_mul (norm_moebius_le_one _) (norm_le_fiberMax d f x θ) (norm_nonneg _)
            zero_le_one
      _ = fiberMax (B.lcm id) d f x := one_mul _
  · exact Finset.sum_nonneg fun q _ => mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun d _ => fiberMax_nonneg _ _ _ _)

/-- The same bound for the `ℓ²` norms over one period (Minkowski). -/
theorem l2_periodicBlockMax_le_sum {B : Finset ℕ} (hB : ∀ q ∈ B, 0 < q) (f : ℤ → ℂ) :
    l2 (B.lcm id) (periodicBlockMax B f) ≤
      ∑ q ∈ B, ((q.totient : ℝ))⁻¹ *
        ∑ d ∈ q.divisors, l2 (B.lcm id) (fiberMax (B.lcm id) d f) := by
  calc l2 (B.lcm id) (periodicBlockMax B f)
      ≤ l2 (B.lcm id) (fun x => ∑ q ∈ B, ((q.totient : ℝ))⁻¹ *
          ∑ d ∈ q.divisors, fiberMax (B.lcm id) d f x) :=
        l2_mono (periodicBlockMax_nonneg B f) (periodicBlockMax_le_sum_fiberMax hB f)
    _ ≤ ∑ q ∈ B, l2 (B.lcm id) (fun x => ((q.totient : ℝ))⁻¹ *
          ∑ d ∈ q.divisors, fiberMax (B.lcm id) d f x) :=
        l2_sum_le (B.lcm id) B (fun q x => ((q.totient : ℝ))⁻¹ *
          ∑ d ∈ q.divisors, fiberMax (B.lcm id) d f x)
    _ = ∑ q ∈ B, ((q.totient : ℝ))⁻¹ *
          l2 (B.lcm id) (fun x => ∑ d ∈ q.divisors, fiberMax (B.lcm id) d f x) :=
        Finset.sum_congr rfl fun q _ =>
          l2_const_mul (B.lcm id) (inv_nonneg.2 (Nat.cast_nonneg _)) _
    _ ≤ ∑ q ∈ B, ((q.totient : ℝ))⁻¹ *
          ∑ d ∈ q.divisors, l2 (B.lcm id) (fiberMax (B.lcm id) d f) :=
        Finset.sum_le_sum fun q _ => mul_le_mul_of_nonneg_left
          (l2_sum_le (B.lcm id) q.divisors (fun d => fiberMax (B.lcm id) d f))
          (inv_nonneg.2 (Nat.cast_nonneg _))

end PrimeCarleson.Proof.Goal0
