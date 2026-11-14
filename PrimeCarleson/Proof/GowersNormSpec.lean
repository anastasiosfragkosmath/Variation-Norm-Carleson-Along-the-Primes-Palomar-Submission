module

public import PrimeCarleson.Frozen.MultDiff
public import PrimeCarleson.Frozen.GowersNorm
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Provider for `PrimeCarleson.gowersNorm_spec`

Proves the statement under the separate name
`PrimeCarleson.Proof.gowersNorm_spec`.
Only `PrimeCarleson.Frozen.GowersNormSpec` imports this module.

Proof outline. A term `multDiff s h f x` vanishes unless `f x ≠ 0` and `f (x + h i) ≠ 0`
for all `i`, so the defining family has finite support. For `s = t + 1`, the term at
`(x, h)` is `D x * conj (D (x + h last))` with `D = multDiff t (Fin.init h) f`; summing over
`x` and the last coordinate gives `|∑ D|²`, so the whole sum is a sum over `h' : Fin t → ℤ`
of the nonnegative reals `|∑_x Δ_{h'} f (x)|²`.
-/

public section

open scoped ComplexConjugate

namespace PrimeCarleson.Proof

/-- A nonzero iterated difference forces `f` to be nonzero at `x` and at every `x + h i`. -/
private theorem multDiff_ne_zero (s : ℕ) (h : Fin s → ℤ) (f : ℤ → ℂ) (x : ℤ) :
    multDiff s h f x ≠ 0 → f x ≠ 0 ∧ ∀ i, f (x + h i) ≠ 0 := by
  induction s generalizing x with
  | zero => intro hne; exact ⟨hne, fun i => i.elim0⟩
  | succ s ih =>
    intro hne
    simp only [multDiff, ne_eq, mul_eq_zero, map_eq_zero, not_or] at hne
    obtain ⟨h1, h2⟩ := hne
    have a := ih (Fin.init h) x h1
    have b := ih (Fin.init h) (x + h (Fin.last s)) h2
    refine ⟨a.1, fun i => ?_⟩
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact b.1
    · simpa [Fin.init] using a.2 j

/-- The defining family of the Gowers norm has finitely many nonzero terms. -/
private theorem support_finite (s : ℕ) (f : ℤ →₀ ℂ) :
    (Function.support fun p : ℤ × (Fin s → ℤ) => multDiff s p.2 f p.1).Finite := by
  have hs : (f.support : Set ℤ).Finite := f.support.finite_toSet
  refine ((hs.prod (Set.Finite.pi (t := fun _ : Fin s => (f.support : Set ℤ))
    (fun _ => hs))).image (fun q : ℤ × (Fin s → ℤ) => (q.1, fun i => q.2 i - q.1))).subset ?_
  intro p hp
  have := multDiff_ne_zero s p.2 f p.1 hp
  refine ⟨(p.1, fun i => p.2 i + p.1), ⟨?_, ?_⟩, ?_⟩
  · simpa using this.1
  · intro i _
    simp only [Finset.mem_coe, Finsupp.mem_support_iff]
    have := this.2 i
    rwa [add_comm] at this
  · ext <;> simp

/-- The defining family is summable, as it has finite support. -/
private theorem summable_multDiff (s : ℕ) (f : ℤ →₀ ℂ) :
    Summable (fun p : ℤ × (Fin s → ℤ) => multDiff s p.2 f p.1) :=
  summable_of_hasFiniteSupport (support_finite s f)

/-- Each fixed iterated difference has finite support, hence is absolutely summable. -/
private theorem summable_norm_multDiff (t : ℕ) (f : ℤ →₀ ℂ) (h : Fin t → ℤ) :
    Summable fun x : ℤ => ‖multDiff t h f x‖ := by
  refine summable_of_hasFiniteSupport ?_
  refine f.support.finite_toSet.subset fun x hx => ?_
  have hne : multDiff t h f x ≠ 0 := by simpa using hx
  simpa using (multDiff_ne_zero t h f x hne).1

/-- The reindexing of `ℤ × (Fin (t + 1) → ℤ)` by `(x, h) ↦ (init h, x, x + h last)`. -/
private def reindex (t : ℕ) : ℤ × (Fin (t + 1) → ℤ) ≃ (Fin t → ℤ) × (ℤ × ℤ) where
  toFun p := (Fin.init p.2, (p.1, p.1 + p.2 (Fin.last t)))
  invFun q := (q.2.1, Fin.snoc q.1 (q.2.2 - q.2.1))
  left_inv p := by
    ext
    · rfl
    · simp [Fin.snoc_init_self]
  right_inv q := by
    ext <;> simp [Fin.init_snoc, Fin.snoc_last]

/-- For `s = t + 1` the sum defining the Gowers norm is a nonnegative real number. -/
private theorem tsum_succ_eq_nonneg_real (t : ℕ) (f : ℤ →₀ ℂ) :
    ∃ r : ℝ, 0 ≤ r ∧
      ∑' p : ℤ × (Fin (t + 1) → ℤ), multDiff (t + 1) p.2 f p.1 = (r : ℂ) := by
  let G : (Fin t → ℤ) × (ℤ × ℤ) → ℂ := fun q =>
    multDiff t q.1 f q.2.1 * conj (multDiff t q.1 f q.2.2)
  have hGe : (fun p : ℤ × (Fin (t + 1) → ℤ) => multDiff (t + 1) p.2 f p.1) =
      G ∘ reindex t := by
    funext p
    rfl
  have hG : Summable G := by
    have h := summable_multDiff (t + 1) f
    rw [hGe] at h
    exact (Equiv.summable_iff (reindex t)).1 h
  have hfib : ∀ h' : Fin t → ℤ,
      ∑' c : ℤ × ℤ, G (h', c) =
        ((Complex.normSq (∑' x, multDiff t h' f x) : ℝ) : ℂ) := by
    intro h'
    have hn : Summable fun x : ℤ => ‖conj (multDiff t h' f x)‖ := by
      simpa only [RCLike.norm_conj] using summable_norm_multDiff t f h'
    have := tsum_mul_tsum_of_summable_norm (summable_norm_multDiff t f h') hn
    rw [← Complex.conj_tsum] at this
    rw [Complex.mul_conj] at this
    exact this.symm
  have hsum : ∑' p : ℤ × (Fin (t + 1) → ℤ), multDiff (t + 1) p.2 f p.1 =
      ∑' h' : Fin t → ℤ,
        ((Complex.normSq (∑' x, multDiff t h' f x) : ℝ) : ℂ) := by
    rw [hGe]
    change ∑' p, G (reindex t p) = _
    rw [Equiv.tsum_eq (reindex t) G, hG.tsum_prod]
    exact tsum_congr hfib
  refine ⟨∑' h' : Fin t → ℤ, Complex.normSq (∑' x, multDiff t h' f x),
    tsum_nonneg fun _ => Complex.normSq_nonneg _, ?_⟩
  rw [hsum, Complex.ofReal_tsum]

/-- For `0 < n` the sum defining the Gowers norm is a nonnegative real number. -/
private theorem tsum_eq_nonneg_real (n : ℕ) (hn : 0 < n) (f : ℤ →₀ ℂ) :
    ∃ r : ℝ, 0 ≤ r ∧
      ∑' p : ℤ × (Fin n → ℤ), multDiff n p.2 f p.1 = (r : ℂ) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  exact tsum_succ_eq_nonneg_real t f

/-- The Gowers norm is the source object: the defining sum has finitely many nonzero terms
(so the `tsum` is the genuine sum), the norm is nonnegative, and its `2^s`-th power is the
sum `∑_{x, h₁, …, h_s} Δ_{h₁,…,h_s} f(x)` of (e;GowersDef).

The binders are implicit so that the proof of the statement is the bare assembly
`by exact PrimeCarleson.Proof.gowersNorm_spec`. -/
theorem gowersNorm_spec {s : ℕ+} {f : ℤ →₀ ℂ} :
    (Function.support fun p : ℤ × (Fin s → ℤ) => multDiff s p.2 f p.1).Finite ∧
      0 ≤ gowersNorm s f ∧
      ((gowersNorm s f : ℝ) : ℂ) ^ (2 ^ (s : ℕ)) =
        ∑' p : ℤ × (Fin s → ℤ), multDiff s p.2 f p.1 := by
  obtain ⟨r, hr, hS⟩ := tsum_eq_nonneg_real (s : ℕ) s.pos f
  have hnorm : gowersNorm s f = r ^ ((1 : ℝ) / 2 ^ (s : ℕ)) := by
    unfold gowersNorm
    rw [hS, Complex.ofReal_re]
  refine ⟨support_finite s f, ?_, ?_⟩
  · rw [hnorm]
    exact Real.rpow_nonneg hr _
  · rw [hnorm, hS, ← Complex.ofReal_pow, ← Real.rpow_natCast, ← Real.rpow_mul hr]
    have h2 : (1 : ℝ) / 2 ^ (s : ℕ) * ((2 ^ (s : ℕ) : ℕ) : ℝ) = 1 := by
      push_cast
      field_simp
    rw [h2, Real.rpow_one]

end PrimeCarleson.Proof
