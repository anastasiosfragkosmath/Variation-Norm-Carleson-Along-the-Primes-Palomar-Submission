module

public import PrimeCarleson.Proof.Paper.P6a.Basic
public import PrimeCarleson.Proof.Paper.P6a.Series
public import PrimeCarleson.Proof.Paper.P7.Young
public import PrimeCarleson.Frozen.CarlesonMax

/-!
# The maximal operator `sup_λ |∑_n f(x-n) u(n) e(λ n)|` and its basic API

Source: main paper `s:red`, L1521–L1528 (the maximal endpoint of `p:red-var`, and the root
`t:carmax`).

The paper says only that the proof of `p:red-var` "carries over with every `V^r`-norm replaced by
a supremum over `λ`". This file is the maximal counterpart of `P6a/Basic.lean`:

* `supOp u f x = sup_{λ ∈ [0,1)} |∑_n f(x - n) u(n) e(λ n)|` (the analogue of `varOp`), subadditive
  in the weight `u` and in `f`, with the sign, constant and modulation invariances;
* `carlesonMax_vonMangoldt_eq_supOp`: the `carlesonMax` for `Λ` is `supOp hilbW`;
* the elementary `ℓ^p` bound by the `ℓ¹` norm of the weight (`eLpNorm_supOp_le`: Young's
  inequality, `sup_λ |T_λ f| ≤ |f| * |u|`).
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Goal0

/-! ### Definition and first properties -/

/-- The maximal operator `sup_{λ ∈ 𝕋} |∑_n f(x - n) u(n) e(λ n)|` of a weight `u` (`𝕋 = [0, 1)`);
the maximal counterpart of `varOp`, in the shape of the `carlesonMax`. -/
def supOp (u f : ℤ → ℂ) (x : ℤ) : ℝ≥0∞ :=
  ⨆ lam ∈ Set.Ico (0 : ℝ) 1, ‖weightedModSum u f lam x‖ₑ

/-- Each value of the modulated sum, `λ ∈ [0, 1)`, is at most the maximal operator. -/
theorem enorm_weightedModSum_le_supOp (u f : ℤ → ℂ) {lam : ℝ} (hlam : lam ∈ Set.Ico (0 : ℝ) 1)
    (x : ℤ) : ‖weightedModSum u f lam x‖ₑ ≤ supOp u f x :=
  le_iSup₂ (f := fun lam (_ : lam ∈ Set.Ico (0 : ℝ) 1) => ‖weightedModSum u f lam x‖ₑ) lam hlam

/-- A bound for every `λ ∈ [0, 1)` bounds the maximal operator. -/
theorem supOp_le {u f : ℤ → ℂ} {x : ℤ} {c : ℝ≥0∞}
    (h : ∀ lam ∈ Set.Ico (0 : ℝ) 1, ‖weightedModSum u f lam x‖ₑ ≤ c) : supOp u f x ≤ c :=
  iSup₂_le h

/-- The maximal operator of the zero weight vanishes. -/
theorem supOp_zero_weight (f : ℤ → ℂ) (x : ℤ) : supOp 0 f x = 0 := by
  simp [supOp, weightedModSum_zero_weight]

/-- `supOp` is subadditive in the weight (finitely supported `f`). -/
theorem supOp_add_weight_le (u v : ℤ → ℂ) (f : ℤ →₀ ℂ) (x : ℤ) :
    supOp (u + v) (⇑f) x ≤ supOp u (⇑f) x + supOp v (⇑f) x := by
  refine supOp_le fun lam hlam => ?_
  rw [weightedModSum_add_weight]
  exact (enorm_add_le _ _).trans (add_le_add (enorm_weightedModSum_le_supOp _ _ hlam x)
    (enorm_weightedModSum_le_supOp _ _ hlam x))

/-- `supOp` of a finite sum of weights is at most the sum of the `supOp`'s. -/
theorem supOp_sum_weight_le {ι : Type*} (s : Finset ι) (u : ι → ℤ → ℂ) (f : ℤ →₀ ℂ) (x : ℤ) :
    supOp (fun n => ∑ i ∈ s, u i n) (⇑f) x ≤ ∑ i ∈ s, supOp (u i) (⇑f) x := by
  refine supOp_le fun lam hlam => ?_
  rw [weightedModSum_sum_weight]
  exact (enorm_sum_le _ _).trans (Finset.sum_le_sum fun i _ =>
    enorm_weightedModSum_le_supOp _ _ hlam x)

/-- `supOp` does not see the sign of the weight. -/
theorem supOp_neg_weight (u : ℤ → ℂ) (f : ℤ →₀ ℂ) (x : ℤ) :
    supOp (fun n => -u n) (⇑f) x = supOp u (⇑f) x := by
  simp only [supOp, weightedModSum_neg_weight, enorm_neg]

/-- `supOp` only depends on the weight at the points of `suppAt f x`. -/
theorem supOp_congr_of_finsupp {u v : ℤ → ℂ} (f : ℤ →₀ ℂ) (x : ℤ)
    (h : ∀ n ∈ suppAt f x, u n = v n) : supOp u (⇑f) x = supOp v (⇑f) x := by
  unfold supOp
  refine iSup_congr fun lam => iSup_congr fun _ => ?_
  rw [weightedModSum_eq_sum_of_finsupp, weightedModSum_eq_sum_of_finsupp]
  congr 1
  exact Finset.sum_congr rfl fun n hn => by rw [h n hn]

/-- The modulated sum is homogeneous in a constant factor of the weight. -/
theorem weightedModSum_const_mul_sup (c : ℂ) (v f : ℤ → ℂ) (lam : ℝ) (x : ℤ) :
    weightedModSum (fun n => c * v n) f lam x = c * weightedModSum v f lam x := by
  unfold weightedModSum
  rw [← tsum_mul_left]
  exact tsum_congr fun n => by ring

/-- Homogeneity of `supOp` in a constant factor of the weight. -/
theorem supOp_const_mul_le (c : ℂ) (v f : ℤ → ℂ) (x : ℤ) :
    supOp (fun n => c * v n) f x ≤ ‖c‖ₑ * supOp v f x := by
  refine supOp_le fun lam hlam => ?_
  rw [weightedModSum_const_mul_sup, enorm_mul]
  exact mul_le_mul' le_rfl (enorm_weightedModSum_le_supOp _ _ hlam x)

/-- `supOp` is subadditive in `f` (finitely supported). -/
theorem supOp_add_left_le (u : ℤ → ℂ) (f g : ℤ →₀ ℂ) (x : ℤ) :
    supOp u (⇑(f + g)) x ≤ supOp u (⇑f) x + supOp u (⇑g) x := by
  refine supOp_le fun lam hlam => ?_
  rw [weightedModSum_add_left]
  exact (enorm_add_le _ _).trans (add_le_add (enorm_weightedModSum_le_supOp _ _ hlam x)
    (enorm_weightedModSum_le_supOp _ _ hlam x))

/-! ### Modulation invariance (periodicity in `λ`) -/

/-- A character factor of the weight shifts `λ`: `T^{g e(c ·)}_λ = T^g_{λ + c}`. -/
theorem weightedModSum_mul_e (g f : ℤ → ℂ) (c lam : ℝ) (x : ℤ) :
    weightedModSum (fun n => g n * e (c * n)) f lam x = weightedModSum g f (lam + c) x := by
  unfold weightedModSum
  refine tsum_congr fun n => ?_
  have h : e ((lam + c) * n) = e (c * n) * e (lam * n) := by
    rw [← e_add]; congr 1; ring
  rw [h]; ring

/-- By periodicity every value `T^g_μ f(x)` is a value at some `λ ∈ [0, 1)`. -/
theorem exists_mem_Ico_weightedModSum_eq (g f : ℤ → ℂ) (mu : ℝ) (x : ℤ) :
    ∃ lam ∈ Set.Ico (0 : ℝ) 1, weightedModSum g f mu x = weightedModSum g f lam x := by
  refine ⟨Int.fract mu, ⟨Int.fract_nonneg mu, Int.fract_lt_one mu⟩, ?_⟩
  have h : mu = Int.fract mu + (⌊mu⌋ : ℤ) := (Int.fract_add_floor mu).symm
  conv_lhs => rw [h]
  exact weightedModSum_add_intCast g f _ _ x

/-- The maximal operator does not see a character factor of the weight (one direction). -/
theorem supOp_mul_e_le (g f : ℤ → ℂ) (c : ℝ) (x : ℤ) :
    supOp (fun n => g n * e (c * n)) f x ≤ supOp g f x := by
  refine supOp_le fun lam hlam => ?_
  rw [weightedModSum_mul_e]
  obtain ⟨lam', hlam', h⟩ := exists_mem_Ico_weightedModSum_eq g f (lam + c) x
  rw [h]
  exact enorm_weightedModSum_le_supOp g f hlam' x

/-- **Modulation invariance**: `sup_λ |T^{g e(c ·)}_λ f(x)| = sup_λ |T^g_λ f(x)|`
(`λ ↦ T^g_λ f(x)` is `1`-periodic). -/
theorem supOp_mul_e (g f : ℤ → ℂ) (c : ℝ) (x : ℤ) :
    supOp (fun n => g n * e (c * n)) f x = supOp g f x := by
  refine le_antisymm (supOp_mul_e_le g f c x) ?_
  have h := supOp_mul_e_le (fun n => g n * e (c * n)) f (-c) x
  have h2 : (fun n : ℤ => g n * e (c * n) * e (-c * n)) = g := by
    funext n
    rw [mul_assoc, ← e_add]
    have : c * (n : ℝ) + -c * n = 0 := by ring
    rw [this, e_zero, mul_one]
  rw [h2] at h
  exact h

/-! ### The operator -/

/-- **The `carlesonMax` for `Λ` is `supOp` of the weight `w(n)/n`** (`e:CP`). -/
theorem carlesonMax_vonMangoldt_eq_supOp (f : ℤ →₀ ℂ) (x : ℤ) :
    carlesonMax (ArithmeticFunction.vonMangoldt : ℕ → ℝ) f x = supOp hilbW (⇑f) x := by
  unfold carlesonMax supOp
  refine iSup_congr fun lam => iSup_congr fun _ => ?_
  rw [modulatedSum_vonMangoldt_eq_hilbW]

/-- `C^Q = supOp (w_Q K_Q)`. -/
theorem CQ_eq_supOp (S : KQSetup) (Q : ℕ) (f : ℤ → ℂ) (x : ℤ) :
    S.CQ Q f x = supOp (fun n => wQ Q n * S.KQz Q n) f x := rfl

/-! ### The `ℓ¹` bound -/

/-- **Young's inequality for an `ℝ≥0∞`-valued majorant**: if `G ≤ ∑_n |c(n)| |f(x - n)|` pointwise,
then `‖G‖_{ℓ^p} ≤ ‖c‖_{ℓ¹} ‖f‖_{ℓ^p}` for `1 ≤ p`. -/
theorem eLpNorm_count_le_conv {p : ℝ} (hp : 1 ≤ p) (f c : ℤ → ℂ) (G : ℤ → ℝ≥0∞)
    (hG : ∀ x, G x ≤ ∑' n : ℤ, ‖c n‖ₑ * ‖f (x - n)‖ₑ) :
    eLpNorm G (ENNReal.ofReal p) Measure.count ≤
      (∑' n : ℤ, ‖c n‖ₑ) * eLpNorm f (ENNReal.ofReal p) Measure.count := by
  have hp0 : 0 < p := by linarith
  have hdom : ∀ x : ℤ, G x ≤ ⨆ F : Finset ℤ, ∑ n ∈ F, ‖c n‖ₑ * ‖f (x - n)‖ₑ := fun x =>
    (hG x).trans (by rw [ENNReal.tsum_eq_iSup_sum])
  refine (eLpNorm_count_mono_enn hdom _).trans ?_
  refine (eLpNorm_count_iSup_le hp0 ?_).trans (iSup_le fun F => ?_)
  · intro F₁ F₂
    refine ⟨F₁ ∪ F₂, fun x => ⟨?_, ?_⟩⟩
    · exact Finset.sum_le_sum_of_subset Finset.subset_union_left
    · exact Finset.sum_le_sum_of_subset Finset.subset_union_right
  · calc eLpNorm (fun x : ℤ => ∑ n ∈ F, ‖c n‖ₑ * ‖f (x - n)‖ₑ) (ENNReal.ofReal p) Measure.count
        ≤ ∑ n ∈ F, eLpNorm (fun x : ℤ => ‖c n‖ₑ * ‖f (x - n)‖ₑ) (ENNReal.ofReal p)
            Measure.count := eLpNorm_count_finset_sum_le F _ hp
      _ = ∑ n ∈ F, ‖c n‖ₑ * eLpNorm f (ENNReal.ofReal p) Measure.count := by
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [eLpNorm_count_const_mul _ _ hp0]
          congr 1
          exact (eLpNorm_count_translate hp0 (fun x => ‖f x‖ₑ) n).trans
            (eLpNorm_enorm _ StronglyMeasurable.of_discrete.aestronglyMeasurable)
      _ = (∑ n ∈ F, ‖c n‖ₑ) * eLpNorm f (ENNReal.ofReal p) Measure.count :=
          (Finset.sum_mul _ _ _).symm
      _ ≤ (∑' n : ℤ, ‖c n‖ₑ) * eLpNorm f (ENNReal.ofReal p) Measure.count :=
          mul_le_mul' (ENNReal.sum_le_tsum _) le_rfl

/-- `‖e(t)‖ₑ = 1`. -/
theorem enorm_e_eq_one (t : ℝ) : ‖e t‖ₑ = 1 := by
  rw [← ofReal_norm, norm_e]
  simp

/-- The pointwise bound `sup_λ |T^u_λ f(x)| ≤ ∑_n |f(x - n)| |u(n)|`. -/
theorem supOp_le_tsum (u f : ℤ → ℂ) (x : ℤ) :
    supOp u f x ≤ ∑' n : ℤ, ‖u n‖ₑ * ‖f (x - n)‖ₑ := by
  refine supOp_le fun lam _ => ?_
  unfold weightedModSum
  refine enorm_tsum_le_tsum_enorm.trans (le_of_eq (tsum_congr fun n => ?_))
  rw [enorm_mul, enorm_mul, enorm_e_eq_one, mul_one, mul_comm]

/-- **`ℓ^p` bound by the `ℓ¹` norm of the weight** (`1 ≤ p`):
`‖sup_λ |∑_n f(x-n) u(n) e(λ n)|‖_{ℓ^p} ≤ ‖u‖_{ℓ¹} ‖f‖_{ℓ^p}`. -/
theorem eLpNorm_supOp_le {p : ℝ} (hp : 1 ≤ p) (u f : ℤ → ℂ) :
    eLpNorm (supOp u f) (ENNReal.ofReal p) Measure.count ≤
      (∑' n : ℤ, ‖u n‖ₑ) * eLpNorm f (ENNReal.ofReal p) Measure.count :=
  eLpNorm_count_le_conv hp f u _ (supOp_le_tsum u f)

end PrimeCarleson.Proof.Paper
