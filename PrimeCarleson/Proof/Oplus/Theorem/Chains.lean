module

public import PrimeCarleson.Proof.Oplus.Theorem.Basic
public import PrimeCarleson.Proof.Common.Variation

/-!
# Chains of increments of `𝒮[f](·, x)` and the reduction to finite sets `Ξ` ([O+] L884-L903)

Source: [O+], L884–L890; [O+] `maintheorem`, L693–L696 (in the amended form used here), L880-L903.

* `chainVar r f t x = (∑_{i} |𝒮[f](t_i, x) - 𝒮[f](t_{i+1}, x)|^r)^{1/r}` for a chain
  `t_0 < ⋯ < t_J`, and `chainSup r f J S x` the supremum over strictly increasing chains with `J`
  steps and nodes in `S` (`G_J(x)` for `S = ℝ`). The `rVariationOn r univ (𝒮[f](·, x))` is
  `sup_J G_J(x)` (`rVariationOn_eq_iSup_chainSup`);
* `chainSup_univ_le_succ`: `G_J ≤ G_{J+1}` ("padding at the end": one more point to the right of
  the last node adds a nonnegative term and splits no increment);
* `chainSup_univ_le_of_dense`: `G_J(x) ≤ sup_n` of the same supremum over the chains in `Ξ_n`, for
  finite sets `Ξ_n ↑ D`, `D` dense: continuity of `ξ ↦ 𝒮[f](ξ, x)` (`continuous_chainVar`);
* `denseShift = {q + √2 : q ∈ ℚ}` (dense, no point of the form `n 2^m`: `avoids_denseShift`) with
  the finite exhaustion `shiftFinset n`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped FourierTransform SchwartzMap ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

open PrimeCarleson PrimeCarleson.Proof.Common

/-- The `ℓ^r` functional of the increments of `ξ ↦ 𝒮[f](ξ, x)` along a chain `t`. -/
def chainVar (r : ℝ) (f : 𝓢(ℝ, ℂ)) {J : ℕ} (t : Fin (J + 1) → ℝ) (x : ℝ) : ℝ≥0∞ :=
  (∑ i : Fin J, ‖partialFourierIntegral f (t i.castSucc) x -
    partialFourierIntegral f (t i.succ) x‖ₑ ^ r) ^ (1 / r)

/-- The supremum of `chainVar` over strictly increasing chains with `J` steps and nodes in `S`. -/
def chainSup (r : ℝ) (f : 𝓢(ℝ, ℂ)) (J : ℕ) (S : Set ℝ) (x : ℝ) : ℝ≥0∞ :=
  ⨆ (t : Fin (J + 1) → ℝ) (_ : StrictMono t) (_ : ∀ i, t i ∈ S), chainVar r f t x

/-- The `rVariationOn` over `ℝ` is `sup_J G_J`. -/
theorem rVariationOn_eq_iSup_chainSup (r : ℝ) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    rVariationOn r univ (fun ξ => partialFourierIntegral f ξ x) =
      ⨆ J, chainSup r f J univ x := rfl

/-- `chainSup` is monotone in the set of admissible nodes. -/
theorem chainSup_mono_set (r : ℝ) (f : 𝓢(ℝ, ℂ)) (J : ℕ) {S T : Set ℝ} (h : S ⊆ T) (x : ℝ) :
    chainSup r f J S x ≤ chainSup r f J T x :=
  iSup_mono fun _ => iSup_mono fun _ => iSup_mono' fun hS => ⟨fun i => h (hS i), le_rfl⟩

/-- A strictly increasing chain with nodes in `S` is bounded by `chainSup`. -/
theorem le_chainSup (r : ℝ) (f : 𝓢(ℝ, ℂ)) {J : ℕ} {S : Set ℝ} {t : Fin (J + 1) → ℝ}
    (ht : StrictMono t) (hS : ∀ i, t i ∈ S) (x : ℝ) : chainVar r f t x ≤ chainSup r f J S x :=
  le_iSup₂_of_le t ht (le_iSup_of_le hS le_rfl)

/-- Padding a chain at the end by one point adds a nonnegative term: `G_J ≤ G_{J+1}`. -/
theorem chainSup_univ_le_succ {r : ℝ} (hr : 0 < r) (f : 𝓢(ℝ, ℂ)) (J : ℕ) (x : ℝ) :
    chainSup r f J univ x ≤ chainSup r f (J + 1) univ x := by
  refine iSup_le fun t => iSup_le fun ht => iSup_le fun _ => ?_
  set y : ℝ := t (Fin.last J) + 1 with hy
  set t' : Fin (J + 2) → ℝ := Fin.snoc (α := fun _ => ℝ) t y with ht'
  have hsm : StrictMono t' := by
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [ht', Fin.succ_last, Fin.snoc_last, Fin.snoc_castSucc, hy]
      linarith
    · simp only [ht', Fin.succ_castSucc, Fin.snoc_castSucc]
      exact ht (Fin.castSucc_lt_succ)
  refine le_trans ?_ (le_chainSup r f hsm (fun _ => mem_univ _) x)
  unfold chainVar
  gcongr
  rw [Fin.sum_univ_castSucc (n := J)]
  refine le_trans (le_of_eq ?_) le_self_add
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [ht', Fin.succ_castSucc, Fin.snoc_castSucc]


/-- `chainVar` is continuous in the chain. -/
theorem continuous_chainVar (r : ℝ) (f : 𝓢(ℝ, ℂ)) (J : ℕ) (x : ℝ) :
    Continuous fun t : Fin (J + 1) → ℝ => chainVar r f t x := by
  unfold chainVar
  have hS : Continuous fun ξ : ℝ => partialFourierIntegral f ξ x :=
    (continuous_partialFourierIntegral_prod f).comp (continuous_id.prodMk continuous_const)
  refine (ENNReal.continuous_rpow_const (y := 1 / r)).comp ?_
  refine continuous_finsetSum _ fun i _ => ?_
  refine (ENNReal.continuous_rpow_const (y := r)).comp ?_
  exact ((hS.comp (continuous_apply _)).sub (hS.comp (continuous_apply _))).enorm

/-- `chainVar` is continuous in `x`. -/
theorem continuous_chainVar_x (r : ℝ) (f : 𝓢(ℝ, ℂ)) {J : ℕ} (t : Fin (J + 1) → ℝ) :
    Continuous fun x => chainVar r f t x := by
  unfold chainVar
  have hS : ∀ ξ : ℝ, Continuous fun x : ℝ => partialFourierIntegral f ξ x := fun ξ =>
    (continuous_partialFourierIntegral_prod f).comp (continuous_const.prodMk continuous_id)
  refine (ENNReal.continuous_rpow_const (y := 1 / r)).comp ?_
  refine continuous_finsetSum _ fun i _ => ?_
  refine (ENNReal.continuous_rpow_const (y := r)).comp ?_
  exact ((hS _).sub (hS _)).enorm

/-- `G_J` is measurable: a supremum of continuous functions is lower semicontinuous. -/
theorem measurable_chainSup (r : ℝ) (f : 𝓢(ℝ, ℂ)) (J : ℕ) (S : Set ℝ) :
    Measurable (chainSup r f J S) := by
  unfold chainSup
  refine LowerSemicontinuous.measurable ?_
  exact lowerSemicontinuous_iSup fun t => lowerSemicontinuous_iSup fun _ =>
    lowerSemicontinuous_iSup fun _ => (continuous_chainVar_x r f t).lowerSemicontinuous

/-- **Density reduction**: if `D` is dense and `Ξ_n ↑ D` are finite sets, the supremum over all
chains in `ℝ` is the supremum over the chains in the `Ξ_n`, by the continuity of `ξ ↦ 𝒮[f](ξ, x)`
([O+] L897-L903). -/
theorem chainSup_univ_le_of_dense (r : ℝ) (f : 𝓢(ℝ, ℂ)) (J : ℕ) (x : ℝ) {D : Set ℝ}
    (hD : Dense D) (Ξ : ℕ → Finset ℝ) (hmono : Monotone Ξ) (hcov : ∀ d ∈ D, ∃ n, d ∈ Ξ n) :
    chainSup r f J univ x ≤ ⨆ n, chainSup r f J (↑(Ξ n)) x := by
  set s : ℝ≥0∞ := ⨆ n, chainSup r f J (↑(Ξ n)) x with hs
  refine iSup_le fun t => iSup_le fun ht => iSup_le fun _ => ?_
  have hT := continuous_chainVar r f J x
  set A : Set (Fin (J + 1) → ℝ) := {t | StrictMono t} with hA
  have hAopen : IsOpen A := by
    have : A = ⋂ i : Fin J, {t : Fin (J + 1) → ℝ | t i.castSucc < t i.succ} := by
      ext t
      simp [hA, Fin.strictMono_iff_lt_succ]
    rw [this]
    exact isOpen_iInter_of_finite fun i => isOpen_lt (continuous_apply _) (continuous_apply _)
  have hQ : Dense (Set.pi univ fun _ : Fin (J + 1) => D) := dense_pi _ fun _ _ => hD
  have hcl : t ∈ closure (A ∩ Set.pi univ fun _ : Fin (J + 1) => D) :=
    hQ.open_subset_closure_inter hAopen ht
  have hmaps : MapsTo (fun t' => chainVar r f t' x) (A ∩ Set.pi univ fun _ => D) (Iic s) := by
    rintro t' ⟨ht'A, ht'Q⟩
    choose n hn using fun i => hcov (t' i) (ht'Q i (mem_univ i))
    obtain ⟨N, hN⟩ : ∃ N, ∀ i, n i ≤ N :=
      ⟨Finset.univ.sup n, fun i => Finset.le_sup (Finset.mem_univ i)⟩
    refine (le_chainSup r f ht'A (fun i => ?_) x).trans
      (le_iSup (fun n => chainSup r f J (↑(Ξ n)) x) N)
    exact Finset.mem_coe.2 (hmono (hN i) (hn i))
  have := map_mem_closure hT hcl hmaps
  rwa [isClosed_Iic.closure_eq] at this


/-- The countable dense set `D = {q + √2 : q ∈ ℚ}` (no point is of the form `n 2^m`). -/
def denseShift : Set ℝ := range fun q : ℚ => (q : ℝ) + √2

/-- The set `{q + √2 : q ∈ ℚ}` is dense. -/
theorem dense_denseShift : Dense denseShift := by
  have h1 : DenseRange fun q : ℚ => (q : ℝ) :=  Rat.denseRange_cast
  have h2 : Continuous fun x : ℝ => x + √2 := continuous_id.add continuous_const
  have h3 : Function.Surjective fun x : ℝ => x + √2 := fun y => ⟨y - √2, by simp⟩
  exact h3.denseRange.comp h1 h2

/-- An enumeration of `ℚ`. -/
def enumRat : ℕ → ℚ := Classical.choose (exists_surjective_nat ℚ)

/-- `enumRat` enumerates `ℚ`. -/
theorem surjective_enumRat : Function.Surjective enumRat :=
  Classical.choose_spec (exists_surjective_nat ℚ)

/-- A finite exhaustion of `D`. -/
def shiftFinset (n : ℕ) : Finset ℝ :=
  (Finset.range n).image fun m => ((enumRat m : ℚ) : ℝ) + √2

/-- The finite sets `shiftFinset n` increase with `n`. -/
theorem monotone_shiftFinset : Monotone shiftFinset := fun _ _ h =>
  Finset.image_subset_image (Finset.range_mono h)

/-- Every point of `D` lies in some `shiftFinset n`. -/
theorem exists_mem_shiftFinset {d : ℝ} (hd : d ∈ denseShift) : ∃ n, d ∈ shiftFinset n := by
  obtain ⟨q, rfl⟩ := hd
  obtain ⟨m, rfl⟩ := surjective_enumRat q
  exact ⟨m + 1, Finset.mem_image.2 ⟨m, Finset.mem_range.2 (Nat.lt_succ_self m), rfl⟩⟩

/-- `shiftFinset n ⊆ D`. -/
theorem shiftFinset_subset (n : ℕ) : (↑(shiftFinset n) : Set ℝ) ⊆ denseShift := by
  intro d hd
  obtain ⟨m, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hd)
  exact ⟨_, rfl⟩

/-- `D` contains no number `n 2^m` (irrationality of `√2`). -/
theorem avoids_denseShift : AvoidsDyadicEndpoints denseShift := by
  rintro _ ⟨q, rfl⟩ n m h
  refine irrational_sqrt_two ⟨(n : ℚ) * 2 ^ m - q, ?_⟩
  push_cast
  linarith

/-- `shiftFinset n` avoids the dyadic end points. -/
theorem avoids_shiftFinset (n : ℕ) : AvoidsDyadicEndpoints (↑(shiftFinset n) : Set ℝ) :=
  fun ξ hξ => avoids_denseShift ξ (shiftFinset_subset n hξ)


end PrimeCarleson.Proof.Oplus
