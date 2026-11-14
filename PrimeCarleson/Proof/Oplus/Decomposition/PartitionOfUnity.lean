module

public import PrimeCarleson.Proof.Oplus.Decomposition.Whitney
public import PrimeCarleson.Proof.Oplus.Defs.Cutoff
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

/-!
# The partition of unity `𝟙_{(ξ,ξ')} f̂ = ∑_{J ∈ 𝒥_{ξ,ξ'}} φ_J f̂` ([O+] L961-L972)

[O+] L961-L972: "we define `φ_J = φ_{J,i(J)}` where `i(J)` is
chosen so that `|J'| = 2^{i(J)}|J|`. Then `𝟙_{(ξ,ξ')}(η) f̂(η) = ∑_{J ∈ 𝒥_{ξ,ξ'}} φ_J(η) f̂(η)`.
Since we assume that `f̂` is compactly supported in `ℝ ∖ Ξ` we see that for every pair `ξ < ξ'`
with `ξ, ξ' ∈ Ξ` only a finite number of dyadic intervals `J ∈ 𝒥_{ξ,ξ'}` are relevant" (the
first identity is asserted with "one may check", not proved).

* `phiW ξ ξ' J = φ_{J,i(J)}` (`phiDyadic J (nbrIdx ξ ξ' J)`);
* `Dyadic.phiW_eq_sub`: `φ_J = F_{J'} - F_J` with the *falling half* `F_K(η) = ν((η - b_K)/|K|)`
  of the left neighbour `J'` (this is the telescoping of the rising half of `φ_J`, at the scale
  `|J'| = 2^{i(J)}|J|`, against the falling half of `φ_{J'}`);
* `Dyadic.phiW_eq_zero_of_ne`: for `η ∈ J₀ ∈ 𝒥_{ξ,ξ'}`, only the three Whitney intervals
  `J₀' , J₀, J₀''` (left neighbour, itself, right neighbour) have `φ_J(η) ≠ 0`
  (the gap lemma of `Whitney.lean`);
* `Dyadic.hasSum_phiW`: **the partition of unity**, for all `ξ, ξ', η` (no assumption on the
  dyadic end points); `hasSum_phiW_mul` with a multiplier `g`;
* `Dyadic.finite_relevant`: finiteness of the relevant intervals, from `ℓ_J ≥ ε/5` (the Whitney
  bound `|J| > dist/3`) and the disjointness of the Whitney intervals.
-/

@[expose] public noncomputable section

open MeasureTheory Set

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

/-- The partition function `φ_J = φ_{J,i(J)}` -/
def phiW (ξ ξ' : ℝ) (J : Dyadic) : ℝ → ℝ := phiDyadic J (Dyadic.nbrIdx ξ ξ' J)

/-- The falling half `η ↦ ν((η - b)/|J|)` -/
def fallFn (J : Dyadic) (η : ℝ) : ℝ := nu ((η - J.right) / J.length)

theorem fallFn_eq_one {J : Dyadic} {η : ℝ} (h : J.right + J.length / 100 ≤ η) : fallFn J η = 1 := by
  apply nu_of_ge
  rw [le_div_iff₀ J.length_pos]
  linarith

theorem fallFn_eq_zero {J : Dyadic} {η : ℝ} (h : η ≤ J.right - J.length / 100) :
    fallFn J η = 0 := by
  apply nu_of_le
  rw [div_le_iff₀ J.length_pos]
  linarith

namespace Dyadic

variable {ξ ξ' η : ℝ} {J K : Dyadic}

theorem phiW_eq_sub (hK : K.IsWhitney ξ ξ') (h : K.right = J.left) :
    phiW ξ ξ' J η = fallFn K η - fallFn J η := by
  have hlen : K.length = 2 ^ nbrIdx ξ ξ' J * J.length := by
    have hk := nbrIdx_eq hK h (J := J)
    unfold length
    rw [show K.k = J.k + nbrIdx ξ ξ' J by omega, zpow_add₀ (by norm_num), mul_comm]
  have hl : J.right - J.left = J.length := by rw [right_eq]; ring
  unfold phiW phiDyadic phiJi fallFn
  rw [hl, h, hlen]

/-- `φ_J` vanishes outside `(ξ, ξ')`: its support lies in the `26/25`-dilate of `J`. -/
theorem phiW_eq_zero_of_not_mem (hJ : J.IsWhitney ξ ξ') (hη : η ∉ Ioo ξ ξ') :
    phiW ξ ξ' J η = 0 := by
  have hi := nbrIdx_mem hJ
  have hsupp := support_phiDyadic_subset (i := nbrIdx ξ ξ' J) hi.2 J
  by_contra hne
  have h1 : η ∈ J.dilate (26 / 25) := hsupp (Function.mem_support.2 hne)
  apply hη
  obtain ⟨hA, hB⟩ := hJ.1
  unfold Dyadic.dilate at h1
  have hc := J.center_eq
  have hr := J.right_eq
  have hL := J.length_pos
  obtain ⟨h1, h2⟩ := h1
  constructor <;> linarith

/-- The key vanishing: for `η ∈ J₀`, `K = J₀'` and `N` the right neighbour of `J₀`, `φ_J(η) = 0`
for every other Whitney interval `J`. -/
theorem phiW_eq_zero_of_ne {J₀ N : Dyadic} (hJ : J.IsWhitney ξ ξ') (hJ₀ : J₀.IsWhitney ξ ξ')
    (hN : N.IsWhitney ξ ξ') (hK : K.IsWhitney ξ ξ') (hη : η ∈ J₀.toSet)
    (hKr : K.right = J₀.left) (hNl : N.left = J₀.right)
    (h1 : J ≠ K) (h2 : J ≠ J₀) (h3 : J ≠ N) : phiW ξ ξ' J η = 0 := by
  obtain ⟨M, hM, hMr, hMlen⟩ := hJ.exists_left_nbr_length
  have hMeq : phiW ξ ξ' J η = fallFn M η - fallFn J η := phiW_eq_sub hM hMr
  obtain ⟨hMl1, hMl2⟩ := hJ.nbr_length_le hM hMr
  have hL := J.length_pos
  have hr := J.right_eq
  have hLM := M.length_pos
  rcases hJ.eq_or_disjoint hJ₀ with h | hd
  · exact absurd h h2
  rcases right_le_left_of_disjoint hd with hle | hle
  · -- `J` lies to the left of `J₀`
    by_contra hne
    have hlt : η < J.right + J.length / 100 := by
      by_contra hge
      rw [not_lt] at hge
      apply hne
      rw [hMeq, fallFn_eq_one hge, fallFn_eq_one (by linarith)]
      ring
    have hgap : J₀.left - J.right < J.length / 50 := by linarith [hη.1]
    have := hJ.left_eq_right_of_gap hJ₀ hle (Or.inl hgap)
    exact h1 (hJ.eq_of_right_eq hK (this.symm.trans hKr.symm))
  · -- `J` lies to the right of `J₀`
    by_contra hne
    have hlt : J.left - η < J.length / 50 := by
      by_contra hge
      rw [not_lt] at hge
      apply hne
      rw [hMeq, fallFn_eq_zero (by linarith), fallFn_eq_zero (by linarith)]
      ring
    have hgap : J.left - J₀.right < J.length / 50 := by linarith [hη.2]
    have := hJ₀.left_eq_right_of_gap hJ hle (Or.inr hgap)
    exact h3 (hJ.eq_of_left_eq hN (this.trans hNl.symm))

/-- **The partition of unity** ([O+] L961-L969): for all `ξ, ξ'` and every
`η`, `∑_{J ∈ 𝒥_{ξ,ξ'}} φ_J(η) = 1_{(ξ,ξ')}(η)`. At most three terms are nonzero. -/
theorem hasSum_phiW (η : ℝ) :
    HasSum ({J : Dyadic | J.IsWhitney ξ ξ'}.indicator (fun J => phiW ξ ξ' J η))
      ((Ioo ξ ξ').indicator (fun _ => (1 : ℝ)) η) := by
  classical
  by_cases hη : η ∈ Ioo ξ ξ'
  · obtain ⟨J₀, hJ₀, hηJ⟩ := exists_isWhitney_mem hη
    obtain ⟨K, hK, hKr⟩ := hJ₀.exists_left_nbr
    obtain ⟨N, hN, hNl⟩ := hJ₀.exists_right_nbr
    obtain ⟨K', hK', hK'r⟩ := hK.exists_left_nbr
    have hKJ : K ≠ J₀ := by
      rintro rfl
      have := K.left_lt_right
      rw [hKr] at this
      exact lt_irrefl _ this
    have hJN : J₀ ≠ N := by
      rintro rfl
      have := J₀.left_lt_right
      rw [hNl] at this
      exact lt_irrefl _ this
    have hKN : K ≠ N := by
      rintro rfl
      have h1 := K.left_lt_right
      have h2 := J₀.left_lt_right
      linarith
    have hsum : HasSum ({J : Dyadic | J.IsWhitney ξ ξ'}.indicator (fun J => phiW ξ ξ' J η))
        (∑ J ∈ ({K, J₀, N} : Finset Dyadic),
          {J : Dyadic | J.IsWhitney ξ ξ'}.indicator (fun J => phiW ξ ξ' J η) J) :=
      hasSum_sum_of_ne_finset_zero (by
        intro J hJ
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hJ
        by_cases hw : J.IsWhitney ξ ξ'
        · rw [Set.indicator_of_mem (show J ∈ {J : Dyadic | J.IsWhitney ξ ξ'} from hw)]
          exact phiW_eq_zero_of_ne hw hJ₀ hN hK hηJ hKr hNl hJ.1 hJ.2.1 hJ.2.2
        · exact Set.indicator_of_notMem (show J ∉ {J : Dyadic | J.IsWhitney ξ ξ'} from hw) _)
    rw [Finset.sum_insert (by simp [hKJ, hKN]), Finset.sum_insert (by simp [hJN]),
      Finset.sum_singleton, Set.indicator_of_mem (show K ∈ {J : Dyadic | J.IsWhitney ξ ξ'} from hK),
      Set.indicator_of_mem (show J₀ ∈ {J : Dyadic | J.IsWhitney ξ ξ'} from hJ₀),
      Set.indicator_of_mem (show N ∈ {J : Dyadic | J.IsWhitney ξ ξ'} from hN)] at hsum
    rw [phiW_eq_sub hK' hK'r, phiW_eq_sub hK hKr,
      phiW_eq_sub (K := J₀) hJ₀ (J := N) hNl.symm] at hsum
    have e1 : fallFn K' η = 1 := by
      apply fallFn_eq_one
      have := hK.nbr_length_le hK' hK'r
      have h3 := K.right_eq
      have h4 := K.length_pos
      have := hηJ.1
      linarith
    have e2 : fallFn N η = 0 := by
      apply fallFn_eq_zero
      have h3 := N.right_eq
      have h4 := N.length_pos
      have := hηJ.2
      linarith
    rw [Set.indicator_of_mem hη]
    convert hsum using 1
    rw [e1, e2]
    ring
  · rw [Set.indicator_of_notMem hη]
    convert hasSum_zero with J
    by_cases hw : J.IsWhitney ξ ξ'
    · rw [Set.indicator_of_mem (show J ∈ {J : Dyadic | J.IsWhitney ξ ξ'} from hw)]
      exact phiW_eq_zero_of_not_mem hw hη
    · exact Set.indicator_of_notMem (show J ∉ {J : Dyadic | J.IsWhitney ξ ξ'} from hw) _

/-- There are only finitely many Whitney intervals of length `≥ c > 0` inside a bounded set. -/
theorem finite_isWhitney_length_ge (ξ ξ' : ℝ) {c : ℝ} (hc : 0 < c) (R : ℝ) :
    {J : Dyadic | J.IsWhitney ξ ξ' ∧ J.toSet ⊆ Icc (-R) R ∧ c ≤ J.length}.Finite := by
  classical
  let As : Dyadic → Set ℝ := fun J =>
    if J.IsWhitney ξ ξ' ∧ J.toSet ⊆ Icc (-R) R then J.toSet else ∅
  have hmble : ∀ J, MeasurableSet (As J) := fun J => by
    by_cases h : J.IsWhitney ξ ξ' ∧ J.toSet ⊆ Icc (-R) R
    · simp only [As, h, and_self, ↓reduceIte]; exact J.measurableSet_toSet
    · simp only [As, h, ↓reduceIte]; exact MeasurableSet.empty
  have hdisj : Pairwise (Function.onFun Disjoint As) := by
    intro J K hJK
    by_cases hJ : J.IsWhitney ξ ξ' ∧ J.toSet ⊆ Icc (-R) R
    · by_cases hK : K.IsWhitney ξ ξ' ∧ K.toSet ⊆ Icc (-R) R
      · simp only [Function.onFun, As, hJ, hK, and_self, ↓reduceIte]
        exact (hJ.1.eq_or_disjoint hK.1).resolve_left hJK
      · simp only [Function.onFun, As, hK, ↓reduceIte]; exact Set.disjoint_empty _
    · simp only [Function.onFun, As, hJ, ↓reduceIte]; exact Set.empty_disjoint _
  have hunion : volume (⋃ J, As J) ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt (measure_mono (Set.iUnion_subset fun J => ?_))
      (show volume (Icc (-R) R) < ⊤ from by simp))
    by_cases h : J.IsWhitney ξ ξ' ∧ J.toSet ⊆ Icc (-R) R
    · simp only [As, h, and_self, ↓reduceIte]
    · simp only [As, h, ↓reduceIte]; exact Set.empty_subset _
  refine (Measure.finite_const_le_meas_of_disjoint_iUnion volume
    (ε := ENNReal.ofReal c) (by simpa using hc) hmble hdisj hunion).subset ?_
  rintro J ⟨hJ, hJR, hJc⟩
  change _ ≤ volume (As J)
  have h : J.IsWhitney ξ ξ' ∧ J.toSet ⊆ Icc (-R) R := ⟨hJ, hJR⟩
  simp only [As, h, and_self, ↓reduceIte]
  rw [Dyadic.volume_toSet]
  exact ENNReal.ofReal_le_ofReal hJc

/-- **Only finitely many Whitney intervals are relevant** ([O+] L970-L972): if `g` has compact
support
and `ξ, ξ' ∉ tsupport g` then only finitely many `J ∈ 𝒥_{ξ,ξ'}` have `φ_J g` not identically
zero. -/
theorem finite_relevant {g : ℝ → ℂ} (hg : HasCompactSupport g) (hξ : ξ ∉ tsupport g)
    (hξ' : ξ' ∉ tsupport g) :
    {J : Dyadic | J.IsWhitney ξ ξ' ∧ ∃ η, ((phiW ξ ξ' J η : ℝ) : ℂ) * g η ≠ 0}.Finite := by
  obtain ⟨R₀, hR₀⟩ := hg.isCompact.isBounded.subset_closedBall (0 : ℝ)
  obtain ⟨ε₁, hε₁, hb₁⟩ := Metric.isOpen_iff.1 (isClosed_tsupport g).isOpen_compl ξ hξ
  obtain ⟨ε₂, hε₂, hb₂⟩ := Metric.isOpen_iff.1 (isClosed_tsupport g).isOpen_compl ξ' hξ'
  set ε := min ε₁ ε₂ with hε
  have hεpos : 0 < ε := lt_min hε₁ hε₂
  set Rbd := R₀ + 2 * |ξ' - ξ| with hRbd
  refine (finite_isWhitney_length_ge ξ ξ' (c := ε / 5) (by positivity) Rbd).subset ?_
  rintro J ⟨hJ, η, hη⟩
  have hgη : g η ≠ 0 := right_ne_zero_of_mul hη
  have hφη : phiW ξ ξ' J η ≠ 0 := by
    intro h; apply hη; simp [h]
  have hmem : η ∈ J.dilate (26 / 25) :=
    support_phiDyadic_subset (nbrIdx_mem hJ).2 J (Function.mem_support.2 hφη)
  have hts : η ∈ tsupport g := subset_tsupport _ (Function.mem_support.2 hgη)
  have hηR : |η| ≤ R₀ := by simpa using hR₀ hts
  have hn1 : ε ≤ |η - ξ| := by
    by_contra h
    rw [not_le] at h
    exact (hb₁ (show η ∈ Metric.ball ξ ε₁ from by
      rw [Metric.mem_ball, Real.dist_eq]; exact lt_of_lt_of_le h (min_le_left _ _))) hts
  have hn2 : ε ≤ |η - ξ'| := by
    by_contra h
    rw [not_le] at h
    exact (hb₂ (show η ∈ Metric.ball ξ' ε₂ from by
      rw [Metric.mem_ball, Real.dist_eq]; exact lt_of_lt_of_le h (min_le_right _ _))) hts
  obtain ⟨hA, hB⟩ := hJ.1
  have hL := J.length_pos
  have hr := J.right_eq
  have hc := J.center_eq
  unfold Dyadic.dilate at hmem
  obtain ⟨hm1, hm2⟩ := hmem
  have hLL : 3 * J.length ≤ |ξ' - ξ| := by
    have := le_abs_self (ξ' - ξ)
    linarith
  refine ⟨hJ, ?_, ?_⟩
  · intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    have h1 := abs_le.1 hηR
    constructor <;> linarith [abs_nonneg (ξ' - ξ), le_abs_self (ξ' - ξ)]
  · rcases hJ.wall_lt with w | w
    · have h1 : 0 < η - ξ := by linarith
      rw [abs_of_pos h1] at hn1
      linarith
    · have h1 : 0 < ξ' - η := by linarith
      rw [abs_sub_comm, abs_of_pos h1] at hn2
      linarith

/-- The partition of unity multiplied by a function `g` (the multiplier `f̂`):
`1_{(ξ,ξ')}(η) g(η) = ∑_{J ∈ 𝒥_{ξ,ξ'}} φ_J(η) g(η)`. -/
theorem hasSum_phiW_mul (g : ℝ → ℂ) (η : ℝ) :
    HasSum ({J : Dyadic | J.IsWhitney ξ ξ'}.indicator (fun J => ((phiW ξ ξ' J η : ℝ) : ℂ) * g η))
      ((Ioo ξ ξ').indicator (fun _ => (1 : ℂ)) η * g η) := by
  have h := (hasSum_phiW (ξ := ξ) (ξ' := ξ') η).mapL Complex.ofRealCLM
  have h2 := h.mul_right (g η)
  convert h2 using 1
  · funext J
    by_cases hw : J.IsWhitney ξ ξ'
    · simp [Set.indicator_of_mem (show J ∈ {J : Dyadic | J.IsWhitney ξ ξ'} from hw)]
    · simp [Set.indicator_of_notMem (show J ∉ {J : Dyadic | J.IsWhitney ξ ξ'} from hw)]
  · by_cases hη : η ∈ Ioo ξ ξ' <;> simp [hη]

end Dyadic

end PrimeCarleson.Proof.Oplus
