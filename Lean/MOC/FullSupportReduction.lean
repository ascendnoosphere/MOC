import MOC.CircleSpectra
import MOC.Householder
import MOC.SpectralPerturbation

/-! A strict violation at fixed spectra persists at a unitary with no zero entries. -/

open BigOperators Matrix
open scoped Topology

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem move_one_entry {O : Set (Matrix ι ι ℂ)} (hO : IsOpen O)
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) (hu : U ∈ O) (i j : ι) :
    ∃ V ∈ O, IsUnitary V ∧ V i j ≠ 0 := by
  classical
  by_cases hz : U i j = 0
  · have hex : ∃ k, U k j ≠ 0 := by
      by_contra! h
      have hd := congrArg (fun M : Matrix ι ι ℂ => M j j) hU.2
      simpa [Matrix.mul_apply, h] using hd
    obtain ⟨k, hk⟩ := hex
    have hik : i ≠ k := fun h => hk (h ▸ hz)
    let c : ℂ := ⟨1/2, 1/2⟩
    have hc : star c * c = (1/2 : ℂ) := by
      apply Complex.ext <;> norm_num [c, Complex.star_def, Complex.mul_re, Complex.mul_im]
    let v (l : ι) : ℂ := if l = i ∨ l = k then c else 0
    have hsum (l : ι) : star (v l) * v l =
        (if l = i then (1/2 : ℂ) else 0) + (if l = k then (1/2 : ℂ) else 0) := by
      by_cases hi : l = i <;> by_cases hl : l = k <;> simp_all [v]
    have hv : ∑ l, star (v l) * v l = 1 := by
      simp only [hsum, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      norm_num
    let P := vecMulVec v (star ∘ v)
    have hprod : (P * U) i j = (1/2 : ℂ) * U k j := by
      rw [Matrix.mul_apply, Finset.sum_eq_single k]
      · simp only [P, Matrix.vecMulVec_apply, Function.comp_apply]
        have hcc : c * star c = (1/2 : ℂ) := (mul_comm _ _).trans hc
        change v i * star (v k) * U k j = (1/2 : ℂ) * U k j
        rw [show v i = c by simp [v], show v k = c by simp [v], hcc]
      · intro l _ hl
        by_cases hi : l = i
        · subst l
          rw [hz, mul_zero]
        · simp [P, Matrix.vecMulVec_apply, v, hi, hl]
      · simp
    let V (t : ℝ) := rankOnePhase v (circleRotation t) * U
    have hrot : circleRotation 0 = 1 := by simp [circleRotation]
    have hzero : V 0 = U := by simp [V, rankOnePhase, hrot]
    have hcont : Continuous V := by
      change Continuous fun t : ℝ =>
        ((1 : Matrix ι ι ℂ) + (circleRotation t - 1) • P) * U
      exact (continuous_const.add ((continuous_circleRotation.sub continuous_const).smul
        continuous_const)).mul continuous_const
    have hnear : ∀ᶠ t in 𝓝[≠] (0 : ℝ), V t ∈ O :=
      (hcont.continuousAt.eventually_mem (hO.mem_nhds (by simpa only [hzero] using hu : V 0 ∈ O))).filter_mono
        nhdsWithin_le_nhds
    obtain ⟨t, ht, ht0⟩ := (hnear.and self_mem_nhdsWithin).exists
    have hphase : IsUnitary (rankOnePhase v (circleRotation t)) :=
      rankOnePhase_unitary v _ hv (by
        rw [Complex.star_def, Complex.mul_conj, circleRotation_normSq]
        simp)
    have hadj : IsUnitary (rankOnePhase v (circleRotation t))ᴴ :=
      ⟨by simpa using hphase.2, by simpa using hphase.1⟩
    refine ⟨V t, ht, ?_, ?_⟩
    · simpa only [V, Matrix.conjTranspose_conjTranspose] using relative_unitary _ U hadj hU
    · have ht' : circleRotation t ≠ 1 :=
        fun h => ht0 (circleRotation_injective (h.trans hrot.symm))
      change (((1 : Matrix ι ι ℂ) + (circleRotation t - 1) • P) * U) i j ≠ 0
      rw [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.add_apply, Matrix.smul_apply,
        hz, zero_add, hprod, smul_eq_mul]
      exact mul_ne_zero (sub_ne_zero.mpr ht') (mul_ne_zero (by norm_num) hk)
  · exact ⟨U, hu, hU, hz⟩

/-- Every neighborhood of a unitary contains a unitary with every entry nonzero. -/
theorem exists_full_support_unitary_mem_open {O : Set (Matrix ι ι ℂ)} (hO : IsOpen O)
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) (hu : U ∈ O) :
    ∃ V ∈ O, IsUnitary V ∧ ∀ i j, V i j ≠ 0 := by
  classical
  have hfinite (s : Finset (ι × ι)) :
      ∃ V ∈ O, IsUnitary V ∧ ∀ p ∈ s, V p.1 p.2 ≠ 0 := by
    induction s using Finset.induction_on with
    | empty => exact ⟨U, hu, hU, by simp⟩
    | @insert p s hp ih =>
      obtain ⟨V, hV, hunit, hs⟩ := ih
      let T (k : {q // q ∈ s}) : Set (Matrix ι ι ℂ) := {W | W k.val.1 k.val.2 ≠ 0}
      have hT (k) : IsOpen (T k) := isOpen_ne_fun (by fun_prop) continuous_const
      have hVT : V ∈ ⋂ k, T k := Set.mem_iInter.mpr fun k => hs _ k.property
      obtain ⟨W, hw, huW, hpW⟩ := move_one_entry (hO.inter (isOpen_iInter_of_finite hT))
        V hunit ⟨hV, hVT⟩ p.1 p.2
      refine ⟨W, hw.1, huW, ?_⟩
      intro q hq
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact hpW
      · exact Set.mem_iInter.mp hw.2 ⟨q, hq⟩
  obtain ⟨V, hV, hunit, he⟩ := hfinite Finset.univ
  exact ⟨V, hV, hunit, fun i j => he (i,j) (Finset.mem_univ _)⟩

/-- At fixed spectra, verifying all unitaries with nonzero entries suffices. -/
theorem holds_all_unitaries_iff_full_support (a b : ι → ℂ) :
    (∀ U : Matrix ι ι ℂ, IsUnitary U → Holds a b U) ↔
      ∀ U : Matrix ι ι ℂ, IsUnitary U → (∀ i j, U i j ≠ 0) → Holds a b U := by
  constructor
  · exact fun h U hU _ => h U hU
  · intro h U hU
    by_contra hf
    have hc : IsClosed {V : Matrix ι ι ℂ | Holds a b V} := by
      exact (Set.finite_range (matchingProduct a b)).isClosed_convexHull.preimage
        (show Continuous (determinantValue a b) by unfold determinantValue; fun_prop)
    obtain ⟨V, hV, hunit, he⟩ := exists_full_support_unitary_mem_open hc.isOpen_compl U hU hf
    exact hV (h V hunit he)

/-- The unrestricted conjecture can be checked with nonzero pair sums, distinct
matching products, and no zero entries in the relative unitary, at the same time. -/
theorem conjecture_iff_regular_spectra_full_support :
    Conjecture ι ↔ ∀ (a b : ι → ℂ) (U : Matrix ι ι ℂ), IsUnitary U →
      (∀ i j, a i + b j ≠ 0) → Function.Injective (matchingProduct a b) →
      (∀ i j, U i j ≠ 0) → Holds a b U := by
  constructor
  · exact fun h a b U hU _ _ _ => h a b U hU
  · intro h
    apply conjecture_iff_regular_matching_products.mpr
    intro a b U hU hn hi
    exact (holds_all_unitaries_iff_full_support a b).mpr
      (fun V hV he => h a b V hV hn hi he) U hU

end

end MOC
