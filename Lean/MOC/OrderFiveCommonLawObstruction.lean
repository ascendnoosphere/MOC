import MOC.OrderFivePairMarkers
import MOC.HouseholderSupport

/-! Drury demonstrates compound-law failure for an order-five Householder
reflection in *OMC for Householder reflections*, DOI: 10.1016/S0024-3795(99)00173-1.
The proof here uses a bound on the number of moved labels. -/

open Matrix Finset BigOperators

namespace MOC

noncomputable section

private def flatFiveVector (_ : Fin 5) : ℂ := (Real.sqrt (1 / 5) : ℝ)

/-- The reflection across the orthogonal complement of the constant vector. -/
def orderFiveFlatReflection : Matrix (Fin 5) (Fin 5) ℂ :=
  rankOnePhase flatFiveVector (-1)

private theorem flatFiveVector_product (i j : Fin 5) :
    flatFiveVector i * star (flatFiveVector j) = (1 / 5 : ℂ) := by
  have h : Real.sqrt (1 / 5) * Real.sqrt (1 / 5) = (1 / 5 : ℝ) :=
    Real.mul_self_sqrt (by norm_num)
  simp only [flatFiveVector, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
  rw [h]
  push_cast
  rfl

private theorem flatFiveVector_unit : ∑ i, star (flatFiveVector i) * flatFiveVector i = 1 := by
  simp_rw [mul_comm (star (flatFiveVector _)), flatFiveVector_product]
  norm_num [Finset.sum_const, Fintype.card_fin]

theorem unitary_orderFiveFlatReflection : IsUnitary orderFiveFlatReflection :=
  rankOnePhase_unitary flatFiveVector (-1) flatFiveVector_unit (by norm_num)

/-- The same reflection satisfies each spectral objective individually, even
though no positive law represents all objectives at once. -/
theorem orderFiveFlatReflection_holds (a b : Fin 5 → ℂ) :
    Holds a b orderFiveFlatReflection :=
  holds_householder a b flatFiveVector flatFiveVector_unit

private theorem orderFiveFlatReflection_entry (i j : Fin 5) :
    orderFiveFlatReflection i j = if i = j then (3 / 5 : ℂ) else -2 / 5 := by
  unfold orderFiveFlatReflection rankOnePhase
  rw [Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, vecMulVec_apply]
  change (if i = j then 1 else 0) + (-1 - 1) * (flatFiveVector i * star (flatFiveVector j)) = _
  rw [flatFiveVector_product]
  split <;> norm_num

private theorem flatReflection_disjoint_minor (I J : Finset (Fin 5))
    (hI : I.card = 2) (hJ : J.card = 2) (hd : Disjoint I J) :
    subsetMinorSq orderFiveFlatReflection I J = 0 := by
  classical
  let e : Fin 2 ≃ I := Fintype.equivOfCardEq (by simp [hI])
  let f : Fin 2 ≃ J := Fintype.equivOfCardEq (by simp [hJ])
  rw [subsetMinorSq_eq_normSq_det_submatrix _ unitary_orderFiveFlatReflection I J e f]
  let A := orderFiveFlatReflection.submatrix (Subtype.val ∘ e) (Subtype.val ∘ f)
  have hA (r s : Fin 2) : A r s = (-2 / 5 : ℂ) := by
    change orderFiveFlatReflection (e r).val (f s).val = _
    rw [orderFiveFlatReflection_entry, if_neg]
    intro he
    exact Finset.disjoint_left.mp hd (e r).property (he ▸ (f s).property)
  have hz : A.det = 0 := Matrix.det_zero_of_row_eq (by decide : (0 : Fin 2) ≠ 1)
    (funext fun i => (hA 0 i).trans (hA 1 i).symm)
  change Complex.normSq A.det = 0
  simp [hz]

private theorem flatReflection_singleton_minor (i : Fin 5) :
    subsetMinorSq orderFiveFlatReflection {i} {i} = (9 / 25 : ℝ) := by
  classical
  let e : Fin 1 ≃ ({i} : Finset (Fin 5)) := Fintype.equivOfCardEq (by simp)
  rw [subsetMinorSq_eq_normSq_det_submatrix _ unitary_orderFiveFlatReflection _ _ e e,
    Matrix.det_fin_one]
  have hi : (e 0).val = i := Finset.mem_singleton.mp (e 0).property
  simp only [Matrix.submatrix_apply, Function.comp_apply, hi,
    orderFiveFlatReflection_entry, if_pos rfl, ite_true]
  rw [show (3 / 5 : ℂ) = ((3 / 5 : ℝ) : ℂ) by push_cast; rfl]
  rw [Complex.normSq_ofReal]
  norm_num

/-- Four moved points force a disjoint image of a pair: after choosing one
moved point, avoid itself and its successor and predecessor. -/
theorem exists_disjoint_pair_image_of_four_moved {ι : Type*} [Fintype ι] [DecidableEq ι]
    (σ : Equiv.Perm ι) (h : 4 ≤ (univ.filter fun i => σ i ≠ i).card) :
    ∃ J : Finset ι, J.card = 2 ∧ Disjoint J (J.map σ.toEmbedding) := by
  classical
  let S : Finset ι := univ.filter fun i => σ i ≠ i
  have hs : 4 ≤ S.card := h
  obtain ⟨x,hx⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
  have hsub : ¬ S ⊆ ({x, σ x, σ.symm x} : Finset ι) := by
    intro hst
    have hle := (Finset.card_le_card hst).trans Finset.card_le_three
    omega
  obtain ⟨y, hy, hyn⟩ := Finset.not_subset.mp hsub
  have hy' : y ≠ x ∧ y ≠ σ x ∧ y ≠ σ.symm x := by simpa using hyn
  have hxy' : σ y ≠ x := by
    intro he
    apply hy'.2.2
    rw [← he, σ.symm_apply_apply]
  have hx' := (Finset.mem_filter.mp hx).2
  have hy'' := (Finset.mem_filter.mp hy).2
  refine ⟨{x,y}, Finset.card_pair hy'.1.symm, Finset.disjoint_left.mpr ?_⟩
  intro t ht ht'
  simp only [Finset.map_insert, Finset.map_singleton, Finset.mem_insert,
    Finset.mem_singleton, Equiv.toEmbedding_apply] at ht ht'
  rcases ht with ht | ht <;> subst t
  · exact ht'.elim (Ne.symm hx') (Ne.symm hxy')
  · exact ht'.elim hy'.2.1 (Ne.symm hy'')

/-- No nonnegative normalized law on permutations has even the doubleton
image marginals of the flat five-dimensional Householder reflection. -/
theorem orderFiveFlatReflection_no_positive_pair_law :
    ¬ ∃ w : Equiv.Perm (Fin 5) → ℝ, (∀ σ, 0 ≤ w σ) ∧ (∑ σ, w σ) = 1 ∧
      ∀ I J : Finset (Fin 5), I.card = 2 → J.card = 2 →
        (∑ σ ∈ univ.filter (fun σ : Equiv.Perm (Fin 5) => J.map σ.toEmbedding = I), w σ) =
          subsetMinorSq orderFiveFlatReflection I J := by
  classical
  rintro ⟨w, hw, hmass, hpair⟩
  let moved (σ : Equiv.Perm (Fin 5)) := (univ.filter fun i => σ i ≠ i).card
  have hFew (σ : Equiv.Perm (Fin 5)) (hp : w σ ≠ 0) : moved σ ≤ 3 := by
    by_contra h
    obtain ⟨J,hJ,hd⟩ := exists_disjoint_pair_image_of_four_moved σ (by
      change 4 ≤ moved σ
      omega)
    let I := J.map σ.toEmbedding
    have hi : I.card = 2 := by simp [I, hJ]
    have hm := hpair I J hi hJ
    rw [flatReflection_disjoint_minor I J hi hJ hd.symm] at hm
    exact hp ((Finset.sum_eq_zero_iff_of_nonneg (fun p _ => hw p)).mp hm σ (by simp [I]))
  have hi (i : Fin 5) :
      (∑ σ ∈ (univ.filter (fun σ : Equiv.Perm (Fin 5) => σ i = i)), w σ) = 9 / 25 := by
    have he := orderFive_all_minors_of_pair_images _ unitary_orderFiveFlatReflection w hmass
      hpair {i} {i}
    simpa [flatReflection_singleton_minor] using he
  have hi' (i : Fin 5) : (∑ σ, if σ i ≠ i then w σ else 0) = (16 / 25 : ℝ) := by
    have hsum := Finset.sum_filter_add_sum_filter_not (s := (univ : Finset (Equiv.Perm (Fin 5))))
      (p := fun σ => σ i = i) w
    rw [hi i, hmass, Finset.sum_filter] at hsum
    linarith
  have hexpect : (∑ σ, w σ * (moved σ : ℝ)) = 16 / 5 := by
    have he (σ : Equiv.Perm (Fin 5)) :
        w σ * (moved σ : ℝ) = ∑ i, if σ i ≠ i then w σ else 0 := by
      rw [← Finset.sum_filter]
      simp [moved, mul_comm]
    simp_rw [he]
    rw [Finset.sum_comm]
    calc
      _ = ∑ _i : Fin 5, (16 / 25 : ℝ) := Finset.sum_congr rfl (fun i _ => hi' i)
      _ = _ := by norm_num
  have hle : (∑ σ, w σ * (moved σ : ℝ)) ≤ 3 := by
    calc
      _ ≤ ∑ σ, w σ * 3 := by
        apply Finset.sum_le_sum
        intro σ _
        by_cases hs : w σ = 0
        · simp [hs]
        · exact mul_le_mul_of_nonneg_left (by exact_mod_cast hFew σ hs) (hw σ)
      _ = 3 := by rw [← Finset.sum_mul, hmass, one_mul]
  linarith

/-- A single positive law that works for all spectra of a fixed mixer is
strictly more than the conjecture's objective-dependent convex inclusion. -/
theorem orderFiveFlatReflection_no_positive_all_spectral_law :
    ¬ ∃ w : Equiv.Perm (Fin 5) → ℝ, (∀ σ, 0 ≤ w σ) ∧ (∑ σ, w σ) = 1 ∧
      ∀ a b : Fin 5 → ℂ,
        weightedMatchingValue a b w = determinantValue a b orderFiveFlatReflection := by
  rintro ⟨w, hw, hm, hall⟩
  exact orderFiveFlatReflection_no_positive_pair_law
    ⟨w, hw, hm, (orderFive_weighted_spectra_eq_all_iff_doubleton_images _
      unitary_orderFiveFlatReflection w).mp hall⟩

end

end MOC
