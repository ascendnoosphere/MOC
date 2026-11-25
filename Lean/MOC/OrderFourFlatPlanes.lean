import MOC.OrderFourGivens
import MOC.Realification
import MOC.Support

/-!
Four flat corners force a full two-plane family to be flat. In order four
this family reaches a mixer with a two-supported column even from a dense
real orthogonal mixer.
-/

open Matrix

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
private theorem rotateRows_left_apply (U : Matrix ι ι ℂ) {i j : ι} (hij : i ≠ j)
    (c s : ℝ) (k : ι) : rotateRows U i j c s i k = (c : ℂ) * U i k + (s : ℂ) * U j k := by
  change ((U.updateRow i ((c : ℂ) • U i + (s : ℂ) • U j)).updateRow j
    ((c : ℂ) • U j + (-(s : ℂ)) • U i)) i k = _
  simp [Matrix.updateRow, hij, Pi.smul_apply, smul_eq_mul]

omit [Fintype ι] in
private theorem rotateRows_right_apply (U : Matrix ι ι ℂ) (i j : ι)
    (c s : ℝ) (k : ι) : rotateRows U i j c s j k = (c : ℂ) * U j k - (s : ℂ) * U i k := by
  change ((U.updateRow i ((c : ℂ) • U i + (s : ℂ) • U j)).updateRow j
    ((c : ℂ) • U j + (-(s : ℂ)) • U i)) j k = _
  simp [Matrix.updateRow, Pi.smul_apply, smul_eq_mul, sub_eq_add_neg]

omit [Fintype ι] in
private theorem rotateRows_other_apply (U : Matrix ι ι ℂ) {i j r : ι}
    (hri : r ≠ i) (hrj : r ≠ j) (c s : ℝ) (k : ι) :
    rotateRows U i j c s r k = U r k := by
  change ((U.updateRow i ((c : ℂ) • U i + (s : ℂ) • U j)).updateRow j
    ((c : ℂ) • U j + (-(s : ℂ)) • U i)) r k = _
  simp [Matrix.updateRow, hri, hrj]

omit [Fintype ι] in
private theorem rotateRows_commute (U : Matrix ι ι ℂ) {i j r t : ι}
    (hij : i ≠ j) (hrt : r ≠ t) (hri : r ≠ i) (hrj : r ≠ j)
    (hti : t ≠ i) (htj : t ≠ j) (c s d e : ℝ) :
    rotateRows (rotateRows U i j c s) r t d e =
      rotateRows (rotateRows U r t d e) i j c s := by
  ext x k
  by_cases hi : x = i
  · subst x
    rw [rotateRows_other_apply _ hri.symm hti.symm, rotateRows_left_apply _ hij,
      rotateRows_left_apply _ hij, rotateRows_other_apply _ hri.symm hti.symm,
      rotateRows_other_apply _ hrj.symm htj.symm]
  · by_cases hj : x = j
    · subst x
      rw [rotateRows_other_apply _ hrj.symm htj.symm, rotateRows_right_apply,
        rotateRows_right_apply, rotateRows_other_apply _ hrj.symm htj.symm,
        rotateRows_other_apply _ hri.symm hti.symm]
    · by_cases hr : x = r
      · subst x
        rw [rotateRows_other_apply _ hri hrj, rotateRows_left_apply _ hrt,
          rotateRows_left_apply _ hrt, rotateRows_other_apply _ hri hrj,
          rotateRows_other_apply _ hti htj]
      · by_cases ht : x = t
        · subst x
          rw [rotateRows_other_apply _ hti htj, rotateRows_right_apply,
            rotateRows_right_apply, rotateRows_other_apply _ hti htj,
            rotateRows_other_apply _ hri hrj]
        · rw [rotateRows_other_apply _ hr ht, rotateRows_other_apply _ hi hj,
            rotateRows_other_apply _ hi hj, rotateRows_other_apply _ hr ht]

/-- If both disjoint signed swaps and their product attain the same global
support maximum, the full family of independent rotations in both planes
attains it. Proof: propagate along the two parallel edges first, then use
commutativity and propagate between those edges. -/
theorem flat_disjoint_rotateRows_of_support_max (a b : ι → ℂ) (η : ℂ)
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) {i j r t : ι}
    (hij : i ≠ j) (hrt : r ≠ t) (hri : r ≠ i) (hrj : r ≠ j) (hti : t ≠ i) (htj : t ≠ j)
    (hmax : ∀ V : Matrix ι ι ℂ, IsUnitary V →
      (η * determinantValue a b V).re ≤ (η * determinantValue a b U).re)
    (hfirst : (η * determinantValue a b (rotateRows U i j 0 1)).re =
      (η * determinantValue a b U).re)
    (hsecond : (η * determinantValue a b (rotateRows U r t 0 1)).re =
      (η * determinantValue a b U).re)
    (hboth : (η * determinantValue a b (rotateRows (rotateRows U i j 0 1) r t 0 1)).re =
      (η * determinantValue a b U).re)
    (c s d e : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) (hde : d ^ 2 + e ^ 2 = 1) :
    (η * determinantValue a b (rotateRows (rotateRows U i j c s) r t d e)).re =
      (η * determinantValue a b U).re := by
  let V := rotateRows U i j c s
  let W := rotateRows U r t 0 1
  let f (Z : Matrix ι ι ℂ) := (η * determinantValue a b Z).re
  have hV : IsUnitary V := isUnitary_rotateRows U hU i j hij c s hcs
  have hW : IsUnitary W := isUnitary_rotateRows U hU r t hrt 0 1 (by norm_num)
  have hVeq : f V = f U :=
    flat_rotateRows_of_support_max a b η U hU i j hij hmax hfirst c s hcs
  have hWeq : f W = f U := hsecond
  have hWedge : f (rotateRows W i j 0 1) = f W := by
    rw [hWeq, ← rotateRows_commute U hij hrt hri hrj hti htj 0 1 0 1]
    exact hboth
  have hVedge : f (rotateRows V r t 0 1) = f V := by
    rw [hVeq, rotateRows_commute U hij hrt hri hrj hti htj c s 0 1, ← hWeq]
    exact flat_rotateRows_of_support_max a b η W hW i j hij
      (fun Z hZ => (hmax Z hZ).trans_eq hWeq.symm) hWedge c s hcs
  exact (flat_rotateRows_of_support_max a b η V hV r t hrt
    (fun Z hZ => (hmax Z hZ).trans_eq hVeq.symm) hVedge d e hde).trans hVeq


private theorem annihilating_pair (x y : ℝ) :
    ∃ c s : ℝ, c ^ 2 + s ^ 2 = 1 ∧ c * x + s * y = 0 := by
  by_cases h : x ^ 2 + y ^ 2 = 0
  · have hx : x = 0 := by nlinarith [sq_nonneg y]
    exact ⟨1, 0, by norm_num, by simp [hx]⟩
  · have hp : 0 < x ^ 2 + y ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h)
    let d := Real.sqrt (x ^ 2 + y ^ 2)
    have hd : d ≠ 0 := (Real.sqrt_pos.2 hp).ne'
    have hds : d ^ 2 = x ^ 2 + y ^ 2 := Real.sq_sqrt hp.le
    refine ⟨y / d, -x / d, ?_, ?_⟩
    · rw [div_pow, div_pow, ← add_div, neg_sq, hds, add_comm]
      exact div_self h
    · field_simp
      ring

/-- Dense mixers are included: at a strictly violating real global maximum
two flat disjoint signed swaps must have a strictly losing product. Otherwise
rotate the two planes independently to create two zeros in any one column. -/
theorem four_disjoint_flat_swaps_have_strictly_losing_product
    (a b : Fin 4 → ℂ) (η : ℂ) (O : Matrix.orthogonalGroup (Fin 4) ℝ)
    (i j r t k : Fin 4) (hij : i ≠ j) (hrt : r ≠ t)
    (hri : r ≠ i) (hrj : r ≠ j) (hti : t ≠ i) (htj : t ≠ j) :
    let U := Complex.ofRealHom.mapMatrix O.val
    (∀ V : Matrix (Fin 4) (Fin 4) ℂ, IsUnitary V →
      (η * determinantValue a b V).re ≤ (η * determinantValue a b U).re) →
    (∀ p : Equiv.Perm (Fin 4),
      (η * matchingProduct a b p).re < (η * determinantValue a b U).re) →
    (η * determinantValue a b (rotateRows U i j 0 1)).re =
      (η * determinantValue a b U).re →
    (η * determinantValue a b (rotateRows U r t 0 1)).re =
      (η * determinantValue a b U).re →
    (η * determinantValue a b (rotateRows (rotateRows U i j 0 1) r t 0 1)).re <
      (η * determinantValue a b U).re := by
  intro U hmax hgap hfirst hsecond
  have hU : IsUnitary U := isUnitary_ofReal_orthogonal O
  have hbothle := hmax _ (isUnitary_rotateRows _ (isUnitary_rotateRows U hU i j hij
    0 1 (by norm_num)) r t hrt 0 1 (by norm_num))
  by_contra! hnot
  have hboth := le_antisymm hbothle hnot
  obtain ⟨c, s, hcs, hcs₀⟩ := annihilating_pair (O.val i k) (O.val j k)
  obtain ⟨d, e, hde, hde₀⟩ := annihilating_pair (O.val r k) (O.val t k)
  let V := rotateRows U i j c s
  let W := rotateRows V r t d e
  have hW : IsUnitary W :=
    isUnitary_rotateRows V (isUnitary_rotateRows U hU i j hij c s hcs) r t hrt d e hde
  have hflat := flat_disjoint_rotateRows_of_support_max a b η U hU hij hrt hri hrj hti htj
    hmax hfirst hsecond hboth c s d e hcs hde
  have hi : W i k = 0 := by
    change rotateRows V r t d e i k = _
    rw [rotateRows_other_apply _ hri.symm hti.symm]
    change rotateRows U i j c s i k = _
    rw [rotateRows_left_apply _ hij]
    change (c : ℂ) * (O.val i k : ℂ) + (s : ℂ) * (O.val j k : ℂ) = 0
    exact_mod_cast hcs₀
  have hr : W r k = 0 := by
    change rotateRows V r t d e r k = _
    rw [rotateRows_left_apply _ hrt]
    change (d : ℂ) * rotateRows U i j c s r k + (e : ℂ) * rotateRows U i j c s t k = _
    rw [rotateRows_other_apply _ hri hrj, rotateRows_other_apply _ hti htj]
    change (d : ℂ) * (O.val r k : ℂ) + (e : ℂ) * (O.val t k : ℂ) = 0
    exact_mod_cast hde₀
  classical
  have hsub : supportColumns Wᴴ {k} ⊆ (Finset.univ.erase i).erase r := by
    intro p hp
    have hne : W p k ≠ 0 := by
      simpa [supportColumns, Matrix.conjTranspose_apply] using hp
    have hpi : p ≠ i := fun he => hne (he ▸ hi)
    have hpr : p ≠ r := fun he => hne (he ▸ hr)
    simp [hpi, hpr]
  have hcard : ((Finset.univ.erase i).erase r : Finset (Fin 4)).card = 2 := by
    rw [Finset.card_erase_of_mem (by simp [hri]), Finset.card_erase_of_mem (Finset.mem_univ i)]
    simp
  have hsparse : (supportColumns Wᴴ {k}).card ≤ 2 := (Finset.card_le_card hsub).trans_eq hcard
  have hholds := holds_of_column_degree_le_two conjecture_three a b hW k hsparse
  obtain ⟨p, hp⟩ := (holds_iff_directional a b W).mp hholds η
  exact (not_lt_of_ge (hflat.symm.le.trans hp)) (hgap p)

end

end MOC
