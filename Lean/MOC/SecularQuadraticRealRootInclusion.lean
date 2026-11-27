import MOC.SecularQuadraticSimilarity
import MOC.SecularChamberBoundary

/-! Determinant inclusion for a quadratic image of a rank-one Hermitian
secular matrix with the two real roots above its fixed spectrum. -/

open BigOperators Finset Filter Matrix Polynomial Set
open scoped Topology

namespace MOC

noncomputable section

/-- Adding a diagonal contributes each principal minor multiplied by the
diagonal variables of its deleted coordinates. -/
private theorem det_diagonal_shift_principal_expansion {ι K : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing K]
    (A : Matrix ι ι K) (a : ι → K) :
    (A + diagonal a).det =
      ∑ S : Finset ι, (A.submatrix (fun i : S => i.val) (fun i : S => i.val)).det *
        ∏ i ∈ Sᶜ, a i := by
  let f := (Matrix.detRowAlternating : (ι → K) [⋀^ι]→ₗ[K] K).toMultilinearMap
  have hf : (A + diagonal a).det = ∑ S : Finset ι, Matrix.det (S.piecewise A (diagonal a)) :=
    f.map_add_univ A (diagonal a)
  rw [hf]
  apply sum_congr rfl
  intro S _
  let T := {i : ι // i ∉ S}
  let g : S ⊕ T ≃ ι := Equiv.sumCompl (fun i => i ∈ S)
  let M : Matrix ι ι K := S.piecewise A (diagonal a)
  let N := A.submatrix (fun i : S => i.val) (fun i : S => i.val)
  let B := A.submatrix (fun i : S => i.val) (fun i : T => i.val)
  have hM : M.submatrix g g = fromBlocks N B 0 (diagonal fun i : T => a i.val) := by
    ext (i | i) (j | j) : 1
    · change S.piecewise A (diagonal a) i.val j.val = A i.val j.val
      simp [Finset.piecewise, i.property]
    · change S.piecewise A (diagonal a) i.val j.val = A i.val j.val
      simp [Finset.piecewise, i.property]
    · change S.piecewise A (diagonal a) i.val j.val = 0
      have hij : i.val ≠ j.val := fun he => i.property (he.symm ▸ j.property)
      simp [Finset.piecewise, i.property, Matrix.diagonal_apply_ne _ hij]
    · change S.piecewise A (diagonal a) i.val j.val = (diagonal fun i : T => a i.val) i j
      by_cases hij : i = j
      · subst j
        simp [Finset.piecewise, i.property]
      · have hv : i.val ≠ j.val := fun he => hij (Subtype.ext he)
        simp [Finset.piecewise, i.property, Matrix.diagonal_apply_ne _ hv, Matrix.diagonal_apply_ne _ hij]
  change M.det = _
  rw [← Matrix.det_submatrix_equiv_self g M, hM, Matrix.det_fromBlocks_zero₂₁, Matrix.det_diagonal]
  congr 1
  let e : T ≃ (Sᶜ : Finset ι) :=
    Equiv.subtypeEquivRight (fun x => (mem_compl (s := S) (a := x)).symm)
  have he : (∏ i : T, a i.val) = ∏ i : (Sᶜ : Finset ι), a i.val := by
    exact Fintype.prod_equiv e _ _ (fun _ => rfl)
  rw [he, Finset.prod_coe_sort (Sᶜ : Finset ι) a]


private theorem secular_real_root_support_expansion {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h d : ι → ℝ) (hd : d ∈ secularChamber h) (t u : ℝ) (htu : t ≠ u)
    (ht : ∀ i, d i ≠ t) (hu : ∀ i, d i ≠ u) (a : ι → ℂ) (η : ℂ) :
    (η * (secularQuadraticColumnMatrix d (secularResidue h d)
      (-(t : ℂ)-(u : ℂ)) (t*u : ℂ) a).det).re =
    ∑ S : Finset ι, (η * ∏ i ∈ Sᶜ, a i).re * secularQuadraticMinor h d S t u := by
  let H := secularChamberMatrix h d
  let Q := (H-t • 1)*(H-u • 1)
  rw [det_secularColumnMatrix_eq_physical_quadratic h d hd t u a]
  change (η * (Q.map Complex.ofRealHom + diagonal a).det).re = _
  rw [det_diagonal_shift_principal_expansion]
  simp only [mul_sum, Complex.re_sum]
  apply sum_congr rfl
  intro S _
  have hm : ((Q.map Complex.ofRealHom).submatrix (fun i : S => i.val) (fun i : S => i.val)).det =
      ((Q.submatrix (fun i : S => i.val) (fun i : S => i.val)).det : ℂ) := by
    rw [Matrix.submatrix_map]
    exact (Complex.ofRealHom.map_det _).symm
  have hq : (Q.submatrix (fun i : S => i.val) (fun i : S => i.val)).det =
      secularQuadraticMinor h d S t u :=
    det_quadratic_principal_minor_eq_secular h d (fun i => Real.sqrt (secularResidue h d i))
      (fun i => Real.mul_self_sqrt (hd.2 i).le) S t u htu ht hu
  rw [hm, hq]
  rw [mul_comm (↑(secularQuadraticMinor h d S t u) : ℂ), ← mul_assoc]
  simp

structure SecularObjectiveProperties {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ι → ℝ) (F : (ι → ℝ) × (ι → ℝ) → ℝ) : Prop where
  continuous : Continuous F
  bounded : ∃ B, ∀ d ∈ secularChamber h, F (d, secularResidue h d) ≤ B
  near : ∀ d ∈ secularChamber h, ∀ i, ∀ᶠ t in 𝓝 (d i),
    DifferentiableAt ℝ (fun s => F (Function.update d i s, secularResidue h (Function.update d i s))) t
  second : ∀ d ∈ secularChamber h, ∀ i, DifferentiableAt ℝ
    (deriv (fun s => F (Function.update d i s, secularResidue h (Function.update d i s)))) (d i)
  harmonic : ∀ d ∈ secularChamber h, (∑ i, secularResidue h d i *
    deriv (deriv (fun s => F (Function.update d i s, secularResidue h (Function.update d i s)))) (d i)) = 0

theorem secularColumnMatrix_real_root_objective {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (h : ι → ℝ) (t u : ℝ) (htu : t ≠ u) (ht : ∀ i, h i < t) (hu : ∀ i, h i < u)
    (a : ι → ℂ) (η : ℂ) :
    SecularObjectiveProperties h (fun p => (η * (secularQuadraticColumnMatrix p.1 p.2
      (-(t : ℂ)-(u : ℂ)) (t*u : ℂ) a).det).re) := by
  let c : ℂ := -(t : ℂ)-(u : ℂ)
  let e : ℂ := t*u
  let F (p : (ι → ℝ) × (ι → ℝ)) :=
    (η * (secularQuadraticColumnMatrix p.1 p.2 c e a).det).re
  let U := min t u
  have hU (i : ι) : h i < U := lt_min (ht i) (hu i)
  have hF : Continuous F := by
    have hf : Continuous (fun p : (ι → ℝ) × (ι → ℝ) => secularQuadraticColumnMatrix p.1 p.2 c e a) := by
      apply continuous_matrix
      intro i j
      unfold secularQuadraticColumnMatrix
      simp only [Matrix.add_apply, Matrix.diagonal_apply, Matrix.of_apply]
      split_ifs <;> fun_prop
    exact Complex.continuous_re.comp (continuous_const.mul hf.matrix_det)
  let b := |U| + ∑ i, (U - h i)
  let K := Set.pi Set.univ (fun _ : ι => Set.pi Set.univ (fun _ : ι => Icc (-b) b))
  have hK : IsCompact K :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  let f (H : Matrix ι ι ℝ) :=
    (η * ((((H-t • 1)*(H-u • 1)).map Complex.ofRealHom) + diagonal a).det).re
  have hfc : Continuous f := by
    let Q (H : Matrix ι ι ℝ) := (H-t • 1)*(H-u • 1)
    have hQ : Continuous Q := by unfold Q; fun_prop
    have hQ' : Continuous (fun H : Matrix ι ι ℝ => (Q H).map Complex.ofRealHom) :=
      continuous_matrix fun i j => Complex.continuous_ofReal.comp (hQ.matrix_elem i j)
    exact Complex.continuous_re.comp (continuous_const.mul (hQ'.add continuous_const).matrix_det)
  obtain ⟨B, hB⟩ := (hK.image hfc).bddAbove
  have hbound (d : ι → ℝ) (hd : d ∈ secularChamber h) : F (d,secularResidue h d) ≤ B := by
    have hm : secularChamberMatrix h d ∈ K := by
      intro i _ j _
      exact abs_le.mp (abs_secularChamberMatrix_entry_le h d hd.1 (fun k => (hd.2 k).le) U hU i j)
    have hle : f (secularChamberMatrix h d) ≤ B :=
      hB ⟨secularChamberMatrix h d, hm, rfl⟩
    have he := det_secularColumnMatrix_eq_physical_quadratic h d hd t u a
    change (η * (secularQuadraticColumnMatrix d (secularResidue h d) c e a).det).re ≤ B
    rw [show (secularQuadraticColumnMatrix d (secularResidue h d) c e a).det =
      ((((secularChamberMatrix h d-t • 1)*(secularChamberMatrix h d-u • 1)).map
        Complex.ofRealHom) + diagonal a).det from he]
    exact hle
  let w (S : Finset ι) := (η * ∏ i ∈ Sᶜ, a i).re
  let G (d : ι → ℝ) := ∑ S : Finset ι, w S * secularQuadraticMinor h d S t u
  have hnod (d : ι → ℝ) (hd : d ∈ secularChamber h) (i : ι) : d i < U :=
    secular_nodes_lt_spectral_upper_bound d (secularResidue h d) h (fun j => (hd.2 j).le)
      (secularCharacteristic_eq_spectrum_of_chamber h d hd) U hU i
  have hfG (d : ι → ℝ) (hd : d ∈ secularChamber h) : F (d,secularResidue h d) = G d :=
    secular_real_root_support_expansion h d hd t u htu
      (fun i => ((hnod d hd i).trans_le (min_le_left _ _)).ne)
      (fun i => ((hnod d hd i).trans_le (min_le_right _ _)).ne) a η
  have hG (d : ι → ℝ) (hd : d ∈ secularChamber h) :=
    secularQuadraticMinor_weighted_linear_combination h d hd.1 t u htu
      (fun i => ((hnod d hd i).trans_le (min_le_left _ _)).ne)
      (fun i => ((hnod d hd i).trans_le (min_le_right _ _)).ne) w
  have hrel (d : ι → ℝ) (hd : d ∈ secularChamber h) (i : ι) :
      (fun t => F (Function.update d i t, secularResidue h (Function.update d i t))) =ᶠ[𝓝 (d i)]
        (fun t => G (Function.update d i t)) := by
    have hC : Continuous (fun t : ℝ => Function.update d i t) :=
      continuous_const.update i continuous_id
    have htend : Tendsto (fun t : ℝ => Function.update d i t) (𝓝 (d i)) (𝓝 d) := by
      have hc0 : ContinuousAt (fun t : ℝ => Function.update d i t) (d i) := hC.continuousAt
      simpa only [Function.update_eq_self] using hc0.tendsto
    have hnear := htend.eventually ((isOpen_secularChamber h).mem_nhds hd)
    exact hnear.mono fun _ hp => hfG _ hp
  refine ⟨hF, ⟨B,hbound⟩, ?_, ?_, ?_⟩
  · intro d hd i
    filter_upwards [(hG d hd).1 i, (hrel d hd i).eventuallyEq_nhds] with x hx hE
    exact hx.congr_of_eventuallyEq hE
  · intro d hd i
    exact ((hG d hd).2.1 i).congr_of_eventuallyEq ((hrel d hd i).deriv)
  · intro d hd
    change (∑ i, secularResidue h d i *
      deriv (deriv (fun s => F (Function.update d i s, secularResidue h (Function.update d i s)))) (d i)) = 0
    simp_rw [(hrel d hd _).deriv.deriv_eq]
    exact (hG d hd).2.2

private theorem secularColumnMatrix_supported_on_chamber {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (h : ι → ℝ) (t u : ℝ) (htu : t ≠ u) (ht : ∀ i, h i < t) (hu : ∀ i, h i < u)
    (a : ι → ℂ) (η : ℂ) (M : ℝ)
    (hbd : ∀ d r : ι → ℝ, (∀ i, 0 ≤ r i) →
      secularCharacteristic d r = (∏ i, (X-C (h i))) →
      (¬ Function.Injective d ∨ ∃ i, r i = 0) →
      (η * (secularQuadraticColumnMatrix d r (-(t : ℂ)-(u : ℂ)) (t*u : ℂ) a).det).re ≤ M) :
    ∀ d ∈ secularChamber h,
      (η * (secularQuadraticColumnMatrix d (secularResidue h d)
        (-(t : ℂ)-(u : ℂ)) (t*u : ℂ) a).det).re ≤ M := by
  have h := secularColumnMatrix_real_root_objective h t u htu ht hu a η
  obtain ⟨B, hB⟩ := h.bounded
  exact secularChamber_harmonic_bound _ _ h.continuous M B (min t u)
    (fun i => lt_min (ht i) (hu i)) hB hbd h.near h.second h.harmonic

theorem secularTransfer_nonneg_endpoints {ι : Type*} [Fintype ι] [DecidableEq ι]
    {r : ι → ℝ} (hr : ∀ i, 0 ≤ r i) {i j : ι} (hij : i ≠ j) :
    (∀ k, 0 ≤ secularTransfer r i j (-r i) k) ∧
      (∀ k, 0 ≤ secularTransfer r i j (r j) k) ∧
      secularTransfer r i j (-r i) i = 0 ∧ secularTransfer r i j (r j) j = 0 := by
  have he (x : ℝ) :
      secularTransfer r i j x i = r i+x ∧ secularTransfer r i j x j = r j-x := by
    constructor <;> simp [secularTransfer, hij, Ne.symm hij, sub_eq_add_neg]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k
    by_cases hi : k = i
    · subst k
      rw [(he _).1, add_neg_cancel]
    · by_cases hj : k = j
      · subst k
        rw [(he _).2, sub_neg_eq_add]
        exact add_nonneg (hr j) (hr i)
      · simpa [secularTransfer, hi, hj] using hr k
  · intro k
    by_cases hi : k = i
    · subst k
      rw [(he _).1]
      exact add_nonneg (hr i) (hr j)
    · by_cases hj : k = j
      · subst k
        rw [(he _).2, sub_self]
      · simpa [secularTransfer, hi, hj] using hr k
  · rw [(he _).1, add_neg_cancel]
  · rw [(he _).2, sub_self]

/-- In every finite order, every quadratic image with two distinct real
roots above the spectrum of a positive Hermitian rank-one perturbation
satisfies determinant inclusion against an arbitrary complex diagonal. -/
theorem secularHull_of_real_quadratic_above_spectrum (t u : ℝ) (htu : t ≠ u) :
    ∀ (n : ℕ) (d r h : Fin n → ℝ), (∀ i, 0 ≤ r i) →
      secularCharacteristic d r = (∏ i, (X - C (h i))) →
      (∀ i, h i < t) → (∀ i, h i < u) → ∀ a : Fin n → ℂ,
      (secularQuadraticColumnMatrix d r (-(t : ℂ)-(u : ℂ)) (t*u : ℂ) a).det ∈
        convexHull ℝ (Set.range (matchingProduct
          (secularQuadraticLabels h (-(t : ℂ)-(u : ℂ)) (t*u : ℂ)) a)) := by
  intro n
  induction n with
  | zero =>
      intro d r h _ _ _ _ a
      apply subset_convexHull ℝ _
      refine ⟨Equiv.refl _, ?_⟩
      rw [Matrix.det_fin_zero]
      simp [matchingProduct]
  | succ n ih =>
      intro d r h hr hpoly hlt hlu a
      let c : ℂ := -(t : ℂ)-(u : ℂ)
      let e : ℂ := t*u
      let p := matchingProduct (secularQuadraticLabels h c e) a
      let K := convexHull ℝ (Set.range p)
      have hK : Convex ℝ K := convex_convexHull ℝ _
      have hz (d' r' : Fin (n+1) → ℝ)
          (hr' : ∀ i, 0 ≤ r' i) (hp' : secularCharacteristic d' r' = ∏ i, (X-C (h i)))
          (j : Fin (n+1)) (hj : r' j = 0) :
          (secularQuadraticColumnMatrix d' r' c e a).det ∈ K := by
        refine secular_hull_of_zero_residue d' r' h j hj hp' c e a ?_
        intro k _ hdel
        exact ih (d' ∘ j.succAbove) (r' ∘ j.succAbove) (h ∘ k.succAbove)
          (fun i => hr' (j.succAbove i)) hdel (fun i => hlt (k.succAbove i))
          (fun i => hlu (k.succAbove i)) (a ∘ j.succAbove)
      have hb (d' r' : Fin (n+1) → ℝ)
          (hr' : ∀ i, 0 ≤ r' i) (hp' : secularCharacteristic d' r' = ∏ i, (X-C (h i)))
          (hbad : ¬ Function.Injective d' ∨ ∃ i, r' i = 0) :
          (secularQuadraticColumnMatrix d' r' c e a).det ∈ K := by
        rcases hbad with hcollision | ⟨j,hj⟩
        · unfold Function.Injective at hcollision
          push_neg at hcollision
          obtain ⟨i,j,hij,hneq⟩ := hcollision
          obtain ⟨hleft,hright,hi,hj⟩ := secularTransfer_nonneg_endpoints hr' hneq
          have hL := hz d' (secularTransfer r' i j (-r' i)) hleft
            ((secularCharacteristic_transfer d' r' hij _).trans hp') i hi
          have hR := hz d' (secularTransfer r' i j (r' j)) hright
            ((secularCharacteristic_transfer d' r' hij _).trans hp') j hj
          exact hK.segment_subset hL hR (det_secularQuadraticColumnMatrix_mem_transfer_segment
            d' r' c e a hij (hr' i) (hr' j))
        · exact hz d' r' hr' hp' j hj
      by_cases hbad : (¬ Function.Injective d ∨ ∃ i, r i = 0)
      · exact hb d r hr hpoly hbad
      · have hd : Function.Injective d := not_not.mp (fun h => hbad (Or.inl h))
        have hp : ∀ i, 0 < r i := fun i => lt_of_le_of_ne (hr i)
          (fun hi => hbad (Or.inr ⟨i,hi.symm⟩))
        have he := secular_residues_unique_of_distinct_nodes d r h hd hpoly
        have hdom : d ∈ secularChamber h := ⟨hd, fun i => he ▸ hp i⟩
        rw [he]
        change _ ∈ K
        apply mem_hull_of_directional_bound p
        intro η
        obtain ⟨σ,_,hσ⟩ := Finset.exists_max_image (Finset.univ : Finset (Equiv.Perm (Fin (n+1))))
          (fun π => (η*p π).re) ⟨Equiv.refl _, Finset.mem_univ _⟩
        refine ⟨σ, ?_⟩
        apply secularColumnMatrix_supported_on_chamber h t u htu hlt hlu a η (η*p σ).re _ d hdom
        intro d' r' hr' hp' hbad'
        let ℓ := Complex.reLm.comp (LinearMap.mulLeft ℝ η)
        have hh := hb d' r' hr' hp' hbad'
        apply convexHull_min ?_ (convex_halfSpace_le ℓ.isLinear _) hh
        rintro _ ⟨π,rfl⟩
        exact hσ π (mem_univ π)

/-- A real diagonal plus a positive Hermitian rank-one perturbation,
followed by a quadratic with two distinct real roots above its spectrum,
satisfies the determinant inclusion with every complex diagonal partner. -/
theorem det_quadratic_rank_one_hermitian_mem_hull_of_roots_above
    {n : ℕ} (d v h : Fin n → ℝ) (t u : ℝ) (htu : t ≠ u)
    (hH : (diagonal d + vecMulVec v v).charpoly = ∏ i, (X-C (h i)))
    (ht : ∀ i, h i < t) (hu : ∀ i, h i < u) (a : Fin n → ℂ) :
    let H := diagonal d + vecMulVec v v
    let Q := (H-t • 1)*(H-u • 1)
    (Q.map Complex.ofRealHom + diagonal a).det ∈
      convexHull ℝ (Set.range (matchingProduct
        (fun i : Fin n => (((h i-t)*(h i-u) : ℝ) : ℂ)) a)) := by
  intro H Q
  have hh := charpoly_diagonal_add_outer d v v
  rw [hH] at hh
  have hMain := secularHull_of_real_quadratic_above_spectrum t u htu n d (fun i => v i * v i) h
    (fun i => mul_self_nonneg (v i)) hh.symm ht hu a
  have hl : secularQuadraticLabels h (-(t : ℂ)-(u : ℂ)) (t*u : ℂ) =
      fun i : Fin n => (((h i-t)*(h i-u) : ℝ) : ℂ) := by
    funext i
    simp only [secularQuadraticLabels, Complex.ofReal_mul, Complex.ofReal_sub]
    ring
  rw [hl, det_secularColumnMatrix_eq_rank_one_quadratic d v t u a] at hMain
  exact hMain

end

end MOC
