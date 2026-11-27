import MOC.SecularCauchyDeterminantObjective
import MOC.SecularCauchyDeletion
import MOC.SecularQuadraticCommonWeights

/-! One permutation law for a finite family of spectral evaluations of a
Hermitian rank-one update, through the real column model. -/

open BigOperators Finset Filter Matrix Polynomial Set
open scoped Topology

namespace MOC

noncomputable section

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The determinant values of a finite family of spectral evaluations. -/
def secularEvaluationProfile {n : ℕ} (d r : Fin n → ℝ) (p : κ → ℝ[X])
    (a : κ → Fin n → ℝ) (k : κ) : ℝ :=
  secularEvaluationDet d r (p k) (a k)

/-- The permutation value of each member of a finite spectral family. -/
def secularEvaluationMatching {n : ℕ} (h : Fin n → ℝ) (p : κ → ℝ[X])
    (a : κ → Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (k : κ) : ℝ :=
  realMatchingProduct (a k) (fun i => (p k).eval (h i)) σ

omit [Fintype κ] [DecidableEq κ] in
private theorem secularEvaluationProfile_zero {n : ℕ}
    (d r h : Fin (n+1) → ℝ) (p : κ → ℝ[X]) (a : κ → Fin (n+1) → ℝ)
    (i : Fin (n+1)) (hr : r i = 0)
    (hspec : secularCharacteristic d r = ∏ j, (X-C (h j)))
    (hsmall : ∀ j : Fin (n+1), h j = d i →
      secularCharacteristic (d ∘ i.succAbove) (r ∘ i.succAbove) =
        (∏ k : Fin n, (X-C (h (j.succAbove k)))) →
      secularEvaluationProfile (d ∘ i.succAbove) (r ∘ i.succAbove) p (fun k => a k ∘ i.succAbove) ∈
        convexHull ℝ (Set.range (secularEvaluationMatching
          (h ∘ j.succAbove) p (fun k => a k ∘ i.succAbove)))) :
    secularEvaluationProfile d r p a ∈ convexHull ℝ (Set.range (secularEvaluationMatching h p a)) := by
  obtain ⟨j,hj,hpoly⟩ := exists_secularCharacteristic_deleted_label d r h i hr hspec
  let m (k : κ) : ℝ := a k i + (p k).eval (d i)
  let L : (κ → ℝ) →ₗ[ℝ] (κ → ℝ) :=
    { toFun := fun x k => m k * x k
      map_add' := fun x y => by funext k; exact mul_add _ _ _
      map_smul' := fun s x => by funext k; simp [smul_eq_mul, mul_left_comm (m k)] }
  let D := secularEvaluationProfile (d ∘ i.succAbove) (r ∘ i.succAbove) p (fun k => a k ∘ i.succAbove)
  have hD : secularEvaluationProfile d r p a = L D := by
    funext k
    exact det_secular_evaluation_delete d r (p k) (a k) i hr
  have hπ (σ : Equiv.Perm (Fin n)) :
      L (secularEvaluationMatching (h ∘ j.succAbove) p (fun k => a k ∘ i.succAbove) σ) =
        secularEvaluationMatching h p a (secularExtendPermutation j i σ) := by
    funext k
    change m k * realMatchingProduct _ _ σ = realMatchingProduct _ _ _
    unfold realMatchingProduct
    rw [Fin.prod_univ_succAbove _ j, secularExtendPermutation_at]
    simp only [secularExtendPermutation_succAbove, Function.comp_apply, hj, m]
  rw [hD]
  have hL : L D ∈ convexHull ℝ (L '' Set.range
      (secularEvaluationMatching (h ∘ j.succAbove) p (fun k => a k ∘ i.succAbove))) := by
    rw [← LinearMap.image_convexHull]
    exact ⟨D, hsmall j hj hpoly, rfl⟩
  apply convexHull_mono _ hL
  rintro _ ⟨_,⟨σ,rfl⟩,rfl⟩
  exact ⟨_, (hπ σ).symm⟩

private theorem secularEvaluationDet_transfer_weights {n : ℕ} (d r : Fin n → ℝ)
    (p : ℝ[X]) (a : Fin n → ℝ) {i j : Fin n} (hd : d i = d j)
    (hi : 0 ≤ r i) (hj : 0 ≤ r j) :
    let x := r i/(r i+r j)
    (1-x) * secularEvaluationDet d (secularTransfer r i j (-r i)) p a +
      x * secularEvaluationDet d (secularTransfer r i j (r j)) p a = secularEvaluationDet d r p a := by
  intro x
  let F (z : ℝ) := secularEvaluationDet d (secularTransfer r i j z) p a
  have hz : secularTransfer r i j 0 = r := by funext k; simp [secularTransfer]
  have hF (z : ℝ) : F z = (1-z) * secularEvaluationDet d r p a + z * F 1 := by
    have he := det_secular_evaluation_transfer d r p id (diagonal a) hd z
    simpa only [F, secularEvaluationDet, Matrix.submatrix_id_id, hz] using he
  change (1-x)*F (-r i)+x*F (r j)=_
  by_cases ht : r i+r j = 0
  · have hzi : r i = 0 := by linarith only [hi,hj,ht]
    simp [x, ht, hzi, F, hz]
  · have hmul : x*(r i+r j)=r i := div_mul_cancel₀ _ ht
    rw [hF (-r i), hF (r j)]
    linear_combination (F 1 - secularEvaluationDet d r p a) * hmul

private theorem real_profile_functional (L : (κ → ℝ) →L[ℝ] ℝ) :
    ∃ c : κ → ℝ, ∀ v : κ → ℝ, L v = ∑ k, c k*v k := by
  let e (k : κ) : κ → ℝ := Pi.single k 1
  refine ⟨fun k => L (e k), fun v => ?_⟩
  have hv : v = ∑ k, v k • e k := by
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, e, Pi.single_apply, smul_eq_mul,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, mem_univ, if_true]
    exact (if_pos (Finset.mem_univ j)).symm
  calc
    _ = L (∑ k, v k • e k) := congrArg L hv
    _ = _ := by simp only [map_sum, map_smul, smul_eq_mul, mul_comm]

/-- Every finite family of spectral polynomial determinant evaluations has a
common convex representation by matching products on a fixed simple spectrum. -/
theorem secularEvaluationProfile_mem_hull (p : κ → ℝ[X]) :
    ∀ (n : ℕ) (d r h : Fin n → ℝ), Function.Injective h → (∀ i, 0 ≤ r i) →
      secularCharacteristic d r = (∏ i, (X-C (h i))) → ∀ a : κ → Fin n → ℝ,
      secularEvaluationProfile d r p a ∈ convexHull ℝ (Set.range (secularEvaluationMatching h p a)) := by
  classical
  intro n
  induction n with
  | zero =>
      intro d r h _ _ _ a
      apply subset_convexHull ℝ _
      refine ⟨Equiv.refl _, ?_⟩
      funext k
      simp [secularEvaluationProfile, secularEvaluationDet, secularEvaluationMatching, realMatchingProduct]
  | succ n ih =>
      intro d r h hh hr hp a
      let P := secularEvaluationMatching h p a
      let C := convexHull ℝ (Set.range P)
      have hC : Convex ℝ C := convex_convexHull ℝ _
      have hzero (d' r' : Fin (n+1) → ℝ) (hr' : ∀ i, 0 ≤ r' i)
          (hp' : secularCharacteristic d' r' = ∏ i, (X-Polynomial.C (h i)))
          (i : Fin (n+1)) (hi : r' i = 0) : secularEvaluationProfile d' r' p a ∈ C := by
        apply secularEvaluationProfile_zero d' r' h p a i hi hp'
        intro j _ hdel
        exact ih (d' ∘ i.succAbove) (r' ∘ i.succAbove) (h ∘ j.succAbove)
          (hh.comp (fun _ _ he => Fin.succAbove_right_inj.mp he))
          (fun k => hr' (i.succAbove k)) hdel _
      have hboundary (d' r' : Fin (n+1) → ℝ) (hr' : ∀ i, 0 ≤ r' i)
          (hp' : secularCharacteristic d' r' = ∏ i, (X-Polynomial.C (h i)))
          (hbad : ¬ Function.Injective d' ∨ ∃ i, r' i = 0) : secularEvaluationProfile d' r' p a ∈ C := by
        rcases hbad with hcoll | ⟨i,hi⟩
        · unfold Function.Injective at hcoll
          push_neg at hcoll
          obtain ⟨i,j,hij,hne⟩ := hcoll
          obtain ⟨hl,hu,hi,hj⟩ := secularTransfer_nonneg_endpoints hr' hne
          let R := secularTransfer r' i j (-r' i)
          let S := secularTransfer r' i j (r' j)
          let x := r' i/(r' i+r' j)
          have hx : 0 ≤ x := div_nonneg (hr' i) (add_nonneg (hr' i) (hr' j))
          have hle : x ≤ 1 := by
            by_cases hz : r' i+r' j = 0
            · simp [x,hz]
            · exact (div_le_one (lt_of_le_of_ne (add_nonneg (hr' i) (hr' j)) (Ne.symm hz))).mpr
                (le_add_of_nonneg_right (hr' j))
          have hR := hzero d' R hl ((secularCharacteristic_transfer d' r' hij _).trans hp') i hi
          have hS := hzero d' S hu ((secularCharacteristic_transfer d' r' hij _).trans hp') j hj
          have he : (1-x) • secularEvaluationProfile d' R p a + x • secularEvaluationProfile d' S p a =
              secularEvaluationProfile d' r' p a := by
            funext k
            exact secularEvaluationDet_transfer_weights d' r' (p k) (a k) hij (hr' i) (hr' j)
          rw [← he]
          exact hC hR hS (sub_nonneg.mpr hle) hx (sub_add_cancel _ _)
        · exact hzero d' r' hr' hp' i hi
      by_cases hbad : ¬ Function.Injective d ∨ ∃ i, r i = 0
      · exact hboundary d r hr hp hbad
      · have hi : Function.Injective d := not_not.mp (fun he => hbad (Or.inl he))
        have hpos (i : Fin (n+1)) : 0 < r i := lt_of_le_of_ne (hr i)
          (fun he => hbad (Or.inr ⟨i,he.symm⟩))
        have he := secular_residues_unique_of_distinct_nodes d r h hi hp
        have hdom : d ∈ secularChamber h := ⟨hi, fun i => he ▸ hpos i⟩
        let target := secularEvaluationProfile d r p a
        change target ∈ C
        refine Classical.byContradiction fun hnt => ?_
        obtain ⟨L,_,hL,htarget⟩ := geometric_hahn_banach_closed_point hC
          (Set.finite_range P).isClosed_convexHull hnt
        obtain ⟨c,hc⟩ := real_profile_functional L
        let F (q : (Fin (n+1) → ℝ) × (Fin (n+1) → ℝ)) :=
          ∑ k, c k * secularEvaluationDet q.1 q.2 (p k) (a k)
        obtain ⟨σ,_,hmax⟩ := Finset.exists_max_image (univ : Finset (Equiv.Perm (Fin (n+1))))
          (fun π => L (P π)) ⟨Equiv.refl _,mem_univ _⟩
        let M := L (P σ)
        let U := 1+∑ i, |h i|
        have hU (i : Fin (n+1)) : h i < U := by
          have hi' : |h i| ≤ ∑ j, |h j| := single_le_sum (fun j _ => abs_nonneg (h j)) (mem_univ i)
          dsimp only [U]
          linarith only [hi', le_abs_self (h i)]
        have hF : SecularObjectiveProperties h F := secularEvaluation_objective h hh p a c
        obtain ⟨B,hB⟩ := hF.bounded
        have hbd (d' r' : Fin (n+1) → ℝ) (hr' : ∀ i, 0 ≤ r' i)
            (hp' : secularCharacteristic d' r' = ∏ i, (X-Polynomial.C (h i)))
            (hbad' : ¬ Function.Injective d' ∨ ∃ i, r' i = 0) : F (d',r') ≤ M := by
          change (∑ k, c k * secularEvaluationProfile d' r' p a k) ≤ M
          rw [← hc]
          apply convexHull_min ?_ (convex_halfSpace_le L.toLinearMap.isLinear _) (hboundary d' r' hr' hp' hbad')
          rintro _ ⟨π,rfl⟩
          exact hmax π (mem_univ _)
        have hle := secularChamber_harmonic_bound h F hF.continuous M B U hU hB hbd
          hF.near hF.second hF.harmonic d hdom
        rw [← he] at hle
        have hLt : L target ≤ M := (hc target).trans_le hle
        exact (not_lt_of_ge hLt) ((hL (P σ) (subset_convexHull ℝ (Set.range P) ⟨σ,rfl⟩)).trans htarget)


end

end MOC
