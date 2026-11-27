import MOC.SecularQuadraticRealRootInclusion

/-! A common determinant law for finitely many real-root quadratics
using one secular chamber maximum principle. -/

open BigOperators Finset Filter Matrix Polynomial Set
open scoped Topology

namespace MOC

noncomputable section

variable {J ι : Type*} [Fintype J] [DecidableEq J] [Fintype ι] [DecidableEq ι]

omit [DecidableEq J] in
private theorem secularObjectiveProperties_sum (h : ι → ℝ)
    (F : J → (ι → ℝ) × (ι → ℝ) → ℝ)
    (hF : ∀ j, SecularObjectiveProperties h (F j)) :
    SecularObjectiveProperties h (fun p => ∑ j, F j p) := by
  classical
  have hN (d : ι → ℝ) (hd : d ∈ secularChamber h) (i : ι) :
      ∀ᶠ t in 𝓝 (d i), ∀ j, DifferentiableAt ℝ
        (fun s => F j (Function.update d i s, secularResidue h (Function.update d i s))) t :=
    Filter.eventually_all.mpr fun j => (hF j).near d hd i
  have h₂ (d : ι → ℝ) (hd : d ∈ secularChamber h) (i : ι) :
      HasDerivAt
        (deriv (fun s => ∑ j, F j (Function.update d i s, secularResidue h (Function.update d i s))))
        (∑ j, deriv (deriv (fun s => F j (Function.update d i s,
          secularResidue h (Function.update d i s)))) (d i)) (d i) := by
    have hd₂ := HasDerivAt.sum (u := (univ : Finset J))
      (fun j _ => ((hF j).second d hd i).hasDerivAt)
    apply hd₂.congr_of_eventuallyEq
    filter_upwards [hN d hd i] with t ht
    exact deriv_sum fun j _ => ht j
  choose B hB using fun j => (hF j).bounded
  refine ⟨continuous_finset_sum _ (fun j _ => (hF j).continuous),
    ⟨∑ j, B j, fun d hd => sum_le_sum fun j _ => hB j d hd⟩,
    ?_, ?_, ?_⟩
  · intro d hd i
    filter_upwards [hN d hd i] with t ht using DifferentiableAt.sum fun j _ => ht j
  · exact fun d hd i => (h₂ d hd i).differentiableAt
  · intro d hd
    simp_rw [(h₂ d hd _).deriv, mul_sum]
    rw [sum_comm]
    exact sum_eq_zero fun j _ => (hF j).harmonic d hd

private theorem pi_complex_direction_coordinates (L : (J → ℂ) →L[ℝ] ℝ) :
    ∃ η : J → ℂ, ∀ x : J → ℂ, L x = ∑ j, (η j * x j).re := by
  let a (j : J) : J → ℂ := Pi.single j 1
  let b (j : J) : J → ℂ := Pi.single j Complex.I
  refine ⟨fun j => (L (a j) : ℂ) - (L (b j) : ℂ)*Complex.I, ?_⟩
  intro x
  have he : x = ∑ j, ((x j).re • a j + (x j).im • b j) := by
    funext k
    simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, a, b, Pi.single_apply,
      Complex.real_smul, mul_ite, mul_one, mul_zero, ← ite_add, add_zero]
    rw [sum_add_distrib, sum_ite_eq univ k, sum_ite_eq univ k]
    simp [Complex.re_add_im]
  calc
    L x = L (∑ j, ((x j).re • a j + (x j).im • b j)) := congrArg L he
    _ = _ := by
      simp only [map_sum, map_add, map_smul, smul_eq_mul]
      apply sum_congr rfl
      intro j _
      simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul, mul_zero, mul_one,
        add_zero, zero_add, sub_zero, zero_sub]
      ring

/-- Evaluate the determinant of the shifted column model for every
quadratic in a finite family. -/
def secularQuadraticProfile (d r : ι → ℝ) (t u : J → ℝ) (a : ι → ℂ) (j : J) : ℂ :=
  (secularQuadraticColumnMatrix d r (-(t j : ℂ)-(u j : ℂ)) (t j*u j : ℂ) a).det

/-- Evaluate a permutation product for every quadratic in the family. -/
def secularQuadraticProfileMatching {n : ℕ} (h : Fin n → ℝ)
    (t u : J → ℝ) (a : Fin n → ℂ) (σ : Equiv.Perm (Fin n)) (j : J) : ℂ :=
  matchingProduct (secularQuadraticLabels h (-(t j : ℂ)-(u j : ℂ)) (t j*u j : ℂ)) a σ

omit [Fintype J] [DecidableEq J] in
private theorem secularQuadraticProfile_hull_of_zero {n : ℕ}
    (d r h : Fin (n+1) → ℝ) (t u : J → ℝ) (a : Fin (n+1) → ℂ)
    (i : Fin (n+1)) (hr : r i = 0)
    (hh : secularCharacteristic d r = ∏ j, (X-C (h j)))
    (hSmall : ∀ k : Fin (n+1), h k = d i →
      secularCharacteristic (d ∘ i.succAbove) (r ∘ i.succAbove) =
        (∏ j : Fin n, (X-C (h (k.succAbove j)))) →
      secularQuadraticProfile (d ∘ i.succAbove) (r ∘ i.succAbove) t u (a ∘ i.succAbove) ∈
        convexHull ℝ (Set.range (secularQuadraticProfileMatching
          (h ∘ k.succAbove) t u (a ∘ i.succAbove)))) :
    secularQuadraticProfile d r t u a ∈ convexHull ℝ (Set.range (secularQuadraticProfileMatching h t u a)) := by
  obtain ⟨k,hk,hpoly⟩ := exists_secularCharacteristic_deleted_label d r h i hr hh
  let c (j : J) : ℂ := -(t j : ℂ)-(u j : ℂ)
  let e (j : J) : ℂ := t j*u j
  let m (j : J) : ℂ := (d i : ℂ)^2+c j*d i+e j+a i
  let L : (J → ℂ) →ₗ[ℝ] (J → ℂ) :=
    { toFun := fun x j => m j * x j
      map_add' := fun x y => by funext j; exact mul_add _ _ _
      map_smul' := fun s x => by funext j; simp [Complex.real_smul, mul_left_comm (m j)] }
  let D := secularQuadraticProfile (d ∘ i.succAbove) (r ∘ i.succAbove) t u (a ∘ i.succAbove)
  have hD : secularQuadraticProfile d r t u a = L D := by
    funext j
    exact det_secularQuadraticColumnMatrix_zero_residue d r (c j) (e j) a i hr
  have hp (σ : Equiv.Perm (Fin n)) :
      L (secularQuadraticProfileMatching (h ∘ k.succAbove) t u (a ∘ i.succAbove) σ) =
        secularQuadraticProfileMatching h t u a (secularExtendPermutation i k σ) := by
    funext j
    change m j * matchingProduct _ _ σ = matchingProduct _ _ _
    unfold matchingProduct
    rw [Fin.prod_univ_succAbove _ i, secularExtendPermutation_at]
    simp only [secularQuadraticLabels, secularExtendPermutation_succAbove, Function.comp_apply, hk]
    rfl
  rw [hD]
  have hx : L D ∈ convexHull ℝ (L '' Set.range
      (secularQuadraticProfileMatching (h ∘ k.succAbove) t u (a ∘ i.succAbove))) := by
    rw [← LinearMap.image_convexHull]
    exact ⟨D, hSmall k hk hpoly, rfl⟩
  apply convexHull_mono _ hx
  rintro _ ⟨_,⟨σ,rfl⟩,rfl⟩
  exact ⟨secularExtendPermutation i k σ, (hp σ).symm⟩

/-- A single law represents every quadratic in a finite family of
real-root quadratics above the spectral list. The diagonal partner is fixed. -/
theorem secularQuadraticProfile_mem_hull (t u : J → ℝ) (htu : ∀ j, t j ≠ u j) :
    ∀ (n : ℕ) (d r h : Fin n → ℝ), (∀ i, 0 ≤ r i) →
      secularCharacteristic d r = (∏ i, (X-C (h i))) →
      (∀ j i, h i < t j) → (∀ j i, h i < u j) → ∀ a : Fin n → ℂ,
      secularQuadraticProfile d r t u a ∈ convexHull ℝ (Set.range (secularQuadraticProfileMatching h t u a)) := by
  classical
  intro n
  induction n with
  | zero =>
      intro d r h _ _ _ _ a
      apply subset_convexHull ℝ _
      refine ⟨Equiv.refl _, ?_⟩
      funext j
      simp [secularQuadraticProfile, secularQuadraticProfileMatching, matchingProduct]
  | succ n ih =>
      intro d r h hr hp ht hu a
      let P := secularQuadraticProfileMatching h t u a
      let K := convexHull ℝ (Set.range P)
      have hK : Convex ℝ K := convex_convexHull ℝ _
      have hzero (d' r' : Fin (n+1) → ℝ) (hr' : ∀ i, 0 ≤ r' i)
          (hp' : secularCharacteristic d' r' = ∏ i, (X-C (h i)))
          (i : Fin (n+1)) (hi : r' i = 0) : secularQuadraticProfile d' r' t u a ∈ K := by
        apply secularQuadraticProfile_hull_of_zero d' r' h t u a i hi hp'
        intro k _ hdel
        exact ih (d' ∘ i.succAbove) (r' ∘ i.succAbove) (h ∘ k.succAbove)
          (fun j => hr' (i.succAbove j)) hdel (fun j i => ht j (k.succAbove i))
          (fun j i => hu j (k.succAbove i)) (a ∘ i.succAbove)
      have hb (d' r' : Fin (n+1) → ℝ) (hr' : ∀ i, 0 ≤ r' i)
          (hp' : secularCharacteristic d' r' = ∏ i, (X-C (h i)))
          (hbad : ¬ Function.Injective d' ∨ ∃ i, r' i = 0) :
          secularQuadraticProfile d' r' t u a ∈ K := by
        rcases hbad with hcoll | ⟨i,hi⟩
        · unfold Function.Injective at hcoll
          push_neg at hcoll
          obtain ⟨i,k,hik,hneq⟩ := hcoll
          obtain ⟨hl,hh,hi,hk⟩ := secularTransfer_nonneg_endpoints hr' hneq
          let R := secularTransfer r' i k (-r' i)
          let S := secularTransfer r' i k (r' k)
          let x := r' i/(r' i+r' k)
          have hx : 0 ≤ x := div_nonneg (hr' i) (add_nonneg (hr' i) (hr' k))
          have hbound : x ≤ 1 := by
            by_cases hz : r' i+r' k = 0
            · simp [x,hz]
            · exact (div_le_one (lt_of_le_of_ne (add_nonneg (hr' i) (hr' k)) (Ne.symm hz))).mpr
                (le_add_of_nonneg_right (hr' k))
          have hR := hzero d' R hl ((secularCharacteristic_transfer d' r' hik _).trans hp') i hi
          have hS := hzero d' S hh ((secularCharacteristic_transfer d' r' hik _).trans hp') k hk
          have he :
              (1-x) • secularQuadraticProfile d' R t u a + x • secularQuadraticProfile d' S t u a =
                secularQuadraticProfile d' r' t u a := by
            funext j
            exact det_secularQuadraticColumnMatrix_transfer_weights d' r'
              (-(t j : ℂ)-(u j : ℂ)) (t j*u j : ℂ) a hik (hr' i) (hr' k)
          rw [← he]
          exact hK hR hS (sub_nonneg.mpr hbound) hx (sub_add_cancel _ _)
        · exact hzero d' r' hr' hp' i hi
      by_cases hbad : ¬ Function.Injective d ∨ ∃ i, r i = 0
      · exact hb d r hr hp hbad
      · have hi : Function.Injective d := not_not.mp (fun hd => hbad (Or.inl hd))
        have hpos (i : Fin (n+1)) : 0 < r i := lt_of_le_of_ne (hr i)
          (fun he => hbad (Or.inr ⟨i,he.symm⟩))
        have he := secular_residues_unique_of_distinct_nodes d r h hi hp
        have hdom : d ∈ secularChamber h := ⟨hi,fun i => he ▸ hpos i⟩
        let target := secularQuadraticProfile d r t u a
        change target ∈ K
        refine Classical.byContradiction fun hbad' => ?_
        obtain ⟨L,_,hL,htarget⟩ :=
          geometric_hahn_banach_closed_point hK (Set.finite_range P).isClosed_convexHull hbad'
        obtain ⟨η,hη⟩ := pi_complex_direction_coordinates L
        let F (p : (Fin (n+1) → ℝ) × (Fin (n+1) → ℝ)) :=
          ∑ j, (η j * secularQuadraticProfile p.1 p.2 t u a j).re
        obtain ⟨σ,_,hMax⟩ := Finset.exists_max_image (Finset.univ : Finset (Equiv.Perm (Fin (n+1))))
          (fun π => L (P π)) ⟨Equiv.refl _, mem_univ _⟩
        let M := L (P σ)
        have hF : SecularObjectiveProperties h F :=
          secularObjectiveProperties_sum h _
            (fun j => secularColumnMatrix_real_root_objective h (t j) (u j) (htu j) (ht j) (hu j) a (η j))
        obtain ⟨B,hB⟩ := hF.bounded
        let U := 1+ ∑ i, |h i|
        have hU (i : Fin (n+1)) : h i < U := by
          dsimp only [U]
          have hle : |h i| ≤ ∑ j, |h j| := single_le_sum (fun j _ => abs_nonneg (h j)) (mem_univ i)
          linarith only [hle, le_abs_self (h i)]
        have hBD (d' r' : Fin (n+1) → ℝ) (hr' : ∀ i, 0 ≤ r' i)
            (hp' : secularCharacteristic d' r' = ∏ i, (X-C (h i)))
            (hbd : ¬ Function.Injective d' ∨ ∃ i, r' i = 0) : F (d',r') ≤ M := by
          change (∑ j, (η j * secularQuadraticProfile d' r' t u a j).re) ≤ M
          rw [← hη]
          apply convexHull_min ?_ (convex_halfSpace_le L.toLinearMap.isLinear _) (hb d' r' hr' hp' hbd)
          rintro _ ⟨π,rfl⟩
          exact hMax π (mem_univ _)
        have hle := secularChamber_harmonic_bound h F hF.continuous M B U hU hB hBD
          hF.near hF.second hF.harmonic d hdom
        rw [← he] at hle
        have hLe : L target ≤ M := (hη target).trans_le hle
        have hlt := hL (P σ) (subset_convexHull ℝ (Set.range P) ⟨σ,rfl⟩)
        exact (not_lt_of_ge hLe) (hlt.trans htarget)

end

end MOC
