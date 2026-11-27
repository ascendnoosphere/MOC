import MOC.Hermitian
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.FieldSimp

/-! The homogeneous two-outlier support comparison used in the entry-face pattern branch
of Zheng (preprint DOI: 10.13140/RG.2.2.36790.25923, Appendix E).
It reduces a real part to two real projective support comparisons,
each following the Hermitian theorem of Fiedler
(DOI: 10.1090/S0002-9939-1971-0286814-1).
The signed determinant evaluation is the Merikoski--Virtanen law
(DOI: 10.1016/0024-3795(89)90709-X). -/

open BigOperators Matrix

namespace MOC.ProjectiveTwoOutliers

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private def bracket {R : Type*} [CommRing R] (a c : R × R) : R :=
  a.1*c.2-a.2*c.1

/-- Homogeneous matching profile in the column-to-row convention. -/
def profile {R : Type*} [CommRing R] (a c : ι → R × R) (σ : Equiv.Perm ι) : R :=
  ∏ j, bracket (a (σ j)) (c j)

/-- The linear determinant evaluation on a real matching profile. -/
def evaluate (U : Matrix ι ι ℂ) (p : Equiv.Perm ι → ℝ) : ℝ :=
  ∑ σ, realSignedWeight U σ * p σ

omit [DecidableEq ι] in
private theorem reduce_real_chart (a c : ι → ℝ × ℝ)
    (ha : ∀ i, a i ≠ (0,0)) (hc : ∀ j, c j ≠ (0,0)) :
    ∃ (x y : ι → ℝ) (K : ℝ), ∀ σ : Equiv.Perm ι,
      profile a c σ = K * (matchingProduct (fun i => (x i : ℂ))
        (fun j => (y j : ℂ)) σ).re := by
  let inadmissible : Finset ℝ :=
    (Finset.univ.image fun i => -(a i).2/(a i).1) ∪
      (Finset.univ.image fun i => -(c i).2/(c i).1)
  obtain ⟨t, _, ht⟩ :=
    (Set.infinite_univ : (Set.univ : Set ℝ).Infinite).exists_not_mem_finset inadmissible
  let d (z : ℝ × ℝ) := z.2+t*z.1
  have hnon (z : ℝ × ℝ) (hz : z ≠ (0,0)) (h : -(z.2)/z.1 ≠ t) : d z ≠ 0 := by
    intro he
    by_cases h0 : z.1 = 0
    · apply hz
      have h1 : z.2 = 0 := by simpa [d,h0] using he
      exact Prod.ext h0 h1
    · apply h
      exact (div_eq_iff h0).2 (by dsimp [d] at he; linarith)
  have hda (i : ι) : d (a i) ≠ 0 := hnon _ (ha i) (fun he => ht
    (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,he⟩)))
  have hdc (j : ι) : d (c j) ≠ 0 := hnon _ (hc j) (fun he => ht
    (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,he⟩)))
  let x i := (a i).1/d (a i)
  let y j := -(c j).1/d (c j)
  refine ⟨x,y,(∏ i, d (a i))*(∏ j, d (c j)),fun σ => ?_⟩
  have he (i j : ι) : bracket (a i) (c j) = d (a i)*d (c j)*(x i+y j) := by
    dsimp [x,y,bracket]
    field_simp [hda,hdc]
    dsimp [d]
    ring
  simp only [profile,he, Finset.prod_mul_distrib, Equiv.prod_comp σ (fun i => d (a i))]
  congr 1
  simp only [matchingProduct, ← Complex.ofReal_add, ← Complex.ofReal_prod, Complex.ofReal_re]

/-- Fiedler's real-spectra support comparison also applies to real
homogeneous profiles, including points at infinity. -/
theorem real_projective_support (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (a c : ι → ℝ × ℝ) (ha : ∀ i, a i ≠ (0,0)) (hc : ∀ j, c j ≠ (0,0))
    (r : ℝ) (hs : ∀ σ : Equiv.Perm ι, r * profile a c σ ≤ 0) :
    evaluate U (fun σ => r * profile a c σ) ≤ 0 := by
  obtain ⟨x,y,K,hK⟩ := reduce_real_chart a c ha hc
  let X (i : ι) : ℂ := x i
  let Y (i : ι) : ℂ := y i
  have he (σ : Equiv.Perm ι) :
      r * profile a c σ = (((r*K : ℝ) : ℂ) * matchingProduct X Y σ).re := by
    rw [hK]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    ring
  obtain ⟨σ,hσ⟩ := (holds_iff_directional X Y U).mp
    (holds_of_real_spectra x y U hU) ((r*K : ℝ) : ℂ)
  have hd : (((r*K : ℝ) : ℂ) * determinantValue X Y U).re =
      evaluate U (fun τ => r * profile a c τ) := by
    rw [← real_signed_determinant X Y U hU, Finset.mul_sum, Complex.re_sum]
    unfold evaluate
    apply Finset.sum_congr rfl
    intro τ _
    change _ = realSignedWeight U τ * (r * profile a c τ)
    rw [he τ,mul_left_comm ((r*K : ℝ) : ℂ)]
    simp [Complex.mul_re]
  rw [hd,← he] at hσ
  exact hσ.trans (hs σ)

/-- Include real homogeneous coordinates into the complex projective chart. -/
def asComplex (x : ℝ × ℝ) : ℂ × ℂ := (x.1,x.2)

private theorem bracket_real (a c : ℝ × ℝ) :
    bracket (asComplex a) (asComplex c) = ((bracket a c : ℝ) : ℂ) := by
  simp [bracket,asComplex]

private theorem read_products (a c : ι → ℝ × ℝ) (o : ι) (p q : ℝ)
    (σ : Equiv.Perm ι) :
    (profile (Function.update (fun i => asComplex (a i)) o (Complex.I*p,1))
      (Function.update (fun i => asComplex (c i)) o (Complex.I*q,1)) σ).re =
    profile (Function.update a o (0,1)) (Function.update c o (0,1)) σ -
      p*q * profile (Function.update a o (1,0)) (Function.update c o (1,0)) σ := by
  let e := σ.symm o
  let S := (Finset.univ : Finset ι).erase o
  have he : σ e = o := σ.apply_symm_apply o
  by_cases h : σ o = o
  · have hreal (j : ι) (hj : j ∈ S) : σ j ≠ o :=
      fun hj' => (Finset.mem_erase.mp hj).1 (σ.injective (hj'.trans h.symm))
    have hprod : (∏ j ∈ S, bracket
        (Function.update (fun i => asComplex (a i)) o (Complex.I*p,1) (σ j))
        (Function.update (fun i => asComplex (c i)) o (Complex.I*q,1) j)) =
        ((∏ j ∈ S, bracket (a (σ j)) (c j) : ℝ) : ℂ) := by
      rw [Complex.ofReal_prod]
      apply Finset.prod_congr rfl
      intro j hj
      simp only [Function.update_of_ne (hreal _ hj),Function.update_of_ne (Finset.mem_erase.mp hj).1,
        bracket_real]
    unfold profile
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ o),
      ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ o),
      ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ o)]
    change Complex.re (bracket _ _ * (∏ j ∈ S, _)) = _ - p*q*_
    rw [hprod,h]
    simp only [Function.update_self,bracket,Complex.mul_re,Complex.sub_re,
      Complex.I_re,Complex.ofReal_re,Complex.ofReal_im,Complex.one_re,Complex.one_im,
      mul_zero,zero_mul,sub_self,sub_zero,zero_sub,one_mul,mul_one, Prod.fst_zero,Prod.snd_zero]

  · have heo : e ≠ o := fun h' => h ((congrArg σ h').symm.trans he)
    have heS : e ∈ S := Finset.mem_erase.mpr ⟨heo,Finset.mem_univ _⟩
    have hall (j : ι) (hj : j ∈ S.erase e) : j ≠ o ∧ σ j ≠ o :=
      ⟨(Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1,
        fun hh => (Finset.mem_erase.mp hj).1 (σ.injective (hh.trans he.symm))⟩
    let R := ∏ j ∈ S.erase e, bracket (a (σ j)) (c j)
    have hpc (A C : ℂ × ℂ) :
        profile (Function.update (fun i => asComplex (a i)) o A)
          (Function.update (fun i => asComplex (c i)) o C) σ =
          bracket (asComplex (a (σ o))) C * bracket A (asComplex (c e)) * R := by
      unfold profile
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ o)]
      change _ * (∏ j ∈ S, _) = _
      rw [← Finset.mul_prod_erase S _ heS, ← mul_assoc,he]
      simp only [Function.update_self,Function.update_of_ne heo,Function.update_of_ne h]
      congr 1
      rw [Complex.ofReal_prod]
      apply Finset.prod_congr rfl
      intro j hj
      simp only [Function.update_of_ne (hall j hj).1,Function.update_of_ne (hall j hj).2,
        bracket_real]
    have hpr (A C : ℝ × ℝ) :
        profile (Function.update a o A) (Function.update c o C) σ =
          bracket (a (σ o)) C * bracket A (c e) * R := by
      unfold profile
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ o)]
      change _ * (∏ j ∈ S, _) = _
      rw [← Finset.mul_prod_erase S _ heS, ← mul_assoc,he]
      simp only [Function.update_self,Function.update_of_ne heo,Function.update_of_ne h]
      congr 1
      apply Finset.prod_congr rfl
      intro j hj
      simp only [Function.update_of_ne (hall j hj).1,Function.update_of_ne (hall j hj).2]
    rw [hpc,hpr,hpr]
    simp [bracket,asComplex,Complex.mul_re,Complex.mul_im,Complex.sub_re,Complex.sub_im]
    ring

/-- If the two real pieces of each crossed assignment have compatible
signs, a zero-height support inequality for all permutations yields
the determinant support inequality in every order. -/
theorem support_of_aligned_crosses (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (a c : ι → ℝ × ℝ) (o : ι) (p q r : ℝ)
    (ha : ∀ i, i ≠ o → a i ≠ (0,0)) (hc : ∀ j, j ≠ o → c j ≠ (0,0))
    (halign : ∀ i j, i ≠ o → j ≠ o →
      0 ≤ (-(a i).1*(c j).1)*(p*q*(a i).2*(c j).2))
    (hs : ∀ σ : Equiv.Perm ι, r *
      (profile (Function.update (fun i => asComplex (a i)) o (Complex.I*p,1))
        (Function.update (fun i => asComplex (c i)) o (Complex.I*q,1)) σ).re ≤ 0) :
    evaluate U (fun σ => r *
      (profile (Function.update (fun i => asComplex (a i)) o (Complex.I*p,1))
        (Function.update (fun i => asComplex (c i)) o (Complex.I*q,1)) σ).re) ≤ 0 := by
  classical
  let a0 := Function.update a o (0,1)
  let c0 := Function.update c o (0,1)
  let aInf := Function.update a o (1,0)
  let cInf := Function.update c o (1,0)
  let P (σ : Equiv.Perm ι) := r * profile a0 c0 σ
  let Q (σ : Equiv.Perm ι) := (-(r*p*q)) * profile aInf cInf σ
  have hsum (σ : Equiv.Perm ι) : P σ + Q σ ≤ 0 := by
    have h := hs σ
    rw [read_products] at h
    dsimp [P,Q,a0,c0,aInf,cInf]
    nlinarith only [h]
  have hsamesign (σ : Equiv.Perm ι) : 0 ≤ P σ * Q σ := by
    let e := σ.symm o
    let S := (Finset.univ : Finset ι).erase o
    have he : σ e = o := σ.apply_symm_apply o
    by_cases h : σ o = o
    · have hP0 : P σ = 0 := by
        unfold P profile
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ o)]
        simp [h,a0,c0,bracket]
      rw [hP0,zero_mul]
    · have heo : e ≠ o := fun h' => h ((congrArg σ h').symm.trans he)
      have heS : e ∈ S := Finset.mem_erase.mpr ⟨heo,Finset.mem_univ _⟩
      let B := ∏ j ∈ S.erase e, bracket (a (σ j)) (c j)
      have ht (A C : ℝ × ℝ) :
          profile (Function.update a o A) (Function.update c o C) σ =
            bracket (a (σ o)) C * bracket A (c e) * B := by
        unfold profile
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ o)]
        change _ * (∏ j ∈ S, _) = _
        rw [← Finset.mul_prod_erase S _ heS, ← mul_assoc, he]
        simp only [Function.update_self,Function.update_of_ne h,Function.update_of_ne heo]
        congr 1
        apply Finset.prod_congr rfl
        intro j hj
        have hj0 : j ≠ o := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
        have hsj : σ j ≠ o := fun hh => (Finset.mem_erase.mp hj).1 (σ.injective (hh.trans he.symm))
        simp only [Function.update_of_ne hj0,Function.update_of_ne hsj]
      dsimp [P,Q,a0,c0,aInf,cInf]
      rw [ht,ht]
      have hx : r * (bracket (a (σ o)) (0,1) * bracket (0,1) (c e) * B) *
          (-(r*p*q) * (bracket (a (σ o)) (1,0) * bracket (1,0) (c e) * B)) =
          (r*B)^2 * ((-(a (σ o)).1*(c e).1)*(p*q*(a (σ o)).2*(c e).2)) := by
        simp [bracket]
        ring
      rw [hx]
      exact mul_nonneg (sq_nonneg _) (halign _ _ h heo)
  have hP (σ : Equiv.Perm ι) : P σ ≤ 0 := by
    by_contra! hp
    have hn := nonneg_of_mul_nonneg_right (hsamesign σ) hp
    linarith [hsum σ]
  have hQ (σ : Equiv.Perm ι) : Q σ ≤ 0 := by
    by_contra! hq
    have hn := nonneg_of_mul_nonneg_left (hsamesign σ) hq
    linarith [hsum σ]
  have hmark (M : ι → ℝ × ℝ) (hM : ∀ i, i ≠ o → M i ≠ (0,0))
      (z : ℝ × ℝ) (hz : z ≠ (0,0)) (i : ι) : Function.update M o z i ≠ (0,0) := by
    by_cases hi : i = o
    · subst i; simpa only [Function.update_self] using hz
    · simpa [Function.update_of_ne hi] using hM i hi
  have h0 := real_projective_support U hU a0 c0
    (hmark a ha _ (by simp)) (hmark c hc _ (by simp)) r hP
  have hInf := real_projective_support U hU aInf cInf
    (hmark a ha _ (by simp)) (hmark c hc _ (by simp)) (-(r*p*q)) hQ
  calc
    _ = evaluate U P + evaluate U Q := by
      unfold evaluate
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro σ _
      dsimp only
      rw [read_products]
      dsimp [P,Q,a0,c0,aInf,cInf]
      ring
    _ ≤ 0 := by linarith

end

end MOC.ProjectiveTwoOutliers
