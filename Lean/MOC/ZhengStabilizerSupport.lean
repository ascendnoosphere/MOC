import MOC.FourCoincidence
import Mathlib.Data.Complex.BigOperators
import Mathlib.Tactic.LinearCombination

/-! Three zero-pair profiles transfer every zero-height one-outlier projection
with real spectators to one positive law. In order four the common law is
the construction in Zheng's preprint, Appendix B.1, DOI
10.13140/RG.2.2.36790.25923. The signed determinant identity is from Merikoski
and Virtanen, DOI 10.1016/0024-3795(89)90709-X. -/

open BigOperators Matrix

namespace MOC
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private def mark (x : ι → ℝ) (o : ι) (u : ℂ) : ι → ℂ :=
  Function.update (fun i => (x i : ℂ)) o u

private def anchor (x : ι → ℝ) (o : ι) (d : ℝ) : ι → ℂ :=
  mark (fun i => x i + d) o 0

private theorem match_mark_split (x y : ι → ℝ) (o : ι) (u v : ℂ)
    (p : Equiv.Perm ι) :
    matchingProduct (mark x o u) (mark y o v) p =
      if p o = o then (u+v) * (↑(∏ t ∈ Finset.univ.erase o, (x (p t)+y t)) : ℂ)
      else ((x (p o) : ℂ)+v)*(u+(y (p.symm o) : ℂ)) *
        (↑(∏ t ∈ (Finset.univ.erase o).erase (p.symm o), (x (p t)+y t)) : ℂ) := by
  let S := (Finset.univ : Finset ι).erase o
  let a := mark x o u
  let b := mark y o v
  have ha (i : ι) (hi : i ≠ o) : a i = (x i : ℂ) := by simp [a,mark,hi]
  have hb (i : ι) (hi : i ≠ o) : b i = (y i : ℂ) := by simp [b,mark,hi]
  have hao : a o = u := by simp [a,mark]
  have hbo : b o = v := by simp [b,mark]
  have split : matchingProduct a b p =
      (a (p o)+b o)*∏ t ∈ S, (a (p t)+b t) := by
    exact (Finset.mul_prod_erase Finset.univ (fun t => a (p t)+b t)
      (Finset.mem_univ o)).symm
  change matchingProduct a b p = _
  rw [split]
  by_cases ho : p o = o
  · rw [if_pos ho,ho,hao,hbo]
    congr 1
    simp only [Complex.ofReal_prod,Complex.ofReal_add]
    apply Finset.prod_congr rfl
    intro t ht
    have hto := (Finset.mem_erase.mp ht).1
    rw [ha _ (fun h => hto (p.injective (h.trans ho.symm))),hb _ hto]
  · rw [if_neg ho]
    let k := p.symm o
    have hk : k ≠ o := fun he => ho ((congrArg p he).symm.trans (p.apply_symm_apply o))
    have hpk : p k = o := p.apply_symm_apply o
    have hks : k ∈ S := Finset.mem_erase.mpr ⟨hk,Finset.mem_univ _⟩
    rw [← Finset.mul_prod_erase S _ hks,hpk,hao,hbo,ha _ ho,hb _ hk,← mul_assoc]
    congr 1
    simp only [Complex.ofReal_prod,Complex.ofReal_add]
    apply Finset.prod_congr rfl
    intro t ht
    have hto := (Finset.mem_erase.mp (Finset.mem_erase.mp ht).2).1
    have htk := (Finset.mem_erase.mp ht).1
    rw [ha _ (fun h => htk (p.injective (h.trans hpk.symm))),hb _ hto]

private theorem anchor_shift_profile (x y : ι → ℝ) (o : ι) (p : Equiv.Perm ι) (d : ℝ) :
    (matchingProduct (anchor x o (-d)) (anchor y o d) p).re =
      if p o = o then 0 else
      ((x (p o)-d)*(y (p.symm o)+d)) *
        ∏ t ∈ (Finset.univ.erase o).erase (p.symm o), (x (p t)+y t) := by
  unfold anchor
  rw [match_mark_split]
  by_cases ho : p o = o
  · simp [ho]
  · rw [if_neg ho,if_neg ho]
    have he (t : ι) : x (p t) + -d + (y t+d) = x (p t)+y t := by ring
    simp only [he,zero_add,add_zero,← Complex.ofReal_mul,Complex.ofReal_re,sub_eq_add_neg]

/-- A projected two-outlier profile at matched height zero is an exact real
linear combination of three profiles with a zero on each side. -/
theorem marked_real_profile_of_zero_pair (x y : ι → ℝ) (o : ι) (u v η : ℂ)
    (h : (η*(u+v)).re = 0) (p : Equiv.Perm ι) :
    let A := η.re
    let B := (η*u*v).re
    let C := (η*u).re
    (η*matchingProduct (mark x o u) (mark y o v) p).re =
      (A+B)*(matchingProduct (anchor x o 0) (anchor y o 0) p).re +
      ((C-B)/2)*(matchingProduct (anchor x o (-1)) (anchor y o 1) p).re -
      ((C+B)/2)*(matchingProduct (anchor x o 1) (anchor y o (-1)) p).re := by
  dsimp only
  have h₀ := anchor_shift_profile x y o p 0
  have h₁ := anchor_shift_profile x y o p 1
  have h₂ := anchor_shift_profile x y o p (-1)
  rw [neg_zero] at h₀
  rw [neg_neg] at h₂
  rw [match_mark_split,h₀,h₁,h₂]
  by_cases ho : p o = o
  · simp only [ho,if_pos,mul_zero,add_zero,sub_zero]
    rw [← mul_assoc,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,h]
    ring
  · simp only [if_neg ho,Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,mul_zero,sub_zero]
    simp only [mul_add,Complex.add_re] at h
    have hv : η.re*v.re-η.im*v.im = -(η.re*u.re-η.im*u.im) := by
      simp only [Complex.mul_re] at h
      linarith only [h]
    linear_combination (y (p.symm o) *
      (∏ t ∈ (Finset.univ.erase o).erase (p.symm o), (x (p t)+y t))) * hv

private theorem projected_weighted_sum {F : Equiv.Perm ι → ℂ} (η : ℂ)
    (w : Equiv.Perm ι → ℝ) :
    (η*(∑ p, (w p : ℂ)*F p)).re = ∑ p, w p*(η*F p).re := by
  rw [Finset.mul_sum,Complex.re_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [show η*((w p : ℂ)*F p) = (w p : ℂ)*(η*F p) by ring]
  simp [Complex.mul_re]

/-- The zero-pair common law yields the height-zero bound for two arbitrary
complex outliers in order four; no sign conditions on the real spectators
are needed. -/
theorem four_marked_real_zero_height_support
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U)
    (x y : Fin 4 → ℝ) (u v η : ℂ) (h : (η*(u+v)).re = 0)
    (hs : ∀ p, (η*matchingProduct (mark x 0 u) (mark y 0 v) p).re ≤ 0) :
    (η*determinantValue (mark x 0 u) (mark y 0 v) U).re ≤ 0 := by
  obtain ⟨w,hw,_,_,hrep⟩ := exists_four_zero_pair_weights U hU
  let wₛ := realSignedWeight U
  let A := η.re
  let B := (η*u*v).re
  let C := (η*u).re
  let F (d : ℝ) (p : Equiv.Perm (Fin 4)) :=
    (matchingProduct (anchor x 0 (-d)) (anchor y 0 d) p).re
  let P (p : Equiv.Perm (Fin 4)) := (η*matchingProduct (mark x 0 u) (mark y 0 v) p).re
  have hp (p : Equiv.Perm (Fin 4)) :
      P p = (A+B)*F 0 p + ((C-B)/2)*F 1 p - ((C+B)/2)*F (-1) p := by
    simpa [P,A,B,C,F] using marked_real_profile_of_zero_pair x y 0 u v η h p
  have hF (d : ℝ) : (∑ p, wₛ p*F d p) = ∑ p, w p*F d p := by
    have e₁ := real_signed_determinant (anchor x 0 (-d)) (anchor y 0 d) U hU
    have e₂ := hrep (anchor x 0 (-d)) (anchor y 0 d)
      (by simp [anchor,mark]) (by simp [anchor,mark])
    simpa only [F,wₛ,Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,sub_zero] using congrArg Complex.re (e₁.trans e₂.symm)
  have expand (q : Equiv.Perm (Fin 4) → ℝ) :
      (∑ p, q p*P p) =
        (A+B)*(∑ p, q p*F 0 p) + ((C-B)/2)*(∑ p, q p*F 1 p) -
          ((C+B)/2)*(∑ p, q p*F (-1) p) := by
    simp only [Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _
    rw [hp p]
    ring
  rw [← real_signed_determinant _ _ U hU,projected_weighted_sum]
  change (∑ p, wₛ p*P p) ≤ 0
  rw [expand wₛ,hF 0,hF 1,hF (-1),← expand w]
  exact Finset.sum_nonpos fun p _ => mul_nonpos_of_nonneg_of_nonpos (hw p) (hs p)

/-- An order-four version stated directly on the input spectral lists. -/
theorem four_real_spectators_zero_height_support
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U)
    (a b : Fin 4 → ℂ) (η : ℂ)
    (ha : ∀ i, i ≠ 0 → (a i).im = 0) (hb : ∀ i, i ≠ 0 → (b i).im = 0)
    (h : (η*(a 0+b 0)).re = 0)
    (hs : ∀ p, (η*matchingProduct a b p).re ≤ 0) :
    (η*determinantValue a b U).re ≤ 0 := by
  have realize (f : Fin 4 → ℂ) (hf : ∀ i, i ≠ 0 → (f i).im = 0) :
      mark (fun i => (f i).re) 0 (f 0) = f := by
    funext i
    by_cases hi : i = 0
    · subst i
      simp [mark]
    · have he : ((f i).re : ℂ) = f i := Complex.ext (by simp) (by simp [hf i hi])
      simpa [mark,hi] using he
  have h' := four_marked_real_zero_height_support U hU
    (fun i => (a i).re) (fun i => (b i).re) (a 0) (b 0) η h
  rw [realize a ha,realize b hb] at h'
  exact h' hs

end
end MOC
