import MOC.SpectralMinorDecomposition

/-! A positive Gram certificate for a genuine complex support direction.
For reciprocal-conjugate spectra no full minor law is used. -/

open BigOperators Finset Matrix
open scoped ComplexConjugate

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Nonnegative scalar multiples of reciprocal conjugate spectral entries. -/
def reciprocalConjugatePartner (a : ι → ℂ) (γ : ℝ) (j : ι) : ℂ :=
  (γ : ℂ) * conj ((a j)⁻¹)

private def invSubsetProduct (a : ι → ℂ) (I : Finset ι) : ℂ := ∏ i ∈ I, (a i)⁻¹

private theorem prod_compl_eq_total_mul_invSubset (a : ι → ℂ)
    (ha : ∀ i, a i ≠ 0) (I : Finset ι) :
    (∏ i ∈ Iᶜ, a i) = (∏ i, a i) * invSubsetProduct a I := by
  have hI : ∏ i ∈ I, a i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => ha i
  rw [invSubsetProduct, Finset.prod_inv_distrib, ← Finset.prod_mul_prod_compl I a]
  rw [mul_comm (∏ i ∈ I, a i), mul_assoc, mul_inv_cancel₀ hI, mul_one]

omit [Fintype ι] [DecidableEq ι] in
private theorem prod_reciprocalPartner (a : ι → ℂ) (γ : ℝ) (J : Finset ι) :
    (∏ j ∈ J, reciprocalConjugatePartner a γ j) =
      ((γ ^ J.card : ℝ) : ℂ) * conj (invSubsetProduct a J) := by
  unfold reciprocalConjugatePartner invSubsetProduct
  rw [Finset.prod_mul_distrib, Finset.prod_const, map_prod, Complex.ofReal_pow]

private theorem re_mul_conj_gram_le (x y : ℂ) :
    (x * conj y).re ≤ (Complex.normSq x + Complex.normSq y) / 2 := by
  have h₁ : 0 ≤ (x.re - y.re) ^ 2 := sq_nonneg _
  have h₂ : 0 ≤ (x.im - y.im) ^ 2 := sq_nonneg _
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
  nlinarith only [h₁, h₂]

private def permutationOnAllSubsets (σ : Equiv.Perm ι) : Equiv.Perm (Finset ι) where
  toFun J := J.map σ.toEmbedding
  invFun J := J.map σ.symm.toEmbedding
  left_inv J := by ext i; simp [Finset.mem_map_equiv]
  right_inv J := by ext i; simp [Finset.mem_map_equiv]

/-- For reciprocal-conjugate spectra the phase-rotated determinant support
is maximized at the matching identity. This is one direction, not a
claim of full convex-hull containment for the whole spectral class. -/
theorem reciprocalConjugate_support_identity (a : ι → ℂ) (ha : ∀ j, a j ≠ 0)
    (γ : ℝ) (hγ : 0 ≤ γ) (U : Matrix ι ι ℂ) (hU : IsUnitary U) :
    ((conj (∏ j, a j)) * determinantValue a (reciprocalConjugatePartner a γ) U).re ≤
      ((conj (∏ j, a j)) * matchingProduct a (reciprocalConjugatePartner a γ) 1).re := by
  classical
  let A : ℂ := ∏ j, a j
  let η : ℂ := conj A
  let b := reciprocalConjugatePartner a γ
  let x := invSubsetProduct a
  let mass (J : Finset ι) : ℝ := Complex.normSq A * γ ^ J.card
  let g (I : Finset ι) : ℝ := mass I * Complex.normSq (x I) / 2
  let C (I J : Finset ι) : ℝ := mass J * (x I * conj (x J)).re
  let B : ℝ := (∑ I, g I) + ∑ J, g J
  have hscore (σ : Equiv.Perm ι) :
      (η * matchingProduct a b σ).re = ∑ J : Finset ι, C (J.map σ.toEmbedding) J := by
    rw [matchingProduct_expand_subsets, Finset.mul_sum, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro J _
    rw [prod_compl_eq_total_mul_invSubset a ha, prod_reciprocalPartner]
    change (conj A * ((A * x (J.map σ.toEmbedding)) *
        (↑(γ ^ J.card : ℝ) * conj (x J)))).re =
      mass J * (x (J.map σ.toEmbedding) * conj (x J)).re
    have hRe : (conj A * ((A * x (J.map σ.toEmbedding)) *
        (↑(γ ^ J.card : ℝ) * conj (x J)))) =
          (↑(mass J) : ℂ) * (x (J.map σ.toEmbedding) * conj (x J)) := by
      unfold mass
      rw [Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self]
      ring
    rw [hRe]
    simp [Complex.mul_re]
  have hdual (I J : Finset ι) (hIJ : I.card = J.card) : C I J ≤ g I + g J := by
    have hsame : mass I = mass J := by simp [mass, hIJ]
    have hmass : 0 ≤ mass J := mul_nonneg (Complex.normSq_nonneg _) (pow_nonneg hγ _)
    have h := mul_le_mul_of_nonneg_left (re_mul_conj_gram_le (x I) (x J)) hmass
    unfold C g
    rw [hsame]
    linarith only [h]
  have hdiag (J : Finset ι) : C J J = g J + g J := by
    unfold C g
    rw [Complex.mul_conj, Complex.ofReal_re]
    ring
  have hB : B = (η * matchingProduct a b 1).re := by
    rw [hscore]
    have hid (J : Finset ι) : J.map (1 : Equiv.Perm ι).toEmbedding = J := by
      ext i
      simp [Finset.mem_map_equiv]
    simp only [hid, hdiag, Finset.sum_add_distrib, B]
  have hBound : (η * determinantValue a b U).re ≤ B := by
    let W := Finset ι × Finset ι
    let I (e : W) := e.2
    let J (e : W) := e.1
    let w (e : W) : ℝ := if e.2.card = e.1.card then g e.2 + g e.1 - C e.2 e.1 else 0
    have hw (e : W) : 0 ≤ w e := by
      unfold w
      split
      · exact sub_nonneg.mpr (hdual _ _ ‹_›)
      · exact le_rfl
    apply spectral_support_of_subsetImage_certificate a b U hU η B I J w
      hw
      (fun _ => 0) (by simp)
    intro σ
    have hs (J₀ : Finset ι) :
        (∑ I₀ : Finset ι, w (J₀, I₀) * subsetImageEvent I₀ J₀ σ) =
          g (J₀.map σ.toEmbedding) + g J₀ - C (J₀.map σ.toEmbedding) J₀ := by
      rw [Finset.sum_eq_single (J₀.map σ.toEmbedding)]
      · simp [w, subsetImageEvent, Finset.card_map]
      · intro I₀ _ h
        simp [subsetImageEvent, Ne.symm h]
      · simp
    rw [hscore]
    simp only [zero_add]
    change _ = ∑ e : Finset ι × Finset ι, w e * subsetImageEvent e.2 e.1 σ
    rw [Fintype.sum_prod_type]
    simp only [hs, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    have hperm : (∑ J₀ : Finset ι, g (J₀.map σ.toEmbedding)) = ∑ I₀, g I₀ :=
      Equiv.sum_comp (permutationOnAllSubsets σ) g
    rw [hperm]
  rw [hB] at hBound
  exact hBound

end

end MOC
