import MOC.ReciprocalConjugateSupport

/-! Strict Gram dual slack persists under simultaneous perturbations of both
spectra and the support direction. -/

open BigOperators Finset Matrix Filter Topology
open scoped ComplexConjugate

namespace MOC
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private def spectralSubsetCost (a b : ι → ℂ) (η : ℂ) (I J : Finset ι) : ℝ :=
  (η * ((∏ i ∈ Iᶜ, a i) * ∏ j ∈ J, b j)).re

private def permutationOnAllSubsets (σ : Equiv.Perm ι) : Equiv.Perm (Finset ι) where
  toFun J := J.map σ.toEmbedding
  invFun J := J.map σ.symm.toEmbedding
  left_inv J := by ext i; simp [Finset.mem_map_equiv]
  right_inv J := by ext i; simp [Finset.mem_map_equiv]

/-- On each subset layer, the diagonal-average criterion certifies the
identity for this objective only. -/
theorem spectral_support_identity_of_diagonal_average
    (a b : ι → ℂ) (η : ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (havg : ∀ I J : Finset ι, I.card = J.card →
      spectralSubsetCost a b η I J ≤
        (spectralSubsetCost a b η I I + spectralSubsetCost a b η J J) / 2) :
    (η * determinantValue a b U).re ≤ (η * matchingProduct a b 1).re := by
  classical
  let C := spectralSubsetCost a b η
  let g (I : Finset ι) : ℝ := C I I / 2
  let B : ℝ := (∑ I, g I) + ∑ J, g J
  have hscore (σ : Equiv.Perm ι) :
      (η * matchingProduct a b σ).re = ∑ J : Finset ι, C (J.map σ.toEmbedding) J := by
    rw [matchingProduct_expand_subsets, Finset.mul_sum, Complex.re_sum]
    rfl
  have hdual (I J : Finset ι) (hIJ : I.card = J.card) : C I J ≤ g I + g J := by
    have h : C I J ≤ (C I I + C J J) / 2 := havg I J hIJ
    unfold g
    linarith only [h]
  have hdiag (J : Finset ι) : C J J = g J + g J := by unfold g; ring
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

private theorem gram_spectralSubsetCost (a : ι → ℂ) (ha : ∀ j, a j ≠ 0)
    (γ : ℝ) (I J : Finset ι) :
    spectralSubsetCost a (reciprocalConjugatePartner a γ) (conj (∏ j, a j)) I J =
      (Complex.normSq (∏ j, a j) * γ ^ J.card) *
        (invSubsetProduct a I * conj (invSubsetProduct a J)).re := by
  unfold spectralSubsetCost
  rw [prod_compl_eq_total_mul_invSubset a ha, prod_reciprocalPartner]
  let A : ℂ := ∏ j, a j
  change (conj A * ((A * invSubsetProduct a I) *
    (↑(γ ^ J.card : ℝ) * conj (invSubsetProduct a J)))).re = _
  have he : conj A * ((A * invSubsetProduct a I) *
        (↑(γ ^ J.card : ℝ) * conj (invSubsetProduct a J))) =
      (↑(Complex.normSq A * γ ^ J.card) : ℂ) *
        (invSubsetProduct a I * conj (invSubsetProduct a J)) := by
    rw [Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self]
    ring
  rw [he]
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- The identity matching remains a valid support bound throughout an
open neighborhood of a strict reciprocal-conjugate Gram instance. All
three inputs, including the direction, can vary independently. -/
theorem spectral_support_identity_near_reciprocalConjugate
    (a : ι → ℂ) (ha : ∀ j, a j ≠ 0) (γ : ℝ) (hγ : 0 < γ)
    (hsep : ∀ I J : Finset ι, I.card = J.card → I ≠ J →
      (∏ i ∈ I, (a i)⁻¹) ≠ ∏ j ∈ J, (a j)⁻¹) :
    ∀ᶠ x : (ι → ℂ) × (ι → ℂ) × ℂ in
        𝓝 (a, reciprocalConjugatePartner a γ, conj (∏ j, a j)),
      ∀ U : Matrix ι ι ℂ, IsUnitary U →
        (x.2.2 * determinantValue x.1 x.2.1 U).re ≤
          (x.2.2 * matchingProduct x.1 x.2.1 1).re := by
  classical
  let P := (ι → ℂ) × (ι → ℂ) × ℂ
  let x₀ : P := (a, reciprocalConjugatePartner a γ, conj (∏ j, a j))
  let C (x : P) := spectralSubsetCost x.1 x.2.1 x.2.2
  have hC (I J : Finset ι) : Continuous fun x => C x I J := by
    change Continuous (fun x : (ι → ℂ) × (ι → ℂ) × ℂ =>
      (x.2.2 * ((∏ i ∈ Iᶜ, x.1 i) * ∏ j ∈ J, x.2.1 j)).re)
    fun_prop
  have hstrict (I J : Finset ι) (hc : I.card = J.card) (hne : I ≠ J) :
      C x₀ I J < (C x₀ I I + C x₀ J J) / 2 := by
    dsimp [C, x₀]
    simp only [gram_spectralSubsetCost a ha, hc]
    let X := invSubsetProduct a I
    let Y := invSubsetProduct a J
    have hxy : X ≠ Y := hsep I J hc hne
    have hN : 0 < Complex.normSq (X - Y) :=
      Complex.normSq_pos.mpr (sub_ne_zero.mpr hxy)
    have hGram : (X * conj Y).re < ((X * conj X).re + (Y * conj Y).re) / 2 := by
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im] at hN
      simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
      nlinarith only [hN]
    have hpos : 0 < Complex.normSq (∏ j, a j) * γ ^ J.card :=
      mul_pos (Complex.normSq_pos.mpr (Finset.prod_ne_zero_iff.mpr fun j _ => ha j))
        (pow_pos hγ _)
    change (Complex.normSq (∏ j, a j) * γ ^ J.card) * (X * conj Y).re <
      ((Complex.normSq (∏ j, a j) * γ ^ J.card) * (X * conj X).re +
       (Complex.normSq (∏ j, a j) * γ ^ J.card) * (Y * conj Y).re) / 2
    rw [← mul_add, mul_div_assoc]
    exact mul_lt_mul_of_pos_left hGram hpos
  have hE (I J : Finset ι) :
      ∀ᶠ x in 𝓝 x₀, I.card = J.card → C x I J ≤ (C x I I + C x J J) / 2 := by
    by_cases hc : I.card = J.card
    · by_cases h : I = J
      · subst J
        exact Filter.Eventually.of_forall fun x _ => by linarith
      · have ht : Continuous fun x => (C x I I + C x J J) / 2 :=
          ((hC I I).add (hC J J)).div_const 2
        filter_upwards [(hC I J).continuousAt.eventually_lt ht.continuousAt (hstrict I J hc h)] with x hx
        exact fun _ => hx.le
    · exact Filter.Eventually.of_forall fun _ h => (hc h).elim
  have hAll : ∀ᶠ x in 𝓝 x₀, ∀ I J : Finset ι,
      I.card = J.card → C x I J ≤ (C x I I + C x J J) / 2 := by
    rw [Filter.eventually_all]
    intro I
    rw [Filter.eventually_all]
    exact hE I
  filter_upwards [hAll] with x hx U hU
  exact spectral_support_identity_of_diagonal_average x.1 x.2.1 x.2.2 U hU hx

end
end MOC
