import MOC.QuaternionBinaryNormalize

/-! Transpose averaging supplies nonnegative spectral weights for a
quaternion mixer with aligned identical spectra, even for shapes whose
common subset-marginal parity repair is infeasible. -/

open Finset BigOperators Matrix

namespace MOC.QuaternionIntrinsic

noncomputable section

private lemma binarySign_zero (j : BinaryLabels) : quaternionBinarySign 0 j = 1 := by
  unfold quaternionBinarySign
  change (if (0 : ZMod 2)*j.1+0*j.1+0*j.2=0 then (1 : ℝ) else -1) = 1
  simp

private lemma transpose_binarySign (i j : BinaryLabels) :
    quaternionBinarySign (i+j) i =
      (if i+j=0 then (1 : ℝ) else -1) * quaternionBinarySign (i+j) j := by
  by_cases h : i=j
  · subst j
    simp [binaryLabels_exponentTwo]
  have hne : i+j ≠ 0 := by
    intro he
    exact h (add_right_cancel (he.trans (binaryLabels_exponentTwo j).symm))
  have hpair := quaternionBinarySign_basisSigning.pair 0 i j h
  simp only [add_zero, binarySign_zero, mul_one] at hpair
  rw [if_neg hne, neg_one_mul]
  calc
    _ = (quaternionBinarySign (i+j) i * quaternionBinarySign (i+j) j) *
          quaternionBinarySign (i+j) j := by
      symm
      rw [mul_assoc, ← pow_two, quaternionBinarySign_basisSigning.sq, mul_one]
    _ = _ := by rw [hpair, neg_one_mul]

private lemma signedPairProd
    (σ : Equiv.Perm BinaryLabels) (p r s : BinaryLabels) (hrs : r ≠ s)
    (hr : σ r+r = r+s+p) (hs : σ s+s = r+s+p)
    (hout : ∀ j, j ≠ r → j ≠ s → σ j+j=p) :
    (∏ j, quaternionBinarySign (σ j+j) j) = -1 := by
  let z := quaternionBinarySign
  have hb := quaternionBinarySign_basisSigning
  let R : Finset BinaryLabels := (univ.erase r).erase s
  have hRs : s ∈ (univ : Finset BinaryLabels).erase r := mem_erase.mpr ⟨hrs.symm, mem_univ _⟩
  have hbase := hb.shift p
  rw [← mul_prod_erase univ _ (mem_univ r), ← mul_prod_erase (univ.erase r) _ hRs] at hbase
  have hmid : (∏ j ∈ R, z p j) = z p r * z p s := by
    have hsq : (z p r * z p s)^2 = 1 := by rw [mul_pow, hb.sq, hb.sq, one_mul]
    calc
      _ = (z p r * z p s)^2 * (∏ j ∈ R, z p j) := by rw [hsq, one_mul]
      _ = (z p r * (z p s * (∏ j ∈ R, z p j))) * (z p r * z p s) := by ring
      _ = _ := by rw [hbase, one_mul]
  rw [← mul_prod_erase univ _ (mem_univ r), ← mul_prod_erase (univ.erase r) _ hRs, hr, hs]
  have hprod : (∏ j ∈ R, z (σ j+j) j) = ∏ j ∈ R, z p j := by
    apply prod_congr rfl
    intro j hj
    rw [hout j (mem_erase.mp (mem_erase.mp hj).2).1 (mem_erase.mp hj).1]
  change z (r+s+p) r * (z (r+s+p) s * (∏ j ∈ R, z (σ j+j) j)) = -1
  rw [hprod, hmid, ← mul_assoc]
  exact hb.pair p r s hrs

private lemma realSignedWeight_binaryFormula (q : BinaryLabels → ℝ)
    (σ : Equiv.Perm BinaryLabels) (hn : ∑ k, q k^2 = 1) :
    realSignedWeight (signedKleinMixerTable quaternionBinarySign q) σ =
      parityReal σ * ((∏ j, quaternionBinarySign (σ j+j) j) * ∏ j, q (σ j+j)) := by
  unfold realSignedWeight signedWeight leibnizTerm
  rw [quaternionBinary_det q hn, div_one]
  simp only [signedKleinMixerTable, Matrix.of_apply, ← Complex.ofReal_prod, ← Complex.ofReal_intCast,
    ← Complex.ofReal_mul, Complex.ofReal_re, parityReal, Finset.prod_mul_distrib]

private lemma realSignedWeight_binaryTransposeFormula (q : BinaryLabels → ℝ)
    (σ : Equiv.Perm BinaryLabels) (hn : ∑ k, q k^2 = 1) :
    realSignedWeight (signedKleinMixerTable quaternionBinarySign q)ᵀ σ =
      (∏ j, if σ j+j=0 then (1 : ℝ) else -1) *
        realSignedWeight (signedKleinMixerTable quaternionBinarySign q) σ := by
  rw [realSignedWeight_binaryFormula q σ hn]
  unfold realSignedWeight signedWeight leibnizTerm
  rw [Matrix.det_transpose, quaternionBinary_det q hn, div_one]
  simp only [Matrix.transpose_apply, signedKleinMixerTable, Matrix.of_apply, ← Complex.ofReal_prod,
    ← Complex.ofReal_intCast, ← Complex.ofReal_mul, Complex.ofReal_re, parityReal]
  have he (j : BinaryLabels) :
      quaternionBinarySign (j+σ j) (σ j) * q (j+σ j) =
        (if σ j+j=0 then (1 : ℝ) else -1) *
          (quaternionBinarySign (σ j+j) j * q (σ j+j)) := by
    rw [add_comm j (σ j), transpose_binarySign, mul_assoc]
  simp_rw [he, Finset.prod_mul_distrib]
  ring

private lemma realSignedWeight_binary_average_nonneg
    (q : BinaryLabels → ℝ) (hn : ∑ k, q k^2 = 1)
    (σ : Equiv.Perm BinaryLabels) :
    let U := signedKleinMixerTable quaternionBinarySign q
    0 ≤ (realSignedWeight U σ + realSignedWeight Uᵀ σ) / 2 := by
  classical
  dsimp only
  rw [realSignedWeight_binaryTransposeFormula q σ hn, realSignedWeight_binaryFormula q σ hn]
  let p := σ 0
  let f : Equiv.Perm BinaryLabels := σ.trans (Equiv.subRight p)
  let τ : Equiv.Perm BinaryLabels := Equiv.addRight p
  have hf (j : BinaryLabels) : f j = σ j-p := rfl
  have hf0 : f 0 = 0 := by simp [hf, p]
  have hdis (j : BinaryLabels) : σ j+j = f j+j+p := by rw [hf]; abel
  have hsign : Equiv.Perm.sign σ = Equiv.Perm.sign f := by
    have hσ : σ = τ * f := by
      apply Equiv.ext
      intro j
      change σ j = f j+p
      rw [hf, sub_add_cancel]
    rw [hσ, Equiv.Perm.sign_mul,
      klein_translation_even binaryLabels_card binaryLabels_exponentTwo p, one_mul]
  let d (j : BinaryLabels) : ℝ := if j=0 then 1 else -1
  have hds (j : BinaryLabels) : d j^2=1 := by unfold d; split_ifs <;> norm_num
  change 0 ≤ (_ + (∏ j, d (σ j+j)) * _) / 2
  rcases fixedOrigin_perm_types binaryLabels_card binaryLabels_exponentTwo f hf0 with
    h | ⟨r,s,hrs,h⟩ | hb
  · have hd (j : BinaryLabels) : σ j+j=p := by simp [hdis, h, binaryLabels_exponentTwo]
    have hp : parityReal σ=1 := by simp [parityReal, hsign, h]
    have hD : (∏ j, d (σ j+j)) = 1 := by
      simp only [hd, Finset.prod_const, card_univ, binaryLabels_card]
      rw [show d p^4 = (d p^2)^2 by ring, hds, one_pow]
    simp only [hd, hp, quaternionBinarySign_basisSigning.shift, one_mul, hD,
      Finset.prod_const, card_univ, binaryLabels_card]
    positivity
  · have hr : σ r+r=r+s+p := by rw [hdis, h, Equiv.swap_apply_left]; abel
    have hs : σ s+s=r+s+p := by rw [hdis, h, Equiv.swap_apply_right]
    have hout (j : BinaryLabels) (hrj : j ≠ r) (hsj : j ≠ s) : σ j+j=p := by
      rw [hdis, h, Equiv.swap_apply_of_ne_of_ne hrj hsj, binaryLabels_exponentTwo, zero_add]
    have hp : parityReal σ = -1 := by simp [parityReal, hsign, h, Equiv.Perm.sign_swap hrs]
    have hpairs (a : BinaryLabels → ℝ) : (∏ j, a (σ j+j)) = a (r+s+p)^2 * a p^2 := by
      have hsE : s ∈ (univ : Finset BinaryLabels).erase r := mem_erase.mpr ⟨hrs.symm, mem_univ _⟩
      let E : Finset BinaryLabels := (univ.erase r).erase s
      have hC : E.card = 2 := by
        simp [E, card_erase_of_mem hsE, card_erase_of_mem (mem_univ r), binaryLabels_card]
      rw [← mul_prod_erase univ _ (mem_univ r), ← mul_prod_erase (univ.erase r) _ hsE, hr, hs]
      have he : (∏ j ∈ E, a (σ j+j)) = a p^2 := by
        calc
          _ = ∏ _j ∈ E, a p := by
            apply prod_congr rfl
            intro j hj
            rw [hout j (mem_erase.mp (mem_erase.mp hj).2).1 (mem_erase.mp hj).1]
          _ = _ := by simpa only [hC] using Finset.prod_const (s := E) (a p)
      rw [he]
      ring
    have hD : (∏ j, d (σ j+j)) = 1 := by rw [hpairs d, hds, hds, one_mul]
    rw [hp, signedPairProd σ p r s hrs hr hs hout, hD, hpairs q]
    simp only [neg_one_mul, neg_neg, one_mul]
    positivity
  · have hbij : Function.Bijective (fun j => σ j+j) := by
      have he := τ.bijective.comp hb
      change Function.Bijective (fun j => f j+j+p) at he
      simpa only [← hdis] using he
    have hD : (∏ j, d (σ j+j)) = -1 := by
      have hc : (∏ j, d (σ j+j)) = ∏ j, d j := Equiv.prod_comp (Equiv.ofBijective _ hbij) d
      rw [hc]
      rw [← mul_prod_erase univ _ (mem_univ (0 : BinaryLabels))]
      have he : (∏ j ∈ (univ : Finset BinaryLabels).erase 0, d j) = (-1 : ℝ)^3 := by
        calc
          _ = ∏ _j ∈ (univ : Finset BinaryLabels).erase 0, (-1 : ℝ) := by
            apply prod_congr rfl
            intro j hj
            simp [d, (mem_erase.mp hj).1]
          _ = _ := by rw [Finset.prod_const, card_erase_of_mem (mem_univ _), card_univ, binaryLabels_card]
      rw [he]
      norm_num [d]
    rw [hD]
    ring_nf
    norm_num


/-- For arbitrary spectra and quaternion shapes, the midpoint of the
values for the mixer and its transpose lies in the matching hull. -/
theorem quaternionBinary_transposeAverage_mem (a b : BinaryLabels → ℂ)
    (q : BinaryLabels → ℝ) (hn : ∑ k, q k^2 = 1) :
    let U := signedKleinMixerTable quaternionBinarySign q
    (determinantValue a b U + determinantValue a b Uᵀ) / 2 ∈
      convexHull ℝ (Set.range (matchingProduct a b)) := by
  let U := signedKleinMixerTable quaternionBinarySign q
  have hU : IsUnitary U := quaternionBinary_isUnitary q hn
  have htr : Uᵀ = Uᴴ := by
    ext i j
    change ((quaternionBinarySign (j+i) i * q (j+i) : ℝ) : ℂ) =
      star (((quaternionBinarySign (j+i) i * q (j+i) : ℝ) : ℂ))
    exact (Complex.conj_ofReal _).symm
  have ht : IsUnitary Uᵀ := by
    rw [htr]
    exact ⟨by simpa using hU.2, by simpa using hU.1⟩
  let w (σ : Equiv.Perm BinaryLabels) :=
    (realSignedWeight U σ + realSignedWeight Uᵀ σ) / 2
  refine mem_convexHull_of_exists_fintype w (matchingProduct a b)
    (fun σ => realSignedWeight_binary_average_nonneg q hn σ) ?_ (fun σ => ⟨σ,rfl⟩) ?_
  · unfold w
    rw [← sum_div, sum_add_distrib, sum_realSignedWeight U hU, sum_realSignedWeight Uᵀ ht]
    norm_num
  · unfold w
    simp only [Complex.real_smul]
    push_cast
    simp_rw [div_mul_eq_mul_div, add_mul]
    rw [← Finset.sum_div, Finset.sum_add_distrib]
    rw [real_signed_determinant a b U hU, real_signed_determinant a b Uᵀ ht]

/-- Transpose-invariance of the spectral value turns the midpoint law
into a certificate for the original mixer. -/
theorem holds_quaternionBinary_of_transposeValue
    (a b : BinaryLabels → ℂ) (q : BinaryLabels → ℝ)
    (hn : ∑ k, q k^2 = 1)
    (hval : determinantValue a b (signedKleinMixerTable quaternionBinarySign q)ᵀ =
      determinantValue a b (signedKleinMixerTable quaternionBinarySign q)) :
    Holds a b (signedKleinMixerTable quaternionBinarySign q) := by
  have hm := quaternionBinary_transposeAverage_mem a b q hn
  dsimp only at hm
  rw [hval, ← two_mul, mul_div_cancel_left₀ _ (by norm_num : (2 : ℂ) ≠ 0)] at hm
  exact hm

/-- Identically ordered spectra give MOC on this whole quaternion
class, with no balance restriction on the coordinates. -/
theorem holds_quaternionBinary_identicalSpectra (a : BinaryLabels → ℂ)
    (q : BinaryLabels → ℝ) (hn : ∑ k, q k^2 = 1) :
    Holds a a (signedKleinMixerTable quaternionBinarySign q) := by
  apply holds_quaternionBinary_of_transposeValue a a q hn
  let U := signedKleinMixerTable quaternionBinarySign q
  have hU : IsUnitary U := quaternionBinary_isUnitary q hn
  have htr : Uᵀ = Uᴴ := by
    ext i j
    change ((quaternionBinarySign (j+i) i * q (j+i) : ℝ) : ℂ) =
      star (((quaternionBinarySign (j+i) i * q (j+i) : ℝ) : ℂ))
    exact (Complex.conj_ofReal _).symm
  change determinantValue a a Uᵀ = _
  rw [htr]
  have h := determinantValue_relative a a U (1 : Matrix BinaryLabels BinaryLabels ℂ) hU
  simpa only [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one,
    determinantValue, add_comm (U * diagonal a * Uᴴ) (diagonal a)] using h.symm

end

end MOC.QuaternionIntrinsic
