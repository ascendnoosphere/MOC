import MOC.Weights
import MOC.Variational
import MOC.ZhengContactReduction
import MOC.OrderFourIndependent
import MOC.Singular
import MOC.ComplexTiedSwap
import MOC.AffineGapCover

/-!
# Stationary signed determinant marginals

For additive spectral kernels, at a real relative support maximum the
signed determinant score has the same normalized value in every pivot
fibre. This is an identity of signed sums, not positivity of the fibres.
For the determinant weight method see Merikoski–Virtanen,
DOI: 10.1016/0024-3795(89)90709-X.
For contact transfer see Zheng, DOI: 10.13140/RG.2.2.36790.25923.
-/

open BigOperators Matrix
namespace MOC
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem marginal_leibnizTerm (W : Matrix ι ι ℂ) (i j : ι) :
    marginal (leibnizTerm W) i j = W i j * W.adjugate j i := by
  let V := W.updateCol j (Pi.single i (W i j))
  have hf : V.det = marginal (leibnizTerm W) i j := by
    rw [marginal, Matrix.det_apply']
    apply Finset.sum_congr rfl
    intro σ _
    by_cases hij : σ j = i
    · rw [if_pos hij]
      unfold leibnizTerm
      congr 1
      apply Finset.prod_congr rfl
      intro k _
      by_cases hk : k = j
      · subst k
        simp [V, hij]
      · simp [V, Matrix.updateCol_apply, hk, Ne.symm hk]
    · rw [if_neg hij]
      have hz : (∏ k, V (σ k) k) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ j)
        simp [V, Pi.single_apply, hij]
      rw [hz, mul_zero]
  rw [← hf]
  have hv : Pi.single i (W i j) = W i j • (Pi.single i (1 : ℂ) : ι → ℂ) := by
    funext k
    by_cases hk : k = i <;> simp [Pi.single_apply, hk]
  dsimp [V]
  rw [hv, Matrix.det_updateCol_smul, ← Matrix.det_transpose,
    ← Matrix.updateRow_transpose, ← Matrix.adjugate_apply, ← Matrix.adjugate_transpose]
  rfl

theorem stationary_weighted_pivot (a b : ι → ℂ) (V : Matrix ι ι ℂ)
    (hV : IsUnitary V) (hreal : ∀ i j, (V i j).im = 0) (η : ℂ)
    (hd : determinantValue a b V ≠ 0)
    (hmax : ∀ W : Matrix ι ι ℂ, IsUnitary W →
      (η * determinantValue a b W).re ≤ (η * determinantValue a b V).re)
    (i j : ι) :
    (η * marginal (fun σ => signedWeight V σ * matchingProduct a b σ) i j).re =
      (V i j).re ^ 2 * (η * determinantValue a b V).re := by
  let A := diagonal a
  let B := V * diagonal b * Vᴴ
  let C := A + B
  have hv : Vᴴ = Vᵀ := by
    ext r s
    apply Complex.ext <;> simp [Matrix.conjTranspose_apply, Matrix.transpose_apply, hreal]
  have ha : Aᵀ = A := Matrix.diagonal_transpose _
  have hb : Bᵀ = B := by
    simp [B, hv, Matrix.transpose_mul, Matrix.mul_assoc]
  have hc : Cᵀ = C := by simp [C, ha, hb]
  have hmax' (R : Matrix ι ι ℂ) (hR : IsUnitary R) :
      (η * (A + R * B * Rᴴ).det).re ≤ (η * C.det).re := by
    have hR' : IsUnitary Rᴴ := by
      simpa only [IsUnitary, Matrix.conjTranspose_conjTranspose] using And.intro hR.2 hR.1
    have hRV : IsUnitary (R * V) := by
      simpa only [Matrix.conjTranspose_conjTranspose] using relative_unitary Rᴴ V hR' hV
    simpa [determinantValue, A, B, C, Matrix.conjTranspose_mul, Matrix.mul_assoc] using hmax (R * V) hRV
  change C.det ≠ 0 at hd
  let D := η • (B * C.adjugate - C.adjugate * B)
  have hD : Dᴴ = D := by
    have h := support_maximum_inverse_commutator A B η hd hmax'
    change ((η * C.det) • (B * C⁻¹ - C⁻¹ * B))ᴴ =
      (η * C.det) • (B * C⁻¹ - C⁻¹ * B) at h
    have hadj : C.adjugate = C.det • C⁻¹ := by
      rw [Matrix.inv_def, smul_smul]
      simp [hd]
    simpa only [D, hadj, Matrix.mul_smul, Matrix.smul_mul, ← smul_sub, smul_smul] using h
  have hskew : Dᵀ = -D := by
    simp [D, Matrix.transpose_smul, Matrix.transpose_sub, Matrix.transpose_mul,
      Matrix.adjugate_transpose, hb, hc]
    rw [← smul_neg, neg_sub]
  have hDr (r s : ι) : (D r s).re = 0 := by
    have h₁ := congrArg (fun M : Matrix ι ι ℂ => (M r s).re) hD
    have h₂ := congrArg (fun M : Matrix ι ι ℂ => (M r s).re) hskew
    simp [Matrix.conjTranspose_apply, Matrix.transpose_apply] at h₁ h₂
    linarith
  let W := Matrix.of fun r s => (a r + b s) * V r s
  have hBV : B * V = V * diagonal b := by
    simp only [B, Matrix.mul_assoc, hV.2, Matrix.mul_one]
  have hW : W = C * V := by
    rw [show C * V = A * V + V * diagonal b by dsimp only [C]; rw [Matrix.add_mul, hBV]]
    ext r s
    simp only [W, A, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.of_apply, Matrix.add_apply]
    ring
  have hscore : marginal (fun σ => signedWeight V σ * matchingProduct a b σ) i j =
      marginal (leibnizTerm W) i j / V.det := by
    rw [marginal, marginal, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro σ _
    split_ifs
    · simp only [signedWeight, leibnizTerm, matchingProduct, W, Matrix.of_apply, Finset.prod_mul_distrib]
      ring
    · simp
  have hWadj : W.adjugate j i = V.det * (C.adjugate * V) i j := by
    rw [hW, Matrix.adjugate_mul_distrib, adjugate_unitary V hV, hv,
      Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul,
      ← Matrix.transpose_apply (Vᵀ * C.adjugate), Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.adjugate_transpose, hc]
  have hK : Matrix.of (fun r s => (a r + b s) * (C.adjugate * V) r s) =
      C.det • V + (A * C.adjugate - C.adjugate * A) * V := by
    calc
      _ = A * (C.adjugate * V) + (C.adjugate * V) * diagonal b := by
        ext r s
        simp only [Matrix.of_apply, Matrix.add_apply, A, Matrix.diagonal_mul, Matrix.mul_diagonal]
        ring
      _ = (A * C.adjugate + C.adjugate * B) * V := by
        rw [Matrix.add_mul]
        simp only [Matrix.mul_assoc, hBV]
      _ = _ := by
        rw [show B = C - A by dsimp [C]; abel, Matrix.mul_sub, Matrix.adjugate_mul,
          Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.sub_mul]
        abel
  have hDc : η • (A * C.adjugate - C.adjugate * A) = -D := by
    change _ = -(η • (B * C.adjugate - C.adjugate * B))
    rw [← smul_neg, neg_sub]
    have hA : A = C - B := by dsimp only [C]; abel
    rw [hA,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_adjugate, Matrix.adjugate_mul]
    congr 1
    abel
  have hval : (η * ((a i + b j) * (C.adjugate * V) i j)).re =
      (η * C.det).re * (V i j).re := by
    have he := congrArg (fun M : Matrix ι ι ℂ => η * M i j) hK
    simp only [Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, mul_add] at he
    have hz : (η * ((A * C.adjugate - C.adjugate * A) * V) i j).re = 0 := by
      change (((η • ((A * C.adjugate - C.adjugate * A) * V)) : Matrix ι ι ℂ) i j).re = 0
      rw [← Matrix.smul_mul, hDc, Matrix.neg_mul, Matrix.neg_apply, Complex.neg_re]
      simp [Matrix.mul_apply, Complex.re_sum, Complex.mul_re, hDr, hreal]
    rw [he, Complex.add_re, ← mul_assoc, Complex.mul_re, hreal i j, mul_zero, sub_zero, hz, add_zero]
  rw [hscore, marginal_leibnizTerm, hWadj]
  have he : W i j * (V.det * (C.adjugate * V) i j) / V.det =
      V i j * ((a i + b j) * (C.adjugate * V) i j) := by
    change (a i + b j) * V i j * (V.det * (C.adjugate * V) i j) / V.det = _
    field_simp [det_ne_zero_of_unitary hV]
    ring
  rw [he, mul_left_comm η, Complex.mul_re, hreal i j, zero_mul, sub_zero, hval]
  change (V i j).re * ((η * C.det).re * (V i j).re) = (V i j).re ^ 2 * (η * C.det).re
  ring

/-- At a strictly violating nonsingular real maximum, each nonzero
pivot fibre contains an inactive permutation. -/
theorem exists_inactive_of_stationary_pivot (a b : ι → ℂ) (V : Matrix ι ι ℂ)
    (hV : IsUnitary V) (hreal : ∀ i j, (V i j).im = 0) (η : ℂ)
    (hd : determinantValue a b V ≠ 0)
    (hmax : ∀ W : Matrix ι ι ℂ, IsUnitary W →
      (η * determinantValue a b W).re ≤ (η * determinantValue a b V).re)
    (p : Equiv.Perm ι)
    (hupper : ∀ q : Equiv.Perm ι, (η * matchingProduct a b q).re ≤
      (η * matchingProduct a b p).re)
    (hstrict : (η * matchingProduct a b p).re < (η * determinantValue a b V).re)
    {i j : ι} (hpivot : V i j ≠ 0) :
    ∃ q : Equiv.Perm ι, q j = i ∧
      (η * matchingProduct a b q).re < (η * matchingProduct a b p).re := by
  classical
  have hrealW (q : Equiv.Perm ι) : (signedWeight V q).im = 0 := by
    let V₀ : Matrix ι ι ℝ := fun r s => (V r s).re
    have hv : Complex.ofRealHom.mapMatrix V₀ = V := by
      ext r s
      apply Complex.ext <;> simp [V₀, hreal]
    have he : signedWeight (Complex.ofRealHom.mapMatrix V₀) q =
        (((((Equiv.Perm.sign q : ℤ) : ℝ) * ∏ k, V₀ (q k) k) / V₀.det : ℝ) : ℂ) := by
      have hdmap : (Complex.ofRealHom.mapMatrix V₀).det = (V₀.det : ℂ) :=
        (RingHom.map_det Complex.ofRealHom V₀).symm
      unfold signedWeight leibnizTerm
      rw [hdmap]
      simp [RingHom.mapMatrix_apply, Matrix.map_apply, Complex.ofReal_prod]
    rw [← hv, he, Complex.ofReal_im]
  by_cases hx : ∃ q : Equiv.Perm ι, q j = i ∧
      (η * matchingProduct a b q).re < (η * matchingProduct a b p).re
  · exact hx
  exfalso
  have hvpos : 0 < (V i j).re ^ 2 := sq_pos_of_ne_zero (by
    intro hz
    apply hpivot
    apply Complex.ext <;> simp [hz, hreal])
  have he := stationary_weighted_pivot a b V hV hreal η hd hmax i j
  have hm := congrArg Complex.re (marginal_signedWeight V hV i j)
  rw [Complex.ofReal_re, Complex.normSq_apply, hreal, mul_zero, add_zero, ← pow_two] at hm
  unfold marginal at he hm
  rw [Finset.mul_sum, Complex.re_sum] at he
  rw [Complex.re_sum] at hm
  have localEq (q : Equiv.Perm ι) :
      (η * (if q j = i then signedWeight V q * matchingProduct a b q else 0)).re =
      (if q j = i then signedWeight V q else 0).re * (η * matchingProduct a b p).re := by
    by_cases hq : q j = i
    · simp only [if_pos hq, mul_left_comm η, Complex.mul_re (signedWeight V q),
        hrealW, zero_mul, sub_zero]
      rw [le_antisymm (hupper q) (le_of_not_gt (fun hlt => hx ⟨q, hq, hlt⟩))]
    · simp [hq]
  simp_rw [localEq] at he
  rw [← Finset.sum_mul, hm] at he
  exact (ne_of_lt (mul_lt_mul_of_pos_left hstrict hvpos)) he

/-- The seven contacts can be imposed before orbit maximization. The real
replacement leaves those contact equalities unchanged since they involve
only the spectra and the direction. -/
theorem conjecture_four_iff_terminal_stationary_pivots :
    Conjecture (Fin 4) ↔ ¬ ∃ O : Matrix.orthogonalGroup (Fin 4) ℝ,
      let V := Complex.ofRealHom.mapMatrix O.val
      ∃ w : StrictMatchingSupport V,
        7 ≤ w.contacts.card ∧ determinantValue w.a w.b V ≠ 0 ∧
        (∀ W : Matrix (Fin 4) (Fin 4) ℂ, IsUnitary W →
          (w.η * determinantValue w.a w.b W).re ≤ (w.η * determinantValue w.a w.b V).re) ∧
        (∀ i j, V i j ≠ 0 →
          ∃ q : Equiv.Perm (Fin 4), q j = i ∧ q ∉ w.contacts) := by
  classical
  constructor
  · rintro h ⟨O, w, hw, -⟩
    exact (conjecture_four_iff_seven_orthogonal_contacts.mp h) ⟨O, w, hw⟩
  · intro h
    apply conjecture_four_iff_seven_orthogonal_contacts.mpr
    rintro ⟨O, w, hw⟩
    obtain ⟨W, hW, hmax⟩ := exists_support_maximizer w.a w.b w.η
    obtain ⟨P, heq, hmaxP, _⟩ :=
      exists_four_orthogonal_support_maximizer_with_zeros w.a w.b w.η W hW hmax
    let V := Complex.ofRealHom.mapMatrix P.val
    have hV : IsUnitary V := isUnitary_ofReal_orthogonal P
    have hVP : (w.η * determinantValue w.a w.b (Complex.ofRealHom.mapMatrix O.val)).re ≤
        (w.η * determinantValue w.a w.b V).re :=
      hmaxP _ (isUnitary_ofReal_orthogonal O)
    let v : StrictMatchingSupport V := ⟨w.a, w.b, w.η, w.pivot, w.maximal, w.strict.trans_le hVP⟩
    have hvd : determinantValue v.a v.b V ≠ 0 :=
      fun hzero => v.not_holds (holds_of_singular v.a v.b hV hzero)
    apply h
    refine ⟨P, v, hw, hvd, hmaxP, ?_⟩
    intro i j hpivot
    have hreal (r s : Fin 4) : (V r s).im = 0 := by simp [V]
    obtain ⟨q, hq, hlt⟩ := exists_inactive_of_stationary_pivot v.a v.b V hV hreal v.η
      hvd hmaxP v.pivot v.maximal v.strict hpivot
    exact ⟨q, hq, by simpa [StrictMatchingSupport.contacts] using hlt.ne⟩

end
end MOC

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem weighted_pivot_cofactor (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) (η : ℂ) (i j : ι) :
    let A := diagonal a
    let B := U * diagonal b * Uᴴ
    let C := A + B
    let T := η • (A * C.adjugate - C.adjugate * A)
    η * marginal (fun σ => signedWeight U σ * matchingProduct a b σ) i j =
      (Complex.normSq (U i j) : ℂ) * (η * C.det) - U i j * (Uᴴ * T) j i := by
  intro A B C T
  let W := Matrix.of fun r s => (a r + b s) * U r s
  have hBU : B * U = U * diagonal b := by
    simp only [B, Matrix.mul_assoc, hU.2, Matrix.mul_one]
  have hUB : Uᴴ * B = diagonal b * Uᴴ := by
    dsimp only [B]
    rw [← Matrix.mul_assoc Uᴴ (U * diagonal b), ← Matrix.mul_assoc Uᴴ U,
      hU.2, Matrix.one_mul]
  have hW : W = C * U := by
    rw [show C * U = A * U + U * diagonal b by dsimp only [C]; rw [Matrix.add_mul, hBU]]
    ext r s
    simp only [W, A, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.of_apply, Matrix.add_apply]
    ring
  have hscore : marginal (fun σ => signedWeight U σ * matchingProduct a b σ) i j =
      marginal (leibnizTerm W) i j / U.det := by
    rw [marginal, marginal, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro σ _
    split_ifs
    · simp only [signedWeight, leibnizTerm, matchingProduct, W, Matrix.of_apply,
        Finset.prod_mul_distrib]
      ring
    · simp
  have hWadj : W.adjugate j i = U.det * (Uᴴ * C.adjugate) j i := by
    rw [hW, Matrix.adjugate_mul_distrib, adjugate_unitary U hU, Matrix.smul_mul,
      Matrix.smul_apply, smul_eq_mul]
  have hK : Matrix.of (fun s r => (a r + b s) * (Uᴴ * C.adjugate) s r) =
      C.det • Uᴴ - Uᴴ * (A * C.adjugate - C.adjugate * A) := by
    calc
      _ = (Uᴴ * C.adjugate) * A + diagonal b * (Uᴴ * C.adjugate) := by
        ext s r
        simp only [Matrix.of_apply, Matrix.add_apply, A, Matrix.diagonal_mul, Matrix.mul_diagonal]
        ring
      _ = Uᴴ * (C.adjugate * A + B * C.adjugate) := by
        rw [Matrix.mul_add, ← Matrix.mul_assoc (diagonal b), ← hUB]
        simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [show B = C - A by dsimp [C]; abel, Matrix.sub_mul, Matrix.mul_adjugate]
        simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one]
        abel
  have hk := congrArg (fun M : Matrix ι ι ℂ => M j i) hK
  simp only [Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at hk
  have hcancel : W i j * (U.det * (Uᴴ * C.adjugate) j i) / U.det =
      U i j * ((a i + b j) * (Uᴴ * C.adjugate) j i) := by
    change (a i + b j) * U i j * (U.det * (Uᴴ * C.adjugate) j i) / U.det = _
    field_simp [det_ne_zero_of_unitary hU]
    ring
  rw [hscore, marginal_leibnizTerm, hWadj, hcancel, hk]
  rw [show (Uᴴ * T) j i =
      η * (Uᴴ * (A * C.adjugate - C.adjugate * A)) j i by
    simp only [T, Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul]]
  rw [Matrix.conjTranspose_apply, Complex.normSq_eq_conj_mul_self, Complex.star_def]
  ring

/-- At a unitary support maximum, the complex signed marginal of the real
score equals the full score times the squared entry modulus. -/
theorem stationary_signedWeight_pivot (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) (η : ℂ)
    (hmax : ∀ V : Matrix ι ι ℂ, IsUnitary V →
      (η * determinantValue a b V).re ≤ (η * determinantValue a b U).re)
    (i j : ι) :
    marginal (fun σ => signedWeight U σ * ((η * matchingProduct a b σ).re : ℂ)) i j =
      (Complex.normSq (U i j) : ℂ) * ((η * determinantValue a b U).re : ℂ) := by
  let A := diagonal a
  let B := U * diagonal b * Uᴴ
  let C := A + B
  let T := η • (A * C.adjugate - C.adjugate * A)
  have hleft (R : Matrix ι ι ℂ) (hR : IsUnitary R) :
      (η * (R * A * Rᴴ + B).det).re ≤ (η * C.det).re := by
    have hrel := determinantValue_relative a b R U hR
    change (η * (R * diagonal a * Rᴴ + U * diagonal b * Uᴴ).det).re ≤ _
    rw [hrel]
    exact hmax _ (relative_unitary R U hR hU)
  have hentry (r s : ι) :
      T r s = (η * (a r - a s)) * C.adjugate r s := by
    simp only [T, A, Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply,
      Matrix.diagonal_mul, Matrix.mul_diagonal]
    ring
  have hT : Tᴴ = T := by
    ext r s
    rw [Matrix.conjTranspose_apply, hentry, hentry]
    by_cases hrs : r = s
    · subst s
      simp
    · have hs := adjugate_cross_of_complex_diagonal_support_max a B η hrs hleft
      change (η * (a r - a s)) * C.adjugate r s +
        star ((η * (a r - a s)) * C.adjugate s r) = 0 at hs
      rw [show a s - a r = -(a r - a s) by ring, mul_neg, neg_mul, star_neg]
      linear_combination -hs
  let a' : ι → ℂ := fun k => star (a k)
  let b' : ι → ℂ := fun k => star (b k)
  have ha : diagonal a' = Aᴴ := (Matrix.diagonal_conjTranspose a).symm
  have hb : U * diagonal b' * Uᴴ = Bᴴ := by
    simp only [B, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.diagonal_conjTranspose, Matrix.mul_assoc, b']
    rfl
  have hc : diagonal a' + U * diagonal b' * Uᴴ = Cᴴ := by
    rw [ha, hb]
    change Aᴴ + Bᴴ = (A + B)ᴴ
    rw [Matrix.conjTranspose_add]
  have ht :
      star η • (Aᴴ * Cᴴ.adjugate - Cᴴ.adjugate * Aᴴ) = -T := by
    rw [← Matrix.adjugate_conjTranspose]
    have he : Tᴴ = star η • (C.adjugateᴴ * Aᴴ - Aᴴ * C.adjugateᴴ) := by
      simp only [T, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul]
    rw [← hT, he, ← smul_neg, neg_sub]
  have hp (σ : Equiv.Perm ι) :
      star (matchingProduct a b σ) = matchingProduct a' b' σ := by
    change (starRingEnd ℂ) (matchingProduct a b σ) = matchingProduct a' b' σ
    unfold matchingProduct
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro k _
    simp only [map_add, a', b', starRingEnd_apply]
  have hconj := weighted_pivot_cofactor a' b' U hU (star η) i j
  dsimp only at hconj
  rw [hc, ha, ht, Matrix.mul_neg, Matrix.neg_apply, mul_neg, sub_neg_eq_add,
    Matrix.det_conjTranspose] at hconj
  have hbase := weighted_pivot_cofactor a b U hU η i j
  change η * marginal (fun σ => signedWeight U σ * matchingProduct a b σ) i j =
    (Complex.normSq (U i j) : ℂ) * (η * C.det) - U i j * (Uᴴ * T) j i at hbase
  have hrealPart (z : ℂ) : z + star z = 2 * (z.re : ℂ) := by
    rw [Complex.star_def, Complex.add_conj, Complex.ofReal_mul, Complex.ofReal_ofNat] <;> ring
  have haverage :
      2 * marginal (fun σ => signedWeight U σ * ((η * matchingProduct a b σ).re : ℂ)) i j =
      η * marginal (fun σ => signedWeight U σ * matchingProduct a b σ) i j +
        star η * marginal (fun σ => signedWeight U σ * matchingProduct a' b' σ) i j := by
    simp only [marginal, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro σ _
    by_cases h : σ j = i
    · simp only [if_pos h, ← hp σ]
      rw [← mul_assoc, mul_comm (2 : ℂ) (signedWeight U σ), mul_assoc, ← hrealPart, star_mul']
      ring
    · simp [h]
  change _ = (Complex.normSq (U i j) : ℂ) * ((η * C.det).re : ℂ)
  apply mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0)
  rw [haverage, hbase, hconj]
  have hdet := hrealPart (η * C.det)
  rw [star_mul'] at hdet
  linear_combination (Complex.normSq (U i j) : ℂ) * hdet

/-- The real part of the stationary complex marginal uses the real signed weights. -/
theorem stationary_realSignedWeight_pivot (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) (η : ℂ)
    (hmax : ∀ V : Matrix ι ι ℂ, IsUnitary V →
      (η * determinantValue a b V).re ≤ (η * determinantValue a b U).re)
    (i j : ι) :
    (∑ σ : Equiv.Perm ι, if σ j = i then
      realSignedWeight U σ * (η * matchingProduct a b σ).re else 0) =
      Complex.normSq (U i j) * (η * determinantValue a b U).re := by
  have h := congrArg Complex.re (stationary_signedWeight_pivot a b U hU η hmax i j)
  simpa only [marginal, Complex.re_sum, apply_ite, Complex.zero_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, realSignedWeight] using h

/-- A nonzero pivot of a strictly violating complex unitary maximum
lies in an inactive permutation with negative signed weight. -/
theorem exists_negative_inactive_of_stationary_pivot (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) (η : ℂ)
    (hmax : ∀ V : Matrix ι ι ℂ, IsUnitary V →
      (η * determinantValue a b V).re ≤ (η * determinantValue a b U).re)
    (p : Equiv.Perm ι)
    (hp : ∀ σ : Equiv.Perm ι, (η * matchingProduct a b σ).re ≤
      (η * matchingProduct a b p).re)
    (hstrict : (η * matchingProduct a b p).re < (η * determinantValue a b U).re)
    {i j : ι} (hij : U i j ≠ 0) :
    ∃ σ : Equiv.Perm ι, σ j = i ∧ realSignedWeight U σ < 0 ∧
      (η * matchingProduct a b σ).re < (η * matchingProduct a b p).re := by
  classical
  let H := (η * matchingProduct a b p).re
  let F := (η * determinantValue a b U).re
  let score (σ : Equiv.Perm ι) := (η * matchingProduct a b σ).re
  have hpos : 0 < Complex.normSq (U i j) :=
    lt_of_le_of_ne (Complex.normSq_nonneg _) (Ne.symm (mt Complex.normSq_eq_zero.mp hij))
  have hid :
      (∑ σ : Equiv.Perm ι, if σ j = i then
        realSignedWeight U σ * (H - score σ) else 0) =
      Complex.normSq (U i j) * (H - F) := by
    have hterm (σ : Equiv.Perm ι) :
        (if σ j = i then realSignedWeight U σ * (H - score σ) else 0) =
        (if σ j = i then realSignedWeight U σ else 0) * H -
        (if σ j = i then realSignedWeight U σ * score σ else 0) := by
      by_cases hs : σ j = i <;> simp [hs, mul_sub]
    simp_rw [hterm]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, marginal_realSignedWeight U hU,
      mul_sub, stationary_realSignedWeight_pivot a b U hU η hmax]
  by_contra h
  have hnonnegative : 0 ≤ ∑ σ : Equiv.Perm ι, if σ j = i then
      realSignedWeight U σ * (H - score σ) else 0 := by
    apply Finset.sum_nonneg
    intro σ _
    by_cases hs : σ j = i
    · rw [if_pos hs]
      by_cases hlt : score σ < H
      · have hw : 0 ≤ realSignedWeight U σ :=
          le_of_not_gt fun hn => h ⟨σ, hs, hn, hlt⟩
        exact mul_nonneg hw (sub_nonneg.mpr (hp σ))
      · have he : score σ = H := le_antisymm (hp σ) (le_of_not_gt hlt)
        rw [he, sub_self, mul_zero]
    · rw [if_neg hs]
  rw [hid] at hnonnegative
  exact (not_lt_of_ge hnonnegative) (mul_neg_of_pos_of_neg hpos (sub_neg.mpr hstrict))

/-- The terminal contact bound can require both orbit maximality and a
negative inactive weight through every nonzero entry of the mixer. -/
theorem conjecture_iff_terminal_negative_pivots :
    Conjecture ι ↔ ¬ ∃ (U : Matrix ι ι ℂ), IsUnitary U ∧
      ∃ w : StrictMatchingSupport U,
        2 * Fintype.card ι - 1 ≤ w.contacts.card ∧
        (∀ V : Matrix ι ι ℂ, IsUnitary V →
          (w.η * determinantValue w.a w.b V).re ≤
            (w.η * determinantValue w.a w.b U).re) ∧
        ∀ i j, U i j ≠ 0 → ∃ σ : Equiv.Perm ι,
          σ j = i ∧ realSignedWeight U σ < 0 ∧ σ ∉ w.contacts := by
  classical
  rw [conjecture_iff_sharp_terminal_contact_bound]
  constructor
  · rintro h ⟨U, hU, w, hcard, _⟩
    exact h ⟨U, hU, w, hcard⟩
  · rintro h ⟨U, hU, w, hcard⟩
    obtain ⟨V, hV, hmax⟩ := exists_support_maximizer w.a w.b w.η
    let v : StrictMatchingSupport V :=
      ⟨w.a, w.b, w.η, w.pivot, w.maximal, w.strict.trans_le (hmax U hU)⟩
    apply h
    refine ⟨V, hV, v, hcard, hmax, ?_⟩
    intro i j hij
    obtain ⟨σ, hσ, hw, hlt⟩ := exists_negative_inactive_of_stationary_pivot v.a v.b V hV
      v.η hmax v.pivot v.maximal v.strict hij
    exact ⟨σ, hσ, hw, by simpa [StrictMatchingSupport.contacts] using hlt.ne⟩

end
end MOC
