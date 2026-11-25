import MOC.Weights
import MOC.Variational
import MOC.ZhengContactReduction
import MOC.OrderFourIndependent
import MOC.Singular

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
