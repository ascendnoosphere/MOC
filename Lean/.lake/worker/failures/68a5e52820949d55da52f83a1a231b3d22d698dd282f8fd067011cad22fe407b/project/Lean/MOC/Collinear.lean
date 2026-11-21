import MOC.Geometry
import MOC.Normal
import MOC.Singular
import MOC.Support
import MOC.Variational

/-! Fiedler's determinant bounds for two Hermitian spectra.
At a nonsingular support maximum the scaled inverse commutator is both
Hermitian and skew-Hermitian, so the summands admit a common eigenbasis. -/

open BigOperators Matrix

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem isHermitian_diagonal_real (a : ι → ℝ) :
    (diagonal fun i => (a i : ℂ)).IsHermitian := by
  refine Matrix.isHermitian_diagonal_iff.mpr fun i => ?_
  change star (a i : ℂ) = (a i : ℂ)
  exact Complex.conj_ofReal _

private theorem star_det_of_isHermitian {M : Matrix ι ι ℂ} (hM : M.IsHermitian) :
    star M.det = M.det := by
  rw [← Matrix.det_conjTranspose, hM.eq]

private theorem commute_of_hermitian_support_max (A B : Matrix ι ι ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (r : ℝ) (hr : r ≠ 0)
    (hd : (A + B).det ≠ 0)
    (hmax : ∀ R : Matrix ι ι ℂ, IsUnitary R →
      ((r : ℂ) * (A + R * B * Rᴴ).det).re ≤ ((r : ℂ) * (A + B).det).re) :
    Commute A B := by
  let C := A + B
  let k : ℂ := (r : ℂ) * C.det
  let J := B * C⁻¹ - C⁻¹ * B
  have hC : C.IsHermitian := hA.add hB
  have hk : k ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hr) hd
  have hkstar : star k = k := by
    change star ((r : ℂ) * C.det) = (r : ℂ) * C.det
    rw [star_mul, star_det_of_isHermitian hC]
    exact congrArg (· * C.det) (Complex.conj_ofReal r)
  have hJstar : Jᴴ = -J := by
    simp only [J, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hB.eq, hC.inv.eq, neg_sub]
  have hstat : (k • J)ᴴ = k • J := support_maximum_inverse_commutator A B r hd hmax
  rw [Matrix.conjTranspose_smul, hkstar, hJstar] at hstat
  have hJneg : -J = J := (smul_right_injective (Matrix ι ι ℂ) hk) hstat
  have hJzero : J = 0 := by
    apply (smul_right_injective (Matrix ι ι ℂ) (two_ne_zero : (2 : ℂ) ≠ 0))
    rw [smul_zero, two_smul]
    calc
      J + J = -J + J := congrArg (· + J) hJneg.symm
      _ = 0 := neg_add_cancel J
  have he : B * C⁻¹ = C⁻¹ * B := sub_eq_zero.mp hJzero
  have hu : IsUnit C.det := isUnit_iff_ne_zero.mpr hd
  have hBC : B * C = C * B := calc
    B * C = C * (C⁻¹ * B) * C := by
      rw [← Matrix.mul_assoc C C⁻¹ B, C.mul_nonsing_inv hu, Matrix.one_mul]
    _ = C * (B * C⁻¹) * C := by rw [he]
    _ = C * B := by
      rw [Matrix.mul_assoc C, Matrix.mul_assoc B, C.nonsing_inv_mul hu, Matrix.mul_one]
  change B * (A + B) = (A + B) * B at hBC
  rw [Matrix.mul_add, Matrix.add_mul] at hBC
  exact add_right_cancel hBC.symm

private theorem exists_matchingProduct_of_commuting_hermitian
    (a b : ι → ℂ) (V : Matrix ι ι ℂ) (hV : IsUnitary V)
    (ha : (diagonal a).IsHermitian) (hb : (diagonal b).IsHermitian)
    (hcomm : Commute (diagonal a) (V * diagonal b * Vᴴ)) :
    ∃ σ : Equiv.Perm ι, determinantValue a b V = matchingProduct a b σ := by
  obtain ⟨x, y, Q, hQ, hx, hy⟩ := exists_simultaneous_hermitian_diagonalization
    (diagonal a) (V * diagonal b * Vᴴ) ha (hb.mul_mul_conjTranspose V) hcomm
  have hxroots : (Finset.univ : Finset ι).val.map x = Finset.univ.val.map a := by
    have h1 : IsUnitary (1 : Matrix ι ι ℂ) := by simp [IsUnitary]
    have h := roots_unitary_diagonalization a h1
    simp only [Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one] at h
    rw [← h, hx, roots_unitary_diagonalization x hQ]
  have hyroots : (Finset.univ : Finset ι).val.map y = Finset.univ.val.map b := by
    rw [← roots_unitary_diagonalization b hV, hy, roots_unitary_diagonalization y hQ]
  obtain ⟨e, he⟩ := exists_perm_of_equal_multisets x a hxroots
  obtain ⟨f, hf⟩ := exists_perm_of_equal_multisets y b hyroots
  have hd : determinantValue a b V = ∏ i, (x i + y i) := by
    unfold determinantValue
    rw [hx, hy, ← Matrix.add_mul, ← Matrix.mul_add, det_unitary_conjugation _ _ hQ,
      Matrix.diagonal_add, Matrix.det_diagonal]
  refine ⟨f.symm.trans e, ?_⟩
  rw [hd, he, hf]
  unfold matchingProduct
  rw [← Equiv.prod_comp f (fun j => a ((f.symm.trans e) j) + b j)]
  simp

/-- The determinant hull inclusion for two arbitrary real spectra. -/
theorem holds_of_real_spectra (a b : ι → ℝ) (U : Matrix ι ι ℂ) (hU : IsUnitary U) :
    Holds (fun i => (a i : ℂ)) (fun i => (b i : ℂ)) U := by
  let x : ι → ℂ := fun i => a i
  let y : ι → ℂ := fun i => b i
  have hx : (diagonal x).IsHermitian := isHermitian_diagonal_real a
  have hy : (diagonal y).IsHermitian := isHermitian_diagonal_real b
  change Holds x y U
  apply (holds_iff_directional x y U).mpr
  intro η
  have hreal (V : Matrix ι ι ℂ) : (determinantValue x y V).im = 0 :=
    Complex.conj_eq_iff_im.mp
      (star_det_of_isHermitian (hx.add (hy.mul_mul_conjTranspose V)))
  have hη (V : Matrix ι ι ℂ) : (η * determinantValue x y V).re =
      ((η.re : ℂ) * determinantValue x y V).re := by
    simp only [Complex.mul_re, hreal, mul_zero, sub_zero, Complex.ofReal_re]
  by_cases hzero : η.re = 0
  · have hid : determinantValue x y 1 = matchingProduct x y (Equiv.refl ι) := by
      simp [determinantValue, matchingProduct]
    refine ⟨Equiv.refl ι, ?_⟩
    rw [← hid, hη U, hη 1, hzero, Complex.ofReal_zero, zero_mul, zero_mul]
  obtain ⟨V, hV, hmax⟩ := exists_support_maximizer x y (η.re : ℂ)
  have hbound : (η * determinantValue x y U).re ≤ (η * determinantValue x y V).re := by
    rw [hη U, hη V]
    exact hmax U hU
  have hVbound : ∃ σ : Equiv.Perm ι,
      (η * determinantValue x y V).re ≤ (η * matchingProduct x y σ).re := by
    by_cases hd : determinantValue x y V = 0
    · exact (holds_iff_directional x y V).mp (holds_of_singular x y hV hd) η
    let B := V * diagonal y * Vᴴ
    have hB : B.IsHermitian := hy.mul_mul_conjTranspose V
    have hmax' (R : Matrix ι ι ℂ) (hR : IsUnitary R) :
        ((η.re : ℂ) * (diagonal x + R * B * Rᴴ).det).re ≤
          ((η.re : ℂ) * (diagonal x + B).det).re := by
      have hR' : IsUnitary Rᴴ := ⟨by simpa using hR.2, by simpa using hR.1⟩
      have hRV : IsUnitary (R * V) := by
        simpa only [Matrix.conjTranspose_conjTranspose] using relative_unitary Rᴴ V hR' hV
      simpa only [determinantValue, B, Matrix.conjTranspose_mul, Matrix.mul_assoc] using
        hmax (R * V) hRV
    have hcomm := commute_of_hermitian_support_max (diagonal x) B hx hB η.re hzero hd hmax'
    obtain ⟨σ, hσ⟩ := exists_matchingProduct_of_commuting_hermitian x y V hV hx hy hcomm
    exact ⟨σ, by rw [hσ]⟩
  obtain ⟨σ, hσ⟩ := hVbound
  exact ⟨σ, hbound.trans hσ⟩

/-- A common complex scaling and opposite translations preserve the real-spectrum case. -/
theorem holds_of_scaled_shifted_real_spectra (a b : ι → ℝ) (c t : ℂ)
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) :
    Holds (fun i => c * (a i : ℂ) + t) (fun i => c * (b i : ℂ) - t) U := by
  apply (holds_shift_iff _ _ hU t).mpr
  exact hull_of_common_factor (determinantValue_scale _ _ U c)
    (matchingProduct_scale _ _ c) (holds_of_real_spectra a b U hU)

end

end MOC
