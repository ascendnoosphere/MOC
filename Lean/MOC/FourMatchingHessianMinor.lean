import MOC.FourMatchingSecantWitness
import Mathlib.Algebra.Polynomial.Roots

/-! The order-four matching Hessian has vanishing thirteen-row minors on
the secant parametrization, including its degenerate strata. -/

open Matrix Polynomial

namespace MOC

private theorem matchingHessian_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (m : Fin 14 → R) :
    (fourMatchingHessian m).map f = fourMatchingHessian (fun j => f (m j)) := by
  ext i j : 1
  let v := Pi.single j (1 : R)
  have hv : (fun k => f (v k)) = Pi.single j (1 : S) := by
    funext k
    by_cases h : k = j <;> simp [v, Pi.single_apply, h]
  have h₁ := fourMatchingHessian_mulVec_apply m v i
  have h₂ := fourMatchingHessian_mulVec_apply (fun k => f (m k)) (Pi.single j (1 : S)) i
  simp only [v, Matrix.mulVec_single_one, Matrix.transpose_apply] at h₁ h₂
  change f (fourMatchingHessian m i j) = fourMatchingHessian (fun k => f (m k)) i j
  rw [h₁, h₂]
  simp only [map_sub, fourMatchingGradient_map, map_add]
  rw [show (fun k => f ((Pi.single j (1 : R)) k)) = _ from hv]

private theorem det_submatrix_eq_zero_of_finrank_le (A : Matrix (Fin 14) (Fin 14) ℂ)
    (h : Module.finrank ℂ (LinearMap.range A.mulVecLin) ≤ 12)
    (rows cols : Fin 13 → Fin 14) : (A.submatrix rows cols).det = 0 := by
  by_contra hn
  have hM : Matrix.of (fun i j => A.mulVecLin (Pi.single (cols j) 1) (rows i)) =
      A.submatrix rows cols := by
    ext i j : 1
    simp only [Matrix.of_apply, Matrix.mulVecLin_apply, Matrix.mulVec_single_one,
      Matrix.transpose_apply, Matrix.submatrix_apply]
  have hge := finrank_range_ge_of_coordinate_minor A.mulVecLin rows (fun j => Pi.single (cols j) 1)
    (by rwa [hM])
  omega

/-- Every thirteen-by-thirteen minor of the matching Hessian vanishes at
the sum of two noncrossing spectral profiles. A line to the exact regular
witness extends the rank bound across all exceptional parameters. -/
theorem fourMatchingHessian_det_secant_submatrix_eq_zero (p q : Fin 8 → ℂ)
    (rows cols : Fin 13 → Fin 14) :
    ((fourMatchingHessian (fun j =>
      fourNoncrossingCoordinates p j + fourNoncrossingCoordinates q j)).submatrix rows cols).det = 0 := by
  obtain ⟨p₁, q₁, h₁⟩ := exists_fourMatchingSecantRegular_ne_zero
  let P (i : Fin 8) : Polynomial ℂ := C (p i) + X * C (p₁ i - p i)
  let Q (i : Fin 8) : Polynomial ℂ := C (q i) + X * C (q₁ i - q i)
  let g := fourMatchingSecantRegular P Q
  let f := ((fourMatchingHessian (fun j =>
    fourNoncrossingCoordinates P j + fourNoncrossingCoordinates Q j)).submatrix rows cols).det
  have hP₁ : (fun i => (evalRingHom (1 : ℂ)) (P i)) = p₁ := by
    funext i
    simp [P] <;> ring
  have hQ₁ : (fun i => (evalRingHom (1 : ℂ)) (Q i)) = q₁ := by
    funext i
    simp [Q] <;> ring
  have hg (t : ℂ) : g.eval t =
      fourMatchingSecantRegular (fun i => (evalRingHom t) (P i)) (fun i => (evalRingHom t) (Q i)) :=
    fourMatchingSecantRegular_map (evalRingHom t) P Q
  have hgn : g ≠ 0 := by
    intro hzero
    have he := hg 1
    rw [hzero, eval_zero, hP₁, hQ₁] at he
    exact h₁ he.symm
  have hf (t : ℂ) : f.eval t = ((fourMatchingHessian (fun j =>
      fourNoncrossingCoordinates (fun i => (evalRingHom t) (P i)) j +
        fourNoncrossingCoordinates (fun i => (evalRingHom t) (Q i)) j)).submatrix rows cols).det := by
    change (evalRingHom t) f = _
    dsimp only [f]
    rw [RingHom.map_det, RingHom.mapMatrix_apply, ← Matrix.submatrix_map, matchingHessian_map]
    simp only [map_add, fourNoncrossingCoordinates_map]
  have hfg : f * g = 0 := by
    apply Polynomial.zero_of_eval_zero
    intro t
    rw [eval_mul]
    by_cases hz : g.eval t = 0
    · rw [hz, mul_zero]
    · have hgood := fourMatchingHessian_finrank_le_twelve_of_regular
        (fun i => (evalRingHom t) (P i)) (fun i => (evalRingHom t) (Q i))
        (by rw [← hg t]; exact hz)
      rw [hf, det_submatrix_eq_zero_of_finrank_le _ hgood, zero_mul]
  have hf₀ : f = 0 := (mul_eq_zero.mp hfg).resolve_right hgn
  have hP₀ : (fun i => (evalRingHom (0 : ℂ)) (P i)) = p := by
    funext i
    simp [P]
  have hQ₀ : (fun i => (evalRingHom (0 : ℂ)) (Q i)) = q := by
    funext i
    simp [Q]
  have he := hf 0
  rw [hf₀, eval_zero, hP₀, hQ₀] at he
  exact he.symm

/-- The real weighted order-four matching Hessian has vanishing
thirteen-by-thirteen minors on every spectral input. -/
theorem fourMatchingHessian_det_spectral_submatrix_eq_zero (p : Fin 8 → ℂ) (η : ℂ)
    (rows cols : Fin 13 → Fin 14) :
    ((fourMatchingHessian (fun j => (η * fourNoncrossingCoordinates p j).re)).submatrix rows cols).det = 0 := by
  obtain ⟨a, b, h⟩ := exists_noncrossing_secant_real p η
  let H := (fourMatchingHessian (fun j => (η * fourNoncrossingCoordinates p j).re)).submatrix rows cols
  have he : Complex.ofRealHom H.det = 0 := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
    dsimp only [H]
    rw [← Matrix.submatrix_map, matchingHessian_map, funext h]
    exact fourMatchingHessian_det_secant_submatrix_eq_zero a b rows cols
  exact Complex.ofReal_injective (show (H.det : ℂ) = (0 : ℝ) from he)

end MOC
