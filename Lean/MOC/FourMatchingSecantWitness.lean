import MOC.FourMatchingSecantDifferential
import Mathlib.Data.ZMod.Basic

/-! An exact witness for twelve independent secant tangent coordinates. -/

open Matrix
open scoped BigOperators

namespace MOC

variable {R : Type*} [CommRing R]

private def secantRows : Fin 12 → Fin 14 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 13]

private def secantDirection (j : Fin 12) : (Fin 8 → R) × (Fin 8 → R) :=
  (fun i => if j.val < 6 ∧ i.val = j.val then 1 else 0,
    fun i => if 6 ≤ j.val ∧ i.val = j.val - 6 then 1 else 0)

/-- A fixed twelve-by-twelve minor of the secant derivative. -/
def fourMatchingSecantMinor (p q : Fin 8 → R) : Matrix (Fin 12) (Fin 12) R :=
  fun i j => fourMatchingSecantDifferential p q (secantDirection j) (secantRows i)

/-- This derivative minor is polynomial over the integers. -/
theorem fourMatchingSecantMinor_map {S : Type*} [CommRing S] (f : R →+* S) (p q : Fin 8 → R) :
    (fourMatchingSecantMinor p q).map f =
      fourMatchingSecantMinor (fun i => f (p i)) (fun i => f (q i)) := by
  ext i j : 1
  simp only [Matrix.map_apply, fourMatchingSecantMinor]
  let d := secantDirection (R := R) j
  change f (fourMatchingSecantDifferential p q (d.1, d.2) (secantRows i)) = _
  have hd : ((fun k => f (d.1 k)), fun k => f (d.2 k)) = secantDirection (R := S) j := by
    apply Prod.ext <;> funext k <;> simp [d, secantDirection, apply_ite f]
  rw [fourMatchingSecantDifferential_map, hd]

private def witnessLeft : Fin 8 → R := ![3, 3, 0, 1, 2, 2, 2, 1]

private def witnessRight : Fin 8 → R := ![0, 1, 2, 1, 1, 2, 3, 0]

private def witnessInverse : Matrix (Fin 12) (Fin 12) (ZMod 5) :=
  !![0, 1, 4, 3, 0, 0, 1, 1, 2, 4, 0, 4;
     0, 1, 1, 3, 0, 0, 1, 1, 2, 4, 0, 4;
     0, 1, 2, 4, 0, 0, 1, 4, 2, 0, 0, 0;
     1, 3, 2, 0, 0, 1, 3, 2, 2, 4, 0, 2;
     1, 2, 0, 0, 0, 1, 2, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0;
     2, 4, 0, 0, 0, 2, 4, 0, 0, 4, 2, 0;
     4, 2, 0, 0, 2, 2, 4, 0, 0, 4, 2, 0;
     3, 4, 0, 0, 0, 2, 1, 0, 0, 1, 2, 0;
     4, 4, 0, 0, 2, 2, 1, 0, 0, 1, 2, 0;
     4, 4, 0, 2, 2, 2, 1, 0, 0, 1, 2, 0;
     0, 1, 0, 2, 2, 2, 1, 0, 0, 1, 2, 0]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
private theorem witnessInverse_check :
    fourMatchingSecantMinor witnessLeft witnessRight * witnessInverse = 1 := by
  decide +kernel

private theorem witnessLeft_cast (S : Type*) [CommRing S] :
    (fun j => (Int.castRingHom S) (witnessLeft (R := ℤ) j)) = witnessLeft (R := S) := by
  funext j
  fin_cases j <;> simp [witnessLeft]

private theorem witnessRight_cast (S : Type*) [CommRing S] :
    (fun j => (Int.castRingHom S) (witnessRight (R := ℤ) j)) = witnessRight (R := S) := by
  funext j
  fin_cases j <;> simp [witnessRight]

private theorem witnessMinor_det_ne_zero :
    (fourMatchingSecantMinor (R := ℂ) witnessLeft witnessRight).det ≠ 0 := by
  let T := fourMatchingSecantMinor (R := ℤ) witnessLeft witnessRight
  have hmap (S : Type*) [CommRing S] :
      T.map (Int.castRingHom S) = fourMatchingSecantMinor witnessLeft witnessRight := by
    rw [fourMatchingSecantMinor_map, witnessLeft_cast, witnessRight_cast]
  have hdet : T.det ≠ 0 := by
    intro hz
    have he :
        (fourMatchingSecantMinor (R := ZMod 5) witnessLeft witnessRight).det = 0 := by
      simpa only [RingHom.mapMatrix_apply, hmap (ZMod 5), hz, map_zero] using
        ((Int.castRingHom (ZMod 5)).map_det T).symm
    have h := congrArg Matrix.det witnessInverse_check
    rw [Matrix.det_mul, he, zero_mul, Matrix.det_one] at h
    exact zero_ne_one h
  intro hz
  have he := (Int.castRingHom ℂ).map_det T
  rw [RingHom.mapMatrix_apply, hmap ℂ, hz] at he
  exact hdet (Int.cast_injective (show (T.det : ℂ) = ↑(0 : ℤ) by simpa using he))

/-- A nonzero coordinate minor gives a matching lower bound on image dimension. -/
theorem finrank_range_ge_of_coordinate_minor {V : Type*} [AddCommGroup V] [Module ℂ V] {k : ℕ}
    (J : V →ₗ[ℂ] (Fin 14 → ℂ)) (rows : Fin k → Fin 14) (cols : Fin k → V)
    (hnz : (Matrix.of (fun i j => J (cols j) (rows i))).det ≠ 0) :
    k ≤ Module.finrank ℂ (LinearMap.range J) := by
  let M : Matrix (Fin k) (Fin k) ℂ := Matrix.of (fun i j => J (cols j) (rows i))
  let P := LinearMap.funLeft ℂ ℂ rows
  let B : (Fin k → ℂ) →ₗ[ℂ] V := ∑ j, (LinearMap.proj j).smulRight (cols j)
  have he : P.comp (J.comp B) = M.mulVecLin := by
    apply LinearMap.ext
    intro x
    funext i
    simp [P, B, M, LinearMap.sum_apply, LinearMap.funLeft_apply, LinearMap.smulRight_apply,
      Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, mul_comm]
  let J' := (J.comp B).codRestrict (LinearMap.range J) (fun x => ⟨B x, rfl⟩)
  have hu : IsUnit M := Matrix.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hnz)
  have hJ' : Function.Injective J' := by
    intro x y hxy
    apply Matrix.mulVec_injective_iff_isUnit.mpr hu
    change M.mulVecLin x = M.mulVecLin y
    rw [← he]
    exact congrArg (fun z : LinearMap.range J => P z.val) hxy
  have hdim := LinearMap.finrank_le_finrank_of_injective hJ'
  simpa [Module.finrank_fintype_fun_eq_card] using hdim

private def frameColumns : Fin 4 → Fin 8 := ![0, 1, 2, 3]

private def frameBasis (p q : Fin 8 → R) : Matrix (Fin 4) (Fin 4) R :=
  (fourMatchingSegreMatrix p q).submatrix id frameColumns

private def frameColumn (p q : Fin 8 → R) : Fin 4 → R :=
  fun i => fourMatchingSegreMatrix p q i 6

/-- The selected secant minor and all five frame determinants are
simultaneously nonzero exactly where this polynomial is nonzero. -/
def fourMatchingSecantRegular (p q : Fin 8 → R) : R :=
  (fourMatchingSecantMinor p q).det *
    ((frameBasis p q).det * ∏ i, ((frameBasis p q).updateCol i (frameColumn p q)).det)

/-- The chart polynomial commutes with ring evaluation. -/
theorem fourMatchingSecantRegular_map {S : Type*} [CommRing S] (f : R →+* S) (p q : Fin 8 → R) :
    f (fourMatchingSecantRegular p q) =
      fourMatchingSecantRegular (fun j => f (p j)) (fun j => f (q j)) := by
  have hX : (fourMatchingSegreMatrix p q).map f =
      fourMatchingSegreMatrix (fun j => f (p j)) (fun j => f (q j)) := by
    ext i j : 1
    fin_cases i <;> simp [fourMatchingSegreMatrix, Matrix.map_apply]
  have hb : (frameBasis p q).map f =
      frameBasis (fun j => f (p j)) (fun j => f (q j)) := by
    simp only [frameBasis, ← Matrix.submatrix_map, hX]
  have hc : (f ∘ frameColumn p q) = frameColumn (fun j => f (p j)) (fun j => f (q j)) := by
    funext i
    exact congrArg (fun A : Matrix (Fin 4) (Fin 8) S => A i 6) hX
  simp only [fourMatchingSecantRegular, map_mul, map_prod, RingHom.map_det, RingHom.mapMatrix_apply,
    fourMatchingSecantMinor_map, Matrix.map_updateCol, hb, hc]

private theorem witnessFrame_det_check :
    (frameBasis (R := ℤ) witnessLeft witnessRight).det = 6 := by
  decide +kernel

private theorem witnessFrame_replacement_check (i : Fin 4) :
    ((frameBasis (R := ℤ) witnessLeft witnessRight).updateCol i
      (frameColumn witnessLeft witnessRight)).det = ![-8, 13, 4, -3] i := by
  fin_cases i <;> decide +kernel

/-- The regular chart has a common exact witness for all its factors. -/
theorem exists_fourMatchingSecantRegular_ne_zero :
    ∃ p q : Fin 8 → ℂ, fourMatchingSecantRegular p q ≠ 0 := by
  refine ⟨witnessLeft, witnessRight, ?_⟩
  have hmin := witnessMinor_det_ne_zero
  have hframe : (frameBasis (R := ℂ) witnessLeft witnessRight).det *
      (∏ i, ((frameBasis witnessLeft witnessRight).updateCol i
        (frameColumn witnessLeft witnessRight)).det) ≠ 0 := by
    have hZ :
        (frameBasis (R := ℤ) witnessLeft witnessRight).det *
          (∏ i, ((frameBasis witnessLeft witnessRight).updateCol i
            (frameColumn witnessLeft witnessRight)).det) ≠ 0 := by
      rw [witnessFrame_det_check]
      simp_rw [witnessFrame_replacement_check]
      norm_num [Fin.prod_univ_four]
    have hX : (fourMatchingSegreMatrix (R := ℤ) witnessLeft witnessRight).map (Int.castRingHom ℂ) =
        fourMatchingSegreMatrix (R := ℂ) witnessLeft witnessRight := by
      have hp (j : Fin 8) := congrFun (witnessLeft_cast ℂ) j
      have hq (j : Fin 8) := congrFun (witnessRight_cast ℂ) j
      ext i j : 1
      fin_cases i <;> simp [fourMatchingSegreMatrix, Matrix.map_apply, hp, hq]
    have hb : (frameBasis (R := ℤ) witnessLeft witnessRight).map (Int.castRingHom ℂ) =
        frameBasis (R := ℂ) witnessLeft witnessRight := by
      simp only [frameBasis, ← Matrix.submatrix_map, hX]
    have hc : (Int.castRingHom ℂ) ∘ frameColumn (R := ℤ) witnessLeft witnessRight =
        frameColumn (R := ℂ) witnessLeft witnessRight := by
      funext i
      exact congrArg (fun A : Matrix (Fin 4) (Fin 8) ℂ => A i 6) hX
    intro h
    apply hZ
    apply Int.cast_injective (R := ℂ)
    change (Int.castRingHom ℂ) _ = (Int.castRingHom ℂ) 0
    simpa only [map_mul, map_prod, RingHom.map_det, RingHom.mapMatrix_apply,
      Matrix.map_updateCol, hb, hc, map_zero] using h
  exact mul_ne_zero hmin hframe

/-- Nonvanishing of the regular chart polynomial supplies the rank-twelve
bound, with Cramer's rule supplying the fifth column coordinates. -/
theorem fourMatchingHessian_finrank_le_twelve_of_regular (p q : Fin 8 → ℂ)
    (h : fourMatchingSecantRegular p q ≠ 0) :
    Module.finrank ℂ (LinearMap.range (fourMatchingHessian
      (fun j => fourNoncrossingCoordinates p j + fourNoncrossingCoordinates q j)).mulVecLin) ≤ 12 := by
  obtain ⟨hJ, hframe⟩ := mul_ne_zero_iff.mp h
  obtain ⟨hP, hrep⟩ := mul_ne_zero_iff.mp hframe
  let P := frameBasis p q
  let b := frameColumn p q
  let v := P⁻¹.mulVec b
  have hPd : IsUnit P.det := isUnit_iff_ne_zero.mpr hP
  have hPv : P.mulVec v = b := by
    simp only [v, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv P hPd, Matrix.one_mulVec]
  have hv (i : Fin 4) : v i ≠ 0 := by
    intro hz
    have he := congrFun (Matrix.det_smul_inv_mulVec_eq_cramer P b hPd) i
    have he' : P.det * v i = (P.updateCol i b).det := by
      simpa only [Matrix.cramer_apply, Pi.smul_apply, smul_eq_mul, v] using he
    have hh : (P.updateCol i b).det = 0 := by
      rw [← he', hz, mul_zero]
    exact Finset.prod_ne_zero_iff.mp hrep i (Finset.mem_univ i) hh
  exact fourMatchingHessian_finrank_le_twelve_of_secant_frame p q frameColumns 6 v
    (Matrix.isUnit_iff_isUnit_det.mpr hPd) hv hPv
    (finrank_range_ge_of_coordinate_minor _ secantRows secantDirection hJ)

end MOC
