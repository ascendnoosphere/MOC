import MOC.FourMatchingRelations
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! The matching gradient of a secant sum factors through complementary
minors of the two spectra's Segre matrix. -/

open Matrix
open scoped BigOperators ComplexConjugate

namespace MOC

variable {R : Type*} [CommRing R]

/-- The Segre embedding of two affine eight-point configurations. -/
def fourMatchingSegreMatrix (p q : Fin 8 → R) : Matrix (Fin 4) (Fin 8) R :=
  fun i j => ![1, p j, q j, p j * q j] i

private def segreBlocks : Fin 14 → (Fin 4 → Fin 8) × (Fin 4 → Fin 8) :=
  ![(![0, 1, 2, 3], ![4, 5, 6, 7]), (![0, 1, 2, 4], ![3, 5, 6, 7]),
    (![0, 1, 2, 5], ![3, 4, 6, 7]), (![0, 1, 2, 6], ![3, 4, 5, 7]),
    (![0, 1, 3, 4], ![2, 5, 6, 7]), (![0, 1, 3, 5], ![2, 4, 6, 7]),
    (![0, 1, 3, 6], ![2, 4, 5, 7]), (![0, 1, 4, 5], ![2, 3, 6, 7]),
    (![0, 1, 4, 6], ![2, 3, 5, 7]), (![0, 2, 3, 4], ![1, 5, 6, 7]),
    (![0, 2, 3, 5], ![1, 4, 6, 7]), (![0, 2, 3, 6], ![1, 4, 5, 7]),
    (![0, 2, 4, 5], ![1, 3, 6, 7]), (![0, 2, 4, 6], ![1, 3, 5, 7])]

private def segreProducts (X : Matrix (Fin 4) (Fin 8) R) (i : Fin 14) : R :=
  (X.submatrix id (segreBlocks i).1).det * (X.submatrix id (segreBlocks i).2).det

private def segreGradient (d : Fin 14 → R) : Fin 14 → R :=
  ![4 * d 0 - 4 * d 1 + 2 * d 2 - 2 * d 3 + 2 * d 4 - d 5 + d 6 +
      d 7 - d 8 - 2 * d 9 + d 10 - d 11 - d 12 + d 13,
    2 * d 0 - 2 * d 1 + 2 * d 2 + d 4 - d 5 + d 7 - d 9 + d 10 - d 12,
    3 * d 0 - d 1 + d 2 - d 3 + d 4 - d 5 + d 6 - d 9 + d 10 - d 11,
    2 * d 0 - d 1 + d 2 + d 4 - d 5 - d 9 + d 10,
    d 0 - d 1 + d 4 - d 9,
    2 * d 0 - 2 * d 1 + d 2 - d 3 + 2 * d 4 - d 5 + d 6 + d 7 - d 8,
    d 0 - d 1 + d 2 + d 4 - d 5 + d 7,
    2 * d 0 - d 1 + d 2 - d 3 + d 4 - d 5 + d 6,
    d 0 - d 1 + d 2 - d 3,
    2 * d 0 - d 1 + d 2 + d 4 - d 5,
    d 0 - d 1 + d 4,
    d 0 - d 1 + d 2,
    d 0 - d 1,
    d 0]

/-- A fixed linear combination of complementary products of maximal minors. -/
def fourSegreResponse (X : Matrix (Fin 4) (Fin 8) R) : Fin 14 → R :=
  segreGradient (segreProducts X)

/-- The Segre response is polynomial over the integers and commutes with
ring homomorphisms. -/
theorem fourSegreResponse_map {S : Type*} [CommRing S] (f : R →+* S)
    (X : Matrix (Fin 4) (Fin 8) R) (i : Fin 14) :
    f (fourSegreResponse X i) = fourSegreResponse (X.map f) i := by
  have hminor (I : Fin 4 → Fin 8) :
      f ((X.submatrix id I).det) = ((X.map f).submatrix id I).det := by
    rw [RingHom.map_det]
    congr 1
    ext a b
    simp [Matrix.submatrix_apply, Matrix.map_apply]
  have hprod (j : Fin 14) : f (segreProducts X j) = segreProducts (X.map f) j := by
    simp only [segreProducts, map_mul, hminor]
  fin_cases i <;>
    simp only [fourSegreResponse, segreGradient, Matrix.cons_val, hprod, map_add, map_sub,
      map_mul, map_ofNat]

private theorem finFour_succAbove_table :
    ∀ (i : Fin 4) (j : Fin 3),
      i.succAbove j = ![![1, 2, 3], ![0, 2, 3], ![0, 1, 3], ![0, 1, 2]] i j := by
  decide +kernel

private theorem finThree_succ_table :
    ∀ j : Fin 3, Fin.succ j = ![1, 2, 3] j := by
  decide +kernel

private theorem segre_minor_eq (p q : Fin 8 → R) (I : Fin 4 → Fin 8) :
    ((fourMatchingSegreMatrix p q).submatrix id I).det =
      (p (I 0) - p (I 1)) * (p (I 2) - p (I 3)) *
        (q (I 0) - q (I 2)) * (q (I 1) - q (I 3)) -
      (p (I 0) - p (I 2)) * (p (I 1) - p (I 3)) *
        (q (I 0) - q (I 1)) * (q (I 2) - q (I 3)) := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four, Matrix.det_fin_three, Matrix.submatrix_apply, id_eq,
    finFour_succAbove_table, finThree_succ_table, fourMatchingSegreMatrix, Matrix.cons_val]
  norm_num <;> ring

-- Each Segre minor splits into two products of four brackets. Grouping
-- their complementary products first keeps the gradient check quadratic.
private def segreMatchings (d : Fin 8 → Fin 8 → R) : Fin 32 → R :=
  ![d 0 1 * d 2 3 * d 4 5 * d 6 7,
    d 0 1 * d 2 3 * d 4 6 * d 5 7,
    d 0 1 * d 2 4 * d 3 5 * d 6 7,
    d 0 1 * d 2 4 * d 3 6 * d 5 7,
    d 0 1 * d 2 5 * d 3 4 * d 6 7,
    d 0 1 * d 2 5 * d 3 6 * d 4 7,
    d 0 1 * d 2 5 * d 3 7 * d 4 6,
    d 0 1 * d 2 6 * d 3 4 * d 5 7,
    d 0 1 * d 2 6 * d 3 5 * d 4 7,
    d 0 1 * d 2 6 * d 3 7 * d 4 5,
    d 0 2 * d 1 3 * d 4 5 * d 6 7,
    d 0 2 * d 1 3 * d 4 6 * d 5 7,
    d 0 2 * d 1 4 * d 3 5 * d 6 7,
    d 0 2 * d 1 4 * d 3 6 * d 5 7,
    d 0 2 * d 1 5 * d 3 4 * d 6 7,
    d 0 2 * d 1 5 * d 3 6 * d 4 7,
    d 0 2 * d 1 5 * d 3 7 * d 4 6,
    d 0 2 * d 1 6 * d 3 4 * d 5 7,
    d 0 2 * d 1 6 * d 3 5 * d 4 7,
    d 0 2 * d 1 6 * d 3 7 * d 4 5,
    d 0 3 * d 1 4 * d 2 5 * d 6 7,
    d 0 3 * d 1 4 * d 2 6 * d 5 7,
    d 0 3 * d 1 5 * d 2 4 * d 6 7,
    d 0 3 * d 1 5 * d 2 6 * d 4 7,
    d 0 3 * d 1 6 * d 2 4 * d 5 7,
    d 0 3 * d 1 6 * d 2 5 * d 4 7,
    d 0 4 * d 1 3 * d 2 5 * d 6 7,
    d 0 4 * d 1 3 * d 2 6 * d 5 7,
    d 0 4 * d 1 5 * d 2 3 * d 6 7,
    d 0 4 * d 1 5 * d 2 6 * d 3 7,
    d 0 4 * d 1 6 * d 2 3 * d 5 7,
    d 0 4 * d 1 6 * d 2 5 * d 3 7]

private def straightenedSegreMatchings (u : Fin 14 → R) : Fin 32 → R :=
  ![u 0,
    u 0 + u 1,
    u 0 + u 2,
    u 0 + u 1 + u 2 + u 3,
    u 2,
    u 0 + u 1 + u 2 + u 3 + u 4,
    u 0 + u 1 + u 3 + u 4,
    u 2 + u 3,
    u 0 + u 2 + u 3 + u 4,
    u 0 + u 4,
    u 0 + u 5,
    u 0 + u 1 + u 5 + u 6,
    u 0 + u 2 + u 5 + u 7,
    u 0 + u 1 + u 2 + u 3 + u 5 + u 6 + u 7 + u 9,
    u 2 + u 7,
    u 0 + u 1 + u 2 + u 3 + u 4 + u 5 + u 6 + u 7 + u 9 + u 10,
    u 0 + u 1 + u 3 + u 4 + u 5 + u 6 + u 9 + u 10,
    u 2 + u 3 + u 7 + u 9,
    u 0 + u 2 + u 3 + u 4 + u 5 + u 7 + u 9 + u 10,
    u 0 + u 4 + u 5 + u 10,
    u 0 + u 2 + u 5 + u 7 + u 8,
    u 0 + u 1 + u 2 + u 3 + u 5 + u 6 + u 7 + u 8 + u 9 + u 11,
    u 0 + u 2 + u 7 + u 8,
    2 * u 0 + u 1 + u 2 + u 3 + u 4 + u 5 + u 6 + u 7 + u 8 + u 9 + u 10 + u 11 + u 12,
    u 0 + u 1 + u 2 + u 3 + u 7 + u 8 + u 9 + u 11,
    2 * u 0 + u 1 + u 2 + u 3 + u 4 + u 5 + u 7 + u 8 + u 9 + u 10 + u 11 + u 12,
    u 0 + u 5 + u 7 + u 8,
    u 0 + u 1 + u 5 + u 6 + u 7 + u 8 + u 9 + u 11,
    u 0 + u 8,
    2 * u 0 + u 1 + u 2 + u 3 + u 4 + u 5 + u 6 + u 7 + u 8 + 2 * u 9 + u 10 + u 11 + u 12 + u 13,
    u 0 + u 1 + u 8 + u 11,
    2 * u 0 + u 1 + u 2 + u 3 + u 4 + u 5 + u 7 + u 8 + u 9 + u 10 + u 11 + u 12 + u 13]

private def segreMatchingIndices : Fin 14 → Fin 4 → Fin 32 :=
  ![![0, 1, 10, 11],
    ![2, 3, 12, 13],
    ![4, 5, 14, 15],
    ![7, 8, 17, 18],
    ![4, 7, 20, 21],
    ![2, 8, 22, 23],
    ![3, 5, 24, 25],
    ![0, 9, 28, 29],
    ![1, 6, 30, 31],
    ![14, 17, 22, 24],
    ![12, 18, 20, 25],
    ![13, 15, 21, 23],
    ![10, 19, 26, 31],
    ![11, 16, 27, 29]]

private def segreMatchingCombination (u v : Fin 32 → R) (i : Fin 14) : R :=
  let j := segreMatchingIndices i
  u (j 0) * v (j 3) - u (j 1) * v (j 2) - u (j 2) * v (j 1) + u (j 3) * v (j 0)

set_option maxHeartbeats 2000000 in
private theorem segreMatchings_straightened (p : Fin 8 → R) :
    segreMatchings (fun i j => p i - p j) =
      straightenedSegreMatchings (fourNoncrossingCoordinates p) := by
  funext i
  fin_cases i <;>
    dsimp only [segreMatchings, straightenedSegreMatchings,
      fourNoncrossingCoordinates, fourBracketCoordinates, Matrix.cons_val] <;> ring

private def segreBracketMinor (d e : Fin 8 → Fin 8 → R) (I : Fin 4 → Fin 8) : R :=
  d (I 0) (I 1) * d (I 2) (I 3) * e (I 0) (I 2) * e (I 1) (I 3) -
    d (I 0) (I 2) * d (I 1) (I 3) * e (I 0) (I 1) * e (I 2) (I 3)

set_option maxHeartbeats 1000000 in
private theorem segreBracketMinor_mul (d e : Fin 8 → Fin 8 → R) (i : Fin 14) :
    segreBracketMinor d e (segreBlocks i).1 * segreBracketMinor d e (segreBlocks i).2 =
      segreMatchingCombination (segreMatchings d) (segreMatchings e) i := by
  fin_cases i <;>
    dsimp only [segreBracketMinor, segreBlocks, segreMatchingCombination,
      segreMatchingIndices, segreMatchings, Matrix.cons_val] <;> ring

private theorem segreProducts_straightened (p q : Fin 8 → R) :
    segreProducts (fourMatchingSegreMatrix p q) =
      segreMatchingCombination (straightenedSegreMatchings (fourNoncrossingCoordinates p))
        (straightenedSegreMatchings (fourNoncrossingCoordinates q)) := by
  funext i
  simp only [segreProducts, segre_minor_eq]
  change segreBracketMinor (fun i j => p i - p j) (fun i j => q i - q j) (segreBlocks i).1 *
    segreBracketMinor (fun i j => p i - p j) (fun i j => q i - q j) (segreBlocks i).2 = _
  simp only [segreBracketMinor_mul, segreMatchings_straightened]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem segreGradient_polarized (p q : Fin 14 → R) (i : Fin 14) :
    fourMatchingGradient (fun j => p j + q j) i -
      fourMatchingGradient p i - fourMatchingGradient q i =
      segreGradient (segreMatchingCombination (straightenedSegreMatchings p)
        (straightenedSegreMatchings q)) i := by
  fin_cases i <;>
    dsimp only [fourMatchingGradient, segreGradient, segreMatchingCombination,
      segreMatchingIndices, straightenedSegreMatchings, Matrix.cons_val] <;> ring

/-- The secant gradient agrees with the complementary-minor map on the
Segre matrix of the two configurations. -/
theorem fourMatchingGradient_segre (p q : Fin 8 → R) (i : Fin 14) :
    fourMatchingGradient (fun j => fourNoncrossingCoordinates p j + fourNoncrossingCoordinates q j) i =
      fourSegreResponse (fourMatchingSegreMatrix p q) i := by
  have h := segreGradient_polarized (fourNoncrossingCoordinates p) (fourNoncrossingCoordinates q) i
  simpa only [fourSegreResponse, segreProducts_straightened, fourMatchingGradient_noncrossing,
    sub_zero] using h

private theorem segreProducts_mul_left (L : Matrix (Fin 4) (Fin 4) R)
    (X : Matrix (Fin 4) (Fin 8) R) (i : Fin 14) :
    segreProducts (L * X) i = L.det ^ 2 * segreProducts X i := by
  have hsub (I : Fin 4 → Fin 8) :
      (L * X).submatrix id I = L * (X.submatrix id I) := by
    rw [Matrix.submatrix_mul L X id id I Function.bijective_id, Matrix.submatrix_id_id]
  simp only [segreProducts, hsub, Matrix.det_mul]
  ring

/-- Row operations of determinant one preserve the Segre response. -/
theorem fourSegreResponse_mul_left (L : Matrix (Fin 4) (Fin 4) R)
    (X : Matrix (Fin 4) (Fin 8) R) (hL : L.det = 1) :
    fourSegreResponse (L * X) = fourSegreResponse X := by
  have h : segreProducts (L * X) = segreProducts X := by
    funext i
    simp only [segreProducts_mul_left, hL, one_pow, one_mul]
  unfold fourSegreResponse
  rw [h]

private theorem segreBlockProduct (c : Fin 8 → R) (i : Fin 14) :
    (∏ j, c ((segreBlocks i).1 j)) * (∏ j, c ((segreBlocks i).2 j)) = ∏ j, c j := by
  fin_cases i <;> simp [segreBlocks, Fin.prod_univ_succ] <;> ring

private theorem segreProducts_mul_diagonal (X : Matrix (Fin 4) (Fin 8) R) (c : Fin 8 → R)
    (i : Fin 14) : segreProducts (X * diagonal c) i = (∏ j, c j) * segreProducts X i := by
  have hsub (I : Fin 4 → Fin 8) :
      ((X * diagonal c).submatrix id I).det =
        (∏ j, c (I j)) * (X.submatrix id I).det := by
    rw [← Matrix.det_mul_row (fun j => c (I j)) (X.submatrix id I)]
    congr 1
    ext r j : 1
    simp [Matrix.mul_diagonal, mul_comm]
  simp only [segreProducts, hsub, ← segreBlockProduct c i]
  ring

/-- Rescaling the columns by a family with product one preserves the
Segre response. -/
theorem fourSegreResponse_mul_diagonal (X : Matrix (Fin 4) (Fin 8) R) (c : Fin 8 → R)
    (hc : (∏ j, c j) = 1) :
    fourSegreResponse (X * diagonal c) = fourSegreResponse X := by
  have h : segreProducts (X * diagonal c) = segreProducts X := by
    funext i
    simp only [segreProducts_mul_diagonal, hc, one_mul]
  unfold fourSegreResponse
  rw [h]

private theorem noncrossing_scale (p : Fin 8 → R) (z : R) (i : Fin 14) :
    fourNoncrossingCoordinates (fun j => z * p j) i = z ^ 4 * fourNoncrossingCoordinates p i := by
  fin_cases i <;> simp [fourNoncrossingCoordinates, fourBracketCoordinates] <;> ring

/-- Real weighted matching profiles lie on the complex secant
parametrization, including zero weights and repeated points. -/
theorem exists_noncrossing_secant_real (p : Fin 8 → ℂ) (η : ℂ) :
    ∃ x y : Fin 8 → ℂ, ∀ i,
      ((η * fourNoncrossingCoordinates p i).re : ℂ) =
        fourNoncrossingCoordinates x i + fourNoncrossingCoordinates y i := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (η / 2) (n := 4) (by decide)
  let x (j : Fin 8) := z * p j
  refine ⟨x, fun j => conj (x j), fun i => ?_⟩
  have hconj (i : Fin 14) :
      fourNoncrossingCoordinates (fun j => conj (x j)) i = conj (fourNoncrossingCoordinates x i) := by
    fin_cases i <;> simp [fourNoncrossingCoordinates, fourBracketCoordinates, map_sub, map_mul]
  have hx : fourNoncrossingCoordinates x i = (η * fourNoncrossingCoordinates p i) / 2 := by
    change fourNoncrossingCoordinates (fun j => z * p j) i = _
    rw [noncrossing_scale, hz]
    ring
  rw [hconj, hx, Complex.re_eq_add_conj, add_div]
  simp only [map_div₀, map_ofNat]

end MOC
