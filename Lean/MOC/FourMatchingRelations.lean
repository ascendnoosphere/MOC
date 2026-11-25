import MOC.ContactCensus
import MOC.FourContactCertificate
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.LinearCombination

/-! Spectral vanishing of the matching cubic in Zheng's noncrossing basis. -/

open BigOperators
open scoped ComplexConjugate

namespace MOC

noncomputable section

/-- Noncrossing matching products written in bracket coordinates. -/
def fourBracketCoordinates {R : Type*} [CommRing R]
    (d : Fin 8 → Fin 8 → R) : Fin 14 → R :=
  ![d 0 1 * d 2 3 * d 4 5 * d 6 7,
    d 0 1 * d 2 3 * d 4 7 * d 5 6,
    d 0 1 * d 2 5 * d 3 4 * d 6 7,
    d 0 1 * d 2 7 * d 3 4 * d 5 6,
    d 0 1 * d 2 7 * d 3 6 * d 4 5,
    d 0 3 * d 1 2 * d 4 5 * d 6 7,
    d 0 3 * d 1 2 * d 4 7 * d 5 6,
    d 0 5 * d 1 2 * d 3 4 * d 6 7,
    d 0 5 * d 1 4 * d 2 3 * d 6 7,
    d 0 7 * d 1 2 * d 3 4 * d 5 6,
    d 0 7 * d 1 2 * d 3 6 * d 4 5,
    d 0 7 * d 1 4 * d 2 3 * d 5 6,
    d 0 7 * d 1 6 * d 2 3 * d 4 5,
    d 0 7 * d 1 6 * d 2 5 * d 3 4]

/-- The noncrossing matching products (A.1) for the eight affine points
`(u i, 1)`. In this chart each bracket is the difference of its two labels. -/
def fourNoncrossingCoordinates {R : Type*} [CommRing R] (u : Fin 8 → R) : Fin 14 → R :=
  fourBracketCoordinates (fun i j => u i - u j)

private theorem difference_plucker {R : Type*} [CommRing R] (u : Fin 8 → R)
    (i j k l : Fin 8) :
    (u i - u j) * (u k - u l) + (u i - u l) * (u j - u k) =
      (u i - u k) * (u j - u l) := by ring

/-- The two spectra give the first and the negated second four affine labels. -/
def fourSpectralPoints (a b : Fin 4 → ℂ) : Fin 8 → ℂ :=
  ![a 0, a 1, a 2, a 3, -b 0, -b 1, -b 2, -b 3]

/-- The fourteen quadratic derivatives of the matching cubic. -/
def fourMatchingGradient {R : Type*} [CommRing R] (m : Fin 14 → R) : Fin 14 → R :=
  ![-m 0 * m 9 + m 10 * (-m 3 - m 9) + m 11 * (-m 7 - m 9) - m 12 * m 9 +
      m 13 * m 6 - m 9 * (m 0 + m 1 + m 2 + m 3 + m 5 + m 7 + m 9),
    -m 0 * m 9 + m 10 * (m 2 + m 7) + m 12 * m 7 - m 13 * m 5 - m 5 * m 9,
    -m 0 * m 9 + m 1 * m 10 + m 10 * m 11 + m 11 * m 5 + m 12 * (-m 6 - m 9),
    -m 0 * m 10 - m 0 * m 9 - m 10 * m 8 + m 11 * m 5 + m 12 * (m 5 + m 7),
    -m 11 * m 7 + m 8 * m 9,
    -m 0 * m 9 - m 1 * m 13 - m 1 * m 9 + m 11 * (m 2 + m 3) + m 12 * m 3,
    m 0 * m 13 - m 12 * m 2,
    -m 0 * m 11 - m 0 * m 9 + m 1 * m 10 - m 11 * m 4 + m 12 * (m 1 + m 3),
    -m 10 * m 3 + m 4 * m 9,
    -m 0 * m 10 - m 0 * m 11 - m 0 * m 9 -
      m 0 * (m 0 + m 1 + m 2 + m 3 + m 5 + m 7 + m 9) - m 1 * m 5 +
      m 12 * (-m 0 - m 2) + m 4 * m 8,
    -m 0 * m 3 - m 0 * m 9 + m 1 * m 2 + m 1 * m 7 + m 11 * m 2 - m 3 * m 8,
    -m 0 * m 7 - m 0 * m 9 + m 10 * m 2 + m 2 * m 5 + m 3 * m 5 - m 4 * m 7,
    -m 0 * m 9 + m 1 * m 7 - m 2 * m 6 - m 2 * m 9 + m 3 * m 5 + m 3 * m 7,
    m 0 * m 6 - m 1 * m 5]

set_option maxHeartbeats 2500000 in
private theorem fourMatchingGradient_brackets {R : Type*} [CommRing R]
    (d : Fin 8 → Fin 8 → R)
    (hPlucker : ∀ i j k l, d i j * d k l + d i l * d j k = d i k * d j l)
    (i : Fin 14) : fourMatchingGradient (fourBracketCoordinates d) i = 0 := by
  fin_cases i
  · simp [fourMatchingGradient, fourBracketCoordinates] <;>
    linear_combination -d 0 7 * d 1 2 * d 2 5 * d 3 4 * d 4 7 * d 5 6 * hPlucker 0 1 3 6 - d 0 7 * d 1 2 * d 1 3 * d 2 5 * d 3 4 * d 5 6 * hPlucker 0 4 6 7
      - d 0 7 * d 0 7 * d 1 2 * d 3 4 * d 4 6 * d 5 6 * hPlucker 1 2 3 5 - d 0 7 * d 0 7 * d 1 2 * d 2 3 * d 3 4 * d 5 6 * hPlucker 1 4 5 6
      - d 0 7 * d 0 7 * d 1 2 * d 1 2 * d 3 4 * d 5 6 * hPlucker 3 4 5 6 - d 0 1 * d 0 7 * d 1 2 * d 3 4 * d 4 7 * d 5 6 * hPlucker 2 3 5 6
      - d 0 7 * d 1 2 * d 1 3 * d 3 4 * d 5 6 * d 6 7 * hPlucker 0 2 4 5 - d 0 1 * d 0 7 * d 1 2 * d 3 4 * d 3 5 * d 5 6 * hPlucker 2 4 6 7
      - d 0 5 * d 0 7 * d 1 2 * d 3 4 * d 5 6 * d 6 7 * hPlucker 1 2 3 4 - d 0 1 * d 0 7 * d 1 2 * d 2 7 * d 3 4 * d 5 6 * hPlucker 3 4 5 6
      - d 0 7 * d 1 2 * d 3 4 * d 4 5 * d 5 6 * d 6 7 * hPlucker 0 1 2 3 - d 0 1 * d 0 7 * d 1 2 * d 3 4 * d 5 6 * d 6 7 * hPlucker 2 3 4 5
  · simp [fourMatchingGradient, fourBracketCoordinates] <;>
    linear_combination d 0 7 * d 1 2 * d 2 5 * d 3 4 * d 4 5 * d 6 7 * hPlucker 0 1 3 6 + d 0 6 * d 0 7 * d 1 2 * d 3 4 * d 4 5 * d 6 7 * hPlucker 1 2 3 5
      - d 0 7 * d 1 2 * d 2 3 * d 3 4 * d 4 5 * d 6 7 * hPlucker 0 1 5 6 - d 0 7 * d 1 2 * d 1 2 * d 3 4 * d 4 5 * d 6 7 * hPlucker 0 3 5 6
  · simp [fourMatchingGradient, fourBracketCoordinates] <;>
    linear_combination -d 0 7 * d 0 7 * d 1 2 * d 2 3 * d 4 5 * d 5 6 * hPlucker 1 3 4 6 + d 0 7 * d 1 2 * d 2 3 * d 4 5 * d 4 7 * d 5 6 * hPlucker 0 1 3 6
      + d 0 7 * d 1 2 * d 1 3 * d 2 3 * d 4 5 * d 5 6 * hPlucker 0 4 6 7 - d 0 7 * d 1 2 * d 2 3 * d 4 5 * d 5 6 * d 6 7 * hPlucker 0 1 3 4
  · simp [fourMatchingGradient, fourBracketCoordinates] <;>
    linear_combination d 0 7 * d 1 2 * d 1 4 * d 2 3 * d 4 5 * d 6 7 * hPlucker 0 3 5 6 + d 0 6 * d 0 7 * d 1 2 * d 2 3 * d 4 5 * d 6 7 * hPlucker 1 3 4 5
      - d 0 7 * d 1 2 * d 2 3 * d 3 4 * d 4 5 * d 6 7 * hPlucker 0 1 5 6 - d 0 7 * d 1 2 * d 2 3 * d 4 5 * d 4 5 * d 6 7 * hPlucker 0 1 3 6
  · simp [fourMatchingGradient, fourBracketCoordinates] <;>
    ring
  · simp [fourMatchingGradient, fourBracketCoordinates] <;>
    linear_combination d 0 1 * d 0 7 * d 2 3 * d 2 5 * d 3 4 * d 5 6 * hPlucker 1 4 6 7 + d 0 1 * d 0 7 * d 1 7 * d 2 3 * d 3 4 * d 5 6 * hPlucker 2 4 5 6
      - d 0 1 * d 0 7 * d 2 3 * d 3 4 * d 4 5 * d 5 6 * hPlucker 1 2 6 7 - d 0 1 * d 0 7 * d 2 3 * d 3 4 * d 5 6 * d 5 6 * hPlucker 1 2 4 7
  · simp [fourMatchingGradient, fourBracketCoordinates] <;>
    ring
  · simp [fourMatchingGradient, fourBracketCoordinates] <;>
    linear_combination d 0 1 * d 0 7 * d 2 3 * d 3 6 * d 4 5 * d 5 6 * hPlucker 1 2 4 7 + d 0 1 * d 0 7 * d 1 7 * d 2 3 * d 4 5 * d 5 6 * hPlucker 2 3 4 6
      - d 0 1 * d 0 7 * d 2 3 * d 3 4 * d 4 5 * d 5 6 * hPlucker 1 2 6 7 - d 0 1 * d 0 7 * d 2 3 * d 2 3 * d 4 5 * d 5 6 * hPlucker 1 4 6 7
  · simp [fourMatchingGradient, fourBracketCoordinates] <;>
    ring
  · simp [fourMatchingGradient, fourBracketCoordinates] <;>
    linear_combination -d 0 1 * d 1 4 * d 2 3 * d 3 6 * d 4 5 * d 6 7 * hPlucker 0 2 5 7 - d 0 1 * d 0 7 * d 2 3 * d 3 6 * d 4 5 * d 6 7 * hPlucker 1 2 4 5
      - d 0 1 * d 0 7 * d 2 3 * d 2 4 * d 4 5 * d 6 7 * hPlucker 1 3 5 6 - d 0 1 * d 0 7 * d 1 6 * d 2 3 * d 4 5 * d 6 7 * hPlucker 2 3 4 5
      - d 0 1 * d 0 7 * d 2 3 * d 4 5 * d 5 6 * d 6 7 * hPlucker 1 2 3 4 - d 0 1 * d 2 3 * d 3 6 * d 4 5 * d 5 7 * d 6 7 * hPlucker 0 1 2 4
      - d 0 1 * d 1 2 * d 2 3 * d 4 5 * d 5 7 * d 6 7 * hPlucker 0 3 4 6 - d 0 1 * d 1 2 * d 2 3 * d 3 4 * d 4 5 * d 6 7 * hPlucker 0 5 6 7
      - d 0 1 * d 0 3 * d 1 2 * d 2 3 * d 4 5 * d 6 7 * hPlucker 4 5 6 7 - d 0 1 * d 0 1 * d 2 3 * d 4 5 * d 5 7 * d 6 7 * hPlucker 2 3 4 6
      - d 0 1 * d 0 1 * d 2 3 * d 3 4 * d 4 5 * d 6 7 * hPlucker 2 5 6 7 - d 0 1 * d 0 1 * d 2 3 * d 2 3 * d 4 5 * d 6 7 * hPlucker 4 5 6 7
  · simp [fourMatchingGradient, fourBracketCoordinates] <;>
    linear_combination d 0 1 * d 1 4 * d 2 3 * d 3 4 * d 5 6 * d 6 7 * hPlucker 0 2 5 7 - d 0 1 * d 1 2 * d 2 3 * d 3 4 * d 5 6 * d 6 7 * hPlucker 0 4 5 7
      + d 0 1 * d 2 3 * d 3 4 * d 5 6 * d 5 7 * d 6 7 * hPlucker 0 1 2 4 - d 0 1 * d 0 1 * d 2 3 * d 3 4 * d 5 6 * d 6 7 * hPlucker 2 4 5 7
  · simp [fourMatchingGradient, fourBracketCoordinates] <;>
    linear_combination d 0 1 * d 1 2 * d 3 4 * d 3 6 * d 4 5 * d 6 7 * hPlucker 0 2 5 7 - d 0 1 * d 1 2 * d 3 4 * d 4 5 * d 5 6 * d 6 7 * hPlucker 0 2 3 7
      + d 0 1 * d 0 2 * d 1 2 * d 3 4 * d 4 5 * d 6 7 * hPlucker 3 5 6 7 - d 0 1 * d 1 2 * d 3 4 * d 4 5 * d 6 7 * d 6 7 * hPlucker 0 2 3 5
  · simp [fourMatchingGradient, fourBracketCoordinates] <;>
    linear_combination -d 0 1 * d 1 2 * d 3 4 * d 3 4 * d 5 6 * d 6 7 * hPlucker 0 2 5 7 + d 0 1 * d 1 2 * d 3 4 * d 4 7 * d 5 6 * d 6 7 * hPlucker 0 2 3 5
      - d 0 1 * d 1 2 * d 3 4 * d 4 5 * d 5 6 * d 6 7 * hPlucker 0 2 3 7 + d 0 1 * d 0 2 * d 1 2 * d 3 4 * d 5 6 * d 6 7 * hPlucker 3 4 5 7
  · simp [fourMatchingGradient, fourBracketCoordinates] <;>
    ring

theorem fourMatchingGradient_noncrossing {R : Type*} [CommRing R] (u : Fin 8 → R)
    (i : Fin 14) : fourMatchingGradient (fourNoncrossingCoordinates u) i = 0 :=
  fourMatchingGradient_brackets (fun j k => u j - u k) (difference_plucker u) i

theorem fourMatchingGradient_scale {R : Type*} [CommRing R]
    (m : Fin 14 → R) (k : R) (i : Fin 14) :
    fourMatchingGradient (fun j => k * m j) i = k ^ 2 * fourMatchingGradient m i := by
  fin_cases i <;> simp [fourMatchingGradient] <;> ring

/-- The matching gradient commutes with ring evaluation. -/
theorem fourMatchingGradient_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (m : Fin 14 → R) (i : Fin 14) :
    f (fourMatchingGradient m i) = fourMatchingGradient (fun j => f (m j)) i := by
  fin_cases i <;> simp [fourMatchingGradient]

private theorem fourMatchingCubic_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (m : Fin 14 → R) :
    f (fourMatchingCubic m) = fourMatchingCubic (fun j => f (m j)) := by
  simp only [fourMatchingCubic, map_add, map_sub, map_mul, map_neg]

private theorem fourMatchingCubic_scale {R : Type*} [CommRing R]
    (m : Fin 14 → R) (k : R) :
    fourMatchingCubic (fun j => k * m j) = k ^ 3 * fourMatchingCubic m := by
  unfold fourMatchingCubic
  ring

private theorem fourMatchingCubic_euler {R : Type*} [CommRing R] (m : Fin 14 → R) :
    ∑ i, fourMatchingGradient m i * m i = 3 * fourMatchingCubic m := by
  simp [Fin.sum_univ_succ, fourMatchingGradient, fourMatchingCubic]
  <;> ring

private theorem fourMatchingCubic_add {R : Type*} [CommRing R] (m n : Fin 14 → R) :
    fourMatchingCubic (fun i => m i + n i) =
      fourMatchingCubic m + fourMatchingCubic n +
        (∑ i, fourMatchingGradient m i * n i) +
        (∑ i, fourMatchingGradient n i * m i) := by
  simp [Fin.sum_univ_succ, fourMatchingGradient, fourMatchingCubic]
  <;> ring

private theorem fourMatchingCubic_zero_of_gradient (m : Fin 14 → ℂ)
    (hm : ∀ i, fourMatchingGradient m i = 0) : fourMatchingCubic m = 0 := by
  have he := fourMatchingCubic_euler m
  simp only [hm, zero_mul, Finset.sum_const_zero] at he
  exact (mul_eq_zero.mp he.symm).resolve_left (by norm_num)

/-- A complex point with zero matching gradient projects onto the real cubic. -/
theorem fourMatchingCubic_real_part_zero (m : Fin 14 → ℂ)
    (hm : ∀ i, fourMatchingGradient m i = 0) :
    fourMatchingCubic (fun i => (m i).re) = 0 := by
  let n (i : Fin 14) := conj (m i)
  have hn (i : Fin 14) : fourMatchingGradient n i = 0 := by
    rw [show fourMatchingGradient n i = conj (fourMatchingGradient m i) from
      (fourMatchingGradient_map (starRingEnd ℂ) m i).symm, hm, map_zero]
  have hadd := fourMatchingCubic_add m n
  simp only [fourMatchingCubic_zero_of_gradient m hm, fourMatchingCubic_zero_of_gradient n hn,
    hm, hn, zero_mul, Finset.sum_const_zero, add_zero] at hadd
  have heq : (fun i => m i + n i) = fun i => (2 : ℂ) * ((m i).re : ℂ) := by
    funext i
    simpa only [n, Complex.ofReal_mul, Complex.ofReal_ofNat] using Complex.add_conj (m i)
  rw [heq, fourMatchingCubic_scale] at hadd
  have hcast := fourMatchingCubic_map Complex.ofRealHom (fun i => (m i).re)
  change (2 : ℂ) ^ 3 * fourMatchingCubic (fun i => Complex.ofRealHom (m i).re) = 0 at hadd
  rw [← hcast] at hadd
  apply Complex.ofReal_injective
  exact (mul_eq_zero.mp hadd).resolve_left (by norm_num)

/-- The real coordinate vector of scaled matching data from actual spectra
obeys the cubic equation used in the order-four contact certificates. -/
theorem fourMatchingCubic_of_spectral_real_part (a b : Fin 4 → ℂ) (η : ℂ) :
    fourMatchingCubic (fun i => (η * fourNoncrossingCoordinates (fourSpectralPoints a b) i).re) = 0 := by
  apply fourMatchingCubic_real_part_zero
  intro i
  rw [fourMatchingGradient_scale, fourMatchingGradient_noncrossing, mul_zero]


/-- Evaluate all twenty-four bipartite matchings in the noncrossing basis. -/
def fourMatchingEvaluation {R : Type*} [CommRing R] (m : Fin 14 → R) : Fin 24 → R :=
  ![2 * m 0 + m 1 + m 2 + m 3 + m 4 + m 5 + m 6 + m 7 + m 8 + 2 * m 9 + m 10 + m 11 + m 12 + m 13,
    m 0 + m 1 + m 2 + m 3 + m 4 + m 5 + m 6 + m 7 + 2 * m 9 + m 10 + m 11 + m 12 + m 13,
    2 * m 0 + m 1 + m 2 + m 3 + m 4 + m 5 + m 7 + m 8 + m 9 + m 10 + m 11 + m 12 + m 13,
    m 0 + m 2 + m 3 + m 4 + m 5 + m 7 + m 9 + m 10 + m 12 + m 13,
    m 0 + m 1 + m 2 + m 3 + m 4 + m 9 + m 10 + m 11 + m 12 + m 13,
    m 0 + m 2 + m 3 + m 4 + m 9 + m 10 + m 12 + m 13,
    m 0 + m 1 + m 2 + m 3 + m 5 + m 6 + m 7 + m 8 + 2 * m 9 + m 10 + m 11 + m 12 + m 13,
    m 0 + m 1 + m 2 + m 3 + m 5 + m 6 + m 7 + 2 * m 9 + m 10 + m 11 + m 12 + m 13,
    m 0 + m 1 + m 2 + m 3 + m 7 + m 8 + m 9 + m 11 + m 12 + m 13,
    m 2 + m 3 + m 7 + m 9 + m 13,
    m 0 + m 1 + m 2 + m 3 + m 9 + m 11 + m 12 + m 13,
    m 2 + m 3 + m 9 + m 13,
    m 0 + m 2 + m 5 + m 7 + m 8 + m 9 + m 10 + m 11 + m 12 + m 13,
    m 0 + m 2 + m 5 + m 7 + m 9 + m 10 + m 12 + m 13,
    m 0 + m 2 + m 7 + m 8 + m 9 + m 11 + m 12 + m 13,
    m 2 + m 7 + m 9 + m 13,
    m 0 + m 2 + m 12 + m 13,
    m 2 + m 13,
    m 9 + m 10 + m 11 + m 12 + m 13,
    m 9 + m 10 + m 12 + m 13,
    m 9 + m 11 + m 12 + m 13,
    m 9 + m 13,
    m 12 + m 13,
    m 13]

/-- Recover the noncrossing coordinates from the unimodular minor of the
matching evaluation given in Appendix A of Zheng's paper. -/
def fourMatchingCoordinatesOfValues {R : Type*} [CommRing R] (v : Fin 24 → R) : Fin 14 → R :=
  ![v 0 - v 1 - v 6 + v 7,
    -v 0 + v 1 + v 2 - v 3 + v 6 - v 7 - v 12 + v 13,
    -v 2 + v 4 + v 12 - v 18,
    -v 1 + v 3 + v 7 - v 13,
    v 1 - v 7,
    -v 0 + v 1 + v 2 - v 4 + v 6 - v 7 - v 8 + v 10,
    v 7 - v 10 - v 13 + v 16,
    -v 6 + v 7 + v 8 - v 10,
    v 6 - v 7,
    v 0 - v 2 - v 7 + v 10 + v 13 - v 16,
    -v 1 + v 4 + v 7 - v 10,
    -v 6 + v 7 + v 12 - v 13,
    -v 2 + v 3 + v 8 - v 9,
    -v 0 + v 1 + 2 * v 2 - v 3 - v 4 + v 6 - v 7 - v 8 + v 9 - v 12 + v 16 + v 18]

set_option maxHeartbeats 2000000 in
theorem fourMatchingEvaluation_leftInverse {R : Type*} [CommRing R] :
    Function.LeftInverse (fourMatchingCoordinatesOfValues : (Fin 24 → R) → Fin 14 → R)
      fourMatchingEvaluation := by
  intro m
  funext i
  fin_cases i <;>
    simp [fourMatchingCoordinatesOfValues] <;>
    dsimp only [fourMatchingEvaluation, Matrix.cons_val] <;> ring_nf

theorem fourMatchingEvaluation_injective {R : Type*} [CommRing R] :
    Function.Injective (fourMatchingEvaluation : (Fin 14 → R) → Fin 24 → R) :=
  fourMatchingEvaluation_leftInverse.injective

set_option maxHeartbeats 3500000 in
private theorem fourMatchingEvaluation_brackets {R : Type*} [CommRing R]
    (d : Fin 8 → Fin 8 → R)
    (hPlucker : ∀ i j k l, d i j * d k l + d i l * d j k = d i k * d j l)
    (i : Fin 24) :
    let j (k : Fin 4) := (![4, 5, 6, 7] : Fin 4 → Fin 8) (fourPerm i k)
    fourMatchingEvaluation (fourBracketCoordinates d) i =
      d 0 (j 0) * d 1 (j 1) * d 2 (j 2) * d 3 (j 3) := by
  fin_cases i
  · simp [fourMatchingEvaluation, fourBracketCoordinates, fourPerm,
      Equiv.Perm.mul_apply, Equiv.swap_apply_def] <;>
    linear_combination d 2 6 * d 3 7 * hPlucker 0 1 4 5 + d 1 4 * d 3 7 * hPlucker 0 2 5 6
      + d 1 4 * d 2 5 * hPlucker 0 3 6 7 + d 0 7 * d 3 6 * hPlucker 1 2 4 5
      + d 0 7 * d 2 4 * hPlucker 1 3 5 6 + d 0 7 * d 1 6 * hPlucker 2 3 4 5
      + d 0 7 * d 5 6 * hPlucker 1 2 3 4 + d 2 5 * d 6 7 * hPlucker 0 1 3 4
      + d 1 3 * d 6 7 * hPlucker 0 2 4 5 + d 3 7 * d 5 6 * hPlucker 0 1 2 4
      + d 0 5 * d 6 7 * hPlucker 1 2 3 4 + d 1 2 * d 5 6 * hPlucker 0 3 4 7
      + d 0 1 * d 4 5 * hPlucker 2 3 6 7 + d 0 1 * d 5 6 * hPlucker 2 3 4 7
      + d 4 5 * d 6 7 * hPlucker 0 1 2 3
  · simp [fourMatchingEvaluation, fourBracketCoordinates, fourPerm,
      Equiv.Perm.mul_apply, Equiv.swap_apply_def] <;>
    linear_combination d 2 7 * d 3 6 * hPlucker 0 1 4 5 + d 1 4 * d 3 6 * hPlucker 0 2 5 7
      + d 0 7 * d 3 6 * hPlucker 1 2 4 5 + d 0 7 * d 2 4 * hPlucker 1 3 5 6
      + d 0 7 * d 1 6 * hPlucker 2 3 4 5 + d 0 7 * d 5 6 * hPlucker 1 2 3 4
      + d 3 6 * d 5 7 * hPlucker 0 1 2 4 + d 1 2 * d 5 7 * hPlucker 0 3 4 6
      + d 1 2 * d 3 4 * hPlucker 0 5 6 7 + d 0 3 * d 1 2 * hPlucker 4 5 6 7
      + d 0 1 * d 5 7 * hPlucker 2 3 4 6 + d 0 1 * d 3 4 * hPlucker 2 5 6 7
      + d 0 1 * d 2 3 * hPlucker 4 5 6 7
  · simp [fourMatchingEvaluation, fourBracketCoordinates, fourPerm,
      Equiv.Perm.mul_apply, Equiv.swap_apply_def] <;>
    linear_combination d 2 5 * d 3 7 * hPlucker 0 1 4 6 + d 1 4 * d 2 5 * hPlucker 0 3 6 7
      + d 0 7 * d 3 6 * hPlucker 1 2 4 5 + d 0 7 * d 2 4 * hPlucker 1 3 5 6
      + d 0 7 * d 1 6 * hPlucker 2 3 4 5 + d 0 7 * d 5 6 * hPlucker 1 2 3 4
      + d 2 5 * d 6 7 * hPlucker 0 1 3 4 + d 1 3 * d 6 7 * hPlucker 0 2 4 5
      + d 0 1 * d 4 6 * hPlucker 2 3 5 7 + d 0 5 * d 6 7 * hPlucker 1 2 3 4
      + d 0 1 * d 2 7 * hPlucker 3 4 5 6 + d 4 5 * d 6 7 * hPlucker 0 1 2 3
      + d 0 1 * d 2 3 * hPlucker 4 5 6 7
  · simp [fourMatchingEvaluation, fourBracketCoordinates, fourPerm,
      Equiv.Perm.mul_apply, Equiv.swap_apply_def] <;>
    linear_combination d 2 7 * d 3 5 * hPlucker 0 1 4 6 + d 1 4 * d 3 5 * hPlucker 0 2 6 7
      + d 0 7 * d 3 5 * hPlucker 1 2 4 6 + d 0 7 * d 1 6 * hPlucker 2 3 4 5
      + d 0 7 * d 1 2 * hPlucker 3 4 5 6 + d 0 1 * d 2 7 * hPlucker 3 4 5 6
      + d 3 5 * d 6 7 * hPlucker 0 1 2 4 + d 1 2 * d 6 7 * hPlucker 0 3 4 5
      + d 0 1 * d 6 7 * hPlucker 2 3 4 5
  · simp [fourMatchingEvaluation, fourBracketCoordinates, fourPerm,
      Equiv.Perm.mul_apply, Equiv.swap_apply_def] <;>
    linear_combination d 2 5 * d 3 6 * hPlucker 0 1 4 7 + d 0 7 * d 3 6 * hPlucker 1 2 4 5
      + d 0 7 * d 2 4 * hPlucker 1 3 5 6 + d 0 7 * d 1 6 * hPlucker 2 3 4 5
      + d 0 7 * d 5 6 * hPlucker 1 2 3 4 + d 0 1 * d 4 7 * hPlucker 2 3 5 6
      + d 0 1 * d 3 5 * hPlucker 2 4 6 7 + d 0 1 * d 2 7 * hPlucker 3 4 5 6
      + d 0 1 * d 6 7 * hPlucker 2 3 4 5
  · simp [fourMatchingEvaluation, fourBracketCoordinates, fourPerm,
      Equiv.Perm.mul_apply, Equiv.swap_apply_def] <;>
    linear_combination d 2 6 * d 3 5 * hPlucker 0 1 4 7 + d 0 7 * d 3 5 * hPlucker 1 2 4 6
      + d 0 7 * d 1 6 * hPlucker 2 3 4 5 + d 0 7 * d 1 2 * hPlucker 3 4 5 6
      + d 0 1 * d 3 5 * hPlucker 2 4 6 7 + d 0 1 * d 2 7 * hPlucker 3 4 5 6
      + d 0 1 * d 6 7 * hPlucker 2 3 4 5
  · simp [fourMatchingEvaluation, fourBracketCoordinates, fourPerm,
      Equiv.Perm.mul_apply, Equiv.swap_apply_def] <;>
    linear_combination d 1 4 * d 3 7 * hPlucker 0 2 5 6 + d 1 4 * d 2 5 * hPlucker 0 3 6 7
      + d 0 7 * d 3 6 * hPlucker 1 2 4 5 + d 0 7 * d 2 4 * hPlucker 1 3 5 6
      + d 0 7 * d 1 6 * hPlucker 2 3 4 5 + d 0 7 * d 5 6 * hPlucker 1 2 3 4
      + d 2 5 * d 6 7 * hPlucker 0 1 3 4 + d 1 3 * d 6 7 * hPlucker 0 2 4 5
      + d 3 7 * d 5 6 * hPlucker 0 1 2 4 + d 0 5 * d 6 7 * hPlucker 1 2 3 4
      + d 1 2 * d 5 6 * hPlucker 0 3 4 7 + d 0 1 * d 5 6 * hPlucker 2 3 4 7
      + d 4 5 * d 6 7 * hPlucker 0 1 2 3
  · simp [fourMatchingEvaluation, fourBracketCoordinates, fourPerm,
      Equiv.Perm.mul_apply, Equiv.swap_apply_def] <;>
    linear_combination d 1 4 * d 3 6 * hPlucker 0 2 5 7 + d 0 7 * d 3 6 * hPlucker 1 2 4 5
      + d 0 7 * d 2 4 * hPlucker 1 3 5 6 + d 0 7 * d 1 6 * hPlucker 2 3 4 5
      + d 0 7 * d 5 6 * hPlucker 1 2 3 4 + d 3 6 * d 5 7 * hPlucker 0 1 2 4
      + d 1 2 * d 5 7 * hPlucker 0 3 4 6 + d 1 2 * d 3 4 * hPlucker 0 5 6 7
      + d 0 3 * d 1 2 * hPlucker 4 5 6 7 + d 0 1 * d 5 7 * hPlucker 2 3 4 6
      + d 0 1 * d 3 4 * hPlucker 2 5 6 7 + d 0 1 * d 2 3 * hPlucker 4 5 6 7
  · simp [fourMatchingEvaluation, fourBracketCoordinates, fourPerm,
      Equiv.Perm.mul_apply, Equiv.swap_apply_def] <;>
    linear_combination d 2 4 * d 3 7 * hPlucker 0 1 5 6 + d 1 5 * d 2 4 * hPlucker 0 3 6 7
      + d 0 7 * d 2 4 * hPlucker 1 3 5 6 + d 0 7 * d 1 6 * hPlucker 2 3 4 5
      + d 0 7 * d 5 6 * hPlucker 1 2 3 4 + d 2 4 * d 6 7 * hPlucker 0 1 3 5
      + d 0 5 * d 6 7 * hPlucker 1 2 3 4 + d 0 1 * d 5 6 * hPlucker 2 3 4 7
      + d 0 1 * d 6 7 * hPlucker 2 3 4 5
  · simp [fourMatchingEvaluation, fourBracketCoordinates, fourPerm,
      Equiv.Perm.mul_apply, Equiv.swap_apply_def] <;>
    linear_combination d 2 7 * d 3 4 * hPlucker 0 1 5 6 + d 1 5 * d 3 4 * hPlucker 0 2 6 7
      + d 0 7 * d 3 4 * hPlucker 1 2 5 6 + d 3 4 * d 6 7 * hPlucker 0 1 2 5
  · simp [fourMatchingEvaluation, fourBracketCoordinates, fourPerm,
      Equiv.Perm.mul_apply, Equiv.swap_apply_def] <;>
    linear_combination d 2 4 * d 3 6 * hPlucker 0 1 5 7 + d 0 7 * d 2 4 * hPlucker 1 3 5 6
      + d 0 7 * d 1 6 * hPlucker 2 3 4 5 + d 0 7 * d 5 6 * hPlucker 1 2 3 4
      + d 0 1 * d 5 7 * hPlucker 2 3 4 6 + d 0 1 * d 3 4 * hPlucker 2 5 6 7
      + d 0 1 * d 2 3 * hPlucker 4 5 6 7
  · simp [fourMatchingEvaluation, fourBracketCoordinates, fourPerm,
      Equiv.Perm.mul_apply, Equiv.swap_apply_def] <;>
    linear_combination d 2 6 * d 3 4 * hPlucker 0 1 5 7 + d 0 7 * d 3 4 * hPlucker 1 2 5 6
      + d 0 1 * d 3 4 * hPlucker 2 5 6 7
  · simp [fourMatchingEvaluation, fourBracketCoordinates, fourPerm,
      Equiv.Perm.mul_apply, Equiv.swap_apply_def] <;>
    linear_combination d 1 4 * d 2 5 * hPlucker 0 3 6 7 + d 0 7 * d 3 6 * hPlucker 1 2 4 5
      + d 0 7 * d 2 4 * hPlucker 1 3 5 6 + d 0 7 * d 1 6 * hPlucker 2 3 4 5
      + d 0 7 * d 5 6 * hPlucker 1 2 3 4 + d 2 5 * d 6 7 * hPlucker 0 1 3 4
      + d 1 3 * d 6 7 * hPlucker 0 2 4 5 + d 0 5 * d 6 7 * hPlucker 1 2 3 4
      + d 4 5 * d 6 7 * hPlucker 0 1 2 3
  · simp [fourMatchingEvaluation, fourBracketCoordinates, fourPerm,
      Equiv.Perm.mul_apply, Equiv.swap_apply_def] <;>
    linear_combination d 1 4 * d 3 5 * hPlucker 0 2 6 7 + d 0 7 * d 3 5 * hPlucker 1 2 4 6
      + d 0 7 * d 1 6 * hPlucker 2 3 4 5 + d 0 7 * d 1 2 * hPlucker 3 4 5 6
      + d 3 5 * d 6 7 * hPlucker 0 1 2 4 + d 1 2 * d 6 7 * hPlucker 0 3 4 5
      + d 0 1 * d 6 7 * hPlucker 2 3 4 5
  · simp [fourMatchingEvaluation, fourBracketCoordinates, fourPerm,
      Equiv.Perm.mul_apply, Equiv.swap_apply_def] <;>
    linear_combination d 1 5 * d 2 4 * hPlucker 0 3 6 7 + d 0 7 * d 2 4 * hPlucker 1 3 5 6
      + d 0 7 * d 1 6 * hPlucker 2 3 4 5 + d 0 7 * d 5 6 * hPlucker 1 2 3 4
      + d 2 4 * d 6 7 * hPlucker 0 1 3 5 + d 0 5 * d 6 7 * hPlucker 1 2 3 4
      + d 0 1 * d 6 7 * hPlucker 2 3 4 5
  · simp [fourMatchingEvaluation, fourBracketCoordinates, fourPerm,
      Equiv.Perm.mul_apply, Equiv.swap_apply_def] <;>
    linear_combination d 1 5 * d 3 4 * hPlucker 0 2 6 7 + d 0 7 * d 3 4 * hPlucker 1 2 5 6
      + d 3 4 * d 6 7 * hPlucker 0 1 2 5
  · simp [fourMatchingEvaluation, fourBracketCoordinates, fourPerm,
      Equiv.Perm.mul_apply, Equiv.swap_apply_def] <;>
    linear_combination d 2 4 * d 3 5 * hPlucker 0 1 6 7 + d 0 7 * d 1 6 * hPlucker 2 3 4 5
      + d 0 1 * d 6 7 * hPlucker 2 3 4 5
  · simp [fourMatchingEvaluation, fourBracketCoordinates, fourPerm,
      Equiv.Perm.mul_apply, Equiv.swap_apply_def] <;>
    linear_combination d 2 5 * d 3 4 * hPlucker 0 1 6 7
  · simp [fourMatchingEvaluation, fourBracketCoordinates, fourPerm,
      Equiv.Perm.mul_apply, Equiv.swap_apply_def] <;>
    linear_combination d 0 7 * d 3 6 * hPlucker 1 2 4 5 + d 0 7 * d 2 4 * hPlucker 1 3 5 6
      + d 0 7 * d 1 6 * hPlucker 2 3 4 5 + d 0 7 * d 5 6 * hPlucker 1 2 3 4
  · simp [fourMatchingEvaluation, fourBracketCoordinates, fourPerm,
      Equiv.Perm.mul_apply, Equiv.swap_apply_def] <;>
    linear_combination d 0 7 * d 3 5 * hPlucker 1 2 4 6 + d 0 7 * d 1 6 * hPlucker 2 3 4 5
      + d 0 7 * d 1 2 * hPlucker 3 4 5 6
  · simp [fourMatchingEvaluation, fourBracketCoordinates, fourPerm,
      Equiv.Perm.mul_apply, Equiv.swap_apply_def] <;>
    linear_combination d 0 7 * d 2 4 * hPlucker 1 3 5 6 + d 0 7 * d 1 6 * hPlucker 2 3 4 5
      + d 0 7 * d 5 6 * hPlucker 1 2 3 4
  · simp [fourMatchingEvaluation, fourBracketCoordinates, fourPerm,
      Equiv.Perm.mul_apply, Equiv.swap_apply_def] <;>
    linear_combination d 0 7 * d 3 4 * hPlucker 1 2 5 6
  · simp [fourMatchingEvaluation, fourBracketCoordinates, fourPerm,
      Equiv.Perm.mul_apply, Equiv.swap_apply_def] <;>
    linear_combination d 0 7 * d 1 6 * hPlucker 2 3 4 5
  · simp [fourMatchingEvaluation, fourBracketCoordinates, fourPerm,
      Equiv.Perm.mul_apply, Equiv.swap_apply_def] <;>
    ring

/-- The basis evaluation gives the actual matching products. The inverse
permutation converts the row convention in the table to Lean's column convention. -/
theorem fourMatchingEvaluation_spectral (a b : Fin 4 → ℂ) (i : Fin 24) :
    fourMatchingEvaluation (fourNoncrossingCoordinates (fourSpectralPoints a b)) i =
      matchingProduct a b (fourPerm i).symm := by
  rw [matchingProduct_inverse, Fin.prod_univ_four]
  let u := fourSpectralPoints a b
  have hright (j : Fin 4) : u ((![4, 5, 6, 7] : Fin 4 → Fin 8) j) = -b j := by
    fin_cases j <;> rfl
  have h := fourMatchingEvaluation_brackets (fun j k => u j - u k) (difference_plucker u) i
  change fourMatchingEvaluation (fourNoncrossingCoordinates u) i =
    (u 0 - u ((![4, 5, 6, 7] : Fin 4 → Fin 8) (fourPerm i 0))) *
      (u 1 - u ((![4, 5, 6, 7] : Fin 4 → Fin 8) (fourPerm i 1))) *
      (u 2 - u ((![4, 5, 6, 7] : Fin 4 → Fin 8) (fourPerm i 2))) *
      (u 3 - u ((![4, 5, 6, 7] : Fin 4 → Fin 8) (fourPerm i 3))) at h
  simp only [hright, sub_neg_eq_add] at h
  simpa only [u, fourSpectralPoints, Matrix.cons_val, mul_assoc] using h

set_option maxHeartbeats 2000000 in
theorem fourMatchingEvaluation_spectral_real_part (a b : Fin 4 → ℂ) (η : ℂ) (i : Fin 24) :
    fourMatchingEvaluation (fun j => (η * fourNoncrossingCoordinates (fourSpectralPoints a b) j).re) i =
      (η * matchingProduct a b (fourPerm i).symm).re := by
  rw [← fourMatchingEvaluation_spectral]
  generalize fourNoncrossingCoordinates (fourSpectralPoints a b) = m
  fin_cases i <;> simp [fourMatchingEvaluation] <;> ring

/-- Prescribing the real values of all twenty-four matching products
forces the corresponding noncrossing coordinate lift to lie on the cubic. -/
theorem fourMatchingCubic_zero_of_evaluation_eq_spectral
    (a b : Fin 4 → ℂ) (η : ℂ) (m : Fin 14 → ℝ)
    (hm : ∀ i, fourMatchingEvaluation m i = (η * matchingProduct a b (fourPerm i).symm).re) :
    fourMatchingCubic m = 0 := by
  have heq : m = fun j => (η * fourNoncrossingCoordinates (fourSpectralPoints a b) j).re := by
    apply fourMatchingEvaluation_injective
    funext i
    rw [hm, fourMatchingEvaluation_spectral_real_part]
  rw [heq]
  exact fourMatchingCubic_of_spectral_real_part a b η

/-- For the paper's `T21` lift, agreement with actual zero-height matching
values rules out its sole mixed coefficient. -/
theorem t21_mixed_coefficient_zero_of_spectral
    (α β : Fin 4 → ℂ) (η : ℂ) {q a b c e f d h : ℝ}
    (hq : 0 ≤ q) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (he : 0 ≤ e) (hf : 0 ≤ f) (hd : 0 ≤ d) (hh : 0 ≤ h)
    (hmatch : ∀ i,
      fourMatchingEvaluation (t21CanonicalLift q a b c e f d h) i =
        (η * matchingProduct α β (fourPerm i).symm).re) :
    d = 0 :=
  t21_mixed_coefficient_zero hq ha hb hc he hf hd hh
    (fourMatchingCubic_zero_of_evaluation_eq_spectral α β η _ hmatch)

/-- The paper's `T34` radial division is valid on the positive mixed branch
of a lifted vector that matches the real spectral evaluations. -/
theorem t34_radialQ_ne_zero_of_spectral
    (α β : Fin 4 → ℂ) (η : ℂ) {p r a b c q d s h : ℝ}
    (hp : 0 ≤ p) (hr : 0 ≤ r) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hq : 0 ≤ q) (hd : 0 < d) (hs : 0 ≤ s)
    (hmatch : ∀ i,
      fourMatchingEvaluation (t34HeightLift p r a b c q d s h) i =
        (η * matchingProduct α β (fourPerm i).symm).re) :
    t34RadialQ a b c d r s ≠ 0 :=
  t34_radialQ_ne_zero_of_cubic hp hr hb hc hq hd hs
    (fourMatchingCubic_zero_of_evaluation_eq_spectral α β η _ hmatch)

end

end MOC
