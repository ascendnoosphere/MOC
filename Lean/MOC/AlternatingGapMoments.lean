import MOC.FourParityCorrection
import MOC.GeneralizedSpectralCircles
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Data.Matrix.Rank

/-!
# The alternating second moment of projected matching gaps

The separable factorization below is a direct argument. For the general
rank inequality for Hadamard products, see G. P. H. Styan,
*Hadamard products and multivariate statistical analysis*,
DOI: 10.1016/0024-3795(73)90023-2.
-/

open Matrix BigOperators

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem det_mul_eq_zero_of_narrow {K κ : Type*} [Field K] [Fintype κ]
    (L : Matrix ι κ K) (R : Matrix κ ι K) (h : Fintype.card κ < Fintype.card ι) :
    (L * R).det = 0 := by
  by_contra hn
  have hu : IsUnit (L * R) := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hn)
  have hr := (Matrix.rank_mul_le_left L R).trans (Matrix.rank_le_card_width L)
  rw [Matrix.rank_of_isUnit _ hu] at hr
  omega

/-- A signed mixed power of two matching profiles vanishes below the
binomial rank budget. The two spectra pairs need not be conjugate. -/
theorem alternating_mixed_matching_moment_eq_zero (a b c d : ι → ℂ) (r s : ℕ)
    (h : (r+1)*(s+1) < Fintype.card ι) :
    (∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℂ) *
      ((matchingProduct a b σ)^r * (matchingProduct c d σ)^s)) = 0 := by
  let κ := Fin (r+1) × Fin (s+1)
  let L : Matrix ι κ ℂ := Matrix.of fun i k =>
    a i ^ (k.1 : ℕ) * (r.choose k.1 : ℂ) * (c i ^ (k.2 : ℕ) * (s.choose k.2 : ℂ))
  let R : Matrix κ ι ℂ := Matrix.of fun k j => b j ^ (r-k.1) * d j ^ (s-k.2)
  have he (i j : ι) : (L * R) i j = (a i + b j)^r * (c i + d j)^s := by
    simp only [L, R, Matrix.mul_apply, Matrix.of_apply]
    rw [Fintype.sum_prod_type]
    rw [add_pow, add_pow, ← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range,
      Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    ring
  have hd := det_mul_eq_zero_of_narrow L R (by simpa [κ] using h)
  simpa only [Matrix.det_apply', he, Finset.prod_mul_distrib, Finset.prod_pow,
    matchingProduct] using hd

private theorem sum_parityReal_zero (h : 1 < Fintype.card ι) :
    (∑ σ : Equiv.Perm ι, parityReal σ) = 0 := by
  let L : Matrix ι (Fin 1) ℝ := Matrix.of fun _ _ => 1
  let R : Matrix (Fin 1) ι ℝ := Matrix.of fun _ _ => 1
  have hdet := det_mul_eq_zero_of_narrow L R (by simpa using h)
  rw [Matrix.det_apply'] at hdet
  simpa [L, R, Matrix.mul_apply, parityReal] using hdet

private theorem alternating_linear_zero (a b : ι → ℂ) (η : ℂ) (h : 2 < Fintype.card ι) :
    (∑ σ : Equiv.Perm ι, parityReal σ * (η * matchingProduct a b σ).re) = 0 := by
  let L : Matrix ι (Fin 2) ℂ := Matrix.of fun i k => ![a i, 1] k
  let R : Matrix (Fin 2) ι ℂ := Matrix.of fun k j => ![1, b j] k
  have he (i j : ι) : (L * R) i j = a i + b j := by
    simp [L, R, Matrix.mul_apply, Fin.sum_univ_two]
  have hd := det_mul_eq_zero_of_narrow L R (by simpa using h)
  rw [Matrix.det_apply'] at hd
  simp only [he] at hd
  change (∑ σ : Equiv.Perm ι, (((Equiv.Perm.sign σ : ℤ) : ℂ) * matchingProduct a b σ)) = 0 at hd
  calc
    _ = (η * ∑ σ : Equiv.Perm ι, (((Equiv.Perm.sign σ : ℤ) : ℂ) *
      matchingProduct a b σ)).re := by
      rw [Finset.mul_sum, Complex.re_sum]
      apply Finset.sum_congr rfl
      intro σ _
      rw [mul_left_comm η, ← Complex.ofReal_intCast, Complex.re_ofReal_mul]
      rfl
    _ = 0 := by rw [hd, mul_zero, Complex.zero_re]

private theorem alternating_complex_square_zero (a b : ι → ℂ) (η : ℂ)
    (h : 3 < Fintype.card ι) :
    (∑ σ : Equiv.Perm ι, parityReal σ * ((η * matchingProduct a b σ)^2).re) = 0 := by
  let L : Matrix ι (Fin 3) ℂ := Matrix.of fun i k => ![(a i)^2, 2 * a i, 1] k
  let R : Matrix (Fin 3) ι ℂ := Matrix.of fun k j => ![1, b j, (b j)^2] k
  have he (i j : ι) : (L * R) i j = (a i + b j)^2 := by
    simp [L, R, Matrix.mul_apply, Fin.sum_univ_three]
    ring
  have hd := det_mul_eq_zero_of_narrow L R (by simpa using h)
  rw [Matrix.det_apply'] at hd
  simp only [he, Finset.prod_pow] at hd
  change (∑ σ : Equiv.Perm ι, (((Equiv.Perm.sign σ : ℤ) : ℂ) * (matchingProduct a b σ)^2)) = 0 at hd
  calc
    _ = (η^2 * ∑ σ : Equiv.Perm ι, (((Equiv.Perm.sign σ : ℤ) : ℂ) *
      (matchingProduct a b σ)^2)).re := by
      rw [Finset.mul_sum, Complex.re_sum]
      apply Finset.sum_congr rfl
      intro σ _
      rw [mul_pow, mul_left_comm (η^2), ← Complex.ofReal_intCast, Complex.re_ofReal_mul]
      rfl
    _ = 0 := by rw [hd, mul_zero, Complex.zero_re]

/-- A rank-four Euclidean distance kernel gives the second moment exactly. -/
theorem alternating_projected_gap_second_moment (a b : ι → ℂ) (η : ℂ) (H : ℝ)
    (h : 3 < Fintype.card ι) :
    (∑ σ : Equiv.Perm ι, parityReal σ * (H - (η * matchingProduct a b σ).re)^2) =
      Complex.normSq η / 2 * (Matrix.of fun i j => Complex.normSq (a i + b j)).det := by
  let M : Matrix ι ι ℝ := Matrix.of fun i j => Complex.normSq (a i + b j)
  have h₀ := sum_parityReal_zero (ι := ι) (by omega)
  have h₁ := alternating_linear_zero a b η (by omega)
  have h₂ := alternating_complex_square_zero a b η h
  have h₃ : (∑ σ : Equiv.Perm ι, parityReal σ * Complex.normSq (η * matchingProduct a b σ)) =
      Complex.normSq η * M.det := by
    rw [Matrix.det_apply', Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    simp only [parityReal, M, Matrix.of_apply, matchingProduct, map_mul, map_prod]
    ring
  have hid (z : ℂ) :
      z.re ^ 2 = ((z^2).re + Complex.normSq z) / 2 := by
    simp [pow_two, Complex.mul_re, Complex.normSq_apply]
  have hpoly (σ : Equiv.Perm ι) :
      parityReal σ * (H - (η * matchingProduct a b σ).re)^2 =
        H^2 * parityReal σ - 2 * H * (parityReal σ * (η * matchingProduct a b σ).re) +
        (1/2) * (parityReal σ * ((η * matchingProduct a b σ)^2).re +
          parityReal σ * Complex.normSq (η * matchingProduct a b σ)) := by
    let z := η * matchingProduct a b σ
    change parityReal σ * (H - z.re)^2 = _
    linear_combination parityReal σ * hid z
  simp only [hpoly, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, h₀, h₁, h₂, h₃]
  change _ = Complex.normSq η / 2 * M.det
  ring

/-- The two parity classes have identical gap second moments in every order
at least five. No hypothesis of simple spectra or nonzero products. -/
theorem alternating_projected_gap_second_moment_zero (a b : ι → ℂ) (η : ℂ)
    (H : ℝ) (h : 4 < Fintype.card ι) :
    (∑ σ : Equiv.Perm ι, parityReal σ * (H - (η * matchingProduct a b σ).re)^2) = 0 := by
  let L : Matrix ι (Fin 4) ℝ := Matrix.of fun i k =>
    ![1, (a i).re, (a i).im, Complex.normSq (a i)] k
  let R : Matrix (Fin 4) ι ℝ := Matrix.of fun k j =>
    ![Complex.normSq (b j), 2 * (b j).re, 2 * (b j).im, 1] k
  have he : Matrix.of (fun i j => Complex.normSq (a i + b j)) = L * R := by
    ext i j
    simp [L, R, Matrix.mul_apply, Fin.sum_univ_four, Complex.normSq_apply, Complex.add_re,
      Complex.add_im]
    ring
  rw [alternating_projected_gap_second_moment a b η H (by omega), he,
    det_mul_eq_zero_of_narrow L R (by simpa using h), mul_zero]

/-- Four squared distances factor over the lifted planar coordinates. -/
def circleDesign (a : Fin 4 → ℂ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i k => ![1, (a i).re, (a i).im, Complex.normSq (a i)] k

private theorem det_normSq_add_four (a b : Fin 4 → ℂ) :
    (Matrix.of fun i j => Complex.normSq (a i + b j)).det =
      -4 * (circleDesign a).det * (circleDesign b).det := by
  let D : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal ![1,2,2,1]
  let τ : Equiv.Perm (Fin 4) := Equiv.swap 0 3
  let R : Matrix (Fin 4) (Fin 4) ℝ := D * (circleDesign b)ᵀ.submatrix τ id
  have he (k j : Fin 4) : R k j =
      ![Complex.normSq (b j), 2 * (b j).re, 2 * (b j).im, 1] k := by
    fin_cases k <;> simp [R, τ, D, circleDesign, Matrix.diagonal_mul, Equiv.swap_apply_def]
  have h (i j : Fin 4) : Complex.normSq (a i + b j) = (circleDesign a * R) i j := by
    simp [circleDesign, Matrix.mul_apply, Fin.sum_univ_four, he, Complex.normSq_apply,
      Complex.add_re, Complex.add_im]
    ring
  have hD : D.det = 4 := by
    rw [Matrix.det_diagonal, Fin.prod_univ_four]
    change (1 : ℝ) * 2 * 2 * 1 = 4
    ring
  have hτ : (((Equiv.Perm.sign τ : ℤ) : ℝ)) = -1 := by
    simp [τ, Equiv.Perm.sign_swap]
  rw [show Matrix.of (fun i j => Complex.normSq (a i + b j)) = circleDesign a * R from
    Matrix.ext h, Matrix.det_mul, show R.det = _ from
    (Matrix.det_mul _ _), Matrix.det_permute, Matrix.det_transpose, hD, hτ]
  ring

/-- In order four the signed second moment is the product of the two
orientations in the paraboloid lift. The common height cancels. -/
theorem alternating_projected_gap_second_moment_four (a b : Fin 4 → ℂ)
    (η : ℂ) (H : ℝ) :
    (∑ σ : Equiv.Perm (Fin 4), parityReal σ * (H - (η * matchingProduct a b σ).re)^2) =
      -2 * Complex.normSq η * (circleDesign a).det * (circleDesign b).det := by
  rw [alternating_projected_gap_second_moment a b η H (by simp), det_normSq_add_four]
  ring

/-- The lifted planar orientation vanishes exactly on a generalized circle. -/
theorem circleDesign_det_zero_iff_generalizedCircle (a : Fin 4 → ℂ) :
    (circleDesign a).det = 0 ↔ SpectrumOnGeneralizedCircle a := by
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  constructor
  · rintro ⟨w, hw, h⟩
    have hp (i : Fin 4) : w 0 + (a i).re * w 1 + (a i).im * w 2 +
        Complex.normSq (a i) * w 3 = 0 := by
      simpa [Matrix.mulVec, dotProduct, circleDesign, Fin.sum_univ_four] using congrFun h i
    refine ⟨w 3, -(w 1)/2, -(w 2)/2, w 0, ?_, ?_⟩
    · by_contra! hz
      obtain ⟨h3, h1, h2⟩ := hz
      have h1' : w 1 = 0 := by linarith
      have h2' : w 2 = 0 := by linarith
      have h0 : w 0 = 0 := by simpa [h3, h1', h2'] using hp 0
      exact hw (funext (fun k => by fin_cases k <;> assumption))
    · intro i
      change w 3 * Complex.normSq (a i) - 2 * (-(w 1)/2 * (a i).re +
        -(w 2)/2 * (a i).im) + w 0 = 0
      linear_combination hp i
  · rintro ⟨q, u, v, c, hn, h⟩
    let w : Fin 4 → ℝ := ![c, -2*u, -2*v, q]
    refine ⟨w, ?_, ?_⟩
    · intro hw
      have hq : q = 0 := by simpa [w] using congrFun hw 3
      have hu : u = 0 := by simpa [w] using congrFun hw 1
      have hv : v = 0 := by simpa [w] using congrFun hw 2
      simp [hq, hu, hv] at hn
    · funext i
      simp only [Matrix.mulVec, dotProduct, circleDesign, Fin.sum_univ_four, Matrix.of_apply,
        Pi.zero_apply]
      have hi := h i
      change q * Complex.normSq (a i) - 2 * (u * (a i).re + v * (a i).im) + c = 0 at hi
      simp [w]
      linear_combination hi

/-- An order-four real projection has equal parity gap second moments
exactly when one of the two spectra is circular or collinear. -/
theorem alternating_projected_gap_second_moment_four_eq_zero_iff (a b : Fin 4 → ℂ)
    (η : ℂ) (hη : η ≠ 0) (H : ℝ) :
    (∑ σ : Equiv.Perm (Fin 4), parityReal σ * (H - (η * matchingProduct a b σ).re)^2) = 0
      ↔ SpectrumOnGeneralizedCircle a ∨ SpectrumOnGeneralizedCircle b := by
  rw [alternating_projected_gap_second_moment_four a b η H, ← circleDesign_det_zero_iff_generalizedCircle,
    ← circleDesign_det_zero_iff_generalizedCircle]
  simp [mul_eq_zero, (Complex.normSq_pos.mpr hη).ne']

end

end MOC
