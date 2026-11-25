import MOC.Householder
import MOC.Pencil
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Real.Sqrt

/-! Determinant support for a rank-one compression with a distinguished
deleted spectral label. Its squared retained amplitude fixes the anchor quota. -/

open Matrix

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- In isometric coordinates, subtracting the distinguished spectral value
removes the top row from the weighted compression. -/
theorem rankOneCompressionDisk_eq_compression (b : ι → ℂ) (γ : ℂ)
    (R : Matrix Unit ι ℂ) (v : ι → ℂ) (z : ℂ)
    (hW : let W := fromRows R (rankOnePhase v z)ᴴ; Wᴴ * W = 1) :
    let H := rankOnePhase v z
    let W := fromRows R Hᴴ
    Wᴴ * diagonal (Sum.elim (fun _ : Unit => γ) b) * W =
      γ • (1 : Matrix ι ι ℂ) + H * diagonal (fun j => b j - γ) * Hᴴ := by
  intro H W
  let D := diagonal (fun j => b j - γ)
  have hWW : Wᴴ * W = 1 := hW
  have hD : diagonal (Sum.elim (fun _ : Unit => γ) b) =
      γ • (1 : Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℂ) + fromBlocks 0 0 0 D := by
    ext (i | i) (j | j) : 1
    · have h : i = j := Subsingleton.elim _ _
      subst j
      simp [Matrix.diagonal_apply, Matrix.one_apply]
    · simp [Matrix.diagonal_apply, Matrix.one_apply]
    · simp [Matrix.diagonal_apply, Matrix.one_apply]
    · by_cases h : i = j <;> simp [D, Matrix.diagonal_apply, Matrix.one_apply, h] <;> ring
  rw [hD, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hWW]
  congr 1
  simp only [D, W, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
    Matrix.conjTranspose_conjTranspose, Matrix.fromCols_mul_fromBlocks,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.fromCols_mul_fromRows]
  rfl

private theorem rankOnePhase_conjTranspose (v : ι → ℂ) (z : ℂ) :
    (rankOnePhase v z)ᴴ = rankOnePhase v (star z) := by
  have hP : (vecMulVec v (star ∘ v))ᴴ = vecMulVec v (star ∘ v) := by
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.vecMulVec_apply, Function.comp_apply,
      star_mul', star_star]
    ring
  change (1 + (z - 1) • vecMulVec v (star ∘ v))ᴴ =
    1 + (star z - 1) • vecMulVec v (star ∘ v)
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one,
    Matrix.conjTranspose_smul, hP, star_sub, star_one]

private theorem det_rankOnePhase_biaffine (A B : Matrix ι ι ℂ) (v : ι → ℂ) (s t : ℂ) :
    let d (x y : ℂ) := (A + rankOnePhase v x * B * rankOnePhase v y).det
    d s t = d 0 0 + s * (d 1 0 - d 0 0) + t * (d 0 1 - d 0 0) +
      s * t * (d 1 1 - d 1 0 - d 0 1 + d 0 0) := by
  intro d
  let P : Matrix ι ι ℂ := vecMulVec v (star ∘ v)
  let L : Matrix ι (Fin 1) ℂ := Matrix.of fun i _ => v i
  let R : Matrix (Fin 1) ι ℂ := Matrix.of fun _ j => star (v j)
  have hLR : L * R = P := by
    ext i j
    simp [L, R, P, Matrix.mul_apply, Matrix.vecMulVec_apply]
  have hphase (z : ℂ) : 1 - P + z • (L * R) = rankOnePhase v z := by
    rw [hLR, rankOnePhase, sub_smul, one_smul]
    change 1 - P + z • P = 1 + (z • P - P)
    abel
  let p (x y : ℂ) :=
    (A + (1 - P + x • (L * R)) * B * (1 - P + y • (L * R))).det
  have hp : p s t = p 0 0 + s * (p 1 0 - p 0 0) + t * (p 0 1 - p 0 0) +
      s * t * (p 1 1 - p 1 0 - p 0 1 + p 0 0) := by
    simpa only [p, Matrix.one_mul] using
      det_completion_biaffine A (1 : Matrix ι ι ℂ) (1 - P) (1 - P) B L R L R s t
  have hdp (x y : ℂ) : d x y = p x y := by
    dsimp only [d, p]
    rw [hphase x, hphase y]
  simp only [hdp]
  exact hp

/-- Five scalar evaluations recover the support everywhere on the compression disk. -/
theorem rankOneCompressionDisk_support (A B : Matrix ι ι ℂ) (v : ι → ℂ) (η z : ℂ) :
    let F (w : ℂ) := (η * (A + rankOnePhase v w * B * (rankOnePhase v w)ᴴ).det).re
    F z = F 0 + (F 1 - F (-1)) / 2 * z.re + (F Complex.I - F (-Complex.I)) / 2 * z.im +
      ((F 1 + F (-1)) / 2 - F 0) * Complex.normSq z := by
  intro F
  let d (x y : ℂ) := (A + rankOnePhase v x * B * rankOnePhase v y).det
  let a := d 0 0
  let b := d 1 0 - a
  let c := d 0 1 - a
  let e := d 1 1 - d 1 0 - d 0 1 + a
  have hf (w : ℂ) : F w = (η * (a + w * b + star w * c + w * star w * e)).re := by
    change (η * (A + rankOnePhase v w * B * (rankOnePhase v w)ᴴ).det).re = _
    rw [rankOnePhase_conjTranspose]
    exact congrArg (fun x : ℂ => (η * x).re) (det_rankOnePhase_biaffine A B v w (star w))
  rw [hf z, hf 0, hf 1, hf (-1), hf Complex.I, hf (-Complex.I)]
  norm_num [Complex.star_def, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im] <;> ring

/-- The fixed quota `normSq z` contributes the boundary score at the distinguished
label. The remaining quota pays an explicit support correction. -/
theorem rankOneCompressionDisk_support_le_quota (A B : Matrix ι ι ℂ) (v : ι → ℂ) (η z : ℂ) :
    let F (w : ℂ) := (η * (A + rankOnePhase v w * B * (rankOnePhase v w)ᴴ).det).re
    let a := F 0
    let c := (F 1 + F (-1)) / 2 - F 0
    let Bnd := Real.sqrt (((F 1 - F (-1)) / 2) ^ 2 + ((F Complex.I - F (-Complex.I)) / 2) ^ 2)
    let p := Complex.normSq z
    let r := Real.sqrt p
    F z ≤ p * (a + c + Bnd) + (1 - p) * (a + r / (1 + r) * Bnd) := by
  intro F a c Bnd p r
  let x := (F 1 - F (-1)) / 2
  let y := (F Complex.I - F (-Complex.I)) / 2
  have hF : F z = a + x * z.re + y * z.im + c * p := rankOneCompressionDisk_support A B v η z
  have hp : 0 ≤ p := Complex.normSq_nonneg z
  have hr : 0 ≤ r := Real.sqrt_nonneg p
  have hr2 : r ^ 2 = p := Real.sq_sqrt hp
  have hB : 0 ≤ Bnd := Real.sqrt_nonneg _
  have hB2 : Bnd ^ 2 = x ^ 2 + y ^ 2 := Real.sq_sqrt (by positivity)
  have hn : p = z.re ^ 2 + z.im ^ 2 := by
    change Complex.normSq z = _
    rw [Complex.normSq_apply]
    ring
  have hsq : (x * z.re + y * z.im) ^ 2 ≤ (r * Bnd) ^ 2 := by
    rw [mul_pow, hr2, hB2, hn]
    nlinarith only [sq_nonneg (x * z.im - y * z.re)]
  have hlinear := (le_abs_self (x * z.re + y * z.im)).trans
    (abs_le_of_sq_le_sq hsq (mul_nonneg hr hB))
  have hden : 0 < 1 + r := by positivity
  have hsplit : (1 - p) * (r / (1 + r)) = r - p := by
    rw [← mul_div_assoc]
    apply (div_eq_iff hden.ne').mpr
    linear_combination -hr2
  rw [hF]
  calc
    _ ≤ a + r * Bnd + c * p := by linarith only [hlinear]
    _ = _ := by
      rw [show (1 - p) * (a + r / (1 + r) * Bnd) =
        (1 - p) * a + ((1 - p) * (r / (1 + r))) * Bnd by ring, hsplit]
      ring

end

end MOC
