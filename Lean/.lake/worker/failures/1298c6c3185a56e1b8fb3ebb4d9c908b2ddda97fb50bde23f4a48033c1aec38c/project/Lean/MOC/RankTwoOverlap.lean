import MOC.RankSum
import MOC.TwoFrame
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Complementary-block compression of a sum supported on two frames. -/

open BigOperators Matrix
open scoped InnerProductSpace

namespace MOC

noncomputable section

variable {ι κ ρ σ : Type*}
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype ρ] [DecidableEq ρ] [Fintype σ] [DecidableEq σ]

/-- Two frames for a common subspace give the reciprocal determinant on that
subspace. The change of column labels places the complementary blocks in a
single square matrix. -/
theorem det_support_frames (e : ι ⊕ κ ≃ ρ ⊕ σ)
    (X : Matrix ι ρ ℂ) (Y : Matrix ι σ ℂ)
    (E : Matrix ρ κ ℂ) (F : Matrix σ κ ℂ)
    (hE : Eᴴ * E = 1) (hF : Fᴴ * F = 1) (hcommon : X * E = Y * F)
    (hG : IsUnit (X * Xᴴ + Y * Yᴴ).det)
    (a : ρ → ℂ) (b : σ → ℂ) (ha : ∀ i, a i ≠ 0) (hb : ∀ j, b j ≠ 0) :
    (X * diagonal a * Xᴴ + Y * diagonal b * Yᴴ).det =
      ((∏ i, a i) * ∏ j, b j) * ((X * Xᴴ + Y * Yᴴ).det / (2 : ℂ) ^ Fintype.card κ) *
        (Eᴴ * diagonal (fun i => (a i)⁻¹) * E + Fᴴ * diagonal (fun j => (b j)⁻¹) * F).det := by
  let s : ℂ := ((1 / 2 : ℝ) : ℂ) + ((1 / 2 : ℝ) : ℂ) * Complex.I
  have hs₀ : star s * s = ((1 / 2 : ℝ) : ℂ) := by
    apply Complex.ext <;> norm_num [s, Complex.star_def, Complex.mul_re, Complex.mul_im]
  have hs : star s * s = (2 : ℂ)⁻¹ := by simpa [one_div, Complex.ofReal_inv] using hs₀
  have hs' : s * star s = (2 : ℂ)⁻¹ := (mul_comm _ _).trans hs
  let W₀ := fromBlocks X Y (star s • Eᴴ) ((-star s) • Fᴴ)
  let W := W₀.submatrix id e
  have hreindex (L : Matrix (ρ ⊕ σ) (ρ ⊕ σ) ℂ) :
      W * L.submatrix e e * Wᴴ = W₀ * L * W₀ᴴ := by
    dsimp only [W]
    rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_mul_equiv]
    rfl
  have hupper : X * (s • E) + Y * ((-s) • F) = 0 := by
    simp only [Matrix.mul_smul, hcommon, neg_smul, add_neg_cancel]
  have hlower : (star s • Eᴴ) * Xᴴ + ((-star s) • Fᴴ) * Yᴴ = 0 := by
    have h := congrArg Matrix.conjTranspose hupper
    simpa only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_smul,
      star_neg, Matrix.conjTranspose_zero] using h
  have hgram : W * Wᴴ = fromBlocks (X * Xᴴ + Y * Yᴴ) 0 0 (1 : Matrix κ κ ℂ) := by
    have h := hreindex (1 : Matrix (ρ ⊕ σ) (ρ ⊕ σ) ℂ)
    rw [Matrix.submatrix_one_equiv, Matrix.mul_one, Matrix.mul_one] at h
    rw [h]
    simp only [W₀, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_conjTranspose, star_neg, star_star, Matrix.fromBlocks_multiply,
      hupper, hlower]
    congr 1
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, neg_mul_neg, hs, hs', hE, hF,
      ← add_smul]
    norm_num
  have hblocks (c : ρ → ℂ) (d : σ → ℂ) :
      let L := (diagonal (Sum.elim c d)).submatrix e e
      (W * L * Wᴴ).toBlocks₁₁ = X * diagonal c * Xᴴ + Y * diagonal d * Yᴴ ∧
      (W * L * Wᴴ).toBlocks₂₂ =
        ((2 : ℂ)⁻¹) • (Eᴴ * diagonal c * E + Fᴴ * diagonal d * F) := by
    dsimp only
    rw [hreindex, ← Matrix.fromBlocks_diagonal]
    simp only [W₀, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_conjTranspose, star_neg, star_star, Matrix.fromBlocks_multiply,
      Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.toBlocks_fromBlocks₁₁,
      Matrix.toBlocks_fromBlocks₂₂, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      neg_mul_neg, hs, hs', ← smul_add] <;> exact ⟨rfl, rfl⟩
  let c : ρ → ℂ := fun i => (a i)⁻¹
  let d : σ → ℂ := fun j => (b j)⁻¹
  let L := (diagonal (Sum.elim a b)).submatrix e e
  let Linv := (diagonal (Sum.elim c d)).submatrix e e
  have hL : L * Linv = 1 := by
    dsimp only [L, Linv]
    rw [Matrix.submatrix_mul_equiv, Matrix.diagonal_mul_diagonal, Matrix.submatrix_diagonal_equiv,
      ← Matrix.diagonal_one]
    apply congrArg Matrix.diagonal
    funext k
    cases e k <;> simp [c, d, ha, hb]
  have hdet : L.det = (∏ i, a i) * ∏ j, b j := by
    dsimp only [L]
    rw [Matrix.det_submatrix_equiv_self, Matrix.det_diagonal, Fintype.prod_sum_type]
    rfl
  have h := det_compress_of_orthogonal_row_blocks W L Linv _ hgram hG hL
  rw [(hblocks a b).1, (hblocks c d).2, hdet, Matrix.det_smul] at h
  rw [h, inv_pow, div_eq_mul_inv]
  ring

private theorem exists_overlap_frames (e : ι ⊕ κ ≃ ρ ⊕ σ)
    (X : Matrix ι ρ ℂ) (Y : Matrix ι σ ℂ) (hX : Xᴴ * X = 1) (hY : Yᴴ * Y = 1)
    (hG : IsUnit (X * Xᴴ + Y * Yᴴ).det) :
    ∃ (E : Matrix ρ κ ℂ) (F : Matrix σ κ ℂ), Eᴴ * E = 1 ∧ Fᴴ * F = 1 ∧ X * E = Y * F := by
  let T := fromCols X Y
  let G := X * Xᴴ + Y * Yᴴ
  have hTG : T * Tᴴ = G := by
    simp only [T, G, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
      Matrix.fromCols_mul_fromRows]
  have hInv : T * (Tᴴ * G⁻¹) = 1 := by
    rw [← Matrix.mul_assoc, hTG, Matrix.mul_nonsing_inv _ hG]
  let L := Matrix.toEuclideanLin T
  have hsurj : Function.Surjective L := by
    intro v
    refine ⟨(WithLp.equiv 2 _).symm ((Tᴴ * G⁻¹) *ᵥ WithLp.equiv 2 _ v), ?_⟩
    apply (WithLp.equiv 2 _).injective
    simp only [L, Matrix.piLp_equiv_toEuclideanLin_apply, Equiv.apply_symm_apply,
      Matrix.mulVec_mulVec, hInv, Matrix.one_mulVec]
  have hcard := Fintype.card_congr e
  have hdim := L.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj, Submodule.finrank_top,
    finrank_euclideanSpace, finrank_euclideanSpace, Fintype.card_sum] at hdim
  rw [Fintype.card_sum, Fintype.card_sum] at hcard
  have hdim' : Module.finrank ℂ (LinearMap.ker L) = Fintype.card κ := by omega
  let b := (stdOrthonormalBasis ℂ (LinearMap.ker L)).reindex
    ((finCongr hdim').trans (Fintype.equivFin κ).symm)
  let K : Matrix (ρ ⊕ σ) κ ℂ := Matrix.of fun i j => WithLp.equiv 2 _ (b j).val i
  have hK : Kᴴ * K = 1 := by
    ext i j
    rw [Matrix.one_apply, ← orthonormal_iff_ite.mp b.orthonormal i j]
    change (Kᴴ * K) i j = ⟪(b i).val, (b j).val⟫_ℂ
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    rfl
  have hTK : T * K = 0 := by
    ext i j
    have h := congrArg (fun v => WithLp.equiv 2 _ v i) (LinearMap.mem_ker.mp (b j).property)
    simpa only [L, Matrix.piLp_equiv_toEuclideanLin_apply] using h
  let E₀ := K.toRows₁
  let F₀ := K.toRows₂
  have hK' : fromRows E₀ F₀ = K := Matrix.fromRows_toRows _
  have hsum : E₀ᴴ * E₀ + F₀ᴴ * F₀ = 1 := by
    rw [← hK, ← hK', Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
      Matrix.fromCols_mul_fromRows]
  have hz : X * E₀ + Y * F₀ = 0 := by
    rw [← hTK, ← hK', Matrix.fromCols_mul_fromRows]
  have hneg : X * E₀ = -(Y * F₀) := eq_neg_of_add_eq_zero_left hz
  have hEq : E₀ᴴ * E₀ = F₀ᴴ * F₀ := by
    have h (X : Matrix ι ρ ℂ) (E : Matrix ρ κ ℂ) (hX : Xᴴ * X = 1) :
        (X * E)ᴴ * (X * E) = Eᴴ * E := by
      rw [Matrix.conjTranspose_mul, Matrix.mul_assoc Eᴴ Xᴴ,
        ← Matrix.mul_assoc Xᴴ X, hX, Matrix.one_mul]
    have h' (Y : Matrix ι σ ℂ) (F : Matrix σ κ ℂ) (hY : Yᴴ * Y = 1) :
        (Y * F)ᴴ * (Y * F) = Fᴴ * F := by
      rw [Matrix.conjTranspose_mul, Matrix.mul_assoc Fᴴ Yᴴ,
        ← Matrix.mul_assoc Yᴴ Y, hY, Matrix.one_mul]
    rw [← h X E₀ hX, hneg, Matrix.conjTranspose_neg, neg_mul_neg, h' Y F₀ hY]
  let t : ℂ := 1 + Complex.I
  have ht : star t * t = (2 : ℂ) := by
    apply Complex.ext <;> norm_num [t, Complex.star_def, Complex.mul_re, Complex.mul_im]
  have ht' : t * star t = (2 : ℂ) := (mul_comm _ _).trans ht
  refine ⟨t • E₀, (-t) • F₀, ?_, ?_, ?_⟩
  · simpa only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      ht, ht', two_smul] using (by rw [hEq] at hsum; rw [hEq]; exact hsum :
        E₀ᴴ * E₀ + E₀ᴴ * E₀ = 1)
  · simpa only [Matrix.conjTranspose_smul, star_neg, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      neg_mul_neg, ht, ht', two_smul] using (hEq ▸ hsum : F₀ᴴ * F₀ + F₀ᴴ * F₀ = 1)
  · rw [Matrix.mul_smul, Matrix.mul_smul, hneg, smul_neg, neg_smul]

end

end MOC
