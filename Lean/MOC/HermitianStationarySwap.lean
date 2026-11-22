import MOC.StrongSupport
import MOC.Variational
import Mathlib.Data.Complex.Order
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-! Comparing a stationary support maximum with a swap of two Hermitian
eigenvalues gives a strict constraint when the partner's imaginary part is definite. -/

open Matrix
open scoped ComplexOrder

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem det_add_diagonal_swap (h : ι → ℝ) (B : Matrix ι ι ℂ)
    (i j : ι) (hij : i ≠ j) (hM : IsUnit ((diagonal fun k => (h k : ℂ)) + B).det) :
    let M := (diagonal fun k => (h k : ℂ)) + B
    let N := M⁻¹
    let d : ℂ := (h j : ℂ) - h i
    let f : Fin 2 → ι := ![i, j]
    ((diagonal fun k => (h (Equiv.swap i j k) : ℂ)) + B).det =
      M.det * (1 + d * (N i i - N j j) - d ^ 2 * (N.submatrix f f).det) := by
  intro M N d f
  let E : Matrix ι (Fin 2) ℂ := (1 : Matrix ι ι ℂ).submatrix id f
  let D : Matrix (Fin 2) (Fin 2) ℂ := diagonal ![d, -d]
  have hE (A : Matrix ι ι ℂ) : Eᴴ * A * E = A.submatrix f f := by
    calc
      _ = (1 * A * 1).submatrix f f := by
        rw [Matrix.submatrix_mul _ _ f id f Function.bijective_id,
          Matrix.submatrix_mul _ _ f id id Function.bijective_id, Matrix.submatrix_id_id]
        simp [E]
      _ = _ := by simp
  have hupdate :
      (diagonal fun k => (h (Equiv.swap i j k) : ℂ)) + B = M + E * (D * Eᴴ) := by
    have hentry (k l : ι) :
        (E * (D * Eᴴ)) k l =
          (if k = i ∧ l = i then d else 0) - (if k = j ∧ l = j then d else 0) := by
      have he (r : ι) (c : ℂ) :
          (if k = r then (1 : ℂ) else 0) * c * star (if l = r then 1 else 0) =
            if k = r ∧ l = r then c else 0 := by
        by_cases hk : k = r <;> by_cases hl : l = r <;> simp [hk, hl]
      rw [← Matrix.mul_assoc, Matrix.mul_apply, Fin.sum_univ_two]
      simp only [D, Matrix.mul_diagonal, E, Matrix.conjTranspose_apply, Matrix.submatrix_apply,
        id_eq, Matrix.one_apply, f, Matrix.cons_val_zero, Matrix.cons_val_one, he]
      by_cases hj : k = j ∧ l = j <;> simp [hj, sub_eq_add_neg]
    ext k l : 1
    simp only [Matrix.add_apply, hentry]
    by_cases hkl : k = l
    · subst l
      by_cases hki : k = i
      · subst k
        simp [M, d, hij, Equiv.swap_apply_left] <;> ring
      by_cases hkj : k = j
      · subst k
        simp [M, d, hij.symm, Equiv.swap_apply_right] <;> ring
      simp [M, hki, hkj, Equiv.swap_apply_of_ne_of_ne]
    · have hn (r : ι) : ¬ (k = r ∧ l = r) := fun hr => hkl (hr.1.trans hr.2.symm)
      simp [M, Matrix.diagonal_apply_ne _ hkl, hn]
  rw [hupdate, Matrix.det_add_mul E (D * Eᴴ) hM]
  rw [show (D * Eᴴ) * M⁻¹ * E = D * (Eᴴ * M⁻¹ * E) by simp only [Matrix.mul_assoc],
    hE, Matrix.det_fin_two]
  simp only [Matrix.add_apply, Matrix.diagonal_mul, Matrix.diagonal_apply_eq,
    Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), Matrix.submatrix_apply,
    Matrix.det_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one, f, D, zero_add, N]
  ring

private theorem inverse_imaginary_congruence (M : Matrix ι ι ℂ) (hM : IsUnit M.det) :
    (M⁻¹)ᴴ * ((-(Complex.I) / 2) • (M - Mᴴ)) * M⁻¹ =
      (Complex.I / 2) • (M⁻¹ - (M⁻¹)ᴴ) := by
  have hleft : (M⁻¹)ᴴ * Mᴴ = 1 := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_one] using
      congrArg Matrix.conjTranspose (M.mul_nonsing_inv hM)
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_assoc, M.mul_nonsing_inv hM, Matrix.mul_one]
  rw [← Matrix.mul_assoc (M⁻¹)ᴴ Mᴴ M⁻¹, hleft, Matrix.one_mul, neg_div,
    neg_smul, ← smul_neg, neg_sub]

private theorem real_scaled_inverse_pair_det (P : Matrix (Fin 2) (Fin 2) ℂ)
    (η : ℂ) (hx : η * P 0 1 + star (η * P 1 0) = 0) :
    let x₀ := (η * P 0 0).re
    let x₁ := (η * P 1 1).re
    let G := (Complex.I / 2) • (P - Pᴴ)
    η.re * (η * P.det).re = x₀ * x₁ - Complex.normSq η * G.det.re := by
  intro x₀ x₁ G
  have hr := congrArg Complex.re hx
  have hi := congrArg Complex.im hx
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.zero_re, Complex.zero_im] at hr hi
  have h₀ : (Complex.I / 2).re = 0 := by norm_num [Complex.div_re]
  have h₁ : (Complex.I / 2).im = 1 / 2 := by norm_num [Complex.div_im]
  simp only [x₀, x₁, G, Matrix.det_fin_two, Matrix.smul_apply, smul_eq_mul,
    Matrix.sub_apply, Matrix.conjTranspose_apply, Complex.star_def, Complex.normSq_apply,
    Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im, Complex.mul_re,
    Complex.mul_im, h₀, h₁, zero_mul, zero_sub, zero_add, sub_self]
  linear_combination
    -((η.re * (P 0 1).re - η.im * (P 0 1).im) +
      (η.re * (P 1 0).re - η.im * (P 1 0).im)) / 4 * hr -
    ((η.re * (P 0 1).im + η.im * (P 0 1).re) -
      (η.re * (P 1 0).im + η.im * (P 1 0).re)) / 4 * hi

private theorem pair_imaginary_congruence_det_pos (M : Matrix ι ι ℂ) (hM : IsUnit M.det)
    (hp : ((-(Complex.I) / 2) • (M - Mᴴ)).PosDef ∨
      (-((-(Complex.I) / 2) • (M - Mᴴ))).PosDef)
    (f : Fin 2 → ι) (hf : Function.Injective f) :
    0 < (((Complex.I / 2) • (M⁻¹ - (M⁻¹)ᴴ)).submatrix f f).det.re := by
  let E : Matrix ι (Fin 2) ℂ := (1 : Matrix ι ι ℂ).submatrix id f
  have hE (A : Matrix ι ι ℂ) : Eᴴ * A * E = A.submatrix f f := by
    calc
      _ = (1 * A * 1).submatrix f f := by
        rw [Matrix.submatrix_mul _ _ f id f Function.bijective_id,
          Matrix.submatrix_mul _ _ f id id Function.bijective_id, Matrix.submatrix_id_id]
        simp [E]
      _ = _ := by simp
  have hEi : Function.Injective E.mulVec := by
    have he : Eᴴ * E = 1 := by simpa [Matrix.submatrix_one _ hf] using hE 1
    intro x y h
    simpa only [Matrix.mulVec_mulVec, he, Matrix.one_mulVec] using congrArg Eᴴ.mulVec h
  have hNi : Function.Injective M⁻¹.mulVec := by
    intro x y h
    simpa only [Matrix.mulVec_mulVec, M.mul_nonsing_inv hM, Matrix.one_mulVec] using
      congrArg M.mulVec h
  let Q := (Complex.I / 2) • (M⁻¹ - (M⁻¹)ᴴ)
  let R := M⁻¹ * E
  have hRi : Function.Injective R.mulVec := by
    intro x y h
    exact hEi (hNi (by simpa only [R, ← Matrix.mulVec_mulVec] using h))
  have hQR : Q.submatrix f f = Rᴴ * ((-(Complex.I) / 2) • (M - Mᴴ)) * R := by
    rw [← hE, show Q = (M⁻¹)ᴴ * ((-(Complex.I) / 2) • (M - Mᴴ)) * M⁻¹ from
      (inverse_imaginary_congruence M hM).symm]
    simp only [R, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rcases hp with hp | hp
  · rw [hQR]
    exact (Complex.pos_iff.mp (hp.conjTranspose_mul_mul_same hRi).det_pos).1
  · have hneg : (-(Q.submatrix f f)).PosDef := by
      rw [hQR, ← Matrix.neg_mul, ← Matrix.mul_neg]
      exact hp.conjTranspose_mul_mul_same hRi
    have hd := (Complex.pos_iff.mp hneg.det_pos).1
    simpa [Matrix.det_neg] using hd

set_option maxHeartbeats 500000 in
/-- The exact transposition bound at a positive support maximum, with no
sign condition on the partner. The correction is a principal minor of
the negative imaginary part of the inverse. -/
theorem hermitian_support_maximum_swap_bound (h : ι → ℝ) (B : Matrix ι ι ℂ)
    (θ : ℂ) (hh : Function.Injective h)
    (hmax : ∀ V : Matrix ι ι ℂ, IsUnitary V →
      (θ * (B + V * (diagonal fun i => (h i : ℂ)) * Vᴴ).det).re ≤
        (θ * (B + (diagonal fun i => (h i : ℂ))).det).re) :
    let M := (diagonal fun i => (h i : ℂ)) + B
    let η := θ * M.det
    let x (i : ι) := (η * M⁻¹ i i).re
    0 < η.re → ∀ i j, i ≠ j →
      let P := M⁻¹.submatrix (![i, j] : Fin 2 → ι) (![i, j] : Fin 2 → ι)
      (h j - h i) * (η.re * (x i - x j) - (h j - h i) * x i * x j) +
        (h j - h i) ^ 2 * (Complex.normSq η * (((Complex.I / 2) • (P - Pᴴ))).det.re) ≤ 0 := by
  intro M η x hη i j hij
  let H := diagonal fun i => (h i : ℂ)
  let N := M⁻¹
  let f : Fin 2 → ι := ![i, j]
  let P := N.submatrix f f
  let d := h j - h i
  have hM : IsUnit M.det := isUnit_iff_ne_zero.mpr (fun he => by simp [η, he] at hη)
  have hH : Hᴴ = H := by
    simp only [H, Matrix.diagonal_conjTranspose]
    exact congrArg diagonal (funext fun k => by
      simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal])
  have hstat := support_maximum_inverse_commutator B H θ
    (by simpa only [add_comm B H] using hM.ne_zero) hmax
  dsimp only at hstat
  rw [add_comm B H] at hstat
  change ((η • (H * N - N * H)) : Matrix ι ι ℂ)ᴴ = η • (H * N - N * H) at hstat
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hH]
    at hstat
  have hentry := congrArg (fun A : Matrix ι ι ℂ => A i j) hstat
  have hoff : η * P 0 1 + star (η * P 1 0) = 0 := by
    have hd : (h i : ℂ) - h j ≠ 0 := sub_ne_zero.mpr
      (fun he => hij (hh (Complex.ofReal_injective he)))
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_mul,
      Matrix.mul_diagonal, H, Matrix.conjTranspose_apply] at hentry
    have he : ((h i : ℂ) - h j) * (η * N i j + star (η * N j i)) = 0 := by
      rw [star_mul']
      linear_combination -hentry
    simpa [P, f] using (mul_eq_zero.mp he).resolve_left hd
  have hpair := real_scaled_inverse_pair_det P η hoff
  change η.re * (η * P.det).re =
    x i * x j - Complex.normSq η * (((Complex.I / 2) • (P - Pᴴ))).det.re at hpair
  have hswap := hmax ((Equiv.swap i j).permMatrix ℂ) (isUnitary_permMatrix (Equiv.swap i j))
  rw [permMatrix_conjugates, show H.submatrix (Equiv.swap i j) (Equiv.swap i j) =
    diagonal (fun k => (h (Equiv.swap i j k) : ℂ)) from
      Matrix.submatrix_diagonal_equiv _ _, add_comm B, add_comm B] at hswap
  rw [det_add_diagonal_swap h B i j hij hM] at hswap
  simp only [← Complex.ofReal_sub] at hswap
  change (θ * (M.det * (1 + (d : ℂ) * (N i i - N j j) - (d : ℂ) ^ 2 * P.det))).re ≤
    (θ * M.det).re at hswap
  have hswap' : d * (x i - x j) - d ^ 2 * (η * P.det).re ≤ 0 := by
    have he : θ * (M.det * (1 + (d : ℂ) * (N i i - N j j) - (d : ℂ) ^ 2 * P.det)) =
        η + (d : ℂ) * (η * N i i - η * N j j) - ((d ^ 2 : ℝ) : ℂ) * (η * P.det) := by
      simp only [η, Complex.ofReal_pow]
      ring
    rw [he] at hswap
    simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] at hswap
    change η.re + d * (x i - x j) - d ^ 2 * (η * P.det).re ≤ η.re at hswap
    linarith
  have hbound := mul_nonpos_of_nonneg_of_nonpos hη.le hswap'
  let s := Complex.normSq η * (((Complex.I / 2) • (P - Pᴴ))).det.re
  have hle : d * (η.re * (x i - x j) - d * x i * x j) + d ^ 2 * s ≤ 0 := by
    calc
      _ = η.re * (d * (x i - x j)) - d ^ 2 * (x i * x j - s) := by ring
      _ = η.re * (d * (x i - x j) - d ^ 2 * (η * P.det).re) := by
        rw [show x i * x j - s = η.re * (η * P.det).re from hpair.symm]
        ring
      _ ≤ 0 := hbound
  exact hle

/-- A positive support maximum against a partner with definite imaginary
part satisfies a strict swap inequality for distinct Hermitian labels. -/
theorem hermitian_support_maximum_swap (h : ι → ℝ) (B : Matrix ι ι ℂ)
    (θ : ℂ) (hh : Function.Injective h)
    (hp : ((-(Complex.I) / 2) • (B - Bᴴ)).PosDef ∨
      (-((-(Complex.I) / 2) • (B - Bᴴ))).PosDef)
    (hmax : ∀ V : Matrix ι ι ℂ, IsUnitary V →
      (θ * (B + V * (diagonal fun i => (h i : ℂ)) * Vᴴ).det).re ≤
        (θ * (B + (diagonal fun i => (h i : ℂ))).det).re) :
    let M := (diagonal fun i => (h i : ℂ)) + B
    let η := θ * M.det
    let x (i : ι) := (η * M⁻¹ i i).re
    0 < η.re → ∀ i j, i ≠ j →
      (h j - h i) * (η.re * (x i - x j) - (h j - h i) * x i * x j) < 0 := by
  intro M η x hη i j hij
  let H := diagonal fun i => (h i : ℂ)
  let f : Fin 2 → ι := ![i, j]
  let P := M⁻¹.submatrix f f
  have hM : IsUnit M.det := isUnit_iff_ne_zero.mpr (fun he => by simp [η, he] at hη)
  have hf : Function.Injective f := by
    intro r s hrs
    fin_cases r <;> fin_cases s <;> simp [f, hij, hij.symm] at hrs ⊢
  have hH : Hᴴ = H := by
    simp only [H, Matrix.diagonal_conjTranspose]
    exact congrArg diagonal (funext fun k => by
      simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal])
  have hMi : ((-(Complex.I) / 2) • (M - Mᴴ)).PosDef ∨
      (-((-(Complex.I) / 2) • (M - Mᴴ))).PosDef := by
    change ((-(Complex.I) / 2) • ((H + B) - (H + B)ᴴ)).PosDef ∨
      (-((-(Complex.I) / 2) • ((H + B) - (H + B)ᴴ))).PosDef
    rw [Matrix.conjTranspose_add, hH, add_sub_add_left_eq_sub]
    exact hp
  have hG := pair_imaginary_congruence_det_pos M hM hMi f hf
  have hG' : 0 < (((Complex.I / 2) • (P - Pᴴ))).det.re := by
    simpa only [Matrix.submatrix_smul, Matrix.submatrix_sub, ← Matrix.conjTranspose_submatrix, P]
      using hG
  have hd : h j - h i ≠ 0 := sub_ne_zero.mpr (fun he => hij (hh he.symm))
  have hη₀ : η ≠ 0 := fun he => by simp [he] at hη
  have hstrict := mul_pos (sq_pos_of_ne_zero hd) (mul_pos (Complex.normSq_pos.mpr hη₀) hG')
  have hbound := hermitian_support_maximum_swap_bound h B θ hh hmax hη i j hij
  exact (lt_add_of_pos_right _ hstrict).trans_le hbound

/-- If the stationary pair term vanishes, the corresponding inverse
imaginary principal minor is nonpositive, even for mixed partner signs. -/
theorem hermitian_support_maximum_swap_minor_nonpos (h : ι → ℝ) (B : Matrix ι ι ℂ)
    (θ : ℂ) (hh : Function.Injective h)
    (hmax : ∀ V : Matrix ι ι ℂ, IsUnitary V →
      (θ * (B + V * (diagonal fun i => (h i : ℂ)) * Vᴴ).det).re ≤
        (θ * (B + (diagonal fun i => (h i : ℂ))).det).re) :
    let M := (diagonal fun i => (h i : ℂ)) + B
    let η := θ * M.det
    let x (i : ι) := (η * M⁻¹ i i).re
    0 < η.re → ∀ i j, i ≠ j →
      η.re * (x i - x j) = (h j - h i) * x i * x j →
      let P := M⁻¹.submatrix (![i, j] : Fin 2 → ι) (![i, j] : Fin 2 → ι)
      (((Complex.I / 2) • (P - Pᴴ))).det.re ≤ 0 := by
  intro M η x hη i j hij he
  have hb := hermitian_support_maximum_swap_bound h B θ hh hmax hη i j hij
  dsimp only at hb
  change (h j - h i) * (η.re * (x i - x j) - (h j - h i) * x i * x j) + _ ≤ 0 at hb
  rw [he, sub_self, mul_zero, zero_add] at hb
  have hd : h j - h i ≠ 0 := sub_ne_zero.mpr (fun eq => hij (hh eq.symm))
  have hη₀ : η ≠ 0 := fun eq => by simp [eq] at hη
  dsimp only
  by_contra! hf
  exact (not_lt_of_ge hb)
    (mul_pos (sq_pos_of_ne_zero hd) (mul_pos (Complex.normSq_pos.mpr hη₀) hf))

/-- If the inverse diagonal entries are nonzero, the swap inequality gives
the order of the two real stationary poles and proves they are distinct. -/
theorem hermitian_stationary_swap_pole_order {h₀ h₁ a x₀ x₁ : ℝ} (hh : h₀ < h₁)
    (hx₀ : x₀ ≠ 0) (hx₁ : x₁ ≠ 0)
    (hswap : (h₁ - h₀) * (a * (x₀ - x₁) - (h₁ - h₀) * x₀ * x₁) < 0) :
    0 < x₀ * x₁ * ((h₁ - a / x₁) - (h₀ - a / x₀)) := by
  have he :
      a * (x₀ - x₁) - (h₁ - h₀) * x₀ * x₁ =
        -(x₀ * x₁ * ((h₁ - a / x₁) - (h₀ - a / x₀))) := by
    field_simp [hx₀, hx₁] <;> ring
  rw [he, mul_neg, neg_lt_zero] at hswap
  by_contra! ha
  exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos (sub_pos.mpr hh).le ha)) hswap

omit [Fintype ι] [DecidableEq ι] in
/-- The swap condition makes the poles distinct, including the pole at
infinity corresponding to a zero diagonal entry of the scaled inverse. -/
theorem hermitian_stationary_swap_projective_poles (h x : ι → ℝ) (a : ℝ)
    (hh : Function.Injective h)
    (hswap : ∀ i j, i ≠ j →
      (h j - h i) * (a * (x i - x j) - (h j - h i) * x i * x j) < 0) :
    Function.Injective
      (fun i => if x i = 0 then (none : Option ℝ) else some (h i - a / x i)) := by
  intro i j he
  by_contra hij
  by_cases hxi : x i = 0 <;> by_cases hxj : x j = 0
  · have hs := hswap i j hij
    simp [hxi, hxj] at hs
  · simp [hxi, hxj] at he
  · simp [hxi, hxj] at he
  · have hp : h i - a / x i = h j - a / x j := by simpa [hxi, hxj] using he
    rcases lt_or_gt_of_ne (fun hn => hij (hh hn)) with hlt | hlt
    · have hs := hermitian_stationary_swap_pole_order hlt hxi hxj (hswap i j hij)
      simp [hp] at hs
    · have hs := hermitian_stationary_swap_pole_order hlt hxj hxi (hswap j i (fun he => hij he.symm))
      simp [hp] at hs

omit [Fintype ι] [DecidableEq ι] in
/-- Along increasing Hermitian eigenvalues, the signs of the nonzero scaled
inverse diagonal entries cannot alternate on three labels. -/
theorem hermitian_stationary_swap_no_alternating_signs (h x : ι → ℝ) (a : ℝ)
    (hswap : ∀ i j, i ≠ j →
      (h j - h i) * (a * (x i - x j) - (h j - h i) * x i * x j) < 0)
    {i j k : ι} (hij : h i < h j) (hjk : h j < h k)
    (hij' : x i * x j < 0) (hjk' : x j * x k < 0) (hik' : 0 < x i * x k) : False := by
  let p (l : ι) := h l - a / x l
  have horder {r s : ι} (hrs : h r < h s) (hn : x r * x s ≠ 0) :
      0 < (x r * x s) * (p s - p r) :=
    hermitian_stationary_swap_pole_order hrs (left_ne_zero_of_mul hn) (right_ne_zero_of_mul hn)
      (hswap r s (fun he => (ne_of_lt hrs) (congrArg h he)))
  have hdesc {r s : ι} (hrs : h r < h s) (hneg : x r * x s < 0) : p s < p r := by
    by_contra! hn
    exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg hneg.le (sub_nonneg.mpr hn)))
      (horder hrs hneg.ne)
  have hlt := (hdesc hjk hjk').trans (hdesc hij hij')
  exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hik'.le (sub_nonpos.mpr hlt.le)))
    (horder (hij.trans hjk) hik'.ne')

end

end MOC
