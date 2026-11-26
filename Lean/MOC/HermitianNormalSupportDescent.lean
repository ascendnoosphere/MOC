import MOC.HermitianByNormal
import MOC.HermitianExteriorShift
import MOC.StrongSupport

/-! A normal sum of a Hermitian matrix and a normal partner has a block
decomposition by the imaginary levels of the partner. -/

open Matrix

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- In the partner eigenbasis, normality is equivalent to the absence of
Hermitian entries between distinct imaginary levels of the partner. -/
theorem normal_diagonal_add_hermitian_iff_imaginary_blocks
    (b : ι → ℂ) (H : Matrix ι ι ℂ) (hH : H.IsHermitian) :
    IsStarNormal (diagonal b + H) ↔
      ∀ i j, (b i).im ≠ (b j).im → H i j = 0 := by
  let D := diagonal b
  let c (i : ι) : ℂ := star (b i) - b i
  have hD : Dᴴ * D = D * Dᴴ := by
    dsimp only [D]
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal]
    exact congrArg diagonal (funext fun i => mul_comm _ _)
  have hdiff : Dᴴ - D = diagonal c := by
    dsimp only [D]
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_sub] <;> rfl
  have hidentity : (D + H)ᴴ * (D + H) - (D + H) * (D + H)ᴴ =
      (Dᴴ - D) * H - H * (Dᴴ - D) := by
    simp only [Matrix.conjTranspose_add, hH.eq, Matrix.add_mul, Matrix.mul_add,
      Matrix.sub_mul, Matrix.mul_sub, hD]
    abel
  have hlevel (i j : ι) : c i = c j ↔ (b i).im = (b j).im := by
    constructor
    · intro h
      have hi := congrArg Complex.im h
      simp only [c, Complex.star_def, Complex.sub_im, Complex.conj_im] at hi
      linarith only [hi]
    · intro h
      apply Complex.ext
      · simp only [c, Complex.star_def, Complex.sub_re, Complex.conj_re, sub_self]
      · simp only [c, Complex.star_def, Complex.sub_im, Complex.conj_im, h]
  have hentry (i j : ι) :
      ((D + H)ᴴ * (D + H) - (D + H) * (D + H)ᴴ) i j = (c i - c j) * H i j := by
    rw [hidentity, hdiff, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
      sub_mul, mul_comm (H i j) (c j)]
  constructor
  · intro hN i j hij
    have he : (D + H)ᴴ * (D + H) = (D + H) * (D + H)ᴴ := hN.star_comm_self.eq
    have hz : (c i - c j) * H i j = 0 := by
      rw [← hentry, he, sub_self, Matrix.zero_apply]
    exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr fun hc => hij ((hlevel i j).mp hc))
  · intro hblock
    constructor
    change (D + H)ᴴ * (D + H) = (D + H) * (D + H)ᴴ
    apply sub_eq_zero.mp
    ext i j : 1
    rw [hentry, Matrix.zero_apply]
    by_cases h : (b i).im = (b j).im
    · rw [(hlevel i j).mpr h, sub_self, zero_mul]
    · rw [hblock i j h, mul_zero]

/-- A Hermitian matrix with a normal partner satisfies determinant inclusion
at every mixer that gives a normal sum. -/
theorem holds_of_normal_sum_with_hermitian_right
    (a : ι → ℝ) (b : ι → ℂ) (V : Matrix ι ι ℂ) (hV : IsUnitary V)
    (hN : IsStarNormal (diagonal b + V * diagonal (fun i => (a i : ℂ)) * Vᴴ)) :
    Holds b (fun i => (a i : ℂ)) V := by
  classical
  let H := V * diagonal (fun i => (a i : ℂ)) * Vᴴ
  have hH : H.IsHermitian := Matrix.isHermitian_mul_mul_conjTranspose V
    (Matrix.isHermitian_diagonal_iff.mpr fun i => by
      simp only [isSelfAdjoint_iff, Complex.star_def, Complex.conj_ofReal])
  have hz := (normal_diagonal_add_hermitian_iff_imaginary_blocks b H hH).mp hN
  have hex (t : ℝ) (ht : t ∈ Set.range (fun i => (b i).im)) : ∃ j, (b j).im = t := ht
  let f (i : ι) := Classical.choose (hex (b i).im ⟨i, rfl⟩)
  have him (i : ι) : (b (f i)).im = (b i).im := Classical.choose_spec (hex (b i).im ⟨i, rfl⟩)
  have hclass (i j : ι) : f i = f j ↔ (b i).im = (b j).im := by
    constructor
    · intro he
      rw [← him i, ← him j, he]
    · intro he
      dsimp only [f]
      simp only [he]
  apply holds_of_affine_partner_blocks a b V hV f
  · change exteriorOffBlock f H = 0
    ext i j : 1
    change (if f i = f j then 0 else H i j) = 0
    by_cases h : f i = f j
    · rw [if_pos h]
    · rw [if_neg h]
      exact hz i j (fun he => h ((hclass i j).mpr he))
  · intro i
    refine ⟨(b i).im * Complex.I, 1, fun j hj => ⟨(b j).re, ?_⟩⟩
    have he := (hclass j i).mp hj
    rw [mul_one, ← he, add_comm, Complex.re_add_im]

/-- In any finite dimension, the Hermitian–normal conjecture is equivalent
to existence of a normal sum at a maximizer in every support direction. -/
theorem hermitianByNormal_iff_normal_support_maximizer : HermitianByNormal ι ↔
    ∀ (a : ι → ℝ) (b : ι → ℂ) (η : ℂ),
      ∃ V : Matrix ι ι ℂ, IsUnitary V ∧
        IsStarNormal (diagonal b + V * diagonal (fun i => (a i : ℂ)) * Vᴴ) ∧
        ∀ W : Matrix ι ι ℂ, IsUnitary W →
          (η * determinantValue b (fun i => (a i : ℂ)) W).re ≤
            (η * determinantValue b (fun i => (a i : ℂ)) V).re := by
  classical
  constructor
  · intro h a b η
    let A (i : ι) : ℂ := a i
    obtain ⟨σ, _, hσ⟩ := Finset.exists_max_image Finset.univ
      (fun σ : Equiv.Perm ι => (η * matchingProduct b A σ).re) Finset.univ_nonempty
    let V := Equiv.Perm.permMatrix ℂ σ.symm
    have hdiag : diagonal b + V * diagonal A * Vᴴ = diagonal (b + A ∘ σ.symm) := by
      dsimp only [V]
      rw [permMatrix_conjugates, Matrix.submatrix_diagonal_equiv, Matrix.diagonal_add] <;> rfl
    have hvalue : determinantValue b A V = matchingProduct b A σ := by
      rw [determinantValue, hdiag, Matrix.det_diagonal]
      simpa only [Pi.add_apply, Function.comp_apply, Equiv.symm_symm] using
        (matchingProduct_inverse b A σ.symm).symm
    refine ⟨V, isUnitary_permMatrix σ.symm, ?_, ?_⟩
    · rw [hdiag]
      exact (by simpa only [Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one] using
        (isStarNormal_unitary_diagonalization (b + A ∘ σ.symm) (U := 1) isUnitary_one))
    · intro W hW
      have hW' : IsUnitary Wᴴ := ⟨by simpa only [Matrix.conjTranspose_conjTranspose] using hW.2,
        by simpa only [Matrix.conjTranspose_conjTranspose] using hW.1⟩
      have hHolds := (holds_swap_iff b A hW).mp (h a b Wᴴ hW')
      obtain ⟨τ, hτ⟩ := (holds_iff_directional b A W).mp hHolds η
      rw [hvalue]
      exact hτ.trans (hσ τ (Finset.mem_univ τ))
  · intro h a b U hU
    let A (i : ι) : ℂ := a i
    have hU' : IsUnitary Uᴴ := ⟨by simpa only [Matrix.conjTranspose_conjTranspose] using hU.2,
      by simpa only [Matrix.conjTranspose_conjTranspose] using hU.1⟩
    apply (holds_swap_iff A b hU).mp
    apply (holds_iff_directional b A Uᴴ).mpr
    intro η
    obtain ⟨V, hV, hn, hmax⟩ := h a b η
    obtain ⟨σ, hσ⟩ := (holds_iff_directional b A V).mp
      (holds_of_normal_sum_with_hermitian_right a b V hV hn) η
    exact ⟨σ, (hmax Uᴴ hU').trans hσ⟩

/-- In the partner eigenbasis, the Hermitian part of the scaled inverse
commutes with the moving summand. Its entries and the entries after
multiplication by that summand satisfy a second equation for each pair of
partner labels. The equation allows both signs of the partner imaginary parts. -/
theorem hermitian_support_maximum_partner_pair_equation
    (b : ι → ℂ) (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (θ : ℂ)
    (hdet : (diagonal b + H).det ≠ 0)
    (hmax : ∀ V : Matrix ι ι ℂ, IsUnitary V →
      (θ * (diagonal b + V * H * Vᴴ).det).re ≤ (θ * (diagonal b + H).det).re) :
    let M := diagonal b + H
    let Z := (θ * M.det) • M⁻¹
    let X := Z + Zᴴ
    Commute H X ∧ ∀ i j,
      ((b i - star (b i)) - (b j - star (b j))) * (H * X) i j =
        (star (b i) * b j - b i * star (b j)) * X i j := by
  intro M Z X
  let D := diagonal b
  let η := θ * M.det
  have hstat := support_maximum_inverse_commutator D H θ hdet hmax
  change ((η • (H * M⁻¹ - M⁻¹ * H)) : Matrix ι ι ℂ)ᴴ =
    η • (H * M⁻¹ - M⁻¹ * H) at hstat
  have hcomm : Commute H X := by
    have he : (H * Z - Z * H)ᴴ = H * Z - Z * H := by
      simpa only [Z, Matrix.mul_smul, Matrix.smul_mul, ← smul_sub] using hstat
    have he' : Zᴴ * H - H * Zᴴ = H * Z - Z * H := by
      simpa only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hH.eq] using he
    change H * (Z + Zᴴ) = (Z + Zᴴ) * H
    simp only [Matrix.mul_add, Matrix.add_mul]
    calc
      H * Z + H * Zᴴ = (H * Z - Z * H) + (Z * H + H * Zᴴ) := by abel
      _ = Z * H + Zᴴ * H := by rw [← he']; abel
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.mpr hdet
  have hMZ : M * Z = η • (1 : Matrix ι ι ℂ) := by
    change M * (η • M⁻¹) = _
    rw [Matrix.mul_smul, M.mul_nonsing_inv hunit]
  have hZM : Z * M = η • (1 : Matrix ι ι ℂ) := by
    change (η • M⁻¹) * M = _
    rw [Matrix.smul_mul, M.nonsing_inv_mul hunit]
  have hZstarMstar : Zᴴ * Mᴴ = star η • (1 : Matrix ι ι ℂ) := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
      using congrArg Matrix.conjTranspose hMZ
  have hMstarZstar : Mᴴ * Zᴴ = star η • (1 : Matrix ι ι ℂ) := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
      using congrArg Matrix.conjTranspose hZM
  have hbalance : M * X * Mᴴ = Mᴴ * X * M := by
    calc
      M * X * Mᴴ = η • Mᴴ + star η • M := by
        rw [show X = Z + Zᴴ from rfl, Matrix.mul_add, Matrix.add_mul, hMZ,
          Matrix.mul_assoc M Zᴴ Mᴴ, hZstarMstar]
        simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
      _ = Mᴴ * X * M := by
        rw [show X = Z + Zᴴ from rfl, Matrix.mul_add, Matrix.add_mul,
          Matrix.mul_assoc Mᴴ Z M, hZM, hMstarZstar]
        simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  have hidentity : M * X * Mᴴ - Mᴴ * X * M =
      (D - Dᴴ) * (H * X) - (H * X) * (D - Dᴴ) -
        (Dᴴ * X * D - D * X * Dᴴ) := by
    change (D + H) * X * (D + H)ᴴ - (D + H)ᴴ * X * (D + H) = _
    simp only [Matrix.conjTranspose_add, hH.eq, Matrix.add_mul, Matrix.mul_add,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, ← hcomm.eq]
    abel
  have hmatrix : (D - Dᴴ) * (H * X) - (H * X) * (D - Dᴴ) =
      Dᴴ * X * D - D * X * Dᴴ := by
    apply sub_eq_zero.mp
    rw [← hidentity, hbalance, sub_self]
  refine ⟨hcomm, fun i j => ?_⟩
  have hd : D - Dᴴ = diagonal (fun k => b k - star (b k)) := by
    dsimp only [D]
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_sub] <;> rfl
  have he := congrArg (fun K : Matrix ι ι ℂ => K i j) hmatrix
  rw [hd] at he
  simp only [D, Matrix.sub_apply, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul,
    Matrix.mul_diagonal, Pi.star_apply] at he
  linear_combination he

end MOC
