import MOC.FourCircleLineCommonWeights

/-! An integer separating functional for the eight corner evaluations of
three free diagonal entries. The fixed mixer is a product of three reflections. -/

open BigOperators Matrix

namespace MOC.ThreeFreeEigenvalueObstruction

noncomputable section

private def reflectionProduct : Matrix (Fin 4) (Fin 4) GaussianInt :=
  !![-1252, 1683, 162, 1218; 1161, 748, -1956, 420;
     -540, 1122, -334, -2061; 1644, 1122, 1395, -46]

private def integerReflection (v : Fin 4 → ℤ) : Matrix (Fin 4) (Fin 4) ℤ :=
  Matrix.of fun i j => (if i = j then ∑ k, v k ^ 2 else 0) - 2*v i*v j

/-- Clearing denominators verifies the three Householder factors in the given order. -/
theorem reflection_factorization :
    integerReflection ![3,-3,2,2] * integerReflection ![-3,0,-2,2] *
      integerReflection ![-2,0,3,3] =
      (4 : ℤ) • (!![-1252, 1683, 162, 1218; 1161, 748, -1956, 420;
        -540, 1122, -334, -2061; 1644, 1122, 1395, -46] :
          Matrix (Fin 4) (Fin 4) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide +kernel

def threeFreeMixer : Matrix (Fin 4) (Fin 4) ℂ :=
  (1 / 2431 : ℂ) • reflectionProduct.map GaussianInt.toComplex

theorem isUnitary_threeFreeMixer : IsUnitary threeFreeMixer := by
  let g := GaussianInt.toComplex
  have hInt : reflectionProduct * reflectionProductᴴ =
      (5909761 : GaussianInt) • (1 : Matrix (Fin 4) (Fin 4) GaussianInt) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  have hG := congrArg (fun M : Matrix (Fin 4) (Fin 4) GaussianInt => M.map g) hInt
  have hstar := Matrix.conjTranspose_map (A := reflectionProduct) g GaussianInt.toComplex_star
  simp only [Matrix.map_mul, hstar, Matrix.map_smul' g _ _ (map_mul g), map_ofNat,
    Matrix.map_one g (map_zero g) (map_one g)] at hG
  have hU : threeFreeMixer * threeFreeMixerᴴ = 1 := by
    unfold threeFreeMixer
    change ((1 / 2431 : ℂ) • reflectionProduct.map g) *
      ((1 / 2431 : ℂ) • reflectionProduct.map g)ᴴ = 1
    simp only [Matrix.conjTranspose_smul, star_div₀, star_one, star_ofNat, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, hG]
    norm_num [smul_smul]
  exact ⟨hU, Matrix.mul_eq_one_comm.mp hU⟩


private def obstructionSpectrumInt : Fin 4 → GaussianInt :=
  ![⟨3, 3⟩, ⟨-2, 1⟩, ⟨-3, -2⟩, ⟨0, -2⟩]

def fixedSpectrum : Fin 4 → ℂ := GaussianInt.toComplex ∘ obstructionSpectrumInt

private def obstructionCornerInt (q : Fin 8) : Fin 4 → GaussianInt :=
  ![⟨0, -2⟩, if q.val / 4 % 2 = 1 then 1 else 0,
    if q.val / 2 % 2 = 1 then 1 else 0, if q.val % 2 = 1 then 1 else 0]

def corner (q : Fin 8) : Fin 4 → ℂ := GaussianInt.toComplex ∘ obstructionCornerInt q

private def obstructionScaledSum (q : Fin 8) : Matrix (Fin 4) (Fin 4) GaussianInt :=
  (5909761 : GaussianInt) • diagonal (obstructionCornerInt q) +
    reflectionProduct * diagonal obstructionSpectrumInt * reflectionProductᴴ

private def obstructionValueInt : Fin 8 → GaussianInt :=
  ![⟨384011914,-146523718⟩, ⟨359051220,-135092780⟩, ⟨319942689,-32537957⟩,
    ⟨288401404,-16940576⟩, ⟨345866224,-98765582⟩, ⟨326534528,-78875004⟩,
    ⟨273105467,-2080230⟩, ⟨246151982,14672734⟩]

/-- Boolean finite differences convert the coefficient separator to these corner directions. -/
private def obstructionDirection : Fin 8 → GaussianInt :=
  ![⟨-135,113⟩, ⟨192,-135⟩, ⟨-4,-72⟩, ⟨0,112⟩, ⟨104,-40⟩, ⟨-152,23⟩, 33, 0]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
private theorem obstructionScaledDet (q : Fin 8) :
    (obstructionScaledSum q).det = (5909761 : GaussianInt)^3 * obstructionValueInt q := by
  rw [Matrix.det_succ_column_zero]
  simp only [Matrix.det_fin_three, Fin.sum_univ_four]
  fin_cases q <;> decide +kernel

private theorem obstructionCorner_determinant (q : Fin 8) :
    determinantValue (corner q) fixedSpectrum threeFreeMixer = GaussianInt.toComplex (obstructionValueInt q) / 5909761 := by
  let g := GaussianInt.toComplex
  let U := threeFreeMixer
  let D := diagonal (corner q) + U * diagonal fixedSpectrum * Uᴴ
  have hmap : reflectionProduct.map g = (2431 : ℂ) • U := by
    simp [U, threeFreeMixer, smul_smul] <;> norm_num
  have hstar := Matrix.conjTranspose_map (A := reflectionProduct) g GaussianInt.toComplex_star
  have hsum : (obstructionScaledSum q).map g = (5909761 : ℂ) • D := by
    change (obstructionScaledSum q).map g = (5909761 : ℂ) •
      (diagonal (fun i => g (obstructionCornerInt q i)) +
        U * diagonal (fun i => g (obstructionSpectrumInt i)) * Uᴴ)
    simp only [obstructionScaledSum, Matrix.map_add g (map_add g),
      Matrix.map_smul' g _ _ (map_mul g), map_ofNat, Matrix.map_mul,
      Matrix.diagonal_map (map_zero g), hstar, hmap, Matrix.conjTranspose_smul,
      star_ofNat, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_add]
    norm_num
  have he := congrArg g (obstructionScaledDet q)
  simp only [RingHom.map_det, RingHom.mapMatrix_apply, hsum, Matrix.det_smul,
    Fintype.card_fin, map_mul, map_pow, map_ofNat] at he
  have hd : (5909761 : ℂ) ≠ 0 := by norm_num
  have hdet : D.det = g (obstructionValueInt q) / 5909761 := by
    apply (eq_div_iff hd).mpr
    apply mul_left_cancel₀ (pow_ne_zero 3 hd)
    linear_combination he
  exact hdet

private def obstructionVertex (σ : Equiv.Perm (Fin 4)) (q : Fin 8) : GaussianInt :=
  ∏ j, (obstructionCornerInt q (σ j) + obstructionSpectrumInt j)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
private theorem obstructionVertex_bound (σ : Equiv.Perm (Fin 4)) :
    1170 ≤ (∑ q, (obstructionDirection q * obstructionVertex σ q).re) := by
  obtain ⟨i, rfl⟩ := fourPerm_surjective σ
  have h : ∀ i : Fin 24, 1170 ≤ (∑ q, (obstructionDirection q * obstructionVertex (fourPerm i) q).re) := by
    decide +kernel
  exact h i

private theorem obstructionNumerator_score :
    (∑ q, (obstructionDirection q * obstructionValueInt q).re) = 6903542799 := by
  decide +kernel

/-- No probability law represents the eight corners of this trilinear pencil. -/
theorem no_common_law_at_eight_corners :
    ¬ ∃ w : Equiv.Perm (Fin 4) → ℝ, (∀ σ, 0 ≤ w σ) ∧ (∑ σ, w σ = 1) ∧
      ∀ q : Fin 8, weightedMatchingValue (corner q) fixedSpectrum w =
        determinantValue (corner q) fixedSpectrum threeFreeMixer := by
  classical
  rintro ⟨w, hw, hs, he⟩
  let g := GaussianInt.toComplex
  have hc (q : Fin 8) :
      (∑ σ, w σ * ((obstructionDirection q * obstructionVertex σ q).re : ℝ)) =
        ((obstructionDirection q * obstructionValueInt q).re : ℝ) / 5909761 := by
    have heq := (he q).trans (obstructionCorner_determinant q)
    have hp (σ : Equiv.Perm (Fin 4)) :
        matchingProduct (corner q) fixedSpectrum σ = g (obstructionVertex σ q) := by
      simp only [g, obstructionVertex, matchingProduct, fixedSpectrum,
        corner, Function.comp_apply, map_prod, map_add]
    simp only [weightedMatchingValue, hp] at heq
    have h := congrArg (fun z : ℂ => (g (obstructionDirection q) * z).re) heq
    change (g (obstructionDirection q) * (∑ σ, (w σ : ℂ) * g (obstructionVertex σ q))).re =
      (g (obstructionDirection q) * (g (obstructionValueInt q) / 5909761)).re at h
    rw [Finset.mul_sum, Complex.re_sum, ← mul_div_assoc, ← map_mul] at h
    have hterm (σ : Equiv.Perm (Fin 4)) :
        (g (obstructionDirection q) * ((w σ : ℂ) * g (obstructionVertex σ q))).re =
          w σ * ((obstructionDirection q * obstructionVertex σ q).re : ℝ) := by
      rw [mul_left_comm, Complex.re_ofReal_mul, ← map_mul, ← GaussianInt.to_real_re]
    simp_rw [hterm] at h
    rw [show (5909761 : ℂ) = ((5909761 : ℝ) : ℂ) by norm_num, Complex.div_ofReal_re,
      ← GaussianInt.to_real_re] at h
    exact h
  have hbound : (1170 : ℝ) ≤ ∑ σ, w σ * ∑ q, ((obstructionDirection q * obstructionVertex σ q).re : ℝ) := calc
    _ = ∑ σ, w σ * (1170 : ℝ) := by rw [← Finset.sum_mul, hs, one_mul]
    _ ≤ _ := Finset.sum_le_sum fun σ _ =>
      mul_le_mul_of_nonneg_left (by exact_mod_cast obstructionVertex_bound σ) (hw σ)
  simp_rw [Finset.mul_sum] at hbound
  rw [Finset.sum_comm] at hbound
  simp_rw [hc, ← Finset.sum_div, ← Int.cast_sum, obstructionNumerator_score] at hbound
  norm_num at hbound

/-- The first spectral list has the form (-2i,x,y,z). -/
theorem no_common_law_three_free_entries :
    ¬ ∃ w : Equiv.Perm (Fin 4) → ℝ, (∀ σ, 0 ≤ w σ) ∧ (∑ σ, w σ = 1) ∧
      ∀ x y z : ℂ, weightedMatchingValue ![-2 * Complex.I, x, y, z] fixedSpectrum w =
        determinantValue ![-2 * Complex.I, x, y, z] fixedSpectrum threeFreeMixer := by
  rintro ⟨w, hw, hs, h⟩
  apply no_common_law_at_eight_corners
  refine ⟨w, hw, hs, fun q => ?_⟩
  have hcorner : ![-2 * Complex.I, corner q 1, corner q 2, corner q 3] = corner q := by
    funext j
    fin_cases j <;> norm_num [corner, obstructionCornerInt, GaussianInt.toComplex_def',
      Complex.ext_iff, Complex.mul_re, Complex.mul_im]
  rw [← hcorner]
  exact h _ _ _

end

end MOC.ThreeFreeEigenvalueObstruction
