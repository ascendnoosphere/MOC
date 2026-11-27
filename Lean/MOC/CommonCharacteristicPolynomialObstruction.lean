import MOC.ContactCensus
import MOC.Reformulations.SecondCoefficient
import MOC.Support
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-! An exact order-four counterexample to a common law for all coefficients.
The spectra in the proof map are multiplied by `490000` so that the
matrix sum and the matching sums have Gaussian integer entries. -/

open BigOperators Matrix Polynomial

namespace MOC.CommonCharacteristicPolynomialObstruction

open MOC.Reformulations.CStar (signedCoefficient)

private def affineProductCoefficient {R : Type*} [CommRing R]
    (u v : Fin 4 → R) (k : ℕ) : R :=
  ∑ S ∈ (Finset.univ : Finset (Fin 4)).powersetCard k,
    (∏ j ∈ S, v j) * ∏ j ∈ Sᶜ, u j

private theorem coeff_affineProduct {R : Type*} [CommRing R]
    (u v : Fin 4 → R) (k : ℕ) :
    (∏ j, (C (v j) * X + C (u j))).coeff k = affineProductCoefficient u v k := by
  rw [Fintype.prod_add, Polynomial.finset_sum_coeff, affineProductCoefficient,
    Finset.powersetCard_eq_filter, Finset.powerset_univ, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro S _
  rw [Finset.prod_mul_distrib, Finset.prod_const, ← map_prod C, ← map_prod C,
    mul_right_comm _ (X ^ S.card), ← map_mul, Polynomial.coeff_C_mul_X_pow]
  by_cases h : S.card = k
  · simp [h]
  · simp only [h, Ne.symm h, if_false]

private def integerCoefficient (M : Matrix (Fin 4) (Fin 4) GaussianInt) (k : ℕ) : GaussianInt :=
  ∑ p : Fin 24, ((Equiv.Perm.sign (fourPerm p) : ℤ) : GaussianInt) *
    affineProductCoefficient (fun j => -M (fourPerm p j) j)
      (fun j => if fourPerm p j = j then 1 else 0) k

private theorem integerCoefficient_eq (M : Matrix (Fin 4) (Fin 4) GaussianInt) (k : ℕ) :
    M.charpoly.coeff k = integerCoefficient M k := by
  have hmatrix : M.charmatrix = Matrix.of fun i j =>
      C (if i = j then 1 else 0) * X + C (-M i j) := by
    ext i j : 1
    by_cases h : i = j
    · subst j
      simp [Matrix.charmatrix_apply, Matrix.diagonal_apply, sub_eq_add_neg]
    · simp [Matrix.charmatrix_apply, Matrix.diagonal_apply, h, sub_eq_add_neg]
  rw [Matrix.charpoly, hmatrix, Matrix.det_apply', Polynomial.finset_sum_coeff,
    ← Equiv.sum_comp fourPermEquiv, integerCoefficient]
  apply Finset.sum_congr rfl
  intro p _
  change (((Equiv.Perm.sign (fourPerm p) : ℤ) : GaussianInt[X]) *
      ∏ j, (C (if fourPerm p j = j then 1 else 0) * X + C (-M (fourPerm p j) j))).coeff k = _
  rw [← map_intCast (C : GaussianInt →+* GaussianInt[X]), Polynomial.coeff_C_mul,
    coeff_affineProduct]

private theorem integerCoefficient_diagonal (x : Fin 4 → GaussianInt) (k : ℕ) :
    integerCoefficient (diagonal x) k =
      affineProductCoefficient (fun j => -x j) (fun _ => 1) k := by
  have he : (diagonal x).charmatrix = diagonal (fun j => C (1 : GaussianInt) * X + C (-x j)) := by
    ext i j : 1
    by_cases h : i = j
    · subst j
      simp [Matrix.charmatrix_apply, Matrix.diagonal_apply, sub_eq_add_neg]
    · simp [Matrix.charmatrix_apply, Matrix.diagonal_apply, h]
  rw [← integerCoefficient_eq, Matrix.charpoly, he, Matrix.det_diagonal, coeff_affineProduct]

private def first : Fin 4 → GaussianInt :=
  ![⟨560, 17062⟩, ⟨-13061, -19835⟩, ⟨-13135, -19794⟩, ⟨25636, 22567⟩]

private def second : Fin 4 → GaussianInt :=
  ![⟨10341, 21575⟩, ⟨-15084, -9084⟩, ⟨-5643, -34138⟩, ⟨10386, 21647⟩]

private def mixer : Matrix (Fin 4) (Fin 4) GaussianInt :=
  !![1, 4, 4, 4; -4, 1, 4, -4; -4, -4, 1, 4; -4, 4, -4, 1]

private def numerator : Matrix (Fin 4) (Fin 4) GaussianInt :=
  (49 : GaussianInt) • diagonal first + mixer * diagonal second * mixerᴴ

private def matched (σ : Equiv.Perm (Fin 4)) : Matrix (Fin 4) (Fin 4) GaussianInt :=
  diagonal fun j => 49 * (first (σ j) + second j)

private def matchingCoefficient (σ : Equiv.Perm (Fin 4)) (k : ℕ) : GaussianInt :=
  affineProductCoefficient (fun j => -(49 * (first (σ j) + second j))) (fun _ => 1) k

private theorem matchingCoefficient_eq (σ : Equiv.Perm (Fin 4)) (k : ℕ) :
    integerCoefficient (matched σ) k = matchingCoefficient σ k := by
  rw [matched, integerCoefficient_diagonal]
  rfl

private def actualCoefficient (k : Fin 4) : GaussianInt :=
  ![⟨-1781331011994057108299064, -3291195624120283048452248⟩,
    ⟨96849708314492560, -1294751408530744500⟩, ⟨1893027679942, -3087757106644⟩, 0] k

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem actualCoefficient_eq (k : Fin 4) :
    integerCoefficient numerator k.val = actualCoefficient k := by
  exact (by decide +kernel : ∀ k : Fin 4, integerCoefficient numerator k.val = actualCoefficient k) k

private def direction (k : Fin 3) : GaussianInt :=
  ![⟨-24243, -13124⟩, ⟨11115, -829⟩, ⟨4970, -2858⟩] k * (490000 : GaussianInt) ^ k.val

private def integerScore (M : Matrix (Fin 4) (Fin 4) GaussianInt) : ℤ :=
  (∑ k : Fin 3, direction k * integerCoefficient M k.val).re

private theorem mixer_gram : mixerᴴ * mixer = (49 : GaussianInt) • 1 := by
  have h : ∀ i j : Fin 4, (mixerᴴ * mixer) i j =
      ((49 : GaussianInt) • (1 : Matrix (Fin 4) (Fin 4) GaussianInt)) i j := by
    decide +kernel
  exact Matrix.ext h

private theorem numerator_score : integerScore numerator = 132800207858112018217905800 := by
  have hk (j : Fin 3) : integerCoefficient numerator j.val = actualCoefficient (Fin.castSucc j) :=
    actualCoefficient_eq (Fin.castSucc j)
  rw [integerScore]
  simp only [hk]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
private theorem matching_score_bound (σ : Equiv.Perm (Fin 4)) :
    integerScore (matched σ) ≤ 99657478674686397294013345 := by
  obtain ⟨p, rfl⟩ := fourPerm_surjective σ
  rw [integerScore]
  simp only [matchingCoefficient_eq]
  exact (by decide +kernel : ∀ p : Fin 24,
    (∑ k : Fin 3, direction k * matchingCoefficient (fourPerm p) k.val).re ≤
      99657478674686397294013345) p

private def triangleVertex (j : Fin 3) : Equiv.Perm (Fin 4) :=
  (fourPerm (![0, 1, 3] j)).symm

private def triangleDenominator (k : Fin 3) : ℕ :=
  ![313991694742009651922360972378881809, 2465565567340330462865515413,
    6259541654842597359] k

private def triangleNumerator (k j : Fin 3) : ℕ :=
  (![![44219154038390145860449619529952837, 244122071048917971683949652921293940,
      25650469654701534377961699927635032],
     ![1637075544162980912452845813, 791066949198584469666585760,
      37423073978765080746083840],
     ![588515664231890255, 5449235618971190496, 221790371639516608]] k) j

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
private theorem triangle_identity (k : Fin 3) :
    ∑ j : Fin 3, (triangleNumerator k j : GaussianInt) *
      integerCoefficient (matched (triangleVertex j)) k.val =
        (triangleDenominator k : GaussianInt) * integerCoefficient numerator k.val := by
  have hk : integerCoefficient numerator k.val = actualCoefficient (Fin.castSucc k) :=
    actualCoefficient_eq (Fin.castSucc k)
  simp only [matchingCoefficient_eq, hk]
  exact (by decide +kernel : ∀ k : Fin 3,
    ∑ j : Fin 3, (triangleNumerator k j : GaussianInt) *
      matchingCoefficient (triangleVertex j) k.val =
        (triangleDenominator k : GaussianInt) * actualCoefficient (Fin.castSucc k)) k

set_option maxRecDepth 100000 in
private theorem trace_coefficient_identity :
    integerCoefficient numerator 3 = integerCoefficient (matched (triangleVertex 0)) 3 := by
  rw [show integerCoefficient numerator 3 = actualCoefficient 3 from actualCoefficient_eq 3,
    matchingCoefficient_eq]
  decide +kernel

noncomputable section

private abbrev g : GaussianInt →+* ℂ := GaussianInt.toComplex

private def a (i : Fin 4) : ℂ := 49 * g (first i)
private def b (i : Fin 4) : ℂ := 49 * g (second i)
private def W : Matrix (Fin 4) (Fin 4) ℂ := mixer.map g
private def U : Matrix (Fin 4) (Fin 4) ℂ := (7 : ℂ)⁻¹ • W

private theorem unitary_U : IsUnitary U := by
  have hW : Wᴴ * W = (49 : ℂ) • 1 := by
    have hm := congrArg (fun M : Matrix (Fin 4) (Fin 4) GaussianInt => M.map g) mixer_gram
    have hstar := Matrix.conjTranspose_map (A := mixer) g GaussianInt.toComplex_star
    simpa only [W, Matrix.map_mul, hstar, Matrix.map_smul' g _ _ (map_mul g), map_ofNat,
      Matrix.map_one g (map_zero g) (map_one g)] using hm
  have hr : star ((7 : ℂ)⁻¹) = (7 : ℂ)⁻¹ := by norm_num [Complex.star_def]
  have h : Uᴴ * U = 1 := by
    rw [U, Matrix.conjTranspose_smul, hr, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      hW, smul_smul]
    norm_num
  exact ⟨Matrix.mul_eq_one_comm.mp h, h⟩

private theorem U_im (i j : Fin 4) : (U i j).im = 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [U, W, mixer, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
      GaussianInt.toComplex_def₂, Complex.mul_im, Matrix.cons_val]

private theorem numerator_map : numerator.map g = diagonal a + U * diagonal b * Uᴴ := by
  have hU : W = (7 : ℂ) • U := by rw [U, smul_smul]; norm_num
  have hr : star (7 : ℂ) = 7 := by norm_num [Complex.star_def]
  have hstar := Matrix.conjTranspose_map (A := mixer) g GaussianInt.toComplex_star
  simp only [numerator, Matrix.map_add g (map_add g), Matrix.map_mul,
    Matrix.diagonal_map (map_zero g), hstar, Matrix.map_smul' g _ _ (map_mul g), map_ofNat]
  change (49 : ℂ) • diagonal (g ∘ first) + W * diagonal (g ∘ second) * Wᴴ = _
  have ha : (49 : ℂ) • diagonal (g ∘ first) = diagonal a := by
    rw [← Matrix.diagonal_smul]
    rfl
  have hb : (49 : ℂ) • diagonal (g ∘ second) = diagonal b := by
    rw [← Matrix.diagonal_smul]
    rfl
  rw [ha, ← hb, hU, Matrix.conjTranspose_smul, hr]
  congr 1
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  norm_num

private theorem matched_map (σ : Equiv.Perm (Fin 4)) :
    (matched σ).map g = diagonal fun j => a (σ j) + b j := by
  rw [matched, Matrix.diagonal_map (map_zero g)]
  apply congrArg Matrix.diagonal
  funext j
  change g (49 * (first (σ j) + second j)) = _
  simp only [map_mul, map_add, map_ofNat, a, b, mul_add]

private theorem coeff_map (M : Matrix (Fin 4) (Fin 4) GaussianInt) (k : ℕ) :
    (M.map g).charpoly.coeff k = g (integerCoefficient M k) := by
  rw [Matrix.charpoly_map, Polynomial.coeff_map, integerCoefficient_eq]

private def score : ℂ[X] →ₗ[ℝ] ℝ :=
  Complex.reLm.comp (∑ k : Fin 3, signedCoefficient (g (direction k)) k.val)

private theorem score_map (M : Matrix (Fin 4) (Fin 4) GaussianInt) :
    score (M.map g).charpoly = (integerScore M : ℝ) := by
  simp only [score, LinearMap.comp_apply, LinearMap.sum_apply,
    signedCoefficient, LinearMap.coe_mk, AddHom.coe_mk, coeff_map,
    ← map_mul, ← map_sum]
  change (g (∑ k : Fin 3, direction k * integerCoefficient M k.val)).re = _
  rw [← GaussianInt.to_real_re, integerScore]

private theorem not_mem_polynomial_hull :
    (diagonal a + U * diagonal b * Uᴴ).charpoly ∉
      convexHull ℝ (Set.range fun σ : Equiv.Perm (Fin 4) =>
        (diagonal fun j => a (σ j) + b j).charpoly) := by
  intro hh
  let C := {p : ℂ[X] | score p ≤ (99657478674686397294013345 : ℝ)}
  have hsub : Set.range (fun σ : Equiv.Perm (Fin 4) =>
      (diagonal fun j => a (σ j) + b j).charpoly) ⊆ C := by
    rintro _ ⟨σ, rfl⟩
    change score (diagonal fun j => a (σ j) + b j).charpoly ≤ _
    rw [← matched_map σ, score_map]
    exact_mod_cast matching_score_bound σ
  have hle := convexHull_min hsub (convex_halfSpace_le score.isLinear _) hh
  change score _ ≤ (99657478674686397294013345 : ℝ) at hle
  rw [← numerator_map, score_map, numerator_score] at hle
  norm_num at hle

private theorem mem_coefficient_hull (k : ℕ) :
    (diagonal a + U * diagonal b * Uᴴ).charpoly.coeff k ∈
      convexHull ℝ (Set.range fun σ : Equiv.Perm (Fin 4) =>
        (diagonal fun j => a (σ j) + b j).charpoly.coeff k) := by
  by_cases hk : k < 3
  · let t : Fin 3 := ⟨k, hk⟩
    let w (j : Fin 3) : ℝ := (triangleNumerator t j : ℝ) / triangleDenominator t
    have hd : 0 < triangleDenominator t := by
      exact (by decide +kernel : ∀ t : Fin 3, 0 < triangleDenominator t) t
    have hsum : ∑ j : Fin 3, triangleNumerator t j = triangleDenominator t := by
      exact (by decide +kernel : ∀ t : Fin 3,
        ∑ j : Fin 3, triangleNumerator t j = triangleDenominator t) t
    have hw : ∑ j, w j = 1 := by
      dsimp only [w]
      rw [← Finset.sum_div, ← Nat.cast_sum, hsum, div_self (by exact_mod_cast hd.ne')]
    refine mem_convexHull_of_exists_fintype w
      (fun j => (diagonal fun i => a (triangleVertex j i) + b i).charpoly.coeff k)
      (fun j => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hw
      (fun j => ⟨triangleVertex j, rfl⟩) ?_
    simp only [← matched_map, ← numerator_map, coeff_map, Complex.real_smul,
      w, Complex.ofReal_div, Complex.ofReal_natCast]
    have h := congrArg g (triangle_identity t)
    simp only [map_sum, map_mul, map_natCast, t] at h
    have hdenom : (triangleDenominator t : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    rw [← mul_right_inj' hdenom, Finset.mul_sum, ← h]
    apply Finset.sum_congr rfl
    intro j _
    change (triangleDenominator t : ℂ) * ((triangleNumerator t j : ℂ) /
      (triangleDenominator t : ℂ) * _) = _
    rw [← mul_assoc, mul_comm (triangleDenominator t : ℂ), div_mul_cancel₀ _ hdenom]
  · apply subset_convexHull ℝ _
    refine ⟨triangleVertex 0, ?_⟩
    dsimp only
    rw [← matched_map, ← numerator_map]
    by_cases h3 : k = 3
    · subst k
      rw [coeff_map, coeff_map, trace_coefficient_identity]
    · by_cases h4 : k = 4
      · subst k
        have hmonic (M : Matrix (Fin 4) (Fin 4) ℂ) : M.charpoly.coeff 4 = 1 := by
          have h := M.charpoly_monic
          rw [Polynomial.Monic, Polynomial.leadingCoeff, Matrix.charpoly_natDegree_eq_dim,
            Fintype.card_fin] at h
          exact h
        rw [hmonic, hmonic]
      · have hgt : 4 < k := by omega
        have hz (M : Matrix (Fin 4) (Fin 4) ℂ) : M.charpoly.coeff k = 0 := by
          apply Polynomial.coeff_eq_zero_of_natDegree_lt
          simpa only [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] using hgt
        rw [hz, hz]

/-- A real orthogonal change of basis separates the full characteristic
polynomial from the matching hull, though every coefficient is in its own
scalar matching hull. -/
theorem exists_orderFour_coefficient_hulls_without_common_law :
    ∃ (a b : Fin 4 → ℂ) (U : Matrix (Fin 4) (Fin 4) ℂ),
      IsUnitary U ∧ (∀ i j, (U i j).im = 0) ∧
      (∀ k, (diagonal a + U * diagonal b * Uᴴ).charpoly.coeff k ∈
        convexHull ℝ (Set.range fun σ : Equiv.Perm (Fin 4) =>
          (diagonal fun j => a (σ j) + b j).charpoly.coeff k)) ∧
      (diagonal a + U * diagonal b * Uᴴ).charpoly ∉
        convexHull ℝ (Set.range fun σ : Equiv.Perm (Fin 4) =>
          (diagonal fun j => a (σ j) + b j).charpoly) :=
  ⟨a, b, U, unitary_U, U_im, mem_coefficient_hull, not_mem_polynomial_hull⟩

end

end MOC.CommonCharacteristicPolynomialObstruction
