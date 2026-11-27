import MOC.CommonWeights
import MOC.FourMatchingMarginalObstructions
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-! Four corner evaluations obstruct common matching weights when one spectral
coordinate is free in each list. The integer matrices give orders four and five. -/

open BigOperators Matrix

namespace MOC.OppositeCoordinateObstruction

def fiveNumerator : Matrix (Fin 5) (Fin 5) GaussianInt :=
  !![33,444,-300,-320,0; -180,135,500,-300,0; 444,292,225,240,0;
     -400,300,0,375,0; 0,0,0,0,625]

private def firstFour (x : GaussianInt) : Fin 4 → GaussianInt :=
  ![x, ⟨-1,1⟩, ⟨1,-1⟩, ⟨2,-3⟩]

private def secondFour (y : GaussianInt) : Fin 4 → GaussianInt :=
  ![y, ⟨0,3⟩, ⟨3,-2⟩, ⟨-1,-3⟩]

private def firstFive (x : GaussianInt) : Fin 5 → GaussianInt :=
  ![x, ⟨-1,1⟩, ⟨1,-1⟩, ⟨2,-3⟩, ⟨1,-1⟩]

private def secondFive (y : GaussianInt) : Fin 5 → GaussianInt :=
  ![y, ⟨0,3⟩, ⟨3,-2⟩, ⟨-1,-3⟩, ⟨3,-2⟩]

private def xCorner : Fin 4 → GaussianInt := ![0,1,0,1]
private def yCorner : Fin 4 → GaussianInt := ![0,0,1,1]

private def fourValue : Fin 4 → GaussianInt :=
  ![⟨-866272,-2822112⟩, ⟨-1546542,-3063945⟩, ⟨617682,-4088361⟩, ⟨-97452,-4822434⟩]

private def fiveValue (q : Fin 4) : GaussianInt := (⟨4,-3⟩ : GaussianInt) * fourValue q

private def fourDirection : Fin 4 → GaussianInt :=
  ![⟨1795,5000⟩, ⟨-2571,-3167⟩, ⟨-2096,-3929⟩, ⟨2445,2155⟩]

private def fiveDirection : Fin 4 → GaussianInt :=
  ![⟨-3080,10000⟩, ⟨-308,-8028⟩, ⟨1341,-8668⟩, ⟨1305,6285⟩]

private def entryMatrix {n : ℕ} (V : Matrix (Fin n) (Fin n) GaussianInt)
    (a b : Fin n → GaussianInt) : Matrix (Fin n) (Fin n) GaussianInt :=
  Matrix.of fun i j => (a i + b j) * V i j

private def vertex {n : ℕ} (a b : GaussianInt → Fin n → GaussianInt)
    (f : Fin n → Fin n) (q : Fin 4) : GaussianInt :=
  ∏ j, (a (xCorner q) (f j) + b (yCorner q) j)

private def score (direction values : Fin 4 → GaussianInt) : ℤ :=
  ∑ q, (direction q * values q).re

noncomputable section

def normalizedMixer {n : ℕ} (V : Matrix (Fin n) (Fin n) GaussianInt) :
    Matrix (Fin n) (Fin n) ℂ := (625 : ℂ)⁻¹ • V.map GaussianInt.toComplex

private theorem unitary_of_gram {n : ℕ} (V : Matrix (Fin n) (Fin n) GaussianInt)
    (hg : Vᴴ * V = (390625 : GaussianInt) • 1) : IsUnitary (normalizedMixer V) := by
  let g := GaussianInt.toComplex
  have h := congrArg (fun M : Matrix (Fin n) (Fin n) GaussianInt => M.map g) hg
  have hs := Matrix.conjTranspose_map (A := V) g GaussianInt.toComplex_star
  simp only [Matrix.map_mul, hs, Matrix.map_smul' g _ _ (map_mul g), map_ofNat,
    Matrix.map_one g (map_zero g) (map_one g)] at h
  have hu : (normalizedMixer V)ᴴ * normalizedMixer V = 1 := by
    change ((625 : ℂ)⁻¹ • V.map g)ᴴ * ((625 : ℂ)⁻¹ • V.map g) = 1
    rw [Matrix.conjTranspose_smul, star_inv₀, star_ofNat, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, h, smul_smul]
    norm_num
  exact ⟨Matrix.mul_eq_one_comm.mp hu, hu⟩

theorem fiveNumerator_unitary : IsUnitary (normalizedMixer fiveNumerator) := by
  apply unitary_of_gram
  ext i j : 1
  fin_cases i <;> fin_cases j <;> decide +kernel

private theorem corner_value {n : ℕ} (V : Matrix (Fin n) (Fin n) GaussianInt)
    (hU : IsUnitary (normalizedMixer V)) (a b : Fin n → GaussianInt) (v : GaussianInt)
    (hc : 78125 * (entryMatrix V a b).det = v * V.det) :
    determinantValue (GaussianInt.toComplex ∘ a) (GaussianInt.toComplex ∘ b)
      (normalizedMixer V) = GaussianInt.toComplex v / 78125 := by
  let g := GaussianInt.toComplex
  let U := normalizedMixer V
  let D := diagonal (g ∘ a) + U * diagonal (g ∘ b) * Uᴴ
  have hs : V.map g = (625 : ℂ) • U := by
    simp [U, normalizedMixer, g, smul_smul]
  have hne : g V.det ≠ 0 := by
    rw [g.map_det, RingHom.mapMatrix_apply, hs, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (det_ne_zero_of_unitary hU)
  have hm : (entryMatrix V a b).map g = D * V.map g := by
    rw [hs]
    dsimp only [D]
    rw [Matrix.mul_smul, Matrix.add_mul, Matrix.mul_assoc (U * diagonal (g ∘ b)),
      hU.2, Matrix.mul_one]
    ext i j
    have hij : g (V i j) = (625 : ℂ) * U i j :=
      congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i j) hs
    simp only [entryMatrix, Matrix.map_apply, Matrix.of_apply, map_mul, map_add, hij,
      Matrix.smul_apply, smul_eq_mul, Matrix.add_apply, Matrix.diagonal_mul,
      Matrix.mul_diagonal, Function.comp_apply]
    ring
  have he := congrArg g hc
  have hdet : g (entryMatrix V a b).det = D.det * g V.det := by
    rw [g.map_det, RingHom.mapMatrix_apply, hm, Matrix.det_mul, g.map_det,
      RingHom.mapMatrix_apply]
  simp only [map_mul, map_ofNat, hdet] at he
  change D.det = g v / 78125
  apply (eq_div_iff (by norm_num : (78125 : ℂ) ≠ 0)).mpr
  apply mul_right_cancel₀ hne
  linear_combination he

private theorem no_corner_law {n : ℕ} (V : Matrix (Fin n) (Fin n) GaussianInt)
    (hU : IsUnitary (normalizedMixer V)) (a b : GaussianInt → Fin n → GaussianInt)
    (d v : Fin 4 → GaussianInt) (bound : ℤ)
    (hdet : ∀ q, 78125 * (entryMatrix V (a (xCorner q)) (b (yCorner q))).det = v q * V.det)
    (hb : ∀ σ : Equiv.Perm (Fin n), score d (vertex a b σ) ≤ bound)
    (hgap : 78125 * bound < score d v) :
    ¬ ∃ w : Equiv.Perm (Fin n) → ℝ, (∀ σ, 0 ≤ w σ) ∧ (∑ σ, w σ = 1) ∧
      ∀ q : Fin 4, weightedMatchingValue (GaussianInt.toComplex ∘ a (xCorner q))
        (GaussianInt.toComplex ∘ b (yCorner q)) w =
        determinantValue (GaussianInt.toComplex ∘ a (xCorner q))
          (GaussianInt.toComplex ∘ b (yCorner q)) (normalizedMixer V) := by
  classical
  rintro ⟨w, hw, hsum, hwdet⟩
  let g := GaussianInt.toComplex
  have hq (q : Fin 4) : (∑ σ, w σ * ((d q * vertex a b σ q).re : ℝ)) =
      ((d q * v q).re : ℝ) / 78125 := by
    have hh := (hwdet q).trans (corner_value V hU _ _ _ (hdet q))
    have hp (σ : Equiv.Perm (Fin n)) :
        matchingProduct (g ∘ a (xCorner q)) (g ∘ b (yCorner q)) σ = g (vertex a b σ q) := by
      simp only [vertex, matchingProduct, Function.comp_apply, map_prod, map_add]
    change (∑ σ, (w σ : ℂ) * matchingProduct (g ∘ a (xCorner q))
      (g ∘ b (yCorner q)) σ) = g (v q) / 78125 at hh
    simp only [hp] at hh
    have h := congrArg (fun z : ℂ => (g (d q) * z).re) hh
    change (g (d q) * (∑ σ, (w σ : ℂ) * g (vertex a b σ q))).re =
      (g (d q) * (g (v q) / 78125)).re at h
    rw [Finset.mul_sum, Complex.re_sum, ← mul_div_assoc, ← map_mul] at h
    have ht (σ : Equiv.Perm (Fin n)) :
        (g (d q) * ((w σ : ℂ) * g (vertex a b σ q))).re =
          w σ * ((d q * vertex a b σ q).re : ℝ) := by
      rw [mul_left_comm, Complex.re_ofReal_mul, ← map_mul, ← GaussianInt.to_real_re]
    simp_rw [ht] at h
    rw [show (78125 : ℂ) = ((78125 : ℝ) : ℂ) by norm_num, Complex.div_ofReal_re,
      ← GaussianInt.to_real_re] at h
    exact h
  have hbound : ∑ σ, w σ * ∑ q, ((d q * vertex a b σ q).re : ℝ) ≤ (bound : ℝ) := calc
    _ ≤ ∑ σ, w σ * (bound : ℝ) := Finset.sum_le_sum fun σ _ =>
      mul_le_mul_of_nonneg_left (by exact_mod_cast hb σ) (hw σ)
    _ = _ := by rw [← Finset.sum_mul, hsum, one_mul]
  simp_rw [Finset.mul_sum] at hbound
  rw [Finset.sum_comm] at hbound
  simp_rw [hq, ← Finset.sum_div, ← Int.cast_sum] at hbound
  change (score d v : ℝ) / 78125 ≤ bound at hbound
  have hg : (78125 : ℝ) * bound < score d v := by exact_mod_cast hgap
  linarith

/-- The first entry of each spectral list may vary independently. -/
def CommonOppositeCoordinateWeights {n : ℕ} [NeZero n]
    (a b : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ w : Equiv.Perm (Fin n) → ℝ, (∀ σ, 0 ≤ w σ) ∧ (∑ σ, w σ = 1) ∧
    ∀ x y : ℂ, weightedMatchingValue (Function.update a 0 x) (Function.update b 0 y) w =
      determinantValue (Function.update a 0 x) (Function.update b 0 y) U

set_option synthInstance.maxSize 4096 in
set_option maxHeartbeats 20000000 in
set_option maxRecDepth 100000 in
private theorem fourVertexBound (σ : Equiv.Perm (Fin 4)) :
    score fourDirection (vertex firstFour secondFour σ) ≤ (-4898 : ℤ) := by
  have h : ∀ i0 i1 i2 i3 : Fin 4, i0 ≠ i1 → i0 ≠ i2 → i0 ≠ i3 → i1 ≠ i2 → i1 ≠ i3 → i2 ≠ i3 →
      score fourDirection (vertex firstFour secondFour ![i0,i1,i2,i3]) ≤ (-4898 : ℤ) := by
    decide +kernel
  have hv : ![σ 0,σ 1,σ 2,σ 3] = (σ : Fin 4 → Fin 4) := by
    funext j
    fin_cases j <;> rfl
  rw [← hv]
  apply h (σ 0) (σ 1) (σ 2) (σ 3) <;> simp

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 100000 in
/-- Independent variation of opposite spectral coordinates fails in order four. -/
theorem no_common_opposite_coordinates_four :
    ¬ CommonOppositeCoordinateWeights (GaussianInt.toComplex ∘ firstFour 0)
      (GaussianInt.toComplex ∘ secondFour 0) fourMarginalMixer := by
  rintro ⟨w, hw, hs, hh⟩
  apply no_corner_law marginalMixerNumerator fourMarginalMixer_unitary firstFour secondFour
    fourDirection fourValue (-4898) (by
      intro q
      simp only [Matrix.det_succ_column_zero, Matrix.det_fin_three, Fin.sum_univ_four]
      fin_cases q <;> decide +kernel) fourVertexBound (by decide +kernel)
  refine ⟨w, hw, hs, fun q => ?_⟩
  have ha : Function.update (GaussianInt.toComplex ∘ firstFour 0) 0
      (GaussianInt.toComplex (xCorner q)) = GaussianInt.toComplex ∘ firstFour (xCorner q) := by
    funext j
    fin_cases j <;> simp [Function.update, firstFour]
  have hb : Function.update (GaussianInt.toComplex ∘ secondFour 0) 0
      (GaussianInt.toComplex (yCorner q)) = GaussianInt.toComplex ∘ secondFour (yCorner q) := by
    funext j
    fin_cases j <;> simp [Function.update, secondFour]
  simpa only [ha, hb] using hh (GaussianInt.toComplex (xCorner q)) (GaussianInt.toComplex (yCorner q))

set_option synthInstance.maxSize 4096 in
set_option maxHeartbeats 20000000 in
set_option maxRecDepth 100000 in
private theorem fiveVertexBound (σ : Equiv.Perm (Fin 5)) :
    score fiveDirection (vertex firstFive secondFive σ) ≤ (-48365 : ℤ) := by
  have h : ∀ i0 i1 i2 i3 i4 : Fin 5, i0 ≠ i1 → i0 ≠ i2 → i0 ≠ i3 → i0 ≠ i4 → i1 ≠ i2 → i1 ≠ i3 → i1 ≠ i4 → i2 ≠ i3 → i2 ≠ i4 → i3 ≠ i4 →
      score fiveDirection (vertex firstFive secondFive ![i0,i1,i2,i3,i4]) ≤ (-48365 : ℤ) := by
    intro i0 i1
    fin_cases i0 <;> fin_cases i1 <;> decide +kernel
  have hv : ![σ 0,σ 1,σ 2,σ 3,σ 4] = (σ : Fin 5 → Fin 5) := by
    funext j
    fin_cases j <;> rfl
  rw [← hv]
  apply h (σ 0) (σ 1) (σ 2) (σ 3) (σ 4) <;> simp

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 100000 in
/-- Independent variation of opposite spectral coordinates fails in order five. -/
theorem no_common_opposite_coordinates_five :
    ¬ CommonOppositeCoordinateWeights (GaussianInt.toComplex ∘ firstFive 0)
      (GaussianInt.toComplex ∘ secondFive 0) (normalizedMixer fiveNumerator) := by
  rintro ⟨w, hw, hs, hh⟩
  apply no_corner_law fiveNumerator fiveNumerator_unitary firstFive secondFive
    fiveDirection fiveValue (-48365) (by
      intro q
      simp only [Matrix.det_succ_column_zero, Matrix.det_fin_three, Fin.sum_univ_four]
      fin_cases q <;> decide +kernel) fiveVertexBound (by decide +kernel)
  refine ⟨w, hw, hs, fun q => ?_⟩
  have ha : Function.update (GaussianInt.toComplex ∘ firstFive 0) 0
      (GaussianInt.toComplex (xCorner q)) = GaussianInt.toComplex ∘ firstFive (xCorner q) := by
    funext j
    fin_cases j <;> simp [Function.update, firstFive]
  have hb : Function.update (GaussianInt.toComplex ∘ secondFive 0) 0
      (GaussianInt.toComplex (yCorner q)) = GaussianInt.toComplex ∘ secondFive (yCorner q) := by
    funext j
    fin_cases j <;> simp [Function.update, secondFive]
  simpa only [ha, hb] using hh (GaussianInt.toComplex (xCorner q)) (GaussianInt.toComplex (yCorner q))

end

end MOC.OppositeCoordinateObstruction
