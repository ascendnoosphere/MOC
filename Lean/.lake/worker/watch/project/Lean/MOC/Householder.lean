import MOC.Core
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.LinearCombination
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Topology.Instances.Matrix

/-! Exact determinant compression for rank-one unitary phase updates. The
Householder reflection is the phase `z = -1` (Drury, LAA 298, 1999). -/

open BigOperators Matrix

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The rank-one phase update in the direction of `v`. -/
def rankOnePhase (v : ι → ℂ) (z : ℂ) : Matrix ι ι ℂ :=
  1 + (z - 1) • vecMulVec v (star ∘ v)

theorem rankOnePhase_unitary (v : ι → ℂ) (z : ℂ)
    (hv : ∑ i, star (v i) * v i = 1) (hz : z * star z = 1) :
    IsUnitary (rankOnePhase v z) := by
  let P : Matrix ι ι ℂ := vecMulVec v (star ∘ v)
  have hPstar : Pᴴ = P := by
    ext i j
    simp only [P, Matrix.conjTranspose_apply, Matrix.vecMulVec_apply, Function.comp_apply,
      star_mul', star_star]
    ring
  have hPmul : P * P = P := by
    ext i j
    simp only [P, Matrix.mul_apply, Matrix.vecMulVec_apply, Function.comp_apply]
    calc
      _ = ∑ k, (v i * star (v j)) * (star (v k) * v k) :=
        Finset.sum_congr rfl fun k _ => by ring
      _ = _ := by rw [← Finset.mul_sum, hv, mul_one]
  have hstar : (rankOnePhase v z)ᴴ = 1 + (star z - 1) • P := by
    change (1 + (z - 1) • P)ᴴ = 1 + (star z - 1) • P
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.conjTranspose_smul,
      star_sub, star_one, hPstar]
  have hmul (x y : ℂ) (hxy : x * y = 1) :
      (1 + (x - 1) • P) * (1 + (y - 1) • P) = 1 := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
      Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul, hPmul]
    ext i j : 1
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    linear_combination P i j * hxy
  change rankOnePhase v z * (rankOnePhase v z)ᴴ = 1 ∧
    (rankOnePhase v z)ᴴ * rankOnePhase v z = 1
  rw [hstar]
  exact ⟨hmul z (star z) hz, hmul (star z) z (by rwa [mul_comm])⟩

theorem det_rankOnePhase (v : ι → ℂ) (z : ℂ)
    (hv : ∑ i, star (v i) * v i = 1) :
    (rankOnePhase v z).det = z := by
  let L : Matrix ι (Fin 1) ℂ := Matrix.of fun i _ => v i
  let R : Matrix (Fin 1) ι ℂ := Matrix.of fun _ j => star (v j)
  have hLR : L * R = vecMulVec v (star ∘ v) := by
    ext i j
    simp [L, R, Matrix.mul_apply, Matrix.vecMulVec_apply]
  have hRL : R * L = 1 := by
    ext i j
    have hij : i = j := Subsingleton.elim _ _
    subst j
    rw [Matrix.mul_apply, Matrix.one_apply_eq]
    exact hv
  rw [rankOnePhase, ← hLR, ← Matrix.smul_mul, Matrix.det_one_add_mul_comm,
    Matrix.mul_smul, hRL, Matrix.det_fin_one]
  simp [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]

/-- The two-by-two compression of the regular spectral determinant. Each
summand is a rank-one matrix scaled by the corresponding coordinate mass. -/
def rankOneSpectralCompression (a b v : ι → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun i j => ∑ k,
    (if i = 0 then 1 else b k) * (star (v k) * v k / (a k + b k)) *
      (if j = 0 then a k else 1)

omit [DecidableEq ι] in
theorem rankOneSpectralCompression_diagonal_sum (a b v : ι → ℂ)
    (hv : ∑ i, star (v i) * v i = 1) (hreg : ∀ i, a i + b i ≠ 0) :
    let N := rankOneSpectralCompression a b v
    N 0 0 + N 1 1 = 1 := by
  simp [rankOneSpectralCompression, ← Finset.sum_add_distrib]
  calc
    _ = ∑ i, star (v i) * v i :=
      Finset.sum_congr rfl fun i _ => by field_simp [hreg i] <;> ring
    _ = 1 := hv

/-- With nonzero identity matching factors, the determinant for a rank-one
phase update is its diagonal matching product times a two-by-two formula. -/
theorem determinantValue_rankOnePhase (a b v : ι → ℂ) (z : ℂ)
    (hv : ∑ i, star (v i) * v i = 1) (hz : z * star z = 1)
    (hreg : ∀ i, a i + b i ≠ 0) :
    determinantValue a b (rankOnePhase v z) =
      (∏ i, (a i + b i)) *
        (1 - (2 - z - star z) * (rankOneSpectralCompression a b v).det) := by
  let U := rankOnePhase v z
  let N := rankOneSpectralCompression a b v
  let X : Matrix ι (Fin 2) ℂ := Matrix.of fun i j =>
    (v i / (a i + b i)) * (if j = 0 then a i else 1)
  let Y : Matrix (Fin 2) ι ℂ := Matrix.of fun i j =>
    (if i = 0 then 1 else b j) * star (v j)
  have hYX : Y * X = N := by
    ext i j
    simp only [X, Y, N, rankOneSpectralCompression, Matrix.mul_apply, Matrix.of_apply]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hXY (i j : ι) :
      (a i + b i) * (X * Y) i j = (a i + b j) * (v i * star (v j)) := by
    simp [X, Y, Matrix.mul_apply, Fin.sum_univ_two]
    field_simp [hreg i]
    <;> ring
  have hU : IsUnitary U := rankOnePhase_unitary v z hv hz
  have hmat : (diagonal a + U * diagonal b * Uᴴ) * U =
      diagonal (fun i => a i + b i) * (1 + (z - 1) • (X * Y)) := by
    rw [Matrix.add_mul, Matrix.mul_assoc (U * diagonal b), hU.2, Matrix.mul_one]
    ext i j
    have hd : (a i + b j) * (1 : Matrix ι ι ℂ) i j =
        (a i + b i) * (1 : Matrix ι ι ℂ) i j := by
      by_cases hij : i = j
      · subst j
        rfl
      · simp [Matrix.one_apply_ne hij]
    simp only [Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, U, rankOnePhase,
      Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply, Function.comp_apply]
    calc
      _ = (a i + b j) * (1 : Matrix ι ι ℂ) i j +
          (z - 1) * ((a i + b j) * (v i * star (v j))) := by ring
      _ = _ := by rw [hd, ← hXY]; ring
  have hdet : determinantValue a b U * z =
      (∏ i, (a i + b i)) * (1 + (z - 1) • N).det := by
    have hUd : U.det = z := det_rankOnePhase v z hv
    calc
      determinantValue a b U * z = determinantValue a b U * U.det := by rw [hUd]
      _ = _ := by
        unfold determinantValue
        rw [← Matrix.det_mul, hmat, Matrix.det_mul, Matrix.det_diagonal]
        congr 1
        calc
          (1 + (z - 1) • (X * Y)).det = (1 + ((z - 1) • X) * Y).det := by
            rw [Matrix.smul_mul]
          _ = (1 + Y * ((z - 1) • X)).det := Matrix.det_one_add_mul_comm _ _
          _ = _ := by rw [Matrix.mul_smul, hYX]
  have htr : N 0 0 + N 1 1 = 1 :=
    rankOneSpectralCompression_diagonal_sum a b v hv hreg
  have hsmall : (1 + (z - 1) • N).det = z + (z - 1)^2 * N.det := by
    simp only [Matrix.det_fin_two, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
      Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), zero_add]
    linear_combination (z - 1) * htr
  have hphase : z + (z - 1)^2 * N.det = (1 - (2 - z - star z) * N.det) * z := by
    linear_combination -N.det * hz
  have hzn : z ≠ 0 := by
    intro h
    simp [h] at hz
  apply mul_right_cancel₀ hzn
  change determinantValue a b U * z = ((∏ i, (a i + b i)) *
    (1 - (2 - z - star z) * N.det)) * z
  rw [hdet, hsmall, hphase, mul_assoc]

private theorem phase_distance_sq (z : ℂ) (hz : z * star z = 1) :
    (Complex.normSq (z - 1) : ℂ) = 2 - z - star z := by
  rw [Complex.normSq_eq_conj_mul_self]
  change star (z - 1) * (z - 1) = _
  rw [star_sub, star_one]
  linear_combination hz

/-- The determinant interpolates between the identity matching and the
Householder reflection with coefficient `‖z - 1‖² / 4`, even at zero factors. -/
theorem determinantValue_rankOnePhase_interpolate (a b v : ι → ℂ) (z : ℂ)
    (hv : ∑ i, star (v i) * v i = 1) (hz : z * star z = 1) :
    let s := Complex.normSq (z - 1) / 4
    determinantValue a b (rankOnePhase v z) =
      (1 - (s : ℂ)) * matchingProduct a b 1 +
        (s : ℂ) * determinantValue a b (rankOnePhase v (-1)) := by
  intro s
  let A (t : ℂ) (i : ι) := a i + t
  let K : Set ℂ := Set.range fun i : ι => -(a i + b i)
  have hK : Dense Kᶜ := (Set.finite_range _).countable.dense_compl ℂ
  let f (t : ℂ) := determinantValue (A t) b (rankOnePhase v z)
  let g (t : ℂ) := (1 - (s : ℂ)) * matchingProduct (A t) b 1 +
    (s : ℂ) * determinantValue (A t) b (rankOnePhase v (-1))
  have hs : 4 * (s : ℂ) = 2 - z - star z := by
    dsimp only [s]
    rw [Complex.ofReal_div, phase_distance_sq z hz]
    norm_num
    <;> ring
  have hminus : (-1 : ℂ) * star (-1) = 1 := by simp
  have hfg : Set.EqOn f g Kᶜ := by
    intro t ht
    have hreg (i : ι) : A t i + b i ≠ 0 := by
      intro he
      apply ht
      refine ⟨i, ?_⟩
      change a i + t + b i = 0 at he
      linear_combination -he
    change determinantValue (A t) b (rankOnePhase v z) =
      (1 - (s : ℂ)) * matchingProduct (A t) b 1 +
        (s : ℂ) * determinantValue (A t) b (rankOnePhase v (-1))
    rw [determinantValue_rankOnePhase _ _ _ _ hv hz hreg,
      determinantValue_rankOnePhase _ _ _ _ hv hminus hreg]
    change _ = (1 - (s : ℂ)) * (∏ i, (A t i + b i)) + (s : ℂ) * _
    simp only [star_neg, star_one]
    linear_combination ((∏ i, (A t i + b i)) *
      (rankOneSpectralCompression (A t) b v).det) * hs
  have hcA : Continuous A := continuous_pi fun _ => continuous_const.add continuous_id
  have hc (U : Matrix ι ι ℂ) : Continuous (fun t => determinantValue (A t) b U) := by
    unfold determinantValue
    fun_prop
  have hm : Continuous (fun t => matchingProduct (A t) b 1) := by
    unfold matchingProduct
    exact continuous_finset_prod _ fun i _ =>
      ((continuous_apply ((1 : Equiv.Perm ι) i)).comp hcA).add continuous_const
  have hf : Continuous f := hc _
  have hReflection := hc (rankOnePhase v (-1))
  have hg : Continuous g := (continuous_const.mul hm).add (continuous_const.mul hReflection)
  have hzero := hfg.closure hf hg (hK 0)
  have hA : A 0 = a := by funext i; simp [A]
  simpa only [f, g, hA] using hzero

/-- Every rank-one unitary phase determinant lies on the segment joining the
identity matching product to the Householder determinant. -/
theorem determinantValue_rankOnePhase_mem_segment (a b v : ι → ℂ) (z : ℂ)
    (hv : ∑ i, star (v i) * v i = 1) (hz : z * star z = 1) :
    determinantValue a b (rankOnePhase v z) ∈ segment ℝ (matchingProduct a b 1)
      (determinantValue a b (rankOnePhase v (-1))) := by
  let s := Complex.normSq (z - 1) / 4
  have hs0 : 0 ≤ s := div_nonneg (Complex.normSq_nonneg _) (by norm_num)
  have hn : ‖z‖ = 1 := by
    have hn' : (Complex.normSq z : ℂ) = 1 := by
      rw [Complex.normSq_eq_conj_mul_self]
      change star z * z = 1
      rwa [mul_comm]
    have hR := congrArg Complex.re hn'
    simp only [Complex.ofReal_re, Complex.one_re, Complex.normSq_eq_norm_sq] at hR
    nlinarith [norm_nonneg z]
  have hdist : ‖z - 1‖ ≤ 2 := by
    simpa only [hn, norm_one, one_add_one_eq_two] using norm_sub_le z (1 : ℂ)
  have hs1 : s ≤ 1 := by
    have hp := pow_le_pow_left₀ (norm_nonneg (z - 1)) hdist 2
    dsimp only [s]
    rw [Complex.normSq_eq_norm_sq]
    linarith
  refine ⟨1 - s, s, sub_nonneg.mpr hs1, hs0, by ring, ?_⟩
  rw [determinantValue_rankOnePhase_interpolate a b v z hv hz]
  simp only [Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_one, s]

/-- The reflection hull inclusion at the same spectra implies the inclusion
for every rank-one phase in its direction. -/
theorem holds_rankOnePhase_of_householder (a b v : ι → ℂ) (z : ℂ)
    (hv : ∑ i, star (v i) * v i = 1) (hz : z * star z = 1)
    (h : Holds a b (rankOnePhase v (-1))) :
    Holds a b (rankOnePhase v z) :=
  (convex_convexHull ℝ _).segment_subset (matchingProduct_mem_hull a b 1) h
    (determinantValue_rankOnePhase_mem_segment a b v z hv hz)

end

end MOC
