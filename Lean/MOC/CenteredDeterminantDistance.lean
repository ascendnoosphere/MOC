import MOC.GaussianCayley
import MOC.Support
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Data.Matrix.Notation
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-! Centered disk tests and the integer determinant of Gaussian multiplication. -/

open BigOperators Matrix
open scoped ComplexConjugate

namespace MOC

private theorem normSq_sub_far_center (z k : ℂ) (r : ℝ) :
    Complex.normSq (z - (-(r : ℂ) * conj k)) =
      Complex.normSq z + Complex.normSq (-(r : ℂ) * conj k) + 2 * r * (k * z).re := by
  rw [Complex.normSq_sub]
  have hc : conj (-(r : ℂ) * conj k) = -(r : ℂ) * k := by simp
  rw [hc, neg_mul, mul_neg, Complex.neg_re,
    show z * ((r : ℂ) * k) = (r : ℂ) * (k * z) by ring, Complex.re_ofReal_mul]
  ring

/-- The convex hull of finitely many complex points is the intersection of
the closed disks that contain all those points. -/
theorem mem_hull_iff_centered_normSq {J : Type*} [Finite J] (f : J → ℂ) (z : ℂ) :
    z ∈ convexHull ℝ (Set.range f) ↔
      ∀ c : ℂ, ∃ j, Complex.normSq (z - c) ≤ Complex.normSq (f j - c) := by
  classical
  letI : Fintype J := Fintype.ofFinite J
  constructor
  · intro h c
    have hn : (Finset.univ : Finset J).Nonempty := by
      by_contra he
      have hr : Set.range f = ∅ := by
        apply Set.eq_empty_iff_forall_not_mem.mpr
        rintro _ ⟨j, rfl⟩
        exact he ⟨j, Finset.mem_univ j⟩
      simp [hr] at h
    obtain ⟨j, _, hmax⟩ := Finset.exists_max_image Finset.univ (fun i => ‖f i - c‖) hn
    refine ⟨j, ?_⟩
    have hb : Set.range f ⊆ Metric.closedBall c ‖f j - c‖ := by
      rintro _ ⟨i, rfl⟩
      exact Metric.mem_closedBall.mpr (hmax i (Finset.mem_univ i))
    have hz := Metric.mem_closedBall.mp (convexHull_min hb (convex_closedBall c _) h)
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    exact pow_le_pow_left₀ (norm_nonneg _) hz 2
  · intro h
    obtain ⟨j₀, _⟩ := h 0
    apply mem_hull_of_directional_bound
    intro k
    by_contra! hs
    let gap (j : J) := (k * z).re - (k * f j).re
    obtain ⟨j₁, _, hmin⟩ :=
      Finset.exists_min_image Finset.univ gap ⟨j₀, Finset.mem_univ j₀⟩
    let δ := gap j₁
    have hδ : 0 < δ := sub_pos.mpr (hs j₁)
    let s := ∑ j, Complex.normSq (f j)
    let r := (s + 1) / (2 * δ)
    have hs₀ : 0 ≤ s := Finset.sum_nonneg fun j _ => Complex.normSq_nonneg (f j)
    have hr : 0 ≤ r := div_nonneg (by linarith only [hs₀]) (by positivity)
    have heq : 2 * r * δ = s + 1 := by
      dsimp only [r]
      field_simp [hδ.ne'] <;> ring
    obtain ⟨j, hj⟩ := h (-(r : ℂ) * conj k)
    have hbudget : Complex.normSq (f j) ≤ s :=
      Finset.single_le_sum (fun i _ => Complex.normSq_nonneg (f i)) (Finset.mem_univ j)
    have hlarge : s + 1 ≤ 2 * r * gap j := by
      rw [← heq]
      exact mul_le_mul_of_nonneg_left (hmin j (Finset.mem_univ j)) (by positivity)
    simp only [normSq_sub_far_center] at hj
    dsimp only [gap] at hlarge
    nlinarith only [hj, hlarge, hbudget, Complex.normSq_nonneg z]

/-- Gaussian-rational centers suffice for the centered disk test. -/
theorem mem_hull_iff_gaussian_rational_centered_normSq {J : Type*} [Finite J]
    (f : J → ℂ) (z : ℂ) :
    z ∈ convexHull ℝ (Set.range f) ↔
      ∀ c ∈ gaussianRationalSubfield, ∃ j, Complex.normSq (z - c) ≤ Complex.normSq (f j - c) := by
  rw [mem_hull_iff_centered_normSq]
  refine ⟨fun h c _ => h c, fun h => ?_⟩
  let C : Set ℂ := ⋃ j, {c | Complex.normSq (z - c) ≤ Complex.normSq (f j - c)}
  have hC : IsClosed C := isClosed_iUnion_of_finite fun j =>
    isClosed_le (by fun_prop) (by fun_prop)
  have hsub : (gaussianRationalSubfield : Set ℂ) ⊆ C := by
    intro c hc
    exact Set.mem_iUnion.mpr (h c hc)
  have hall := closure_minimal hsub hC
  rw [dense_gaussianRationalSubfield.closure_eq] at hall
  intro c
  exact Set.mem_iUnion.mp (hall (Set.mem_univ c))

/-- The finite matrix for multiplication by a Gaussian integer on the
lattice basis consisting of one and the imaginary unit. -/
def gaussianMultiplicationMatrix (m : GaussianInt) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![m.re, -m.im; m.im, m.re]

theorem det_gaussianMultiplicationMatrix (m : GaussianInt) :
    (gaussianMultiplicationMatrix m).det = m.norm := by
  simp [gaussianMultiplicationMatrix, Matrix.det_fin_two, Zsqrtd.norm] <;> ring

/-- The lattice quotient by multiplication by a nonzero Gaussian integer
has as many elements as the norm of that integer. -/
theorem card_gaussianMultiplication_cokernel (m : GaussianInt) (hm : m ≠ 0) :
    Nat.card ((Fin 2 → ℤ) ⧸ LinearMap.range (Matrix.toLin' (gaussianMultiplicationMatrix m))) =
      m.norm.natAbs := by
  let A := gaussianMultiplicationMatrix m
  let f := Matrix.toLin' A
  have hdet : A.det ≠ 0 := by
    rw [show A = gaussianMultiplicationMatrix m from rfl, det_gaussianMultiplicationMatrix]
    exact (GaussianInt.norm_pos.mpr hm).ne'
  have hf : Function.Injective f := by
    intro x y h
    change A *ᵥ x = A *ᵥ y at h
    have he := congrArg (fun v => Matrix.adjugate A *ᵥ v) h
    change Matrix.adjugate A *ᵥ (A *ᵥ x) = Matrix.adjugate A *ᵥ (A *ᵥ y) at he
    simp only [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec_assoc,
      Matrix.one_mulVec] at he
    funext i
    exact mul_left_cancel₀ hdet (congrFun he i)
  let e := LinearEquiv.ofInjective f hf
  have hcomp : (LinearMap.range f).subtype ∘ₗ
      AddMonoidHom.toIntLinearMap (e.toAddEquiv : (Fin 2 → ℤ) →+ LinearMap.range f) = f := by
    ext v i
    rfl
  have hc := Submodule.natAbs_det_equiv (LinearMap.range f) e.toAddEquiv
  rw [hcomp, show f = Matrix.toLin' A from rfl, LinearMap.det_toLin',
    show A = gaussianMultiplicationMatrix m from rfl, det_gaussianMultiplicationMatrix] at hc
  exact hc.symm

/-- For any positive common denominator, the centered distance comparison
equals a comparison of Gaussian multiplication determinants. -/
theorem gaussianMultiplication_det_le_iff_centered_normSq {z w c : ℂ}
    {N : ℕ} (hN : N ≠ 0) (d p : GaussianInt)
    (hd : (d : ℂ) = (N : ℂ) * (z - c)) (hp : (p : ℂ) = (N : ℂ) * (w - c)) :
    (gaussianMultiplicationMatrix d).det ≤ (gaussianMultiplicationMatrix p).det ↔
      Complex.normSq (z - c) ≤ Complex.normSq (w - c) := by
  rw [det_gaussianMultiplicationMatrix, det_gaussianMultiplicationMatrix]
  have he : 0 < Complex.normSq (N : ℂ) :=
    Complex.normSq_pos.mpr (by exact_mod_cast hN)
  have hc : d.norm ≤ p.norm ↔ (d.norm : ℝ) ≤ (p.norm : ℝ) := Int.cast_le.symm
  rw [hc, GaussianInt.intCast_real_norm, GaussianInt.intCast_real_norm, hd, hp,
    Complex.normSq_mul, Complex.normSq_mul]
  exact mul_le_mul_left he

/-- Unrestricted MOC is equivalent to centered disk comparisons with
Gaussian-integer spectra, Gaussian-rational mixers and Gaussian-rational centers. -/
theorem mocIsTrue_iff_gaussian_rational_centered_normSq :
    MOCIsTrue ↔ ∀ (n : ℕ) (a b : Fin n → ℤ × ℤ) (U : Matrix (Fin n) (Fin n) ℂ),
      IsUnitary U → (∀ i j, U i j ∈ gaussianRationalSubfield) →
      ∀ c ∈ gaussianRationalSubfield, ∃ σ : Equiv.Perm (Fin n),
        Complex.normSq (determinantValue (fun i => (a i).1 + (a i).2 * Complex.I)
          (fun i => (b i).1 + (b i).2 * Complex.I) U - c) ≤
        Complex.normSq (matchingProduct (fun i => (a i).1 + (a i).2 * Complex.I)
          (fun i => (b i).1 + (b i).2 * Complex.I) σ - c) := by
  rw [mocIsTrue_iff_gaussian_spectra_rational_mixer]
  simp only [Holds, mem_hull_iff_gaussian_rational_centered_normSq]

end MOC
