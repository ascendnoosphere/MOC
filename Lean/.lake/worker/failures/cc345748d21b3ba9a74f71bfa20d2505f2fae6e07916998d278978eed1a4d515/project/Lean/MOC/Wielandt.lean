import MOC.Singular
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import Mathlib.Tactic.Linarith

/-! Wielandt's strict circle-or-line criterion for eigenvalues of sums of
normal matrices (Pacific J. Math. 5 (1955), Lemma 2). -/

open Matrix

namespace MOC

noncomputable section

/-- The two spectra lie in opposite open half-planes, or one is strictly
inside a circle and the other is strictly outside it. The radius is squared. -/
def StrictlySeparatedByCircleOrLine {ι : Type*} (a b : ι → ℂ) : Prop :=
  (∃ x y t : ℝ, (x ≠ 0 ∨ y ≠ 0) ∧
    (∀ i, x * (a i).re + y * (a i).im < t) ∧
    (∀ i, t < x * (b i).re + y * (b i).im)) ∨
  ∃ (center : ℂ) (radiusSq : ℝ), 0 < radiusSq ∧
    (((∀ i, Complex.normSq (a i - center) < radiusSq) ∧
      (∀ i, radiusSq < Complex.normSq (b i - center))) ∨
      ((∀ i, radiusSq < Complex.normSq (a i - center)) ∧
      (∀ i, Complex.normSq (b i - center) < radiusSq)))

private def circleLinePolynomial (x y r t : ℝ) (z : ℂ) : ℝ :=
  x * z.re + y * z.im + r * Complex.normSq z + t

private theorem linear_apply_spectralMomentLift (L : (ℂ × ℝ) →L[ℝ] ℝ) (z : ℂ) :
    L (spectralMomentLift z) =
      L (1, 0) * z.re + L (Complex.I, 0) * z.im + L (0, 1) * Complex.normSq z := by
  have he : spectralMomentLift z =
      z.re • ((1 : ℂ), (0 : ℝ)) + z.im • (Complex.I, (0 : ℝ)) +
        Complex.normSq z • ((0 : ℂ), (1 : ℝ)) := by
    apply Prod.ext
    · simpa [spectralMomentLift, Complex.real_smul] using (Complex.re_add_im z).symm
    · simp [spectralMomentLift]
  rw [he]
  simp only [map_add, map_smul, smul_eq_mul]
  ring

private theorem disjoint_lifted_hulls_iff {ι : Type*} [Fintype ι] (a b : ι → ℂ) :
    Disjoint (convexHull ℝ (Set.range (spectralMomentLift ∘ a)))
      (convexHull ℝ (Set.range (spectralMomentLift ∘ b))) ↔
    ∃ x y r t : ℝ, (∀ i, circleLinePolynomial x y r t (a i) < 0) ∧
      (∀ i, 0 < circleLinePolynomial x y r t (b i)) := by
  constructor
  · intro h
    obtain ⟨L, u, v, hA, huv, hB⟩ := geometric_hahn_banach_compact_closed
      (convex_convexHull ℝ _) (Set.finite_range _).isCompact_convexHull
      (convex_convexHull ℝ _) (Set.finite_range _).isClosed_convexHull h
    refine ⟨L (1, 0), L (Complex.I, 0), L (0, 1), -u, ?_, ?_⟩
    · intro i
      have hi := hA (spectralMomentLift (a i)) (subset_convexHull ℝ _ (Set.mem_range_self i))
      rw [linear_apply_spectralMomentLift] at hi
      unfold circleLinePolynomial
      linarith only [hi]
    · intro i
      have hi := hB (spectralMomentLift (b i)) (subset_convexHull ℝ _ (Set.mem_range_self i))
      rw [linear_apply_spectralMomentLift] at hi
      unfold circleLinePolynomial
      linarith only [hi, huv]
  · rintro ⟨x, y, r, t, ha, hb⟩
    let L : (ℂ × ℝ) →ₗ[ℝ] ℝ :=
      x • Complex.reLm.comp (LinearMap.fst ℝ ℂ ℝ) +
        y • Complex.imLm.comp (LinearMap.fst ℝ ℂ ℝ) + r • LinearMap.snd ℝ ℂ ℝ
    have he (z : ℂ) : L (spectralMomentLift z) + t = circleLinePolynomial x y r t z := by
      simp [L, spectralMomentLift, circleLinePolynomial, smul_eq_mul]
    have hA : convexHull ℝ (Set.range (spectralMomentLift ∘ a)) ⊆ {p | L p < -t} := by
      refine convexHull_min ?_ (convex_halfSpace_lt L.isLinear (-t))
      rintro _ ⟨i, rfl⟩
      change L (spectralMomentLift (a i)) < -t
      linarith only [he (a i), ha i]
    have hB : convexHull ℝ (Set.range (spectralMomentLift ∘ b)) ⊆ {p | -t < L p} := by
      refine convexHull_min ?_ (convex_halfSpace_gt L.isLinear (-t))
      rintro _ ⟨i, rfl⟩
      change -t < L (spectralMomentLift (b i))
      linarith only [he (b i), hb i]
    rw [Set.disjoint_left]
    intro p hp hq
    exact not_lt_of_ge (le_of_lt (show -t < L p from hB hq)) (hA hp)

private theorem quadratic_separator_iff_circle_or_line {ι : Type*} [Nonempty ι] (a b : ι → ℂ) :
    (∃ x y r t : ℝ, (∀ i, circleLinePolynomial x y r t (a i) < 0) ∧
      (∀ i, 0 < circleLinePolynomial x y r t (b i))) ↔ StrictlySeparatedByCircleOrLine a b := by
  let i₀ : ι := Classical.choice ‹Nonempty ι›
  constructor
  · rintro ⟨x, y, r, t, ha, hb⟩
    by_cases hr : r = 0
    · have hnormal : x ≠ 0 ∨ y ≠ 0 := by
        by_contra! h
        have h₁ := ha i₀
        have h₂ := hb i₀
        simp [circleLinePolynomial, hr, h.1, h.2] at h₁ h₂
        linarith only [h₁, h₂]
      refine Or.inl ⟨x, y, -t, hnormal, ?_, ?_⟩
      · intro i
        have hi := ha i
        simp [circleLinePolynomial, hr] at hi
        linarith only [hi]
      · intro i
        have hi := hb i
        simp [circleLinePolynomial, hr] at hi
        linarith only [hi]
    · let center : ℂ := ⟨-(x / (2 * r)), -(y / (2 * r))⟩
      let radiusSq := Complex.normSq center - t / r
      have he (z : ℂ) : circleLinePolynomial x y r t z =
          r * (Complex.normSq (z - center) - radiusSq) := by
        simp only [circleLinePolynomial, radiusSq, center, Complex.normSq_apply,
          Complex.sub_re, Complex.sub_im]
        field_simp [hr] <;> ring
      simp only [he] at ha hb
      rcases lt_or_gt_of_ne hr with hr' | hr'
      · have ha' (i : ι) := sub_pos.mp (pos_of_mul_neg_right (ha i) hr'.le)
        have hb' (i : ι) := sub_neg.mp (neg_of_mul_pos_right (hb i) hr'.le)
        exact Or.inr ⟨center, radiusSq, (Complex.normSq_nonneg _).trans_lt (hb' i₀),
          Or.inr ⟨ha', hb'⟩⟩
      · have ha' (i : ι) := sub_neg.mp (neg_of_mul_neg_right (ha i) hr'.le)
        have hb' (i : ι) := sub_pos.mp (pos_of_mul_pos_right (hb i) hr'.le)
        exact Or.inr ⟨center, radiusSq, (Complex.normSq_nonneg _).trans_lt (ha' i₀),
          Or.inl ⟨ha', hb'⟩⟩
  · rintro (⟨x, y, t, _, ha, hb⟩ | ⟨center, radiusSq, _, h⟩)
    · refine ⟨x, y, 0, -t, ?_, ?_⟩
      · intro i
        simp only [circleLinePolynomial, zero_mul, add_zero]
        linarith only [ha i]
      · intro i
        simp only [circleLinePolynomial, zero_mul, add_zero]
        linarith only [hb i]
    · have he (z : ℂ) : circleLinePolynomial (-2 * center.re) (-2 * center.im) 1
          (Complex.normSq center - radiusSq) z = Complex.normSq (z - center) - radiusSq := by
        simp only [circleLinePolynomial, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
        ring
      rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · refine ⟨-2 * center.re, -2 * center.im, 1, Complex.normSq center - radiusSq,
          ?_, ?_⟩
        · intro i
          rw [he]
          exact sub_neg.mpr (ha i)
        · intro i
          rw [he]
          exact sub_pos.mpr (hb i)
      · have hneg (z : ℂ) : circleLinePolynomial (2 * center.re) (2 * center.im) (-1)
            (radiusSq - Complex.normSq center) z = -(Complex.normSq (z - center) - radiusSq) := by
          rw [← he]
          unfold circleLinePolynomial
          ring
        refine ⟨2 * center.re, 2 * center.im, -1, radiusSq - Complex.normSq center, ?_, ?_⟩
        · intro i
          rw [hneg]
          linarith only [ha i]
        · intro i
          rw [hneg]
          linarith only [hb i]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- All relative unitary bases give a nonsingular sum exactly when a circle
or line strictly separates the first spectrum from the negated second. -/
theorem not_exists_singular_iff_circle_or_line (a b : ι → ℂ) :
    (¬ ∃ U : Matrix ι ι ℂ, IsUnitary U ∧ determinantValue a b U = 0) ↔
      StrictlySeparatedByCircleOrLine a (fun i => -b i) := by
  rw [exists_singular_iff_inter_spectralMomentHulls_nonempty,
    Set.not_nonempty_iff_eq_empty, ← Set.disjoint_iff_inter_eq_empty]
  rcases isEmpty_or_nonempty (α := ι) with hi | hi
  · letI : IsEmpty ι := hi
    constructor
    · intro _
      exact Or.inl ⟨1, 0, 0, Or.inl one_ne_zero, fun i => isEmptyElim i, fun i => isEmptyElim i⟩
    · intro _
      simp [Set.range_eq_empty]
  · letI : Nonempty ι := hi
    exact (disjoint_lifted_hulls_iff a _).trans (quadratic_separator_iff_circle_or_line a _)

private theorem mem_charpoly_roots_iff_shifted_det_zero (a b : ι → ℂ)
    {U : Matrix ι ι ℂ} (hU : IsUnitary U) (z : ℂ) :
    z ∈ (diagonal a + U * diagonal b * Uᴴ).charpoly.roots ↔
      determinantValue a (fun i => b i - z) U = 0 := by
  let M := diagonal a + U * diagonal b * Uᴴ
  have hshift : determinantValue a (fun i => b i - z) U =
      determinantValue (fun i => a i - z) b U := by
    simpa only [sub_add_cancel] using determinantValue_shift (fun i => a i - z) b hU z
  have hmatrix : diagonal (fun i => a i - z) + U * diagonal b * Uᴴ =
      -(Matrix.scalar ι z - M) := by
    rw [← Matrix.diagonal_sub a (fun _ => z), Matrix.scalar_apply]
    unfold M
    abel
  change z ∈ M.charpoly.roots ↔ _
  rw [Polynomial.mem_roots M.charpoly_monic.ne_zero]
  change M.charpoly.eval z = 0 ↔ _
  rw [Matrix.charpoly, Matrix.eval_det, Matrix.matPolyEquiv_charmatrix, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, hshift, determinantValue, hmatrix, Matrix.det_neg]
  simp [mul_eq_zero]

/-- Wielandt's criterion. A complex number is excluded from the attainable
eigenvalues exactly when a circle or line strictly separates the first
spectrum from the reflected second spectrum. -/
theorem not_exists_charpoly_root_iff_circle_or_line (a b : ι → ℂ) (z : ℂ) :
    (¬ ∃ U : Matrix ι ι ℂ, IsUnitary U ∧
      z ∈ (diagonal a + U * diagonal b * Uᴴ).charpoly.roots) ↔
      StrictlySeparatedByCircleOrLine a (fun i => z - b i) := by
  have he : (∃ U : Matrix ι ι ℂ, IsUnitary U ∧
        z ∈ (diagonal a + U * diagonal b * Uᴴ).charpoly.roots) ↔
      ∃ U : Matrix ι ι ℂ, IsUnitary U ∧ determinantValue a (fun i => b i - z) U = 0 :=
    exists_congr (fun U => and_congr_right (fun hU =>
      mem_charpoly_roots_iff_shifted_det_zero a b (U := U) hU z))
  rw [he]
  simpa only [neg_sub] using not_exists_singular_iff_circle_or_line a (fun i => b i - z)

end

end MOC
