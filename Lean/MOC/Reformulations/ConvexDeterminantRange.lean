import MOC.CenteredDeterminantDistance
import MOC.StrongSupport
import MOC.Variational
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Data.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-! Convex range tests for the determinant on the unitary orbit. -/

open BigOperators Matrix

namespace MOC.Reformulations

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A column phase sets the determinant of the mixer to one without
changing its conjugation of any diagonal matrix. -/
theorem conjecture_iff_special_unitary [Nonempty ι] : Conjecture ι ↔
    ∀ (a b : ι → ℂ) (U : Matrix ι ι ℂ), IsUnitary U → U.det = 1 → Holds a b U := by
  constructor
  · intro h a b U hU _
    exact h a b U hU
  · intro h a b U hU
    obtain ⟨o⟩ := ‹Nonempty ι›
    let d (i : ι) : ℂ := if i = o then star U.det else 1
    let D := diagonal d
    have hdU : U.det * star U.det = 1 := by
      have hd := congrArg Matrix.det hU.1
      rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at hd
      exact hd
    have hd (i : ι) : d i * star (d i) = 1 := by
      by_cases hi : i = o
      · simpa only [d, if_pos hi, star_star, mul_comm (star U.det)] using hdU
      · simp only [d, if_neg hi, star_one, one_mul]
    have hDs : Dᴴ = diagonal (fun i => star (d i)) := by
      exact Matrix.diagonal_conjTranspose d
    have hD : IsUnitary D := by
      have he₁ : d * (fun i => star (d i)) = (fun _ => 1) := funext hd
      have he₂ : (fun i => star (d i)) * d = (fun _ => 1) := by
        funext i
        change star (d i) * d i = 1
        rw [mul_comm, hd]
      unfold IsUnitary
      rw [hDs, D, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, he₁, he₂,
        Matrix.diagonal_one]
      exact ⟨rfl, rfl⟩
    have hDdet : D.det = star U.det := by
      rw [D, Matrix.det_diagonal, Finset.prod_eq_single o]
      · simp only [d, if_pos rfl]
      · intro i _ hi
        exact if_neg hi
      · simp
    have hUstar : IsUnitary Uᴴ := by
      simpa only [IsUnitary, Matrix.conjTranspose_conjTranspose] using And.intro hU.2 hU.1
    have hu := h a b (U * D) (by simpa only [Matrix.conjTranspose_conjTranspose] using
      relative_unitary Uᴴ D hUstar hD) (by rw [Matrix.det_mul, hDdet, hdU])
    have hcomm : Commute D (diagonal b) := by
      change D * diagonal b = diagonal b * D
      rw [D, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, mul_comm d b]
    have he : determinantValue a b (U * D) = determinantValue a b U := by
      have hDdiag : D * diagonal b * Dᴴ = diagonal b := by
        rw [hcomm.eq, Matrix.mul_assoc, hD.1, Matrix.mul_one]
      simp only [determinantValue, Matrix.conjTranspose_mul]
      rw [show U * D * diagonal b * (Dᴴ * Uᴴ) = U * (D * diagonal b * Dᴴ) * Uᴴ by
        simp only [Matrix.mul_assoc], hDdiag]
    unfold Holds at hu ⊢
    rwa [he] at hu

theorem matching_range_subset_determinant_orbit (a b : ι → ℂ) :
    Set.range (matchingProduct a b) ⊆ determinantRange a b := by
  rintro _ ⟨p, rfl⟩
  exact matchingProduct_mem_determinantRange a b p

/-- Range inclusion for every pair of spectra is precisely the conjecture. -/
theorem conjecture_iff_determinant_range : Conjecture ι ↔
    ∀ a b : ι → ℂ, determinantRange a b ⊆ convexHull ℝ (Set.range (matchingProduct a b)) := by
  constructor
  · rintro h a b _ ⟨U, hU, rfl⟩
    exact h a b U hU
  · intro h a b U hU
    exact h a b ⟨U, hU, rfl⟩

/-- Convexification of the determinant range gives the matching hull
exactly when the conjecture holds for those spectra. -/
theorem determinant_range_subset_iff_convex_hulls_eq (a b : ι → ℂ) :
    determinantRange a b ⊆ convexHull ℝ (Set.range (matchingProduct a b)) ↔
      convexHull ℝ (determinantRange a b) = convexHull ℝ (Set.range (matchingProduct a b)) := by
  constructor
  · intro h
    exact Set.Subset.antisymm (convexHull_min h (convex_convexHull ℝ _))
      (convexHull_mono (matching_range_subset_determinant_orbit a b))
  · intro h
    rw [← h]
    exact subset_convexHull ℝ _

/-- A permutation attains each directional maximum exactly when the
conjecture holds. This compares the full unitary orbit with all permutations. -/
theorem conjecture_iff_permutation_support_maximum : Conjecture ι ↔
    ∀ (a b : ι → ℂ) (η : ℂ), ∃ p : Equiv.Perm ι,
      ∀ U : Matrix ι ι ℂ, IsUnitary U →
        (η * determinantValue a b U).re ≤ (η * matchingProduct a b p).re := by
  constructor
  · intro h a b η
    obtain ⟨U, hU, hmax⟩ := exists_support_maximizer a b η
    obtain ⟨p, hp⟩ := (holds_iff_directional a b U).mp (h a b U hU) η
    exact ⟨p, fun V hV => (hmax V hV).trans hp⟩
  · intro h a b U hU
    apply (holds_iff_directional a b U).mpr
    intro η
    obtain ⟨p, hp⟩ := h a b η
    exact ⟨p, hp U hU⟩

/-- Continuous convex functions on the plane give exactly the matching
hull test. The converse uses real linear support functions. -/
theorem holds_iff_convex_function_test (a b : ι → ℂ) (U : Matrix ι ι ℂ) :
    Holds a b U ↔ ∀ φ : ℂ → ℝ, Continuous φ → ConvexOn ℝ Set.univ φ →
      ∃ p : Equiv.Perm ι, φ (determinantValue a b U) ≤ φ (matchingProduct a b p) := by
  classical
  constructor
  · intro h φ _ hφ
    obtain ⟨p, _, hp⟩ := Finset.exists_max_image Finset.univ
      (fun σ : Equiv.Perm ι => φ (matchingProduct a b σ)) ⟨1, Finset.mem_univ _⟩
    obtain ⟨κ, _, w, q, hw, hs, hq, hv⟩ := mem_convexHull_iff_exists_fintype.mp h
    refine ⟨p, ?_⟩
    have hj := hφ.map_sum_le (t := Finset.univ) (p := q) (fun i _ => hw i) hs
      (fun i _ => Set.mem_univ (q i))
    rw [hv] at hj
    refine hj.trans ?_
    calc
      _ ≤ ∑ i : κ, w i * φ (matchingProduct a b p) := by
        apply Finset.sum_le_sum
        intro i _
        obtain ⟨σ, hσ⟩ := hq i
        exact mul_le_mul_of_nonneg_left (hσ ▸ hp σ (Finset.mem_univ _)) (hw i)
      _ = _ := by rw [← Finset.sum_mul, hs, one_mul]
  · intro h
    apply (holds_iff_directional a b U).mpr
    intro η
    let L : ℂ →ₗ[ℝ] ℝ := Complex.reLm.comp (LinearMap.mulLeft ℝ η)
    have hc : Continuous L := by
      change Continuous (fun z : ℂ => (η * z).re)
      fun_prop
    exact h L hc (L.convexOn convex_univ)

/-- The shifted modulus test permits every complex center. -/
theorem holds_iff_shifted_modulus (a b : ι → ℂ) (U : Matrix ι ι ℂ) : Holds a b U ↔
    ∀ c : ℂ, ∃ p : Equiv.Perm ι,
      ‖determinantValue a b U - c‖ ≤ ‖matchingProduct a b p - c‖ := by
  unfold Holds
  simp only [mem_hull_iff_centered_normSq, Complex.normSq_eq_norm_sq,
    sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]

private theorem exists_at_most_three_points {s : Set ℂ} {z : ℂ} (h : z ∈ convexHull ℝ s) :
    ∃ k ≤ 3, ∃ (q : Fin k → ℂ) (w : Fin k → ℝ),
      (∀ i, q i ∈ s) ∧ (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧ ∑ i, w i • q i = z := by
  obtain ⟨κ, _, q, w, hq, hind, hw, hsum, he⟩ := eq_pos_convex_span_of_mem_convexHull h
  have hb : Fintype.card κ ≤ 3 := by
    have hd : Module.finrank ℝ (vectorSpan ℝ (Set.range q)) ≤ 2 := by
      rw [← Complex.finrank_real_complex]
      exact Submodule.finrank_le _
    exact hind.card_le_finrank_succ.trans (Nat.add_le_add_right hd 1)
  let e := Fintype.equivFin κ
  refine ⟨Fintype.card κ, hb, q ∘ e.symm, w ∘ e.symm, fun i => hq ⟨e.symm i, rfl⟩,
    fun i => (hw (e.symm i)).le, ?_, ?_⟩
  · exact (Equiv.sum_comp e.symm w).trans hsum
  · exact (Equiv.sum_comp e.symm (fun i => w i • q i)).trans he

/-- Three matching products suffice for every determinant in the matching hull. -/
theorem holds_iff_at_most_three_matchings (a b : ι → ℂ) (U : Matrix ι ι ℂ) :
    Holds a b U ↔ ∃ k ≤ 3, ∃ (p : Fin k → Equiv.Perm ι) (w : Fin k → ℝ),
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧
      (∑ i, (w i : ℂ) * matchingProduct a b (p i)) = determinantValue a b U := by
  constructor
  · intro h
    obtain ⟨k, hk, q, w, hq, hw, hs, hv⟩ := exists_at_most_three_points h
    choose p hp using hq
    exact ⟨k, hk, p, w, hw, hs, by simpa only [hp, Complex.real_smul] using hv⟩
  · rintro ⟨k, _, p, w, hw, hs, hv⟩
    apply mem_convexHull_of_exists_fintype w (fun i => matchingProduct a b (p i)) hw hs
      (fun i => ⟨p i, rfl⟩)
    simpa only [Complex.real_smul] using hv

private theorem isCompact_convexHull_complex {s : Set ℂ} (h : IsCompact s) :
    IsCompact (convexHull ℝ s) := by
  let T (k : Fin 4) : Set ((Fin k.val → ℝ) × (Fin k.val → ℂ)) :=
    (stdSimplex ℝ (Fin k.val)).prod (Set.univ.pi fun _ => s)
  let f (k : Fin 4) (q : (Fin k.val → ℝ) × (Fin k.val → ℂ)) : ℂ := ∑ i, q.1 i • q.2 i
  have he : convexHull ℝ s = ⋃ k : Fin 4, f k '' T k := by
    ext z
    rw [Set.mem_iUnion]
    constructor
    · intro hz
      obtain ⟨k, hk, q, w, hq, hw, hs, hv⟩ := exists_at_most_three_points hz
      refine ⟨⟨k, by omega⟩, (w, q), ⟨⟨hw, hs⟩, Set.mem_pi.mpr (fun i _ => hq i)⟩, hv⟩
    · rintro ⟨k, ⟨w, q⟩, ⟨⟨hw, hs⟩, hq⟩, rfl⟩
      exact mem_convexHull_of_exists_fintype w q hw hs
        (fun i => Set.mem_pi.mp hq i (Set.mem_univ _)) rfl
  rw [he]
  apply isCompact_iUnion
  intro k
  have ht : IsCompact (T k) := (isCompact_stdSimplex _).prod (isCompact_univ_pi fun _ => h)
  exact ht.image (by unfold f; fun_prop)

private theorem isCompact_determinant_orbit_hull (a b : ι → ℂ) :
    IsCompact (convexHull ℝ (determinantRange a b)) := by
  apply isCompact_convexHull_complex
  exact isCompact_setOf_isUnitary.image (by unfold determinantValue; fun_prop)

/-- Extreme points of the convexified orbit all belong to the matching
set exactly when the orbit is contained in the matching hull. -/
theorem determinant_range_subset_iff_extreme_points (a b : ι → ℂ) :
    determinantRange a b ⊆ convexHull ℝ (Set.range (matchingProduct a b)) ↔
      (convexHull ℝ (determinantRange a b)).extremePoints ℝ ⊆
        Set.range (matchingProduct a b) := by
  constructor
  · intro h
    rw [(determinant_range_subset_iff_convex_hulls_eq a b).mp h]
    exact extremePoints_convexHull_subset
  · intro h
    let K := convexHull ℝ (determinantRange a b)
    have hK : IsCompact K := isCompact_determinant_orbit_hull a b
    have he := closure_convexHull_extremePoints hK (convex_convexHull ℝ (determinantRange a b))
    exact (subset_convexHull ℝ _).trans (he ▸ closure_minimal (convexHull_mono h)
      (Set.finite_range (matchingProduct a b)).isClosed_convexHull)

private theorem exposed_of_maximal_distance {s : Set ℂ} {q c : ℂ} (hq : q ∈ s)
    (hmax : ∀ z ∈ s, Complex.normSq (z - c) ≤ Complex.normSq (q - c)) :
    q ∈ s.exposedPoints ℝ := by
  let L : ℂ →L[ℝ] ℝ := (q - c).re • Complex.reCLM + (q - c).im • Complex.imCLM
  have he (z : ℂ) : 2 * (L q - L z) = Complex.normSq (q - c) -
      Complex.normSq (z - c) + Complex.normSq (q - z) := by
    simp only [L, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, Complex.reCLM_apply, Complex.imCLM_apply, Complex.normSq_apply,
      Complex.sub_re, Complex.sub_im]
    ring
  have hle (z : ℂ) (hz : z ∈ s) : L z ≤ L q := by
    linarith only [he z, hmax z hz, Complex.normSq_nonneg (q - z)]
  have hlt (z : ℂ) (hz : z ∈ s) (hne : z ≠ q) : L z < L q := by
    have hp := Complex.normSq_pos.mpr (sub_ne_zero.mpr hne.symm)
    linarith only [he z, hmax z hz, hp]
  apply mem_exposedPoints_iff_exposed_singleton.mpr
  intro _
  refine ⟨L, ?_⟩
  ext z
  simp only [Set.mem_singleton_iff, Set.mem_setOf_eq]
  constructor
  · rintro rfl
    exact ⟨hq, fun y hy => hle y hy⟩
  · rintro ⟨hz, hm⟩
    by_contra hne
    exact (not_lt_of_ge (hm q hq)) (hlt z hz hne)

/-- The same matching-set condition on exposed points suffices. A point
of largest distance from a shifted disk center is an exposed point. -/
theorem conjecture_iff_exposed_points : Conjecture ι ↔
    ∀ a b : ι → ℂ, (convexHull ℝ (determinantRange a b)).exposedPoints ℝ ⊆
      Set.range (matchingProduct a b) := by
  constructor
  · intro h a b
    exact exposedPoints_subset_extremePoints.trans
      ((determinant_range_subset_iff_extreme_points a b).mp
        ((conjecture_iff_determinant_range.mp h) a b))
  · intro h a b U hU
    apply (holds_iff_shifted_modulus a b U).mpr
    intro c
    let K := convexHull ℝ (determinantRange a b)
    have hU' : determinantValue a b U ∈ K := subset_convexHull ℝ _ ⟨U, hU, rfl⟩
    have hcont : Continuous (fun z : ℂ => Complex.normSq (z - c)) :=
      Complex.continuous_normSq.comp (continuous_id.sub continuous_const)
    obtain ⟨q, hq, hmax⟩ := (isCompact_determinant_orbit_hull a b).exists_isMaxOn
      ⟨_, hU'⟩ hcont.continuousOn
    have hq' : q ∈ K.exposedPoints ℝ := exposed_of_maximal_distance hq (fun _ hz => hmax hz)
    obtain ⟨p, rfl⟩ := h a b hq'
    refine ⟨p, (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_⟩
    simpa only [← Complex.normSq_eq_norm_sq] using hmax hU'

end
end MOC.Reformulations
