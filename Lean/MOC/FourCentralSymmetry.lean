import MOC.ContactCensus
import MOC.Geometry
import MOC.Normal
import MOC.Small
import MOC.Support
import MOC.TwoValues
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! An order-four centrally symmetric family from three nonnegative minor certificates. -/

open BigOperators Matrix

namespace MOC

private def centralLeftInt : Fin 4 → GaussianInt :=
  ![⟨2, 0⟩, ⟨-2, 0⟩, ⟨2, 1⟩, ⟨-2, -1⟩]

private def centralRightInt : Fin 4 → GaussianInt :=
  ![⟨3, -1⟩, ⟨-3, 1⟩, ⟨3, 0⟩, ⟨-3, 0⟩]

private def centralLeft (i : Fin 4) : ℂ := GaussianInt.toComplex (centralLeftInt i)
private def centralRight (i : Fin 4) : ℂ := GaussianInt.toComplex (centralRightInt i)

private def centralProductInt (σ : Equiv.Perm (Fin 4)) : GaussianInt :=
  ∏ j, (centralLeftInt (σ j) + centralRightInt j)

private theorem centralProduct_map (σ : Equiv.Perm (Fin 4)) :
    GaussianInt.toComplex (centralProductInt σ) = matchingProduct centralLeft centralRight σ := by
  simp only [centralProductInt, matchingProduct, centralLeft, centralRight, map_prod, map_add]

private def centralDirection : Fin 3 → GaussianInt := ![⟨-100, -751⟩, ⟨0, 1⟩, ⟨100, 71⟩]
private def centralHeight : Fin 3 → ℤ := ![-67600, 0, -400]

-- Entries are row subset, column subset, and coefficient.
private def centralMinorTable : Fin 3 → Fin 13 → Finset (Fin 4) × Finset (Fin 4) × ℤ :=
  ![![({0}, {1}, 8520), ({0}, {3}, 25948), ({1}, {0}, 8520), ({1}, {2}, 25948),
      ({2}, {0}, 692), ({2}, {3}, 17122), ({3}, {2}, 16430), ({0, 1}, {0, 3}, 2600),
      ({0, 1}, {1, 2}, 1908), ({0, 2}, {1, 3}, 13000), ({0, 3}, {1, 2}, 4408),
      ({0, 3}, {1, 3}, 12512), (∅, ∅, 0)],
    ![({2}, {1}, 2), ({3}, {0}, 2), ({0, 1}, {0, 2}, 30), ({0, 2}, {0, 1}, 20),
      ({0, 2}, {1, 2}, 48), ({0, 2}, {2, 3}, 20), ({0, 3}, {0, 2}, 48),
      ({2, 3}, {0, 2}, 30), (∅, ∅, 0), (∅, ∅, 0), (∅, ∅, 0), (∅, ∅, 0), (∅, ∅, 0)],
    ![({0}, {0}, 1228), ({1}, {1}, 580), ({2}, {2}, 988), ({3}, {1}, 2900),
      ({3}, {3}, 4820), ({0, 1}, {0, 2}, 260), ({0, 1}, {0, 3}, 142),
      ({0, 1}, {1, 3}, 3950), ({0, 2}, {0, 2}, 60000), ({0, 2}, {2, 3}, 790),
      ({0, 3}, {0, 1}, 142), ({0, 3}, {0, 3}, 384), (∅, ∅, 0)]]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
private theorem centralCertificateInt : ∀ (k : Fin 3) (i : Fin 24),
    (centralDirection k * centralProductInt (fourPerm i)).re - centralHeight k =
      ∑ j : Fin 13, if (centralMinorTable k j).2.1.map (fourPerm i).toEmbedding =
        (centralMinorTable k j).1 then (centralMinorTable k j).2.2 else 0 := by
  decide +kernel

private theorem centralCertificate_nonneg : ∀ (k : Fin 3) (j : Fin 13),
    0 ≤ (centralMinorTable k j).2.2 := by
  decide +kernel

private theorem centralSupport (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) (k : Fin 3) :
    (centralHeight k : ℝ) ≤
      (GaussianInt.toComplex (centralDirection k) * determinantValue centralLeft centralRight U).re := by
  apply support_of_minor_gap_decomposition centralLeft centralRight _ _ U hU
    (fun j : Fin 13 => (centralMinorTable k j).1) (fun j => (centralMinorTable k j).2.1)
    (fun j => ((centralMinorTable k j).2.2 : ℝ))
  · intro j
    exact_mod_cast centralCertificate_nonneg k j
  · intro σ
    obtain ⟨i, rfl⟩ := fourPerm_surjective σ
    have h := congrArg (fun z : ℤ => (z : ℝ)) (centralCertificateInt k i)
    simpa only [Int.cast_sub, Int.cast_sum, Int.cast_ite, Int.cast_zero, GaussianInt.to_real_re,
      map_mul, centralProduct_map] using h

private def centralVertexIndex : Fin 3 → Fin 24 := ![22, 0, 7]
private def centralVertexInt : Fin 3 → GaussianInt := ![⟨-75, -100⟩, ⟨676, 0⟩, ⟨-4, 0⟩]

private theorem centralVertex_eval : ∀ k : Fin 3,
    centralProductInt (fourPerm (centralVertexIndex k)) = centralVertexInt k := by
  decide +kernel

private theorem centralVertex_mem (k : Fin 3) :
    GaussianInt.toComplex (centralVertexInt k) ∈ Set.range (matchingProduct centralLeft centralRight) := by
  exact ⟨fourPerm (centralVertexIndex k), by rw [← centralProduct_map, centralVertex_eval]⟩

private theorem holds_four_central_base (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    Holds centralLeft centralRight U := by
  let z := determinantValue centralLeft centralRight U
  have h₀ := centralSupport U hU 0
  have h₁ := centralSupport U hU 1
  have h₂ := centralSupport U hU 2
  change (centralHeight 0 : ℝ) ≤ (GaussianInt.toComplex (centralDirection 0) * z).re at h₀
  change (centralHeight 1 : ℝ) ≤ (GaussianInt.toComplex (centralDirection 1) * z).re at h₁
  change ((-400 : ℤ) : ℝ) ≤ (GaussianInt.toComplex ⟨100, 71⟩ * z).re at h₂
  norm_num [centralHeight, centralDirection, Complex.mul_re] at h₀ h₁ h₂
  let w : Fin 3 → ℝ :=
    ![-z.im / 100, (100 * z.re - 71 * z.im + 400) / 68000,
      (67600 - 100 * z.re + 751 * z.im) / 68000]
  have hw : ∀ k, 0 ≤ w k := by
    intro k
    fin_cases k <;> simp [w] <;> linarith only [h₀, h₁, h₂]
  have hsum : ∑ k, w k = 1 := by
    simp [Fin.sum_univ_three, w]
    ring
  unfold Holds
  refine mem_convexHull_of_exists_fintype w (fun k => GaussianInt.toComplex (centralVertexInt k))
    hw hsum centralVertex_mem ?_
  change (∑ k, w k • GaussianInt.toComplex (centralVertexInt k)) = z
  apply Complex.ext <;>
    simp [Fin.sum_univ_three, w, centralVertexInt, Complex.real_smul, Complex.mul_re,
      Complex.mul_im] <;> ring

noncomputable section

/-- The first spectrum has center `t` and offsets `±2s` and `±(2+i)s`. -/
def fourCentralLeft (s t : ℂ) (i : Fin 4) : ℂ := s * centralLeft i + t

/-- The second spectrum has center `-t` and offsets `±(3-i)s` and `±3s`. -/
def fourCentralRight (s t : ℂ) (i : Fin 4) : ℂ := s * centralRight i - t

/-- The centrally symmetric spectra satisfy the determinant hull inclusion
for every relative unitary. -/
theorem holds_four_central_family (s t : ℂ) (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : IsUnitary U) : Holds (fourCentralLeft s t) (fourCentralRight s t) U := by
  apply (holds_shift_iff (fun i => s * centralLeft i) (fun i => s * centralRight i) hU t).mpr
  exact hull_of_common_factor (determinantValue_scale centralLeft centralRight U s)
    (matchingProduct_scale centralLeft centralRight s) (holds_four_central_base U hU)

private def centralOpposite : Fin 4 → Fin 4 := ![1, 0, 3, 2]

private theorem centralLeftInt_opposite : ∀ i, centralLeftInt (centralOpposite i) = -centralLeftInt i := by
  decide +kernel

private theorem centralRightInt_opposite : ∀ i, centralRightInt (centralOpposite i) = -centralRightInt i := by
  decide +kernel

/-- Reflection about each center preserves its spectrum. -/
theorem four_central_family_symmetry (s t : ℂ) :
    (∀ i, ∃ j, fourCentralLeft s t j = 2 * t - fourCentralLeft s t i) ∧
    (∀ i, ∃ j, fourCentralRight s t j = 2 * (-t) - fourCentralRight s t i) := by
  constructor <;> intro i <;> refine ⟨centralOpposite i, ?_⟩
  · simp only [fourCentralLeft, centralLeft, centralLeftInt_opposite, map_neg]
    ring
  · simp only [fourCentralRight, centralRight, centralRightInt_opposite, map_neg]
    ring

private theorem central_nonconcyclic (a : Fin 4 → ℂ) (h₁ : a 1 = -a 0) (h₃ : a 3 = -a 2)
    (ha : Complex.normSq (a 0) ≠ Complex.normSq (a 2)) {s : ℂ} (hs : s ≠ 0) (t : ℂ) :
    ¬ ∃ (z : ℂ) (R : ℝ), ∀ i, Complex.normSq (s * a i + t - z) = R := by
  rintro ⟨z, R, h⟩
  let c := (z - t) / s
  have hc : s * c = z - t := by
    dsimp [c]
    rw [mul_comm s, div_mul_cancel₀ _ hs]
  have h' (i : Fin 4) : Complex.normSq s * Complex.normSq (a i - c) = R := by
    rw [← Complex.normSq_mul, mul_sub, hc,
      show s * a i - (z - t) = s * a i + t - z by ring]
    exact h i
  have hpair (u : ℂ) :
      Complex.normSq (u - c) + Complex.normSq (-u - c) =
        2 * (Complex.normSq u + Complex.normSq c) := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im]
    ring
  have hp₀ := h' 0
  have hp₁ := h' 1
  have hp₂ := h' 2
  have hp₃ := h' 3
  rw [h₁] at hp₁
  rw [h₃] at hp₃
  have he : Complex.normSq s * (2 * (Complex.normSq (a 0) + Complex.normSq c)) =
      Complex.normSq s * (2 * (Complex.normSq (a 2) + Complex.normSq c)) := by
    rw [← hpair, ← hpair, mul_add, mul_add, hp₀, hp₁, hp₂, hp₃]
  have he' := mul_left_cancel₀ (Complex.normSq_pos.mpr hs).ne' he
  exact ha (by linarith only [he'])

/-- At nonzero scale, neither spectrum lies on a circle. -/
theorem four_central_family_nonconcyclic {s : ℂ} (hs : s ≠ 0) (t : ℂ) :
    (¬ ∃ (z : ℂ) (R : ℝ), ∀ i, Complex.normSq (fourCentralLeft s t i - z) = R) ∧
    (¬ ∃ (z : ℂ) (R : ℝ), ∀ i, Complex.normSq (fourCentralRight s t i - z) = R) := by
  constructor
  · apply central_nonconcyclic centralLeft _ _ _ hs t
    · simpa only [centralLeft, map_neg] using
        congrArg GaussianInt.toComplex (centralLeftInt_opposite 0)
    · simpa only [centralLeft, map_neg] using
        congrArg GaussianInt.toComplex (centralLeftInt_opposite 2)
    · change Complex.normSq (GaussianInt.toComplex ⟨2, 0⟩) ≠
        Complex.normSq (GaussianInt.toComplex ⟨2, 1⟩)
      norm_num [Complex.normSq_apply]
  · simp only [fourCentralRight, sub_eq_add_neg]
    apply central_nonconcyclic centralRight _ _ _ hs (-t)
    · simpa only [centralRight, map_neg] using
        congrArg GaussianInt.toComplex (centralRightInt_opposite 0)
    · simpa only [centralRight, map_neg] using
        congrArg GaussianInt.toComplex (centralRightInt_opposite 2)
    · change Complex.normSq (GaussianInt.toComplex ⟨3, -1⟩) ≠
        Complex.normSq (GaussianInt.toComplex ⟨3, 0⟩)
      norm_num [Complex.normSq_apply]

private theorem centralCrossSumInt : ∀ i j, centralLeftInt i + centralRightInt j ≠ 0 := by
  decide +kernel

/-- No cross-sum of eigenvalues vanishes at a nonzero scale. -/
theorem four_central_family_cross_sum_ne {s : ℂ} (hs : s ≠ 0) (t : ℂ) (i j : Fin 4) :
    fourCentralLeft s t i + fourCentralRight s t j ≠ 0 := by
  have h : centralLeft i + centralRight j ≠ 0 := by
    intro hz
    apply centralCrossSumInt i j
    apply GaussianInt.toComplex_eq_zero.mp
    simpa only [map_add, centralLeft, centralRight] using hz
  have he : fourCentralLeft s t i + fourCentralRight s t j =
      s * (centralLeft i + centralRight j) := by
    unfold fourCentralLeft fourCentralRight
    ring
  rw [he]
  exact mul_ne_zero hs h

/-- At any fixed scale, the translation parameter gives infinitely many
pairs of spectra, even as unordered multisets. -/
theorem four_central_family_infinite (s : ℂ) :
    (Set.range fun t : ℂ =>
      ((Finset.univ : Finset (Fin 4)).val.map (fourCentralLeft s t),
        (Finset.univ : Finset (Fin 4)).val.map (fourCentralRight s t))).Infinite := by
  have hsum (t : ℂ) : ∑ i, fourCentralLeft s t i = 4 * t := by
    have h₁ : centralLeft 1 = -centralLeft 0 := by
      simpa only [centralLeft, map_neg] using
        congrArg GaussianInt.toComplex (centralLeftInt_opposite 0)
    have h₃ : centralLeft 3 = -centralLeft 2 := by
      simpa only [centralLeft, map_neg] using
        congrArg GaussianInt.toComplex (centralLeftInt_opposite 2)
    simp only [Fin.sum_univ_four, fourCentralLeft, h₁, h₃]
    ring
  apply Set.infinite_range_of_injective
  intro t u h
  have he := congrArg (fun p : Multiset ℂ × Multiset ℂ => p.1.sum) h
  change (∑ i, fourCentralLeft s t i) = ∑ i, fourCentralLeft s u i at he
  rw [hsum t, hsum u] at he
  exact mul_left_cancel₀ (by norm_num : (4 : ℂ) ≠ 0) he

/-- The same inclusion in the normal-matrix formulation with characteristic
roots counted with multiplicity. -/
theorem det_add_mem_hull_four_central_family (s t : ℂ) (A B : Matrix (Fin 4) (Fin 4) ℂ)
    (hA : IsStarNormal A) (hB : IsStarNormal B)
    (ha : A.charpoly.roots = (Finset.univ : Finset (Fin 4)).val.map (fourCentralLeft s t))
    (hb : B.charpoly.roots = (Finset.univ : Finset (Fin 4)).val.map (fourCentralRight s t)) :
    (A + B).det ∈ convexHull ℝ (Set.range (matchingProduct (fourCentralLeft s t) (fourCentralRight s t))) := by
  obtain ⟨a, V, hV, rfl⟩ := exists_unitary_diagonalization A hA
  obtain ⟨b, W, hW, rfl⟩ := exists_unitary_diagonalization B hB
  rw [roots_unitary_diagonalization a hV] at ha
  rw [roots_unitary_diagonalization b hW] at hb
  obtain ⟨e, he⟩ := exists_perm_of_equal_multisets _ _ ha.symm
  obtain ⟨f, hf⟩ := exists_perm_of_equal_multisets _ _ hb.symm
  rw [determinantValue_relative a b V W hV]
  rw [← determinantValue_reindex e f a b (Vᴴ * W), ← he, ← hf]
  exact holds_four_central_family s t ((Vᴴ * W).submatrix e f)
    (unitary_reindex e f (relative_unitary V W hV hW))

end

end MOC
