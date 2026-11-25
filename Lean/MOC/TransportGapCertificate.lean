import MOC.IndependentCrossingObstruction
import MOC.NestedContactObjective

/-! Local transport certificates for support gaps. The nested and crossed
minor couplings use the finite shadow method of Lyons, DOI
10.1007/s10240-003-0016-0. No joint law of all minor events is assumed. -/

open BigOperators Finset Matrix

namespace MOC
noncomputable section

/-- A supported nonnegative flow tests additive reduced costs. Strictness
occurs precisely when some positive flow uses a strictly positive edge. -/
theorem transportReducedCost_nonneg_and_zero
    {A B : Type*} [Fintype A] [Fintype B] (R : A → B → Prop)
    (m : A → ℝ) (n : B → ℝ) (p : A → ℝ) (q : B → ℝ)
    (t : A → B → ℝ) (ht : ∀ a b, 0 ≤ t a b)
    (hs : ∀ a b, t a b ≠ 0 → R a b)
    (hr : ∀ a, ∑ b, t a b = m a) (hc : ∀ b, ∑ a, t a b = n b)
    (hcost : ∀ a b, R a b → 0 ≤ p a + q b) :
    let z := (∑ a, m a * p a) + ∑ b, n b * q b
    0 ≤ z ∧ (z = 0 ↔ ∀ a b, 0 < t a b → p a + q b = 0) := by
  have he : (∑ a, m a * p a) + ∑ b, n b * q b =
      ∑ a, ∑ b, t a b * (p a + q b) := by
    simp_rw [← hr, ← hc, Finset.sum_mul, mul_add, Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun b a => t a b * q b)]
  dsimp only
  rw [he]
  have H (a : A) (b : B) : 0 ≤ t a b * (p a + q b) := by
    by_cases h : t a b = 0
    · simp [h]
    · exact mul_nonneg (ht a b) (hcost a b (hs a b h))
  refine ⟨sum_nonneg (fun a _ => sum_nonneg (fun b _ => H a b)), ?_⟩
  constructor
  · intro hz a b hab
    have ha := (Finset.sum_eq_zero_iff_of_nonneg
      (fun a _ => sum_nonneg (fun b _ => H a b))).mp hz a (mem_univ a)
    have hb := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => H a b)).mp ha b (mem_univ b)
    exact (mul_eq_zero.mp hb).resolve_left (ne_of_gt hab)
  · intro h
    apply Finset.sum_eq_zero
    intro a _
    apply Finset.sum_eq_zero
    intro b _
    by_cases hb : t a b = 0
    · simp [hb]
    · rw [h a b (lt_of_le_of_ne (ht a b) (Ne.symm hb)), mul_zero]

/-- Arbitrary signed potentials on two nested images are legal whenever their
sum is nonnegative on the allowed inclusion edges. -/
theorem nestedMinorReducedCost_nonneg {n : ℕ}
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U)
    (J K : Finset (Fin n)) (hJK : J ⊆ K) (p q : Finset (Fin n) → ℝ)
    (hcost : ∀ I L, I ⊆ L → I.card = J.card → L.card = K.card → 0 ≤ p I + q L) :
    0 ≤ (∑ I, subsetMinorSq U I J * p I) + ∑ L, subsetMinorSq U L K * q L := by
  obtain ⟨t, ht, hs, hr, hc⟩ := exists_nested_minor_transport U hU J K hJK
  have hsized I L (h : t I L ≠ 0) : I ⊆ L ∧ I.card = J.card ∧ L.card = K.card := by
    refine ⟨hs I L h, ?_, ?_⟩
    · by_contra hb
      have hz : ∑ L, t I L = 0 := by rw [hr]; simp [subsetMinorSq, hb]
      exact h ((Finset.sum_eq_zero_iff_of_nonneg (fun L _ => ht I L)).mp hz L (mem_univ L))
    · by_contra hb
      have hz : ∑ I, t I L = 0 := by rw [hc]; simp [subsetMinorSq, hb]
      exact h ((Finset.sum_eq_zero_iff_of_nonneg (fun I _ => ht I L)).mp hz I (mem_univ I))
  exact (transportReducedCost_nonneg_and_zero _ _ _ p q t ht hsized hr hc
    (fun I L h => hcost I L h.1 h.2.1 h.2.2)).1

/-- Independent row and column marks give legal crossed reduced costs, with
no common permutation law across different marks. -/
theorem crossedMinorReducedCost_nonneg {n : ℕ}
    (U : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (hU : IsUnitary U)
    (r c : Equiv.Perm (Fin (n+1)))
    (p q : (Finset (Fin n) × Finset (Fin n)) → ℝ)
    (hcost : ∀ A B, A.1 ⊆ B.1 ∧ B.2 ⊆ A.2 ∧ A.1.card = B.2.card →
      0 ≤ p A + q B) :
    let rv := (Fin.succEmb n).trans r.toEmbedding
    let cv := (Fin.succEmb n).trans c.toEmbedding
    0 ≤ (∑ A, subsetMinorSq U (insert (r 0) (A.1.map rv)) (A.2.map cv) * p A) +
      ∑ B, subsetMinorSq U (B.1.map rv) (insert (c 0) (B.2.map cv)) * q B := by
  obtain ⟨t, ht, hs, hr, hc⟩ := independentCrossedTests_of_unitary U hU r c
  exact (transportReducedCost_nonneg_and_zero _ _ _ p q t ht hs hr hc hcost).1

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The atomic permutation event that sends the column subset J onto the row subset I. -/
def minorEvent (I J : Finset ι) (σ : Equiv.Perm ι) : ℝ :=
  if J.map σ.toEmbedding = I then 1 else 0

/-- An exact identity on matching labels and a nonnegative minor certificate
imply a spectral support inequality. This lets a proof combine ordinary and
crossed flow certificates, even if their flows have no common refinement. -/
theorem projected_partialMatchingGap_certificate
    (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U) (η : ℂ)
    (r : Equiv.Perm ι) (c : Finset ι → Finset ι → ℝ)
    (hgap : ∀ σ, matchingGap a b η r σ = ∑ I, ∑ J, c I J * minorEvent I J σ)
    (hminor : 0 ≤ ∑ I, ∑ J, c I J * subsetMinorSq U I J) :
    (η * determinantValue a b U).re ≤ (η * matchingProduct a b r).re := by
  classical
  have he (I J : Finset ι) :
      (∑ σ, realSignedWeight U σ * minorEvent I J σ) = subsetMinorSq U I J := by
    unfold minorEvent
    simp only [mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
    simpa only [Complex.re_sum, Complex.ofReal_re, realSignedWeight] using
      congrArg Complex.re (sum_signedWeight_image_eq_subsetMinorSq U hU I J)
  rw [← sub_nonneg, support_gap_eq a b U hU, show
      (∑ σ, realSignedWeight U σ * matchingGap a b η r σ) =
        ∑ I, ∑ J, c I J * subsetMinorSq U I J from ?_]
  · exact hminor
  simp_rw [hgap, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [← he, Finset.mul_sum]
  exact Finset.sum_congr rfl fun σ _ => by ring

end
end MOC
