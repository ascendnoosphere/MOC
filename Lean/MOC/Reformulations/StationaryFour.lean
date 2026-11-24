import MOC.Reformulations.Contacts
import MOC.FourMinorTransport
import MOC.SpectralPerturbation

open BigOperators Matrix

namespace MOC.Reformulations
noncomputable section

/-- At fixed complex spectra, the order-four unitary test is exactly its
real orthogonal restriction. The minor mixture does not change the spectra. -/
theorem fourHolds_iff_orthogonalAt (a b : Fin 4 → ℂ) :
    (∀ U : Matrix (Fin 4) (Fin 4) ℂ, IsUnitary U → Holds a b U) ↔
      ∀ O : Matrix.orthogonalGroup (Fin 4) ℝ,
        Holds a b (Complex.ofRealHom.mapMatrix O.val) := by
  constructor
  · intro h O
    exact h _ (isUnitary_ofReal_orthogonal O)
  · intro h U hU
    obtain ⟨κ, inst, w, O, hw, hs, hm⟩ := four_minor_mixture U hU
    letI : Fintype κ := inst
    let V (k : κ) : Matrix (Fin 4) (Fin 4) ℂ := Complex.ofRealHom.mapMatrix (O k).val
    have hV (k : κ) : IsUnitary (V k) := isUnitary_ofReal_orthogonal (O k)
    have hdet : ∑ k, w k • determinantValue a b (V k) = determinantValue a b U := by
      simp_rw [determinantValue_eq_sum_subsetMinors a b U hU,
        fun k => determinantValue_eq_sum_subsetMinors a b (V k) (hV k),
        Complex.real_smul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro J _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro I _
      rw [hm I J, Complex.ofReal_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      rw [Complex.ofReal_mul, mul_assoc]
    rw [Holds, ← hdet]
    exact (convex_convexHull ℝ _).sum_mem (fun k _ => hw k) hs (fun k _ => h (O k))

/-- Real orthogonal mixers and regular spectra together suffice in order four.
Neither restriction changes the complex spectral support question. -/
theorem conjecture_four_iff_regularOrthogonal :
    Conjecture (Fin 4) ↔
      ∀ (a b : Fin 4 → ℂ) (O : Matrix.orthogonalGroup (Fin 4) ℝ),
        (∀ i j, a i + b j ≠ 0) → Function.Injective (matchingProduct a b) →
          Holds a b (Complex.ofRealHom.mapMatrix O.val) := by
  constructor
  · intro h a b O _ _
    exact h a b _ (isUnitary_ofReal_orthogonal O)
  · intro h
    apply conjecture_iff_regular_matching_products.mpr
    intro a b U hU hnonzero hinj
    exact (fourHolds_iff_orthogonalAt a b).mpr (fun O => h a b O hnonzero hinj) U hU

private def denseSigns : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 1, 1, 1; 1, -1, -1, 1; 1, -1, 1, -1; 1, 1, -1, -1]

private def minorAt (O : Matrix (Fin 4) (Fin 4) ℝ) (i k j l : Fin 4) : ℝ :=
  O i j * O k l - O i l * O k j

/-- The explicit sign chamber of the open stationary witness target. -/
def InCanonicalDenseChamber (O : Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  (∀ i j, 0 < denseSigns i j * O i j) ∧
  minorAt O 0 1 0 3 < 0 ∧ minorAt O 0 1 1 2 < 0 ∧
  minorAt O 0 2 0 2 < 0 ∧ 0 < minorAt O 0 2 1 3 ∧
  minorAt O 0 3 0 1 < 0 ∧ minorAt O 0 3 2 3 < 0

private def weightedEntryFour (a b : Fin 4 → ℂ) (X : Matrix (Fin 4) (Fin 4) ℝ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun i j => (a i + b j) * (X i j : ℂ)

/-- Adjugate equations for stationarity along real skew row directions. -/
def SatisfiesStationaryEquations (a b : Fin 4 → ℂ)
    (O : Matrix.orthogonalGroup (Fin 4) ℝ) (η : ℂ) : Prop :=
  ∀ X : Matrix (Fin 4) (Fin 4) ℝ, Xᵀ = -X →
    (η * ((weightedEntryFour a b O.val).adjugate *
      weightedEntryFour a b (X * O.val)).trace /
      (Complex.ofRealHom.mapMatrix O.val).det).re = 0

/-- A strict separating witness in the specified chamber with seven contact
labels. This is a finite-dimensional proof target, not an assumed solution
or an assumed counterexample. The converse reduction is a separate gap. -/
def SevenContactStationaryWitness : Prop :=
  ∃ (a b : Fin 4 → ℂ) (O : Matrix.orthogonalGroup (Fin 4) ℝ) (η : ℂ)
      (p : Equiv.Perm (Fin 4)),
    InCanonicalDenseChamber O.val ∧ SatisfiesStationaryEquations a b O η ∧
    (∀ q : Equiv.Perm (Fin 4),
      (η * matchingProduct a b q).re ≤ (η * matchingProduct a b p).re) ∧
    7 ≤ (Finset.univ.filter fun q : Equiv.Perm (Fin 4) =>
      (η * matchingProduct a b q).re = (η * matchingProduct a b p).re).card ∧
    (η * matchingProduct a b p).re <
      (η * determinantValue a b (Complex.ofRealHom.mapMatrix O.val)).re

theorem not_moc_of_sevenContactStationaryWitness (h : SevenContactStationaryWitness) :
    ¬ MOCIsTrue := by
  rintro hm
  obtain ⟨a, b, O, η, p, _, _, hp, hcontacts, hgap⟩ := h
  exact (not_le_of_gt hgap) (contactForm_of_conjecture (k := 7) (hm 4) a b _ η p
    (isUnitary_ofReal_orthogonal O) hp hcontacts)

end

end MOC.Reformulations
