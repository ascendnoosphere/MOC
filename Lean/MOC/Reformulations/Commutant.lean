import MOC.Reformulations.Common
import MOC.FullSupportReduction
import MOC.Normal
import MOC.StrongSupport
import MOC.Variational

open Matrix

namespace MOC.Reformulations

noncomputable section

/-- The determinants in the commuting part of the right summand's
unitary orbit, written in an eigenbasis of the left summand. -/
def commutantDeterminants {n : ℕ} (a b : Fin n → ℂ) : Set ℂ :=
  {z | ∃ V : Matrix (Fin n) (Fin n) ℂ, IsUnitary V ∧
    Commute (diagonal a) (V * diagonal b * Vᴴ) ∧ z = determinantValue a b V}

private theorem matching_subset_commutant {n : ℕ} (a b : Fin n → ℂ) :
    Set.range (matchingProduct a b) ⊆ commutantDeterminants a b := by
  rintro z ⟨p, rfl⟩
  refine ⟨Equiv.Perm.permMatrix ℂ p.symm, isUnitary_permMatrix p.symm, ?_, ?_⟩
  · rw [permMatrix_conjugates, Matrix.submatrix_diagonal_equiv]
    change diagonal a * diagonal (b ∘ p.symm) = diagonal (b ∘ p.symm) * diagonal a
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    apply congrArg Matrix.diagonal
    funext i
    apply mul_comm
  · rw [determinantValue, permMatrix_conjugates, Matrix.submatrix_diagonal_equiv,
      Matrix.diagonal_add, Matrix.det_diagonal]
    simpa only [Function.comp_apply, Equiv.symm_symm] using matchingProduct_inverse a b p.symm

private theorem injective_left_of_injective_products {n : ℕ} {a b : Fin n → ℂ}
    (hp : Function.Injective (matchingProduct a b)) : Function.Injective a := by
  classical
  intro i j hij
  by_contra hne
  have hswap : a ∘ Equiv.swap i j = a := by
    funext k
    by_cases hki : k = i
    · subst k
      simpa using hij.symm
    by_cases hkj : k = j
    · subst k
      simpa using hij
    simp [Equiv.swap_apply_of_ne_of_ne hki hkj]
  have hprod : matchingProduct a b (Equiv.swap i j) =
      matchingProduct a b (Equiv.refl (Fin n)) := by
    unfold matchingProduct
    apply Finset.prod_congr rfl
    intro k _
    exact congrArg (fun x : ℂ => x + b k) (congrFun hswap k)
  have hcontra := DFunLike.congr_fun (hp hprod) i
  exact hne (by simpa using hcontra.symm)

private theorem commutant_subset_matching {n : ℕ} (a b : Fin n → ℂ)
    (ha : Function.Injective a) :
    commutantDeterminants a b ⊆ Set.range (matchingProduct a b) := by
  classical
  rintro z ⟨V, hV, hcomm, rfl⟩
  let Y := V * diagonal b * Vᴴ
  let y := Y.diag
  have hy : Y = diagonal y := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [y]
    · rw [Matrix.diagonal_apply_ne _ hij]
      have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i j) hcomm.eq
      change (diagonal a * Y) i j = (Y * diagonal a) i j at h
      rw [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm (Y i j)] at h
      have hzero : (a i - a j) * Y i j = 0 := by rw [sub_mul, h, sub_self]
      exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr (fun e => hij (ha e)))
  have hroots := roots_unitary_diagonalization b hV
  change Y.charpoly.roots = _ at hroots
  have hI : IsUnitary (1 : Matrix (Fin n) (Fin n) ℂ) := isUnitary_one
  have hd := roots_unitary_diagonalization y hI
  simp only [Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one] at hd
  obtain ⟨p, hp⟩ := exists_perm_of_equal_multisets y b (hd.symm.trans (hy ▸ hroots))
  refine ⟨p.symm, ?_⟩
  change matchingProduct a b p.symm = (diagonal a + Y).det
  rw [hy, hp, Matrix.diagonal_add, Matrix.det_diagonal, matchingProduct_inverse]
  rfl

/-- C★ 3. Taking the convex hull of determinants in the commuting part
of each orbit is equivalent to MOC. The proof needs the reverse set
inclusion only on the existing, exact regular-spectra reduction. -/
def CommutantForm : Prop :=
  ∀ (n : ℕ) (a b : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ), IsUnitary U →
    determinantValue a b U ∈ convexHull ℝ (commutantDeterminants a b)

theorem commutantForm_iff : CommutantForm ↔ MOCIsTrue := by
  constructor
  · intro h n
    apply conjecture_iff_regular_spectra_full_support.mpr
    intro a b U hU _ hp _
    exact convexHull_mono (commutant_subset_matching a b
      (injective_left_of_injective_products hp)) (h n a b U hU)
  · intro h n a b U hU
    exact convexHull_mono (matching_subset_commutant a b) (h n a b U hU)

/-- Each directional support maximum can be attained by commuting
summands exactly when the conjecture holds in the given order. -/
theorem conjecture_iff_commuting_support_maximum (n : ℕ) : Conjecture (Fin n) ↔
    ∀ (a b : Fin n → ℂ) (η : ℂ), ∃ V : Matrix (Fin n) (Fin n) ℂ, IsUnitary V ∧
      Commute (diagonal a) (V * diagonal b * Vᴴ) ∧
      ∀ U : Matrix (Fin n) (Fin n) ℂ, IsUnitary U →
        (η * determinantValue a b U).re ≤ (η * determinantValue a b V).re := by
  constructor
  · intro h a b η
    obtain ⟨U, hU, hmax⟩ := exists_support_maximizer a b η
    obtain ⟨p, hp⟩ := (holds_iff_directional a b U).mp (h a b U hU) η
    obtain ⟨V, hV, hc, he⟩ := matching_subset_commutant a b ⟨p, rfl⟩
    refine ⟨V, hV, hc, fun W hW => (hmax W hW).trans ?_⟩
    rw [← he]
    exact hp
  · intro h
    apply conjecture_iff_regular_spectra_full_support.mpr
    intro a b U hU _ hp _
    apply (holds_iff_directional a b U).mpr
    intro η
    obtain ⟨V, hV, hc, hmax⟩ := h a b η
    obtain ⟨p, he⟩ := commutant_subset_matching a b
      (injective_left_of_injective_products hp) ⟨V, hV, hc, rfl⟩
    exact ⟨p, by rw [he]; exact hmax U hU⟩

end

end MOC.Reformulations
