import MOC.UnequalColorHall
import MOC.StrongSupport
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-! The spectral multiplicities give the least root multiplicity of the
characteristic polynomial of the sum over all relative eigenbases. -/

open BigOperators Matrix Polynomial

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Number of equal-color pairs in a matching from columns to rows. -/
def colorMatchCount {C : Type*} [DecidableEq C]
    (a b : ι → C) (σ : Equiv.Perm ι) : ℕ :=
  ∑ j, if a (σ j) = b j then 1 else 0

private theorem colorMultiplicity_pair_eq_sum {C : Type*} [DecidableEq C]
    (a b : ι → C) (σ : Equiv.Perm ι) (c : C) :
    colorMultiplicity a c + colorMultiplicity b c =
      ∑ j, ((if a (σ j) = c then 1 else 0) + (if b j = c then 1 else 0)) := by
  have h := Equiv.sum_comp σ (fun j => if a j = c then (1 : ℕ) else 0)
  change (∑ j, if a (σ j) = c then 1 else 0) = ∑ j, if a j = c then 1 else 0 at h
  rw [Finset.sum_add_distrib, h]
  simp only [Finset.sum_boole, colorMultiplicity]

private theorem colorMultiplicity_add_le_card_add_matchCount {C : Type*} [DecidableEq C]
    (a b : ι → C) (σ : Equiv.Perm ι) (c : C) :
    colorMultiplicity a c + colorMultiplicity b c ≤ Fintype.card ι + colorMatchCount a b σ := by
  have hn : (∑ _ : ι, (1 : ℕ)) = Fintype.card ι := by simp
  rw [colorMultiplicity_pair_eq_sum a b σ c, colorMatchCount, ← hn, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  by_cases ha : a (σ j) = c
  · by_cases hb : b j = c
    · simp [ha, hb]
    · simp only [if_pos ha, if_neg hb, add_zero]
      exact Nat.le_add_right 1 _
  · by_cases hb : b j = c
    · rw [if_neg ha, if_pos hb, zero_add]
      exact Nat.le_add_right 1 _
    · rw [if_neg ha, if_neg hb, zero_add]
      exact Nat.zero_le _

private theorem colorMatchCount_swap_lt {C : Type*} [DecidableEq C]
    (a b : ι → C) (σ : Equiv.Perm ι) {i j : ι} (hij : i ≠ j)
    (hi : a (σ i) = b i) (hji : a (σ j) ≠ b i) (hij' : a (σ i) ≠ b j) :
    colorMatchCount a b (σ * Equiv.swap i j) < colorMatchCount a b σ := by
  let S := (Finset.univ : Finset ι).erase j
  have hiS : i ∈ S := Finset.mem_erase.mpr ⟨hij, Finset.mem_univ _⟩
  have hsplit (f : ι → ℕ) : (∑ l, f l) = (∑ l ∈ S.erase i, f l) + f i + f j := by
    rw [Finset.sum_erase_add S f hiS]
    exact (Finset.sum_erase_add Finset.univ f (Finset.mem_univ j)).symm
  unfold colorMatchCount
  rw [hsplit (fun l => if a ((σ * Equiv.swap i j) l) = b l then 1 else 0),
    hsplit (fun l => if a (σ l) = b l then 1 else 0)]
  have hsum : (∑ l ∈ S.erase i, if a ((σ * Equiv.swap i j) l) = b l then 1 else 0) =
      ∑ l ∈ S.erase i, if a (σ l) = b l then (1 : ℕ) else 0 := by
    apply Finset.sum_congr rfl
    intro l hl
    obtain ⟨hli, hlS⟩ := Finset.mem_erase.mp hl
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hli (Finset.mem_erase.mp hlS).1]
  rw [hsum]
  simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right,
    if_neg hji, if_neg hij', if_pos hi, add_zero]
  omega

/-- A matching with at most `k` equal-color pairs exists exactly when, for
every color, its combined multiplicity is at most the order plus `k`. -/
theorem exists_colorMatchCount_le_iff {C : Type*} [DecidableEq C]
    (a b : ι → C) (k : ℕ) :
    (∃ σ : Equiv.Perm ι, colorMatchCount a b σ ≤ k) ↔
      ∀ c, colorMultiplicity a c + colorMultiplicity b c ≤ Fintype.card ι + k := by
  constructor
  · rintro ⟨σ, hσ⟩ c
    exact (colorMultiplicity_add_le_card_add_matchCount a b σ c).trans (Nat.add_le_add_left hσ _)
  · intro hcolors
    obtain ⟨σ, _, hmin⟩ := Finset.exists_min_image Finset.univ (colorMatchCount a b)
      ⟨Equiv.refl ι, Finset.mem_univ _⟩
    use σ
    by_cases hz : ∃ i, a (σ i) = b i
    · obtain ⟨i, hi⟩ := hz
      have htouch (j : ι) : a (σ j) = b i ∨ b j = b i := by
        by_contra h
        push_neg at h
        have hij : i ≠ j := fun he => h.2 (congrArg b he.symm)
        have hcross : a (σ i) ≠ b j := by
          rw [hi]
          exact h.2.symm
        exact (not_lt_of_ge (hmin _ (Finset.mem_univ _)))
          (colorMatchCount_swap_lt a b σ hij hi h.1 hcross)
      have hcount : colorMultiplicity a (b i) + colorMultiplicity b (b i) =
          Fintype.card ι + colorMatchCount a b σ := by
        rw [colorMultiplicity_pair_eq_sum a b σ, colorMatchCount]
        calc
          _ = ∑ j, (1 + if a (σ j) = b j then (1 : ℕ) else 0) := by
            apply Finset.sum_congr rfl
            intro j _
            by_cases ha : a (σ j) = b i
            · by_cases hb : b j = b i
              · simp [ha, hb]
              · simp [ha, hb, show b i ≠ b j from hb.symm]
            · have hb := (htouch j).resolve_left ha
              simp [ha, hb]
          _ = _ := by rw [Finset.sum_add_distrib]; simp
      have h := hcolors (b i)
      omega
    · push_neg at hz
      simp [colorMatchCount, hz]

/-- The characteristic polynomial of the sum is the signed sum of the
matching polynomials, with the same real weights for every coefficient. -/
theorem charpoly_eq_realSignedWeight_matching_polynomials (a b : ι → ℂ)
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) :
    (diagonal a + U * diagonal b * Uᴴ).charpoly =
      ∑ σ : Equiv.Perm ι, Polynomial.C (realSignedWeight U σ : ℂ) *
        ∏ j, (X - Polynomial.C (a (σ j) + b j)) := by
  apply Polynomial.funext
  intro z
  rw [Matrix.charpoly, Matrix.eval_det, Matrix.matPolyEquiv_charmatrix,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, Matrix.scalar_apply]
  simp only [Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X]
  have he := (real_signed_determinant (fun i => z - a i) (fun j => -b j) U hU).symm
  have hd : diagonal (fun i => z - a i) = diagonal (fun _ : ι => z) - diagonal a := by
    rw [← Matrix.diagonal_sub]
  unfold determinantValue matchingProduct at he
  rw [hd, ← Matrix.diagonal_neg, Matrix.mul_neg, Matrix.neg_mul] at he
  simpa only [← sub_eq_add_neg, sub_sub] using he

private theorem rootMultiplicity_matching_polynomial (a b : ι → ℂ) (σ : Equiv.Perm ι) (z : ℂ) :
    (∏ j, (X - Polynomial.C (a (σ j) + b j))).rootMultiplicity z =
      colorMatchCount a (fun j => z - b j) σ := by
  let v (j : ι) := a (σ j) + b j
  have hroots : (∏ j, (X - Polynomial.C (v j))).roots = (Finset.univ : Finset ι).val.map v := by
    change ((Finset.univ : Finset ι).val.map ((fun z : ℂ => X - Polynomial.C z) ∘ v)).prod.roots = _
    rw [← Multiset.map_map, Polynomial.roots_multiset_prod_X_sub_C]
  change (∏ j, (X - Polynomial.C (v j))).rootMultiplicity z = _
  rw [← Polynomial.count_roots, hroots, Multiset.count_map, ← Finset.filter_val,
    colorMatchCount, Finset.sum_boole]
  change (Finset.univ.filter (fun j => z = v j)).card = _
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => eq_sub_iff_add_eq.mpr h.symm, fun h => (eq_sub_iff_add_eq.mp h).symm⟩

private theorem charpoly_spectralSum_perm (a b : ι → ℂ) (σ : Equiv.Perm ι) :
    (diagonal a + σ.symm.permMatrix ℂ * diagonal b * (σ.symm.permMatrix ℂ)ᴴ).charpoly =
      ∏ j, (X - Polynomial.C (a (σ j) + b j)) := by
  rw [permMatrix_conjugates, Matrix.submatrix_diagonal_equiv, Matrix.diagonal_add]
  let v (i : ι) := a i + b (σ.symm i)
  change (diagonal v).charpoly = _
  have hmatrix : (diagonal v).charmatrix = diagonal (fun i => X - Polynomial.C (v i)) := by
    ext i j : 1
    by_cases h : i = j
    · subst j
      simp
    · simp [h, Matrix.diagonal_apply_ne]
  rw [Matrix.charpoly, hmatrix, Matrix.det_diagonal,
    ← Equiv.prod_comp σ (fun i => X - Polynomial.C (v i))]
  simp only [Function.comp_apply, v, Equiv.symm_apply_apply]

/-- A complex number `z` has root multiplicity at least `k + 1` for every
unitary mixer exactly when two spectral values that sum to `z` have combined
multiplicity above the order plus `k`. -/
theorem forced_rootMultiplicity_iff (a b : ι → ℂ) (z : ℂ) (k : ℕ) :
    (∀ U : Matrix ι ι ℂ, IsUnitary U →
      k + 1 ≤ (diagonal a + U * diagonal b * Uᴴ).charpoly.rootMultiplicity z) ↔
    ∃ c : ℂ, Fintype.card ι + k <
      colorMultiplicity a c + colorMultiplicity (fun j => z - b j) c := by
  constructor
  · intro hall
    by_contra hcolor
    push_neg at hcolor
    obtain ⟨σ, hσ⟩ := (exists_colorMatchCount_le_iff a (fun j => z - b j) k).mpr hcolor
    have hu := hall (σ.symm.permMatrix ℂ) (isUnitary_permMatrix σ.symm)
    rw [charpoly_spectralSum_perm a b σ, rootMultiplicity_matching_polynomial] at hu
    omega
  · rintro ⟨c, hc⟩ U hU
    apply (Polynomial.le_rootMultiplicity_iff (Matrix.charpoly_monic _).ne_zero).mpr
    rw [charpoly_eq_realSignedWeight_matching_polynomials a b U hU]
    apply Finset.dvd_sum
    intro σ _
    have hcount := colorMultiplicity_add_le_card_add_matchCount a (fun j => z - b j) σ c
    have hp : (∏ j, (X - Polynomial.C (a (σ j) + b j))) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun _ _ => Polynomial.X_sub_C_ne_zero _)
    have hmul : k + 1 ≤ (∏ j, (X - Polynomial.C (a (σ j) + b j))).rootMultiplicity z := by
      rw [rootMultiplicity_matching_polynomial]
      omega
    exact ((Polynomial.le_rootMultiplicity_iff hp).mp hmul).mul_left _

end

end MOC
