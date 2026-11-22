import MOC.Interlacing
import MOC.Small
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.Topology.Order.IntermediateValue

/-! Strict interlacing for a Hermitian principal compression with simple
spectrum and nonzero deleted-row weights. -/

open BigOperators Matrix

namespace MOC

noncomputable section

variable {n : ℕ}

/-- Weighted products obtained by deleting one spectral label. -/
def deletedRootPolynomial (lam w : Fin (n + 1) → ℝ) (t : ℝ) : ℝ :=
  ∑ j, w j * ∏ k ∈ Finset.univ.erase j, (t - lam k)

private theorem deletedRootPolynomial_at_knot (lam w : Fin (n + 1) → ℝ) (j : Fin (n + 1)) :
    deletedRootPolynomial lam w (lam j) = w j * ∏ k ∈ Finset.univ.erase j, (lam j - lam k) := by
  unfold deletedRootPolynomial
  rw [Finset.sum_eq_single j]
  · intro k _ hk
    rw [Finset.prod_eq_zero (i := j) (Finset.mem_erase.mpr ⟨hk.symm, Finset.mem_univ _⟩)
      (sub_self (lam j)), mul_zero]
  · simp

private theorem deletedRootPolynomial_alternate {lam w : Fin (n + 1) → ℝ}
    (hlam : StrictMono lam) (hw : ∀ j, 0 < w j) (i : Fin n) :
    deletedRootPolynomial lam w (lam i.castSucc) * deletedRootPolynomial lam w (lam i.succ) < 0 := by
  classical
  let a := i.castSucc
  let b := i.succ
  let s := (Finset.univ.erase a).erase b
  have hab : a < b := i.castSucc_lt_succ
  have ha : a ∈ (Finset.univ : Finset (Fin (n + 1))).erase b := by simp [hab.ne]
  have hb : b ∈ (Finset.univ : Finset (Fin (n + 1))).erase a := by simp [hab.ne']
  have hleft : (∏ k ∈ Finset.univ.erase a, (lam a - lam k)) =
      (lam a - lam b) * ∏ k ∈ s, (lam a - lam k) := by
    exact (Finset.mul_prod_erase _ _ hb).symm
  have hright : (∏ k ∈ Finset.univ.erase b, (lam b - lam k)) =
      (lam b - lam a) * ∏ k ∈ s, (lam b - lam k) := by
    simpa only [s, Finset.erase_right_comm] using
      (Finset.mul_prod_erase _ (fun k => lam b - lam k) ha).symm
  have hsign : 0 < ∏ k ∈ s, ((lam a - lam k) * (lam b - lam k)) := by
    apply Finset.prod_pos
    intro k hk
    have hkb : k ≠ b := (Finset.mem_erase.mp hk).1
    have hka : k ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
    rcases Fin.succ_le_or_le_castSucc k i with h | h
    · have hlt : b < k := lt_of_le_of_ne h hkb.symm
      exact mul_pos_of_neg_of_neg (sub_neg.mpr (hlam (hab.trans hlt))) (sub_neg.mpr (hlam hlt))
    · have hlt : k < a := lt_of_le_of_ne h hka
      exact mul_pos (sub_pos.mpr (hlam hlt)) (sub_pos.mpr (hlam (hlt.trans hab)))
  change deletedRootPolynomial lam w (lam a) * deletedRootPolynomial lam w (lam b) < 0
  rw [deletedRootPolynomial_at_knot lam w a, deletedRootPolynomial_at_knot lam w b, hleft, hright]
  have hneg : (w a * w b) * ((lam a - lam b) * (lam b - lam a)) < 0 :=
    mul_neg_of_pos_of_neg (mul_pos (hw a) (hw b))
      (mul_neg_of_neg_of_pos (sub_neg.mpr (hlam hab)) (sub_pos.mpr (hlam hab)))
  convert mul_neg_of_neg_of_pos hneg hsign using 1
  rw [Finset.prod_mul_distrib]
  ring

/-- Positive deletion weights give one root in each open spectral interval. -/
theorem exists_strict_interlaced_roots {lam w : Fin (n + 1) → ℝ}
    (hlam : StrictMono lam) (hw : ∀ j, 0 < w j) :
    ∃ α : Fin n → ℝ, ∀ i, lam i.castSucc < α i ∧ α i < lam i.succ ∧
      deletedRootPolynomial lam w (α i) = 0 := by
  let P := deletedRootPolynomial lam w
  have hcont : Continuous P := by unfold P deletedRootPolynomial; fun_prop
  have hroot (i : Fin n) : ∃ t, lam i.castSucc < t ∧ t < lam i.succ ∧ P t = 0 := by
    let a := lam i.castSucc
    let b := lam i.succ
    have hab : a < b := hlam i.castSucc_lt_succ
    have hsign : P a * P b < 0 := deletedRootPolynomial_alternate hlam hw i
    have hex : ∃ t ∈ Set.Icc a b, P t = 0 := by
      by_cases hleft : P a ≤ 0
      · have hright : 0 ≤ P b := by
          by_contra! hbad
          exact (not_lt_of_ge (mul_nonneg_of_nonpos_of_nonpos hleft hbad.le)) hsign
        exact intermediate_value_Icc hab.le hcont.continuousOn ⟨hleft, hright⟩
      · have hright : P b ≤ 0 := by
          by_contra! hbad
          exact (not_lt_of_ge (mul_nonneg (le_of_lt (lt_of_not_ge hleft)) hbad.le)) hsign
        exact intermediate_value_Icc' hab.le hcont.continuousOn ⟨hright, (lt_of_not_ge hleft).le⟩
    obtain ⟨t, ht, hz⟩ := hex
    refine ⟨t, lt_of_le_of_ne ht.1 ?_, lt_of_le_of_ne ht.2 ?_, hz⟩
    · intro h
      change a = t at h
      rw [h, hz, zero_mul] at hsign
      exact (lt_irrefl 0) hsign
    · intro h
      change t = b at h
      rw [← h, hz, mul_zero] at hsign
      exact (lt_irrefl 0) hsign
  choose α hα using hroot
  exact ⟨α, hα⟩

private theorem diagonal_const_smul_one {ι : Type*} [DecidableEq ι] (t : ℂ) :
    diagonal (fun _ : ι => t) = t • (1 : Matrix ι ι ℂ) := by
  ext i j : 1
  by_cases hij : i = j <;> simp [Matrix.diagonal_apply, Matrix.one_apply, hij]

private theorem diagonal_minus_unitary {ι : Type*} [Fintype ι] [DecidableEq ι] (lam : ι → ℝ)
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) (t : ℝ) :
    U * diagonal (fun j => (t : ℂ) - (lam j : ℂ)) * Uᴴ =
      diagonal (fun _ : ι => (t : ℂ)) -
        U * diagonal (fun j => (lam j : ℂ)) * Uᴴ := by
  rw [← Matrix.diagonal_sub, Matrix.mul_sub, Matrix.sub_mul, diagonal_const_smul_one,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hU.1]

/-- The eigenvalues of a Hermitian principal compression strictly interlace
simple ordered eigenvalues when the deleted row meets every eigenvector. -/
theorem exists_strict_interlacing_of_hermitian_compression
    (lam : Fin (n + 1) → ℝ) (hlam : StrictMono lam)
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hU : IsUnitary U) (p : Fin (n + 1))
    (hrow : ∀ j, U p j ≠ 0) :
    ∃ (α : Fin n → ℝ) (V : Matrix (Fin n) (Fin n) ℂ), IsUnitary V ∧
      (∀ i, lam i.castSucc < α i ∧ α i < lam i.succ) ∧
      (U * diagonal (fun j => (lam j : ℂ)) * Uᴴ).submatrix p.succAbove p.succAbove =
        V * diagonal (fun i => (α i : ℂ)) * Vᴴ := by
  classical
  let w : Fin (n + 1) → ℝ := fun j => Complex.normSq (U p j)
  let M := U * diagonal (fun j => (lam j : ℂ)) * Uᴴ
  let C := M.submatrix p.succAbove p.succAbove
  have hM : M.IsHermitian := by
    change Mᴴ = M
    simp only [M, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.diagonal_conjTranspose, Pi.star_def, Complex.star_def, Complex.conj_ofReal,
      Matrix.mul_assoc]
  have hC : C.IsHermitian := hM.submatrix p.succAbove
  let E : Matrix (Fin n) (Fin n) ℂ := hC.eigenvectorUnitary
  have hEu : IsUnitary E :=
    ⟨Matrix.mem_unitaryGroup_iff.mp hC.eigenvectorUnitary.2,
      Matrix.mem_unitaryGroup_iff'.mp hC.eigenvectorUnitary.2⟩
  let δ : Fin n → ℝ := hC.eigenvalues
  have hspec : C = E * diagonal (fun j => (δ j : ℂ)) * Eᴴ := by
    simpa only [E, δ, Function.comp_apply, Matrix.star_eq_conjTranspose] using hC.spectral_theorem
  have hdet1 (t : ℝ) :
      (diagonal (fun _ : Fin n => (t : ℂ)) - C).det = (deletedRootPolynomial lam w t : ℂ) := by
    have h := det_principal_unitary_diagonalization (fun j => (t : ℂ) - (lam j : ℂ)) hU p
    rw [diagonal_minus_unitary lam U hU t] at h
    change ((diagonal (fun _ : Fin (n + 1) => (t : ℂ))).submatrix p.succAbove p.succAbove -
      C).det = _ at h
    rw [Matrix.submatrix_diagonal _ _ Fin.succAbove_right_injective] at h
    simpa only [Function.comp_apply, w, deletedRootPolynomial, Complex.ofReal_sum,
      Complex.ofReal_mul, Complex.ofReal_prod, Complex.ofReal_sub] using h
  have hdet2 (t : ℝ) : (diagonal (fun _ : Fin n => (t : ℂ)) - C).det =
      ∏ j, ((t : ℂ) - (δ j : ℂ)) := by
    rw [hspec, ← diagonal_minus_unitary δ E hEu t, det_unitary_conjugation E _ hEu,
      Matrix.det_diagonal]
  obtain ⟨α, hα⟩ := exists_strict_interlaced_roots (w := w) hlam
    (fun j => Complex.normSq_pos.mpr (hrow j))
  have hroot (i : Fin n) : ∃ j, δ j = α i := by
    have h := hdet2 (α i)
    rw [hdet1, (hα i).2.2, Complex.ofReal_zero] at h
    obtain ⟨j, _, hj⟩ := Finset.prod_eq_zero_iff.mp h.symm
    exact ⟨j, Complex.ofReal_injective (sub_eq_zero.mp hj).symm⟩
  choose f hf using hroot
  have hαmono : StrictMono α := by
    intro i j hij
    have hij' : i.succ ≤ j.castSucc := Nat.succ_le_of_lt hij
    exact ((hα i).2.1.trans_le (hlam.monotone hij')).trans ((hα j).1)
  have hfinj : Function.Injective f := fun i j h => hαmono.injective (by
    simpa only [hf] using congrArg δ h)
  let e := Equiv.ofBijective f ⟨hfinj, Finite.injective_iff_surjective.mp hfinj⟩
  refine ⟨α, E.submatrix (Equiv.refl _) e, unitary_reindex (Equiv.refl _) e hEu,
    fun i => ⟨(hα i).1, (hα i).2.1⟩, ?_⟩
  change C = _
  have heq : (fun j => (α j : ℂ)) = (fun j => (δ j : ℂ)) ∘ e := by
    funext j
    exact congrArg Complex.ofReal (hf j).symm
  rw [hspec, heq, Matrix.conjTranspose_submatrix, ← Matrix.submatrix_diagonal_equiv _ e,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv] <;> rfl

end

end MOC
