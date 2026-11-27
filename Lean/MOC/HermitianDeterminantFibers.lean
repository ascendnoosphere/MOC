import MOC.Hermitian
import MOC.StrongSupport
import Mathlib.Data.Complex.BigOperators
import Mathlib.Topology.Separation.Connected

/-! Positive maximum fibers of the determinant on Hermitian orbits. -/

open BigOperators Matrix

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The fiber consists of conjugated matrices, with different mixers that
produce the same conjugate counted only once. -/
def determinantOrbitFiber (a b : ι → ℂ) (z : ℂ) : Set (Matrix ι ι ℂ) :=
  {C | (∃ U : Matrix ι ι ℂ, IsUnitary U ∧ U * diagonal b * Uᴴ = C) ∧
    (diagonal a + C).det = z}

private theorem hermitianDiagonalOfReal (a : ι → ℝ) :
    (diagonal fun i => (a i : ℂ)).IsHermitian := by
  apply Matrix.isHermitian_diagonal_iff.mpr
  intro i
  simp [isSelfAdjoint_iff, Complex.star_def]

/-- A positive upper bound on all real matching products has a fiber
consisting precisely of the diagonal assignments that attain the bound,
provided the first spectrum is simple. -/
theorem determinantOrbitFiber_eq_matching_diagonals (a b : ι → ℝ)
    (ha : Function.Injective a) (r : ℝ) (hr : 0 < r)
    (hbound : ∀ p : Equiv.Perm ι, (∏ i, (a i + b (p i))) ≤ r) :
    determinantOrbitFiber (fun i => (a i : ℂ)) (fun i => (b i : ℂ)) (r : ℂ) =
      {C | ∃ p : Equiv.Perm ι, C = diagonal (fun i => (b (p i) : ℂ)) ∧
        (∏ i, (a i + b (p i))) = r} := by
  classical
  let A := diagonal (fun i => (a i : ℂ))
  let β : ι → ℂ := fun i => b i
  have haC : Function.Injective (fun i => (a i : ℂ)) :=
    fun _ _ h => ha (Complex.ofReal_injective h)
  have hdet (p : Equiv.Perm ι) : (A + diagonal (β ∘ p)).det =
      Complex.ofReal (∏ i, (a i + b (p i))) := by
    change (diagonal (fun i => (a i : ℂ)) + diagonal (β ∘ p)).det = _
    rw [Matrix.diagonal_add, Matrix.det_diagonal, Complex.ofReal_prod] <;>
      simp only [β, Function.comp_apply, Complex.ofReal_add]
  have hglobal (U : Matrix ι ι ℂ) (hU : IsUnitary U) :
      (A + U * diagonal β * Uᴴ).det.re ≤ r := by
    have h := (holds_iff_directional _ _ U).mp (holds_of_real_spectra a b U hU)
      (1 : ℂ)
    obtain ⟨σ, hσ⟩ := h
    have hp := matchingProduct_inverse (fun i => (a i : ℂ)) β σ.symm
    rw [Equiv.symm_symm] at hp
    have hp' : (matchingProduct (fun i => (a i : ℂ)) β σ).re =
        ∏ i, (a i + b (σ.symm i)) := by
      rw [hp] <;> simp only [β, ← Complex.ofReal_add, ← Complex.ofReal_prod, Complex.ofReal_re]
    have hscore : (A + U * diagonal β * Uᴴ).det.re ≤ (∏ i, (a i + b (σ.symm i))) := by
      rw [← hp']
      simpa only [determinantValue, A, β, one_mul] using hσ
    exact hscore.trans (hbound σ.symm)
  ext C
  constructor
  · rintro ⟨⟨U, hU, hUC⟩, hC⟩
    change (A + C).det = (r : ℂ) at hC
    change U * diagonal β * Uᴴ = C at hUC
    have hHerm : C.IsHermitian := hUC ▸
      Matrix.isHermitian_mul_mul_conjTranspose U (hermitianDiagonalOfReal b)
    have hComm : Commute A C := by
      apply commute_of_hermitian_support_maximum A C 1 (hermitianDiagonalOfReal a) hHerm
        (by simp) (by rw [hC]; exact Complex.ofReal_ne_zero.mpr hr.ne')
      intro V hV
      have hVstar : IsUnitary Vᴴ := ⟨by simpa using hV.2, by simpa using hV.1⟩
      have hVU : IsUnitary (V * U) := by simpa using relative_unitary Vᴴ U hVstar hU
      rw [one_mul, one_mul, hC, Complex.ofReal_re, ← hUC]
      simpa only [Matrix.conjTranspose_mul, Matrix.mul_assoc] using hglobal (V * U) hVU
    let d := C.diag
    have hd : C = diagonal d := by
      ext i j : 1
      by_cases hij : i = j
      · subst j
        simp only [d, Matrix.diagonal_apply_eq, Matrix.diag_apply]
      · rw [Matrix.diagonal_apply_ne _ hij]
        have he := congrArg (fun M : Matrix ι ι ℂ => M i j) hComm.eq
        change (diagonal (fun k => (a k : ℂ)) * C) i j =
          (C * diagonal (fun k => (a k : ℂ))) i j at he
        rw [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm (C i j)] at he
        have hz : ((a i : ℂ) - (a j : ℂ)) * C i j = 0 := by
          rw [sub_mul, he, sub_self]
        exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr (fun h => hij (haC h)))
    have hroots : C.charpoly.roots = (Finset.univ : Finset ι).val.map β :=
      hUC ▸ roots_unitary_diagonalization β hU
    have hdroots := roots_unitary_diagonalization d isUnitary_one
    simp only [Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one] at hdroots
    obtain ⟨p, hp⟩ := exists_perm_of_equal_multisets d β (hdroots.symm.trans (hd ▸ hroots))
    have hpC : C = diagonal (β ∘ p) := hd.trans (congrArg diagonal hp)
    rw [hpC, hdet p] at hC
    exact ⟨p, hpC, Complex.ofReal_injective hC⟩
  · rintro ⟨p, rfl, hp⟩
    refine ⟨⟨p.permMatrix ℂ, isUnitary_permMatrix p, ?_⟩, ?_⟩
    · rw [permMatrix_conjugates, Matrix.submatrix_diagonal_equiv] <;> rfl
    · change (A + diagonal (β ∘ p)).det = (r : ℂ)
      rw [hdet p, hp]

private def integralScore (a b : ι → ℤ) (p : Equiv.Perm ι) : ℤ :=
  ∏ i, (a i + b (p i))

private theorem exists_pair_of_integral_scores (a b : ι → ℤ) (r : ℤ)
    (p q : Equiv.Perm ι) (ha : Function.Injective a) (hb : Function.Injective b)
    (hr : 0 < r) (hpq : p ≠ q)
    (hs : ∀ s, integralScore a b s ≤ r ∧ (integralScore a b s = r ↔ s = p ∨ s = q)) :
    ∃ C D : Matrix ι ι ℂ, C ≠ D ∧
      determinantOrbitFiber (fun i => (a i : ℂ)) (fun i => (b i : ℂ)) (r : ℂ) = {C, D} := by
  let C := diagonal (fun i => (b (p i) : ℂ))
  let D := diagonal (fun i => (b (q i) : ℂ))
  have hne : C ≠ D := by
    intro h
    apply hpq
    ext i
    apply hb
    have hentry := congrArg (fun M : Matrix ι ι ℂ => M i i) h
    simp only [C, D, Matrix.diagonal_apply_eq] at hentry
    exact_mod_cast hentry
  have haR : Function.Injective (fun i => (a i : ℝ)) := by
    intro i j h
    exact ha (Int.cast_inj.mp h)
  have hbound (s : Equiv.Perm ι) : (∏ i, ((a i : ℝ) + (b (s i) : ℝ))) ≤ (r : ℝ) := by
    simpa only [integralScore, Int.cast_prod, Int.cast_add] using
      (show (integralScore a b s : ℝ) ≤ (r : ℝ) by exact_mod_cast (hs s).1)
  have hreal (s : Equiv.Perm ι) : (∏ i, ((a i : ℝ) + (b (s i) : ℝ))) = (r : ℝ) ↔
      s = p ∨ s = q := by
    rw [show (∏ i, ((a i : ℝ) + (b (s i) : ℝ))) = (integralScore a b s : ℝ) by
      simp only [integralScore, Int.cast_prod, Int.cast_add]]
    simpa only [Int.cast_inj] using (hs s).2
  have hfiber := determinantOrbitFiber_eq_matching_diagonals
    (fun i => (a i : ℝ)) (fun i => (b i : ℝ)) haR (r : ℝ) (by exact_mod_cast hr) hbound
  refine ⟨C, D, hne, ?_⟩
  simp only [Complex.ofReal_intCast] at hfiber
  rw [hfiber]
  ext X
  change (∃ s : Equiv.Perm ι, X = diagonal (fun i => (b (s i) : ℂ)) ∧
    (∏ i, ((a i : ℝ) + (b (s i) : ℝ))) = (r : ℝ)) ↔ X ∈ {C, D}
  simp only [hreal, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨s, hX, rfl | rfl⟩
    · exact Or.inl hX
    · exact Or.inr hX
  · rintro (rfl | rfl)
    · exact ⟨p, rfl, Or.inl rfl⟩
    · exact ⟨q, rfl, Or.inr rfl⟩

private def leftThree : Fin 3 → ℤ := ![-2, 1, 4]
private def leftFour : Fin 4 → ℤ := ![-4, -3, -1, 0]
private def rightFour : Fin 4 → ℤ := ![-3, -2, 1, 2]
private def leftFive : Fin 5 → ℤ := ![-4, -3, -2, -1, 2]
private def rightFive : Fin 5 → ℤ := ![-3, -2, 0, 3, 4]

/-- For the given order-three Hermitian lists, exactly two points attain
the positive maximum determinant of eight. -/
theorem orderThree_hermitianDeterminantFiber_two_points :
    ∃ C D : Matrix (Fin 3) (Fin 3) ℂ, C ≠ D ∧
      determinantOrbitFiber (fun i => (leftThree i : ℂ)) (fun i => (leftThree i : ℂ)) 8 =
        {C, D} := by
  simpa only [Int.cast_ofNat] using exists_pair_of_integral_scores leftThree leftThree 8
    (Equiv.swap 0 1) (Equiv.swap 0 2) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- For the given order-four Hermitian lists, exactly two points attain
the positive maximum determinant of thirty-six. -/
theorem orderFour_hermitianDeterminantFiber_two_points :
    ∃ C D : Matrix (Fin 4) (Fin 4) ℂ, C ≠ D ∧
      determinantOrbitFiber (fun i => (leftFour i : ℂ)) (fun i => (rightFour i : ℂ)) 36 =
        {C, D} := by
  simpa only [Int.cast_ofNat] using exists_pair_of_integral_scores leftFour rightFour 36
    (Equiv.swap 0 1 * Equiv.swap 2 3) (Equiv.swap 0 3 * Equiv.swap 1 2)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
/-- For the given order-five Hermitian lists, exactly two points attain
the positive maximum determinant of 288. -/
theorem orderFive_hermitianDeterminantFiber_two_points :
    ∃ C D : Matrix (Fin 5) (Fin 5) ℂ, C ≠ D ∧
      determinantOrbitFiber (fun i => (leftFive i : ℂ)) (fun i => (rightFive i : ℂ)) 288 =
        {C, D} := by
  simpa only [Int.cast_ofNat] using exists_pair_of_integral_scores leftFive rightFive 288
    (Equiv.swap 0 1 * Equiv.swap 2 4) (Equiv.swap 0 3 * Equiv.swap 1 2)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- An exact two-point fiber is disconnected in the matrix topology. -/
theorem not_isConnected_of_determinantOrbitFiber_two_points (a b : ι → ℂ) (z : ℂ)
    (h : ∃ C D : Matrix ι ι ℂ, C ≠ D ∧ determinantOrbitFiber a b z = {C, D}) :
    ¬ IsConnected (determinantOrbitFiber a b z) := by
  obtain ⟨C, D, hne, heq⟩ := h
  rw [heq]
  intro hc
  have hn : ({C, D} : Set (Matrix ι ι ℂ)).Nontrivial := ⟨C, by simp, D, by simp, hne⟩
  exact (hc.isPreconnected.infinite_of_nontrivial hn) ((Set.finite_singleton D).insert C)

end

end MOC
