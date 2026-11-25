import MOC.OrderFourReflectionTest
import MOC.SparseRow
import MOC.Support

/-!
An explicit dense-candidate test: reflecting a column to a signed coordinate
vector gives a mixer covered by the smaller-order theorem.
-/

open Matrix BigOperators

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem real_rankOnePhase_neg_one_mul_apply (u : ι → ℝ)
    (U : Matrix ι ι ℂ) (i k : ι) :
    (rankOnePhase (fun j => (u j : ℂ)) (-1) * U) i k =
      U i k - 2 * (u i : ℂ) * ∑ j, (u j : ℂ) * U j k := by
  rw [rankOnePhase, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.add_apply,
    Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul]
  simp only [Matrix.vecMulVec_apply, Function.comp_apply, Complex.star_def, Complex.conj_ofReal,
    mul_assoc, ← Finset.mul_sum]
  ring

omit [DecidableEq ι] in
private theorem normalized_reflection_data (x y : ι → ℝ)
    (hx : ∑ i, x i ^ 2 = 1) (hy : ∑ i, y i ^ 2 = 1) (hxy : x ≠ y) :
    let d := Real.sqrt (∑ i, (x i - y i) ^ 2)
    let u := fun i => (x i - y i) / d
    (∑ i, u i ^ 2 = 1) ∧ ∀ i, x i - 2 * u i * (∑ j, u j * x j) = y i := by
  intro d u
  let q := ∑ i, (x i - y i) ^ 2
  have hq : 0 < q := by
    apply lt_of_le_of_ne (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    intro h
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (x i - y i))).mp h.symm
    exact hxy (funext fun i => by nlinarith only [hz i (Finset.mem_univ _)])
  have hd : d ≠ 0 := (Real.sqrt_pos.2 hq).ne'
  have hd2 : d ^ 2 = q := Real.sq_sqrt hq.le
  have hq' : q = 2 * (∑ i, (x i - y i) * x i) := by
    have ht (i : ι) : (x i - y i) ^ 2 =
        2 * ((x i - y i) * x i) - x i ^ 2 + y i ^ 2 := by ring
    simp_rw [q, ht]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hx, hy]
    ring
  constructor
  · change (∑ i, ((x i - y i) / d) ^ 2) = _
    simp_rw [div_pow, div_eq_mul_inv]
    rw [← Finset.sum_mul, ← div_eq_mul_inv, show (∑ i, (x i - y i) ^ 2) = q from rfl, ← hd2,
      div_self (pow_ne_zero 2 hd)]
  · intro i
    have htotal : (∑ j, u j * x j) = (∑ j, (x j - y j) * x j) / d := by
      change (∑ j, (x j - y j) / d * x j) = _
      simp_rw [div_mul_eq_mul_div, div_eq_mul_inv]
      rw [← Finset.sum_mul]
    rw [htotal]
    change x i - 2 * ((x i - y i) / d) * ((∑ j, (x j - y j) * x j) / d) = y i
    field_simp
    rw [← pow_two, hd2, hq']
    ring

/-- Given any unit real column and any different signed coordinate vector,
one real rank-one reflection sends the column to that vector. The resulting
mixer has column degree one, so its order-four determinant is in the hull. -/
theorem four_reflect_column_to_signed_coordinate
    (a b : Fin 4 → ℂ) (O : Matrix.orthogonalGroup (Fin 4) ℝ)
    (i k : Fin 4) (r : ℝ) (hr : r ^ 2 = 1)
    (hdiff : (fun j => O.val j k) ≠ (fun j => if j = i then r else 0)) :
    ∃ u : Fin 4 → ℝ,
      (∑ j, star (u j : ℂ) * (u j : ℂ) = 1) ∧
      let U := Complex.ofRealHom.mapMatrix O.val
      let V := rankOnePhase (fun j => (u j : ℂ)) (-1) * U
      (∀ j, V j k = (if j = i then (r : ℂ) else 0)) ∧ Holds a b V := by
  let x : Fin 4 → ℝ := fun j => O.val j k
  let y : Fin 4 → ℝ := fun j => if j = i then r else 0
  let U := Complex.ofRealHom.mapMatrix O.val
  have hU : IsUnitary U := isUnitary_ofReal_orthogonal O
  have hx : ∑ j, x j ^ 2 = 1 := by
    have hh := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M k k) hU.2
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at hh
    have hxU (j : Fin 4) : U j k = (x j : ℂ) := rfl
    simp only [hxU, Complex.star_def, Complex.conj_ofReal, ← pow_two] at hh
    exact_mod_cast hh
  have hy : ∑ j, y j ^ 2 = 1 := by
    rw [Finset.sum_eq_single i]
    · simp [y, hr]
    · intro j _ hji
      simp [y, hji]
    · simp
  let d := Real.sqrt (∑ j, (x j - y j) ^ 2)
  let u := fun j => (x j - y j) / d
  have ⟨hu, huMap⟩ := normalized_reflection_data x y hx hy hdiff
  have hu' : ∑ j, star (u j : ℂ) * (u j : ℂ) = 1 := by
    simp only [Complex.star_def, Complex.conj_ofReal, ← pow_two]
    exact_mod_cast hu
  let V := rankOnePhase (fun j => (u j : ℂ)) (-1) * U
  have hcol (j : Fin 4) : V j k = (if j = i then (r : ℂ) else 0) := by
    change (rankOnePhase (fun j => (u j : ℂ)) (-1) * U) j k = _
    rw [real_rankOnePhase_neg_one_mul_apply]
    have hxU (i : Fin 4) : U i k = (x i : ℂ) := rfl
    simp only [hxU]
    have hrow : x j - 2 * u j * (∑ l, u l * x l) = y j := huMap j
    have h := congrArg (fun z : ℝ => (z : ℂ)) hrow
    push_cast at h
    rw [show (y j : ℂ) = (if j = i then (r : ℂ) else 0) by by_cases hh : j = i <;> simp [y, hh]] at h
    exact h
  refine ⟨u, hu', hcol, ?_⟩
  have hR := rankOnePhase_unitary (fun j => (u j : ℂ)) (-1) hu' (by simp)
  have hR' : IsUnitary (rankOnePhase (fun j => (u j : ℂ)) (-1))ᴴ := by
    simpa only [IsUnitary, Matrix.conjTranspose_conjTranspose] using And.intro hR.2 hR.1
  have hV : IsUnitary V := by
    simpa only [V, Matrix.conjTranspose_conjTranspose] using relative_unitary _ U hR' hU
  classical
  have hS : supportColumns Vᴴ {k} ⊆ {i} := by
    intro j hj
    have hn : V j k ≠ 0 := by simpa [supportColumns, Matrix.conjTranspose_apply] using hj
    by_cases hji : j = i
    · simp [hji]
    · exact (hn (by simp [hcol, hji])).elim
  have hcard : (supportColumns Vᴴ {k}).card ≤ 2 :=
    (Finset.card_le_card hS).trans (by simp)
  exact holds_of_column_degree_le_two conjecture_three a b hV k hcard


/-- Every signed coordinate target for a dense column determines a strict
support descent reflection at a strict order-four witness. This uses only
the support gap, not stationarity or numerical optimization. -/
theorem four_column_reflection_strict_support_descent
    (a b : Fin 4 → ℂ) (η : ℂ) (O : Matrix.orthogonalGroup (Fin 4) ℝ)
    (i k : Fin 4) (r : ℝ) (hr : r ^ 2 = 1)
    (hdiff : (fun j => O.val j k) ≠ (fun j => if j = i then r else 0))
    (hgap : ∀ p : Equiv.Perm (Fin 4), (η * matchingProduct a b p).re <
      (η * determinantValue a b (Complex.ofRealHom.mapMatrix O.val)).re) :
    ∃ u : Fin 4 → ℝ,
      (∑ j, star (u j : ℂ) * (u j : ℂ) = 1) ∧
      let U := Complex.ofRealHom.mapMatrix O.val
      let V := rankOnePhase (fun j => (u j : ℂ)) (-1) * U
      (∀ j, V j k = (if j = i then (r : ℂ) else 0)) ∧
      (η * determinantValue a b V).re < (η * determinantValue a b U).re := by
  obtain ⟨u, hu, hcol, hh⟩ := four_reflect_column_to_signed_coordinate a b O i k r hr hdiff
  obtain ⟨p, hp⟩ := (holds_iff_directional _ _ _).mp hh η
  exact ⟨u, hu, hcol, hp.trans_lt (hgap p)⟩

end

end MOC
