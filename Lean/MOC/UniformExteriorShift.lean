import MOC.SmallSpectralPerturbation

/-!
# Uniform exterior shifts for complex spectra

For fixed complex spectral lists, general position of the assignment sums
gives one exterior disk where the determinant inclusion holds for every
relative unitary. The normalized matching polynomials use the reciprocal
shift parameter.
-/

open BigOperators Finset Matrix Polynomial

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [Fintype ι] in
private theorem exterior_product_difference (u v : ι → ℂ) (S : Finset ι) :
    ∃ Q : ℂ[X], Q.eval 0 = ∑ j ∈ S, u j * v j ∧
      (∏ j ∈ S, (1 + C (u j) * X) * (1 + C (v j) * X)) =
        (∏ j ∈ S, (1 + C (u j + v j) * X)) + X ^ 2 * Q := by
  classical
  let A (j : ι) : ℂ[X] := (1 + C (u j) * X) * (1 + C (v j) * X)
  let B (j : ι) : ℂ[X] := 1 + C (u j + v j) * X
  have ha (j : ι) : A j = B j + X ^ 2 * C (u j * v j) := by
    dsimp [A, B]
    rw [map_add, map_mul]
    ring
  change ∃ Q : ℂ[X], Q.eval 0 = ∑ j ∈ S, u j * v j ∧
    (∏ j ∈ S, A j) = (∏ j ∈ S, B j) + X ^ 2 * Q
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp, by simp⟩
  | @insert j S hj ih =>
    obtain ⟨Q, hQ₀, hQ⟩ := ih
    refine ⟨B j * Q + C (u j * v j) * (∏ k ∈ S, A k), ?_, ?_⟩
    · simp [A, B, eval_prod, hQ₀, sum_insert hj, add_comm]
    · rw [prod_insert hj, prod_insert hj, ha]
      calc
        _ = B j * (∏ k ∈ S, A k) + X ^ 2 * (C (u j * v j) * (∏ k ∈ S, A k)) := by
          ring
        _ = _ := by
          rw [hQ]
          ring

private theorem exterior_matching_polynomials (a b : ι → ℂ) :
    ∃ (F : ℂ[X]) (Q : Equiv.Perm ι → ℂ[X]), ∀ π,
      (Q π).eval 0 = reciprocalAssignmentSum a b π ∧
      ∀ t : ℂ, (∏ j, (1 + t * (a (π j) + b j))) = F.eval t - t ^ 2 * (Q π).eval t := by
  classical
  let F : ℂ[X] := (∏ j, (1 + C (a j) * X)) * ∏ j, (1 + C (b j) * X)
  have he (π : Equiv.Perm ι) :
      F = ∏ j, (1 + C (a (π j)) * X) * (1 + C (b j) * X) := by
    unfold F
    rw [Finset.prod_mul_distrib, Equiv.prod_comp π (fun j => 1 + C (a j) * X)]
  have h (π : Equiv.Perm ι) := exterior_product_difference (a ∘ π) b univ
  choose Q hQ using h
  refine ⟨F, Q, fun π => ⟨(hQ π).1, fun t => ?_⟩⟩
  have hp := congrArg (eval t) ((he π).trans (hQ π).2)
  simp only [Function.comp_apply, eval_add, eval_mul, eval_pow, eval_prod, eval_C,
    eval_X, eval_one] at hp
  simpa only [mul_comm t] using (eq_sub_of_add_eq (Eq.symm hp))

/-- A single exterior radius works for every unitary when the assignment sums
of the two fixed spectra are distinct and no three are collinear. -/
theorem holds_uniform_exterior_shift (a b : ι → ℂ)
    (hgeneric : ReciprocalAssignmentsInGeneralPosition a b) :
    ∃ R : ℝ, 0 < R ∧ ∀ (z : ℂ), R < ‖z‖ → ∀ (U : Matrix ι ι ℂ),
      IsUnitary U → Holds (fun i => a i + z) b U := by
  obtain ⟨F, Q, hQ⟩ := exterior_matching_polynomials a b
  obtain ⟨r, hr, hnear⟩ := supported_polynomial_near_zero a b hgeneric Q (fun π => (hQ π).1)
  refine ⟨r⁻¹, inv_pos.mpr hr, fun z hz U hU => ?_⟩
  have hznorm : 0 < ‖z‖ := (inv_pos.mpr hr).trans hz
  have hzne : z ≠ 0 := norm_pos_iff.mp hznorm
  have ht : ‖z⁻¹‖ < r := by
    rw [norm_inv]
    simpa only [inv_inv] using (inv_lt_inv₀ hznorm (inv_pos.mpr hr)).mpr hz
  let k := z ^ Fintype.card ι
  apply holds_of_affine_signed_support (fun i => a i + z) b U hU
    (k * F.eval z⁻¹) (-(k * (z⁻¹) ^ 2)) (fun π => (Q π).eval z⁻¹)
  · intro π
    calc
      matchingProduct (fun i => a i + z) b π =
          ∏ j, z * (1 + z⁻¹ * (a (π j) + b j)) := by
        unfold matchingProduct
        apply Finset.prod_congr rfl
        intro j _
        rw [mul_add, mul_one, ← mul_assoc, mul_inv_cancel₀ hzne, one_mul]
        ring
      _ = k * ∏ j, (1 + z⁻¹ * (a (π j) + b j)) := by
        rw [Finset.prod_mul_distrib]
        simp [k]
      _ = _ := by rw [(hQ π).2]; ring
  exact fun η hη => hnear z⁻¹ ht η hη U hU

end

end MOC
