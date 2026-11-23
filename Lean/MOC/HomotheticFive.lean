import MOC.HomotheticFiveLaw
import MOC.SpectralZeroPadding
import MOC.Small

/-! Every real scale gives the five-point homothetic case, with arbitrary
complex axes and arbitrary mixing of added center values. -/

open BigOperators Matrix MOC.RayCoefficients

namespace MOC.HomotheticFive

def spectrum (x y : ℂ) : Fin 5 → ℂ := ![0, x, -x, y, -y]
private def ax : Fin 5 → ℤ := ![0,1,-1,0,0]
private def ay : Fin 5 → ℤ := ![0,0,0,1,-1]

private theorem spectrum_coordinates (x y : ℂ) (i : Fin 5) :
    spectrum x y i = (ax i : ℂ)*x + (ay i : ℂ)*y := by
  fin_cases i <;> simp [spectrum, ax, ay]

private def linear (v : Fin 5 → ℤ) (p : Label) (j : Fin 5) : Poly :=
  [v (FivePermutations.perm p j) + v j, v j]

private def coef (a b : Fin 5 → Poly) : Fin 6 → Poly :=
  ![(mul (a 0) (mul (a 1) (mul (a 2) (mul (a 3) (a 4))))),
    (add (mul (b 0) (mul (a 1) (mul (a 2) (mul (a 3) (a 4))))) (add (mul (a 0) (mul (b 1) (mul (a 2) (mul (a 3) (a 4))))) (add (mul (a 0) (mul (a 1) (mul (b 2) (mul (a 3) (a 4))))) (add (mul (a 0) (mul (a 1) (mul (a 2) (mul (b 3) (a 4))))) (mul (a 0) (mul (a 1) (mul (a 2) (mul (a 3) (b 4))))))))),
    (add (mul (b 0) (mul (b 1) (mul (a 2) (mul (a 3) (a 4))))) (add (mul (b 0) (mul (a 1) (mul (b 2) (mul (a 3) (a 4))))) (add (mul (b 0) (mul (a 1) (mul (a 2) (mul (b 3) (a 4))))) (add (mul (b 0) (mul (a 1) (mul (a 2) (mul (a 3) (b 4))))) (add (mul (a 0) (mul (b 1) (mul (b 2) (mul (a 3) (a 4))))) (add (mul (a 0) (mul (b 1) (mul (a 2) (mul (b 3) (a 4))))) (add (mul (a 0) (mul (b 1) (mul (a 2) (mul (a 3) (b 4))))) (add (mul (a 0) (mul (a 1) (mul (b 2) (mul (b 3) (a 4))))) (add (mul (a 0) (mul (a 1) (mul (b 2) (mul (a 3) (b 4))))) (mul (a 0) (mul (a 1) (mul (a 2) (mul (b 3) (b 4)))))))))))))),
    (add (mul (b 0) (mul (b 1) (mul (b 2) (mul (a 3) (a 4))))) (add (mul (b 0) (mul (b 1) (mul (a 2) (mul (b 3) (a 4))))) (add (mul (b 0) (mul (b 1) (mul (a 2) (mul (a 3) (b 4))))) (add (mul (b 0) (mul (a 1) (mul (b 2) (mul (b 3) (a 4))))) (add (mul (b 0) (mul (a 1) (mul (b 2) (mul (a 3) (b 4))))) (add (mul (b 0) (mul (a 1) (mul (a 2) (mul (b 3) (b 4))))) (add (mul (a 0) (mul (b 1) (mul (b 2) (mul (b 3) (a 4))))) (add (mul (a 0) (mul (b 1) (mul (b 2) (mul (a 3) (b 4))))) (add (mul (a 0) (mul (b 1) (mul (a 2) (mul (b 3) (b 4))))) (mul (a 0) (mul (a 1) (mul (b 2) (mul (b 3) (b 4)))))))))))))),
    (add (mul (b 0) (mul (b 1) (mul (b 2) (mul (b 3) (a 4))))) (add (mul (b 0) (mul (b 1) (mul (b 2) (mul (a 3) (b 4))))) (add (mul (b 0) (mul (b 1) (mul (a 2) (mul (b 3) (b 4))))) (add (mul (b 0) (mul (a 1) (mul (b 2) (mul (b 3) (b 4))))) (mul (a 0) (mul (b 1) (mul (b 2) (mul (b 3) (b 4))))))))),
    (mul (b 0) (mul (b 1) (mul (b 2) (mul (b 3) (b 4)))))]

set_option maxRecDepth 15000 in
set_option maxHeartbeats 14000000 in
private theorem coef_check : ∀ p : Label,
    let q := coef (linear ax p) (linear ay p)
    zero (q 0) = true ∧ equal (q 1) (point p 1) = true ∧
    equal (q 2) (point p 2) = true ∧ equal (q 3) (point p 3) = true ∧
    equal (q 4) (point p 4) = true ∧ zero (q 5) = true := by
  decide +kernel

private theorem expansion (s : ℝ) (x y : ℂ) (a b : Fin 5 → Poly) :
    ∏ j, ((eval s (a j) : ℂ) * x + (eval s (b j) : ℂ) * y) =
      (eval s (coef a b 0) : ℂ)*x^5 + (eval s (coef a b 1) : ℂ)*(x^4*y) +
      (eval s (coef a b 2) : ℂ)*(x^3*y^2) + (eval s (coef a b 3) : ℂ)*(x^2*y^3) +
      (eval s (coef a b 4) : ℂ)*(x*y^4) + (eval s (coef a b 5) : ℂ)*y^5 := by
  simp only [Fin.prod_univ_five, coef, Matrix.cons_val_zero', Matrix.cons_val_succ', eval_add, eval_mul]
  push_cast
  ring

private def monomial (x y : ℂ) : Axis → ℂ := ![0,x^4*y,x^3*y^2,x^2*y^3,x*y^4]

private theorem product_eq (s : ℝ) (x y : ℂ) (p : Label) :
    matchingProduct (spectrum x y) (fun j => ((1+s : ℝ) : ℂ) * spectrum x y j)
      (FivePermutations.perm p) = ∑ k, (eval s (point p k) : ℂ) * monomial x y k := by
  have hf (j : Fin 5) : spectrum x y (FivePermutations.perm p j) + ((1+s : ℝ) : ℂ) * spectrum x y j =
      (eval s (linear ax p j) : ℂ)*x + (eval s (linear ay p j) : ℂ)*y := by
    rw [spectrum_coordinates x y (FivePermutations.perm p j), spectrum_coordinates x y j]
    simp only [linear, eval, mul_zero, add_zero, Int.cast_add]
    push_cast
    ring
  rw [matchingProduct, show (∏ j, (spectrum x y (FivePermutations.perm p j) +
    ((1+s : ℝ) : ℂ) * spectrum x y j)) = ∏ j, ((eval s (linear ax p j) : ℂ)*x +
      (eval s (linear ay p j) : ℂ)*y) from Finset.prod_congr rfl (fun j _ => hf j), expansion]
  obtain ⟨h0,h1,h2,h3,h4,h5⟩ := coef_check p
  rw [eval_zero_of_check s h0, eval_eq_of_check s h1, eval_eq_of_check s h2,
    eval_eq_of_check s h3, eval_eq_of_check s h4, eval_zero_of_check s h5]
  simp [monomial, Fin.sum_univ_succ]
  <;> ring

/-- Above scale one, five matching products give the same law for all choices of the axes. -/
theorem exists_homothetic_law (s : ℝ) (hs : 0 < s)
    (U : Matrix (Fin 5) (Fin 5) ℂ) (hU : IsUnitary U) :
    ∃ (σ : Axis → FivePermutations.Perm) (w : Axis → ℝ), (∀ j, 0 ≤ w j) ∧ (∑ j, w j = 1) ∧
      ∀ x y : ℂ, ∑ j, (w j : ℂ) * matchingProduct (spectrum x y)
        (fun i => ((1+s : ℝ) : ℂ) * spectrum x y i) (σ j) =
        determinantValue (spectrum x y) (fun i => ((1+s : ℝ) : ℂ)*spectrum x y i) U := by
  obtain ⟨t,w,hw,hm,hc⟩ := exists_law s hs U hU
  refine ⟨fun j => FivePermutations.perm (vertex t j), w, hw, hm, ?_⟩
  intro x y
  let F (p : Label) := matchingProduct (spectrum x y) (fun i => ((1+s : ℝ) : ℂ)*spectrum x y i)
    (FivePermutations.perm p)
  have he : (∑ p : Label, (realSignedWeight U (FivePermutations.perm p) : ℂ)*F p) = _ :=
    (Equiv.sum_comp FivePermutations.permEquiv _).trans (real_signed_determinant _ _ U hU)
  rw [← he]
  change (∑ j, (w j : ℂ) * F (vertex t j)) = _
  simp only [F, product_eq, Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_comm (s := (Finset.univ : Finset Label))]
  apply Finset.sum_congr rfl
  intro k _
  simp_rw [← mul_assoc, ← Finset.sum_mul]
  congr 1
  exact_mod_cast hc k

private theorem holds_gt_one (r : ℝ) (hr : 1 < r) (x y : ℂ)
    (U : Matrix (Fin 5) (Fin 5) ℂ) (hU : IsUnitary U) :
    Holds (spectrum x y) (fun i => (r : ℂ)*spectrum x y i) U := by
  obtain ⟨σ,w,hw,hm,h⟩ := exists_homothetic_law (r-1) (sub_pos.mpr hr) U hU
  unfold Holds
  refine mem_convexHull_of_exists_fintype w _ hw hm (fun j => ⟨σ j, rfl⟩) ?_
  simpa only [Complex.real_smul, show 1+(r-1)=r by ring] using h x y

private theorem holds_one (x y : ℂ) (U : Matrix (Fin 5) (Fin 5) ℂ) (hU : IsUnitary U) :
    Holds (spectrum x y) (fun i => ((1 : ℝ) : ℂ)*spectrum x y i) U := by
  let S := {r : ℝ | Holds (spectrum x y) (fun i => (r : ℂ)*spectrum x y i) U}
  have hclosed : IsClosed S := by
    simp only [S, holds_iff_directional, Set.setOf_forall, Set.setOf_exists]
    refine isClosed_iInter fun z => isClosed_iUnion_of_finite fun p => ?_
    apply isClosed_le <;> simp only [determinantValue, matchingProduct] <;> fun_prop
  have hsub : Set.Ioi (1 : ℝ) ⊆ S := fun r hr => holds_gt_one r hr x y U hU
  apply closure_minimal hsub hclosed
  rw [closure_Ioi]
  exact le_rfl

private theorem holds_positive (r : ℝ) (hr : 0 < r) (x y : ℂ)
    (U : Matrix (Fin 5) (Fin 5) ℂ) (hU : IsUnitary U) :
    Holds (spectrum x y) (fun i => (r : ℂ)*spectrum x y i) U := by
  rcases lt_trichotomy r 1 with h | he | h
  · have hu : IsUnitary Uᴴ := by simpa only [IsUnitary, Matrix.conjTranspose_conjTranspose] using And.intro hU.2 hU.1
    have ht : 1 < r⁻¹ := (one_lt_inv₀ hr).mpr h
    have h' := holds_gt_one r⁻¹ ht ((r : ℂ)*x) ((r : ℂ)*y) Uᴴ hu
    have hscale : spectrum ((r : ℂ)*x) ((r : ℂ)*y) = fun i => (r : ℂ)*spectrum x y i := by
      funext i
      fin_cases i <;> simp [spectrum]
    rw [hscale] at h'
    have hn : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    apply (holds_swap_iff _ _ hU).mp
    simpa only [Complex.ofReal_inv, ← mul_assoc, inv_mul_cancel₀ hn, one_mul] using h'
  · simpa only [he] using holds_one x y U hU
  · exact holds_gt_one r h x y U hU

/-- All real scales apply to arbitrary complex axes and every relative unitary. -/
theorem holds_real (r : ℝ) (x y : ℂ) (U : Matrix (Fin 5) (Fin 5) ℂ) (hU : IsUnitary U) :
    Holds (spectrum x y) (fun i => (r : ℂ)*spectrum x y i) U := by
  rcases lt_trichotomy r 0 with h | he | h
  · let p : FivePermutations.Perm := Equiv.swap 1 2 * Equiv.swap 3 4
    have hn (i : Fin 5) : spectrum x y (p i) = -spectrum x y i := by
      fin_cases i <;> simp [spectrum, p, Equiv.Perm.mul_apply, Equiv.swap_apply_def]
    apply (holds_reindex_iff (Equiv.refl _) p _ _ U).mp
    have heq : (fun i => (r : ℂ)*spectrum x y i) ∘ p =
        (fun i => ((-r : ℝ) : ℂ)*spectrum x y i) := by
      funext i; simp only [Function.comp_apply, hn, Complex.ofReal_neg, mul_neg, neg_mul]
    rw [heq]
    exact holds_positive _ (neg_pos.mpr h) x y _ (unitary_reindex _ _ hU)
  · subst r
    apply holds_of_commute _ _ hU
    simp [Commute]
  · exact holds_positive r h x y U hU

/-- Added center values can mix with all five original labels in every higher order. -/
theorem holds_padded (m : ℕ) (r : ℝ) (x y c : ℂ)
    (U : Matrix (Fin (5+m)) (Fin (5+m)) ℂ) (hU : IsUnitary U) :
    Holds (fun i => padSpectrumWithZeros (spectrum x y) m i + c)
      (fun i => padSpectrumWithZeros (fun j => (r : ℂ)*spectrum x y j) m i - c) U := by
  apply (holds_shift_iff _ _ hU c).mpr
  have hz : spectrum x y 0 = 0 := rfl
  exact holds_all_zero_paddings_five _ _ 0 0 hz (by simp [hz]) (holds_real r x y) m U hU

end MOC.HomotheticFive
