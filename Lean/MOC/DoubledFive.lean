import MOC.DoubledFiveCertificate
import MOC.SpectralZeroPadding

/-! The zero-padded doubled antipodal spectra allow arbitrary complex axes
and arbitrary relative unitaries. -/

open BigOperators Matrix

namespace MOC.DoubledFive

/-- The origin and two pairs of opposite complex eigenvalues. -/
def spectrum (x y : ℂ) : Fin 5 → ℂ := ![0, x, -x, y, -y]

private def axisX : Fin 5 → ℤ := ![0, 1, -1, 0, 0]
private def axisY : Fin 5 → ℤ := ![0, 0, 0, 1, -1]

private theorem spectrum_coordinates (x y : ℂ) (i : Fin 5) :
    spectrum x y i = (axisX i : ℂ) * x + (axisY i : ℂ) * y := by
  fin_cases i <;> simp [spectrum, axisX, axisY]

private def linearX (p : Label) (j : Fin 5) : ℤ := axisX (perm p j) + 2 * axisX j
private def linearY (p : Label) (j : Fin 5) : ℤ := axisY (perm p j) + 2 * axisY j

private def quart (a b : Fin 5 → ℤ) : Fin 6 → ℤ :=
  ![a 0*a 1*a 2*a 3*a 4,
    b 0*a 1*a 2*a 3*a 4 +
      a 0*b 1*a 2*a 3*a 4 +
      a 0*a 1*b 2*a 3*a 4 +
      a 0*a 1*a 2*b 3*a 4 +
      a 0*a 1*a 2*a 3*b 4,
    b 0*b 1*a 2*a 3*a 4 +
      b 0*a 1*b 2*a 3*a 4 +
      b 0*a 1*a 2*b 3*a 4 +
      b 0*a 1*a 2*a 3*b 4 +
      a 0*b 1*b 2*a 3*a 4 +
      a 0*b 1*a 2*b 3*a 4 +
      a 0*b 1*a 2*a 3*b 4 +
      a 0*a 1*b 2*b 3*a 4 +
      a 0*a 1*b 2*a 3*b 4 +
      a 0*a 1*a 2*b 3*b 4,
    b 0*b 1*b 2*a 3*a 4 +
      b 0*b 1*a 2*b 3*a 4 +
      b 0*b 1*a 2*a 3*b 4 +
      b 0*a 1*b 2*b 3*a 4 +
      b 0*a 1*b 2*a 3*b 4 +
      b 0*a 1*a 2*b 3*b 4 +
      a 0*b 1*b 2*b 3*a 4 +
      a 0*b 1*b 2*a 3*b 4 +
      a 0*b 1*a 2*b 3*b 4 +
      a 0*a 1*b 2*b 3*b 4,
    b 0*b 1*b 2*b 3*a 4 +
      b 0*b 1*b 2*a 3*b 4 +
      b 0*b 1*a 2*b 3*b 4 +
      b 0*a 1*b 2*b 3*b 4 +
      a 0*b 1*b 2*b 3*b 4,
    b 0*b 1*b 2*b 3*b 4]

private theorem expand_product (a b : Fin 5 → ℤ) (x y : ℂ) :
    ∏ j, ((a j : ℂ) * x + (b j : ℂ) * y) =
      (quart a b 0 : ℂ) * x^5 + (quart a b 1 : ℂ) * (x^4*y) +
      (quart a b 2 : ℂ) * (x^3*y^2) + (quart a b 3 : ℂ) * (x^2*y^3) +
      (quart a b 4 : ℂ) * (x*y^4) + (quart a b 5 : ℂ) * y^5 := by
  simp only [Fin.prod_univ_five, quart, Matrix.cons_val_zero', Matrix.cons_val_succ']
  push_cast
  ring

set_option maxRecDepth 12000 in
set_option maxHeartbeats 12000000 in
private theorem raw_coordinates : ∀ p : Label,
    let c := quart (linearX p) (linearY p)
    c 0 = 0 ∧ c 1 = coord p 1 ∧ c 2 = coord p 2 ∧ c 3 = coord p 3 ∧
      c 4 = coord p 4 ∧ c 5 = 0 := by decide +kernel

private def monomial (x y : ℂ) : Fin 5 → ℂ := ![0, x^4*y, x^3*y^2, x^2*y^3, x*y^4]

private theorem product_eq (x y : ℂ) (p : Label) :
    matchingProduct (spectrum x y) (fun j => 2 * spectrum x y j) (perm p) =
      ∑ k, (coord p k : ℂ) * monomial x y k := by
  have hf (j : Fin 5) : spectrum x y (perm p j) + 2 * spectrum x y j =
      (linearX p j : ℂ) * x + (linearY p j : ℂ) * y := by
    rw [spectrum_coordinates x y (perm p j), spectrum_coordinates x y j]
    simp only [linearX, linearY, Int.cast_add, Int.cast_mul, Int.cast_ofNat]
    ring
  rw [matchingProduct, show (∏ j, (spectrum x y (perm p j) + 2 * spectrum x y j)) =
    ∏ j, ((linearX p j : ℂ) * x + (linearY p j : ℂ) * y) from
      Finset.prod_congr rfl (fun j _ => hf j), expand_product]
  obtain ⟨h0,h1,h2,h3,h4,h5⟩ := raw_coordinates p
  rw [h0,h1,h2,h3,h4,h5]
  simp [monomial, Fin.sum_univ_succ]
  <;> ring

private theorem row_match (x y : ℂ) (t : Cell) (p : Label) :
    let F := fun q => matchingProduct (spectrum x y) (fun j => 2 * spectrum x y j) (perm q)
    ∑ j, (lawCertificate.bary t j p : ℂ) * F (vertex t j) =
      (lawCertificate.denominator t : ℂ) * F p := by
  dsimp only
  simp_rw [product_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp_rw [← mul_assoc, ← Finset.sum_mul]
  congr 1
  exact_mod_cast reconstruct t p k

/-- Five matching products suffice, with the same weights for all complex axes. -/
theorem exists_doubled_law (U : Matrix (Fin 5) (Fin 5) ℂ) (hU : IsUnitary U) :
    ∃ (σ : Fin 5 → Perm) (w : Fin 5 → ℝ), (∀ j, 0 ≤ w j) ∧ ∑ j, w j = 1 ∧
      ∀ x y : ℂ, ∑ j, (w j : ℂ) * matchingProduct (spectrum x y) (fun i => 2 * spectrum x y i)
        (σ j) = determinantValue (spectrum x y) (fun i => 2 * spectrum x y i) U := by
  obtain ⟨t,w,hw,hs,hr⟩ := lawCertificate.exists_law U hU
  refine ⟨fun j => perm (vertex t j), w, hw, hs, ?_⟩
  intro x y
  let F := fun p => matchingProduct (spectrum x y) (fun i => 2 * spectrum x y i) (perm p)
  exact (hr F (fun p => row_match x y t p)).trans
    ((Equiv.sum_comp permEquiv _).trans (real_signed_determinant _ _ U hU))

theorem holds_doubled (x y : ℂ) (U : Matrix (Fin 5) (Fin 5) ℂ) (hU : IsUnitary U) :
    Holds (spectrum x y) (fun i => 2 * spectrum x y i) U := by
  obtain ⟨σ,w,hw,hs,h⟩ := exists_doubled_law U hU
  unfold Holds
  refine mem_convexHull_of_exists_fintype w _ hw hs (fun j => ⟨σ j, rfl⟩) ?_
  simpa only [Complex.real_smul] using h x y


/-- The relative unitary can mix all five original labels and any number of
extra zero labels. Opposite scalar shifts give the two centers. -/
theorem holds_padded_doubled (m : ℕ) (x y c : ℂ)
    (U : Matrix (Fin (5 + m)) (Fin (5 + m)) ℂ) (hU : IsUnitary U) :
    Holds (fun i => padSpectrumWithZeros (spectrum x y) m i + c)
      (fun i => padSpectrumWithZeros (fun j => 2 * spectrum x y j) m i - c) U := by
  apply (holds_shift_iff _ _ hU c).mpr
  have hz : spectrum x y 0 = 0 := rfl
  exact holds_all_zero_paddings_five _ _ 0 0 hz (by simp [hz]) (holds_doubled x y) m U hU

end MOC.DoubledFive
