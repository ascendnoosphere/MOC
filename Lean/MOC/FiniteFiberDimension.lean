import MOC.PolynomialEvaluationHeight
import MOC.FiniteCurveAtPinnedPrime
import MOC.FiniteCurveCofiniteImage

/-! A finite fiber cannot remove more affine dimension than its equations.
An open condition can be imposed by adding one inverse variable and one
equation, with no net cost in the count. -/

open MvPolynomial Set

namespace MOC

variable {σ κ : Type*} [Fintype σ] [Fintype κ]

/-- If one nonempty fiber of a polynomial map, intersected with the zero
locus of the auxiliary equations, is finite, the coordinates of the map
and the auxiliary equations together number at least as many as the
ambient variables. Only that fiber must be finite. -/
theorem le_dimension_of_finite_polynomial_fiber
    (B : Finset (MvPolynomial σ ℂ)) (F : κ → MvPolynomial σ ℂ)
    (z : σ → ℂ) (hz : ∀ b ∈ B, eval z b = 0)
    (hfin : {x : σ → ℂ | (∀ b ∈ B, eval x b = 0) ∧
      ∀ j, eval x (F j) = eval z (F j)}.Finite) :
    Fintype.card σ ≤ B.card + Fintype.card κ := by
  classical
  by_contra! hbudget
  let G (j : κ) := F j - C (eval z (F j))
  let E := B ∪ Finset.univ.image G
  have hEb : E.card < Fintype.card σ := by
    have hcard := Finset.card_union_le B (Finset.univ.image G)
    change (B ∪ Finset.univ.image G).card < Fintype.card σ
    have himg : (Finset.univ.image G).card ≤ Fintype.card κ := by
      simpa only [Finset.card_univ] using Finset.card_image_le (f := G) (s := Finset.univ)
    omega
  have hEz (p) (hp : p ∈ E) : eval z p = 0 := by
    rcases Finset.mem_union.mp hp with h | h
    · exact hz p h
    · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp h
      simp [G]
  obtain ⟨I, hI, hE⟩ := exists_prime_lt_polynomial_eval_of_few_equations z E hEz hEb
  obtain ⟨g, _, hg⟩ := SetLike.exists_of_lt hI
  obtain ⟨Q, hIQ, _, hQprime, _, f, hf, hfi, t, ht⟩ :=
    @exists_finite_affine_curve_from_prime_below_point σ _ z I.asIdeal I.isPrime hI g hg
  letI : Q.IsPrime := hQprime
  have hcurve : Infinite (zeroLocus Q) :=
    Infinite.of_surjective _ (surjective_finite_affine_projection Q f hf hfi t ht)
  letI := hcurve
  have hEQ (p) (hp : p ∈ E) : p ∈ Q := hIQ (hE (Ideal.subset_span hp))
  have hsub : zeroLocus Q ⊆ {x : σ → ℂ | (∀ b ∈ B, eval x b = 0) ∧
      ∀ j, eval x (F j) = eval z (F j)} := by
    intro x hx
    refine ⟨fun b hb => hx b (hEQ b (Finset.mem_union_left _ hb)), fun j => ?_⟩
    have hj := hx (G j) (hEQ _ (Finset.mem_union_right _
      (Finset.mem_image_of_mem G (Finset.mem_univ j))))
    simpa only [G, map_sub, eval_C, sub_eq_zero] using hj
  exact (Set.infinite_coe_iff.mp hcurve) (hfin.subset hsub)


end MOC

namespace MOC

variable {σ τ κ : Type*} [Fintype σ] [Fintype τ] [Fintype κ]

omit [Fintype κ] in
/-- A finite polynomial normalization has finite point fibers over
every base value, not just when the base has one variable. -/
theorem finite_points_over_finite_multivariate_projection
    (Q : Ideal (MvPolynomial τ ℂ))
    (f : MvPolynomial κ ℂ →ₐ[ℂ] (MvPolynomial τ ℂ ⧸ Q)) (hf : f.Finite)
    (t : κ → MvPolynomial τ ℂ) (ht : ∀ j, Ideal.Quotient.mk Q (t j) = f (X j))
    (a : κ → ℂ) :
    {z : τ → ℂ | z ∈ zeroLocus Q ∧ ∀ j, eval z (t j) = a j}.Finite := by
  let A := MvPolynomial κ ℂ
  let B := MvPolynomial τ ℂ ⧸ Q
  letI : Algebra A B := f.toRingHom.toAlgebra
  letI : Module.Finite A B := hf
  let x (i : τ) : B := Ideal.Quotient.mk Q (X i)
  have hInt (i : τ) := Algebra.IsIntegral.isIntegral (R := A) (x i)
  choose P hMonic hRoot using hInt
  have hfin (i : τ) : {v : ℂ | ((P i).map (eval a)).IsRoot v}.Finite :=
    Polynomial.finite_setOf_isRoot (((hMonic i).map _).ne_zero)
  refine (Set.Finite.pi' hfin).subset fun z hz i => ?_
  let φ : B →ₐ[ℂ] ℂ := Ideal.Quotient.liftₐ Q (aeval z) fun r hr => hz.1 r hr
  have hφ (r : MvPolynomial τ ℂ) : φ (Ideal.Quotient.mk Q r) = eval z r := rfl
  have hφx : φ (x i) = z i := (hφ (X i)).trans (eval_X i)
  have he : φ.comp f = aeval a := by
    apply MvPolynomial.algHom_ext
    intro j
    change φ (f (X j)) = aeval a (X j)
    rw [← ht, hφ, aeval_X, hz.2]
  have he' : φ.toRingHom.comp (algebraMap A B) = eval a :=
    congrArg AlgHom.toRingHom he
  have h := (Polynomial.hom_eval₂ (p := P i) (f := algebraMap A B)
    (g := φ.toRingHom) (x i)).symm.trans
    ((congrArg φ.toRingHom (hRoot i)).trans (map_zero _))
  rw [he', show φ.toRingHom (x i) = z i from hφx] at h
  simpa only [Polynomial.IsRoot, Polynomial.eval_map] using h

/-- Any finite normalization of a complex affine target has at least as
many variables as an injective chart of it, after subtracting the number
of auxiliary chart equations. The chart need not contain every point or
be open in the target. -/
theorem le_base_dimension_of_injective_polynomial_chart
    (Q : Ideal (MvPolynomial τ ℂ))
    (f : MvPolynomial κ ℂ →ₐ[ℂ] (MvPolynomial τ ℂ ⧸ Q)) (hf : f.Finite)
    (B : Finset (MvPolynomial σ ℂ)) (F : τ → MvPolynomial σ ℂ)
    (z : σ → ℂ) (hz : ∀ b ∈ B, eval z b = 0)
    (hland : Set.MapsTo (fun x j => eval x (F j))
      {x : σ → ℂ | ∀ b ∈ B, eval x b = 0} (zeroLocus Q))
    (hinj : Set.InjOn (fun x j => eval x (F j))
      {x : σ → ℂ | ∀ b ∈ B, eval x b = 0}) :
    Fintype.card σ ≤ B.card + Fintype.card κ := by
  classical
  choose t ht using fun j : κ => Ideal.Quotient.mk_surjective (f (X j))
  let A (x : σ → ℂ) (j : τ) := eval x (F j)
  let G (j : κ) := aeval F (t j)
  let S := {x : σ → ℂ | (∀ b ∈ B, eval x b = 0) ∧
    ∀ j, eval x (G j) = eval z (G j)}
  have hG (x : σ → ℂ) (j : κ) : eval x (G j) = eval (A x) (t j) :=
    MvPolynomial.comp_aeval_apply F (aeval x) (t j)
  have hfin := finite_points_over_finite_multivariate_projection Q f hf t ht
    (fun j => eval (A z) (t j))
  apply le_dimension_of_finite_polynomial_fiber B G z hz
  apply Set.Finite.of_finite_image (f := A)
  · apply hfin.subset
    rintro p ⟨x, hx, rfl⟩
    refine ⟨hland hx.1, fun j => ?_⟩
    rw [← hG, ← hG, hx.2 j]
  · exact hinj.mono fun x hx => hx.1


end MOC
