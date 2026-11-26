import MOC.Reformulations.Compounds
import MOC.OrderFiveCommonLawObstruction
import MOC.FourMatchingMarginalObstructions

/-! Intersection with a divided divisor power in the squarefree monomial
model of the cohomology of a product of projective lines. -/

open BigOperators Finset Matrix

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Coefficients of the monomials `x_I y_J` with square-zero generators. -/
abbrev SquarefreeClass (ι : Type*) := Finset ι → Finset ι → ℂ

/-- Multiply in the squarefree basis. Each summand chooses disjoint factors
whose union is the output monomial. -/
def squarefreeClassProduct (u v : SquarefreeClass ι) : SquarefreeClass ι :=
  fun K L => ∑ I ∈ K.powerset, ∑ J ∈ L.powerset, u I J * v (K \ I) (L \ J)

/-- The coefficient of the product of all generators. -/
def squarefreeIntegral (u : SquarefreeClass ι) : ℂ := u univ univ

/-- The divided middle power of a divisor in the squarefree basis. In
characteristic zero, each squarefree monomial occurs in `n!` orders in
the ordinary power, where `n` is the number of labels. -/
def squarefreeDividedDivisor (a b : ι → ℂ) : SquarefreeClass ι :=
  fun I J => if Iᶜ.card = J.card then (∏ i ∈ I, a i) * ∏ j ∈ J, b j else 0

/-- The squarefree correspondence class, with coefficient of `x_I y_J`
equal to the squared minor with column set `Jᶜ`. -/
def unitaryCorrespondenceClass (U : Matrix ι ι ℂ) : SquarefreeClass ι :=
  fun I J => subsetMinorSq U I Jᶜ

theorem unitaryCorrespondenceClass_coeff_nonneg (U : Matrix ι ι ℂ) (I J : Finset ι) :
    0 ≤ (unitaryCorrespondenceClass U I J).re := by
  simpa only [unitaryCorrespondenceClass, Complex.ofReal_re] using subsetMinorSq_nonneg U I Jᶜ

/-- Graph correspondence in the column-to-row permutation convention. -/
def matchingCorrespondenceClass (σ : Equiv.Perm ι) : SquarefreeClass ι :=
  fun I J => if Jᶜ.map σ.toEmbedding = I then 1 else 0

private def complementSubset : Equiv.Perm (Finset ι) where
  toFun := (·ᶜ)
  invFun := (·ᶜ)
  left_inv := compl_compl
  right_inv := compl_compl

private theorem intersection_reindex (u : SquarefreeClass ι) (a b : ι → ℂ) :
    squarefreeIntegral (squarefreeClassProduct u (squarefreeDividedDivisor a b)) =
      ∑ J : Finset ι, ∑ I : Finset ι, u I Jᶜ * squarefreeDividedDivisor a b Iᶜ J := by
  unfold squarefreeIntegral squarefreeClassProduct
  simp only [Finset.powerset_univ, ← Finset.compl_eq_univ_sdiff]
  rw [Finset.sum_comm]
  calc
    _ = ∑ J : Finset ι, (fun L : Finset ι =>
          ∑ I : Finset ι, u I L * squarefreeDividedDivisor a b Iᶜ Lᶜ)
          (complementSubset J) := (Equiv.sum_comp complementSubset _).symm
    _ = _ := by simp only [complementSubset, Equiv.coe_fn_mk, compl_compl]

/-- Integrating the squared-minor class against the divided divisor power
gives the determinant. -/
theorem squarefreeIntersection_unitary (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) :
    squarefreeIntegral (squarefreeClassProduct (unitaryCorrespondenceClass U)
      (squarefreeDividedDivisor a b)) = determinantValue a b U := by
  rw [intersection_reindex, determinantValue_eq_sum_subsetMinors a b U hU]
  apply Finset.sum_congr rfl
  intro J _
  apply Finset.sum_congr rfl
  intro I _
  by_cases h : I.card = J.card
  · simp only [unitaryCorrespondenceClass, squarefreeDividedDivisor, compl_compl, h, if_true]
  · simp only [unitaryCorrespondenceClass, squarefreeDividedDivisor, compl_compl, h, if_false,
      mul_zero]
    simp [subsetMinorSq, h]

/-- Integrating a graph correspondence gives its matching product. -/
theorem squarefreeIntersection_matching (a b : ι → ℂ) (σ : Equiv.Perm ι) :
    squarefreeIntegral (squarefreeClassProduct (matchingCorrespondenceClass σ)
      (squarefreeDividedDivisor a b)) = matchingProduct a b σ := by
  rw [intersection_reindex, matchingProduct_expand_subsets]
  apply Finset.sum_congr rfl
  intro J _
  simp only [matchingCorrespondenceClass, compl_compl]
  rw [Finset.sum_eq_single (J.map σ.toEmbedding)]
  · simp [squarefreeDividedDivisor]
  · intro I _ hI
    simp [hI, Ne.symm hI]
  · simp

/-- The convex hull test on each divided divisor power is equivalent to
the ordinary determinant conjecture in the same order. -/
theorem conjecture_iff_squarefreeIntersectionHull : Conjecture ι ↔
    ∀ (U : Matrix ι ι ℂ), IsUnitary U → ∀ a b : ι → ℂ,
      squarefreeIntegral (squarefreeClassProduct (unitaryCorrespondenceClass U)
        (squarefreeDividedDivisor a b)) ∈ convexHull ℝ (Set.range fun σ : Equiv.Perm ι =>
          squarefreeIntegral (squarefreeClassProduct (matchingCorrespondenceClass σ)
            (squarefreeDividedDivisor a b))) := by
  constructor
  · intro h U hU a b
    simpa only [squarefreeIntersection_unitary a b U hU, squarefreeIntersection_matching] using
      h a b U hU
  · intro h a b U hU
    simpa only [squarefreeIntersection_unitary a b U hU, squarefreeIntersection_matching] using
      h U hU a b

/-- Membership of the full correspondence class in the graph hull gives
one matching law for all spectral observations. -/
theorem universalMatchingWeights_of_squarefreeGraphHull (U : Matrix ι ι ℂ)
    (hU : IsUnitary U)
    (h : unitaryCorrespondenceClass U ∈ convexHull ℝ
      (Set.range (matchingCorrespondenceClass : Equiv.Perm ι → SquarefreeClass ι))) :
    HasUniversalMatchingWeights U := by
  classical
  obtain ⟨κ, inst, w, z, hw, hs, hz, he⟩ := mem_convexHull_iff_exists_fintype.mp h
  letI : Fintype κ := inst
  choose p hp using hz
  apply universalMatchingWeights_of_indexed p w hw hs
  intro a b
  symm
  apply determinantValue_eq_sum_of_indexed_minor_law a b U hU p w
  intro I J
  have hcoord := congrArg (fun v : SquarefreeClass ι => (v I Jᶜ).re) he
  simp only [Finset.sum_apply, Pi.smul_apply, Complex.real_smul, Complex.re_sum,
    Complex.re_ofReal_mul, unitaryCorrespondenceClass, compl_compl, Complex.ofReal_re] at hcoord
  rw [← hcoord, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k _
  rw [← hp k]
  by_cases hk : J.map (p k).toEmbedding = I <;>
    simp [matchingCorrespondenceClass, hk]

/-- The order-four rational mixer is outside the full squarefree graph hull. -/
theorem fourMarginalMixer_outside_squarefreeGraphHull :
    unitaryCorrespondenceClass fourMarginalMixer ∉ convexHull ℝ
      (Set.range (matchingCorrespondenceClass : Equiv.Perm (Fin 4) → SquarefreeClass (Fin 4))) :=
  fun h => fourMarginalMixer_no_universal_weights
    (universalMatchingWeights_of_squarefreeGraphHull _ fourMarginalMixer_unitary h)

/-- The order-five flat reflection passes every squarefree intersection test
and lies outside the convex hull of the full graph classes. -/
theorem orderFiveFlatReflection_separates_squarefreeIntersectionHull :
    (∀ a b : Fin 5 → ℂ,
      squarefreeIntegral (squarefreeClassProduct (unitaryCorrespondenceClass orderFiveFlatReflection)
        (squarefreeDividedDivisor a b)) ∈ convexHull ℝ
        (Set.range fun σ : Equiv.Perm (Fin 5) =>
          squarefreeIntegral (squarefreeClassProduct (matchingCorrespondenceClass σ)
            (squarefreeDividedDivisor a b)))) ∧
    unitaryCorrespondenceClass orderFiveFlatReflection ∉ convexHull ℝ
      (Set.range (matchingCorrespondenceClass : Equiv.Perm (Fin 5) → SquarefreeClass (Fin 5))) := by
  constructor
  · intro a b
    simpa only [squarefreeIntersection_unitary a b _ unitary_orderFiveFlatReflection,
      squarefreeIntersection_matching] using orderFiveFlatReflection_holds a b
  · intro h
    obtain ⟨w, hw, hs, hd⟩ :=
      universalMatchingWeights_of_squarefreeGraphHull _ unitary_orderFiveFlatReflection h
    exact orderFiveFlatReflection_no_positive_all_spectral_law
      ⟨w, hw, hs, fun a b => (hd a b).symm⟩

end

end MOC
