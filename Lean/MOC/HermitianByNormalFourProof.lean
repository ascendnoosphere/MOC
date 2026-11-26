import MOC.FiveNonreal
import MOC.WeightedDiamondLowerCut01
import MOC.WeightedDiamondLowerCut02
import MOC.WeightedDiamondLowerCut03
import MOC.WeightedDiamondLowerCut04
import MOC.WeightedDiamondLowerCut05
import MOC.WeightedDiamondLowerCut06
import MOC.WeightedDiamondLowerCut07
import MOC.WeightedDiamondLowerCut08
import MOC.WeightedDiamondLowerCut09
import MOC.WeightedDiamondLowerCut10
import MOC.WeightedDiamondLowerCut11

/-! The complete lower-chart ray census and its Hermitian-by-normal consequences. -/

namespace MOC
namespace RayCoefficients

private theorem joinPath {a b c : RayStage}
    (hab : RayCensusPath a b) (hbc : RayCensusPath b c) : RayCensusPath a c := by
  induction hab with
  | refl => exact hbc
  | cons plan h hnext _ ih => exact .cons plan h hnext (ih hbc)

private theorem lowerPath :
    RayCensusPath ⟨16, weightedDiamondLowerRays1, weightedDiamondLowerImposed1⟩
      ⟨184, weightedDiamondLowerRays12, weightedDiamondLowerImposed12⟩ :=
  joinPath weightedDiamondLowerCut1 <|
  joinPath weightedDiamondLowerCut2 <|
  joinPath weightedDiamondLowerCut3 <|
  joinPath weightedDiamondLowerCut4 <|
  joinPath weightedDiamondLowerCut5 <|
  joinPath weightedDiamondLowerCut6 <|
  joinPath weightedDiamondLowerCut7 <|
  joinPath weightedDiamondLowerCut8 <|
  joinPath weightedDiamondLowerCut9 <|
  joinPath weightedDiamondLowerCut10 weightedDiamondLowerCut11

/-- The lower chart gives a complete nonnegative facet decomposition. -/
theorem weightedDiamondFacetCompleteness_lower (t : ℝ) (ht : 0 < t) :
    WeightedDiamondFacetCompletenessAt (t / (1 + t)) := by
  have hd : 0 < eval t [1, 1] := by
    simp only [eval, Int.cast_one, mul_zero, add_zero, mul_one]
    exact add_pos zero_lt_one ht
  have hchart : t / (1 + t) = eval t [0, 1] / eval t [1, 1] := by simp [eval]
  refine weightedDiamondFacetCompleteness_of_chart
    (initial := ⟨16, weightedDiamondLowerRays1, weightedDiamondLowerImposed1⟩)
    (final := ⟨184, weightedDiamondLowerRays12, weightedDiamondLowerImposed12⟩)
    ht (div_nonneg ht.le (by positivity))
    [0, 1] [1, 1] hd hchart lowerPath (weightedDiamondLowerFirstCut_generates t ht)
    weightedDiamondLowerFacet weightedDiamondLowerFacetScale weightedDiamondLowerFacetScale_positive
    ?_
  with_reducible exact weightedDiamondLowerFacet_equal

end RayCoefficients

/-- Marcus–de Oliveira inclusion for a Hermitian matrix and an arbitrary
complex normal partner in order four. -/
theorem hermitianByNormal_four : HermitianByNormal (Fin 4) :=
  RayCoefficients.hermitianByNormal_four_of_lower_diamond_chart
    RayCoefficients.weightedDiamondFacetCompleteness_lower

/-- The order-four inclusion holds when either spectrum lies on a circle or line. -/
theorem holds_four_of_generalized_circle (a b : Fin 4 → ℂ)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U)
    (h : SpectrumOnGeneralizedCircle a ∨ SpectrumOnGeneralizedCircle (fun i => -b i)) :
    Holds a b U :=
  hermitianByNormal_iff_generalized_circle.mp hermitianByNormal_four a b U hU h

/-- In any order, a Hermitian first spectrum permits at most four nonreal
partner labels. -/
theorem hermitianByNormalAtMost_four (n : ℕ) : HermitianByNormalAtMost (Fin n) 4 := by
  apply (hermitianByNormalAtMost_iff_orders_le 4).mpr ?_ n
  intro m hm
  by_cases h : m = 4
  · subst m
    exact hermitianByNormal_four
  · have hsmall : m ≤ 3 := Nat.le_of_lt_succ (lt_of_le_of_ne hm h)
    exact fun a b U hU => conjecture_le_three hsmall (fun i => (a i : ℂ)) b U hU

/-- A common circle or line can omit four partner labels in any order. -/
theorem holds_of_common_generalized_circle_with_four_outliers {n : ℕ}
    (a b : Fin n → ℂ) (outliers : Finset (Fin n)) (hcard : outliers.card ≤ 4)
    (ha : SpectrumOnGeneralizedCircle
      (Sum.elim a (fun i : {i // i ∉ outliers} => -b i.val)))
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U) : Holds a b U := by
  obtain ⟨x, f, hf, hxf⟩ := exists_real_chart_of_common_generalized_circle
    a b (fun i => i ∉ outliers) ha U hU
  apply hxf.mp
  apply hermitianByNormalAtMost_four n x (f ∘ b) U hU
  classical
  unfold nonrealCount
  refine (Finset.card_le_card ?_).trans hcard
  intro i hi
  by_contra hnot
  exact (Finset.mem_filter.mp hi).2 (hf i hnot)

/-- Five nonreal partner labels in any order reduce exactly to order five. -/
theorem hermitianByNormalAtMost_five_iff_order_five :
    (∀ n : ℕ, HermitianByNormalAtMost (Fin n) 5) ↔ HermitianByNormal (Fin 5) :=
  hermitianByNormalAtMost_five_iff.trans (and_iff_right hermitianByNormal_four)

/-- In order five, a real partner label suffices for the inclusion. -/
theorem holds_five_hermitian_of_real_partner_label (a : Fin 5 → ℝ) (b : Fin 5 → ℂ)
    (U : Matrix (Fin 5) (Fin 5) ℂ) (hU : IsUnitary U) (p : Fin 5) (hp : (b p).im = 0) :
    Holds (fun i => (a i : ℂ)) b U := by
  exact holds_of_real_pivot_of_transformed_partner a b U hU p hp
    (fun _ a' V hV => hermitianByNormal_four a' _ V hV)

/-- After the order-four base case, only orders at least five with entirely
nonreal partner spectra remain in the all-order problem. -/
theorem hermitianByNormal_iff_nonreal_partners_from_five :
    (∀ n : ℕ, HermitianByNormal (Fin n)) ↔
      ∀ (n : ℕ), 5 ≤ n →
        ∀ (a : Fin n → ℝ) (b : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ),
          IsUnitary U → (∀ i, (b i).im ≠ 0) → Holds (fun i => (a i : ℂ)) b U := by
  refine hermitianByNormal_iff_nonreal_partners.trans ⟨?_, ?_⟩
  · intro h n hn
    exact h n (by omega)
  · intro h n hn a b U hU hb
    by_cases h₅ : 5 ≤ n
    · exact h n h₅ a b U hU hb
    · have h₄ : n = 4 := by omega
      subst n
      exact hermitianByNormal_four a b U hU

/-- For order four it remains to treat two simple noncircular spectra. -/
theorem conjecture_four_iff_noncircular :
    Conjecture (Fin 4) ↔
      ∀ (a b : Fin 4 → ℂ) (U : Matrix (Fin 4) (Fin 4) ℂ), IsUnitary U →
        Function.Injective a → Function.Injective b →
        ¬ SpectrumOnGeneralizedCircle a → ¬ SpectrumOnGeneralizedCircle (fun i => -b i) →
        Holds a b U :=
  conjecture_four_iff_hermitianByNormal_and_noncircular.trans
    (and_iff_right hermitianByNormal_four)

end MOC
