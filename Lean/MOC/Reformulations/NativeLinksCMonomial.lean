import MOC.Claim
import MOC.Geometry
import MOC.Reformulations.FirstGeometric
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! The spectral entries are Laurent monomials evaluated at one complex torus point.
Two disjoint families of coordinate monomials realize
any pair of lists with nonzero entries. An opposite spectral shift
removes all zero entries without changing the determinant or its hull. -/

open BigOperators Matrix
namespace MOC.Reformulations

noncomputable section

/-- The value at a torus point of a Laurent monomial with integer exponent vector. -/
def laurentMonomialValue {r : ℕ} (z : Fin r → ℂ) (e : Fin r → ℤ) : ℂ :=
  ∏ i, z i ^ e i

/-- Two Laurent polynomial supports have injectively enumerated exponent vectors.
The nonzero coefficient of each support monomial can be chosen to be one. -/
def NewtonMonomialForm : Prop :=
  ∀ (r n : ℕ) (z : Fin r → ℂ) (e f : Fin n → Fin r → ℤ),
    (∀ j, z j ≠ 0) → Function.Injective e → Function.Injective f →
    ∀ (U : Matrix (Fin n) (Fin n) ℂ), IsUnitary U →
    Holds (fun i => laurentMonomialValue z (e i))
      (fun i => laurentMonomialValue z (f i)) U

private theorem monomial_single {r : ℕ} (z : Fin r → ℂ) (j : Fin r) :
    laurentMonomialValue z (Pi.single j (1 : ℤ)) = z j := by
  unfold laurentMonomialValue
  rw [Finset.prod_eq_single j]
  · simp
  · intro i _ hi
    simp [Pi.single_apply, hi.symm]
  · simp

/-- The comparison on the homogeneous coordinate section weights of two line bundles.
Use independent torus coordinates for the sections of the two line bundles. -/
def ProjectiveToricSectionForm : Prop :=
  ∀ (n : ℕ) (z : Fin (n + n) → ℂ), (∀ i, z i ≠ 0) →
    ∀ (U : Matrix (Fin n) (Fin n) ℂ), IsUnitary U →
    Holds (fun i => laurentMonomialValue z (Pi.single (Fin.castAdd n i) (1 : ℤ)))
      (fun i => laurentMonomialValue z (Pi.single (Fin.natAdd n i) (1 : ℤ))) U

theorem projectiveToricSectionForm_iff : ProjectiveToricSectionForm ↔ MOCIsTrue := by
  classical
  constructor
  · intro h
    apply moc_iff_nonzeroSpectra.mpr
    intro n a b U hU ha hb
    let z : Fin (n + n) → ℂ := Fin.addCases a b
    have hleft (i : Fin n) : z (Fin.castAdd n i) = a i := Fin.addCases_left i
    have hright (i : Fin n) : z (Fin.natAdd n i) = b i := Fin.addCases_right i
    have hz (i : Fin (n + n)) : z i ≠ 0 :=
      Fin.addCases (fun j => by rw [hleft]; exact ha j)
        (fun j => by rw [hright]; exact hb j) i
    simpa only [monomial_single, hleft, hright] using h n z hz U hU
  · intro h n z _ U hU
    exact h n _ _ U hU

/-- Compare actual monomial evaluations at an actual complex torus point.
There is no free spectral evaluation map and no density or limiting argument. -/
theorem newtonMonomialForm_iff : NewtonMonomialForm ↔ MOCIsTrue := by
  classical
  constructor
  · intro h n a b U hU
    have hf : (Set.range (fun i => -a i) ∪ Set.range b).Finite :=
      (Set.finite_range _).union (Set.finite_range _)
    obtain ⟨t, _, ht⟩ := Set.infinite_univ.exists_not_mem_finite hf
    have ha : ∀ i, a i + t ≠ 0 := by
      intro i hi
      exact ht (Or.inl ⟨i, (eq_neg_of_add_eq_zero_right hi).symm⟩)
    have hb : ∀ j, b j - t ≠ 0 := by
      intro j hj
      exact ht (Or.inr ⟨j, sub_eq_zero.mp hj⟩)
    let z : Fin (n + n) → ℂ := Fin.addCases (fun i => a i + t) (fun j => b j - t)
    have hz (i : Fin (n + n)) : z i ≠ 0 := by
      refine Fin.addCases (m := n) (n := n) ?_ ?_ i
      · intro j
        simpa [z] using ha j
      · intro j
        change z (Fin.natAdd n j) ≠ 0
        rw [show z (Fin.natAdd n j) = b j - t from Fin.addCases_right j]
        exact hb j
    let e (i : Fin n) : Fin (n + n) → ℤ := Pi.single (Fin.castAdd n i) 1
    let f (i : Fin n) : Fin (n + n) → ℤ := Pi.single (Fin.natAdd n i) 1
    have he : Function.Injective e := by
      intro i j hij
      by_cases hne : i = j
      · exact hne
      have hh := congrFun hij (Fin.castAdd n i)
      simp [e, Pi.single_apply, hne, Ne.symm hne] at hh
    have hf' : Function.Injective f := by
      intro i j hij
      by_cases hne : i = j
      · exact hne
      have hh := congrFun hij (Fin.natAdd n i)
      simp [f, Pi.single_apply, hne, Ne.symm hne] at hh
    have hv := h (n + n) n z e f hz he hf' U hU
    have heval : (fun i => laurentMonomialValue z (e i)) = fun i => a i + t := by
      funext i
      simp [e, monomial_single, z]
    have hfeval : (fun i => laurentMonomialValue z (f i)) = fun i => b i - t := by
      funext i
      simp only [f, monomial_single]
      exact Fin.addCases_right i
    rw [heval, hfeval] at hv
    exact (holds_shift_iff a b hU t).mp hv
  · intro h r n z e f _ _ _ U hU
    exact h n _ _ U hU

theorem not_newtonMonomialForm_iff : ¬ NewtonMonomialForm ↔ ¬ MOCIsTrue :=
  not_congr newtonMonomialForm_iff

end
end MOC.Reformulations
