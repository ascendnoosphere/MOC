import MOC.SquarefreeIntersection
import Mathlib.Algebra.Polynomial.Roots

/-! Marginal values and complement symmetry of a balanced squarefree
spectral polynomial under opposite scalar translation. -/

open BigOperators Finset

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Evaluate the degree-`card ι` part of a squarefree coefficient array on
two lists of spectral variables. -/
def squarefreeSpectralValue (c : SquarefreeClass ι) (a b : ι → ℂ) : ℂ :=
  ∑ I : Finset ι, ∑ J : Finset ι, c I J * squarefreeDividedDivisor a b I J

/-- Only the balanced monomial on these two supports can contribute. -/
theorem squarefreeSpectralValue_on_support (c : SquarefreeClass ι)
    (a b : ι → ℂ) (I J : Finset ι) (hIJ : Iᶜ.card = J.card)
    (ha : ∀ i ∉ I, a i = 0) (hb : ∀ j ∉ J, b j = 0) :
    squarefreeSpectralValue c a b =
      c I J * ((∏ i ∈ I, a i) * ∏ j ∈ J, b j) := by
  have hterm (K L : Finset ι) (hne : K ≠ I ∨ L ≠ J) :
      c K L * squarefreeDividedDivisor a b K L = 0 := by
    by_cases hKL : Kᶜ.card = L.card
    · rw [squarefreeDividedDivisor, if_pos hKL]
      by_cases hKI : K ⊆ I
      · by_cases hLJ : L ⊆ J
        · have hK := Finset.card_le_card hKI
          have hL := Finset.card_le_card hLJ
          have hKc := Finset.card_add_card_compl K
          have hIc := Finset.card_add_card_compl I
          have heK : K = I := Finset.eq_of_subset_of_card_le hKI (by omega)
          have heL : L = J := Finset.eq_of_subset_of_card_le hLJ (by omega)
          exact (hne.elim (fun h => h heK) (fun h => h heL)).elim
        · obtain ⟨j, hjL, hjJ⟩ := Finset.not_subset.mp hLJ
          rw [Finset.prod_eq_zero hjL (hb j hjJ), mul_zero, mul_zero]
      · obtain ⟨i, hiK, hiI⟩ := Finset.not_subset.mp hKI
        rw [Finset.prod_eq_zero hiK (ha i hiI), zero_mul, mul_zero]
    · simp only [squarefreeDividedDivisor, hKL, if_false, mul_zero]
  unfold squarefreeSpectralValue
  rw [Finset.sum_eq_single_of_mem I (Finset.mem_univ I)]
  · rw [Finset.sum_eq_single_of_mem J (Finset.mem_univ J)]
    · simp only [squarefreeDividedDivisor, hIJ, if_true]
    · intro L _ hL
      exact hterm I L (Or.inr hL)
  · intro K _ hK
    simp only [fun L => hterm K L (Or.inl hK), Finset.sum_const_zero]

/-- Unit pure coefficients and opposite translation give the two marginal
polynomials. The translation premise applies to complex inputs. -/
theorem squarefreeSpectralValue_marginals_of_opposite_translation
    (c : SquarefreeClass ι) (hA : c univ ∅ = 1) (hB : c ∅ univ = 1)
    (hshift : ∀ (a b : ι → ℂ) (t : ℂ),
      squarefreeSpectralValue c (fun i => a i + t) (fun j => b j - t) =
        squarefreeSpectralValue c a b) (a b : ι → ℂ) :
    squarefreeSpectralValue c a (fun _ => 1) = (∏ i, (a i + 1)) ∧
      squarefreeSpectralValue c (fun _ => 1) b = ∏ j, (b j + 1) := by
  constructor
  · have he := hshift a (fun _ => 1) 1
    simp only [sub_self] at he
    rw [← he, squarefreeSpectralValue_on_support c (fun i => a i + 1) (fun _ => 0)
      univ ∅ (by simp) (by simp) (by simp)]
    simp only [hA, Finset.prod_empty, mul_one, one_mul]
  · have he := hshift (fun _ => 1) b (-1)
    simp only [add_neg_cancel, sub_neg_eq_add] at he
    rw [← he, squarefreeSpectralValue_on_support c (fun _ => 0) (fun j => b j + 1)
      ∅ univ (by simp) (by simp) (by simp)]
    simp only [hB, Finset.prod_empty, one_mul]

private def constantOn (I : Finset ι) (z : ℂ) (i : ι) : ℂ := if i ∈ I then z else 0

private theorem prod_constantOn (I : Finset ι) (z : ℂ) :
    ∏ i ∈ I, constantOn I z i = z ^ I.card := by
  calc
    _ = ∏ _i ∈ I, z := Finset.prod_congr rfl fun i hi => by
      simp only [constantOn, hi, if_true]
    _ = _ := Finset.prod_const _

private theorem squarefreeSpectralValue_constantOn (c : SquarefreeClass ι)
    (I J : Finset ι) (hIJ : Iᶜ.card = J.card) (u v : ℂ) :
    squarefreeSpectralValue c (constantOn I u) (constantOn J v) =
      c I J * (u ^ I.card * v ^ J.card) := by
  rw [squarefreeSpectralValue_on_support c (constantOn I u) (constantOn J v) I J hIJ
    (fun _ hi => if_neg hi) (fun _ hj => if_neg hj)]
  simp only [prod_constantOn]

/-- Opposite translation equates complementary coefficients. The two
evaluations use only the monomials on the two complementary supports. -/
theorem squarefreeSpectralValue_complement_of_opposite_translation
    (c : SquarefreeClass ι)
    (hshift : ∀ (a b : ι → ℂ) (t : ℂ),
      squarefreeSpectralValue c (fun i => a i + t) (fun j => b j - t) =
        squarefreeSpectralValue c a b)
    (I J : Finset ι) (hIJ : Iᶜ.card = J.card) : c I J = c Iᶜ Jᶜ := by
  have hIc := Finset.card_add_card_compl I
  have hJc := Finset.card_add_card_compl J
  have hsign : I.card = Jᶜ.card := by omega
  have hcompl : (Iᶜ)ᶜ.card = Jᶜ.card := by rw [compl_compl, hsign]
  have ha : (fun i => constantOn I (-1) i + 1) = constantOn Iᶜ 1 := by
    funext i
    by_cases hi : i ∈ I <;> simp [constantOn, hi]
  have hb : (fun j => constantOn J 1 j - 1) = constantOn Jᶜ (-1) := by
    funext j
    by_cases hj : j ∈ J <;> simp [constantOn, hj]
  have he := hshift (constantOn I (-1)) (constantOn J 1) 1
  rw [ha, hb, squarefreeSpectralValue_constantOn c Iᶜ Jᶜ hcompl,
    squarefreeSpectralValue_constantOn c I J hIJ] at he
  simp only [one_pow, one_mul, mul_one, ← hsign] at he
  exact (mul_right_cancel₀ (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) he).symm

/-- A left subset has total coefficient one if the two pure coefficients
are one and the value is invariant under opposite translations. -/
theorem squarefreeSpectralValue_left_coefficient_sum
    (c : SquarefreeClass ι) (hA : c univ ∅ = 1) (hB : c ∅ univ = 1)
    (hshift : ∀ (a b : ι → ℂ) (t : ℂ),
      squarefreeSpectralValue c (fun i => a i + t) (fun j => b j - t) =
        squarefreeSpectralValue c a b)
    (I : Finset ι) : (∑ J : Finset ι, if Iᶜ.card = J.card then c I J else 0) = 1 := by
  classical
  let p : Polynomial ℂ :=
    ∑ K : Finset ι, ∑ L : Finset ι,
      if K ⊆ I ∧ Kᶜ.card = L.card then Polynomial.C (c K L) * Polynomial.X ^ K.card else 0
  have heval (t : ℂ) : p.eval t = squarefreeSpectralValue c (constantOn I t) (fun _ => 1) := by
    simp only [p, Polynomial.eval_finset_sum, squarefreeSpectralValue]
    apply Finset.sum_congr rfl
    intro K _
    apply Finset.sum_congr rfl
    intro L _
    by_cases hKL : Kᶜ.card = L.card
    · by_cases hKI : K ⊆ I
      · have hp : ∏ i ∈ K, constantOn I t i = t ^ K.card := calc
          _ = ∏ _i ∈ K, t := Finset.prod_congr rfl fun i hi => if_pos (hKI hi)
          _ = _ := Finset.prod_const _
        simp only [hKI, hKL, true_and, if_true, squarefreeDividedDivisor,
          Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X,
          hp, Finset.prod_const_one, mul_one]
      · obtain ⟨i, hiK, hiI⟩ := Finset.not_subset.mp hKI
        have hz : ∏ j ∈ K, constantOn I t j = 0 := Finset.prod_eq_zero hiK (if_neg hiI)
        simp only [hKI, false_and, if_false, Polynomial.eval_zero,
          squarefreeDividedDivisor, hKL, if_true, hz, zero_mul, mul_zero]
    · simp only [hKL, and_false, if_false, Polynomial.eval_zero, squarefreeDividedDivisor, mul_zero]
  have hp : p = (Polynomial.X + 1) ^ I.card := by
    apply Polynomial.funext
    intro t
    rw [heval, (squarefreeSpectralValue_marginals_of_opposite_translation c hA hB hshift _ _).1,
      Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
    rw [show (fun i => constantOn I t i + 1) = fun i => if i ∈ I then t + 1 else 1 by
      funext i
      by_cases hi : i ∈ I <;> simp only [constantOn, hi, if_true, if_false, zero_add],
      Fintype.prod_ite_mem, Finset.prod_const]
  have hcoef : p.coeff I.card = ∑ J : Finset ι, if Iᶜ.card = J.card then c I J else 0 := by
    simp only [p, Polynomial.finset_sum_coeff]
    rw [Finset.sum_eq_single_of_mem I (Finset.mem_univ _)]
    · apply Finset.sum_congr rfl
      intro L _
      by_cases hIL : Iᶜ.card = L.card <;>
        simp only [subset_refl, true_and, hIL, if_true, if_false, Polynomial.coeff_zero,
          Polynomial.coeff_C_mul_X_pow]
    · intro K _ hKI
      apply Finset.sum_eq_zero
      intro L _
      split
      · next h =>
        have hne : I.card ≠ K.card := fun he =>
          hKI (Finset.eq_of_subset_of_card_le h.1 he.le)
        rw [Polynomial.coeff_C_mul_X_pow, if_neg hne]
      · exact Polynomial.coeff_zero _
  rw [← hcoef, hp, Polynomial.coeff_X_add_one_pow, Nat.choose_self, Nat.cast_one]

/-- Each balanced coefficient is at most one when all balanced coefficients
are nonnegative and the value is invariant under opposite translations. -/
theorem squarefreeSpectralValue_coefficient_le_one
    (c : SquarefreeClass ι) (hA : c univ ∅ = 1) (hB : c ∅ univ = 1)
    (hshift : ∀ (a b : ι → ℂ) (t : ℂ),
      squarefreeSpectralValue c (fun i => a i + t) (fun j => b j - t) =
        squarefreeSpectralValue c a b)
    (hn : ∀ I J : Finset ι, Iᶜ.card = J.card → 0 ≤ (c I J).re)
    (I J : Finset ι) (hIJ : Iᶜ.card = J.card) : (c I J).re ≤ 1 := by
  let f (L : Finset ι) := if Iᶜ.card = L.card then (c I L).re else 0
  have hsum : (∑ L, f L) = 1 := by
    have h := congrArg Complex.re (squarefreeSpectralValue_left_coefficient_sum c hA hB hshift I)
    simpa only [Complex.re_sum, apply_ite, Complex.zero_re, Complex.one_re, f] using h
  have hsingle := Finset.single_le_sum
    (f := f) (fun L _ => by
      dsimp only [f]
      split
      · next h => exact hn I L h
      · exact le_rfl) (Finset.mem_univ J)
  rw [hsum] at hsingle
  simpa only [f, hIJ, if_true] using hsingle

end

end MOC
