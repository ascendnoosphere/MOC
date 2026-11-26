import MOC.SquarefreeIntersection

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

private theorem squarefreeSpectralValue_on_support (c : SquarefreeClass ι)
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

end

end MOC
