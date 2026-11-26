import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Ring

/-! Independent diagonal signs remove the cross terms between different subsets. -/

open BigOperators
open scoped ComplexConjugate

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private def coordinateSign (b : Bool) : ℂ := if b then -1 else 1

def subsetSign (ε : ι → Bool) (S : Finset ι) : ℂ :=
  ∏ i ∈ S, coordinateSign (ε i)

private theorem conj_subsetSign (ε : ι → Bool) (S : Finset ι) :
    conj (subsetSign ε S) = subsetSign ε S := by
  unfold subsetSign
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i _
  cases h : ε i <;> simp [coordinateSign, h]

/-- The subset characters are orthogonal for independent equiprobable signs. -/
theorem sum_subsetSign_mul (S T : Finset ι) :
    (∑ ε : ι → Bool, subsetSign ε S * subsetSign ε T) =
      if S = T then (Fintype.card (ι → Bool) : ℂ) else 0 := by
  classical
  let g (S : Finset ι) (i : ι) (b : Bool) := if i ∈ S then coordinateSign b else 1
  have hg (ε : ι → Bool) (S : Finset ι) :
      subsetSign ε S = ∏ i, g S i (ε i) := by
    have he : Finset.univ.filter (· ∈ S) = S := by ext i; simp
    calc
      subsetSign ε S = ∏ i ∈ Finset.univ.filter (· ∈ S), coordinateSign (ε i) := by
        rw [subsetSign, he]
      _ = ∏ i, g S i (ε i) := by simp only [Finset.prod_filter, g]
  by_cases h : S = T
  · subst T
    have hsq (ε : ι → Bool) : subsetSign ε S * subsetSign ε S = 1 := by
      rw [subsetSign, ← Finset.prod_mul_distrib]
      apply Finset.prod_eq_one
      intro i _
      cases h : ε i <;> simp [coordinateSign, h]
    simp [hsq]
  · rw [if_neg h]
    simp_rw [hg, ← Finset.prod_mul_distrib]
    have hprod := Finset.prod_univ_sum (fun _ : ι => (Finset.univ : Finset Bool))
      (fun i b => g S i b * g T i b)
    rw [Fintype.piFinset_univ] at hprod
    rw [← hprod]
    have hx : ∃ i, ¬ (i ∈ S ↔ i ∈ T) := by
      by_contra! hn
      exact h (Finset.ext hn)
    obtain ⟨i, hi⟩ := hx
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    by_cases hs : i ∈ S <;> by_cases ht : i ∈ T
    · exact (hi (iff_of_true hs ht)).elim
    · simp [Fintype.sum_bool, g, hs, ht, coordinateSign]
    · simp [Fintype.sum_bool, g, hs, ht, coordinateSign]
    · exact (hi (iff_of_false hs ht)).elim

/-- A finite sign average of squared modulus is the sum of the diagonal
terms. The statement applies to the subset amplitudes in Cauchy–Binet. -/
theorem sum_normSq_subsetSign_amplitudes (E : Finset (Finset ι)) (A : Finset ι → ℂ) :
    (∑ ε : ι → Bool, Complex.normSq (∑ S ∈ E, subsetSign ε S * A S)) =
      (Fintype.card (ι → Bool) : ℝ) * ∑ S ∈ E, Complex.normSq (A S) := by
  classical
  let C (ε : ι → Bool) := ∑ S ∈ E, subsetSign ε S * A S
  have hexpand (ε : ι → Bool) :
      C ε * conj (C ε) =
        ∑ S ∈ E, ∑ T ∈ E, (subsetSign ε S * subsetSign ε T) * (A S * conj (A T)) := by
    simp only [C, map_sum, map_mul, conj_subsetSign]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro S _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro T _
    ring
  have hswap :
      (∑ ε : ι → Bool, ∑ S ∈ E, ∑ T ∈ E,
        (subsetSign ε S * subsetSign ε T) * (A S * conj (A T))) =
        ∑ S ∈ E, ∑ T ∈ E, ∑ ε : ι → Bool,
          (subsetSign ε S * subsetSign ε T) * (A S * conj (A T)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro S _
    rw [Finset.sum_comm]
  have he : (∑ ε : ι → Bool, C ε * conj (C ε)) =
      (Fintype.card (ι → Bool) : ℂ) * ∑ S ∈ E, A S * conj (A S) := by
    simp_rw [hexpand]
    rw [hswap, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S hS
    simp_rw [← Finset.sum_mul, sum_subsetSign_mul, ite_mul, zero_mul]
    rw [Finset.sum_eq_single_of_mem S hS]
    · simp
    · intro T _ hTS
      simp [Ne.symm hTS]
  have he' : (∑ ε : ι → Bool, (Complex.normSq (C ε) : ℂ)) =
      ((Fintype.card (ι → Bool) : ℝ) : ℂ) * ∑ S ∈ E, (Complex.normSq (A S) : ℂ) := by
    simpa only [Complex.mul_conj, Complex.ofReal_natCast] using he
  rw [← Complex.ofReal_sum, ← Complex.ofReal_sum, ← Complex.ofReal_mul] at he'
  exact Complex.ofReal_injective he'

end MOC
