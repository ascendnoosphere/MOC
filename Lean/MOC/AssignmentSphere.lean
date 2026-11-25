import MOC.Core

/-! Distinct permutations of an injective label vector lie on the same sphere.
A line through two of these vectors cannot contain a third. -/

open BigOperators

namespace MOC

private theorem normSq_affine_pair (a b : ℂ) (c : ℝ) :
    Complex.normSq (a - (c : ℂ) * (a - b)) =
      (1 - c) * Complex.normSq a + c * Complex.normSq b -
        c * (1 - c) * Complex.normSq (a - b) := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, zero_add]
  ring

/-- For three distinct permutations of injective labels, the two differences
from the first permutation cannot be real scalar multiples. -/
theorem perm_sub_not_real_multiple {ι : Type*} [Fintype ι] (x : ι → ℂ)
    (hx : Function.Injective x) (p q r : Equiv.Perm ι)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (c : ℝ) :
    ¬ ∀ j, x (p j) - x (q j) = (c : ℂ) * (x (p j) - x (r j)) := by
  classical
  intro h
  let S := ∑ j, Complex.normSq (x j)
  let D := ∑ j, Complex.normSq (x (p j) - x (r j))
  have hperm (s : Equiv.Perm ι) : (∑ j, Complex.normSq (x (s j))) = S :=
    Equiv.sum_comp s (fun j => Complex.normSq (x j))
  have ha (j : ι) : x (q j) = x (p j) - (c : ℂ) * (x (p j) - x (r j)) := by
    rw [← h j, sub_sub_cancel]
  have hsum : S = (1 - c) * S + c * S - c * (1 - c) * D := by
    calc
      S = (∑ j, Complex.normSq (x (q j))) := (hperm q).symm
      (∑ j, Complex.normSq (x (q j))) =
          ∑ j, ((1 - c) * Complex.normSq (x (p j)) + c * Complex.normSq (x (r j)) -
            c * (1 - c) * Complex.normSq (x (p j) - x (r j))) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [ha, normSq_affine_pair]
      _ = _ := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
        simp only [← Finset.mul_sum, hperm, D]
  have hn (j : ι) : 0 ≤ Complex.normSq (x (p j) - x (r j)) := Complex.normSq_nonneg _
  have hD : D ≠ 0 := by
    intro hzero
    apply hpr
    ext j
    have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hn j)).mp hzero j (Finset.mem_univ j)
    exact hx (sub_eq_zero.mp (Complex.normSq_eq_zero.mp hj))
  have hm : (c * (1 - c)) * D = 0 := by linarith
  rcases mul_eq_zero.mp ((mul_eq_zero.mp hm).resolve_right hD) with hc | hc
  · apply hpq
    ext j
    exact hx (sub_eq_zero.mp (by simpa [hc] using h j))
  · have hc' : c = 1 := by linarith
    apply hqr
    ext j
    have hj : x (p j) - x (q j) = x (p j) - x (r j) := by
      simpa [hc'] using h j
    exact hx (sub_right_inj.mp hj)

end MOC
