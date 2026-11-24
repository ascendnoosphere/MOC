import MOC.Claim
import MOC.ProjectiveTransport
import MOC.SpectralPerturbation
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.RingTheory.Coprime.Lemmas

/-! A symbolic reduction of MOC to the traceless Cartan spectra in Atlas 149.
A zero of the Wronskian of the two signed root polynomials makes their
logarithmic derivatives agree. The corresponding fractional-linear map
then centers both signed spectra without changing the hull question. -/

open BigOperators Matrix Polynomial
namespace MOC.Reformulations

noncomputable section

private def rootProduct {ι : Type*} (s : Finset ι) (a : ι → ℂ) : ℂ[X] :=
  ∏ i ∈ s, (X - C (a i))

private theorem rootProduct_eval {ι : Type*} (s : Finset ι) (a : ι → ℂ) (z : ℂ) :
    (rootProduct s a).eval z = ∏ i ∈ s, (z - a i) := by
  simp [rootProduct, eval_prod]

private theorem rootProduct_deriv_eval {ι : Type*} (s : Finset ι) (a : ι → ℂ) (z : ℂ)
    (h : ∀ i ∈ s, z ≠ a i) :
    (rootProduct s a).derivative.eval z =
      (rootProduct s a).eval z * ∑ i ∈ s, (z - a i)⁻¹ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rootProduct]
  | @insert i s hi ih =>
    have hzi := sub_ne_zero.mpr (h i (Finset.mem_insert_self i s))
    have hs : ∀ j ∈ s, z ≠ a j := fun j hj => h j (Finset.mem_insert_of_mem hj)
    have hmul : rootProduct (insert i s) a = (X - C (a i)) * rootProduct s a := by
      simp [rootProduct, Finset.prod_insert hi]
    rw [hmul, derivative_mul, derivative_X_sub_C, eval_add, eval_mul, eval_mul, eval_one,
      eval_sub, eval_X, eval_C, ih hs, Finset.sum_insert hi]
    field_simp [hzi] <;> ring

private theorem rootProduct_deriv_at_root {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℂ) (ha : Function.Injective a) (i : ι) :
    (rootProduct Finset.univ a).derivative.eval (a i) ≠ 0 := by
  classical
  let s : Finset ι := Finset.univ.erase i
  have hi : i ∉ s := Finset.not_mem_erase _ _
  have hmul : rootProduct Finset.univ a = (X - C (a i)) * rootProduct s a := by
    have he : insert i s = Finset.univ := Finset.insert_erase (Finset.mem_univ i)
    rw [← he]
    simp [rootProduct, Finset.prod_insert hi]
  rw [hmul, derivative_mul, derivative_X_sub_C, eval_add, eval_mul, eval_mul,
    eval_one, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero, one_mul, rootProduct_eval]
  exact Finset.prod_ne_zero_iff.mpr fun j hj =>
    sub_ne_zero.mpr (ha.ne (Ne.symm (Finset.ne_of_mem_erase hj)))

private theorem rootProduct_natDegree {n : ℕ} (a : Fin n → ℂ) :
    (rootProduct Finset.univ a).natDegree = n := by
  unfold rootProduct
  rw [natDegree_prod_of_monic Finset.univ (fun i => X - C (a i)) (fun _ _ => monic_X_sub_C _)]
  simp

private theorem exists_equal_logDeriv {n : ℕ} (hn : 2 ≤ n) (a c : Fin n → ℂ)
    (ha : Function.Injective a) (hc : Function.Injective c) (hcross : ∀ i j, a i ≠ c j) :
    ∃ p : ℂ, (∀ i, p ≠ a i) ∧ (∀ j, p ≠ c j) ∧
      (∑ i, (p - a i)⁻¹) = ∑ j, (p - c j)⁻¹ := by
  classical
  let P := rootProduct Finset.univ a
  let Q := rootProduct Finset.univ c
  let W := P.derivative * Q - P * Q.derivative
  have hP : P.natDegree = n := rootProduct_natDegree a
  have hQ : Q.natDegree = n := rootProduct_natDegree c
  have hPQ : IsCoprime P Q := by
    apply IsCoprime.prod_left
    intro i _
    apply IsCoprime.prod_right
    intro j _
    exact isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr (hcross i j)).isUnit
  have hW : W.degree ≠ 0 := by
    intro hd
    have hd' : W.natDegree = 0 := natDegree_eq_zero_iff_degree_le_zero.mpr hd.le
    have hw : W.derivative = 0 := derivative_of_natDegree_zero hd'
    have hdiff : P.derivative.derivative * Q = P * Q.derivative.derivative := by
      apply sub_eq_zero.mp
      calc
        P.derivative.derivative * Q - P * Q.derivative.derivative = W.derivative := by
          simp only [W, derivative_sub, derivative_mul]
          ring
        _ = 0 := hw
    have hdiv : P ∣ P.derivative.derivative :=
      hPQ.dvd_of_dvd_mul_right (hdiff.symm ▸ dvd_mul_right P Q.derivative.derivative)
    have hne : P.derivative.derivative ≠ 0 := by
      have hde : P.derivative.degree = (n - 1 : ℕ) := by
        rw [degree_derivative_eq P (by omega), hP]
      have hnd : P.derivative.natDegree = n - 1 := natDegree_eq_of_degree_eq_some hde
      intro hz
      have := natDegree_eq_zero_of_derivative_eq_zero hz
      omega
    have hle := natDegree_le_of_dvd hdiv hne
    have h1 := natDegree_derivative_le P.derivative
    have h2 := natDegree_derivative_le P
    omega
  obtain ⟨p,hp⟩ := IsAlgClosed.exists_root W hW
  have he : P.derivative.eval p * Q.eval p - P.eval p * Q.derivative.eval p = 0 := by
    simpa [IsRoot, W, eval_sub, eval_mul] using hp
  have hpa : ∀ i, p ≠ a i := by
    intro i h
    subst p
    have hp0 : P.eval (a i) = 0 := by
      rw [rootProduct_eval]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)
    have hq0 : Q.eval (a i) ≠ 0 := by
      rw [rootProduct_eval]
      exact Finset.prod_ne_zero_iff.mpr fun j _ => sub_ne_zero.mpr (hcross i j)
    have hp1 : P.derivative.eval (a i) ≠ 0 := rootProduct_deriv_at_root a ha i
    exact mul_ne_zero hp1 hq0 (by simpa [hp0] using he)
  have hpc : ∀ j, p ≠ c j := by
    intro j h
    subst p
    have hq0 : Q.eval (c j) = 0 := by
      rw [rootProduct_eval]
      exact Finset.prod_eq_zero (Finset.mem_univ j) (sub_self _)
    have hp0 : P.eval (c j) ≠ 0 := by
      rw [rootProduct_eval]
      exact Finset.prod_ne_zero_iff.mpr fun i _ => sub_ne_zero.mpr (hcross i j).symm
    have hq1 : Q.derivative.eval (c j) ≠ 0 := rootProduct_deriv_at_root c hc j
    exact mul_ne_zero hp0 hq1 (by simpa [hq0] using he)
  refine ⟨p, hpa, hpc, ?_⟩
  have hP0 : P.eval p ≠ 0 := by
    rw [rootProduct_eval]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => sub_ne_zero.mpr (hpa i)
  have hQ0 : Q.eval p ≠ 0 := by
    rw [rootProduct_eval]
    exact Finset.prod_ne_zero_iff.mpr fun j _ => sub_ne_zero.mpr (hpc j)
  have hPa := rootProduct_deriv_eval Finset.univ a p (fun i _ => hpa i)
  have hQc := rootProduct_deriv_eval Finset.univ c p (fun j _ => hpc j)
  change P.derivative.eval p = _ at hPa
  change Q.derivative.eval p = _ at hQc
  rw [hPa, hQc] at he
  have hf : P.eval p * Q.eval p *
      ((∑ i, (p - a i)⁻¹) - ∑ j, (p - c j)⁻¹) = 0 := by
    convert he using 1 <;> ring
  exact sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_left (mul_ne_zero hP0 hQ0))

private theorem simpleSpectra_of_matchingProduct_injective {n : ℕ} (a b : Fin n → ℂ)
    (h : Function.Injective (matchingProduct a b)) :
    Function.Injective a ∧ Function.Injective b := by
  classical
  have hs {g : Fin n → ℂ} {i j : Fin n} (he : g i = g j) :
      ∀ k, g (Equiv.swap i j k) = g k := by
    intro k
    by_cases hi : k = i
    · subst k
      simpa using he.symm
    by_cases hj : k = j
    · subst k
      simpa using he
    rw [Equiv.swap_apply_of_ne_of_ne hi hj]
  constructor
  · intro i j he
    have hp : matchingProduct a b (Equiv.swap i j) =
        matchingProduct a b 1 := by
      unfold matchingProduct
      apply Finset.prod_congr rfl
      intro k _
      simp [hs he k]
    have := congrArg (fun e : Equiv.Perm (Fin n) => e i) (h hp)
    simpa using this.symm
  · intro i j he
    have hp : matchingProduct a b (Equiv.swap i j) =
        matchingProduct a b 1 := by
      unfold matchingProduct
      trans ∏ k, (a (Equiv.swap i j k) + b (Equiv.swap i j k))
      · apply Finset.prod_congr rfl
        intro k _
        rw [hs he k]
      · simpa using (Equiv.prod_comp (Equiv.swap i j) (fun k => a k + b k))
    have := congrArg (fun e : Equiv.Perm (Fin n) => e i) (h hp)
    simpa using this.symm

/-- Atlas 149 on genuine Cartan spectral lists: arbitrary pairs of traceless
diagonals are realized using the defining modules of the two factors of
`sl_n × sl_n`. No nonlinear evaluation of a Cartan weight is used. -/
def TracelessCartanForm : Prop :=
  ∀ n : ℕ, ∀ (a b : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ),
    IsUnitary U → (∑ i, a i) = 0 → (∑ j, b j) = 0 → Holds a b U

theorem tracelessCartanForm_iff : TracelessCartanForm ↔ MOCIsTrue := by
  constructor
  · intro h
    apply mocIsTrue_iff_from_four.mpr
    intro n hn
    apply conjecture_iff_regular_matching_products.mpr
    intro a b U hU hcross hinj
    obtain ⟨ha,hb⟩ := simpleSpectra_of_matchingProduct_injective a b hinj
    let c : Fin n → ℂ := fun j => -b j
    have hc : Function.Injective c := fun _ _ hz => hb (neg_injective hz)
    have hcross' : ∀ i j, a i ≠ c j :=
      fun i j he => hcross i j ((eq_neg_iff_add_eq_zero).mp he)
    obtain ⟨p,hpa,hpc,he⟩ := exists_equal_logDeriv (by omega) a c ha hc hcross'
    let k := (∑ i, (p - a i)⁻¹) / (n : ℂ)
    let f := fractionalMap k (1 - k * p) 1 (-p)
    have hd : k * (-p) - (1 - k * p) * 1 ≠ 0 := by
      convert (neg_ne_zero.mpr (one_ne_zero : (1 : ℂ) ≠ 0)) using 1 <;> ring
    have hf (z : ℂ) (hz : p ≠ z) : f z = k - (p-z)⁻¹ := by
      have h1 : p - z ≠ 0 := sub_ne_zero.mpr hz
      have h2 : z - p ≠ 0 := sub_ne_zero.mpr hz.symm
      unfold f fractionalMap
      simp only [one_mul, ← sub_eq_add_neg]
      field_simp [h1, h2] <;> ring
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have hk : (n : ℂ) * k = ∑ i, (p - a i)⁻¹ := by
      dsimp [k]
      field_simp
    have hz (x : Fin n → ℂ) (hx : ∀ i, p ≠ x i)
        (hs : (∑ i, (p - a i)⁻¹) = ∑ i, (p - x i)⁻¹) : ∑ i, f (x i) = 0 := by
      simp_rw [fun i => hf (x i) (hx i)]
      rw [Finset.sum_sub_distrib]
      simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hk, hs]
    have hza : ∑ i, (f ∘ a) i = 0 := hz a hpa rfl
    have hzc : ∑ j, -f (-b j) = 0 := by
      rw [Finset.sum_neg_distrib]
      exact neg_eq_zero.mpr (hz c hpc he)
    apply (holds_fractional_iff a b U hU k (1 - k*p) 1 (-p) hd ?_ ?_).mp
    · exact h n (f ∘ a) (fun j => -f (-b j)) U hU hza hzc
    · intro i
      simpa [← sub_eq_add_neg] using sub_ne_zero.mpr (hpa i).symm
    · intro j
      simpa [c, ← sub_eq_add_neg] using sub_ne_zero.mpr (hpc j).symm
  · intro h n a b U hU _ _
    exact h n a b U hU

/-- Both proof and disproof transfer, without an unproved bridge. -/
theorem not_tracelessCartanForm_iff : ¬ TracelessCartanForm ↔ ¬ MOCIsTrue :=
  not_congr tracelessCartanForm_iff

end
end MOC.Reformulations
