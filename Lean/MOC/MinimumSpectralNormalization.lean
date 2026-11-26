import MOC.SpectralPolynomialTranslation
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Minimum normalization from the real roots of the aggregate polynomial. -/

open BigOperators Finset Polynomial
open scoped ComplexConjugate

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Set the first list to one scalar variable and the second list to one. -/
def aggregateSpectralPolynomial (c : SquarefreeClass ι) : ℝ[X] :=
  ∑ I : Finset ι, ∑ J : Finset ι, if Iᶜ.card = J.card then
    monomial I.card (c I J).re else 0

private theorem aggregate_coeff (c : SquarefreeClass ι) (k : ℕ) :
    (aggregateSpectralPolynomial c).coeff k =
      ∑ I : Finset ι, ∑ J : Finset ι, if I.card = k ∧ Iᶜ.card = J.card then
        (c I J).re else 0 := by
  simp only [aggregateSpectralPolynomial, finset_sum_coeff]
  apply Finset.sum_congr rfl
  intro I _
  apply Finset.sum_congr rfl
  intro J _
  by_cases h : Iᶜ.card = J.card <;> simp [h, coeff_monomial]

private theorem aggregate_coeff_single (c : SquarefreeClass ι)
    (k : ℕ) (I₀ J₀ : Finset ι) (hI : I₀.card = k) (hJ : I₀ᶜ.card = J₀.card)
    (huniq : ∀ I J : Finset ι, I.card = k → Iᶜ.card = J.card → I = I₀ ∧ J = J₀) :
    (aggregateSpectralPolynomial c).coeff k = (c I₀ J₀).re := by
  rw [aggregate_coeff, Finset.sum_eq_single_of_mem I₀ (Finset.mem_univ I₀)]
  · rw [Finset.sum_eq_single_of_mem J₀ (Finset.mem_univ J₀)]
    · simp only [hI, hJ, and_self, if_true]
    · intro J _ hne
      apply if_neg
      rintro ⟨hi, hj⟩
      exact hne (huniq I₀ J hi hj).2
  · intro I _ hne
    apply Finset.sum_eq_zero
    intro J _
    apply if_neg
    rintro ⟨hi, hj⟩
    exact hne (huniq I J hi hj).1

private theorem aggregate_coeff_top (c : SquarefreeClass ι) (hA : c univ ∅ = 1) :
    (aggregateSpectralPolynomial c).coeff (Fintype.card ι) = 1 := by
  rw [aggregate_coeff_single c (Fintype.card ι) univ ∅ (by simp) (by simp),
    hA, Complex.one_re]
  intro I J hI hJ
  have he : I = univ := Finset.eq_univ_of_card I hI
  subst I
  exact ⟨rfl, Finset.card_eq_zero.mp (by simpa using hJ.symm)⟩

private theorem aggregate_coeff_zero (c : SquarefreeClass ι) (hB : c ∅ univ = 1) :
    (aggregateSpectralPolynomial c).coeff 0 = 1 := by
  rw [aggregate_coeff_single c 0 ∅ univ (by simp) (by simp), hB, Complex.one_re]
  intro I J hI hJ
  have he : I = ∅ := Finset.card_eq_zero.mp hI
  subst I
  exact ⟨rfl, Finset.eq_univ_of_card J (by simpa using hJ.symm)⟩

private theorem aggregate_degree_le (c : SquarefreeClass ι) :
    (aggregateSpectralPolynomial c).natDegree ≤ Fintype.card ι := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [aggregate_coeff]
  apply Finset.sum_eq_zero
  intro I _
  apply Finset.sum_eq_zero
  intro J _
  exact if_neg (fun hh => (not_lt_of_ge (Finset.card_le_univ I)) (hh.1.symm ▸ hk))

/-- Evaluate the aggregate polynomial at a complex scalar. -/
theorem aggregateSpectralPolynomial_aeval (c : SquarefreeClass ι)
    (hreal : ∀ I J : Finset ι, Iᶜ.card = J.card → (c I J).im = 0) (z : ℂ) :
    aeval z (aggregateSpectralPolynomial c) =
      squarefreeSpectralValue c (fun _ => z) (fun _ => 1) := by
  simp only [aggregateSpectralPolynomial, map_sum, squarefreeSpectralValue]
  apply Finset.sum_congr rfl
  intro I _
  apply Finset.sum_congr rfl
  intro J _
  by_cases h : Iᶜ.card = J.card
  · have hc : ((c I J).re : ℂ) = c I J := by
      apply Complex.ext
      · simp only [Complex.ofReal_re]
      · rw [Complex.ofReal_im, hreal I J h]
    simp only [h, if_true, aeval_def, eval₂_monomial, squarefreeDividedDivisor,
      Finset.prod_const, one_pow, mul_one]
    change (↑(c I J).re : ℂ) * z ^ I.card = _
    rw [hc]
  · simp only [h, if_false, map_zero, squarefreeDividedDivisor, mul_zero]

/-- Scaling both constant lists multiplies the value by the same scalar
raised to the total degree. -/
theorem constant_spectral_scale (c : SquarefreeClass ι) (x y : ℂ) :
    squarefreeSpectralValue c (fun _ => x * y) (fun _ => y) =
      y ^ Fintype.card ι * squarefreeSpectralValue c (fun _ => x) (fun _ => 1) := by
  simp only [squarefreeSpectralValue, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I _
  apply Finset.sum_congr rfl
  intro J _
  by_cases h : Iᶜ.card = J.card
  · have hk : I.card + J.card = Fintype.card ι := by
      rw [← h, Finset.card_add_card_compl]
    simp only [squarefreeDividedDivisor, h, if_true, Finset.prod_const, one_pow, mul_one]
    rw [← hk, pow_add, mul_pow]
    ring
  · simp only [squarefreeDividedDivisor, h, if_false, mul_zero]

private theorem aggregate_no_upper_root (c : SquarefreeClass ι)
    (hreal : ∀ I J : Finset ι, Iᶜ.card = J.card → (c I J).im = 0)
    (hstable : ∀ a b : ι → ℂ, (∀ i, 0 < (a i).im) → (∀ j, 0 < (b j).im) →
      squarefreeSpectralValue c a b ≠ 0)
    (z : ℂ) (hz : 0 < z.im) :
    aeval z (aggregateSpectralPolynomial c) ≠ 0 := by
  let y : ℂ := ⟨|z.re| + 1, z.im / 2⟩
  have hy : 0 < y.im := by
    change 0 < z.im / 2
    positivity
  have hzy : 0 < (z * y).im := by
    rw [Complex.mul_im]
    change 0 < z.re * (z.im / 2) + z.im * (|z.re| + 1)
    have ha := mul_nonneg hz.le (abs_nonneg z.re)
    have hb := mul_nonneg hz.le (show 0 ≤ |z.re| + z.re by
      linarith only [neg_le_abs z.re])
    nlinarith only [hz, ha, hb]
  intro he
  rw [aggregateSpectralPolynomial_aeval c hreal] at he
  apply hstable (fun _ => z * y) (fun _ => y) (fun _ => hzy) (fun _ => hy)
  rw [constant_spectral_scale, he, mul_zero]

private theorem aggregate_splits (c : SquarefreeClass ι)
    (hreal : ∀ I J : Finset ι, Iᶜ.card = J.card → (c I J).im = 0)
    (hstable : ∀ a b : ι → ℂ, (∀ i, 0 < (a i).im) → (∀ j, 0 < (b j).im) →
      squarefreeSpectralValue c a b ≠ 0) :
    (aggregateSpectralPolynomial c).Splits (RingHom.id ℝ) := by
  apply Polynomial.splits_id_of_splits (i := algebraMap ℝ ℂ)
    (IsAlgClosed.splits_codomain (aggregateSpectralPolynomial c))
  intro z hz
  have hroot : aeval z (aggregateSpectralPolynomial c) = 0 := by
    have hz' := Polynomial.isRoot_of_mem_roots hz
    simpa only [Polynomial.IsRoot.def, Polynomial.aeval_def, Polynomial.eval_map] using hz'
  have hup : ¬ 0 < z.im := fun h => aggregate_no_upper_root c hreal hstable z h hroot
  have hdown : ¬ z.im < 0 := by
    intro h
    have hp : 0 < (conj z).im := by rw [Complex.conj_im]; exact neg_pos.mpr h
    apply aggregate_no_upper_root c hreal hstable (conj z) hp
    rw [Polynomial.aeval_conj, hroot, map_zero]
  refine ⟨z.re, ?_⟩
  apply Complex.ext
  · exact Complex.ofReal_re _
  · change (z.re : ℂ).im = z.im
    rw [Complex.ofReal_im]
    exact le_antisymm (le_of_not_gt hdown) (le_of_not_gt hup)

private theorem aggregate_eval_pos (c : SquarefreeClass ι) (hB : c ∅ univ = 1)
    (hnonneg : ∀ I J : Finset ι, Iᶜ.card = J.card → 0 ≤ (c I J).re) (x : ℝ) (hx : 0 ≤ x) :
    0 < (aggregateSpectralPolynomial c).eval x := by
  simp only [aggregateSpectralPolynomial, eval_finset_sum]
  have hterm (I J : Finset ι) :
      0 ≤ (if Iᶜ.card = J.card then monomial I.card (c I J).re else 0).eval x := by
    by_cases h : Iᶜ.card = J.card
    · simp only [h, if_true, eval_monomial]
      exact mul_nonneg (hnonneg I J h) (pow_nonneg hx _)
    · simp only [h, if_false, eval_zero, le_refl]
  apply Finset.sum_pos' (fun I _ => Finset.sum_nonneg fun J _ => hterm I J)
  refine ⟨∅, Finset.mem_univ _, ?_⟩
  apply Finset.sum_pos' (fun J _ => hterm ∅ J)
  refine ⟨univ, Finset.mem_univ _, ?_⟩
  simp [hB, eval_monomial]

private theorem aggregate_positive_factors (c : SquarefreeClass ι)
    (hA : c univ ∅ = 1) (hB : c ∅ univ = 1)
    (hreal : ∀ I J : Finset ι, Iᶜ.card = J.card → (c I J).im = 0)
    (hnonneg : ∀ I J : Finset ι, Iᶜ.card = J.card → 0 ≤ (c I J).re)
    (hstable : ∀ a b : ι → ℂ, (∀ i, 0 < (a i).im) → (∀ j, 0 < (b j).im) →
      squarefreeSpectralValue c a b ≠ 0) :
    ∃ r : Fin (Fintype.card ι) → ℝ, (∀ i, 0 < r i) ∧
      (∏ i, r i) = 1 ∧ aggregateSpectralPolynomial c = ∏ i, (X + C (r i)) := by
  let q := aggregateSpectralPolynomial c
  have htop : q.coeff (Fintype.card ι) = 1 := aggregate_coeff_top c hA
  have hm : q.Monic :=
    Polynomial.monic_of_natDegree_le_of_coeff_eq_one _ (aggregate_degree_le c) htop
  have hd : q.natDegree = Fintype.card ι :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero (aggregate_degree_le c)
      (by rw [htop]; exact one_ne_zero)
  have hs : q.Splits (RingHom.id ℝ) := aggregate_splits c hreal hstable
  let l := q.roots.toList
  have hl : (l : Multiset ℝ) = q.roots := Multiset.coe_toList _
  have hlen : l.length = Fintype.card ι := by
    change q.roots.toList.length = _
    rw [Multiset.length_toList, Polynomial.splits_iff_card_roots.mp hs, hd]
  let r₀ (i : Fin l.length) : ℝ := -l.get i
  have hf : q = ∏ i, (X + C (r₀ i)) := by
    calc
      q = (q.roots.map fun a => X - C a).prod :=
        Polynomial.eq_prod_roots_of_monic_of_splits_id hm hs
      _ = (l.map fun a => X - C a).prod := by
        rw [← Multiset.prod_coe, ← Multiset.map_coe, hl]
      _ = (List.ofFn (fun i : Fin l.length => X - C (l.get i))).prod := by
        have he := congrArg (fun l' : List ℝ => (l'.map fun a => X - C a).prod)
          (List.ofFn_get l)
        simpa only [List.map_ofFn, Function.comp_apply] using he.symm
      _ = ∏ i, (X + C (r₀ i)) := by
        rw [Fin.prod_ofFn]
        simp only [r₀, Function.comp_apply, map_neg, sub_eq_add_neg]
  have hpos (i : Fin l.length) : 0 < r₀ i := by
    have hi : l.get i ∈ q.roots :=
      Multiset.mem_toList.mp (List.mem_iff_get.mpr ⟨i, rfl⟩)
    have he := (Polynomial.isRoot_of_mem_roots hi).eq_zero
    change 0 < -l.get i
    apply neg_pos.mpr
    by_contra! hx
    exact (aggregate_eval_pos c hB hnonneg (l.get i) hx).ne' he
  have hp : (∏ i, r₀ i) = 1 := by
    have hzero : q.eval 0 = 1 := by
      rw [← Polynomial.coeff_zero_eq_eval_zero, aggregate_coeff_zero c hB]
    rw [hf] at hzero
    change Polynomial.evalRingHom 0 (∏ i, (X + C (r₀ i))) = 1 at hzero
    simpa only [map_prod, Polynomial.coe_evalRingHom, eval_add, eval_X, eval_C, zero_add]
      using hzero
  let e : Fin (Fintype.card ι) ≃ Fin l.length := finCongr hlen.symm
  refine ⟨r₀ ∘ e, fun i => hpos (e i), (Equiv.prod_comp e r₀).trans hp, ?_⟩
  rw [hf]
  exact (Equiv.prod_comp e (fun i => X + C (r₀ i))).symm

/-- Minimum normalization and its equality case for the aggregate polynomial.
The coefficients are real and nonnegative, and both pure coefficients equal one. -/
theorem aggregateSpectralPolynomial_minimum_normalization (c : SquarefreeClass ι)
    (hA : c univ ∅ = 1) (hB : c ∅ univ = 1)
    (hreal : ∀ I J : Finset ι, Iᶜ.card = J.card → (c I J).im = 0)
    (hnonneg : ∀ I J : Finset ι, Iᶜ.card = J.card → 0 ≤ (c I J).re)
    (hstable : ∀ a b : ι → ℂ, (∀ i, 0 < (a i).im) → (∀ j, 0 < (b j).im) →
      squarefreeSpectralValue c a b ≠ 0) :
    let q := aggregateSpectralPolynomial c
    (2 : ℝ) ^ Fintype.card ι ≤ q.eval 1 ∧
      (q.eval 1 = (2 : ℝ) ^ Fintype.card ι → q = (X + 1) ^ Fintype.card ι) := by
  dsimp only
  obtain ⟨r, hrpos, hrprod, hfactor⟩ := aggregate_positive_factors c hA hB hreal hnonneg hstable
  let n := Fintype.card ι
  have heval : (aggregateSpectralPolynomial c).eval 1 = ∏ i, (1 + r i) := by
    rw [hfactor]
    change Polynomial.evalRingHom 1 (∏ i, (X + C (r i))) = _
    simp only [map_prod, Polynomial.coe_evalRingHom, eval_add, eval_X, eval_C]
  have hleft : (∏ i, 4 * r i) = ((2 : ℝ) ^ n) ^ 2 := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Fintype.card_fin, hrprod, mul_one]
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  have hright : (∏ i, (1 + r i)^2) = ((aggregateSpectralPolynomial c).eval 1)^2 := by
    rw [heval, Finset.prod_pow]
  have hle (i : Fin n) : 4 * r i ≤ (1 + r i)^2 := by nlinarith [sq_nonneg (r i - 1)]
  have hlpos (i : Fin n) : 0 < 4 * r i := mul_pos (by norm_num) (hrpos i)
  have hqpos : 0 ≤ (aggregateSpectralPolynomial c).eval 1 := by
    rw [heval]
    exact Finset.prod_nonneg fun i _ => add_nonneg zero_le_one (hrpos i).le
  constructor
  · have hh := Finset.prod_le_prod (s := Finset.univ)
      (fun i _ => (hlpos i).le) (fun i _ => hle i)
    rw [hleft, hright] at hh
    exact (sq_le_sq₀ (by positivity) hqpos).mp hh
  · intro he
    have hall (i : Fin n) : r i = 1 := by
      by_contra hi
      have hx : 4 * r i < (1 + r i)^2 := by
        nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr hi)]
      have hh := Finset.prod_lt_prod (fun j _ => hlpos j) (fun j _ => hle j)
        ⟨i, Finset.mem_univ i, hx⟩
      rw [hleft, hright, he] at hh
      exact (lt_irrefl _ hh).elim
    simpa only [hall, map_one, Finset.prod_const, Fintype.card_fin] using hfactor

end

end MOC
