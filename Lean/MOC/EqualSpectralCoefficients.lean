import MOC.Claim
import MOC.ProjectiveTransport
import MOC.SpectralPerturbation
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic.LinearCombination

/-! Exact spectral reductions from the equal-coefficient cases.
The second elementary symmetric coefficient is written in Newton form. -/

open BigOperators Finset Matrix Polynomial
open scoped Topology

namespace MOC

noncomputable section

variable {n : ℕ}

/-- The second elementary symmetric coefficient of an eigenvalue list.
Newton's identity gives twice this value as the square of the sum minus
the sum of the squares. -/
def spectralSecondElementary (a : Fin n → ℂ) : ℂ :=
  ((∑ i, a i)^2 - ∑ i, a i ^ 2) / 2

private theorem sum_translate_spectrum (a : Fin n → ℂ) (t : ℂ) :
    (∑ i, (a i + t)) = (∑ i, a i) + (n : ℂ) * t := by
  simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

private theorem sum_sq_translate_spectrum (a : Fin n → ℂ) (t : ℂ) :
    (∑ i, (a i + t)^2) =
      (∑ i, a i ^ 2) + 2 * t * (∑ i, a i) + (n : ℂ) * t^2 := by
  calc
    _ = ∑ i, (a i ^ 2 + 2 * t * a i + t^2) := by
      apply sum_congr rfl
      intro i _
      ring
    _ = _ := by
      simp only [sum_add_distrib, ← mul_sum, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem spectralSecondElementary_translate (a : Fin n → ℂ) (t : ℂ) :
    spectralSecondElementary (fun i => a i + t) = spectralSecondElementary a +
      ((n : ℂ) - 1) * t * (∑ i, a i) + (n : ℂ) * ((n : ℂ) - 1) * t^2 / 2 := by
  rw [spectralSecondElementary, sum_translate_spectrum, sum_sq_translate_spectrum,
    spectralSecondElementary]
  ring

theorem spectralSecondElementary_opposite_shifts (a b : Fin n → ℂ) (t : ℂ) :
    spectralSecondElementary (fun i => a i + t) -
        spectralSecondElementary (fun i => b i - t) =
      spectralSecondElementary a - spectralSecondElementary b +
        ((n : ℂ) - 1) * t * ((∑ i, a i) + ∑ j, b j) := by
  simp only [sub_eq_add_neg, spectralSecondElementary_translate]
  ring

private theorem spectral_holds_of_nearby (U : Matrix (Fin n) (Fin n) ℂ)
    {A B : ℂ → Fin n → ℂ} (ha : Continuous A) (hb : Continuous B)
    (h : ∀ᶠ t in 𝓝[≠] (0 : ℂ), Holds (A t) (B t) U) : Holds (A 0) (B 0) U := by
  apply (holds_iff_directional (A 0) (B 0) U).mpr
  intro η
  by_contra! hcontra
  have hd : Continuous fun t => (η * determinantValue (A t) (B t) U).re := by
    unfold determinantValue
    fun_prop
  have hm (σ : Equiv.Perm (Fin n)) :
      Continuous fun t => (η * matchingProduct (A t) (B t) σ).re := by
    unfold matchingProduct
    exact Complex.continuous_re.comp (continuous_const.mul
      (continuous_finset_prod _ fun j _ =>
        ((continuous_apply (σ j)).comp ha).add ((continuous_apply j).comp hb)))
  have hstrict : ∀ᶠ t in 𝓝 (0 : ℂ), ∀ σ : Equiv.Perm (Fin n),
      (η * matchingProduct (A t) (B t) σ).re < (η * determinantValue (A t) (B t) U).re := by
    apply Filter.eventually_all.mpr
    intro σ
    exact (isOpen_lt (hm σ) hd).mem_nhds (hcontra σ)
  obtain ⟨t, ht, ht'⟩ := ((hstrict.filter_mono nhdsWithin_le_nhds).and h).exists
  obtain ⟨σ, hσ⟩ := (holds_iff_directional (A t) (B t) U).mp ht' η
  exact (not_lt_of_ge hσ) (ht σ)

private theorem eventually_eval_ne_zero {p : ℂ[X]} (hp : p ≠ 0) :
    ∀ᶠ t in 𝓝[≠] (0 : ℂ), p.eval t ≠ 0 := by
  have hc : IsClosed ({t : ℂ | p.IsRoot t} \ {0}) :=
    ((finite_setOf_isRoot hp).subset Set.diff_subset).isClosed
  have hnear : ∀ᶠ t in 𝓝 (0 : ℂ), t ∉ ({t : ℂ | p.IsRoot t} \ {0}) :=
    hc.isOpen_compl.mem_nhds (by simp)
  filter_upwards [hnear.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht ht₀
  intro hz
  exact ht ⟨hz, ht₀⟩

/-- Testing only pairs with equal second elementary symmetric coefficients
suffices in each fixed order. -/
theorem conjecture_iff_equal_second_elementary :
    Conjecture (Fin n) ↔ ∀ (a b : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ),
      IsUnitary U → spectralSecondElementary a = spectralSecondElementary b → Holds a b U := by
  constructor
  · intro h a b U hU _
    exact h a b U hU
  · intro h a b U hU
    by_cases hn : 2 ≤ n
    · have hn₁ : (n : ℂ) - 1 ≠ 0 := by
        apply sub_ne_zero.mpr
        exact_mod_cast (show n ≠ 1 by omega)
      have hn₀ : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
      have hnorm (A : Fin n → ℂ) (hA : (∑ i, A i) + ∑ j, b j ≠ 0) :
          Holds A b U := by
        let c := ((n : ℂ) - 1) * ((∑ i, A i) + ∑ j, b j)
        have hc : c ≠ 0 := mul_ne_zero hn₁ hA
        let t := -(spectralSecondElementary A - spectralSecondElementary b) / c
        apply (holds_shift_iff A b hU t).mp
        apply h _ _ U hU
        apply sub_eq_zero.mp
        rw [spectralSecondElementary_opposite_shifts]
        rw [mul_right_comm ((n : ℂ) - 1) t ((∑ i, A i) + ∑ j, b j)]
        change spectralSecondElementary A - spectralSecondElementary b + c * t = 0
        dsimp [t]
        field_simp [hc] <;> ring
      let A (t : ℂ) (i : Fin n) := a i + t
      let s := (∑ i, a i) + ∑ j, b j
      let p : ℂ[X] := C (n : ℂ) * X + C s
      have hp : p ≠ 0 := by
        intro hz
        have hc := congrArg (fun q : ℂ[X] => q.coeff 1) hz
        exact hn₀ (by simpa [p, coeff_add, coeff_C_mul, coeff_X] using hc)
      have hnear : ∀ᶠ t in 𝓝[≠] (0 : ℂ), Holds (A t) b U := by
        filter_upwards [eventually_eval_ne_zero hp] with t ht
        apply hnorm
        intro hz
        apply ht
        simp only [p, eval_add, eval_mul, eval_C, eval_X, s]
        dsimp [A] at hz
        rw [sum_translate_spectrum] at hz
        linear_combination hz
      have ha : Continuous A := continuous_pi fun i => continuous_const.add continuous_id
      simpa only [A, add_zero] using spectral_holds_of_nearby U ha continuous_const hnear
    · exact conjecture_le_three (by omega) a b U hU

private theorem injective_first_of_matchingProduct (a b : Fin n → ℂ)
    (h : Function.Injective (matchingProduct a b)) : Function.Injective a := by
  intro i j hij
  by_contra hne
  have hs (k : Fin n) : a (Equiv.swap i j k) = a k := by
    by_cases hki : k = i
    · subst k
      simpa using hij.symm
    by_cases hkj : k = j
    · subst k
      simpa using hij
    rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
  have hp : matchingProduct a b (Equiv.swap i j) = matchingProduct a b 1 := by
    unfold matchingProduct
    apply prod_congr rfl
    intro k _
    rw [hs, Equiv.Perm.one_apply]
  have hz := DFunLike.congr_fun (h hp) i
  exact hne (by simpa using hz.symm)

private theorem injective_second_of_matchingProduct (a b : Fin n → ℂ)
    (h : Function.Injective (matchingProduct a b)) : Function.Injective b := by
  apply injective_first_of_matchingProduct b a
  have hi (σ : Equiv.Perm (Fin n)) :
      matchingProduct b a σ = matchingProduct a b σ.symm := by
    rw [matchingProduct_inverse]
    simp only [matchingProduct, add_comm]
  intro σ τ he
  have hh := h ((hi σ).symm.trans (he.trans (hi τ)))
  simpa only [Equiv.symm_symm] using congrArg Equiv.symm hh

private def spectralRootProduct (a : Fin n → ℂ) : ℂ[X] :=
  ∏ j, (X - C (a j))

private def deletedSpectralRootProduct (a : Fin n → ℂ) (i : Fin n) : ℂ[X] :=
  ∏ j ∈ univ.erase i, (X - C (a j))

private theorem eval_spectralRootProduct (a : Fin n → ℂ) (p : ℂ) :
    (spectralRootProduct a).eval p = ∏ j, (p - a j) := by
  simp only [spectralRootProduct, eval_prod, eval_sub, eval_X, eval_C]

private theorem eval_deletedSpectralRootProduct (a : Fin n → ℂ) (i : Fin n) (p : ℂ) :
    (deletedSpectralRootProduct a i).eval p = ∏ j ∈ univ.erase i, (p - a j) := by
  simp only [deletedSpectralRootProduct, eval_prod, eval_sub, eval_X, eval_C]

private theorem eval_spectralRootProduct_split (a : Fin n → ℂ) (i : Fin n) (p : ℂ) :
    (spectralRootProduct a).eval p = (deletedSpectralRootProduct a i).eval p * (p - a i) := by
  rw [eval_spectralRootProduct, eval_deletedSpectralRootProduct, prod_erase_mul _ _ (mem_univ i)]

private theorem eval_spectralRootProduct_ne_zero (a : Fin n → ℂ) (p : ℂ)
    (hp : ∀ j, p ≠ a j) : (spectralRootProduct a).eval p ≠ 0 := by
  rw [eval_spectralRootProduct]
  exact prod_ne_zero_iff.mpr fun j _ => sub_ne_zero.mpr (hp j)

private theorem eval_deletedSpectralRootProduct_ne_zero (a : Fin n → ℂ) (i : Fin n) (p : ℂ)
    (hp : ∀ j, j ≠ i → p ≠ a j) : (deletedSpectralRootProduct a i).eval p ≠ 0 := by
  rw [eval_deletedSpectralRootProduct]
  exact prod_ne_zero_iff.mpr fun j hj => sub_ne_zero.mpr (hp j (mem_erase.mp hj).1)

private theorem eval_deletedSpectralRootProduct_at_other_root (a : Fin n → ℂ)
    (i j : Fin n) (hij : i ≠ j) : (deletedSpectralRootProduct a j).eval (a i) = 0 := by
  rw [eval_deletedSpectralRootProduct]
  exact Finset.prod_eq_zero (mem_erase.mpr ⟨hij, mem_univ _⟩) (sub_self _)

/-- The numerator of the centered inverse-square sum, with the extra factor
`n`. The denominator is the square of the root product. -/
private def inverseSpectralVarianceNumerator (a : Fin n → ℂ) : ℂ[X] :=
  C (n : ℂ) * (∑ i, (deletedSpectralRootProduct a i)^2) -
    (∑ i, deletedSpectralRootProduct a i)^2

private def inverseSpectralVarianceDifference (a c : Fin n → ℂ) : ℂ[X] :=
  inverseSpectralVarianceNumerator a * (spectralRootProduct c)^2 -
    inverseSpectralVarianceNumerator c * (spectralRootProduct a)^2

private theorem eval_inverseSpectralVarianceDifference_left (a c : Fin n → ℂ) (i : Fin n) :
    (inverseSpectralVarianceDifference a c).eval (a i) =
      ((n : ℂ) - 1) * (deletedSpectralRootProduct a i).eval (a i)^2 *
        (spectralRootProduct c).eval (a i)^2 := by
  have hA : (spectralRootProduct a).eval (a i) = 0 := by
    rw [eval_spectralRootProduct_split a i, sub_self, mul_zero]
  have hd (r : ℕ) (hr : r ≠ 0) :
      (∑ j, (deletedSpectralRootProduct a j).eval (a i)^r) =
        (deletedSpectralRootProduct a i).eval (a i)^r := by
    apply sum_eq_single i
    · intro j _ hj
      rw [eval_deletedSpectralRootProduct_at_other_root a i j hj.symm, zero_pow hr]
    · intro hi
      exact (hi (mem_univ _)).elim
  have hd₁ : (∑ j, (deletedSpectralRootProduct a j).eval (a i)) =
      (deletedSpectralRootProduct a i).eval (a i) := by
    simpa only [pow_one] using hd 1 (by decide)
  simp only [inverseSpectralVarianceDifference, inverseSpectralVarianceNumerator, eval_sub,
    eval_mul, eval_pow, eval_C, eval_finset_sum, hA, zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero,
    hd 2 (by decide), hd₁]
  ring

private theorem eval_inverseSpectralVarianceDifference_right (a c : Fin n → ℂ) (i : Fin n) :
    (inverseSpectralVarianceDifference a c).eval (c i) =
      -(((n : ℂ) - 1) * (deletedSpectralRootProduct c i).eval (c i)^2 *
        (spectralRootProduct a).eval (c i)^2) := by
  have he : inverseSpectralVarianceDifference a c = -inverseSpectralVarianceDifference c a := by
    unfold inverseSpectralVarianceDifference
    ring
  rw [he, eval_neg, eval_inverseSpectralVarianceDifference_left]

private theorem inverseSpectralVarianceDifference_root_off (a c : Fin n → ℂ)
    (hn : (n : ℂ) - 1 ≠ 0) (ha : Function.Injective a) (hc : Function.Injective c)
    (hac : ∀ i j, a i ≠ c j) {p : ℂ}
    (hp : (inverseSpectralVarianceDifference a c).IsRoot p) :
    (∀ i, p ≠ a i) ∧ ∀ j, p ≠ c j := by
  change (inverseSpectralVarianceDifference a c).eval p = 0 at hp
  constructor
  · intro i h
    subst p
    rw [eval_inverseSpectralVarianceDifference_left] at hp
    exact mul_ne_zero (mul_ne_zero hn (pow_ne_zero 2
      (eval_deletedSpectralRootProduct_ne_zero a i (a i) (fun j hj => ha.ne hj.symm))))
      (pow_ne_zero 2 (eval_spectralRootProduct_ne_zero c (a i) (hac i))) hp
  · intro j h
    subst p
    rw [eval_inverseSpectralVarianceDifference_right] at hp
    exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero hn (pow_ne_zero 2
      (eval_deletedSpectralRootProduct_ne_zero c j (c j) (fun i hi => hc.ne hi.symm))))
      (pow_ne_zero 2 (eval_spectralRootProduct_ne_zero a (c j) (fun i => (hac i j).symm)))) hp

private def unnormalizedSpectralVariance (a : Fin n → ℂ) : ℂ :=
  (n : ℂ) * (∑ i, a i ^ 2) - (∑ i, a i)^2

private theorem eval_inverseSpectralVarianceNumerator (a : Fin n → ℂ) (p : ℂ)
    (hp : ∀ i, p ≠ a i) :
    (inverseSpectralVarianceNumerator a).eval p =
      (spectralRootProduct a).eval p ^ 2 *
        unnormalizedSpectralVariance (fun i => (p - a i)⁻¹) := by
  let d := (spectralRootProduct a).eval p
  have hi (i : Fin n) : (deletedSpectralRootProduct a i).eval p = d * (p - a i)⁻¹ := by
    dsimp [d]
    rw [eval_spectralRootProduct_split a i]
    rw [mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr (hp i)), mul_one]
  simp only [inverseSpectralVarianceNumerator, eval_sub, eval_mul, eval_C, eval_pow,
    eval_finset_sum, hi, mul_pow, ← mul_sum, unnormalizedSpectralVariance]
  ring

private theorem variance_eq_of_pole (a c : Fin n → ℂ) (p : ℂ)
    (ha : ∀ i, p ≠ a i) (hc : ∀ i, p ≠ c i)
    (hp : (inverseSpectralVarianceDifference a c).IsRoot p) :
    unnormalizedSpectralVariance (fun i => (p - a i)⁻¹) =
      unnormalizedSpectralVariance (fun i => (p - c i)⁻¹) := by
  change (inverseSpectralVarianceDifference a c).eval p = 0 at hp
  simp only [inverseSpectralVarianceDifference, eval_sub, eval_mul, eval_pow,
    eval_inverseSpectralVarianceNumerator a p ha, eval_inverseSpectralVarianceNumerator c p hc] at hp
  have hprod : (spectralRootProduct a).eval p ^ 2 * (spectralRootProduct c).eval p ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 (eval_spectralRootProduct_ne_zero a p ha))
      (pow_ne_zero 2 (eval_spectralRootProduct_ne_zero c p hc))
  have hzero : ((spectralRootProduct a).eval p ^ 2 * (spectralRootProduct c).eval p ^ 2) *
      (unnormalizedSpectralVariance (fun i => (p - a i)⁻¹) -
        unnormalizedSpectralVariance (fun i => (p - c i)⁻¹)) = 0 := by
    linear_combination hp
  exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left hprod)

private theorem holds_of_inverse_variance_pole (a b : Fin n → ℂ)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U) (hn : (n : ℂ) ≠ 0)
    (h : ∀ (A B : Fin n → ℂ), (∑ i, A i) = (∑ i, B i) →
      spectralSecondElementary A = spectralSecondElementary B → Holds A B U)
    (p : ℂ) (hpa : ∀ i, p ≠ a i) (hpb : ∀ i, p ≠ -b i)
    (hV : unnormalizedSpectralVariance (fun i => (p - a i)⁻¹) =
      unnormalizedSpectralVariance (fun i => (p - -b i)⁻¹)) : Holds a b U := by
  let A (i : Fin n) := (p - a i)⁻¹
  let B (i : Fin n) := (p - -b i)⁻¹
  let sA := ∑ i, A i
  let sB := ∑ i, B i
  let m := (sA + sB) / (2 * (n : ℂ))
  let f := fractionalMap m (1 - m * p) (-1) p
  have hm : 2 * (n : ℂ) * m = sA + sB := by
    dsimp [m]
    field_simp [hn] <;> ring
  have hf (z : ℂ) (hz : p ≠ z) : f z = (p - z)⁻¹ + -m := by
    have hsub := sub_ne_zero.mpr hz
    change (m * z + (1 - m * p)) / (-1 * z + p) = _
    rw [show -1 * z + p = p - z by ring]
    field_simp [hsub] <;> ring
  have ha' : f ∘ a = fun i => A i + -m := funext fun i => hf (a i) (hpa i)
  have hb' : (fun i => -f (-b i)) = fun i => -(B i + -m) := by
    funext i
    exact congrArg Neg.neg (hf (-b i) (hpb i))
  have hd : m * p - (1 - m * p) * (-1) ≠ 0 := by
    rw [show m * p - (1 - m * p) * (-1) = 1 by ring]
    exact one_ne_zero
  have hden (z : ℂ) (hz : p ≠ z) : -1 * z + p ≠ 0 := by
    rw [show -1 * z + p = p - z by ring]
    exact sub_ne_zero.mpr hz
  apply (holds_fractional_iff a b U hU m (1 - m * p) (-1) p hd
    (fun i => hden (a i) (hpa i)) (fun j => hden (-b j) (hpb j))).mp
  change Holds (f ∘ a) (fun i => -f (-b i)) U
  rw [ha', hb']
  have hsum : (∑ i, (A i + -m)) = ∑ i, -(B i + -m) := by
    rw [sum_neg_distrib, sum_translate_spectrum A, sum_translate_spectrum B]
    change sA + (n : ℂ) * -m = -(sB + (n : ℂ) * -m)
    linear_combination -hm
  apply h _ _ hsum
  have hsq : (∑ i, (A i + -m)^2) = ∑ i, (-(B i + -m))^2 := by
    simp only [neg_sq]
    rw [sum_sq_translate_spectrum A, sum_sq_translate_spectrum B]
    apply mul_left_cancel₀ hn
    change (n : ℂ) * ((∑ i, A i ^ 2) + 2 * -m * sA + (n : ℂ) * (-m)^2) =
      (n : ℂ) * ((∑ i, B i ^ 2) + 2 * -m * sB + (n : ℂ) * (-m)^2)
    change (n : ℂ) * (∑ i, A i ^ 2) - sA^2 =
      (n : ℂ) * (∑ i, B i ^ 2) - sB^2 at hV
    linear_combination hV - (sA - sB) * hm
  simp only [spectralSecondElementary, hsum, hsq]

private def perturbSpectralEntry (c : Fin n → ℂ) (k : Fin n) (t : ℂ) (i : Fin n) : ℂ :=
  if i = k then c i + t else c i

private theorem perturbSpectralEntry_zero (c : Fin n → ℂ) (k : Fin n) :
    perturbSpectralEntry c k 0 = c := by
  funext i
  by_cases hi : i = k <;> simp [perturbSpectralEntry, hi]

private theorem continuous_perturbSpectralEntry (c : Fin n → ℂ) (k : Fin n) :
    Continuous (perturbSpectralEntry c k) := by
  apply continuous_pi
  intro i
  by_cases hi : i = k
  · simpa only [perturbSpectralEntry, if_pos hi] using
      (continuous_const.add continuous_id : Continuous (fun t : ℂ => c i + t))
  · simpa only [perturbSpectralEntry, if_neg hi] using
      (continuous_const : Continuous (fun _ : ℂ => c i))

private theorem eval_spectralRootProduct_perturbEntry (c : Fin n → ℂ) (k : Fin n)
    (p t : ℂ) :
    (spectralRootProduct (perturbSpectralEntry c k t)).eval p =
      (deletedSpectralRootProduct c k).eval p * (p - (c k + t)) := by
  rw [eval_spectralRootProduct_split _ k]
  have hdel : (deletedSpectralRootProduct (perturbSpectralEntry c k t) k).eval p =
      (deletedSpectralRootProduct c k).eval p := by
    rw [eval_deletedSpectralRootProduct, eval_deletedSpectralRootProduct]
    apply prod_congr rfl
    intro j hj
    simp only [perturbSpectralEntry, if_neg (mem_erase.mp hj).1]
  rw [hdel, perturbSpectralEntry, if_pos rfl]

private theorem eventually_varianceDifference_nonconstant (a c : Fin n → ℂ) (hn : 2 ≤ n)
    (ha : Function.Injective a) (hac : ∀ i j, a i ≠ c j) :
    ∀ᶠ t in 𝓝[≠] (0 : ℂ),
      (inverseSpectralVarianceDifference a (perturbSpectralEntry c ⟨0, by omega⟩ t)).degree ≠ 0 := by
  let k : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  have hkj : k ≠ j := by
    intro he
    have h' : 0 = 1 := congrArg Fin.val he
    omega
  have hn' : (n : ℂ) - 1 ≠ 0 := by
    apply sub_ne_zero.mpr
    exact_mod_cast (show n ≠ 1 by omega)
  let r (i : Fin n) :=
    ((n : ℂ) - 1) * (deletedSpectralRootProduct a i).eval (a i)^2 *
      (deletedSpectralRootProduct c k).eval (a i)^2
  have hr (i : Fin n) : r i ≠ 0 := mul_ne_zero (mul_ne_zero hn'
    (pow_ne_zero 2 (eval_deletedSpectralRootProduct_ne_zero a i (a i) (fun l hl => ha.ne hl.symm))))
    (pow_ne_zero 2 (eval_deletedSpectralRootProduct_ne_zero c k (a i) (fun l _ => hac i l)))
  let P : ℂ[X] := C (r k) * (C (a k - c k) - X)^2 - C (r j) * (C (a j - c k) - X)^2
  have hp : P ≠ 0 := by
    intro hz
    have hp0 := congrArg (eval (a k - c k)) hz
    simp only [P, eval_sub, eval_mul, eval_pow, eval_C, eval_X, sub_self, zero_pow (by decide : 2 ≠ 0),
      mul_zero, zero_sub, eval_zero] at hp0
    have he : a j - c k - (a k - c k) = a j - a k := by ring
    rw [he] at hp0
    exact (neg_ne_zero.mpr (mul_ne_zero (hr j) (pow_ne_zero 2 (sub_ne_zero.mpr (ha.ne hkj.symm))))) hp0
  have Peval (t : ℂ) (i : Fin n) :
      (inverseSpectralVarianceDifference a (perturbSpectralEntry c k t)).eval (a i) =
        r i * (a i - c k - t)^2 := by
    rw [eval_inverseSpectralVarianceDifference_left, eval_spectralRootProduct_perturbEntry]
    dsimp [r]
    ring
  filter_upwards [eventually_eval_ne_zero hp] with t ht
  change (inverseSpectralVarianceDifference a (perturbSpectralEntry c k t)).degree ≠ 0
  intro hdeg
  let N := inverseSpectralVarianceDifference a (perturbSpectralEntry c k t)
  change N.degree = 0 at hdeg
  have hnat : N.natDegree = 0 := natDegree_eq_zero_iff_degree_le_zero.mpr hdeg.le
  have hconst : N = C (N.coeff 0) := eq_C_of_natDegree_eq_zero hnat
  have hsame : N.eval (a k) = N.eval (a j) := by rw [hconst, eval_C, eval_C]
  change (inverseSpectralVarianceDifference a (perturbSpectralEntry c k t)).eval (a k) =
    (inverseSpectralVarianceDifference a (perturbSpectralEntry c k t)).eval (a j) at hsame
  rw [Peval, Peval] at hsame
  apply ht
  simp only [P, eval_sub, eval_mul, eval_pow, eval_C, eval_X, hsame, sub_self]

/-- Testing only pairs with equal sums and equal second elementary
symmetric coefficients suffices in each fixed order. The nonconstant
variance numerator is obtained by a one-entry approximation. -/
theorem conjecture_iff_equal_first_second_elementary :
    Conjecture (Fin n) ↔ ∀ (a b : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ),
      IsUnitary U → (∑ i, a i) = (∑ i, b i) →
      spectralSecondElementary a = spectralSecondElementary b → Holds a b U := by
  constructor
  · intro h a b U hU _ _
    exact h a b U hU
  · intro h
    by_cases hn : 2 ≤ n
    · have hn₀ : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
      have hn₁ : (n : ℂ) - 1 ≠ 0 := by
        apply sub_ne_zero.mpr
        exact_mod_cast (show n ≠ 1 by omega)
      apply conjecture_iff_regular_matching_products.mpr
      intro a b U hU hnonzero hinj
      let c (i : Fin n) := -b i
      have ha : Function.Injective a := injective_first_of_matchingProduct a b hinj
      have hb : Function.Injective b := injective_second_of_matchingProduct a b hinj
      have hc : Function.Injective c := fun i j he => hb (neg_injective he)
      have hac (i j : Fin n) : a i ≠ c j :=
        fun he => hnonzero i j ((eq_neg_iff_add_eq_zero).mp he)
      let k : Fin n := ⟨0, by omega⟩
      let Cₜ := perturbSpectralEntry c k
      let B (t : ℂ) (i : Fin n) := -Cₜ t i
      have hCzero : Cₜ 0 = c := perturbSpectralEntry_zero c k
      have hBzero : B 0 = b := by
        funext i
        simp only [B, hCzero, c, neg_neg]
      have hCcont : Continuous Cₜ := continuous_perturbSpectralEntry c k
      have hpoint (i : Fin n) : Continuous (fun t => Cₜ t i) :=
        (continuous_apply i).comp hCcont
      have hBcont : Continuous B := continuous_pi fun i => (hpoint i).neg
      have hCinj : ∀ᶠ t in 𝓝 (0 : ℂ), Function.Injective (Cₜ t) := by
        apply Filter.eventually_all.mpr
        intro i
        apply Filter.eventually_all.mpr
        intro j
        by_cases hij : i = j
        · exact Filter.Eventually.of_forall fun t _ => hij
        · have h₀ : Cₜ 0 i ≠ Cₜ 0 j := by
            rw [hCzero]
            exact hc.ne hij
          filter_upwards [(isOpen_ne_fun (hpoint i) (hpoint j)).mem_nhds h₀] with t ht
          exact fun he => (ht he).elim
      have hcross : ∀ᶠ t in 𝓝 (0 : ℂ), ∀ i j, a i ≠ Cₜ t j := by
        apply Filter.eventually_all.mpr
        intro i
        apply Filter.eventually_all.mpr
        intro j
        have h₀ : a i ≠ Cₜ 0 j := by rw [hCzero]; exact hac i j
        exact (isOpen_ne_fun continuous_const (hpoint j)).mem_nhds h₀
      have hdeg : ∀ᶠ t in 𝓝[≠] (0 : ℂ), (inverseSpectralVarianceDifference a (Cₜ t)).degree ≠ 0 :=
        eventually_varianceDifference_nonconstant a c hn ha hac
      have hnear : ∀ᶠ t in 𝓝[≠] (0 : ℂ), Holds a (B t) U := by
        filter_upwards [hCinj.filter_mono nhdsWithin_le_nhds,
          hcross.filter_mono nhdsWithin_le_nhds, hdeg] with t hct hact hN
        obtain ⟨p, hp⟩ := IsAlgClosed.exists_root (inverseSpectralVarianceDifference a (Cₜ t)) hN
        obtain ⟨hpa, hpc⟩ :=
          inverseSpectralVarianceDifference_root_off a (Cₜ t) hn₁ ha hct hact hp
        have hV := variance_eq_of_pole a (Cₜ t) p hpa hpc hp
        exact holds_of_inverse_variance_pole a (B t) U hU hn₀
          (fun A B he₁ he₂ => h A B U hU he₁ he₂) p hpa
          (fun j => by simpa only [B, neg_neg] using hpc j) (by simpa only [B, neg_neg] using hV)
      simpa only [hBzero] using spectral_holds_of_nearby U continuous_const hBcont hnear
    · exact conjecture_le_three (by omega)

end

end MOC
