import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.LinearAlgebra.Lagrange

/-! The elementary secular polynomial and derivative identities for a
Hermitian rank-one isospectral chamber. -/

open BigOperators Finset Filter Polynomial
open scoped Topology

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The residue of the rank-one secular rational function at diagonal
coordinate `i`. -/
def secularResidue {K : Type*} [Field K] (h d : ι → K) (i : ι) : K :=
  -(∏ j, (d i - h j)) / ∏ j ∈ univ.erase i, (d i - d j)

omit [Fintype ι] [DecidableEq ι] in
private theorem degree_secular_nodal_product {K : Type*} [Field K]
    (d : ι → K) (s : Finset ι) :
    (∏ i ∈ s, (X - C (d i))).degree = (s.card : WithBot ℕ) := by
  rw [degree_prod_of_monic s (fun i => X - C (d i)) (fun i _ => monic_X_sub_C (d i))]
  simp

/-- The residues reconstruct the characteristic polynomial at all points.
Distinctness of the diagonal nodes is the only interpolation hypothesis. -/
theorem secular_polynomial_identity {K : Type*} [Field K] (h d : ι → K)
    (hd : Function.Injective d) :
    (∏ i, (X - C (d i))) - (∏ i, (X - C (h i))) =
      ∑ i, C (secularResidue h d i) * ∏ j ∈ univ.erase i, (X - C (d j)) := by
  let P := ∏ i, (X - C (d i))
  let H := ∏ i, (X - C (h i))
  let Q := ∑ i, C (secularResidue h d i) * ∏ j ∈ univ.erase i, (X - C (d j))
  change P - H = Q
  have hP : P.Monic := monic_prod_X_sub_C d univ
  have hH : H.Monic := monic_prod_X_sub_C h univ
  have hPD : P.degree = ((univ : Finset ι).card : WithBot ℕ) :=
    degree_secular_nodal_product d univ
  have hHD : H.degree = ((univ : Finset ι).card : WithBot ℕ) :=
    degree_secular_nodal_product h univ
  have hPH : (P - H).degree < ((univ : Finset ι).card : WithBot ℕ) := by
    rw [← hPD]
    exact degree_sub_lt (hPD.trans hHD.symm) hP.ne_zero (hP.leadingCoeff.trans hH.leadingCoeff.symm)
  have hQ : Q.degree < ((univ : Finset ι).card : WithBot ℕ) := by
    by_cases he : (univ : Finset ι) = ∅
    · simp [Q, he]
    · have hu : (univ : Finset ι).Nonempty := nonempty_iff_ne_empty.mpr he
      have hsize : ((univ : Finset ι).card - 1 : ℕ) < (univ : Finset ι).card := by
        exact Nat.sub_lt (card_pos.mpr hu) (by decide)
      refine (degree_sum_le _ _).trans_lt ((Finset.sup_le fun i hi => ?_).trans_lt
        (WithBot.coe_lt_coe.mpr hsize))
      have hdeg := degree_secular_nodal_product d ((univ : Finset ι).erase i)
      rw [card_erase_of_mem hi] at hdeg
      by_cases hz : secularResidue h d i = 0
      · simp [hz]
      · exact (degree_C_mul hz).le.trans hdeg.le
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq (v := d) univ hd.injOn hPH hQ
  intro i hi
  have hP0 : P.eval (d i) = 0 := by
    simp only [P, eval_prod, eval_sub, eval_X, eval_C]
    exact prod_eq_zero hi (sub_self _)
  rw [eval_sub, hP0, zero_sub]
  have heval : Q.eval (d i) = secularResidue h d i * ∏ j ∈ univ.erase i, (d i - d j) := by
    simp only [Q, eval_finset_sum, eval_mul, eval_prod, eval_C, eval_sub, eval_X]
    apply sum_eq_single i
    · intro j _ hji
      rw [prod_eq_zero (mem_erase.mpr ⟨Ne.symm hji, hi⟩) (sub_self (d i)), mul_zero]
    · exact fun hi' => (hi' hi).elim
  rw [heval, secularResidue]
  rw [div_mul_cancel₀ _ (prod_ne_zero_iff.mpr fun j hj =>
    sub_ne_zero.mpr (hd.ne (Ne.symm (ne_of_mem_erase hj))))]
  simp only [H, eval_prod, eval_sub, eval_X, eval_C]

/-- The sum of the residues is the trace change. -/
theorem sum_secularResidue {K : Type*} [Field K] (h d : ι → K)
    (hd : Function.Injective d) :
    ∑ i, secularResidue h d i = (∑ i, h i) - ∑ i, d i := by
  let n := Fintype.card ι
  by_cases hn : n = 0
  · letI : IsEmpty ι := Fintype.card_eq_zero_iff.mp hn
    simp
  have hnp : 0 < n := Nat.pos_of_ne_zero hn
  have hcoeff := congrArg (fun p : K[X] => p.coeff (n-1)) (secular_polynomial_identity h d hd)
  have hdegree (z : ι → K) (s : Finset ι) :
      (∏ i ∈ s, (X - C (z i))).natDegree = s.card := by
    exact natDegree_eq_of_degree_eq_some (degree_secular_nodal_product z s)
  have hnext (z : ι → K) :
      (∏ i, (X - C (z i))).coeff (n-1) = -(∑ i, z i) := by
    have h := Monic.nextCoeff_prod (univ : Finset ι) (fun i => X - C (z i))
      (fun i _ => monic_X_sub_C (z i))
    have hdegree' : 0 < (∏ i, (X - C (z i))).natDegree := by
      rw [hdegree, card_univ]
      exact hnp
    rw [nextCoeff_of_natDegree_pos hdegree', hdegree, card_univ] at h
    simpa only [nextCoeff_X_sub_C, sum_neg_distrib, n] using h
  have hmono (i : ι) :
      (∏ j ∈ univ.erase i, (X - C (d j))).coeff (n - 1) = 1 := by
    have hm : (∏ j ∈ univ.erase i, (X - C (d j))).Monic := monic_prod_X_sub_C d _
    simpa only [hdegree, card_erase_of_mem (mem_univ i), card_univ, n] using hm.coeff_natDegree
  simp only [coeff_sub, hnext, finset_sum_coeff, coeff_C_mul, hmono, mul_one] at hcoeff
  linear_combination -hcoeff

/-- Moving one diagonal node changes every other residue by a scalar
inverse whose derivative is explicit. -/
theorem hasDerivAt_secularResidue_update_of_ne (h d : ι → ℝ) {i j : ι}
    (hij : i ≠ j) (hd : d i ≠ d j) :
    HasDerivAt (fun t => secularResidue h (Function.update d i t) j)
      (secularResidue h d j / (d j - d i)) (d i) := by
  let S := (univ : Finset ι).erase j
  let c := -(∏ k, (d j - h k)) / ∏ k ∈ S.erase i, (d j - d k)
  have hi : i ∈ S := mem_erase.mpr ⟨hij, mem_univ _⟩
  have he (t : ℝ) :
      secularResidue h (Function.update d i t) j = c / (d j - t) := by
    have hq : (∏ k ∈ S, (d j - Function.update d i t k)) =
        (∏ k ∈ S.erase i, (d j - d k)) * (d j - t) := by
      calc
        _ = (∏ k ∈ S.erase i, (d j - Function.update d i t k)) *
            (d j - Function.update d i t i) := (prod_erase_mul _ _ hi).symm
        _ = _ := by
          rw [Function.update_self]
          congr 1
          exact prod_congr rfl fun k hk => by rw [Function.update_of_ne (ne_of_mem_erase hk)]
    unfold secularResidue
    rw [Function.update_of_ne (Ne.symm hij)]
    change -(∏ k, (d j - h k)) / (∏ k ∈ S, (d j - Function.update d i t k)) = _
    rw [hq]
    simp only [c, div_div]
  have hz : d j - d i ≠ 0 := sub_ne_zero.mpr (Ne.symm hd)
  have hden : HasDerivAt (fun t : ℝ => d j - t) (0 - 1) (d i) :=
    HasDerivAt.sub (hasDerivAt_const (d i) (d j)) (hasDerivAt_id' (d i))
  have hh := (hasDerivAt_const (d i) c).div hden hz
  rw [show (fun t => secularResidue h (Function.update d i t) j) =
    (fun t => c / (d j - t)) from funext he]
  convert hh using 1
  have hval : secularResidue h d j = c / (d j - d i) := by simpa using he (d i)
  rw [hval, div_div]
  ring

/-- An injective list of nodes stays injective under a small motion of
one coordinate. -/
theorem eventually_injective_single_coordinate_update (d : ι → ℝ)
    (hd : Function.Injective d) (i : ι) :
    ∀ᶠ t in 𝓝 (d i), Function.Injective (Function.update d i t) := by
  have hsep : ∀ᶠ t in 𝓝 (d i), ∀ j, j ≠ i → t ≠ d j := by
    apply Filter.eventually_all.mpr
    intro j
    by_cases hj : j = i
    · exact Eventually.of_forall fun _ h => (h hj).elim
    · have hO : IsOpen {t : ℝ | t ≠ d j} :=
        isOpen_ne_fun continuous_id continuous_const
      have hE : ∀ᶠ t in 𝓝 (d i), t ≠ d j :=
        hO.mem_nhds (show d i ≠ d j from hd.ne (Ne.symm hj))
      exact hE.mono fun _ h _ => h
  filter_upwards [hsep] with t ht
  intro j k he
  by_cases hj : j = i
  · subst j
    by_cases hk : i = k
    · exact hk
    · exact (ht k (Ne.symm hk)
        (by simpa only [Function.update_self, Function.update_of_ne (Ne.symm hk)] using he)).elim
  · by_cases hk : k = i
    · subst k
      exact (ht j hj (by simpa only [Function.update_self, Function.update_of_ne hj] using he.symm)).elim
    · exact hd (by simpa only [Function.update_of_ne hj, Function.update_of_ne hk] using he)

/-- The moving residue derivative follows by subtracting the derivatives
of the remaining residues from the trace derivative. -/
theorem hasDerivAt_secularResidue_update_self (h d : ι → ℝ)
    (hd : Function.Injective d) (i : ι) :
    HasDerivAt (fun t => secularResidue h (Function.update d i t) i)
      (-1 - ∑ j ∈ univ.erase i, secularResidue h d j / (d j - d i)) (d i) := by
  let S := (univ : Finset ι).erase i
  let c := (∑ j, h j) - ∑ j ∈ S, d j
  have H (j : ι) (hj : j ∈ S) :
      HasDerivAt (fun t => secularResidue h (Function.update d i t) j)
        (secularResidue h d j / (d j - d i)) (d i) := by
    have hne : i ≠ j := Ne.symm (ne_of_mem_erase hj)
    exact hasDerivAt_secularResidue_update_of_ne h d hne (hd.ne hne)
  have hs : HasDerivAt (fun t => ∑ j ∈ S, secularResidue h (Function.update d i t) j)
      (∑ j ∈ S, secularResidue h d j / (d j - d i)) (d i) := HasDerivAt.sum H
  have hc : HasDerivAt (fun t => c - t) (-1) (d i) := by
    simpa only [zero_sub] using
      HasDerivAt.sub (hasDerivAt_const (d i) c) (hasDerivAt_id' (d i))
  apply (HasDerivAt.sub hc hs).congr_of_eventuallyEq
  filter_upwards [eventually_injective_single_coordinate_update d hd i] with t ht
  have hsD : (∑ j, Function.update d i t j) = (∑ j ∈ S, d j) + t := by
    rw [← sum_erase_add univ (fun j => Function.update d i t j) (mem_univ i),
      Function.update_self]
    congr 1
    exact sum_congr rfl fun j hj => Function.update_of_ne (ne_of_mem_erase hj) _ _
  have hr := sum_secularResidue h (Function.update d i t) ht
  rw [hsD, ← sum_erase_add univ (fun j => secularResidue h (Function.update d i t) j) (mem_univ i)] at hr
  change secularResidue h (Function.update d i t) i =
    (∑ j, h j) - (∑ j ∈ S, d j) - t - ∑ j ∈ S, secularResidue h (Function.update d i t) j
  linarith

/-- The retained characteristic polynomial in diagonal-node coordinates,
using the determinant convention \(H[S]-zI\). -/
def secularLinearMinor (h d : ι → ℝ) (S : Finset ι) (z : ℝ) : ℝ :=
  (∏ j ∈ S, (d j - z)) +
    ∑ j ∈ S, secularResidue h d j * ∏ k ∈ S.erase j, (d k - z)

private theorem hasDerivAt_nodal_product_update (d : ι → ℝ) (S : Finset ι)
    (z : ℝ) (i : ι) :
    HasDerivAt (fun t => ∏ j ∈ S, (Function.update d i t j - z))
      (if i ∈ S then ∏ j ∈ S.erase i, (d j - z) else 0) (d i) := by
  by_cases hi : i ∈ S
  · have he (t : ℝ) : (∏ j ∈ S, (Function.update d i t j - z)) =
          (t-z) * ∏ j ∈ S.erase i, (d j - z) := by
      rw [← prod_erase_mul S (fun j => Function.update d i t j - z) hi,
        Function.update_self, mul_comm]
      congr 1
      exact prod_congr rfl fun _ hj => by rw [Function.update_of_ne (ne_of_mem_erase hj)]
    rw [if_pos hi, show (fun t => ∏ j ∈ S, (Function.update d i t j - z)) =
      (fun t => (t-z) * ∏ j ∈ S.erase i, (d j - z)) from funext he]
    simpa only [one_mul] using
      ((hasDerivAt_id' (d i)).sub_const z).mul_const (∏ j ∈ S.erase i, (d j-z))
  · have he (t : ℝ) : (∏ j ∈ S, (Function.update d i t j - z)) = ∏ j ∈ S, (d j-z) :=
      prod_congr rfl fun j hj => by
        have hji : j ≠ i := fun h => hi (h ▸ hj)
        rw [Function.update_of_ne hji]
    rw [if_neg hi, show (fun t => ∏ j ∈ S, (Function.update d i t j - z)) =
      (fun _ => ∏ j ∈ S, (d j-z)) from funext he]
    exact hasDerivAt_const _ _

/-- The derivative of a retained rank-one minor couples one retained
coordinate to one deleted coordinate. -/
theorem hasDerivAt_secularLinearMinor_update (h d : ι → ℝ)
    (hd : Function.Injective d) (S : Finset ι) (z : ℝ) (i : ι) :
    HasDerivAt (fun t => secularLinearMinor h (Function.update d i t) S z)
      (if i ∈ S then
        (∏ j ∈ S.erase i, (d j-z)) *
          ∑ j ∈ Sᶜ, secularResidue h d j / (d i-d j)
       else
        ∑ j ∈ S, secularResidue h d j / (d j-d i) * ∏ k ∈ S.erase j, (d k-z))
      (d i) := by
  let P (U : Finset ι) := ∏ j ∈ U, (d j-z)
  let r := secularResidue h d
  let r' (j : ι) := if j = i then -1 - ∑ j ∈ univ.erase i, r j / (d j-d i)
    else r j / (d j-d i)
  have hr (j : ι) : HasDerivAt (fun t => secularResidue h (Function.update d i t) j) (r' j) (d i) := by
    by_cases hj : j = i
    · subst j
      simpa only [r', if_pos rfl] using hasDerivAt_secularResidue_update_self h d hd i
    · simpa only [r', if_neg hj] using
        hasDerivAt_secularResidue_update_of_ne h d (Ne.symm hj) (hd.ne (Ne.symm hj))
  have hs (j : ι) :
      HasDerivAt (fun t => secularResidue h (Function.update d i t) j *
          ∏ k ∈ S.erase j, (Function.update d i t k-z))
        (r' j * P (S.erase j) + r j * (if i ∈ S.erase j then P ((S.erase j).erase i) else 0))
        (d i) := by
    have hh := (hr j).mul (hasDerivAt_nodal_product_update d (S.erase j) z i)
    simpa only [Function.update_eq_self, P, r, mul_comm, add_comm] using hh
  have hh := (hasDerivAt_nodal_product_update d S z i).add (HasDerivAt.sum fun j (_ : j ∈ S) => hs j)
  unfold secularLinearMinor
  convert hh using 1
  change (if i ∈ S then P (S.erase i) * ∑ j ∈ Sᶜ, r j / (d i-d j) else
    ∑ j ∈ S, r j / (d j-d i) * P (S.erase j)) =
    (if i ∈ S then P (S.erase i) else 0) +
      ∑ j ∈ S, (r' j * P (S.erase j) + r j * (if i ∈ S.erase j then P ((S.erase j).erase i) else 0))
  by_cases hi : i ∈ S
  · rw [if_pos hi, if_pos hi, ← sum_erase_add S _ hi]
    have he (j : ι) (hj : j ∈ S.erase i) :
        r' j * P (S.erase j) + r j * (if i ∈ S.erase j then P ((S.erase j).erase i) else 0) =
          P (S.erase i) * (r j / (d j-d i)) := by
      have hji : j ≠ i := ne_of_mem_erase hj
      have hjS : j ∈ S := mem_of_mem_erase hj
      have hi' : i ∈ S.erase j := mem_erase.mpr ⟨Ne.symm hji, hi⟩
      have hP₁ : P (S.erase j) = P ((S.erase j).erase i) * (d i-z) :=
        (prod_erase_mul _ _ hi').symm
      have hP₂ : P (S.erase i) = P ((S.erase j).erase i) * (d j-z) := by
        rw [erase_right_comm (s := S) (a := j) (b := i)]
        exact (prod_erase_mul _ _ hj).symm
      simp only [if_pos hi', r', if_neg hji, hP₁, hP₂]
      field_simp [sub_ne_zero.mpr (hd.ne hji)]
      ring
    rw [sum_congr rfl he, ← mul_sum, if_neg (not_mem_erase i S), mul_zero, add_zero]
    simp only [r', if_pos rfl]
    have hsplit : (∑ j ∈ univ.erase i, r j / (d j-d i)) =
        (∑ j ∈ S.erase i, r j / (d j-d i)) + ∑ j ∈ Sᶜ, r j / (d j-d i) := by
      have hu : S.erase i ∪ Sᶜ = univ.erase i := by
        ext j
        simp only [mem_union, mem_erase, mem_compl, mem_univ, and_true]
        by_cases hj : j = i
        · subst j; simp [hi]
        · simp [hj, em (j ∈ S)]
      have hD : Disjoint (S.erase i) Sᶜ := by
        rw [disjoint_left]
        exact fun j hj hc => (mem_compl.mp hc) (mem_of_mem_erase hj)
      rw [← hu, sum_union hD]
    have hn : (∑ j ∈ Sᶜ, r j / (d i-d j)) = -(∑ j ∈ Sᶜ, r j / (d j-d i)) := by
      rw [← sum_neg_distrib]
      exact sum_congr rfl fun j _ => by rw [← neg_sub (d j) (d i), div_neg]
    rw [hsplit, hn]
    ring
  · rw [if_neg hi, if_neg hi, zero_add]
    apply sum_congr rfl
    intro j hj
    have hji : j ≠ i := fun he => hi (he ▸ hj)
    have hi' : i ∉ S.erase j := fun h => hi (mem_of_mem_erase h)
    simp only [r', if_neg hji, if_neg hi', mul_zero, add_zero]

private theorem hasDerivAt_divided_secularResidue_update (h d : ι → ℝ) {i j : ι}
    (hij : i ≠ j) (hd : d i ≠ d j) :
    HasDerivAt (fun t => secularResidue h (Function.update d i t) j / (d j-t))
      (2 * secularResidue h d j / (d j-d i)^2) (d i) := by
  have hden : HasDerivAt (fun t : ℝ => d j - t) (0 - 1) (d i) :=
    HasDerivAt.sub (hasDerivAt_const (d i) (d j)) (hasDerivAt_id' (d i))
  have hz : d j - d i ≠ 0 := sub_ne_zero.mpr (Ne.symm hd)
  have hh := (hasDerivAt_secularResidue_update_of_ne h d hij hd).div hden hz
  convert hh using 1
  rw [Function.update_eq_self, div_mul_cancel₀ _ hz]
  ring

/-- A second pure derivative of the retained characteristic polynomial
is a sum of inverse-square interactions across its coordinate cut. -/
theorem hasSecondDerivAt_secularLinearMinor_update (h d : ι → ℝ)
    (hd : Function.Injective d) (S : Finset ι) (z : ℝ) (i : ι) :
    HasDerivAt (deriv (fun t => secularLinearMinor h (Function.update d i t) S z))
      (if i ∈ S then
        -(∏ j ∈ S.erase i, (d j-z)) *
          ∑ j ∈ Sᶜ, 2 * secularResidue h d j / (d j-d i)^2
       else
        ∑ j ∈ S, (2 * secularResidue h d j / (d j-d i)^2) *
          ∏ k ∈ S.erase j, (d k-z))
      (d i) := by
  let P (U : Finset ι) := ∏ j ∈ U, (d j-z)
  let v (j : ι) (t : ℝ) := secularResidue h (Function.update d i t) j / (d j-t)
  let w (j : ι) := 2 * secularResidue h d j / (d j-d i)^2
  have hP (U : Finset ι) (hi : i ∉ U) (t : ℝ) :
      (∏ j ∈ U, (Function.update d i t j-z)) = P U := by
    exact prod_congr rfl fun j hj => by
      have hji : j ≠ i := fun h => hi (h ▸ hj)
      rw [Function.update_of_ne hji]
  have hV (j : ι) (hji : j ≠ i) : HasDerivAt (v j) (w j) (d i) :=
    hasDerivAt_divided_secularResidue_update h d (Ne.symm hji) (hd.ne (Ne.symm hji))
  have hgrad (t : ℝ) (ht : Function.Injective (Function.update d i t)) :
      deriv (fun s => secularLinearMinor h (Function.update d i s) S z) t =
        if i ∈ S then
          (∏ j ∈ S.erase i, (Function.update d i t j-z)) *
            ∑ j ∈ Sᶜ, secularResidue h (Function.update d i t) j /
              (t - Function.update d i t j)
        else
          ∑ j ∈ S, secularResidue h (Function.update d i t) j /
            (Function.update d i t j-t) *
            ∏ k ∈ S.erase j, (Function.update d i t k-z) := by
    simpa only [Function.update_self, Function.update_idem] using
      (hasDerivAt_secularLinearMinor_update h (Function.update d i t) ht S z i).deriv
  by_cases hi : i ∈ S
  · rw [if_pos hi]
    have hv : HasDerivAt (fun t => ∑ j ∈ Sᶜ, v j t) (∑ j ∈ Sᶜ, w j) (d i) :=
      HasDerivAt.sum fun j hj => hV j (fun h => (mem_compl.mp hj) (h ▸ hi))
    apply (hv.const_mul (-(P (S.erase i)))).congr_of_eventuallyEq
    filter_upwards [eventually_injective_single_coordinate_update d hd i] with t ht
    rw [hgrad t ht, if_pos hi, hP _ (not_mem_erase i S)]
    have he : (∑ j ∈ Sᶜ, secularResidue h (Function.update d i t) j /
        (t - Function.update d i t j)) = -(∑ j ∈ Sᶜ, v j t) := by
      rw [← sum_neg_distrib]
      apply sum_congr rfl
      intro j hj
      have hji : j ≠ i := fun h => (mem_compl.mp hj) (h ▸ hi)
      simp only [Function.update_of_ne hji, v]
      rw [← neg_sub (d j) t, div_neg]
    rw [he, mul_neg, neg_mul]
  · rw [if_neg hi]
    have hv : HasDerivAt (fun t => ∑ j ∈ S, v j t * P (S.erase j))
        (∑ j ∈ S, w j * P (S.erase j)) (d i) :=
      HasDerivAt.sum fun j hj => (hV j (fun h => hi (h ▸ hj))).mul_const _
    apply hv.congr_of_eventuallyEq
    filter_upwards [eventually_injective_single_coordinate_update d hd i] with t ht
    rw [hgrad t ht, if_neg hi]
    apply sum_congr rfl
    intro j hj
    have hji : j ≠ i := fun h => hi (h ▸ hj)
    rw [hP _ (fun h => hi (mem_of_mem_erase h))]
    simp only [v, Function.update_of_ne hji]

/-- The positive-residue weighted sum of pure second derivatives for
each retained characteristic polynomial is zero. -/
theorem secularLinearMinor_weighted_second_sum (h d : ι → ℝ)
    (hd : Function.Injective d) (S : Finset ι) (z : ℝ) :
    (∑ i, secularResidue h d i *
      deriv (deriv (fun t => secularLinearMinor h (Function.update d i t) S z)) (d i)) = 0 := by
  let r := secularResidue h d
  let P (i : ι) := ∏ j ∈ S.erase i, (d j-z)
  simp_rw [(hasSecondDerivAt_secularLinearMinor_update h d hd S z _).deriv]
  rw [← sum_add_sum_compl S]
  have hA : (∑ i ∈ S, r i * (if i ∈ S then -(P i) *
      ∑ j ∈ Sᶜ, 2 * r j / (d j-d i)^2 else
      ∑ j ∈ S, (2 * r j / (d j-d i)^2) * P j)) =
      -(∑ i ∈ S, ∑ j ∈ Sᶜ, r i * P i * (2 * r j / (d j-d i)^2)) := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro i hi
    simp only [if_pos hi, ← mul_assoc, mul_neg, sum_mul, mul_sum]
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro j _
    ring
  have hB : (∑ i ∈ Sᶜ, r i * (if i ∈ S then -(P i) *
      ∑ j ∈ Sᶜ, 2 * r j / (d j-d i)^2 else
      ∑ j ∈ S, (2 * r j / (d j-d i)^2) * P j)) =
      ∑ i ∈ S, ∑ j ∈ Sᶜ, r i * P i * (2 * r j / (d j-d i)^2) := by
    rw [sum_comm]
    apply sum_congr rfl
    intro j hj
    simp only [if_neg (mem_compl.mp hj), mul_sum]
    apply sum_congr rfl
    intro i _
    rw [← neg_sub (d i) (d j), neg_sq]
    ring
  rw [hA, hB, neg_add_cancel]

end

end MOC
