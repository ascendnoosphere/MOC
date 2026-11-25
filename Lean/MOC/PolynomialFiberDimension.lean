import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Nullstellensatz

/-! A singleton polynomial fiber needs at least as many equations as
coordinates. Counting monomials in finite quotients supplies the dimension
bound without choosing a component of the fiber. -/

open BigOperators MvPolynomial

namespace MOC

noncomputable section

variable {K σ ι : Type*} [Field K] [Fintype σ]

private def highDegreeIdeal (K σ : Type*) [Field K] [Fintype σ] (t : ℕ) :
    Ideal (MvPolynomial σ K) :=
  Ideal.span ((fun e : σ →₀ ℕ => monomial e (1 : K)) '' {e | t ≤ ∑ j, e j})

private theorem highDegreeIdeal_mul (a b : ℕ) :
    highDegreeIdeal K σ a * highDegreeIdeal K σ b ≤ highDegreeIdeal K σ (a + b) := by
  classical
  unfold highDegreeIdeal
  rw [Ideal.span_mul_span']
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨_, ⟨u, hu, rfl⟩, _, ⟨v, hv, rfl⟩, rfl⟩
  change monomial u (1 : K) * monomial v (1 : K) ∈ _
  rw [monomial_mul, one_mul]
  apply Ideal.subset_span
  refine ⟨u + v, ?_, rfl⟩
  simpa only [Set.mem_setOf_eq, Finsupp.add_apply, Finset.sum_add_distrib] using
    Nat.add_le_add hu hv

private theorem highDegreeIdeal_pow (t : ℕ) :
    highDegreeIdeal K σ 1 ^ t ≤ highDegreeIdeal K σ t := by
  classical
  induction t with
  | zero =>
    have h : (1 : MvPolynomial σ K) ∈ highDegreeIdeal K σ 0 := by
      apply Ideal.subset_span
      refine ⟨0, Nat.zero_le _, ?_⟩
      change monomial 0 (1 : K) = 1
      rw [monomial_zero', C_1]
    simp [(Ideal.eq_top_iff_one _).mpr h]
  | succ t ih =>
    rw [pow_succ]
    exact (Ideal.mul_mono_left ih).trans (highDegreeIdeal_mul t 1)

private theorem mem_highDegreeIdeal_one {p : MvPolynomial σ K} (h : eval 0 p = 0) :
    p ∈ highDegreeIdeal K σ 1 := by
  classical
  refine mem_ideal_span_monomial_image.mpr ?_
  intro e he
  refine ⟨e, ?_, le_rfl⟩
  have he0 : e ≠ 0 := by
    rintro rfl
    exact (mem_support_iff.mp he) (by simpa only [eval_zero, constantCoeff_eq] using h)
  obtain ⟨j, hj⟩ : ∃ j, e j ≠ 0 := by
    by_contra! hzero
    exact he0 (Finsupp.ext hzero)
  exact (Nat.one_le_iff_ne_zero.mpr hj).trans
    (Finset.single_le_sum (fun j _ => Nat.zero_le (e j)) (Finset.mem_univ j))

private def boxExponent (N : ℕ) (x : σ → Fin N) : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (x i : ℕ))

private theorem boxExponent_injective {N : ℕ} :
    Function.Injective (boxExponent (σ := σ) N) := by
  intro x y h
  funext i
  exact Fin.ext (congrArg (fun e : σ →₀ ℕ => e i) h)

private theorem boxSpan_sup_ideal (I : Ideal (MvPolynomial σ K)) (N : ℕ)
    (hN : ∀ j, (X j : MvPolynomial σ K) ^ N ∈ I) (p : MvPolynomial σ K) :
    p ∈ Submodule.span K (Set.range (fun x : σ → Fin N => monomial (boxExponent N x) 1)) ⊔
      I.restrictScalars K := by
  classical
  rw [p.as_sum]
  apply Submodule.sum_mem
  intro e _
  rw [show monomial e (coeff e p) = coeff e p • monomial e 1 by
    simp [smul_monomial]]
  apply Submodule.smul_mem
  by_cases he : ∀ j, e j < N
  · apply Submodule.mem_sup_left
    exact Submodule.subset_span ⟨fun j => ⟨e j, he j⟩,
      congrArg (fun u : σ →₀ ℕ => monomial u (1 : K)) (Finsupp.ext fun _ => rfl)⟩
  · push_neg at he
    obtain ⟨j, hj⟩ := he
    apply Submodule.mem_sup_right
    change monomial e (1 : K) ∈ I
    apply I.mem_of_dvd ?_ (hN j)
    rw [X_pow_eq_monomial, monomial_one_dvd_monomial_one, Finsupp.single_le_iff]
    exact hj

variable [Fintype ι]

private theorem span_box_products (p : ι → MvPolynomial σ K) (N t : ℕ)
    (hN : ∀ j, (X j : MvPolynomial σ K) ^ N ∈ Ideal.span (Set.range p)) :
    let J := Ideal.span (Set.range (fun i => p i ^ t))
    Submodule.span K (Set.range (fun x : (σ → Fin N) × (ι → Fin t) =>
      Ideal.Quotient.mkₐ K J
        (monomial (boxExponent N x.1) 1 * ∏ i, p i ^ (x.2 i : ℕ)))) = ⊤ := by
  classical
  dsimp only
  let I := Ideal.span (Set.range p)
  let J := Ideal.span (Set.range (fun i => p i ^ t))
  let q := Ideal.Quotient.mkₐ K J
  let W := Submodule.span K (Set.range (fun x : (σ → Fin N) × (ι → Fin t) =>
    q (monomial (boxExponent N x.1) 1 * ∏ i, p i ^ (x.2 i : ℕ))))
  let prod (b : ι → ℕ) := ∏ i, p i ^ b i
  let count (b : ι → ℕ) := Fintype.card ι * t + 1 - ∑ i, b i
  have hall : ∀ n : ℕ, ∀ b : ι → ℕ, count b = n →
      ∀ u : MvPolynomial σ K, q (u * prod b) ∈ W := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro b hn u
      by_cases hb : ∀ i, b i < t
      · let bf : ι → Fin t := fun i => ⟨b i, hb i⟩
        have hbound : (∑ i, b i) ≤ Fintype.card ι * t := by
          calc
            (∑ i, b i) ≤ ∑ _i : ι, t :=
              Finset.sum_le_sum fun i _ => (hb i).le
            _ = Fintype.card ι * t := by simp
        obtain ⟨v, hv, r, hr, huv⟩ := Submodule.mem_sup.mp (boxSpan_sup_ideal I N hN u)
        obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hv
        obtain ⟨d, hd⟩ := Ideal.mem_span_range_iff_exists_fun.mp (show r ∈ I from hr)
        simp only [← huv, add_mul, map_add, ← hc, ← hd, Finset.sum_mul, map_sum]
        apply W.add_mem
        · apply W.sum_mem
          intro x _
          rw [smul_mul_assoc, map_smul]
          exact W.smul_mem (c x) (Submodule.subset_span ⟨(x, bf), rfl⟩)
        · apply W.sum_mem
          intro i _
          let bi := b + Pi.single i 1
          have hsingle : (∏ j, p j ^ (Pi.single i 1 : ι → ℕ) j) = p i := by
            rw [Finset.prod_eq_single i]
            · simp
            · intro j _ hj
              simp [Pi.single_eq_of_ne hj]
            · simp
          have hprod : prod bi = p i * prod b := by
            simp only [prod, bi, Pi.add_apply, pow_add, Finset.prod_mul_distrib]
            rw [hsingle, mul_comm]
          have hcount : count bi < n := by
            have hsum : (∑ j, bi j) = (∑ j, b j) + 1 := by
              simp [bi, Finset.sum_add_distrib]
            change Fintype.card ι * t + 1 - (∑ j, bi j) < n
            dsimp only [count] at hn
            omega
          change q ((d i * p i) * prod b) ∈ W
          rw [mul_assoc, ← hprod]
          exact ih _ hcount bi rfl (d i)
      · push_neg at hb
        obtain ⟨i, hi⟩ := hb
        have hpi : p i ^ b i ∈ J :=
          J.pow_mem_of_pow_mem (Ideal.subset_span ⟨i, rfl⟩) hi
        have hprod : prod b ∈ J := by
          dsimp only [prod]
          rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
          exact J.mul_mem_left _ hpi
        have hz : q (u * prod b) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr (J.mul_mem_left _ hprod)
        rw [hz]
        exact W.zero_mem
  change W = ⊤
  apply top_unique
  intro y _
  obtain ⟨u, rfl⟩ := Ideal.Quotient.mkₐ_surjective K J y
  simpa [prod] using hall (count 0) 0 rfl u

/-- Over an algebraically closed field, a system of polynomials with the
origin as its only zero has at least as many equations as variables. -/
theorem card_variables_le_of_singleton_zeroLocus [IsAlgClosed K]
    (p : ι → MvPolynomial σ K)
    (hzero : zeroLocus (Ideal.span (Set.range p)) = {0}) :
    Fintype.card σ ≤ Fintype.card ι := by
  classical
  let I := Ideal.span (Set.range p)
  have hX (j : σ) : ∃ n : ℕ, (X j : MvPolynomial σ K) ^ n ∈ I := by
    apply Ideal.mem_radical_iff.mp
    rw [← vanishingIdeal_zeroLocus_eq_radical, hzero]
    exact (mem_vanishingIdeal_singleton_iff 0 _).mpr (by simp)
  choose power hpower using hX
  let N := ∑ j, power j
  have hN (j : σ) : (X j : MvPolynomial σ K) ^ N ∈ I :=
    I.pow_mem_of_pow_mem (hpower j)
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j))
  by_contra! hcard
  let D := Fintype.card σ
  let k := Fintype.card ι
  let s := N ^ D * D ^ k + 1
  let t := D * s
  let J := Ideal.span (Set.range (fun i => p i ^ t))
  let q := Ideal.Quotient.mkₐ K J
  have hJ : J ≤ highDegreeIdeal K σ t := by
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    have hpoint : (0 : σ → K) ∈ zeroLocus (Ideal.span (Set.range p)) := by
      rw [hzero]
      exact Set.mem_singleton _
    have hpi : eval 0 (p i) = 0 :=
      (mem_zeroLocus_iff.mp hpoint) _ (Ideal.subset_span ⟨i, rfl⟩)
    exact highDegreeIdeal_pow t (Ideal.pow_mem_pow (mem_highDegreeIdeal_one hpi) t)
  have hspan := span_box_products p N t hN
  dsimp only at hspan
  let v (x : (σ → Fin N) × (ι → Fin t)) : MvPolynomial σ K ⧸ J :=
    q (monomial (boxExponent N x.1) 1 * ∏ i, p i ^ (x.2 i : ℕ))
  change Submodule.span K (Set.range v) = ⊤ at hspan
  have hsurj : Function.Surjective (Fintype.linearCombination K v) := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hspan]
  letI : Module.Finite K (MvPolynomial σ K ⧸ J) :=
    Module.Finite.of_surjective _ hsurj
  have hupper : Module.finrank K (MvPolynomial σ K ⧸ J) ≤ N ^ D * t ^ k := by
    simpa [D, k, Fintype.card_prod, Fintype.card_fun] using
      finrank_le_of_span_eq_top hspan
  have hli : LinearIndependent K (fun x : σ → Fin s => q (monomial (boxExponent s x) 1)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc a
    let m (x : σ → Fin s) : MvPolynomial σ K := monomial (boxExponent s x) 1
    have hz : coeff (boxExponent s a) (∑ x, c x • m x) = 0 := by
      by_contra hne
      have hin : (∑ x, c x • m x) ∈ J := by
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        change q _ = 0
        simpa only [m, map_sum, map_smul] using hc
      have hdeg := mem_ideal_span_monomial_image.mp (hJ hin) _ (mem_support_iff.mpr hne)
      obtain ⟨e, he, hle⟩ := hdeg
      have hu : (∑ j, boxExponent s a j) < t := by
        have hD : 0 < Fintype.card σ := by omega
        letI : Nonempty σ := Fintype.card_pos_iff.mp hD
        calc
          (∑ j, boxExponent s a j) < ∑ _j : σ, s :=
            Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun j _ => (a j).isLt
          _ = t := by simp [t, D]
      exact (not_le_of_gt hu) (he.trans (Finset.sum_le_sum fun j _ => hle j))
    simpa [m, coeff_sum, coeff_smul, coeff_monomial, boxExponent_injective.eq_iff] using hz
  have hlower : s ^ D ≤ Module.finrank K (MvPolynomial σ K ⧸ J) := by
    simpa [D, Fintype.card_fun] using hli.fintype_card_le_finrank
  have hlt : N ^ D * t ^ k < s ^ D := by
    have hs : 0 < s := by simp [s]
    have hle : k + 1 ≤ D := by exact hcard
    calc
      N ^ D * t ^ k = (N ^ D * D ^ k) * s ^ k := by rw [show t = D * s from rfl, mul_pow, mul_assoc]
      _ < s * s ^ k := Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self _) (Nat.pow_pos hs)
      _ = s ^ (k + 1) := by rw [pow_succ, mul_comm]
      _ ≤ s ^ D := Nat.pow_le_pow_right hs hle
  exact (not_le_of_gt hlt) (hlower.trans hupper)

/-- Fewer polynomial equations than coordinates cannot give a singleton fiber. -/
theorem exists_other_point_of_polynomial_fiber [IsAlgClosed K]
    (p : ι → MvPolynomial σ K) (z : σ → K)
    (hcard : Fintype.card ι < Fintype.card σ) :
    ∃ w : σ → K, w ≠ z ∧ ∀ i, eval w (p i) = eval z (p i) := by
  by_contra! hn
  let translate : MvPolynomial σ K →+* MvPolynomial σ K :=
    eval₂Hom C (fun j => X j + C (z j))
  have htranslate (x : σ → K) :
      (eval x).comp translate = eval (fun j => x j + z j) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [translate]
    · intro j
      simp [translate]
  let q (i : ι) := translate (p i) - C (eval z (p i))
  have hq (x : σ → K) (i : ι) :
      eval x (q i) = eval (fun j => x j + z j) (p i) - eval z (p i) := by
    simp only [q, map_sub, eval_C]
    exact congrArg (fun a : K => a - eval z (p i))
      (RingHom.congr_fun (htranslate x) (p i))
  have hzero : zeroLocus (Ideal.span (Set.range q)) = {0} := by
    ext x
    rw [zeroLocus_span, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro hx
      have hvalue (i : ι) : eval (fun j => x j + z j) (p i) = eval z (p i) :=
        sub_eq_zero.mp ((hq x i).symm.trans (hx _ ⟨i, rfl⟩))
      have hsame : (fun j => x j + z j) = z := by
        by_contra hd
        obtain ⟨i, hi⟩ := hn _ hd
        exact hi (hvalue i)
      funext j
      have he := congrFun hsame j
      exact add_right_cancel (he.trans (zero_add (z j)).symm)
    · rintro rfl _ ⟨i, rfl⟩
      rw [hq]
      simp only [Pi.zero_apply, zero_add, sub_self]
  exact (not_le_of_gt hcard) (card_variables_le_of_singleton_zeroLocus q hzero)

set_option maxHeartbeats 800000 in
/-- Clearing one nonvanishing condition with an inverse variable preserves
the strict inequality between the numbers of equations and coordinates. -/
theorem exists_other_regular_point_of_polynomial_fiber [IsAlgClosed K]
    (p : ι → MvPolynomial σ K) (r : MvPolynomial σ K) (z : σ → K)
    (hz : eval z r ≠ 0) (hcard : Fintype.card ι < Fintype.card σ) :
    ∃ w : σ → K, w ≠ z ∧ eval w r ≠ 0 ∧ ∀ i, eval w (p i) = eval z (p i) := by
  let e : σ → σ ⊕ Unit := Sum.inl
  let q : ι ⊕ Unit → MvPolynomial (σ ⊕ Unit) K :=
    Sum.elim (fun i => rename e (p i)) (fun _ => X (.inr ()) * rename e r)
  let z' : σ ⊕ Unit → K := Sum.elim z (fun _ => (eval z r)⁻¹)
  have he : z' ∘ e = z := rfl
  have hcard' : Fintype.card (ι ⊕ Unit) < Fintype.card (σ ⊕ Unit) := by
    simpa using hcard
  obtain ⟨y, hy, hq⟩ := exists_other_point_of_polynomial_fiber q z' hcard'
  let w := y ∘ e
  have hinr (x : σ ⊕ Unit → K) : eval x (q (Sum.inr ())) = x (Sum.inr ()) * eval (x ∘ e) r := by
    simp only [q, Sum.elim_inr, map_mul, eval_X, eval_rename]
  have hinv : y (.inr ()) * eval w r = 1 := by
    simpa only [hinr, he, w,
      show z' (.inr ()) = (eval z r)⁻¹ from rfl, inv_mul_cancel₀ hz] using (hq (Sum.inr ()))
  have hw : eval w r ≠ 0 := by
    intro hr
    rw [hr, mul_zero] at hinv
    exact zero_ne_one hinv
  have hdiff : w ≠ z := by
    intro h
    apply hy
    funext j
    cases j with
    | inl j => exact congrFun h j
    | inr j =>
      cases j
      change y (.inr ()) = (eval z r)⁻¹
      apply mul_right_cancel₀ hz
      rw [inv_mul_cancel₀ hz]
      simpa only [h] using hinv
  refine ⟨w, hdiff, hw, fun i => ?_⟩
  have h := hq (.inl i)
  change eval y (rename e (p i)) = eval z' (rename e (p i)) at h
  simpa only [eval_rename, he] using h

end

end MOC
