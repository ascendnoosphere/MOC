import MOC.MinimumNormalizedSpectralSlice
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Polynomial.Vieta

/-! A real-rooted slice with fixed first coefficient and affine second
coefficient has a bounded constant term. -/

open BigOperators Finset Polynomial

namespace MOC

noncomputable section

private theorem esymm_one_eq_sum (s : Multiset ℝ) : s.esymm 1 = s.sum := by
  simp only [Multiset.esymm, Multiset.powersetCard_one, Multiset.map_map,
    Function.comp_def, Multiset.prod_singleton, Multiset.map_id']

private theorem esymm_two_cons (a : ℝ) (s : Multiset ℝ) :
    (a ::ₘ s).esymm 2 = s.esymm 2 + a * s.esymm 1 := by
  rw [esymm_one_eq_sum]
  simp only [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_add, Multiset.sum_add,
    Multiset.map_map, Function.comp_def, Multiset.prod_cons, Multiset.sum_map_mul_left,
    Multiset.powersetCard_one, Multiset.prod_singleton, Multiset.map_id']

private theorem sum_squares_eq_esymm (s : Multiset ℝ) :
    (s.map fun x => x ^ 2).sum = (s.esymm 1)^2 - 2 * s.esymm 2 := by
  induction s using Multiset.induction_on with
  | empty => simp [Multiset.esymm, Multiset.powersetCard_zero_right]
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, esymm_two_cons, ih]
    simp only [esymm_one_eq_sum, Multiset.sum_cons]
    ring

private theorem square_le_sum_squares_of_mem (s : Multiset ℝ) (x : ℝ) (hx : x ∈ s) :
    x ^ 2 ≤ (s.map fun z => z ^ 2).sum := by
  induction s using Multiset.induction_on with
  | empty => simp at hx
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons]
    rcases Multiset.mem_cons.mp hx with rfl | h
    · exact le_add_of_nonneg_right
        (Multiset.sum_nonneg fun y hy => by
          obtain ⟨z, _, rfl⟩ := Multiset.mem_map.mp hy
          exact sq_nonneg z)
    · exact (ih h).trans (le_add_of_nonneg_left (sq_nonneg a))

private theorem abs_eval_zero_root_product_le (s : Multiset ℝ) (B : ℝ)
    (hB : 0 ≤ B) (hb : ∀ z ∈ s, |z| ≤ B) :
    |((s.map fun z => X - C z).prod).eval 0| ≤ B ^ s.card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, eval_mul, eval_sub, eval_X, eval_C,
      zero_sub, abs_mul, abs_neg, Multiset.card_cons, pow_succ']
    exact mul_le_mul (hb a (Multiset.mem_cons_self _ _))
      (ih fun z hz => hb z (Multiset.mem_cons_of_mem hz)) (abs_nonneg _) hB

/-- A family of split real monic polynomials of fixed degree has uniformly
bounded constant terms if its first coefficient is constant and its second
coefficient is affine. The parameter ranges over all real numbers. -/
theorem bounded_constant_term_of_split_affine_coefficients
    (n : ℕ) (hn : 2 ≤ n) (p : ℝ → ℝ[X]) (A B D : ℝ)
    (hm : ∀ t, (p t).Monic) (hd : ∀ t, (p t).natDegree = n)
    (hs : ∀ t, (p t).Splits (RingHom.id ℝ))
    (hA : ∀ t, (p t).coeff (n - 1) = A)
    (hB : ∀ t, (p t).coeff (n - 2) = B + D * t) :
    ∃ K : ℝ, ∀ t, |(p t).eval 0| ≤ K := by
  have h₁ : n - (n - 1) = 1 := by omega
  have h₂ : n - (n - 2) = 2 := by omega
  have hsum (t : ℝ) : ((p t).roots.map fun x => x ^ 2).sum = A ^ 2 - 2 * B - 2 * D * t := by
    have he₁ := coeff_eq_esymm_roots_of_splits (hs t)
      (k := n - 1) (by rw [hd t]; omega)
    have he₂ := coeff_eq_esymm_roots_of_splits (hs t)
      (k := n - 2) (by rw [hd t]; omega)
    rw [(hm t).leadingCoeff, hd t, h₁, hA t] at he₁
    rw [(hm t).leadingCoeff, hd t, h₂, hB t] at he₂
    have he₁' : (p t).roots.esymm 1 = -A := by
      simp only [one_mul, pow_one, neg_one_mul] at he₁
      linarith only [he₁]
    have he₂' : (p t).roots.esymm 2 = B + D * t := by
      simpa only [one_mul, neg_one_sq] using he₂.symm
    rw [sum_squares_eq_esymm, he₁', he₂']
    ring
  have hnneg (t : ℝ) : 0 ≤ A ^ 2 - 2 * B - 2 * D * t := by
    rw [← hsum t]
    exact Multiset.sum_nonneg fun x hx => by
      obtain ⟨z, _, rfl⟩ := Multiset.mem_map.mp hx
      exact sq_nonneg z
  have hD : D = 0 := by
    by_contra hne
    let t := (A ^ 2 - 2 * B + 1) / (2 * D)
    have ht : 2 * D * t = A ^ 2 - 2 * B + 1 := by
      dsimp only [t]
      rw [mul_comm (2 * D), div_mul_cancel₀ _ (mul_ne_zero two_ne_zero hne)]
    nlinarith only [hnneg t, ht]
  let R := Real.sqrt (A ^ 2 - 2 * B)
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hK : 0 ≤ A ^ 2 - 2 * B := by
    simpa only [mul_zero, sub_zero] using hnneg 0
  refine ⟨R ^ n, fun t => ?_⟩
  have hb : ∀ x ∈ (p t).roots, |x| ≤ R := by
    intro x hx
    apply (sq_le_sq₀ (abs_nonneg _) hR).mp
    rw [sq_abs, Real.sq_sqrt hK]
    have hle := square_le_sum_squares_of_mem (p t).roots x hx
    simpa only [hsum t, hD, mul_zero, zero_mul, sub_zero] using hle
  have hprod := abs_eval_zero_root_product_le (p t).roots R hR hb
  rw [← Polynomial.eq_prod_roots_of_monic_of_splits_id (hm t) (hs t),
    Polynomial.splits_iff_card_roots.mp (hs t), hd t] at hprod
  exact hprod

/-- A real polynomial that agrees with the constant terms of such a family
is constant. -/
theorem polynomial_eq_constant_of_split_affine_coefficients
    (n : ℕ) (hn : 2 ≤ n) (p : ℝ → ℝ[X]) (A B D : ℝ)
    (hm : ∀ t, (p t).Monic) (hd : ∀ t, (p t).natDegree = n)
    (hs : ∀ t, (p t).Splits (RingHom.id ℝ))
    (hA : ∀ t, (p t).coeff (n - 1) = A)
    (hB : ∀ t, (p t).coeff (n - 2) = B + D * t)
    (q : ℝ[X]) (hq : ∀ t, q.eval t = (p t).eval 0) :
    q = C (q.eval 0) := by
  obtain ⟨K, hK⟩ := bounded_constant_term_of_split_affine_coefficients n hn p A B D
    hm hd hs hA hB
  have hdeg : q.degree ≤ 0 := (q.abs_isBoundedUnder_iff).mp
    ⟨K, Filter.eventually_map.mpr (Filter.Eventually.of_forall fun t => by rw [hq]; exact hK t)⟩
  rw [← Polynomial.coeff_zero_eq_eval_zero]
  exact Polynomial.eq_C_of_degree_le_zero hdeg

private def evaluateLine (s : Multiset (ℝ × ℝ)) (t : ℝ) : Multiset ℝ :=
  s.map fun p => p.1 + t * p.2

private theorem esymm_one_line (s : Multiset (ℝ × ℝ)) (t : ℝ) :
    (evaluateLine s t).esymm 1 = (s.map Prod.fst).esymm 1 + t * (s.map Prod.snd).esymm 1 := by
  simp only [evaluateLine, esymm_one_eq_sum, Multiset.sum_map_add, Multiset.sum_map_mul_left]

private theorem esymm_two_line (s : Multiset (ℝ × ℝ)) (t : ℝ) :
    (evaluateLine s t).esymm 2 =
      (s.map Prod.fst).esymm 2 + t * ((evaluateLine s 1).esymm 2 -
        (s.map Prod.fst).esymm 2 - (s.map Prod.snd).esymm 2) + t^2 * (s.map Prod.snd).esymm 2 := by
  induction s using Multiset.induction_on with
  | empty => simp [evaluateLine, Multiset.esymm, Multiset.powersetCard_zero_right]
  | cons a s ih =>
    have hcons (u : ℝ) : evaluateLine (a ::ₘ s) u = (a.1 + u * a.2) ::ₘ evaluateLine s u := by
      simp only [evaluateLine, Multiset.map_cons]
    simp only [hcons, Multiset.map_cons, esymm_two_cons, esymm_one_line, ih, one_mul]
    ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private def shiftedSliceCoordinates (a b : ι → ℝ) (I J : Finset ι) : Multiset (ℝ × ℝ) :=
  (I.val.map fun i => (a i, 1)) + J.val.map fun j => (b j, -1)

private theorem shiftedSliceCoordinates_base (a b : ι → ℝ) (I J : Finset ι) :
    evaluateLine (shiftedSliceCoordinates a b I J) 0 =
      (shiftedSliceCoordinates a b I J).map Prod.fst := by
  simp only [evaluateLine, zero_mul, add_zero]

private theorem shiftedSliceCoordinates_dir (a b : ι → ℝ) (I J : Finset ι) :
    evaluateLine (shiftedSliceCoordinates (fun _ => 0) (fun _ => 0) I J) 1 =
      (shiftedSliceCoordinates a b I J).map Prod.snd := by
  simp only [evaluateLine, shiftedSliceCoordinates, Multiset.map_add, Multiset.map_map,
    Function.comp_def, zero_add, one_mul]

private theorem squarefreeShiftedSlice_coeff (c : SquarefreeClass ι) (a b : ι → ℝ)
    (t : ℝ) (k : ℕ) (hk : k ≤ Fintype.card ι) :
    (squarefreeShiftedSlice c a b t).coeff (Fintype.card ι - k) =
      ∑ I : Finset ι, ∑ J : Finset ι, if Iᶜ.card = J.card then
        ((c I J).re / (2 : ℝ)^Fintype.card ι) *
          (evaluateLine (shiftedSliceCoordinates a b I J) t).esymm k else 0 := by
  simp only [squarefreeShiftedSlice, Polynomial.finset_sum_coeff]
  apply Finset.sum_congr rfl
  intro I _
  apply Finset.sum_congr rfl
  intro J _
  by_cases hIJ : Iᶜ.card = J.card
  · simp only [hIJ, if_true, Polynomial.coeff_C_mul]
    let s := evaluateLine (shiftedSliceCoordinates a b I J) t
    have hs : s.card = Fintype.card ι := by
      change (evaluateLine (shiftedSliceCoordinates a b I J) t).card = _
      simp only [evaluateLine, shiftedSliceCoordinates, Multiset.card_map, Multiset.card_add]
      change I.card + J.card = _
      rw [← hIJ, Finset.card_add_card_compl]
    have hp : (∏ i ∈ I, (X + C (a i + t))) * (∏ j ∈ J, (X + C (b j - t))) =
        (s.map fun x => X + C x).prod := by
      simp only [s, evaluateLine, shiftedSliceCoordinates, Multiset.map_add, Multiset.map_map,
        Multiset.prod_add, Function.comp_def, mul_one, mul_neg_one, sub_eq_add_neg,
        Finset.prod_eq_multiset_prod]
    rw [hp, Multiset.prod_X_add_C_coeff s (by rw [hs]; omega), hs,
      show Fintype.card ι - (Fintype.card ι - k) = k by omega]
  · simp only [hIJ, if_false, Polynomial.coeff_zero]

private theorem squarefreeShiftedSlice_first_coeff (c : SquarefreeClass ι) (a b : ι → ℝ)
    (t : ℝ) (hn : 1 ≤ Fintype.card ι) :
    let k := Fintype.card ι - 1
    (squarefreeShiftedSlice c a b t).coeff k =
      (squarefreeShiftedSlice c a b 0).coeff k +
      t * (squarefreeShiftedSlice c (fun _ => 0) (fun _ => 0) 1).coeff k := by
  dsimp only
  rw [squarefreeShiftedSlice_coeff c a b t 1 hn, squarefreeShiftedSlice_coeff c a b 0 1 hn,
    squarefreeShiftedSlice_coeff c (fun _ => 0) (fun _ => 0) 1 1 hn]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro I _
  apply Finset.sum_congr rfl
  intro J _
  by_cases hIJ : Iᶜ.card = J.card
  · simp only [hIJ, if_true, esymm_one_line (shiftedSliceCoordinates a b I J) t,
      shiftedSliceCoordinates_base, shiftedSliceCoordinates_dir a b I J]
    ring
  · simp only [hIJ, if_false, mul_zero, add_zero]

private theorem squarefreeShiftedSlice_second_coeff (c : SquarefreeClass ι) (a b : ι → ℝ)
    (t : ℝ) (hn : 2 ≤ Fintype.card ι) :
    let k := Fintype.card ι - 2
    let A := (squarefreeShiftedSlice c a b 0).coeff k
    let B := (squarefreeShiftedSlice c a b 1).coeff k
    let D := (squarefreeShiftedSlice c (fun _ => 0) (fun _ => 0) 1).coeff k
    (squarefreeShiftedSlice c a b t).coeff k = A + t * (B - A - D) + t^2 * D := by
  dsimp only
  rw [squarefreeShiftedSlice_coeff c a b t 2 hn, squarefreeShiftedSlice_coeff c a b 0 2 hn,
    squarefreeShiftedSlice_coeff c a b 1 2 hn,
    squarefreeShiftedSlice_coeff c (fun _ => 0) (fun _ => 0) 1 2 hn]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro I _
  apply Finset.sum_congr rfl
  intro J _
  by_cases hIJ : Iᶜ.card = J.card
  · simp only [hIJ, if_true, esymm_two_line (shiftedSliceCoordinates a b I J) t,
      shiftedSliceCoordinates_base, shiftedSliceCoordinates_dir a b I J]
    ring
  · simp only [hIJ, if_false, sub_zero, mul_zero, add_zero]

private def squarefreeOppositeShiftPolynomial (c : SquarefreeClass ι) (a b : ι → ℝ) : ℝ[X] :=
  ∑ I : Finset ι, ∑ J : Finset ι, if Iᶜ.card = J.card then
    C ((c I J).re / (2 : ℝ) ^ Fintype.card ι) *
      ((∏ i ∈ I, C (a i) + X) * ∏ j ∈ J, C (b j) - X) else 0

private theorem squarefreeOppositeShiftPolynomial_eval (c : SquarefreeClass ι) (a b : ι → ℝ)
    (t : ℝ) : (squarefreeOppositeShiftPolynomial c a b).eval t =
      (squarefreeShiftedSlice c a b t).eval 0 := by
  simp only [squarefreeOppositeShiftPolynomial, squarefreeShiftedSlice, eval_finset_sum]
  apply Finset.sum_congr rfl
  intro I _
  apply Finset.sum_congr rfl
  intro J _
  by_cases hIJ : Iᶜ.card = J.card <;> simp only [hIJ, if_true, if_false, eval_zero,
    eval_mul, eval_prod, eval_add, eval_sub, eval_C, eval_X, zero_add]

private theorem squarefreeShiftedSlice_eval_zero_eq {c : SquarefreeClass ι}
    (hc : IsMinimumNormalizedSpectralValue c) (a b : ι → ℝ) (t : ℝ) :
    (squarefreeShiftedSlice c a b t).eval 0 = (squarefreeShiftedSlice c a b 0).eval 0 := by
  let n := Fintype.card ι
  let p (u : ℝ) := squarefreeShiftedSlice c a b u
  have hm (u : ℝ) : (p u).Monic := (squarefreeShiftedSlice_monic_degree hc a b u).1
  have hd (u : ℝ) : (p u).natDegree = n := (squarefreeShiftedSlice_monic_degree hc a b u).2
  have hzero (k : ℕ) (hk : k < n) :
      (squarefreeShiftedSlice c (fun _ => 0) (fun _ => 0) 1).coeff k = 0 := by
    rw [squarefreeShiftedSlice_zero_base hc 1, coeff_X_pow, if_neg hk.ne]
  have hA (hn : 1 ≤ n) (u : ℝ) : (p u).coeff (n - 1) = (p 0).coeff (n - 1) := by
    have h := squarefreeShiftedSlice_first_coeff c a b u hn
    simpa only [hzero (n - 1) (by omega), mul_zero, add_zero] using h
  change (p t).eval 0 = (p 0).eval 0
  by_cases hn : 2 ≤ n
  · let B := (p 0).coeff (n - 2)
    let D := (p 1).coeff (n - 2) - B
    have hB (u : ℝ) : (p u).coeff (n - 2) = B + D * u := by
      have h := squarefreeShiftedSlice_second_coeff c a b u hn
      simpa only [p, B, D, hzero (n - 2) (by omega), sub_zero, mul_zero, add_zero,
        mul_comm u] using h
    let q := squarefreeOppositeShiftPolynomial c a b
    have hq (u : ℝ) : q.eval u = (p u).eval 0 :=
      squarefreeOppositeShiftPolynomial_eval c a b u
    have hconst := polynomial_eq_constant_of_split_affine_coefficients n hn p
      ((p 0).coeff (n - 1)) B D hm hd
      (squarefreeShiftedSlice_splits hc a b) (hA (by omega)) hB q hq
    have he := congrArg (Polynomial.eval t) hconst
    simpa only [eval_C, hq] using he
  · by_cases h₀ : n = 0
    · have he (u : ℝ) : (p u).eval 0 = 1 := by
        have h := (hm u).leadingCoeff
        rwa [Polynomial.leadingCoeff, hd u, h₀, coeff_zero_eq_eval_zero] at h
      rw [he t, he 0]
    · have h₁ : n - 1 = 0 := by omega
      have h := hA (by omega) t
      rwa [h₁, coeff_zero_eq_eval_zero, coeff_zero_eq_eval_zero] at h

/-- Minimum normalization forces opposite translations on real inputs. -/
theorem IsMinimumNormalizedSpectralValue.opposite_translation_real {c : SquarefreeClass ι}
    (hc : IsMinimumNormalizedSpectralValue c) (a b : ι → ℝ) (t : ℝ) :
    squarefreeSpectralValue c (fun i => ((a i : ℝ) : ℂ) + (t : ℂ))
      (fun i => ((b i : ℝ) : ℂ) - (t : ℂ)) =
      squarefreeSpectralValue c (fun i => (a i : ℂ)) (fun i => (b i : ℂ)) := by
  have h := congrArg Complex.ofReal (squarefreeShiftedSlice_eval_zero_eq hc a b t)
  rw [squarefreeShiftedSlice_eval hc a b t 0, squarefreeShiftedSlice_eval hc a b 0 0] at h
  simp only [Complex.ofReal_zero, Complex.ofReal_add, Complex.ofReal_sub, add_zero, sub_zero] at h
  exact (div_left_inj' (pow_ne_zero _ (by norm_num : (2 : ℂ) ≠ 0))).mp h

private abbrev ShiftVariable (ι : Type*) := (ι ⊕ ι) ⊕ Unit

private def spectralShiftPoly (c : SquarefreeClass ι) (k : ℝ) :
    MvPolynomial (ShiftVariable ι) ℝ :=
  let T := MvPolynomial.X (Sum.inr ())
  ∑ I : Finset ι, ∑ J : Finset ι, if Iᶜ.card = J.card then
    MvPolynomial.C (c I J).re *
      ((∏ i ∈ I, MvPolynomial.X (Sum.inl (Sum.inl i)) + MvPolynomial.C k * T) *
        ∏ j ∈ J, MvPolynomial.X (Sum.inl (Sum.inr j)) - MvPolynomial.C k * T)
    else 0

private theorem spectralShiftPoly_homogeneous (c : SquarefreeClass ι) (k : ℝ) :
    (spectralShiftPoly c k).IsHomogeneous (Fintype.card ι) := by
  dsimp only [spectralShiftPoly]
  apply MvPolynomial.IsHomogeneous.sum
  intro I _
  apply MvPolynomial.IsHomogeneous.sum
  intro J _
  by_cases hIJ : Iᶜ.card = J.card
  · rw [if_pos hIJ]
    let T : MvPolynomial (ShiftVariable ι) ℝ := MvPolynomial.X (Sum.inr ())
    let L (i : ι) := MvPolynomial.X (Sum.inl (Sum.inl i)) + MvPolynomial.C k * T
    let R (j : ι) := MvPolynomial.X (Sum.inl (Sum.inr j)) - MvPolynomial.C k * T
    have hT : T.IsHomogeneous 1 := MvPolynomial.isHomogeneous_X _ _
    have hL (i : ι) : (L i).IsHomogeneous 1 :=
      (MvPolynomial.isHomogeneous_X _ _).add (hT.C_mul k)
    have hR (j : ι) : (R j).IsHomogeneous 1 :=
      (MvPolynomial.isHomogeneous_X _ _).sub (hT.C_mul k)
    have hpL : (∏ i ∈ I, L i).IsHomogeneous I.card := by
      simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using
        MvPolynomial.IsHomogeneous.prod I L (fun _ => 1) (fun i _ => hL i)
    have hpR : (∏ j ∈ J, R j).IsHomogeneous J.card := by
      simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using
        MvPolynomial.IsHomogeneous.prod J R (fun _ => 1) (fun j _ => hR j)
    have hn : I.card + J.card = Fintype.card ι := by
      rw [← hIJ, Finset.card_add_card_compl]
    rw [← hn]
    exact (hpL.mul hpR).C_mul _
  · rw [if_neg hIJ]
    exact MvPolynomial.isHomogeneous_zero _ _

private theorem spectralShiftPoly_eval {c : SquarefreeClass ι}
    (hc : IsMinimumNormalizedSpectralValue c) (k : ℝ) (z : ShiftVariable ι → ℂ) :
    MvPolynomial.eval₂Hom Complex.ofRealHom z (spectralShiftPoly c k) =
      squarefreeSpectralValue c
        (fun i => z (Sum.inl (Sum.inl i)) + (k : ℂ) * z (Sum.inr ()))
        (fun j => z (Sum.inl (Sum.inr j)) - (k : ℂ) * z (Sum.inr ())) := by
  simp only [spectralShiftPoly, squarefreeSpectralValue, map_sum]
  apply Finset.sum_congr rfl
  intro I _
  apply Finset.sum_congr rfl
  intro J _
  by_cases hIJ : Iᶜ.card = J.card
  · have hreal : ((c I J).re : ℂ) = c I J := by
      apply Complex.ext
      · exact Complex.ofReal_re _
      · rw [Complex.ofReal_im, (hc.nonnegative I J hIJ).1]
    simp only [hIJ, if_true, squarefreeDividedDivisor, map_mul, map_prod, map_add, map_sub,
      MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_C, Complex.ofRealHom_eq_coe, hreal]
  · simp only [hIJ, if_false, map_zero, squarefreeDividedDivisor, mul_zero]

/-- Opposite translation holds on complex inputs for every
minimum-normalized stable spectral value. -/
theorem IsMinimumNormalizedSpectralValue.opposite_translation {c : SquarefreeClass ι}
    (hc : IsMinimumNormalizedSpectralValue c) (a b : ι → ℂ) (t : ℂ) :
    squarefreeSpectralValue c (fun i => a i + t) (fun i => b i - t) =
      squarefreeSpectralValue c a b := by
  have hpoly : spectralShiftPoly c 1 = spectralShiftPoly c 0 := by
    apply (spectralShiftPoly_homogeneous c 1).funext (spectralShiftPoly_homogeneous c 0)
    intro z
    apply Complex.ofReal_injective
    have hmap (k : ℝ) :
        (MvPolynomial.eval z (spectralShiftPoly c k) : ℂ) =
          MvPolynomial.eval₂Hom Complex.ofRealHom (fun i => (z i : ℂ)) (spectralShiftPoly c k) := by
      simpa only [MvPolynomial.eval, RingHom.comp_id, Complex.ofRealHom_eq_coe] using
        MvPolynomial.map_eval₂Hom (RingHom.id ℝ) z Complex.ofRealHom (spectralShiftPoly c k)
    rw [hmap 1, hmap 0, spectralShiftPoly_eval hc 1, spectralShiftPoly_eval hc 0]
    simpa only [Complex.ofReal_one, Complex.ofReal_zero, one_mul, zero_mul, add_zero, sub_zero] using
      hc.opposite_translation_real (fun i => z (Sum.inl (Sum.inl i)))
        (fun j => z (Sum.inl (Sum.inr j))) (z (Sum.inr ()))
  let z : ShiftVariable ι → ℂ := Sum.elim (Sum.elim a b) (fun _ => t)
  have he := congrArg (MvPolynomial.eval₂Hom Complex.ofRealHom z) hpoly
  rw [spectralShiftPoly_eval hc 1, spectralShiftPoly_eval hc 0] at he
  simpa only [z, Sum.elim_inl, Sum.elim_inr, Complex.ofReal_one, Complex.ofReal_zero,
    one_mul, zero_mul, add_zero, sub_zero] using he

/-- The two marginal evaluations are products of the corresponding
linear factors. -/
theorem IsMinimumNormalizedSpectralValue.marginals {c : SquarefreeClass ι}
    (hc : IsMinimumNormalizedSpectralValue c) (a b : ι → ℂ) :
    squarefreeSpectralValue c a (fun _ => 1) = (∏ i, (a i + 1)) ∧
      squarefreeSpectralValue c (fun _ => 1) b = ∏ j, (b j + 1) :=
  squarefreeSpectralValue_marginals_of_opposite_translation c hc.leftEndpoint
    hc.rightEndpoint hc.opposite_translation a b

/-- The balanced coefficients equal their complementary coefficients,
and their real values lie in the closed unit interval. -/
theorem IsMinimumNormalizedSpectralValue.coefficient_of_balanced_pair {c : SquarefreeClass ι}
    (hc : IsMinimumNormalizedSpectralValue c) (I J : Finset ι) (hIJ : Iᶜ.card = J.card) :
    c I J = c Iᶜ Jᶜ ∧ (c I J).re ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨squarefreeSpectralValue_complement_of_opposite_translation c hc.opposite_translation I J hIJ,
    (hc.nonnegative I J hIJ).2,
    squarefreeSpectralValue_coefficient_le_one c hc.leftEndpoint hc.rightEndpoint
      hc.opposite_translation (fun K L h => (hc.nonnegative K L h).2) I J hIJ⟩

end

end MOC
