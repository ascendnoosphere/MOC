import MOC.Reformulations.ZeroPaddingElementaryCoefficient
import MOC.Support
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-! A strict fourth-coefficient separation in order five. The certificate
uses Gaussian integers and checks all partial matchings for zero padding. -/

open BigOperators Matrix Polynomial
open scoped Finset

namespace MOC.Reformulations.CStar

private def affineCoefficient {n : ℕ} {R : Type*} [CommRing R]
    (u v : Fin n → R) (k : ℕ) : R :=
  ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
    (∏ j ∈ S, v j) * ∏ j ∈ Sᶜ, u j

private theorem coeff_prod_affine {n : ℕ} {R : Type*} [CommRing R]
    (u v : Fin n → R) (k : ℕ) :
    (∏ j, (C (v j) * X + C (u j))).coeff k = affineCoefficient u v k := by
  rw [Fintype.prod_add, Polynomial.finset_sum_coeff, affineCoefficient,
    Finset.powersetCard_eq_filter, Finset.powerset_univ, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro S _
  rw [Finset.prod_mul_distrib, Finset.prod_const, ← map_prod C, ← map_prod C,
    mul_right_comm _ (X ^ S.card), ← map_mul, Polynomial.coeff_C_mul_X_pow]
  by_cases h : S.card = k
  · simp [h]
  · simp only [h, Ne.symm h, if_false]

private def detCoefficient {n : ℕ} {R : Type*} [CommRing R]
    (M : Matrix (Fin n) (Fin n) R) (k : ℕ) : R :=
  ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : R) *
    affineCoefficient (fun j => if σ j = j then 1 else 0) (fun j => M (σ j) j) k

private theorem elementaryCoefficient_eq_detCoefficient {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) :
    elementaryCoefficient M k = detCoefficient M k := by
  have he : (1 - (X : ℂ[X]) • (-M).map C) =
      Matrix.of fun i j => C (M i j) * X + C (if i = j then 1 else 0) := by
    apply Matrix.ext
    intro i j
    by_cases h : i = j
    · subst j
      simp only [Matrix.one_apply_eq, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply,
        Matrix.neg_apply, smul_eq_mul, Matrix.of_apply, if_pos rfl, if_true, map_neg, mul_neg,
        neg_mul, sub_neg_eq_add, map_one, mul_comm X]
      exact add_comm _ _
    · simp only [Matrix.one_apply_ne h, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply,
        Matrix.neg_apply, smul_eq_mul, Matrix.of_apply, if_neg h, map_neg, mul_neg,
        neg_mul, sub_neg_eq_add, map_zero, zero_mul, zero_add, add_zero, mul_comm X]
  rw [elementaryCoefficient, Matrix.charpolyRev, he, Matrix.det_apply',
    Polynomial.finset_sum_coeff, detCoefficient]
  apply Finset.sum_congr rfl
  intro σ _
  rw [← map_intCast (C : ℂ →+* ℂ[X]), Polynomial.coeff_C_mul]
  exact congrArg (fun z : ℂ => ((Equiv.Perm.sign σ : ℤ) : ℂ) * z)
    (coeff_prod_affine (fun j => if σ j = j then 1 else 0) (fun j => M (σ j) j) k)

private theorem affineCoefficient_map {n : ℕ} {R S : Type*} [CommRing R] [CommRing S]
    (g : R →+* S) (u v : Fin n → R) (k : ℕ) :
    g (affineCoefficient u v k) = affineCoefficient (g ∘ u) (g ∘ v) k := by
  simp only [affineCoefficient, map_sum, map_mul, map_prod, Function.comp_apply]

private theorem detCoefficient_map {n : ℕ} {R S : Type*} [CommRing R] [CommRing S]
    (g : R →+* S) (M : Matrix (Fin n) (Fin n) R) (k : ℕ) :
    g (detCoefficient M k) = detCoefficient (M.map g) k := by
  simp only [detCoefficient, affineCoefficient_map, map_sum, map_mul, map_intCast,
    Matrix.map_apply]
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  congr 1
  ext j
  by_cases h : σ j = j <;> simp [h]

private theorem affineCoefficient_smul {n : ℕ} {R : Type*} [CommRing R]
    (u v : Fin n → R) (d : R) (k : ℕ) :
    affineCoefficient u (fun j => d * v j) k = d ^ k * affineCoefficient u v k := by
  rw [affineCoefficient, affineCoefficient, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  rw [Finset.prod_mul_distrib, Finset.prod_const, (Finset.mem_powersetCard.mp hS).2, mul_assoc]

private theorem detCoefficient_smul {n : ℕ} {R : Type*} [CommRing R]
    (M : Matrix (Fin n) (Fin n) R) (d : R) (k : ℕ) :
    detCoefficient (d • M) k = d ^ k * detCoefficient M k := by
  simp only [detCoefficient, Matrix.smul_apply, smul_eq_mul, affineCoefficient_smul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  ring

private def first : Fin 5 → GaussianInt :=
  ![⟨33, 22⟩, 0, ⟨-11, 8⟩, ⟨60, 17⟩, ⟨-14, -68⟩]

private def second : Fin 5 → GaussianInt :=
  ![⟨-3, 20⟩, ⟨-70, 10⟩, ⟨-60, -47⟩, ⟨16, 20⟩, ⟨16, 20⟩]

private def mixer : Matrix (Fin 5) (Fin 5) GaussianInt :=
  !![1, 4, 4, 4, 0; -4, 1, 4, -4, 0; -4, -4, 1, 4, 0;
    -4, 4, -4, 1, 0; 0, 0, 0, 0, 7]

private def numerator : Matrix (Fin 5) (Fin 5) GaussianInt :=
  (49 : GaussianInt) • diagonal first + mixer * diagonal second * mixerᴴ

private def rowLabels : List (Fin 5) := List.ofFn id

private def partialMatches : ℕ → List (Fin 5) → List (List (Option (Fin 5)))
  | 0, _ => [[]]
  | k + 1, available =>
      (partialMatches k available).map (none :: ·) ++
        available.flatMap fun i => (partialMatches k (available.erase i)).map (some i :: ·)

private theorem mem_partialMatches (xs : List (Option (Fin 5))) {available : List (Fin 5)}
    (hm : ∀ i : Fin 5, some i ∈ xs → i ∈ available)
    (hp : xs.Pairwise fun x y => x = none ∨ x ≠ y) :
    xs ∈ partialMatches xs.length available := by
  induction xs generalizing available with
  | nil => simp [partialMatches]
  | cons x xs ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hp
    cases x with
    | none =>
      simp only [List.length_cons, partialMatches, List.mem_append]
      exact Or.inl (List.mem_map.mpr
        ⟨xs, ih (fun i hi => hm i (List.mem_cons_of_mem _ hi)) htail, rfl⟩)
    | some i =>
      have hi : i ∈ available := hm i List.mem_cons_self
      have htail_mem (j : Fin 5) (hj : some j ∈ xs) : j ∈ available.erase i := by
        have hne : j ≠ i := by
          intro hji
          rw [hji] at hj
          simpa using hhead (some i) hj
        exact (List.mem_erase_of_ne hne).mpr (hm j (List.mem_cons_of_mem _ hj))
      simp only [List.length_cons, partialMatches, List.mem_append]
      exact Or.inr (List.mem_flatMap.mpr
        ⟨i, hi, List.mem_map.mpr ⟨xs, ih htail_mem htail, rfl⟩⟩)

private def partialMatchValues (xs : List (Option (Fin 5))) : List GaussianInt :=
  (List.ofFn fun j : Fin 5 => (xs[j.val]?.getD none).elim 0 first + second j) ++
    List.ofFn fun i : Fin 5 => if some i ∈ xs then 0 else first i

private def firstFourCoefficients : List GaussianInt →
    GaussianInt × GaussianInt × GaussianInt × GaussianInt
  | [] => (0, 0, 0, 0)
  | x :: xs =>
    let c := firstFourCoefficients xs
    (c.1 + x, c.2.1 + x * c.1, c.2.2.1 + x * c.2.1, c.2.2.2 + x * c.2.2.1)

private theorem coeff_affine_succ (x : GaussianInt) (p : GaussianInt[X]) (k : ℕ) :
    ((1 + C x * X) * p).coeff (k + 1) = p.coeff (k + 1) + x * p.coeff k := by
  rw [add_mul, one_mul, mul_assoc, Polynomial.coeff_add, Polynomial.coeff_C_mul,
    mul_comm Polynomial.X p, Polynomial.coeff_mul_X]

private theorem firstFourCoefficients_correct (xs : List GaussianInt) :
    let p := (xs.map fun x => 1 + C x * X).prod
    let c := firstFourCoefficients xs
    p.coeff 0 = 1 ∧ p.coeff 1 = c.1 ∧ p.coeff 2 = c.2.1 ∧
      p.coeff 3 = c.2.2.1 ∧ p.coeff 4 = c.2.2.2 := by
  induction xs with
  | nil => simp [firstFourCoefficients, Polynomial.coeff_one]
  | cons x xs ih =>
    dsimp only [List.map_cons, List.prod_cons] at ih ⊢
    obtain ⟨h₀, h₁, h₂, h₃, h₄⟩ := ih
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_mul]
      simp only [Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_mul,
        Polynomial.eval_X, mul_zero, add_zero, one_mul, ← Polynomial.coeff_zero_eq_eval_zero]
      exact h₀
    · rw [coeff_affine_succ x _ 0, h₀, h₁, mul_one] <;> rfl
    · rw [coeff_affine_succ x _ 1, h₁, h₂] <;> rfl
    · rw [coeff_affine_succ x _ 2, h₂, h₃] <;> rfl
    · rw [coeff_affine_succ x _ 3, h₃, h₄] <;> rfl

private def partialMatchScore (xs : List (Option (Fin 5))) : ℤ :=
  (firstFourCoefficients (partialMatchValues xs)).2.2.2.re

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem partialMatch_none_table :
    ((partialMatches 4 rowLabels).map (none :: ·)).all
      (fun xs => decide (partialMatchScore xs ≤ 1604790)) =
        true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem partialMatch_some_table (i : Fin 5) :
    ((partialMatches 4 (rowLabels.erase i)).map (some i :: ·)).all
      (fun xs => decide (partialMatchScore xs ≤ 1604790)) =
        true := by
  fin_cases i <;> decide +kernel

private theorem partialMatchScore_le (xs : List (Option (Fin 5)))
    (hx : xs ∈ partialMatches 5 rowLabels) :
    partialMatchScore xs ≤ 1604790 := by
  change xs ∈ (partialMatches 4 rowLabels).map (none :: ·) ++
    rowLabels.flatMap (fun i => (partialMatches 4 (rowLabels.erase i)).map (some i :: ·)) at hx
  rcases List.mem_append.mp hx with h | h
  · exact of_decide_eq_true (List.all_eq_true.mp partialMatch_none_table xs h)
  · obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp h
    exact of_decide_eq_true (List.all_eq_true.mp (partialMatch_some_table i) xs hi)

private theorem partialMatchValues_ofFn (d : Fin 5 → Option (Fin 5)) :
    partialMatchValues (List.ofFn d) =
      (List.ofFn fun j => (d j).elim 0 first + second j) ++
        List.ofFn fun i => if ∀ j, d j ≠ some i then first i else 0 := by
  unfold partialMatchValues
  congr 1
  apply congrArg List.ofFn
  funext i
  by_cases h : ∃ j, d j = some i
  · obtain ⟨j, hj⟩ := h
    have hn : ¬∀ j, d j ≠ some i := fun nh => nh j hj
    have hmem : some i ∈ List.ofFn d := List.mem_ofFn.mpr ⟨j, hj⟩
    simp only [if_neg hn, if_pos hmem]
  · have hn : ∀ j, d j ≠ some i := fun j hj => h ⟨j, hj⟩
    have hmem : some i ∉ List.ofFn d := fun hh => h (List.mem_ofFn.mp hh)
    simp only [if_pos hn, if_neg hmem]

private theorem mixerGram : mixerᴴ * mixer = (49 : GaussianInt) • 1 := by
  have h : ∀ i j : Fin 5, (mixerᴴ * mixer) i j =
      ((49 : GaussianInt) • (1 : Matrix (Fin 5) (Fin 5) GaussianInt)) i j := by
    decide +kernel
  exact Matrix.ext h

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem numerator_score :
    (detCoefficient numerator 4).re = 9341473392272 := by
  decide +kernel

noncomputable section

private def a : Fin 5 → ℂ := GaussianInt.toComplex ∘ first
private def b : Fin 5 → ℂ := GaussianInt.toComplex ∘ second
private def W : Matrix (Fin 5) (Fin 5) ℂ := mixer.map GaussianInt.toComplex
private def U : Matrix (Fin 5) (Fin 5) ℂ := (7 : ℂ)⁻¹ • W

private theorem partial_matching_score_bound (d : Fin 5 → Option (Fin 5))
    (hd : ∀ j l i, d j = some i → d l = some i → j = l) :
    (((∏ j, (1 + Polynomial.C ((d j).elim 0 a + b j) * Polynomial.X)) *
      ∏ i ∈ (Finset.univ.filter fun i => ∀ j, d j ≠ some i),
        (1 + Polynomial.C (a i) * Polynomial.X)).coeff 4).re ≤
        (1604790 : ℝ) := by
  let xs := List.ofFn d
  have hp : xs.Pairwise fun x y => x = none ∨ x ≠ y := by
    change (List.ofFn d).Pairwise _
    rw [List.pairwise_ofFn]
    intro j l hjl
    have hcases (x : Option (Fin 5)) : x = none ∨ ∃ i, x = some i := by
      cases x <;> simp
    rcases hcases (d j) with hj | ⟨i, hi⟩
    · exact Or.inl hj
    · exact Or.inr fun he => (ne_of_lt hjl) (hd j l i hi (he.symm.trans hi))
  have hm (i : Fin 5) (_hi : some i ∈ xs) : i ∈ rowLabels :=
    List.mem_ofFn.mpr ⟨i, rfl⟩
  have hx := mem_partialMatches xs hm hp
  change xs ∈ partialMatches (List.ofFn d).length rowLabels at hx
  rw [List.length_ofFn] at hx
  have hb := partialMatchScore_le xs hx
  let g := GaussianInt.toComplex
  let q : GaussianInt[X] := ((partialMatchValues xs).map fun x => 1 + C x * X).prod
  have he : q.coeff 4 = (firstFourCoefficients (partialMatchValues xs)).2.2.2 :=
    (firstFourCoefficients_correct (partialMatchValues xs)).2.2.2.2
  have hq : q.map g =
      (∏ j, (1 + Polynomial.C ((d j).elim 0 a + b j) * Polynomial.X)) *
        ∏ i ∈ (Finset.univ.filter fun i => ∀ j, d j ≠ some i),
          (1 + Polynomial.C (a i) * Polynomial.X) := by
    have hvalues := partialMatchValues_ofFn d
    simp only [q, xs, hvalues, List.map_append, List.prod_append, List.map_ofFn,
      List.prod_ofFn, Function.comp_apply, Polynomial.map_mul, Polynomial.map_prod,
      Polynomial.map_add, Polynomial.map_one, Polynomial.map_C, Polynomial.map_X]
    congr 1
    · apply Finset.prod_congr rfl
      intro j _
      cases h : d j <;> simp [h, g, a, b]
    · rw [Finset.prod_filter]
      apply Finset.prod_congr rfl
      intro i _
      by_cases h : ∀ j, d j ≠ some i <;> simp [h, g, a]
  rw [← hq, Polynomial.coeff_map, he, ← GaussianInt.to_real_re]
  exact_mod_cast hb

private theorem WGram : Wᴴ * W = (49 : ℂ) • 1 := by
  let g := GaussianInt.toComplex
  have h := congrArg (fun M : Matrix (Fin 5) (Fin 5) GaussianInt => M.map g) mixerGram
  have hstar := Matrix.conjTranspose_map (A := mixer) g GaussianInt.toComplex_star
  simpa only [W, g, Matrix.map_mul, hstar,
    Matrix.map_smul' g _ _ (map_mul g), map_ofNat, Matrix.map_one g (map_zero g) (map_one g)]
    using h

private theorem unitary_U : IsUnitary U := by
  have hr : star ((7 : ℂ)⁻¹) = (7 : ℂ)⁻¹ := by norm_num [Complex.star_def]
  have h : Uᴴ * U = 1 := by
    rw [U, Matrix.conjTranspose_smul, hr, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      WGram, smul_smul]
    norm_num
  exact ⟨Matrix.mul_eq_one_comm.mp h, h⟩

private theorem numerator_map : numerator.map GaussianInt.toComplex =
    (49 : ℂ) • (diagonal a + U * diagonal b * Uᴴ) := by
  let g := GaussianInt.toComplex
  change numerator.map g = _
  have hU : W = (7 : ℂ) • U := by rw [U, smul_smul]; norm_num
  have hr : star (7 : ℂ) = 7 := by norm_num [Complex.star_def]
  have hstar := Matrix.conjTranspose_map (A := mixer) g GaussianInt.toComplex_star
  simp only [numerator, Matrix.map_add g (map_add g), Matrix.map_mul,
    Matrix.diagonal_map (map_zero g), hstar,
    Matrix.map_smul' g _ _ (map_mul g), map_ofNat]
  change (49 : ℂ) • diagonal a + W * diagonal b * Wᴴ = _
  rw [hU, Matrix.conjTranspose_smul, hr, smul_add]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  norm_num

private theorem actual_score_gt :
    (1604790 : ℝ) <
      (elementaryCoefficient (diagonal a + U * diagonal b * Uᴴ) 4).re := by
  let g := GaussianInt.toComplex
  let z := elementaryCoefficient (diagonal a + U * diagonal b * Uᴴ) 4
  have he : g (detCoefficient numerator 4) = (49 : ℂ)^4 * z := by
    rw [detCoefficient_map, numerator_map, detCoefficient_smul,
      ← elementaryCoefficient_eq_detCoefficient]
  have hc : (g (detCoefficient numerator 4)).re = (9341473392272 : ℝ) := by
    rw [← GaussianInt.to_real_re, numerator_score] <;> norm_num
  have hr : (49 : ℂ)^4 = (((49 : ℝ)^4 : ℝ) : ℂ) := by
    rw [Complex.ofReal_pow] <;> norm_num
  rw [he, hr, Complex.re_ofReal_mul] at hc
  change _ < z.re
  apply lt_of_not_ge
  intro hle
  have hscaled := mul_le_mul_of_nonneg_left hle (by norm_num : 0 ≤ (49 : ℝ)^4)
  rw [hc] at hscaled
  norm_num at hscaled

/-- In every order at least five, the fourth elementary coefficient of a sum
of two normal matrices can lie outside the matching hull for that coefficient. -/
theorem exists_fourthElementaryCoefficient_outside_hull_of_five_le {n : ℕ} (hn : 5 ≤ n) :
    ∃ (a b : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ), IsUnitary U ∧
      elementaryCoefficient (diagonal a + U * diagonal b * Uᴴ) 4 ∉
        convexHull ℝ (Set.range fun σ : Equiv.Perm (Fin n) =>
          elementaryCoefficient (diagonal fun j => a (σ j) + b j) 4) :=
  fourthElementaryCoefficient_not_mem_after_zero_padding a b U unitary_U 1 1604790
    (by simpa only [one_mul] using actual_score_gt)
    (fun d hd => by simpa only [one_mul] using partial_matching_score_bound d hd) hn

theorem not_separateCoefficientForm : ¬ SeparateCoefficientForm := by
  intro h
  obtain ⟨a, b, U, hU, hbad⟩ := exists_fourthElementaryCoefficient_outside_hull_of_five_le le_rfl
  exact hbad (h 5 a b U hU 4 (by decide) (by decide))

theorem not_simultaneousCharacteristicForm : ¬ SimultaneousCharacteristicForm :=
  fun h => not_separateCoefficientForm (separateCoefficientForm_of_simultaneous h)

end

end MOC.Reformulations.CStar
