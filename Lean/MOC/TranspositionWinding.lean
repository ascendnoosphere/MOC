import MOC.StrongSupport
import MOC.Weights
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Topology.SeparatedMap
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.UniformSpace.HeineCantor

/-! Transposition walks and integer edge cycles for the determinant range. -/

open BigOperators Matrix
open scoped Topology unitInterval

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private abbrev Perm (ι : Type*) := Equiv.Perm ι

/-- An edge of the abstract matching graph. Left multiplication swaps two
labels in the first spectrum. -/
def TranspositionEdge (p q : Equiv.Perm ι) : Prop :=
  ∃ i j, i ≠ j ∧ q = Equiv.swap i j * p

private theorem mul_swap_eq_swap_mul (g : Perm ι) (i j : ι) :
    g * Equiv.swap i j = Equiv.swap (g i) (g j) * g := by
  ext k
  change g (Equiv.swap i j k) = Equiv.swap (g i) (g j) (g k)
  by_cases hi : k = i
  · subst k
    rw [Equiv.swap_apply_left, Equiv.swap_apply_left]
  · by_cases hj : k = j
    · subst k
      rw [Equiv.swap_apply_right, Equiv.swap_apply_right]
    · rw [Equiv.swap_apply_of_ne_of_ne hi hj,
        Equiv.swap_apply_of_ne_of_ne (fun h => hi (g.injective h))
          (fun h => hj (g.injective h))]

private theorem transpositionEdge_translate (g : Perm ι) {p q : Perm ι}
    (h : TranspositionEdge p q) : TranspositionEdge (g * p) (g * q) := by
  obtain ⟨i, j, hij, rfl⟩ := h
  exact ⟨g i, g j, fun h => hij (g.injective h),
    by rw [← mul_assoc, mul_swap_eq_swap_mul, mul_assoc]⟩

private theorem swap_mul_swap_self (i j : ι) :
    Equiv.swap i j * Equiv.swap i j = (1 : Perm ι) := by
  ext k
  change Equiv.swap i j (Equiv.swap i j k) = k
  exact Equiv.swap_apply_self i j k

private theorem telescope_sum (f : ℕ → ℝ) (m : ℕ) :
    (∑ k ∈ Finset.range m, (f (k + 1) - f k)) = f m - f 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    ring

/-- If reversal negates the edge values and each translated square has
zero sum, the edge values are differences of a function on vertices. -/
theorem exists_transposition_potential_of_squares
    (d : Equiv.Perm ι → Equiv.Perm ι → ℝ)
    (hreverse : ∀ p q, TranspositionEdge p q → d q p = -d p q)
    (hsquare : ∀ i j, i ≠ j → ∀ p q, TranspositionEdge p q →
      let s := Equiv.swap i j
      d (s * p) (s * q) - d p q = d q (s * q) - d p (s * p)) :
    ∃ v : Equiv.Perm ι → ℝ, ∀ p q, TranspositionEdge p q → d p q = v q - v p := by
  classical
  have hex (g : Perm ι) : ∃ v : Perm ι → ℝ, ∀ p q, TranspositionEdge p q →
      d (g * p) (g * q) - d p q = v q - v p := by
    induction g using Equiv.Perm.swap_induction_on with
    | one => exact ⟨fun _ => 0, by simp⟩
    | swap_mul g i j hij ih =>
      let s := Equiv.swap i j
      obtain ⟨v, hv⟩ := ih
      refine ⟨fun p => v p + d (g * p) (s * (g * p)), ?_⟩
      intro p q hpq
      have he : d (s * (g * p)) (s * (g * q)) - d (g * p) (g * q) =
          d (g * q) (s * (g * q)) - d (g * p) (s * (g * p)) :=
        hsquare i j hij (g * p) (g * q) (transpositionEdge_translate g hpq)
      change d ((s * g) * p) ((s * g) * q) - d p q =
        v q + d (g * q) (s * (g * q)) - (v p + d (g * p) (s * (g * p)))
      simp only [mul_assoc]
      linarith only [he, hv p q hpq]
  choose v hv using hex
  let N : ℝ := Fintype.card (Perm ι)
  have hN : N ≠ 0 := by
    change (Fintype.card (Perm ι) : ℝ) ≠ 0
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Perm ι) ≠ 0)
  refine ⟨fun p => -(∑ g, v g p) / N, ?_⟩
  intro p q hpq
  have hsum : (∑ g : Perm ι, d (g * p) (g * q)) = 0 := by
    obtain ⟨i, j, hij, hstep⟩ := hpq
    let s := Equiv.swap i j
    let f (g : Perm ι) := d (g * p) (g * q)
    have hsq : s * q = p := by
      rw [hstep, ← mul_assoc, swap_mul_swap_self, one_mul]
    have hf (g : Perm ι) : f (g * s) = -f g := by
      change d ((g * s) * p) ((g * s) * q) = -d (g * p) (g * q)
      simp only [mul_assoc, hsq, show s * p = q from hstep.symm]
      exact hreverse _ _ (transpositionEdge_translate g ⟨i, j, hij, hstep⟩)
    have he : (∑ g, f (g * s)) = ∑ g, f g := Equiv.sum_comp (Equiv.mulRight s) f
    simp only [hf, Finset.sum_neg_distrib] at he
    change (∑ g, f g) = 0
    linarith only [he]
  have hdiff : (∑ g : Perm ι, (d (g * p) (g * q) - d p q)) = ∑ g, (v g q - v g p) :=
    Finset.sum_congr rfl fun g _ => hv g p q hpq
  simp only [Finset.sum_sub_distrib, hsum, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, zero_sub] at hdiff
  rw [← sub_div]
  apply (eq_div_iff hN).mpr
  change -(N * d p q) = (∑ g, v g q) - ∑ g, v g p at hdiff
  linarith only [hdiff]

/-- Edge values with the square and reversal properties sum to zero on
each closed transposition walk. -/
theorem transposition_walk_sum_eq_zero_of_squares
    (d : Equiv.Perm ι → Equiv.Perm ι → ℝ)
    (hreverse : ∀ p q, TranspositionEdge p q → d q p = -d p q)
    (hsquare : ∀ i j, i ≠ j → ∀ p q, TranspositionEdge p q →
      let s := Equiv.swap i j
      d (s * p) (s * q) - d p q = d q (s * q) - d p (s * p))
    (m : ℕ) (p : ℕ → Equiv.Perm ι) (hclosed : p m = p 0)
    (hwalk : ∀ k < m, TranspositionEdge (p k) (p (k + 1))) :
    (∑ k ∈ Finset.range m, d (p k) (p (k + 1))) = 0 := by
  obtain ⟨v, hv⟩ := exists_transposition_potential_of_squares d hreverse hsquare
  calc
    _ = ∑ k ∈ Finset.range m, (v (p (k + 1)) - v (p k)) :=
      Finset.sum_congr rfl fun k hk => hv _ _ (hwalk k (Finset.mem_range.mp hk))
    _ = 0 := by
      rw [telescope_sum (v ∘ p)]
      simp only [Function.comp_apply, hclosed, sub_self]

private theorem swapMatrix_apply (i j k l : ι) :
    (Equiv.swap i j).permMatrix ℂ k l = if k = Equiv.swap i j l then 1 else 0 := by
  have he : l = Equiv.swap i j k ↔ k = Equiv.swap i j l := by
    constructor <;> intro h <;>
      simpa [h, Equiv.swap_apply_self]
  have he' : Equiv.swap i j k = l ↔ k = Equiv.swap i j l := eq_comm.trans he
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_some, he']

/-- A unitary interpolation from the identity to a transposition matrix
times the scalar `Complex.I`. The scalar cancels in conjugation. -/
def swapRotation (i j : ι) (t : I) : Matrix ι ι ℂ :=
  (↑(Real.sqrt (1 - (t : ℝ))) : ℂ) • (1 : Matrix ι ι ℂ) +
    ((↑(Real.sqrt (t : ℝ)) : ℂ) * Complex.I) • (Equiv.swap i j).permMatrix ℂ

theorem swapRotation_unitary (i j : ι) (t : I) : IsUnitary (swapRotation i j t) := by
  let c : ℂ := Real.sqrt (1 - (t : ℝ))
  let d : ℂ := (↑(Real.sqrt (t : ℝ)) : ℂ) * Complex.I
  let P : Matrix ι ι ℂ := (Equiv.swap i j).permMatrix ℂ
  have hP : IsUnitary P := isUnitary_permMatrix (Equiv.swap i j)
  have hinv : (Equiv.swap i j : Perm ι)⁻¹ = Equiv.swap i j := by
    apply inv_eq_of_mul_eq_one_right
    exact swap_mul_swap_self i j
  have hPstar : Pᴴ = P := by
    dsimp only [P]
    rw [Matrix.conjTranspose_permMatrix, hinv]
  have hPP : P * P = 1 := by simpa only [hPstar] using hP.1
  have hcD : star c = c := Complex.conj_ofReal _
  have hdD : star d = -d := by simp [d, Complex.star_def]
  have hconj : (c • (1 : Matrix ι ι ℂ) + d • P)ᴴ =
      c • (1 : Matrix ι ι ℂ) + (-d) • P := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one, hcD, hdD, hPstar]
  have hc : c ^ 2 = (1 - (t : ℝ) : ℝ) := by
    change ((↑(Real.sqrt (1 - (t : ℝ))) : ℂ)) ^ 2 = _
    exact_mod_cast Real.sq_sqrt (sub_nonneg.mpr t.property.2)
  have hd : d ^ 2 = -(↑(t : ℝ) : ℂ) := by
    dsimp [d]
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt t.property.1, mul_neg_one]
  have h₁ : c * c + d * (-d) = 1 := by
    rw [mul_neg, ← pow_two, ← pow_two, hc, hd]
    push_cast
    ring
  have h₂ : c * (-d) + d * c = 0 := by ring
  have hR : swapRotation i j t * (swapRotation i j t)ᴴ = 1 := by
    change (c • (1 : Matrix ι ι ℂ) + d • P) * (c • (1 : Matrix ι ι ℂ) + d • P)ᴴ = _
    rw [hconj, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
    have hsmul (a b : ℂ) (V W : Matrix ι ι ℂ) :
        (a • V) * (b • W) = (a * b) • (V * W) := by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    simp only [hsmul, Matrix.one_mul, Matrix.mul_one, hPP]
    calc
      _ = (c * c + d * (-d)) • (1 : Matrix ι ι ℂ) +
          (c * (-d) + d * c) • P := by rw [add_smul, add_smul]; abel
      _ = _ := by rw [h₁, h₂, one_smul, zero_smul, add_zero]
  exact ⟨hR, Matrix.mul_eq_one_comm.mp hR⟩

private theorem supported_swap_permutation (i j : ι) (π : Perm ι)
    (hs : ∀ k, π k = k ∨ π k = Equiv.swap i j k) :
    π = 1 ∨ π = Equiv.swap i j := by
  have hfix (k : ι) (hki : k ≠ i) (hkj : k ≠ j) : π k = k :=
    (hs k).elim id fun h => h.trans (Equiv.swap_apply_of_ne_of_ne hki hkj)
  have hi : π i = i ∨ π i = j := by simpa only [Equiv.swap_apply_left] using hs i
  have hj : π j = j ∨ π j = i := by simpa only [Equiv.swap_apply_right] using hs j
  by_cases hij : i = j
  · subst j
    left
    ext k
    change π k = k
    by_cases hk : k = i
    · subst k
      exact hi.elim id id
    · exact hfix k hk hk
  · rcases hi with hi | hi
    · have hj' : π j = j := hj.resolve_right fun h => hij (π.injective (hi.trans h.symm))
      left
      ext k
      change π k = k
      by_cases hki : k = i
      · exact hki ▸ hi
      · by_cases hkj : k = j
        · exact hkj ▸ hj'
        · exact hfix k hki hkj
    · have hj' : π j = i := hj.resolve_left fun h => hij (π.injective (hi.trans h.symm))
      right
      ext k
      by_cases hki : k = i
      · subst k
        rw [hi, Equiv.swap_apply_left]
      · by_cases hkj : k = j
        · subst k
          rw [hj', Equiv.swap_apply_right]
        · rw [hfix k hki hkj, Equiv.swap_apply_of_ne_of_ne hki hkj]

private theorem sum_swap_supported {A : Type*} [AddCommMonoid A] (i j : ι) (hij : i ≠ j)
    (f : Perm ι → A) (hf : ∀ π, π ≠ 1 → π ≠ Equiv.swap i j → f π = 0) :
    (∑ π, f π) = f 1 + f (Equiv.swap i j) := by
  have hs : (1 : Perm ι) ≠ Equiv.swap i j := by
    intro h
    apply hij
    have e := DFunLike.congr_fun h i
    simpa only [Equiv.Perm.one_apply, Equiv.swap_apply_left] using e
  rw [← Finset.sum_subset (Finset.subset_univ ({1, Equiv.swap i j} : Finset (Perm ι)))
    (fun π _ hn => hf π (fun h => hn (by simp [h])) (fun h => hn (by simp [h])))]
  rw [Finset.sum_pair hs]

private theorem swapRotation_signedWeight_zero (i j : ι) (t : I) (π : Perm ι)
    (h₁ : π ≠ 1) (h₂ : π ≠ Equiv.swap i j) :
    signedWeight (swapRotation i j t) π = 0 := by
  have hk : ∃ k, π k ≠ k ∧ π k ≠ Equiv.swap i j k := by
    by_contra! h
    apply (supported_swap_permutation i j π ?_).elim h₁ h₂
    intro k
    by_cases he : π k = k
    · exact Or.inl he
    · exact Or.inr (h k he)
  obtain ⟨k, hfix, hswap⟩ := hk
  have hm : swapRotation i j t (π k) k = 0 := by
    simp only [swapRotation, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_ne hfix,
      swapMatrix_apply i j, if_neg hswap, smul_zero, zero_add]
  have hp : (∏ k, swapRotation i j t (π k) k) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ k) hm
  rw [signedWeight, leibnizTerm, hp, mul_zero, zero_div]

/-- A transposition rotates the determinant along the entire straight segment
between the two matchings. All entries outside the swapped pair are fixed
in the normal orbit. The proof allows equal eigenvalues. -/
theorem determinantValue_swapRotation (a b : ι → ℂ) (i j : ι) (hij : i ≠ j)
    (t : I) :
    determinantValue a b (swapRotation i j t) =
      (1 - ↑(t : ℝ)) * matchingProduct a b 1 +
        (↑(t : ℝ) : ℂ) * matchingProduct a b (Equiv.swap i j) := by
  let R := swapRotation i j t
  let w := signedWeight R
  have hR := swapRotation_unitary i j t
  have hzero (π : Perm ι) (h₁ : π ≠ 1) (h₂ : π ≠ Equiv.swap i j) : w π = 0 :=
    swapRotation_signedWeight_zero i j t π h₁ h₂
  have hsum : w 1 + w (Equiv.swap i j) = 1 :=
    (sum_swap_supported i j hij w hzero).symm.trans
      (sum_signedWeight R (det_ne_zero_of_unitary hR))
  have hentry : R j i = (↑(Real.sqrt (t : ℝ)) : ℂ) * Complex.I := by
    simp [R, swapRotation, Matrix.add_apply, Matrix.smul_apply,
      Matrix.one_apply_ne hij.symm, swapMatrix_apply i j]
  have hnorm : Complex.normSq (R j i) = (t : ℝ) := by
    rw [hentry, Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_I, mul_one,
      ← pow_two, Real.sq_sqrt t.property.1]
  have hm := marginal_signedWeight R hR j i
  rw [marginal, sum_swap_supported i j hij (fun π => if π i = j then w π else 0)
    (fun π h₁ h₂ => by simp [hzero π h₁ h₂]), hnorm] at hm
  simp only [Equiv.Perm.one_apply, if_neg hij, Equiv.swap_apply_left, if_true, zero_add] at hm
  have hw : w 1 = 1 - ↑(t : ℝ) := by rw [hm] at hsum; linear_combination hsum
  rw [← signed_determinant a b R hR, sum_swap_supported i j hij
    (fun π => w π * matchingProduct a b π) (fun π h₁ h₂ => by simp [hzero π h₁ h₂]),
    hw, hm]

private theorem continuous_swapRotation (i j : ι) :
    Continuous (swapRotation i j : I → Matrix ι ι ℂ) := by
  unfold swapRotation
  fun_prop

private def orbitConj (U B : Matrix ι ι ℂ) : Matrix ι ι ℂ := U * B * Uᴴ

private theorem orbitConj_mul (U V B : Matrix ι ι ℂ) :
    orbitConj U (orbitConj V B) = orbitConj (U * V) B := by
  simp only [orbitConj, Matrix.conjTranspose_mul, Matrix.mul_assoc]

private theorem orbitConj_one (B : Matrix ι ι ℂ) : orbitConj 1 B = B := by
  simp only [orbitConj, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

private theorem orbitConj_I_smul (U B : Matrix ι ι ℂ) :
    orbitConj (Complex.I • U) B = orbitConj U B := by
  have hstar : star Complex.I = -Complex.I := Complex.conj_I
  simp only [orbitConj, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, hstar, mul_neg, neg_mul, Complex.I_mul_I, neg_neg, one_smul]

private theorem isUnitary_mul_for_winding {U V : Matrix ι ι ℂ}
    (hU : IsUnitary U) (hV : IsUnitary V) : IsUnitary (U * V) := by
  have hU' : IsUnitary Uᴴ := by
    simpa only [IsUnitary, Matrix.conjTranspose_conjTranspose, and_comm] using hU
  simpa only [Matrix.conjTranspose_conjTranspose] using relative_unitary Uᴴ V hU' hV

private theorem swapRotation_zero (i j : ι) : swapRotation i j 0 = 1 := by
  simp [swapRotation]

private theorem swapRotation_one (i j : ι) :
    swapRotation i j 1 = Complex.I • (Equiv.swap i j).permMatrix ℂ := by
  simp [swapRotation]

private theorem permuted_diagonal (b : ι → ℂ) (p : Perm ι) :
    orbitConj (Equiv.Perm.permMatrix ℂ p.symm) (diagonal b) = diagonal (b ∘ p.symm) := by
  rw [orbitConj, permMatrix_conjugates, Matrix.submatrix_diagonal_equiv]

private theorem permuted_diagonal_swap (b : ι → ℂ) (p : Perm ι) (x y : ι) :
    orbitConj ((Equiv.swap x y).permMatrix ℂ) (diagonal (b ∘ p.symm)) =
      diagonal (b ∘ (Equiv.swap x y * p).symm) := by
  rw [orbitConj, permMatrix_conjugates, Matrix.submatrix_diagonal_equiv] <;> rfl

private theorem swapRotation_relabel (x y i j : ι) (t : I) :
    orbitConj ((Equiv.swap x y).permMatrix ℂ) (swapRotation i j t) =
      swapRotation (Equiv.swap x y i) (Equiv.swap x y j) t := by
  let s := Equiv.swap x y
  rw [orbitConj, permMatrix_conjugates s]
  ext k l
  have he : s k = Equiv.swap i j (s l) ↔ k = Equiv.swap (s i) (s j) l := by
    have h := congrArg (fun p : Perm ι => p (s l)) (mul_swap_eq_swap_mul s i j)
    change s (Equiv.swap i j (s l)) = Equiv.swap (s i) (s j) (s (s l)) at h
    rw [show s (s l) = l from Equiv.swap_apply_self x y l] at h
    constructor
    · intro hkl
      exact (Equiv.swap_apply_self x y k).symm.trans ((congrArg s hkl).trans h)
    · intro hkl
      apply s.injective
      exact (Equiv.swap_apply_self x y k).trans (hkl.trans h.symm)
  change swapRotation i j t (s k) (s l) = swapRotation (s i) (s j) t k l
  simp only [swapRotation, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
    swapMatrix_apply, s.injective.eq_iff, he]

private theorem matchingProduct_permute_right (a b : ι → ℂ) (p q : Perm ι) :
    matchingProduct a (b ∘ p.symm) q = matchingProduct a b (q * p) := by
  unfold matchingProduct
  rw [← Equiv.prod_comp p (fun k => a (q k) + (b ∘ p.symm) k)]
  simp only [Function.comp_apply, Equiv.symm_apply_apply, Equiv.Perm.mul_apply]

/-- The point with parameter `t` on the segment from `z` to `w`. -/
def straightSegmentPoint (z w : ℂ) (t : I) : ℂ :=
  (1 - ↑(t : ℝ)) * z + (↑(t : ℝ) : ℂ) * w

private theorem straightSegmentPoint_zero (z w : ℂ) : straightSegmentPoint z w 0 = z := by
  change (1 - (↑(0 : ℝ) : ℂ)) * z + (↑(0 : ℝ) : ℂ) * w = _
  simp

private theorem straightSegmentPoint_one (z w : ℂ) : straightSegmentPoint z w 1 = w := by
  change (1 - (↑(1 : ℝ) : ℂ)) * z + (↑(1 : ℝ) : ℂ) * w = _
  simp

private theorem permuted_edge_value (a b : ι → ℂ) (p : Perm ι)
    (i j : ι) (hij : i ≠ j) (t : I) :
    (diagonal a + orbitConj (swapRotation i j t) (diagonal (b ∘ p.symm))).det =
      straightSegmentPoint (matchingProduct a b p) (matchingProduct a b (Equiv.swap i j * p)) t := by
  change determinantValue a (b ∘ p.symm) (swapRotation i j t) = _
  rw [determinantValue_swapRotation a (b ∘ p.symm) i j hij t]
  simp only [matchingProduct_permute_right, one_mul, straightSegmentPoint]

/-- A square traced by two transposition rotations. Each of the four
boundary paths is the straight edge between its two matching products. -/
theorem transposition_square_in_determinant_range (a b : ι → ℂ) (p : Perm ι)
    (i j x y : ι) (hij : i ≠ j) (hxy : x ≠ y) :
    let z := matchingProduct a b
    let r := Equiv.swap x y
    let s := Equiv.swap i j
    ∃ F : I × I → ℂ, Continuous F ∧
      (∀ u, F u ∈ determinantRange a b) ∧
      (∀ t, F (0,t) = straightSegmentPoint (z p) (z (s * p)) t) ∧
      (∀ t, F (t,0) = straightSegmentPoint (z p) (z (r * p)) t) ∧
      (∀ t, F (1,t) = straightSegmentPoint (z (r * p)) (z (r * (s * p))) t) ∧
      (∀ t, F (t,1) = straightSegmentPoint (z (s * p)) (z (r * (s * p))) t) := by
  let D := diagonal (b ∘ p.symm)
  let F (u : I × I) :=
    (diagonal a + orbitConj (swapRotation x y u.1) (orbitConj (swapRotation i j u.2) D)).det
  refine ⟨F, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h₁ := (continuous_swapRotation x y).comp (continuous_fst : Continuous (Prod.fst : I × I → I))
    have h₂ := (continuous_swapRotation i j).comp (continuous_snd : Continuous (Prod.snd : I × I → I))
    unfold F orbitConj
    fun_prop
  · intro u
    let W := (swapRotation x y u.1 * swapRotation i j u.2) * Equiv.Perm.permMatrix ℂ p.symm
    have hW : IsUnitary W := isUnitary_mul_for_winding
      (isUnitary_mul_for_winding (swapRotation_unitary x y u.1) (swapRotation_unitary i j u.2))
      (isUnitary_permMatrix p.symm)
    refine ⟨W, hW, ?_⟩
    change (diagonal a + orbitConj W (diagonal b)).det = F u
    simp only [F, W, D, ← orbitConj_mul, permuted_diagonal]
  · intro t
    dsimp only [F]
    rw [swapRotation_zero, orbitConj_one]
    exact permuted_edge_value a b p i j hij t
  · intro t
    dsimp only [F]
    rw [swapRotation_zero, orbitConj_one]
    exact permuted_edge_value a b p x y hxy t
  · intro t
    let r := Equiv.swap x y
    let V := r.permMatrix ℂ
    have hV : IsUnitary V := isUnitary_permMatrix r
    have hcomm (R B : Matrix ι ι ℂ) :
        orbitConj V (orbitConj R B) = orbitConj (orbitConj V R) (orbitConj V B) := by
      have hVR : (orbitConj V R) * V = V * R := by
        rw [orbitConj, Matrix.mul_assoc (V * R), hV.2, Matrix.mul_one]
      rw [orbitConj_mul, orbitConj_mul, hVR]
    dsimp only [F, D]
    rw [swapRotation_one, orbitConj_I_smul, hcomm,
      swapRotation_relabel, permuted_diagonal_swap]
    have hh := permuted_edge_value a b (r * p) (r i) (r j)
      (fun he => hij (r.injective he)) t
    rw [← mul_assoc, ← mul_swap_eq_swap_mul, mul_assoc] at hh
    exact hh
  · intro t
    dsimp only [F, D]
    rw [swapRotation_one, orbitConj_I_smul, permuted_diagonal_swap]
    exact permuted_edge_value a b (Equiv.swap i j * p) x y hxy t

/-- A continuous nowhere-zero complex function on the unit square has a
continuous logarithm. -/
theorem exists_continuousLog_unitSquare (f : I × I → ℂ) (hf : Continuous f)
    (hnz : ∀ x, f x ≠ 0) :
    ∃ L : I × I → ℂ, Continuous L ∧ ∀ x, Complex.exp (L x) = f x := by
  obtain ⟨u, _, hmin⟩ := isCompact_univ.exists_isMinOn
    (Set.univ_nonempty : (Set.univ : Set (I × I)).Nonempty) hf.norm.continuousOn
  have hmin' (x : I × I) : ‖f u‖ ≤ ‖f x‖ := hmin (Set.mem_univ x)
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hf)
    ‖f u‖ (norm_pos_iff.mpr (hnz u))
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
  let m : ℕ := N + 1
  have hm : (0 : ℝ) < m := by exact_mod_cast (Nat.succ_pos N)
  have hmδ : 1 / (m : ℝ) < δ := by
    apply (div_lt_iff₀ hm).mpr
    have h' := (div_lt_iff₀ hδ).mp hN
    have hmN : (N : ℝ) < m := by exact_mod_cast (Nat.lt_succ_self N)
    have hp := mul_lt_mul_of_pos_right hmN hδ
    linarith only [h', hp]
  let r (k : ℕ) : I := ⟨min 1 ((k : ℝ) / m), le_min zero_le_one (by positivity), min_le_left _ _⟩
  let scale (k : ℕ) (x : I × I) : I × I := (r k * x.1, r k * x.2)
  let v (k : ℕ) (x : I × I) := f (scale k x)
  have hcoeff (k : ℕ) (hk : k ≤ m) : (r k : ℝ) = (k : ℝ) / m := by
    dsimp [r]
    apply min_eq_right
    exact (div_le_one hm).2 (by exact_mod_cast hk)
  have hzero : r 0 = 0 := by
    apply Subtype.ext
    rw [hcoeff 0 (Nat.zero_le m)]
    simp
  have hone : r m = 1 := by
    apply Subtype.ext
    rw [hcoeff m le_rfl]
    simp [hm.ne']
  have hv0 (x : I × I) : v 0 x = f (0,0) := by simp [v, scale, hzero]
  have hvm (x : I × I) : v m x = f x := by
    rcases x with ⟨x₁, x₂⟩
    simp only [v, scale, hone, one_mul]
  have hv (k : ℕ) : Continuous (v k) := by
    have h₁ : Continuous (fun x : I × I => r k * x.1) :=
      (continuous_const.mul (continuous_subtype_val.comp continuous_fst)).subtype_mk _
    have h₂ : Continuous (fun x : I × I => r k * x.2) :=
      (continuous_const.mul (continuous_subtype_val.comp continuous_snd)).subtype_mk _
    exact hf.comp (h₁.prodMk h₂)
  have hdist (k : ℕ) (hk : k < m) (x : I × I) : dist (scale (k + 1) x) (scale k x) < δ := by
    have hcoord (t : I) : dist (r (k + 1) * t) (r k * t) < δ := by
      change |(r (k + 1) : ℝ) * (t : ℝ) - (r k : ℝ) * (t : ℝ)| < δ
      rw [hcoeff (k + 1) (Nat.succ_le_of_lt hk), hcoeff k hk.le, ← sub_mul, ← sub_div]
      rw [show ((↑(k + 1) : ℝ) - (k : ℝ)) = 1 by push_cast; ring]
      rw [abs_of_nonneg (mul_nonneg (div_nonneg zero_le_one hm.le) t.property.1)]
      exact (mul_le_of_le_one_right (by positivity) t.property.2).trans_lt hmδ
    rw [Prod.dist_eq]
    exact max_lt (hcoord x.1) (hcoord x.2)
  have hratio (k : ℕ) (hk : k < m) (x : I × I) :
      v (k + 1) x / v k x ∈ Complex.slitPlane := by
    have hn : v k x ≠ 0 := hnz (scale k x)
    have ht : ‖v (k + 1) x - v k x‖ < ‖v k x‖ := by
      have h := hclose (hdist k hk x)
      change ‖v (k + 1) x - v k x‖ < ‖f u‖ at h
      exact h.trans_le (hmin' (scale k x))
    rw [show v (k + 1) x / v k x = 1 + (v (k + 1) x - v k x) / v k x by
      rw [sub_div, div_self hn]; ring]
    apply Complex.mem_slitPlane_of_norm_lt_one
    rw [norm_div, div_lt_one (norm_pos_iff.mpr hn)]
    exact ht
  let L (x : I × I) :=
    (f (0,0)).log + ∑ k ∈ Finset.range m, (v (k + 1) x / v k x).log
  refine ⟨L, continuous_const.add (continuous_finset_sum _ fun k hk =>
    ((hv (k + 1)).div (hv k) (fun x => hnz (scale k x))).clog
      (hratio k (Finset.mem_range.mp hk))), ?_⟩
  intro x
  have hprod (n : ℕ) :
      (∏ k ∈ Finset.range n, v (k + 1) x / v k x) = v n x / v 0 x := by
    induction n with
    | zero => simp [hnz (scale 0 x), v]
    | succ n ih =>
      rw [Finset.prod_range_succ, ih]
      have hn : v n x ≠ 0 := hnz (scale n x)
      rw [mul_comm (v n x / v 0 x), div_mul_div_comm, mul_comm (v n x) (v 0 x),
        mul_div_mul_right _ _ hn]
  have hterms :
      (∏ k ∈ Finset.range m, Complex.exp (v (k + 1) x / v k x).log) =
        ∏ k ∈ Finset.range m, v (k + 1) x / v k x := by
    apply Finset.prod_congr rfl
    intro k _
    exact Complex.exp_log (div_ne_zero (hnz (scale (k + 1) x)) (hnz (scale k x)))
  dsimp only [L]
  rw [Complex.exp_add, Complex.exp_sum, Complex.exp_log (hnz (0,0)), hterms,
    hprod, hv0, hvm, mul_comm (f (0,0)), div_mul_cancel₀ _ (hnz (0,0))]

private theorem edge_ratio_slit {z w : ℂ} (hz : z ≠ 0)
    (hseg : ∀ t : I, straightSegmentPoint z w t ≠ 0) (t : I) :
    straightSegmentPoint z w t / z ∈ Complex.slitPlane := by
  let v := w / z
  have hratio (s : I) : straightSegmentPoint z w s / z =
      1 - ↑(s : ℝ) + (↑(s : ℝ) : ℂ) * v := by
    unfold straightSegmentPoint v
    field_simp [hz]
  have hv : v ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    by_contra! hv
    have hp : 0 < 1 - v.re := by linarith only [hv.1]
    let s : I := ⟨1 / (1 - v.re), by positivity,
      (div_le_one hp).mpr (by linarith only [hv.1])⟩
    have he : 1 - (↑(s : ℝ) : ℂ) + (↑(s : ℝ) : ℂ) * v = 0 := by
      apply Complex.ext
      · simp only [Complex.sub_re, Complex.one_re, Complex.add_re, Complex.ofReal_re,
          Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero]
        change 1 - (1 / (1 - v.re)) + (1 / (1 - v.re)) * v.re = 0
        field_simp [hp.ne'] <;> ring
      · simp [hv.2]
    exact (div_ne_zero (hseg s) hz) ((hratio s).trans he)
  rw [hratio t, Complex.mem_slitPlane_iff]
  by_cases ht : (t : ℝ) = 0
  · simp [ht]
  · rcases Complex.mem_slitPlane_iff.mp hv with hpos | him
    · left
      simp only [Complex.sub_re, Complex.one_re, Complex.add_re, Complex.ofReal_re,
          Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero]
      have hmul : 0 < (t : ℝ) * v.re := mul_pos (lt_of_le_of_ne t.property.1 (Ne.symm ht)) hpos
      linarith only [t.property.2, hmul]
    · right
      simpa only [Complex.add_im, Complex.sub_im, Complex.one_im, Complex.ofReal_im,
        Complex.mul_im, Complex.ofReal_re, zero_mul, add_zero, zero_sub, neg_zero, zero_add]
        using mul_ne_zero ht him

private theorem circle_exp_im_eq {x y : ℂ} (h : Complex.exp x = Complex.exp y) :
    Circle.exp x.im = Circle.exp y.im := by
  rcases Complex.exp_eq_exp_iff_exists_int.mp h with ⟨n, hn⟩
  refine Circle.exp_eq_exp.mpr ⟨n, ?_⟩
  have hi := congrArg Complex.im hn
  simpa [Complex.mul_im, Complex.mul_re] using hi

private theorem log_change_along_segment (z w : ℂ) (hz : z ≠ 0)
    (hseg : ∀ t : I, straightSegmentPoint z w t ≠ 0) (L : I → ℂ)
    (hL : Continuous L) (hval : ∀ t, Complex.exp (L t) = straightSegmentPoint z w t) :
    (L 1).im - (L 0).im = Complex.arg (w / z) := by
  let K (t : I) := L 0 + Complex.log (straightSegmentPoint z w t / z)
  have hK : Continuous K := by
    have hpoint : Continuous (straightSegmentPoint z w) := by
      unfold straightSegmentPoint
      fun_prop
    exact continuous_const.add ((hpoint.div_const z).clog (edge_ratio_slit hz hseg))
  have hKval (t : I) : Complex.exp (K t) = straightSegmentPoint z w t := by
    dsimp only [K]
    rw [Complex.exp_add, hval 0, Complex.exp_log (div_ne_zero (hseg t) hz)]
    rw [straightSegmentPoint_zero, mul_comm z, div_mul_cancel₀ _ hz]
  have hK0 : K 0 = L 0 := by simp [K, straightSegmentPoint_zero, hz]
  have he := (T2Space.isSeparatedMap Circle.exp).eq_of_comp_eq
    isLocalHomeomorph_circleExp.isLocallyInjective (Complex.continuous_im.comp hL)
    (Complex.continuous_im.comp hK)
    (funext fun t => circle_exp_im_eq ((hval t).trans (hKval t).symm))
    (0 : I) (congrArg Complex.im hK0.symm)
  have he₁ : (L 1).im = (K 1).im := congrFun he 1
  rw [he₁]
  simp only [K, straightSegmentPoint_one, Complex.add_im, Complex.log_im]
  ring

private theorem straightSegmentPoint_sub (z w q : ℂ) (t : I) :
    straightSegmentPoint z w t - q = straightSegmentPoint (z - q) (w - q) t := by
  unfold straightSegmentPoint
  ring

private theorem square_boundary_angle (F : I × I → ℂ) (hF : Continuous F) (q : ℂ)
    (hz : ∀ u, F u ≠ q) (z₀₀ z₀₁ z₁₀ z₁₁ : ℂ)
    (h₀ : ∀ t, F (0,t) = straightSegmentPoint z₀₀ z₀₁ t)
    (h₁ : ∀ t, F (t,0) = straightSegmentPoint z₀₀ z₁₀ t)
    (h₂ : ∀ t, F (1,t) = straightSegmentPoint z₁₀ z₁₁ t)
    (h₃ : ∀ t, F (t,1) = straightSegmentPoint z₀₁ z₁₁ t) :
    Complex.arg ((z₁₁ - q) / (z₁₀ - q)) - Complex.arg ((z₀₁ - q) / (z₀₀ - q)) =
      Complex.arg ((z₁₁ - q) / (z₀₁ - q)) - Complex.arg ((z₁₀ - q) / (z₀₀ - q)) := by
  obtain ⟨L, hL, hval⟩ := exists_continuousLog_unitSquare (fun u => F u - q)
    (hF.sub continuous_const) (fun u => sub_ne_zero.mpr (hz u))
  have hside (f : I → I × I) (hf : Continuous f) (z w : ℂ)
      (he : ∀ t, F (f t) = straightSegmentPoint z w t) :
      (L (f 1)).im - (L (f 0)).im = Complex.arg ((w - q) / (z - q)) := by
    have hf' (t : I) : F (f t) - q = straightSegmentPoint (z - q) (w - q) t := by
      rw [he t, straightSegmentPoint_sub]
    have hh (t : I) : straightSegmentPoint (z - q) (w - q) t ≠ 0 := by
      rw [← hf' t]
      exact sub_ne_zero.mpr (hz (f t))
    have hstart : z - q ≠ 0 := by simpa only [straightSegmentPoint_zero] using hh 0
    exact log_change_along_segment (z - q) (w - q) hstart hh (L ∘ f)
      (hL.comp hf) (fun t => (hval (f t)).trans (hf' t))
  have H₀ := hside (fun t => (0,t)) (continuous_const.prodMk continuous_id) _ _ h₀
  have H₁ := hside (fun t => (t,0)) (continuous_id.prodMk continuous_const) _ _ h₁
  have H₂ := hside (fun t => (1,t)) (continuous_const.prodMk continuous_id) _ _ h₂
  have H₃ := hside (fun t => (t,1)) (continuous_id.prodMk continuous_const) _ _ h₃
  linarith only [H₀, H₁, H₂, H₃]

/-- The principal change of argument along an oriented matching edge. -/
def matchingEdgeAngle (a b : ι → ℂ) (z : ℂ) (p q : Equiv.Perm ι) : ℝ :=
  Complex.arg ((matchingProduct a b q - z) / (matchingProduct a b p - z))

/-- Reversing an oriented segment that avoids the point negates its angle. -/
theorem matchingEdgeAngle_reverse_of_segment_avoids (a b : ι → ℂ) (z : ℂ)
    (p q : Equiv.Perm ι)
    (h : ∀ t, straightSegmentPoint (matchingProduct a b p) (matchingProduct a b q) t ≠ z) :
    matchingEdgeAngle a b z q p = -matchingEdgeAngle a b z p q := by
  have hp : matchingProduct a b p - z ≠ 0 := by
    apply sub_ne_zero.mpr
    simpa only [straightSegmentPoint_zero] using h 0
  have hseg (t : I) : straightSegmentPoint (matchingProduct a b p - z)
      (matchingProduct a b q - z) t ≠ 0 := by
    rw [← straightSegmentPoint_sub]
    exact sub_ne_zero.mpr (h t)
  have hslit := edge_ratio_slit hp hseg 1
  rw [straightSegmentPoint_one] at hslit
  unfold matchingEdgeAngle
  rw [← inv_div, Complex.arg_inv, if_neg (Complex.slitPlane_arg_ne_pi hslit)]

/-- At an omitted point, each oriented edge angle is a difference of values
on its endpoints. -/
theorem exists_matchingEdgeAngle_potential_of_notMem (a b : ι → ℂ) (q : ℂ)
    (hq : q ∉ determinantRange a b) :
    ∃ v : Equiv.Perm ι → ℝ, ∀ p r, TranspositionEdge p r →
      matchingEdgeAngle a b q p r = v r - v p := by
  let d := matchingEdgeAngle a b q
  have hreverse (p₀ p₁ : Perm ι) (hedge : TranspositionEdge p₀ p₁) :
      d p₁ p₀ = -d p₀ p₁ := by
    obtain ⟨i,j,hij,rfl⟩ := hedge
    obtain ⟨F, _, hF, hside, _, _, _⟩ :=
      transposition_square_in_determinant_range a b p₀ i j i j hij hij
    apply matchingEdgeAngle_reverse_of_segment_avoids
    intro t ht
    apply hq
    rw [← ht, ← hside t]
    exact hF (0,t)
  have hsquare (x y : ι) (hxy : x ≠ y) (p₀ p₁ : Perm ι) (hedge : TranspositionEdge p₀ p₁) :
      let r := Equiv.swap x y
      d (r * p₀) (r * p₁) - d p₀ p₁ = d p₁ (r * p₁) - d p₀ (r * p₀) := by
    obtain ⟨i,j,hij,rfl⟩ := hedge
    obtain ⟨F, hF, hmem, H₀, H₁, H₂, H₃⟩ :=
      transposition_square_in_determinant_range a b p₀ i j x y hij hxy
    exact square_boundary_angle F hF q (fun u he => hq (he ▸ hmem u)) _ _ _ _ H₀ H₁ H₂ H₃
  exact exists_transposition_potential_of_squares d hreverse hsquare

/-- The sum of edge angles along a transposition walk, in radians. If the
walk avoids the point, division by `2 * Real.pi` gives its winding number. -/
def transpositionWindingAngle (a b : ι → ℂ) (q : ℂ)
    (m : ℕ) (p : ℕ → Equiv.Perm ι) : ℝ :=
  ∑ k ∈ Finset.range m, matchingEdgeAngle a b q (p k) (p (k + 1))

/-- A closed transposition walk with nonzero winding gives an attained value. -/
theorem mem_determinantRange_of_transposition_winding_ne_zero (a b : ι → ℂ) (q : ℂ)
    (m : ℕ) (p : ℕ → Equiv.Perm ι) (hclosed : p m = p 0)
    (hwalk : ∀ k < m, TranspositionEdge (p k) (p (k + 1)))
    (hwinding : transpositionWindingAngle a b q m p ≠ 0) :
    q ∈ determinantRange a b := by
  by_contra hq
  obtain ⟨v, hv⟩ := exists_matchingEdgeAngle_potential_of_notMem a b q hq
  apply hwinding
  calc
    transpositionWindingAngle a b q m p = ∑ k ∈ Finset.range m, (v (p (k + 1)) - v (p k)) :=
      Finset.sum_congr rfl fun k hk => hv _ _ (hwalk k (Finset.mem_range.mp hk))
    _ = 0 := by
      rw [telescope_sum (v ∘ p)]
      simp only [Function.comp_apply, hclosed, sub_self]

/-- An integer cellular cycle of the transposition graph. The boundary
at a vertex is the incoming coefficient sum minus the outgoing sum.
Either orientation can represent an edge, with the opposite coefficient. -/
structure TranspositionCycle (ι : Type*) [Fintype ι] [DecidableEq ι] where
  coefficient : Equiv.Perm ι → Equiv.Perm ι → ℤ
  supported : ∀ p q, coefficient p q ≠ 0 → TranspositionEdge p q
  boundary_zero : ∀ p, (∑ q, coefficient q p) = ∑ q, coefficient p q

/-- A cycle avoids the point if every segment with nonzero coefficient avoids it. -/
def TranspositionCycle.Avoids (c : TranspositionCycle ι) (a b : ι → ℂ) (z : ℂ) : Prop :=
  ∀ p q, c.coefficient p q ≠ 0 →
    ∀ t, straightSegmentPoint (matchingProduct a b p) (matchingProduct a b q) t ≠ z

/-- The sum of edge angles weighted by an integer cycle. -/
def TranspositionCycle.windingAngle (c : TranspositionCycle ι) (a b : ι → ℂ) (z : ℂ) : ℝ :=
  ∑ p, ∑ q, (c.coefficient p q : ℝ) * matchingEdgeAngle a b z p q

private theorem TranspositionCycle.two_mul_windingAngle (c : TranspositionCycle ι)
    (a b : ι → ℂ) (z : ℂ) (h : c.Avoids a b z) :
    2 * c.windingAngle a b z = ∑ p, ∑ q,
      ((c.coefficient p q - c.coefficient q p : ℤ) : ℝ) * matchingEdgeAngle a b z p q := by
  have hr : (∑ p, ∑ q, (c.coefficient q p : ℝ) * matchingEdgeAngle a b z p q) =
      -c.windingAngle a b z := by
    rw [Finset.sum_comm, TranspositionCycle.windingAngle, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro p _
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro q _
    by_cases hc : c.coefficient p q = 0
    · simp only [hc, Int.cast_zero, zero_mul, neg_zero]
    · rw [matchingEdgeAngle_reverse_of_segment_avoids a b z p q (h p q hc), mul_neg]
  simp only [Int.cast_sub, sub_mul, Finset.sum_sub_distrib,
    ← TranspositionCycle.windingAngle, hr, sub_neg_eq_add, two_mul]

/-- The angle depends only on the signed coefficient of each oriented edge. -/
theorem TranspositionCycle.windingAngle_eq_of_orientedCoefficients
    (c e : TranspositionCycle ι) (a b : ι → ℂ) (z : ℂ)
    (hc : c.Avoids a b z) (he : e.Avoids a b z)
    (h : ∀ p q, c.coefficient p q - c.coefficient q p = e.coefficient p q - e.coefficient q p) :
    c.windingAngle a b z = e.windingAngle a b z := by
  have hmul : 2 * c.windingAngle a b z = 2 * e.windingAngle a b z := by
    rw [c.two_mul_windingAngle a b z hc, e.two_mul_windingAngle a b z he]
    simp only [h]
  linarith only [hmul]

private theorem TranspositionCycle.sum_vertex_differences_eq_zero
    (c : TranspositionCycle ι) (v : Equiv.Perm ι → ℝ) :
    (∑ p, ∑ q, (c.coefficient p q : ℝ) * (v q - v p)) = 0 := by
  have hin : (∑ p, ∑ q, (c.coefficient p q : ℝ) * v q) =
      ∑ p, ((∑ q, c.coefficient q p : ℤ) : ℝ) * v p := by
    rw [Finset.sum_comm]
    simp only [Int.cast_sum, Finset.sum_mul]
  have hout : (∑ p, ∑ q, (c.coefficient p q : ℝ) * v p) =
      ∑ p, ((∑ q, c.coefficient p q : ℤ) : ℝ) * v p := by
    simp only [Int.cast_sum, Finset.sum_mul]
  simp only [mul_sub, Finset.sum_sub_distrib, hin, hout, c.boundary_zero, sub_self]

/-- Every integer cellular cycle with nonzero angle gives an attained value. -/
theorem mem_determinantRange_of_transpositionCycle_winding_ne_zero
    (a b : ι → ℂ) (z : ℂ) (c : TranspositionCycle ι) (hwinding : c.windingAngle a b z ≠ 0) :
    z ∈ determinantRange a b := by
  by_contra hz
  obtain ⟨v, hv⟩ := exists_matchingEdgeAngle_potential_of_notMem a b z hz
  apply hwinding
  calc
    c.windingAngle a b z = ∑ p, ∑ q, (c.coefficient p q : ℝ) * (v q - v p) := by
      unfold TranspositionCycle.windingAngle
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      by_cases hc : c.coefficient p q = 0
      · simp only [hc, Int.cast_zero, zero_mul]
      · rw [hv p q (c.supported p q hc)]
    _ = 0 := c.sum_vertex_differences_eq_zero v

end

end MOC
