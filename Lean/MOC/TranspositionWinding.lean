import MOC.StrongSupport
import MOC.Weights
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Topology.SeparatedMap
import Mathlib.Topology.UnitInterval

/-! Transposition walks for the attainable determinant range. -/

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

/-- A real value on each oriented edge has zero sum along every closed walk
if reversing an edge negates its value and every translated square has
zero sum. The proof averages over all permutation translates of the walk. -/
theorem transposition_walk_sum_eq_zero_of_squares
    (d : Equiv.Perm ι → Equiv.Perm ι → ℝ)
    (hreverse : ∀ p q, TranspositionEdge p q → d q p = -d p q)
    (hsquare : ∀ i j, i ≠ j → ∀ p q, TranspositionEdge p q →
      let s := Equiv.swap i j
      d (s * p) (s * q) - d p q = d q (s * q) - d p (s * p))
    (m : ℕ) (p : ℕ → Equiv.Perm ι) (hclosed : p m = p 0)
    (hwalk : ∀ k < m, TranspositionEdge (p k) (p (k + 1))) :
    (∑ k ∈ Finset.range m, d (p k) (p (k + 1))) = 0 := by
  let total (g : Perm ι) := ∑ k ∈ Finset.range m, d (g * p k) (g * p (k + 1))
  have hinvariant (g : Perm ι) : total g = total 1 := by
    induction g using Equiv.Perm.swap_induction_on with
    | one => rfl
    | swap_mul g i j hij ih =>
      let s := Equiv.swap i j
      have hdiff : total (s * g) - total g =
          ∑ k ∈ Finset.range m, (d (g * p (k + 1)) (s * (g * p (k + 1))) -
            d (g * p k) (s * (g * p k))) := by
        simp only [total, mul_assoc, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro k hk
        exact hsquare i j hij (g * p k) (g * p (k + 1))
          (transpositionEdge_translate g (hwalk k (Finset.mem_range.mp hk)))
      have hz : total (s * g) - total g = 0 := by
        rw [hdiff, telescope_sum (fun k => d (g * p k) (s * (g * p k))), hclosed, sub_self]
      exact (sub_eq_zero.mp hz).trans ih
  have hedge (k : ℕ) (hk : k < m) : (∑ g : Perm ι, d (g * p k) (g * p (k + 1))) = 0 := by
    obtain ⟨i, j, _, hstep⟩ := hwalk k hk
    let s := Equiv.swap i j
    let f (g : Perm ι) := d (g * p k) (g * p (k + 1))
    have hf (g : Perm ι) : f (g * s) = -f g := by
      have hs : s * p (k + 1) = p k := by
        rw [hstep, ← mul_assoc, s, swap_mul_swap_self, one_mul]
      change d ((g * s) * p k) ((g * s) * p (k + 1)) = _
      rw [mul_assoc, mul_assoc, hs, ← hstep]
      exact hreverse _ _ (transpositionEdge_translate g (hwalk k hk))
    have he : (∑ g, f (g * s)) = ∑ g, f g := Equiv.sum_comp (Equiv.mulRight s) f
    simp only [hf, Finset.sum_neg_distrib] at he
    change (∑ g, f g) = 0
    linarith only [he]
  have hsum : (∑ g : Perm ι, total g) = 0 := by
    unfold total
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero fun k hk => hedge k (Finset.mem_range.mp hk)
  simp only [hinvariant, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  have hcard : (Fintype.card (Perm ι) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Perm ι) ≠ 0)
  simpa only [total, one_mul] using (mul_eq_zero.mp hsum).resolve_left hcard

private theorem swapMatrix_apply (i j k l : ι) :
    (Equiv.swap i j).permMatrix ℂ k l = if k = Equiv.swap i j l then 1 else 0 := by
  have he : l = Equiv.swap i j k ↔ k = Equiv.swap i j l := by
    constructor <;> intro h <;>
      simpa [h, Equiv.swap_apply_self]
  simp [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, he, eq_comm]

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
  have hPstar : Pᴴ = P := by rw [P, Matrix.conjTranspose_permMatrix, hinv]
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
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul,
      Matrix.mul_one, hPP]
    calc
      _ = (c * c + d * (-d)) • (1 : Matrix ι ι ℂ) +
          (c * (-d) + d * c) • P := by rw [add_smul, add_smul]; abel
      _ = _ := by rw [h₁, h₂, one_smul, zero_smul, add_zero]
  exact ⟨hR, Matrix.mul_eq_one_comm.mp hR⟩

private theorem supported_swap_permutation (i j : ι) (σ : Perm ι)
    (hs : ∀ k, σ k = k ∨ σ k = Equiv.swap i j k) :
    σ = 1 ∨ σ = Equiv.swap i j := by
  have hfix (k : ι) (hki : k ≠ i) (hkj : k ≠ j) : σ k = k :=
    (hs k).elim id fun h => h.trans (Equiv.swap_apply_of_ne_of_ne hki hkj)
  have hi : σ i = i ∨ σ i = j := by simpa only [Equiv.swap_apply_left] using hs i
  have hj : σ j = j ∨ σ j = i := by simpa only [Equiv.swap_apply_right] using hs j
  by_cases hij : i = j
  · subst j
    left
    ext k
    change σ k = k
    by_cases hk : k = i
    · subst k
      exact hi.elim id id
    · exact hfix k hk hk
  · rcases hi with hi | hi
    · have hj' : σ j = j := hj.resolve_right fun h => hij (σ.injective (hi.trans h.symm))
      left
      ext k
      change σ k = k
      by_cases hki : k = i
      · exact hki ▸ hi
      · by_cases hkj : k = j
        · exact hkj ▸ hj'
        · exact hfix k hki hkj
    · have hj' : σ j = i := hj.resolve_left fun h => hij (σ.injective (hi.trans h.symm))
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
    (f : Perm ι → A) (hf : ∀ σ, σ ≠ 1 → σ ≠ Equiv.swap i j → f σ = 0) :
    (∑ σ, f σ) = f 1 + f (Equiv.swap i j) := by
  have hs : (1 : Perm ι) ≠ Equiv.swap i j := by
    intro h
    apply hij
    have e := DFunLike.congr_fun h i
    simpa only [Equiv.Perm.one_apply, Equiv.swap_apply_left] using e
  rw [← Finset.sum_subset (Finset.subset_univ ({1, Equiv.swap i j} : Finset (Perm ι)))
    (fun σ _ hn => hf σ (fun h => hn (by simp [h])) (fun h => hn (by simp [h])))]
  rw [Finset.sum_pair hs]

private theorem swapRotation_signedWeight_zero (i j : ι) (t : I) (σ : Perm ι)
    (h₁ : σ ≠ 1) (h₂ : σ ≠ Equiv.swap i j) :
    signedWeight (swapRotation i j t) σ = 0 := by
  have hk : ∃ k, σ k ≠ k ∧ σ k ≠ Equiv.swap i j k := by
    by_contra! h
    exact (supported_swap_permutation i j σ h).elim h₁ h₂
  obtain ⟨k, hfix, hswap⟩ := hk
  have hm : swapRotation i j t (σ k) k = 0 := by
    simp [swapRotation, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_ne hfix,
      swapMatrix_apply i j, hswap]
  have hp : (∏ k, swapRotation i j t (σ k) k) = 0 :=
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
  have hzero (σ : Perm ι) (h₁ : σ ≠ 1) (h₂ : σ ≠ Equiv.swap i j) : w σ = 0 :=
    swapRotation_signedWeight_zero i j t σ h₁ h₂
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
  rw [marginal, sum_swap_supported i j hij (fun σ => if σ i = j then w σ else 0)
    (fun σ h₁ h₂ => by rw [hzero σ h₁ h₂]; simp), hnorm] at hm
  simp only [Equiv.Perm.one_apply, if_neg hij, Equiv.swap_apply_left, if_true, zero_add] at hm
  have hw : w 1 = 1 - ↑(t : ℝ) := by rw [hm] at hsum; linear_combination hsum
  rw [← signed_determinant a b R hR, sum_swap_supported i j hij
    (fun σ => w σ * matchingProduct a b σ) (fun σ h₁ h₂ => by rw [hzero σ h₁ h₂, zero_mul]),
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
    orbitConj (p.symm.permMatrix ℂ) (diagonal b) = diagonal (b ∘ p.symm) := by
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
      rw [hkl, h, Equiv.swap_apply_self]
    · intro hkl
      apply s.injective
      rw [hkl, h, Equiv.swap_apply_self]
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
  · unfold F orbitConj
    fun_prop (disch := exact continuous_swapRotation _ _)
  · intro u
    let W := (swapRotation x y u.1 * swapRotation i j u.2) * p.symm.permMatrix ℂ
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
    dsimp only [F]
    rw [swapRotation_one, orbitConj_I_smul, hcomm,
      swapRotation_relabel, D, permuted_diagonal_swap]
    have hh := permuted_edge_value a b (r * p) (r i) (r j)
      (fun he => hij (r.injective he)) t
    rw [← mul_assoc, ← mul_swap_eq_swap_mul, mul_assoc] at hh
    exact hh
  · intro t
    dsimp only [F]
    rw [swapRotation_one, orbitConj_I_smul, D, permuted_diagonal_swap]
    exact permuted_edge_value a b (Equiv.swap i j * p) x y hxy t

private theorem exists_square_log (f : I × I → ℂ) (hf : Continuous f)
    (hnz : ∀ x, f x ≠ 0) :
    ∃ L : I × I → ℂ, Continuous L ∧ ∀ x, Complex.exp (L x) = f x := by
  obtain ⟨u, _, hmin⟩ := isCompact_univ.exists_isMinOn
    (Set.univ_nonempty : (Set.univ : Set (I × I)).Nonempty) hf.norm.continuousOn
  have hmin' (x : I × I) : ‖f u‖ ≤ ‖f x‖ := hmin (Set.mem_univ x)
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuous_iff.mp hf.uniformContinuous
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
      rw [abs_of_nonneg (by positivity)]
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
      field_simp [hn]; ring]
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
      field_simp [hn]
  have hterms :
      (∏ k ∈ Finset.range m, Complex.exp (v (k + 1) x / v k x).log) =
        ∏ k ∈ Finset.range m, v (k + 1) x / v k x := by
    apply Finset.prod_congr rfl
    intro k _
    exact Complex.exp_log (div_ne_zero (hnz (scale (k + 1) x)) (hnz (scale k x)))
  rw [L, Complex.exp_add, Complex.exp_sum, Complex.exp_log (hnz (0,0)), hterms,
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
      have hmul : 0 < (t : ℝ) * v.re := mul_pos (lt_of_le_of_ne t.property.1 ht.symm) hpos
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
    unfold K
    refine continuous_const.add ((?_.div_const z).clog (edge_ratio_slit hz hseg))
    unfold straightSegmentPoint
    fun_prop
  have hKval (t : I) : Complex.exp (K t) = straightSegmentPoint z w t := by
    rw [K, Complex.exp_add, hval 0, Complex.exp_log (div_ne_zero (hseg t) hz)]
    rw [straightSegmentPoint_zero, mul_comm z, div_mul_cancel₀ _ hz]
  have hK0 : K 0 = L 0 := by simp [K, straightSegmentPoint_zero, hz]
  have he := (T2Space.isSeparatedMap Circle.exp).eq_of_comp_eq
    isLocalHomeomorph_circleExp.isLocallyInjective (Complex.continuous_im.comp hL)
    (Complex.continuous_im.comp hK)
    (funext fun t => circle_exp_im_eq ((hval t).trans (hKval t).symm))
    (0 : I) (congrArg Complex.im hK0.symm)
  rw [congrFun he 1]
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
  obtain ⟨L, hL, hval⟩ := exists_square_log (fun u => F u - q)
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

/-- The sum of principal changes of argument along the matching edges, in
radians. When the polygon avoids the point, division by `2 * Real.pi`
gives its winding number. -/
def transpositionWindingAngle (a b : ι → ℂ) (q : ℂ)
    (m : ℕ) (p : ℕ → Equiv.Perm ι) : ℝ :=
  ∑ k ∈ Finset.range m, Complex.arg
    ((matchingProduct a b (p (k + 1)) - q) / (matchingProduct a b (p k) - q))

/-- A closed transposition walk with nonzero winding certifies an attained
determinant value in every dimension, including repeated eigenvalues. -/
theorem mem_determinantRange_of_transposition_winding_ne_zero (a b : ι → ℂ) (q : ℂ)
    (m : ℕ) (p : ℕ → Equiv.Perm ι) (hclosed : p m = p 0)
    (hwalk : ∀ k < m, TranspositionEdge (p k) (p (k + 1)))
    (hwinding : transpositionWindingAngle a b q m p ≠ 0) :
    q ∈ determinantRange a b := by
  by_contra hq
  let z := matchingProduct a b
  let d (p₀ p₁ : Perm ι) := Complex.arg ((z p₁ - q) / (z p₀ - q))
  have hz (p₀ : Perm ι) : z p₀ - q ≠ 0 := by
    apply sub_ne_zero.mpr
    intro he
    apply hq
    rw [← he]
    exact matchingProduct_mem_determinantRange a b p₀
  have hreverse (p₀ p₁ : Perm ι) (hedge : TranspositionEdge p₀ p₁) :
      d p₁ p₀ = -d p₀ p₁ := by
    obtain ⟨i,j,hij,rfl⟩ := hedge
    obtain ⟨F, _, hF, hside, _, _, _⟩ :=
      transposition_square_in_determinant_range a b p₀ i j i j hij hij
    have hseg (t : I) : straightSegmentPoint (z p₀ - q) (z (Equiv.swap i j * p₀) - q) t ≠ 0 := by
      rw [← straightSegmentPoint_sub, ← hside t]
      exact sub_ne_zero.mpr (fun he => hq (he ▸ hF (0,t)))
    have hslit := edge_ratio_slit (hz p₀) hseg 1
    rw [straightSegmentPoint_one] at hslit
    dsimp only [d]
    rw [← inv_div, Complex.arg_inv, if_neg (Complex.slitPlane_arg_ne_pi hslit)]
  have hsquare (x y : ι) (hxy : x ≠ y) (p₀ p₁ : Perm ι) (hedge : TranspositionEdge p₀ p₁) :
      let r := Equiv.swap x y
      d (r * p₀) (r * p₁) - d p₀ p₁ = d p₁ (r * p₁) - d p₀ (r * p₀) := by
    obtain ⟨i,j,hij,rfl⟩ := hedge
    obtain ⟨F, hF, hmem, H₀, H₁, H₂, H₃⟩ :=
      transposition_square_in_determinant_range a b p₀ i j x y hij hxy
    exact square_boundary_angle F hF q (fun u he => hq (he ▸ hmem u)) _ _ _ _ H₀ H₁ H₂ H₃
  exact hwinding (transposition_walk_sum_eq_zero_of_squares d hreverse hsquare m p hclosed hwalk)

end

end MOC
