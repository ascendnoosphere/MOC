import MOC.OrderFourGivens

/-!
# Complex flat swaps

Kovačec, DMUC Preprint 26-11 v2 (4 November 2026), studies Givens
slices from matching matrices: https://www.mat.uc.pt/preprints/ps/p2611.pdf
(no assigned DOI identified). Here the starting mixer is arbitrary. If
a signed row swap ties a unitary support maximum, phases followed by
any real rotation of the pair preserve the maximum.
-/

open Matrix

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem diagonal_phase_unitary (d : ι → ℂ)
    (hd : ∀ i, star (d i) * d i = 1) : IsUnitary (diagonal d) := by
  have he : (fun i => star (d i) * d i) = fun _ => 1 := funext hd
  constructor
  · rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    change diagonal (fun i => d i * star (d i)) = 1
    simp_rw [mul_comm (d _), hd, Matrix.diagonal_one]
  · rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    change diagonal (fun i => star (d i) * d i) = 1
    rw [he, Matrix.diagonal_one]

private theorem isUnitary_diagonal_phase_mul {U : Matrix ι ι ℂ} (hU : IsUnitary U)
    (d : ι → ℂ) (hd : ∀ i, star (d i) * d i = 1) :
    IsUnitary (diagonal d * U) := by
  have hD := diagonal_phase_unitary d hd
  have hD' : IsUnitary (diagonal d)ᴴ := ⟨by simpa using hD.2, by simpa using hD.1⟩
  simpa only [Matrix.conjTranspose_conjTranspose] using relative_unitary _ U hD' hU

private theorem determinantValue_diagonal_phase (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (d : ι → ℂ) (hd : ∀ i, star (d i) * d i = 1) :
    determinantValue a b (diagonal d * U) = determinantValue a b U := by
  let D := diagonal d
  have hu := diagonal_phase_unitary d hd
  change (diagonal a + (D * U) * diagonal b * (D * U)ᴴ).det =
    (diagonal a + U * diagonal b * Uᴴ).det
  rw [← det_unitary_conjugation D (diagonal a + U * diagonal b * Uᴴ) hu]
  rw [Matrix.conjTranspose_mul, Matrix.mul_add, Matrix.add_mul]
  have hcomm : D * diagonal a = diagonal a * D := by
    dsimp only [D]
    simp_rw [Matrix.diagonal_mul_diagonal, mul_comm (d _)]
  rw [hcomm, Matrix.mul_assoc (diagonal a), hu.1, Matrix.mul_one]
  simp only [Matrix.mul_assoc]

omit [Fintype ι] in
private theorem rotateRows_entry_i (U : Matrix ι ι ℂ) {i j : ι} (hij : i ≠ j)
    (c s : ℝ) (k : ι) :
    rotateRows U i j c s i k = (c : ℂ) * U i k + (s : ℂ) * U j k := by
  change ((U.updateRow i ((c : ℂ) • U i + (s : ℂ) • U j)).updateRow j
    ((c : ℂ) • U j + (-(s : ℂ)) • U i)) i k = _
  simp [Matrix.updateRow_apply, hij, Pi.smul_apply, smul_eq_mul]

omit [Fintype ι] in
private theorem rotateRows_entry_j (U : Matrix ι ι ℂ) (i j : ι) (c s : ℝ) (k : ι) :
    rotateRows U i j c s j k = (c : ℂ) * U j k + (-(s : ℂ)) * U i k := by
  change ((U.updateRow i ((c : ℂ) • U i + (s : ℂ) • U j)).updateRow j
    ((c : ℂ) • U j + (-(s : ℂ)) • U i)) j k = _
  simp [Matrix.updateRow_apply, Pi.smul_apply, smul_eq_mul]

omit [Fintype ι] in
private theorem rotateRows_entry_other (U : Matrix ι ι ℂ) {i j q : ι}
    (hqi : q ≠ i) (hqj : q ≠ j) (c s : ℝ) (k : ι) :
    rotateRows U i j c s q k = U q k := by
  change ((U.updateRow i ((c : ℂ) • U i + (s : ℂ) • U j)).updateRow j
    ((c : ℂ) • U j + (-(s : ℂ)) • U i)) q k = _
  simp [Matrix.updateRow_apply, hqi, hqj]

private theorem signed_swap_diagonal_phase (U : Matrix ι ι ℂ) {i j : ι}
    (hij : i ≠ j) (d : ι → ℂ) :
    rotateRows (diagonal d * U) i j 0 1 =
      diagonal (d ∘ Equiv.swap i j) * rotateRows U i j 0 1 := by
  ext q k
  rw [Matrix.diagonal_mul]
  by_cases hi : q = i
  · subst q
    simp only [rotateRows_entry_i _ hij, Complex.ofReal_zero, Complex.ofReal_one,
      zero_mul, one_mul, zero_add, Function.comp_apply, Equiv.swap_apply_left,
      Matrix.diagonal_mul]
  · by_cases hj : q = j
    · subst q
      simp only [rotateRows_entry_j, Complex.ofReal_zero, Complex.ofReal_one,
        zero_mul, neg_mul, one_mul, zero_add, Function.comp_apply, Equiv.swap_apply_right,
        Matrix.diagonal_mul, mul_neg]
    · simp [rotateRows_entry_other _ hi hj, Equiv.swap_apply_of_ne_of_ne hi hj, Matrix.diagonal_mul]

/-- A tied signed swap at a support maximum makes every phased rotation
of the same two rows preserve that height. The diagonal phases are arbitrary. -/
theorem flat_phase_rotateRows_of_support_max (a b : ι → ℂ) (η : ℂ)
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) {i j : ι} (hij : i ≠ j)
    (hmax : ∀ V : Matrix ι ι ℂ, IsUnitary V →
      (η * determinantValue a b V).re ≤ (η * determinantValue a b U).re)
    (hswap : (η * determinantValue a b (rotateRows U i j 0 1)).re =
      (η * determinantValue a b U).re)
    (d : ι → ℂ) (hd : ∀ i, star (d i) * d i = 1)
    (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    (η * determinantValue a b (rotateRows (diagonal d * U) i j c s)).re =
      (η * determinantValue a b U).re := by
  let V := diagonal d * U
  have hV : IsUnitary V := isUnitary_diagonal_phase_mul hU d hd
  have ht : determinantValue a b V = determinantValue a b U :=
    determinantValue_diagonal_phase a b U d hd
  have hs' : (η * determinantValue a b (rotateRows V i j 0 1)).re =
      (η * determinantValue a b V).re := by
    rw [ht]
    change (η * determinantValue a b (rotateRows (diagonal d * U) i j 0 1)).re = _
    rw [signed_swap_diagonal_phase U hij,
      determinantValue_diagonal_phase a b _ (d ∘ Equiv.swap i j)
        (fun q => hd (Equiv.swap i j q))]
    exact hswap
  exact (flat_rotateRows_of_support_max a b η V hV i j hij
    (by simpa only [ht] using hmax) hs' c s hcs).trans (congrArg (fun z : ℂ => (η * z).re) ht)

private theorem unit_phase_mul_eq_norm (z : ℂ) (hz : z ≠ 0) :
    ∃ u : ℂ, star u * u = 1 ∧ u * z = (‖z‖ : ℂ) := by
  let u : ℂ := (‖z‖ : ℂ) / z
  refine ⟨u, ?_, div_mul_cancel₀ _ hz⟩
  have hn : Complex.normSq z ≠ 0 := by
    rw [Complex.normSq_eq_norm_sq]
    exact pow_ne_zero _ (norm_ne_zero_iff.mpr hz)
  change (starRingEnd ℂ) u * u = 1
  rw [← Complex.normSq_eq_conj_mul_self, show u = (‖z‖ : ℂ) / z from rfl,
    Complex.normSq_div, Complex.normSq_ofReal, ← pow_two, ← Complex.normSq_eq_norm_sq,
    div_self hn, Complex.ofReal_one]

private theorem exists_unit_circle_annihilator (x y : ℝ) (hx : x ≠ 0) :
    ∃ c s : ℝ, c ^ 2 + s ^ 2 = 1 ∧ c * x + s * y = 0 := by
  have hp : 0 < x ^ 2 + y ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hx) (sq_nonneg _)
  let r := Real.sqrt (x ^ 2 + y ^ 2)
  have hr : r ≠ 0 := (Real.sqrt_pos.2 hp).ne'
  have hrsq : r ^ 2 = x ^ 2 + y ^ 2 := Real.sq_sqrt hp.le
  refine ⟨y / r, -x / r, ?_, ?_⟩
  · rw [div_pow, div_pow, ← add_div, neg_sq, hrsq, add_comm]
    exact div_self hp.ne'
  · field_simp
    ring

/-- A tied signed row swap of two nonzero entries in a chosen column permits
a support-preserving change of basis that shrinks the column's support.
Every other zero in the same column is retained. -/
theorem exists_support_max_with_column_support_ssubset_of_flat_swap
    (a b : ι → ℂ) (η : ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U) {i j k : ι}
    (hij : i ≠ j) (hi : U i k ≠ 0) (hj : U j k ≠ 0)
    (hmax : ∀ V : Matrix ι ι ℂ, IsUnitary V →
      (η * determinantValue a b V).re ≤ (η * determinantValue a b U).re)
    (hswap : (η * determinantValue a b (rotateRows U i j 0 1)).re =
      (η * determinantValue a b U).re) :
    ∃ V : Matrix ι ι ℂ, IsUnitary V ∧
      (η * determinantValue a b V).re = (η * determinantValue a b U).re ∧
      supportColumns Vᴴ {k} ⊂ supportColumns Uᴴ {k} := by
  obtain ⟨u, hu, hui⟩ := unit_phase_mul_eq_norm (U i k) hi
  obtain ⟨v, hv, hvj⟩ := unit_phase_mul_eq_norm (U j k) hj
  let d (q : ι) : ℂ := if q = i then u else if q = j then v else 1
  have hd (q : ι) : star (d q) * d q = 1 := by
    by_cases hiq : q = i
    · simpa only [d, if_pos hiq] using hu
    · by_cases hjq : q = j
      · simpa only [d, if_neg hiq, if_pos hjq] using hv
      · simp only [d, if_neg hiq, if_neg hjq, star_one, mul_one]
  obtain ⟨c, s, hcs, hz⟩ := exists_unit_circle_annihilator ‖U i k‖ ‖U j k‖
    (norm_ne_zero_iff.mpr hi)
  let W := diagonal d * U
  have hW : IsUnitary W := isUnitary_diagonal_phase_mul hU d hd
  let V := rotateRows W i j c s
  have hVi : V i k = 0 := by
    change rotateRows W i j c s i k = 0
    rw [rotateRows_entry_i _ hij]
    have hWi : W i k = (‖U i k‖ : ℂ) := by
      simpa [W, Matrix.diagonal_mul, d] using hui
    have hWj : W j k = (‖U j k‖ : ℂ) := by
      simpa [W, Matrix.diagonal_mul, d, Ne.symm hij] using hvj
    rw [hWi, hWj]
    exact_mod_cast hz
  have hVq (q : ι) (hqi : q ≠ i) (hqj : q ≠ j) : V q k = U q k := by
    change rotateRows W i j c s q k = _
    rw [rotateRows_entry_other _ hqi hqj]
    simp [W, Matrix.diagonal_mul, d, hqi, hqj]
  refine ⟨V, isUnitary_rotateRows W hW i j hij c s hcs,
    flat_phase_rotateRows_of_support_max a b η U hU hij hmax hswap d hd c s hcs, ?_⟩
  have memSupp (X : Matrix ι ι ℂ) (q : ι) :
      q ∈ supportColumns Xᴴ {k} ↔ X q k ≠ 0 := by
    simp [supportColumns, Matrix.conjTranspose_apply]
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro q hq
    rw [memSupp] at hq ⊢
    have hqi : q ≠ i := by rintro rfl; exact hq hVi
    by_cases hqj : q = j
    · rwa [hqj]
    · rwa [hVq q hqi hqj] at hq
  · intro h
    have him : i ∈ supportColumns Uᴴ {k} := (memSupp U i).mpr hi
    rw [← h, memSupp] at him
    exact him hVi

/-- Among unitary support maximizers one can choose a mixer so that every
signed swap between two nonzero entries of a prescribed column strictly
decreases the support objective. This holds in every finite order. -/
theorem exists_support_max_strict_swaps_in_column
    (a b : ι → ℂ) (η : ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U) (k : ι)
    (hmax : ∀ W : Matrix ι ι ℂ, IsUnitary W →
      (η * determinantValue a b W).re ≤ (η * determinantValue a b U).re) :
    ∃ V : Matrix ι ι ℂ, IsUnitary V ∧
      (η * determinantValue a b V).re = (η * determinantValue a b U).re ∧
      ∀ i j, i ≠ j → V i k ≠ 0 → V j k ≠ 0 →
        (η * determinantValue a b (rotateRows V i j 0 1)).re <
          (η * determinantValue a b V).re := by
  classical
  let ζ := (η * determinantValue a b U).re
  let P (n : ℕ) := ∃ V : Matrix ι ι ℂ, IsUnitary V ∧
    (η * determinantValue a b V).re = ζ ∧ (supportColumns Vᴴ {k}).card = n
  have hp : ∃ n, P n := ⟨_, U, hU, rfl, rfl⟩
  obtain ⟨V, hV, hval, hcard⟩ := Nat.find_spec hp
  refine ⟨V, hV, hval, ?_⟩
  intro i j hij hi hj
  have hVmax (W : Matrix ι ι ℂ) (hW : IsUnitary W) :
      (η * determinantValue a b W).re ≤ (η * determinantValue a b V).re := by
    rw [hval]
    exact hmax W hW
  have hle := hVmax _ (isUnitary_rotateRows V hV i j hij 0 1 (by norm_num))
  by_contra! hge
  obtain ⟨W, hW, hnew, hs⟩ :=
    exists_support_max_with_column_support_ssubset_of_flat_swap a b η V hV
      hij hi hj hVmax (le_antisymm hle hge)
  have hmin : Nat.find hp ≤ (supportColumns Wᴴ {k}).card :=
    Nat.find_min' hp ⟨W, hW, hnew.trans hval, rfl⟩
  have hlt := Finset.card_lt_card hs
  rw [hcard] at hlt
  exact (not_lt_of_ge hmin) hlt

end

end MOC
