import MOC.Reformulations.StationaryFour
import MOC.Reformulations.NativeLinksD
import MOC.SparseRow
import MOC.SpectralPerturbation
import MOC.Variational

/-!
# Symbolic order-four support reduction

The orthogonal replacement can be made inside every determinantal zero face
already attained by the unitary. Together with the order-three argument this
makes the residual support problem smaller, but does not assert that the
remaining support profiles are bounded by the permutation hull.
-/

open BigOperators Matrix

namespace MOC

/-- The real-orthogonal replacement does not reduce the given support value
and preserves *all* vanishing squared minors of the original mixer. -/
theorem exists_four_orthogonal_support_replacement (a b : Fin 4 → ℂ) (η : ℂ)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    ∃ O : Matrix.orthogonalGroup (Fin 4) ℝ,
      let V := Complex.ofRealHom.mapMatrix O.val
      (η * determinantValue a b U).re ≤ (η * determinantValue a b V).re ∧
        ∀ I J : Finset (Fin 4), subsetMinorSq U I J = 0 → subsetMinorSq V I J = 0 := by
  classical
  obtain ⟨κ, _, w, O, hw, hs, hm⟩ := four_minor_mixture U hU
  let V (k : κ) := Complex.ofRealHom.mapMatrix (O k).val
  let score (W : Matrix (Fin 4) (Fin 4) ℂ) : ℝ := (η * determinantValue a b W).re
  have hV (k : κ) : IsUnitary (V k) := isUnitary_ofReal_orthogonal (O k)
  have hdet : determinantValue a b U = ∑ k, w k • determinantValue a b (V k) := by
    have h := Reformulations.CStar.charpoly_eq_sum_of_minor_mixture a b U hU V hV w hm
    apply congrArg (fun p => p.coeff 0) at h
    simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_smul] at h
    have hc (W : Matrix (Fin 4) (Fin 4) ℂ) :
        (diagonal a + W * diagonal b * Wᴴ).charpoly.coeff 0 = determinantValue a b W := by
      rw [determinantValue, Matrix.det_eq_sign_charpoly_coeff]
      norm_num
    simp only [hc] at h
    exact h
  have hscore : score U = ∑ k, w k * score (V k) := by
    simp only [score, hdet, Finset.mul_sum, Complex.re_sum, Complex.real_smul]
    apply Finset.sum_congr rfl
    intro k _
    rw [mul_left_comm, Complex.mul_re]
    simp
  have hex : ∃ k, 0 < w k ∧ score U ≤ score (V k) := by
    by_contra! hn
    have heq : (∑ k, w k * (score U - score (V k))) = 0 := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hs, one_mul, ← hscore, sub_self]
    have hn₀ (k : κ) : 0 ≤ w k * (score U - score (V k)) := by
      by_cases hpos : 0 < w k
      · exact mul_nonneg (hw k) (sub_nonneg.mpr (hn k hpos).le)
      · rw [le_antisymm (le_of_not_gt hpos) (hw k), zero_mul]
    have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hn₀ k)).mp heq
    have hw₀ (k : κ) : w k = 0 := by
      by_contra hk
      have hpos := lt_of_le_of_ne (hw k) (Ne.symm hk)
      exact (mul_pos hpos (sub_pos.mpr (hn k hpos))).ne' (hall k (Finset.mem_univ k))
    simp [hw₀] at hs
  obtain ⟨k, hk, hsk⟩ := hex
  refine ⟨O k, hsk, fun I J hzero => ?_⟩
  have hz : (∑ l, w l * subsetMinorSq (V l) I J) = 0 := (hm I J).symm.trans hzero
  have hkzero := (Finset.sum_eq_zero_iff_of_nonneg
    (fun l _ => mul_nonneg (hw l) (subsetMinorSq_nonneg (V l) I J))).mp hz k (Finset.mem_univ k)
  exact (mul_eq_zero.mp hkzero).resolve_left hk.ne'

/-- A global support maximizer can be replaced by a real orthogonal global
maximizer in the same prescribed minor-zero face. -/
theorem exists_four_orthogonal_support_maximizer_with_zeros (a b : Fin 4 → ℂ) (η : ℂ)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U)
    (hmax : ∀ W : Matrix (Fin 4) (Fin 4) ℂ, IsUnitary W →
      (η * determinantValue a b W).re ≤ (η * determinantValue a b U).re) :
    ∃ O : Matrix.orthogonalGroup (Fin 4) ℝ,
      let V := Complex.ofRealHom.mapMatrix O.val
      (η * determinantValue a b V).re = (η * determinantValue a b U).re ∧
        (∀ W : Matrix (Fin 4) (Fin 4) ℂ, IsUnitary W →
          (η * determinantValue a b W).re ≤ (η * determinantValue a b V).re) ∧
        (∀ I J : Finset (Fin 4), subsetMinorSq U I J = 0 → subsetMinorSq V I J = 0) := by
  obtain ⟨O, hge, hz⟩ := exists_four_orthogonal_support_replacement a b η U hU
  exact ⟨O, le_antisymm (hmax _ (isUnitary_ofReal_orthogonal O)) hge,
    fun W hW => (hmax W hW).trans hge, hz⟩

/-- The independent order-four residual: regular spectra and maximizers with
all row and column degrees at least three. This is a necessary and sufficient
support problem, not a finite sign-chamber census. -/
theorem conjecture_four_iff_regular_orthogonal_support_maxima :
    Conjecture (Fin 4) ↔
      ∀ (a b : Fin 4 → ℂ) (η : ℂ) (O : Matrix.orthogonalGroup (Fin 4) ℝ),
        let V := Complex.ofRealHom.mapMatrix O.val
        (∀ i j, a i + b j ≠ 0) → Function.Injective (matchingProduct a b) →
        (∀ i, 3 ≤ (supportColumns V {i}).card) →
        (∀ j, 3 ≤ (supportColumns Vᴴ {j}).card) →
        (∀ W : Matrix (Fin 4) (Fin 4) ℂ, IsUnitary W →
          (η * determinantValue a b W).re ≤ (η * determinantValue a b V).re) →
        ∃ p : Equiv.Perm (Fin 4),
          (η * determinantValue a b V).re ≤ (η * matchingProduct a b p).re := by
  constructor
  · intro h a b η O V hn hi hr hc hm
    exact (holds_iff_directional _ _ _).mp (h a b _ (isUnitary_ofReal_orthogonal O)) η
  · intro h
    apply conjecture_iff_regular_matching_products.mpr
    intro a b U hU hn hi
    apply (holds_iff_directional _ _ _).mpr
    intro η
    obtain ⟨W, hW, hmax⟩ := exists_support_maximizer a b η
    obtain ⟨O, hv, hmaxV, _⟩ := exists_four_orthogonal_support_maximizer_with_zeros a b η W hW hmax
    let V := Complex.ofRealHom.mapMatrix O.val
    have hV : IsUnitary V := isUnitary_ofReal_orthogonal O
    have hvle : (η * determinantValue a b U).re ≤ (η * determinantValue a b V).re := hmaxV _ hU
    have hsmall : Conjecture (Fin 3) := conjecture_le_three (by omega)
    have hgoal : ∃ p : Equiv.Perm (Fin 4),
        (η * determinantValue a b V).re ≤ (η * matchingProduct a b p).re := by
      by_cases hr : ∀ i, 3 ≤ (supportColumns V {i}).card
      · by_cases hc : ∀ j, 3 ≤ (supportColumns Vᴴ {j}).card
        · exact h a b η O hn hi hr hc hmaxV
        · push_neg at hc
          obtain ⟨j, hj⟩ := hc
          exact (holds_iff_directional _ _ _).mp
            (holds_of_column_degree_le_two hsmall a b hV j (by omega)) η
      · push_neg at hr
        obtain ⟨i, hi'⟩ := hr
        exact (holds_iff_directional _ _ _).mp
          (holds_of_row_degree_le_two hsmall a b hV i (by omega)) η
    obtain ⟨p, hp⟩ := hgoal
    exact ⟨p, hvle.trans hp⟩


/-- At an invertible order-four global support maximum the explicit adjugate
stationarity equations in real skew directions are necessary. No sign
chamber or contact-count assumption is used. -/
theorem four_stationary_equations_of_support_maximum (a b : Fin 4 → ℂ) (η : ℂ)
    (O : Matrix.orthogonalGroup (Fin 4) ℝ)
    (hd : determinantValue a b (Complex.ofRealHom.mapMatrix O.val) ≠ 0)
    (hmax : ∀ W : Matrix (Fin 4) (Fin 4) ℂ, IsUnitary W →
      (η * determinantValue a b W).re ≤
        (η * determinantValue a b (Complex.ofRealHom.mapMatrix O.val)).re) :
    Reformulations.SatisfiesStationaryEquations a b O η := by
  let V := Complex.ofRealHom.mapMatrix O.val
  let A := diagonal a
  let B := V * diagonal b * Vᴴ
  let C := A + B
  have hV := isUnitary_ofReal_orthogonal O
  change C.det ≠ 0 at hd
  have hmax' (R : Matrix (Fin 4) (Fin 4) ℂ) (hR : IsUnitary R) :
      (η * (A + R * B * Rᴴ).det).re ≤ (η * C.det).re := by
    have hR' : IsUnitary Rᴴ := by
      simpa only [IsUnitary, Matrix.conjTranspose_conjTranspose] using And.intro hR.2 hR.1
    have hRV : IsUnitary (R * V) := by
      simpa only [Matrix.conjTranspose_conjTranspose] using relative_unitary Rᴴ V hR' hV
    simpa only [determinantValue, A, B, C, Matrix.conjTranspose_mul, Matrix.mul_assoc] using
      hmax (R * V) hRV
  have hherm := support_maximum_inverse_commutator A B η hd hmax'
  intro X hX
  let K := Complex.ofRealHom.mapMatrix X
  have hK : Kᴴ = -K := by
    ext i j
    have hx := congrArg (fun m : Matrix (Fin 4) (Fin 4) ℝ => m i j) hX
    change X j i = -X i j at hx
    simp [K, Matrix.conjTranspose_apply, hx]
  have htrK : K.trace = 0 := by
    unfold Matrix.trace
    apply Finset.sum_eq_zero
    intro i _
    have hx := congrArg (fun m : Matrix (Fin 4) (Fin 4) ℝ => m i i) hX
    change X i i = -X i i at hx
    have hz : X i i = 0 := by linarith
    simp [K, hz]
  let P : Matrix (Fin 4) (Fin 4) ℂ → Matrix (Fin 4) (Fin 4) ℂ :=
    fun W => Matrix.of fun i j => (a i + b j) * W i j
  have hP (W : Matrix (Fin 4) (Fin 4) ℂ) : P W = A * W + W * diagonal b := by
    ext i j
    simp only [P, Matrix.of_apply, Matrix.add_apply, A, Matrix.diagonal_mul, Matrix.mul_diagonal]
    ring
  have hBV : B * V = V * diagonal b := by
    dsimp only [B]
    rw [Matrix.mul_assoc _ _ V]
    exact congrArg (fun T => V * diagonal b * T) hV.2 |>.trans (Matrix.mul_one _)
  have hPV : P V = C * V := by
    rw [hP]
    change _ = (A + B) * V
    rw [Matrix.add_mul, hBV]
  have hPX : P (K * V) = (K * B - B * K) * V + C * (K * V) := by
    rw [hP, Matrix.sub_mul]
    dsimp only [C]
    rw [Matrix.add_mul, Matrix.mul_assoc B K, Matrix.mul_assoc K B V, hBV, ← Matrix.mul_assoc K V]
    abel
  have htrace : ((P V).adjugate * P (K * V)).trace =
      V.det * (C.adjugate * (K * B - B * K)).trace := by
    rw [hPV, hPX, Matrix.adjugate_mul_distrib, Matrix.mul_add, Matrix.trace_add]
    have hcancel (D : Matrix (Fin 4) (Fin 4) ℂ) :
        (V.adjugate * D * V).trace = V.det * D.trace := by
      rw [Matrix.trace_mul_cycle, Matrix.mul_adjugate,
        Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, smul_eq_mul]
    rw [← Matrix.mul_assoc, Matrix.mul_assoc V.adjugate C.adjugate (K * B - B * K), hcancel]
    have hzero : (V.adjugate * C.adjugate * (C * (K * V))).trace = 0 := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc C.adjugate C, Matrix.adjugate_mul, Matrix.smul_mul,
        Matrix.one_mul, Matrix.mul_smul, Matrix.trace_smul, ← Matrix.mul_assoc, hcancel, htrK]
      simp
    rw [hzero, add_zero]
  change (η * ((P V).adjugate * P (Complex.ofRealHom.mapMatrix (X * O.val))).trace / V.det).re = 0
  rw [Complex.ofRealHom.mapMatrix.map_mul, htrace]
  rw [mul_left_comm η V.det, mul_comm V.det, mul_div_cancel_right₀ _ (det_ne_zero_of_unitary hV)]
  have hAdj : C.adjugate = C.det • C⁻¹ := by
    rw [Matrix.inv_def, smul_smul]
    simp [hd]
  rw [hAdj, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, ← mul_assoc]
  let D := (η * C.det) • (B * C⁻¹ - C⁻¹ * B)
  have hD : Dᴴ = D := hherm
  have hdt : (η * C.det) * (C⁻¹ * (K * B - B * K)).trace = (D * K).trace := by
    dsimp only [D]
    rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    congr 1
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub]
    rw [Matrix.trace_mul_cycle' C⁻¹ K B, Matrix.mul_assoc B C⁻¹ K, Matrix.mul_assoc C⁻¹ B K]
  rw [hdt]
  have ht := congrArg Complex.re (Matrix.trace_conjTranspose (D * K))
  rw [Matrix.conjTranspose_mul, hD, hK, Matrix.neg_mul, Matrix.trace_neg, Matrix.trace_mul_comm,
    Complex.star_def, Complex.conj_re, Complex.neg_re] at ht
  linarith


/-- A strict order-four violation is equivalent to a regular stationary
orthogonal violation at a global support maximum. The dense sign chamber
and the seven-contact constraint are not needed for this exact reduction,
and are not shown to capture all counterexamples. -/
theorem not_conjecture_four_iff_regular_stationary_orthogonal_witness :
    (¬ Conjecture (Fin 4)) ↔
      ∃ (a b : Fin 4 → ℂ) (η : ℂ) (O : Matrix.orthogonalGroup (Fin 4) ℝ),
        let V := Complex.ofRealHom.mapMatrix O.val
        (∀ i j, a i + b j ≠ 0) ∧ Function.Injective (matchingProduct a b) ∧
        (∀ i, 3 ≤ (supportColumns V {i}).card) ∧
        (∀ j, 3 ≤ (supportColumns Vᴴ {j}).card) ∧
        (∀ W : Matrix (Fin 4) (Fin 4) ℂ, IsUnitary W →
          (η * determinantValue a b W).re ≤ (η * determinantValue a b V).re) ∧
        Reformulations.SatisfiesStationaryEquations a b O η ∧
        ∀ p : Equiv.Perm (Fin 4),
          (η * matchingProduct a b p).re < (η * determinantValue a b V).re := by
  classical
  constructor
  · intro h
    have hn := (not_congr conjecture_four_iff_regular_orthogonal_support_maxima).mp h
    dsimp only at hn
    push_neg at hn
    obtain ⟨a, b, η, O, hnonzero, hinj, hrow, hcol, hmax, hgap⟩ := hn
    have hd : determinantValue a b (Complex.ofRealHom.mapMatrix O.val) ≠ 0 := by
      intro hz
      have hh := holds_of_singular a b (isUnitary_ofReal_orthogonal O) hz
      obtain ⟨p, hp⟩ := (holds_iff_directional _ _ _).mp hh η
      exact (not_lt_of_ge hp) (hgap p)
    exact ⟨a, b, η, O, hnonzero, hinj, hrow, hcol, hmax,
      four_stationary_equations_of_support_maximum a b η O hd hmax, hgap⟩
  · rintro ⟨a, b, η, O, _, _, _, _, _, _, hgap⟩ h
    obtain ⟨p, hp⟩ := (holds_iff_directional _ _ _).mp
      (h a b _ (isUnitary_ofReal_orthogonal O)) η
    exact (not_lt_of_ge hp) (hgap p)

end MOC
