import MOC.FourEffectDecomposition
import Mathlib.Analysis.Convex.Extreme

/-! Extreme points of the full set of real three-effect tuples. -/

open BigOperators Matrix

namespace MOC

noncomputable section

private abbrev Effect := Matrix (Fin 3) (Fin 3) ℝ

/-- The tuples of three positive semidefinite real effects of trace one
whose sum is the identity. The effects can have full rank. -/
def threeEffectSet : Set (Fin 3 → Matrix (Fin 3) (Fin 3) ℝ) :=
  {E | (∀ i, (E i).PosSemidef) ∧ (∀ i, (E i).trace = 1) ∧ ∑ i, E i = 1}

private theorem real_psd_smul (c : ℝ) (hc : 0 ≤ c) {A : Effect} (hA : A.PosSemidef) :
    (c • A).PosSemidef := by
  constructor
  · change (c • A)ᴴ = c • A
    rw [Matrix.conjTranspose_smul, star_trivial, hA.isHermitian.eq]
  · intro x
    rw [Matrix.smul_mulVec_assoc, dotProduct_smul, smul_eq_mul]
    exact mul_nonneg hc (hA.2 x)

/-- Real convex combinations preserve all constraints on the three effects. -/
theorem convex_threeEffectSet : Convex ℝ threeEffectSet := by
  intro E hE F hF a b ha hb hab
  obtain ⟨hEpos, hEtrace, hEsum⟩ := hE
  obtain ⟨hFpos, hFtrace, hFsum⟩ := hF
  refine ⟨fun i => (real_psd_smul a ha (hEpos i)).add (real_psd_smul b hb (hFpos i)), ?_, ?_⟩
  · intro i
    simp only [Pi.add_apply, Pi.smul_apply, Matrix.trace_add, Matrix.trace_smul, hEtrace,
      hFtrace, smul_eq_mul, mul_one, hab]
  · simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_add_distrib, ← Finset.smul_sum, hEsum,
      hFsum, ← add_smul, hab, one_smul]

private def basisDiagonal (V : Effect) (d : Fin 3 → ℝ) : Effect := V * diagonal d * Vᴴ

private theorem basisDiagonal_add_smul (V : Effect) (d e : Fin 3 → ℝ) (z : ℝ) :
    basisDiagonal V d + z • basisDiagonal V e = basisDiagonal V (d + z • e) := by
  have hd : diagonal (d + z • e) = diagonal d + z • diagonal e := by
    rw [← Matrix.diagonal_smul]
    exact (Matrix.diagonal_add d (z • e)).symm
  simp only [basisDiagonal, hd, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]

private theorem basisDiagonal_constant (V : Effect) (hV : V * Vᴴ = 1) (t : ℝ) :
    basisDiagonal V (fun _ => t) = t • (1 : Effect) := by
  have he : (fun _ : Fin 3 => t) = t • (1 : Fin 3 → ℝ) := by
    funext j
    simp
  rw [he, basisDiagonal, Matrix.diagonal_smul, Matrix.diagonal_one, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, hV]

private theorem basisDiagonal_trace (V : Effect) (hV : Vᴴ * V = 1) (d : Fin 3 → ℝ) :
    (basisDiagonal V d).trace = ∑ j, d j := by
  rw [basisDiagonal, Matrix.trace_mul_cycle, hV, Matrix.one_mul, Matrix.trace_diagonal]

private theorem basisDiagonal_pos (V : Effect) {d : Fin 3 → ℝ} (hd : ∀ j, 0 ≤ d j) :
    (basisDiagonal V d).PosSemidef :=
  (Matrix.posSemidef_diagonal_iff.mpr hd).mul_mul_conjTranspose_same V

private theorem spectral_shape (A : Effect) (hA : A.PosSemidef) :
    A = basisDiagonal hA.isHermitian.eigenvectorUnitary.val hA.isHermitian.eigenvalues := by
  simpa only [basisDiagonal, RCLike.ofReal_real_eq_id] using hA.isHermitian.spectral_theorem

private theorem full_rank_eigenvalue_pos (A : Effect) (hA : A.PosSemidef) (hr : 3 ≤ A.rank)
    (j : Fin 3) : 0 < hA.isHermitian.eigenvalues j := by
  classical
  apply lt_of_le_of_ne (hA.eigenvalues_nonneg j)
  intro hz
  have hc : Fintype.card {i // hA.isHermitian.eigenvalues i ≠ 0} < Fintype.card (Fin 3) :=
    Fintype.card_subtype_lt (fun hn : hA.isHermitian.eigenvalues j ≠ 0 => hn hz.symm)
  rw [← hA.isHermitian.rank_eq_card_non_zero_eigs, Fintype.card_fin] at hc
  exact (not_lt_of_ge hr) hc

private theorem rank_pos_of_trace_one (A : Effect) (hA : A.PosSemidef)
    (ht : A.trace = 1) : 0 < A.rank := by
  classical
  by_contra! h
  have hc : Fintype.card {j // hA.isHermitian.eigenvalues j ≠ 0} = 0 := by
    rw [← hA.isHermitian.rank_eq_card_non_zero_eigs]
    omega
  have hempty := Fintype.card_eq_zero_iff.mp hc
  have hz (j : Fin 3) : hA.isHermitian.eigenvalues j = 0 := by
    by_contra hj
    exact hempty.false ⟨j, hj⟩
  rw [spectral_shape A hA, basisDiagonal_trace _
    (Matrix.mem_unitaryGroup_iff'.mp hA.isHermitian.eigenvectorUnitary.property)] at ht
  simp only [hz, Finset.sum_const_zero, zero_ne_one] at ht

private theorem trace_free_transfer (A B : Effect) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hra : 3 ≤ A.rank) (hrb : 1 < B.rank) :
    ∃ (D : Effect) (ε : ℝ), D ≠ 0 ∧ D.trace = 0 ∧ 0 < ε ∧
      ∀ z : ℝ, |z| ≤ ε → (A + z • D).PosSemidef ∧ (B + z • D).PosSemidef := by
  classical
  let a := hA.isHermitian.eigenvalues
  let b := hB.isHermitian.eigenvalues
  let P := hA.isHermitian.eigenvectorUnitary.val
  let Q := hB.isHermitian.eigenvectorUnitary.val
  have hP : P * Pᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hA.isHermitian.eigenvectorUnitary.property
  have hQ : Q * Qᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hB.isHermitian.eigenvectorUnitary.property
  have hQ' : Qᴴ * Q = 1 := Matrix.mem_unitaryGroup_iff'.mp hB.isHermitian.eigenvectorUnitary.property
  have hAc : A = basisDiagonal P a := spectral_shape A hA
  have hBc : B = basisDiagonal Q b := spectral_shape B hB
  have ha (j : Fin 3) : 0 < a j := full_rank_eigenvalue_pos A hA hra j
  let δ := min (a 0) (min (a 1) (a 2))
  have hδ : 0 < δ := lt_min (ha 0) (lt_min (ha 1) (ha 2))
  have hδa (j : Fin 3) : δ ≤ a j := by
    fin_cases j
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  have hcard : 1 < Fintype.card {i // b i ≠ 0} := by
    change 1 < Fintype.card {i // hB.isHermitian.eigenvalues i ≠ 0}
    rwa [← hB.isHermitian.rank_eq_card_non_zero_eigs]
  letI : Nontrivial {i // b i ≠ 0} := Fintype.one_lt_card_iff_nontrivial.mp hcard
  obtain ⟨p, q, hpq⟩ := exists_pair_ne {i // b i ≠ 0}
  have hpq' : p.val ≠ q.val := fun he => hpq (Subtype.ext he)
  have hp : 0 < b p.val := lt_of_le_of_ne' (hB.eigenvalues_nonneg _) p.property
  have hq : 0 < b q.val := lt_of_le_of_ne' (hB.eigenvalues_nonneg _) q.property
  let ε := min δ (min (b p.val) (b q.val))
  have hε : 0 < ε := lt_min hδ (lt_min hp hq)
  have hεa (i : Fin 3) : ε ≤ a i := (min_le_left _ _).trans (hδa i)
  have hεp : ε ≤ b p.val := (min_le_right _ _).trans (min_le_left _ _)
  have hεq : ε ≤ b q.val := (min_le_right _ _).trans (min_le_right _ _)
  let d : Fin 3 → ℝ := Pi.single p.val 1 - Pi.single q.val 1
  have hdp : d p.val = 1 := by simp [d, Pi.single_apply, hpq'.symm, hpq']
  have hdq : d q.val = -1 := by simp [d, Pi.single_apply, hpq'.symm, hpq']
  have hd0 (k : Fin 3) (hkp : k ≠ p.val) (hkq : k ≠ q.val) : d k = 0 := by
    simp [d, Pi.single_apply, hkp, hkq, Ne.symm hkp, Ne.symm hkq]
  let D := basisDiagonal Q d
  have hD : D ≠ 0 := by
    intro he
    have hback : Qᴴ * D * Q = diagonal d := by
      calc
        _ = (Qᴴ * Q) * diagonal d * (Qᴴ * Q) := by simp only [D, basisDiagonal, Matrix.mul_assoc]
        _ = _ := by rw [hQ', Matrix.one_mul, Matrix.mul_one]
    rw [he, Matrix.mul_zero, Matrix.zero_mul] at hback
    have hz := congrArg (fun M : Effect => M p.val p.val) hback
    simp only [Matrix.zero_apply, Matrix.diagonal_apply_eq, hdp, zero_ne_one] at hz
  have htD : D.trace = 0 := by
    rw [show D = basisDiagonal Q d from rfl, basisDiagonal_trace Q hQ']
    simp [d, Pi.sub_apply, Finset.sum_sub_distrib, Finset.sum_pi_single']
  have hbase : (A + (-ε) • (1 : Effect)).PosSemidef := by
    have hPI : basisDiagonal P (fun _ => 1) = (1 : Effect) := by
      simpa only [one_smul] using basisDiagonal_constant P hP 1
    rw [hAc, ← hPI, basisDiagonal_add_smul]
    apply basisDiagonal_pos
    intro i
    change 0 ≤ a i + (-ε) * 1
    linarith only [hεa i]
  refine ⟨D, ε, hD, htD, hε, ?_⟩
  intro z hz
  obtain ⟨hzlow, hzhigh⟩ := abs_le.mp hz
  have hshift (t : Fin 3 → ℝ) (ht : ∀ k, 0 ≤ t k) (htp : ε ≤ t p.val)
      (htq : ε ≤ t q.val) : (basisDiagonal Q t + z • D).PosSemidef := by
    rw [show D = basisDiagonal Q d from rfl, basisDiagonal_add_smul]
    apply basisDiagonal_pos
    intro k
    change 0 ≤ t k + z * d k
    by_cases hkp : k = p.val
    · subst k
      rw [hdp, mul_one]
      linarith only [hzlow, htp]
    by_cases hkq : k = q.val
    · subst k
      rw [hdq, mul_neg_one]
      linarith only [hzhigh, htq]
    rw [hd0 k hkp hkq, mul_zero, add_zero]
    exact ht k
  have hδD : (ε • (1 : Effect) + z • D).PosSemidef := by
    rw [← basisDiagonal_constant Q hQ ε]
    exact hshift (fun _ => ε) (fun _ => hε.le) le_rfl le_rfl
  constructor
  · have hs := hbase.add hδD
    have he : (A + (-ε) • (1 : Effect)) + (ε • (1 : Effect) + z • D) = A + z • D := by
      rw [neg_smul]
      abel
    rwa [he] at hs
  · rw [hBc]
    exact hshift b (hB.eigenvalues_nonneg) hεp hεq

private theorem rank_gt_one_of_other_full_rank (E : Fin 3 → Effect) (hE : E ∈ threeEffectSet)
    (i : Fin 3) (hi : 3 ≤ (E i).rank) : ∃ j, j ≠ i ∧ 1 < (E j).rank := by
  obtain ⟨hpos, htrace, hsum⟩ := hE
  let e : Equiv.Perm (Fin 3) := Equiv.swap 0 i
  have he : e 0 = i := by simp [e]
  let j := e 1
  have hji : j ≠ i := by
    rw [← he]
    exact e.injective.ne (by decide)
  refine ⟨j, hji, ?_⟩
  by_contra! hj
  have h1 : (E j).rank = 1 := by
    have h := rank_pos_of_trace_one _ (hpos j) (htrace j)
    omega
  have hsum' : E j + E i + E (e 2) = 1 := by
    have h := (Equiv.sum_comp e E).trans hsum
    rw [Fin.sum_univ_three, he] at h
    simpa only [j, add_comm (E i) (E (e 1))] using h
  have hproj : E j * E j = E j := effect_rank_one_mul_self _ (hpos j) h1 (htrace j)
  have hkill : E i * E j = 0 :=
    (effects_mul_projection_eq_zero _ _ _ hproj (hpos i) (hpos (e 2)) hsum').1
  have hdet : (E i).det ≠ 0 := by
    rw [(hpos i).isHermitian.det_eq_prod_eigenvalues]
    apply Finset.prod_ne_zero_iff.mpr
    intro k _
    simpa only [RCLike.ofReal_real_eq_id] using (full_rank_eigenvalue_pos _ (hpos i) hi k).ne'
  have hz : E j = 0 := by
    calc
      E j = (E i)⁻¹ * (E i * E j) := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mul]
      _ = 0 := by rw [hkill, Matrix.mul_zero]
  have ht := htrace j
  rw [hz, Matrix.trace_zero] at ht
  exact zero_ne_one ht

private theorem not_extreme_of_full_rank (E : Fin 3 → Effect) (hE : E ∈ threeEffectSet)
    (i : Fin 3) (hi : 3 ≤ (E i).rank) : E ∉ threeEffectSet.extremePoints ℝ := by
  classical
  obtain ⟨j, hji, hj⟩ := rank_gt_one_of_other_full_rank E hE i hi
  obtain ⟨hpos, htrace, hsum⟩ := hE
  obtain ⟨D, ε, hD, htD, hε, htransfer⟩ := trace_free_transfer _ _ (hpos i) (hpos j) hi hj
  let W : Fin 3 → Effect := Pi.single i D - Pi.single j D
  let F (z : ℝ) := E + z • W
  have hWi : W i = D := by simp [W, Pi.single_apply, hji, hji.symm]
  have hWj : W j = -D := by simp [W, Pi.single_apply, hji, hji.symm]
  have hW0 (k : Fin 3) (hki : k ≠ i) (hkj : k ≠ j) : W k = 0 := by
    simp [W, Pi.single_apply, hki, hkj, Ne.symm hki, Ne.symm hkj]
  have htW (k : Fin 3) : (W k).trace = 0 := by
    by_cases hki : k = i
    · simpa only [hki, hWi] using htD
    by_cases hkj : k = j
    · simp only [hkj, hWj, Matrix.trace_neg, htD, neg_zero]
    · rw [hW0 k hki hkj, Matrix.trace_zero]
  have hsumW : ∑ k, W k = 0 := by
    simp [W, Pi.sub_apply, Finset.sum_sub_distrib, Finset.sum_pi_single']
  have hF (z : ℝ) (hz : |z| ≤ ε) : F z ∈ threeEffectSet := by
    refine ⟨?_, ?_, ?_⟩
    · intro k
      change (E k + z • W k).PosSemidef
      by_cases hki : k = i
      · rw [hki, hWi]
        exact (htransfer z hz).1
      by_cases hkj : k = j
      · rw [hkj, hWj, smul_neg, ← neg_smul]
        exact (htransfer (-z) (by simpa only [abs_neg] using hz)).2
      · rw [hW0 k hki hkj, smul_zero, add_zero]
        exact hpos k
    · intro k
      simp only [F, Pi.add_apply, Pi.smul_apply, Matrix.trace_add, Matrix.trace_smul, htrace,
        htW, smul_zero, add_zero]
    · simp only [F, Pi.add_apply, Pi.smul_apply, Finset.sum_add_distrib, ← Finset.smul_sum,
        hsum, hsumW, smul_zero, add_zero]
  have hmid : (1 / 2 : ℝ) • F ε + (1 / 2 : ℝ) • F (-ε) = E := by
    funext k
    ext r c
    simp only [F, Pi.add_apply, Pi.smul_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have hne : F ε ≠ E := by
    intro he
    have hh : E i + ε • D = E i := by simpa only [F, Pi.add_apply, Pi.smul_apply, hWi]
      using congrFun he i
    have hz : ε • D = 0 := add_left_cancel (hh.trans (add_zero _).symm)
    exact (smul_ne_zero hε.ne' hD) hz
  intro he
  have hpAbs : |ε| ≤ ε := by simpa only [abs_of_pos hε] using (le_rfl : ε ≤ ε)
  have hmAbs : |-ε| ≤ ε := by simpa only [abs_neg] using hpAbs
  exact hne ((mem_extremePoints_iff_left.mp he).2 (F ε) (hF ε hpAbs) (F (-ε)) (hF (-ε) hmAbs)
    ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, hmid⟩)

private theorem basis_effect_eq_diagonal (O : Matrix.orthogonalGroup (Fin 3) ℝ) (i : Fin 3) :
    orthogonalBasisEffects O i = basisDiagonal O.val (Pi.single i 1) := by
  ext j k
  change O.val j i * O.val k i = _
  rw [basisDiagonal, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, star_trivial]
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _)
    (fun l _ hl => by simp [Pi.single_eq_of_ne hl])]
  simp

private theorem basis_effect_mem (O : Matrix.orthogonalGroup (Fin 3) ℝ) :
    orthogonalBasisEffects O ∈ threeEffectSet := by
  have hO : O.val * O.valᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp O.property
  have hO' : O.valᴴ * O.val = 1 := Matrix.mem_unitaryGroup_iff'.mp O.property
  refine ⟨?_, ?_, ?_⟩
  · intro i
    rw [basis_effect_eq_diagonal]
    exact basisDiagonal_pos _ (fun j => by by_cases h : j = i <;> simp [Pi.single_apply, h, eq_comm])
  · intro i
    rw [basis_effect_eq_diagonal, basisDiagonal_trace _ hO']
    simp only [Finset.sum_pi_single']
  · have hd : (∑ i : Fin 3, diagonal (Pi.single i (1 : ℝ))) = (1 : Effect) := by
      ext j k
      by_cases h : j = k
      · subst k
        simp only [Matrix.sum_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
        simp [Pi.single_apply, eq_comm]
      · simp [Matrix.sum_apply, Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
    simp only [basis_effect_eq_diagonal, basisDiagonal, ← Matrix.sum_mul, ← Matrix.mul_sum,
      hd, Matrix.mul_one, hO]

private theorem left_eq_diagonal_of_psd_mix (A B : Effect) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (ht : A.trace = 1) (i : Fin 3) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (he : a • A + b • B = diagonal (Pi.single i 1)) : A = diagonal (Pi.single i 1) := by
  have hzero (j : Fin 3) (hji : j ≠ i) : A j j = 0 := by
    have hAj : 0 ≤ A j j := by
      simpa only [← Pi.single_star, star_one, Matrix.mulVec_single_one, single_dotProduct, one_mul]
        using hA.2 (Pi.single j 1)
    have hBj : 0 ≤ B j j := by
      simpa only [← Pi.single_star, star_one, Matrix.mulVec_single_one, single_dotProduct, one_mul]
        using hB.2 (Pi.single j 1)
    have he' := congrArg (fun M : Effect => M j j) he
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_apply_eq,
      Pi.single_eq_of_ne hji] at he'
    exact (mul_eq_zero.mp (le_antisymm (by linarith only [he', mul_nonneg hb.le hBj])
      (mul_nonneg ha.le hAj))).resolve_left ha.ne'
  have hcolumn (j : Fin 3) (hji : j ≠ i) (k : Fin 3) : A k j = 0 := by
    have hvec : A *ᵥ (Pi.single j 1 : Fin 3 → ℝ) = 0 := by
      apply (hA.dotProduct_mulVec_zero_iff _).mp
      simpa only [← Pi.single_star, star_one, Matrix.mulVec_single_one, single_dotProduct, one_mul]
        using hzero j hji
    simpa only [Matrix.mulVec_single_one, Matrix.transpose_apply, Pi.zero_apply] using congrFun hvec k
  have hii : A i i = 1 := by
    change (∑ j, A j j) = 1 at ht
    rwa [Finset.sum_eq_single_of_mem i (Finset.mem_univ _) (fun j _ hj => hzero j hj)] at ht
  ext j k
  by_cases hki : k = i
  · subst k
    by_cases hji : j = i
    · subst j
      simpa using hii
    · have he' := hA.isHermitian.apply j i
      rw [hcolumn j hji i, star_zero] at he'
      rw [← he', Matrix.diagonal_apply_ne _ hji]
  · rw [hcolumn k hki j]
    by_cases hjk : j = k
    · subst j
      simp only [Matrix.diagonal_apply_eq, Pi.single_eq_of_ne hki]
    · rw [Matrix.diagonal_apply_ne _ hjk]

private theorem basis_effect_extreme (O : Matrix.orthogonalGroup (Fin 3) ℝ) :
    orthogonalBasisEffects O ∈ threeEffectSet.extremePoints ℝ := by
  apply mem_extremePoints_iff_left.mpr
  refine ⟨basis_effect_mem O, ?_⟩
  rintro E ⟨hEpos, hEtrace, _⟩ F ⟨hFpos, _, _⟩ ⟨a, b, ha, hb, _, he⟩
  let V := O.val
  have hV : V * Vᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp O.property
  have hV' : Vᴴ * V = 1 := Matrix.mem_unitaryGroup_iff'.mp O.property
  let T (D : Effect) := Vᴴ * D * V
  have hback (D : Effect) : V * T D * Vᴴ = D := by
    calc
      _ = (V * Vᴴ) * D * (V * Vᴴ) := by simp only [T, Matrix.mul_assoc]
      _ = _ := by rw [hV, Matrix.one_mul, Matrix.mul_one]
  have hTb (i : Fin 3) : T (orthogonalBasisEffects O i) = diagonal (Pi.single i 1) := by
    rw [basis_effect_eq_diagonal]
    calc
      _ = (Vᴴ * V) * diagonal (Pi.single i 1) * (Vᴴ * V) := by
        simp only [T, basisDiagonal, V, Matrix.mul_assoc]
      _ = _ := by rw [hV', Matrix.one_mul, Matrix.mul_one]
  funext i
  have hm : a • T (E i) + b • T (F i) = diagonal (Pi.single i 1) := by
    have hc := congrArg T (congrFun he i)
    rw [hTb] at hc
    simpa only [T, Pi.add_apply, Pi.smul_apply, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_smul, Matrix.smul_mul] using hc
  have ht : (T (E i)).trace = 1 := by
    rw [T, Matrix.trace_mul_cycle, hV, Matrix.one_mul, hEtrace]
  have h := left_eq_diagonal_of_psd_mix _ _ ((hEpos i).conjTranspose_mul_mul_same V)
    ((hFpos i).conjTranspose_mul_mul_same V) ht i a b ha hb hm
  rw [← hTb] at h
  exact (hback (E i)).symm.trans
    ((congrArg (fun D : Effect => V * D * Vᴴ) h).trans (hback (orthogonalBasisEffects O i)))

/-- A tuple is extreme in the full trace-one effect set exactly when its
three effects are the projections onto an orthonormal real basis. -/
theorem threeEffectSet_extremePoints :
    threeEffectSet.extremePoints ℝ = Set.range orthogonalBasisEffects := by
  apply Set.Subset.antisymm
  · intro E hE
    obtain ⟨hmem, hext⟩ := mem_extremePoints_iff_left.mp hE
    have hr (i : Fin 3) : (E i).rank ≤ 2 := by
      by_contra! h
      exact not_extreme_of_full_rank E hmem i (by omega) hE
    obtain ⟨hpos, htrace, hsum⟩ := hmem
    obtain ⟨P, Q, t, ht₀, ht₁, ht⟩ := effects_two_bases_of_rank_le_two E hpos htrace hsum hr
    by_cases hzero : t = 0
    · refine ⟨Q, ?_⟩
      symm
      simpa only [hzero, zero_smul, sub_zero, one_smul, zero_add] using ht
    by_cases hone : t = 1
    · refine ⟨P, ?_⟩
      symm
      simpa only [hone, one_smul, sub_self, zero_smul, add_zero] using ht
    have hopen : E ∈ openSegment ℝ (orthogonalBasisEffects P) (orthogonalBasisEffects Q) :=
      ⟨t, 1 - t, lt_of_le_of_ne' ht₀ hzero, sub_pos.mpr (lt_of_le_of_ne ht₁ hone), by ring, ht.symm⟩
    exact ⟨P, hext _ (basis_effect_mem P) _ (basis_effect_mem Q) hopen⟩
  · rintro _ ⟨O, rfl⟩
    exact basis_effect_extreme O

end

end MOC
