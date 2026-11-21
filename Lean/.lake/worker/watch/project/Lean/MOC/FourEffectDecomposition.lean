import MOC.FourRealification
import Mathlib.Data.Matrix.Notation

/-! Decomposition of real three-effect tuples into orthonormal bases. -/

open BigOperators Matrix

namespace MOC

noncomputable section

/-- The three rank-one orthogonal projections onto the columns of a real basis. -/
def orthogonalBasisEffects (O : Matrix.orthogonalGroup (Fin 3) ℝ) :
    Fin 3 → Matrix (Fin 3) (Fin 3) ℝ :=
  fun i => Matrix.vecMulVec (O.valᵀ i) (O.valᵀ i)

private theorem orthogonalBasisEffects_eq_diagonal (O : Matrix.orthogonalGroup (Fin 3) ℝ)
    (i : Fin 3) :
    orthogonalBasisEffects O i = O.val * diagonal (Pi.single i 1) * O.valᴴ := by
  ext j k
  change O.val j i * O.val k i = _
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, star_trivial]
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _) (fun l _ hl => by
    simp [Pi.single_eq_of_ne hl])]
  simp

private theorem exists_orthogonalBasisEffects_reindex (O : Matrix.orthogonalGroup (Fin 3) ℝ)
    (e : Equiv.Perm (Fin 3)) :
    ∃ P : Matrix.orthogonalGroup (Fin 3) ℝ,
      orthogonalBasisEffects P = orthogonalBasisEffects O ∘ e := by
  let M := O.val.submatrix id e
  have hO : O.val * O.valᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp O.property
  have hM : M * Mᴴ = 1 := by
    dsimp only [M]
    rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, hO,
      Matrix.submatrix_id_id]
  have hmem : M ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
    apply Matrix.mem_unitaryGroup_iff.mpr
    exact hM
  exact ⟨⟨M, hmem⟩, rfl⟩

/-- A rank-one effect fixes one column of the basis. The other two columns
are interchanged in the second basis of the mixture. -/
theorem rank_one_effects_two_bases
    (A B C : Matrix (Fin 3) (Fin 3) ℝ) (hA : A.PosSemidef) (hB : B.PosSemidef) (hC : C.PosSemidef)
    (htraceA : A.trace = 1) (htraceB : B.trace = 1) (hrankA : A.rank = 1) (hsum : A + B + C = 1) :
    ∃ (P Q : Matrix.orthogonalGroup (Fin 3) ℝ) (t : ℝ), 0 ≤ t ∧ t ≤ 1 ∧
      (![A, B, C] : Fin 3 → Matrix (Fin 3) (Fin 3) ℝ) =
        t • orthogonalBasisEffects P + (1 - t) • orthogonalBasisEffects Q := by
  obtain ⟨O, i, b, hbound, hbi, htotal, ha, hb, hc⟩ :=
    rank_one_effects_complementary_diagonal A B C hA hB hC htraceA htraceB hrankA hsum
  let e : Equiv.Perm (Fin 3) := Equiv.swap 0 i
  let e' : Equiv.Perm (Fin 3) := (Equiv.swap 1 2).trans e
  let j := e 1
  let k := e 2
  let t := b j
  have h0 : e 0 = i := by simp [e]
  have htotal' := (Equiv.sum_comp e b).trans htotal
  have hk : b k = 1 - t := by
    simp only [Fin.sum_univ_three, h0, hbi, zero_add] at htotal'
    change b k = 1 - b j
    linarith only [htotal']
  have hzero : b (e 0) = 0 := by simpa only [h0] using hbi
  have hlast : b (e 2) = 1 - b (e 1) := hk
  have hbdecomp : b = t • (Pi.single j 1 : Fin 3 → ℝ) + (1 - t) • (Pi.single k 1 : Fin 3 → ℝ) := by
    funext l
    obtain ⟨r, rfl⟩ := e.surjective l
    fin_cases r <;> simp [j, k, t, Pi.single_apply, hzero, hlast, smul_eq_mul,
      Equiv.apply_eq_iff_eq]
  have hcdecomp : (fun l => 1 - (Pi.single i 1 : Fin 3 → ℝ) l - b l) =
      t • (Pi.single k 1 : Fin 3 → ℝ) + (1 - t) • (Pi.single j 1 : Fin 3 → ℝ) := by
    rw [← h0]
    funext l
    obtain ⟨r, rfl⟩ := e.surjective l
    fin_cases r <;> simp [j, k, t, Pi.single_apply, hzero, hlast, smul_eq_mul,
      Equiv.apply_eq_iff_eq] <;> ring
  obtain ⟨P, hp⟩ := exists_orthogonalBasisEffects_reindex O e
  obtain ⟨Q, hq⟩ := exists_orthogonalBasisEffects_reindex O e'
  have hh (u v : Fin 3 → ℝ) :
      O.val * diagonal (t • u + (1 - t) • v) * O.valᴴ =
        t • (O.val * diagonal u * O.valᴴ) + (1 - t) • (O.val * diagonal v * O.valᴴ) := by
    rw [← Matrix.diagonal_add, Matrix.diagonal_smul, Matrix.diagonal_smul, Matrix.mul_add,
      Matrix.add_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul]
  have he' (l : Fin 3) : e' l = e (Equiv.swap 1 2 l) := rfl
  refine ⟨P, Q, t, (hbound j).1, (hbound j).2, ?_⟩
  rw [hp, hq]
  funext l
  simp only [Pi.add_apply, Pi.smul_apply, Function.comp_apply, he']
  fin_cases l
  · change A = t • orthogonalBasisEffects O (e 0) +
      (1 - t) • orthogonalBasisEffects O (e (Equiv.swap (1 : Fin 3) 2 0))
    have hs : Equiv.swap (1 : Fin 3) 2 0 = 0 := by decide
    have hmass : t + (1 - t) = 1 := by ring
    rw [hs, h0, ← add_smul, hmass, one_smul, orthogonalBasisEffects_eq_diagonal, ha]
  · change B = t • orthogonalBasisEffects O j +
      (1 - t) • orthogonalBasisEffects O (e (Equiv.swap (1 : Fin 3) 2 1))
    rw [Equiv.swap_apply_left, orthogonalBasisEffects_eq_diagonal, orthogonalBasisEffects_eq_diagonal,
      hb, hbdecomp, hh]
  · change C = t • orthogonalBasisEffects O k +
      (1 - t) • orthogonalBasisEffects O (e (Equiv.swap (1 : Fin 3) 2 2))
    rw [Equiv.swap_apply_right, orthogonalBasisEffects_eq_diagonal, orthogonalBasisEffects_eq_diagonal,
      hc, hcdecomp, hh]

/-- If any effect has rank one, the tuple belongs to the convex hull of
orthonormal-basis effect tuples. -/
theorem effects_mem_convexHull_of_rank_one
    (E : Fin 3 → Matrix (Fin 3) (Fin 3) ℝ)
    (hpos : ∀ j, (E j).PosSemidef) (htrace : ∀ j, (E j).trace = 1)
    (hsum : ∑ j, E j = 1) (hrank : ∃ j, (E j).rank = 1) :
    E ∈ convexHull ℝ (Set.range orthogonalBasisEffects) := by
  obtain ⟨i, hi⟩ := hrank
  let e : Equiv.Perm (Fin 3) := Equiv.swap 0 i
  have h0 : e 0 = i := by simp [e]
  have hrank' : (E (e 0)).rank = 1 := by rwa [h0]
  have hsum' : E (e 0) + E (e 1) + E (e 2) = 1 := by
    simpa only [Fin.sum_univ_three] using (Equiv.sum_comp e E).trans hsum
  obtain ⟨P, Q, t, ht, ht', hcomb⟩ := rank_one_effects_two_bases (E (e 0)) (E (e 1)) (E (e 2))
    (hpos _) (hpos _) (hpos _) (htrace _) (htrace _) hrank' hsum'
  have hvec : (![E (e 0), E (e 1), E (e 2)] : Fin 3 → Matrix (Fin 3) (Fin 3) ℝ) = E ∘ e := by
    funext j
    fin_cases j <;> rfl
  rw [hvec] at hcomb
  obtain ⟨P', hp⟩ := exists_orthogonalBasisEffects_reindex P e.symm
  obtain ⟨Q', hq⟩ := exists_orthogonalBasisEffects_reindex Q e.symm
  have hE : E = t • orthogonalBasisEffects P' + (1 - t) • orthogonalBasisEffects Q' := by
    funext j
    simpa only [hp, hq, Pi.add_apply, Pi.smul_apply, Function.comp_apply, Equiv.apply_symm_apply]
      using congrFun hcomb (e.symm j)
  rw [hE]
  have hp' : orthogonalBasisEffects P' ∈ convexHull ℝ (Set.range orthogonalBasisEffects) :=
    subset_convexHull ℝ _ ⟨P', rfl⟩
  have hq' : orthogonalBasisEffects Q' ∈ convexHull ℝ (Set.range orthogonalBasisEffects) :=
    subset_convexHull ℝ _ ⟨Q', rfl⟩
  exact (convex_convexHull ℝ _)
    hp' hq' ht
    (sub_nonneg.mpr ht') (by ring)

/-- A finite family of initially positive two-dimensional effects stays
nonnegative in determinant on an interval containing zero. At both endpoints
at least one determinant is zero. -/
theorem exists_traceless_perturbation_endpoints {ι : Type*} [Fintype ι]
    (p q a b : ι → ℝ) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
    (hmove : ∃ i, a i ≠ 0 ∨ b i ≠ 0) :
    let d (i : ι) (s : ℝ) := (p i + s * a i) * (q i - s * a i) - (s * b i) ^ 2
    ∃ l u : ℝ, l < 0 ∧ 0 < u ∧
      (∀ s ∈ Set.Icc l u, ∀ i, 0 ≤ d i s) ∧ (∃ i, d i l = 0) ∧ (∃ j, d j u = 0) := by
  classical
  let d (i : ι) (s : ℝ) := (p i + s * a i) * (q i - s * a i) - (s * b i) ^ 2
  let w i := a i ^ 2 + b i ^ 2
  let z i := (q i - p i) * a i
  let c i := p i * q i
  let D i := Real.sqrt (z i ^ 2 + 4 * w i * c i)
  let L i := (z i - D i) / (2 * w i)
  let U i := (z i + D i) / (2 * w i)
  have hW (i : ι) : 0 ≤ w i := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hC (i : ι) : 0 < c i := mul_pos (hp i) (hq i)
  have hdisc (i : ι) : 0 ≤ z i ^ 2 + 4 * w i * c i :=
    add_nonneg (sq_nonneg _) (mul_nonneg (mul_nonneg (by norm_num) (hW i)) (hC i).le)
  have hformula (i : ι) (s : ℝ) :
      4 * w i * d i s = D i ^ 2 - (2 * w i * s - z i) ^ 2 := by
    rw [show D i ^ 2 = _ from Real.sq_sqrt (hdisc i)]
    dsimp [d, w, z, c]
    ring
  have habs (i : ι) (hi : 0 < w i) : |z i| < D i := by
    rw [← Real.sqrt_sq_eq_abs]
    apply Real.sqrt_lt_sqrt (sq_nonneg _)
    linarith only [mul_pos (mul_pos (by norm_num : (0 : ℝ) < 4) hi) (hC i)]
  have hL (i : ι) (hi : 0 < w i) : L i < 0 := by
    exact div_neg_of_neg_of_pos (sub_neg.mpr ((le_abs_self _).trans_lt (habs i hi)))
      (mul_pos (by norm_num) hi)
  have hU (i : ι) (hi : 0 < w i) : 0 < U i := by
    have h := (le_abs_self (-z i)).trans_lt (by simpa only [abs_neg] using habs i hi)
    exact div_pos (by linarith only [h]) (mul_pos (by norm_num) hi)
  have hleft (i : ι) (hi : 0 < w i) : 2 * w i * L i - z i = -D i := by
    dsimp only [L]
    field_simp [hi.ne'] <;> ring
  have hright (i : ι) (hi : 0 < w i) : 2 * w i * U i - z i = D i := by
    dsimp only [U]
    field_simp [hi.ne'] <;> ring
  let S := Finset.univ.filter (fun i => 0 < w i)
  have hS (i : ι) : i ∈ S ↔ 0 < w i := by simp [S]
  have hne : S.Nonempty := by
    obtain ⟨i, hi⟩ := hmove
    have hpos : 0 < w i := hi.elim
      (fun h => add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h) (sq_nonneg _))
      (fun h => add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero h))
    exact ⟨i, (hS i).mpr hpos⟩
  obtain ⟨i, his, himax⟩ := Finset.exists_max_image S L hne
  obtain ⟨j, hjs, hjmin⟩ := Finset.exists_min_image S U hne
  have hi := (hS i).mp his
  have hj := (hS j).mp hjs
  refine ⟨L i, U j, hL i hi, hU j hj, ?_, ⟨i, ?_⟩, ⟨j, ?_⟩⟩
  · intro s hs k
    change 0 ≤ d k s
    by_cases hk : 0 < w k
    · have hm (a b : ℝ) (h : a ≤ b) :
          2 * w k * a - z k ≤ 2 * w k * b - z k :=
        sub_le_sub_right (mul_le_mul_of_nonneg_left h (mul_nonneg (by norm_num) hk.le)) _
      have h₁ : -D k ≤ 2 * w k * s - z k := by
        rw [← hleft k hk]
        exact hm _ _ ((himax k ((hS k).mpr hk)).trans hs.1)
      have h₂ : 2 * w k * s - z k ≤ D k := by
        rw [← hright k hk]
        exact hm _ _ (hs.2.trans (hjmin k ((hS k).mpr hk)))
      apply nonneg_of_mul_nonneg_right _ (mul_pos (by norm_num : (0 : ℝ) < 4) hk)
      rw [hformula]
      exact sub_nonneg.mpr (sq_le_sq' h₁ h₂)
    · have hwzero : w k = 0 := le_antisymm (le_of_not_gt hk) (hW k)
      change a k ^ 2 + b k ^ 2 = 0 at hwzero
      have ha : a k = 0 := by nlinarith only [hwzero, sq_nonneg (b k)]
      have hb : b k = 0 := by nlinarith only [hwzero, sq_nonneg (a k)]
      simpa [d, ha, hb, c] using (hC k).le
  · change d i (L i) = 0
    have h := hformula i (L i)
    rw [hleft i hi, neg_sq, sub_self] at h
    exact (mul_eq_zero.mp h).resolve_left (mul_pos (by norm_num) hi).ne'
  · change d j (U j) = 0
    have h := hformula j (U j)
    rw [hright j hj, sub_self] at h
    exact (mul_eq_zero.mp h).resolve_left (mul_pos (by norm_num) hj).ne'

private theorem posSemidef_fin_two_of_trace_one_of_det_nonneg
    (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : A.IsHermitian) (htrace : A.trace = 1) (hdet : 0 ≤ A.det) :
    A.PosSemidef ∧ (A.det = 0 → A.rank = 1) := by
  classical
  let e := hA.eigenvalues
  let V := hA.eigenvectorUnitary
  have hVV : V.valᴴ * V.val = 1 := Matrix.mem_unitaryGroup_iff'.mp V.property
  have hdiag : A = V.val * diagonal e * V.valᴴ := by
    simpa [V, e, RCLike.ofReal_real_eq_id] using hA.spectral_theorem
  have hsum : e 0 + e 1 = 1 := by
    have h := htrace
    rw [hdiag, Matrix.trace_mul_cycle, hVV, Matrix.one_mul, Matrix.trace_diagonal,
      Fin.sum_univ_two] at h
    exact h
  have hde : A.det = e 0 * e 1 := by
    simpa [e, RCLike.ofReal_real_eq_id, Fin.prod_univ_two] using hA.det_eq_prod_eigenvalues
  have hprod : 0 ≤ e 0 * e 1 := hde ▸ hdet
  have h0 : 0 ≤ e 0 := by
    by_contra! h
    exact (not_lt_of_ge hprod) (mul_neg_of_neg_of_pos h (by linarith only [hsum, h]))
  have h1 : 0 ≤ e 1 := by
    by_contra! h
    exact (not_lt_of_ge hprod) (mul_neg_of_pos_of_neg (by linarith only [hsum, h]) h)
  have hpos (i : Fin 2) : 0 ≤ e i := by
    fin_cases i
    · exact h0
    · exact h1
  refine ⟨hA.posSemidef_of_eigenvalues_nonneg hpos, ?_⟩
  intro hz
  rw [hde] at hz
  rw [hA.rank_eq_card_non_zero_eigs]
  change Fintype.card {i // e i ≠ 0} = 1
  let S := Finset.univ.filter (fun i : Fin 2 => e i ≠ 0)
  rw [Fintype.card_of_subtype S (by simp [S])]
  rcases mul_eq_zero.mp hz with h | h
  · have ho : e 1 = 1 := by linarith only [hsum, h]
    have hS : S = {1} := by ext i; fin_cases i <;> simp [S, h, ho]
    simp [hS]
  · have ho : e 0 = 1 := by linarith only [hsum, h]
    have hS : S = {0} := by ext i; fin_cases i <;> simp [S, h, ho]
    simp [hS]

private theorem rank_two_column_sandwich
    (X : Matrix (Fin 3) (Fin 2) ℝ) (hX : Xᴴ * X = 1) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    (X * A * Xᴴ).rank = A.rank := by
  apply le_antisymm
  · exact (Matrix.rank_mul_le_left (X * A) Xᴴ).trans (Matrix.rank_mul_le_right X A)
  · have h : Xᴴ * (X * A * Xᴴ) * X = A := calc
      _ = (Xᴴ * X) * A * (Xᴴ * X) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hX, Matrix.one_mul, Matrix.mul_one]
    calc
      A.rank = (Xᴴ * (X * A * Xᴴ) * X).rank := by rw [h]
      _ ≤ (X * A * Xᴴ).rank := (Matrix.rank_mul_le_left (Xᴴ * (X * A * Xᴴ)) X).trans
        (Matrix.rank_mul_le_right Xᴴ (X * A * Xᴴ))

private theorem trace_eq_sum_eigenvalues_real {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) : A.trace = ∑ i, hA.eigenvalues i := by
  let V := hA.eigenvectorUnitary
  have hV : V.valᴴ * V.val = 1 := Matrix.mem_unitaryGroup_iff'.mp V.property
  have hdiag : A = V.val * diagonal hA.eigenvalues * V.valᴴ := by
    simpa [V, RCLike.ofReal_real_eq_id] using hA.spectral_theorem
  calc
    _ = (V.val * diagonal hA.eigenvalues * V.valᴴ).trace := congrArg Matrix.trace hdiag
    _ = _ := by rw [Matrix.trace_mul_cycle, hV, Matrix.one_mul, Matrix.trace_diagonal]

private theorem two_column_frame_of_rank_two
    (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : A.PosSemidef) (htrace : A.trace = 1) (hrank : A.rank = 2) :
    ∃ (X : Matrix (Fin 3) (Fin 2) ℝ) (p q : ℝ), 0 < p ∧ 0 < q ∧ p + q = 1 ∧
      Xᴴ * X = 1 ∧ A = X * diagonal ![p, q] * Xᴴ := by
  classical
  let eig := hA.isHermitian.eigenvalues
  let V := hA.isHermitian.eigenvectorUnitary
  have hV : V.valᴴ * V.val = 1 := Matrix.mem_unitaryGroup_iff'.mp V.property
  have hdiag : A = V.val * diagonal eig * V.valᴴ := by
    simpa [V, eig, RCLike.ofReal_real_eq_id] using hA.isHermitian.spectral_theorem
  have hcard : Fintype.card {j // eig j ≠ 0} = 2 :=
    hA.isHermitian.rank_eq_card_non_zero_eigs.symm.trans hrank
  let e : Fin 2 ≃ {j // eig j ≠ 0} := Fintype.equivOfCardEq (by rw [Fintype.card_fin, hcard])
  let f (i : Fin 2) : Fin 3 := (e i).val
  let X := V.val.submatrix id f
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  have hX : Xᴴ * X = 1 := by
    dsimp only [X]
    rw [Matrix.conjTranspose_submatrix,
      ← Matrix.submatrix_mul V.valᴴ V.val f id f Function.bijective_id, hV,
      Matrix.submatrix_one _ hf]
  let p := eig (f 0)
  let q := eig (f 1)
  have hexp (k : Fin 2) : 0 < eig (f k) :=
    lt_of_le_of_ne (hA.eigenvalues_nonneg _) (e k).property.symm
  have hw : (![p, q] : Fin 2 → ℝ) = eig ∘ f := by
    funext k
    fin_cases k <;> rfl
  have hshape : A = X * diagonal ![p, q] * Xᴴ := by
    rw [hdiag, hw]
    ext i j
    change (∑ k : Fin 3, (V.val * diagonal eig) i k * V.valᴴ k j) =
      ∑ k : Fin 2, (X * diagonal (eig ∘ f)) i k * Xᴴ k j
    simp only [X, Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.submatrix_apply,
      Function.comp_apply, id_eq, star_trivial]
    let g (k : Fin 3) := V.val i k * eig k * V.val j k
    change (∑ k : Fin 3, g k) = ∑ k : Fin 2, g (e k).val
    rw [Equiv.sum_comp e (fun k => g k.val)]
    apply Finset.sum_congr_set {k | eig k ≠ 0}
    · intro k hk
      rfl
    · intro k hk
      have hz : eig k = 0 := by simpa using hk
      simp [g, hz]
  have hsum : p + q = 1 := by
    have h := htrace
    rw [hshape, Matrix.trace_mul_cycle, hX, Matrix.one_mul, Matrix.trace_diagonal,
      Fin.sum_univ_two] at h
    exact h
  exact ⟨X, p, q, hexp 0, hexp 1, hsum, hX, hshape⟩

/-- A trace-one effect tuple presented on three two-column orthonormal
frames is a convex mixture of orthonormal-basis effect tuples. -/
theorem effects_mem_convexHull_of_two_column_frames
    (E : Fin 3 → Matrix (Fin 3) (Fin 3) ℝ) (X : Fin 3 → Matrix (Fin 3) (Fin 2) ℝ)
    (p q : Fin 3 → ℝ) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
    (htrace : ∀ i, p i + q i = 1) (hgram : ∀ i, (X i)ᴴ * X i = 1)
    (hE : ∀ i, E i = X i * diagonal ![p i, q i] * (X i)ᴴ) (hsum : ∑ i, E i = 1) :
    E ∈ convexHull ℝ (Set.range orthogonalBasisEffects) := by
  let A₀ : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]
  let B₀ : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]
  let A i := X i * A₀ * (X i)ᴴ
  let B i := X i * B₀ * (X i)ᴴ
  have hA₀ : A₀ᴴ = A₀ := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [A₀, Matrix.conjTranspose_apply]
  have hB₀ : B₀ᴴ = B₀ := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [B₀, Matrix.conjTranspose_apply]
  have hsandwich (i : Fin 3) (D : Matrix (Fin 2) (Fin 2) ℝ)
      (hD : Dᴴ = D) (htD : D.trace = 0) :
      (X i * D * (X i)ᴴ)ᵀ = X i * D * (X i)ᴴ ∧ (X i * D * (X i)ᴴ).trace = 0 := by
    constructor
    · rw [← Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hD, Matrix.mul_assoc]
    · rw [Matrix.trace_mul_cycle, hgram i, Matrix.one_mul, htD]
  have hA (i : Fin 3) : (A i)ᵀ = A i ∧ (A i).trace = 0 :=
    hsandwich i A₀ hA₀ (by norm_num [A₀, Matrix.trace_fin_two_of])
  have hB (i : Fin 3) : (B i)ᵀ = B i ∧ (B i).trace = 0 :=
    hsandwich i B₀ hB₀ (by norm_num [B₀, Matrix.trace_fin_two_of])
  obtain ⟨x, hx, hsumD⟩ := exists_zero_sum_trace_free_perturbation A B hA hB
  let a i := x (i, 0)
  let b i := x (i, 1)
  let D i := a i • A i + b i • B i
  let F (t : ℝ) (i : Fin 3) := E i + t • D i
  let H (t : ℝ) (i : Fin 3) : Matrix (Fin 2) (Fin 2) ℝ :=
    !![p i + t * a i, t * b i; t * b i, q i - t * a i]
  have hmove : ∃ i, a i ≠ 0 ∨ b i ≠ 0 := by
    by_contra h
    apply hx
    funext ij
    obtain ⟨i, j⟩ := ij
    fin_cases j
    · by_contra hn
      exact h ⟨i, Or.inl hn⟩
    · by_contra hn
      exact h ⟨i, Or.inr hn⟩
  obtain ⟨l, u, hl, hu, hinterval, hleft, hright⟩ :=
    exists_traceless_perturbation_endpoints p q a b hp hq hmove
  have hH (t : ℝ) (i : Fin 3) :
      H t i = diagonal ![p i, q i] + t • (a i • A₀ + b i • B₀) := by
    ext j k
    fin_cases j <;> fin_cases k <;>
      simp [H, A₀, B₀, Matrix.diagonal_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul] <;>
      ring
  have hF (t : ℝ) (i : Fin 3) : F t i = X i * H t i * (X i)ᴴ := by
    rw [hH, show F t i = E i + t • D i from rfl, hE]
    simp only [D, A, B, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  have hHtrace (t : ℝ) (i : Fin 3) : (H t i).trace = 1 := by
    change ( !![p i + t * a i, t * b i; t * b i, q i - t * a i] : Matrix (Fin 2) (Fin 2) ℝ).trace = 1
    rw [Matrix.trace_fin_two_of]
    linarith only [htrace i]
  have hHdet (t : ℝ) (i : Fin 3) :
      (H t i).det = (p i + t * a i) * (q i - t * a i) - (t * b i) ^ 2 := by
    simp [H, Matrix.det_fin_two, pow_two]
  have hHsymm (t : ℝ) (i : Fin 3) : (H t i).IsHermitian := by
    change (H t i)ᴴ = H t i
    ext j k
    fin_cases j <;> fin_cases k <;> simp [H, Matrix.conjTranspose_apply]
  have hFtrace (t : ℝ) (i : Fin 3) : (F t i).trace = 1 := by
    rw [hF, Matrix.trace_mul_cycle, hgram i, Matrix.one_mul, hHtrace]
  have hFsum (t : ℝ) : ∑ i, F t i = 1 := by
    simp only [F, Finset.sum_add_distrib, ← Finset.smul_sum, hsum, show (∑ i, D i) = 0 from hsumD,
      smul_zero, add_zero]
  have hHull (t : ℝ) (ht : t ∈ Set.Icc l u)
      (hz : ∃ i, (p i + t * a i) * (q i - t * a i) - (t * b i) ^ 2 = 0) :
      F t ∈ convexHull ℝ (Set.range orthogonalBasisEffects) := by
    have hpos (i : Fin 3) := posSemidef_fin_two_of_trace_one_of_det_nonneg (H t i) (hHsymm t i)
      (hHtrace t i) (by rw [hHdet]; exact hinterval t ht i)
    refine effects_mem_convexHull_of_rank_one (F t) (fun i => ?_) (hFtrace t) (hFsum t) ?_
    · rw [hF]
      exact (hpos i).1.mul_mul_conjTranspose_same (X i)
    · obtain ⟨i, hi⟩ := hz
      refine ⟨i, ?_⟩
      rw [hF, rank_two_column_sandwich _ (hgram i)]
      exact (hpos i).2 ((hHdet t i).trans hi)
  have hlu : l ≤ u := hl.le.trans hu.le
  have hL := hHull l ⟨le_rfl, hlu⟩ hleft
  have hU := hHull u ⟨hlu, le_rfl⟩ hright
  let w := u / (u - l)
  let v := -l / (u - l)
  have hden : 0 < u - l := sub_pos.mpr (hl.trans hu)
  have hw : 0 ≤ w := div_nonneg hu.le hden.le
  have hv : 0 ≤ v := div_nonneg (neg_nonneg.mpr hl.le) hden.le
  have hmass : w + v = 1 := by
    dsimp only [w, v]
    field_simp [hden.ne'] <;> ring
  have hzero : w * l + v * u = 0 := by
    dsimp only [w, v]
    field_simp [hden.ne'] <;> ring
  have hcomb : E = w • F l + v • F u := by
    funext i
    change E i = w • (E i + l • D i) + v • (E i + u • D i)
    calc
      _ = (w + v) • E i + (w * l + v * u) • D i := by rw [hmass, hzero, one_smul, zero_smul, add_zero]
      _ = _ := by simp only [add_smul, smul_add, smul_smul]; abel
  rw [hcomb]
  exact (convex_convexHull ℝ _) hL hU hw hv hmass

/-- A positive trace-one effect tuple on a real three-space with ranks
at most two is a convex mixture of real basis effect tuples. -/
theorem effects_mem_convexHull_of_rank_le_two
    (E : Fin 3 → Matrix (Fin 3) (Fin 3) ℝ)
    (hpos : ∀ j, (E j).PosSemidef) (htrace : ∀ j, (E j).trace = 1)
    (hsum : ∑ j, E j = 1) (hrank : ∀ j, (E j).rank ≤ 2) :
    E ∈ convexHull ℝ (Set.range orthogonalBasisEffects) := by
  classical
  by_cases h : ∃ j, (E j).rank = 1
  · exact effects_mem_convexHull_of_rank_one E hpos htrace hsum h
  have htwo (i : Fin 3) : (E i).rank = 2 := by
    have hne := not_exists.mp h i
    have hupper := hrank i
    have hn : (E i).rank ≠ 0 := by
      let eig := (hpos i).isHermitian.eigenvalues
      rw [(hpos i).isHermitian.rank_eq_card_non_zero_eigs]
      intro hz
      have hempty : IsEmpty {j // eig j ≠ 0} := Fintype.card_eq_zero_iff.mp hz
      have hzero (j : Fin 3) : eig j = 0 := by
        by_contra hj
        exact hempty.false ⟨j, hj⟩
      have htr := (trace_eq_sum_eigenvalues_real (E i) (hpos i).isHermitian).symm.trans (htrace i)
      change (∑ j, eig j) = 1 at htr
      simp [hzero] at htr
    omega
  choose X p q hp hq htrace' hgram hshape using
    fun i => two_column_frame_of_rank_two (E i) (hpos i) (htrace i) (htwo i)
  exact effects_mem_convexHull_of_two_column_frames E X p q hp hq htrace' hgram hshape hsum

/-- The real quadratic form obtained by squaring the modulus of each row
against real coordinate vectors. -/
def realRowEffects (W : Matrix (Fin 3) (Fin 3) ℂ) : Fin 3 → Matrix (Fin 3) (Fin 3) ℝ :=
  fun i => Matrix.of fun j k => (star (W i j) * W i k).re

private def realRowCoordinates (W : Matrix (Fin 3) (Fin 3) ℂ) (i : Fin 3) :
    Matrix (Fin 2) (Fin 3) ℝ :=
  Matrix.of fun k j => if k = 0 then (W i j).re else (W i j).im

private theorem realRowEffects_eq_gram (W : Matrix (Fin 3) (Fin 3) ℂ) (i : Fin 3) :
    realRowEffects W i = (realRowCoordinates W i)ᴴ * realRowCoordinates W i := by
  ext j k
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  simp [realRowEffects, realRowCoordinates, Matrix.conjTranspose_apply, Complex.star_def,
    Complex.mul_re]

/-- Evaluating a row effect on a real vector gives the squared modulus of
the corresponding complex row pairing. -/
theorem realRowEffects_quadratic (W : Matrix (Fin 3) (Fin 3) ℂ) (i : Fin 3) (v : Fin 3 → ℝ) :
    v ⬝ᵥ realRowEffects W i *ᵥ v = Complex.normSq (∑ j, (v j : ℂ) * W i j) := by
  rw [realRowEffects_eq_gram, ← Matrix.mulVec_mulVec, dotProduct_mulVec, vecMul_conjTranspose]
  simp only [star_trivial]
  have h0 : (realRowCoordinates W i *ᵥ v) 0 = ∑ j, v j * (W i j).re := by
    simp [Matrix.mulVec, dotProduct, realRowCoordinates, mul_comm]
  have h1 : (realRowCoordinates W i *ᵥ v) 1 = ∑ j, v j * (W i j).im := by
    simp [Matrix.mulVec, dotProduct, realRowCoordinates, mul_comm]
  unfold dotProduct
  rw [Fin.sum_univ_two, h0, h1, Complex.normSq_apply, Complex.re_sum, Complex.im_sum]
  simp [Complex.mul_re, Complex.mul_im]

/-- A three-dimensional unitary's row effects have a common convex
decomposition into the rank-one effects of real orthonormal bases. -/
theorem realRowEffects_mem_convexHull (W : Matrix (Fin 3) (Fin 3) ℂ) (hW : IsUnitary W) :
    realRowEffects W ∈ convexHull ℝ (Set.range orthogonalBasisEffects) := by
  have hpos (i : Fin 3) : (realRowEffects W i).PosSemidef := by
    refine ⟨?_, fun x => ?_⟩
    · rw [realRowEffects_eq_gram]
      exact Matrix.isHermitian_transpose_mul_self _
    · rw [star_trivial, realRowEffects_quadratic]
      exact Complex.normSq_nonneg _
  have htrace (i : Fin 3) : (realRowEffects W i).trace = 1 := by
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => (M i i).re) hW.1
    change ((W * Wᴴ) i i).re = ((1 : Matrix (Fin 3) (Fin 3) ℂ) i i).re at h
    rw [Matrix.mul_apply, Complex.re_sum, Matrix.one_apply_eq, Complex.one_re] at h
    calc
      _ = ∑ j, (W i j * star (W i j)).re := by
        apply Finset.sum_congr rfl
        intro j _
        exact congrArg Complex.re (mul_comm _ _)
      _ = 1 := by simpa only [Matrix.conjTranspose_apply] using h
  have hsum : ∑ i, realRowEffects W i = 1 := by
    ext j k
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => (M j k).re) hW.2
    change ((Wᴴ * W) j k).re = ((1 : Matrix (Fin 3) (Fin 3) ℂ) j k).re at h
    rw [Matrix.mul_apply, Complex.re_sum] at h
    simpa [Matrix.sum_apply, realRowEffects, Matrix.conjTranspose_apply, Matrix.one_apply, apply_ite]
      using h
  have hrank (i : Fin 3) : (realRowEffects W i).rank ≤ 2 := by
    rw [realRowEffects_eq_gram]
    exact (Matrix.rank_mul_le_left (realRowCoordinates W i)ᴴ (realRowCoordinates W i)).trans
      (Matrix.rank_le_width (realRowCoordinates W i)ᴴ)
  exact effects_mem_convexHull_of_rank_le_two _ hpos htrace hsum hrank

end

end MOC
