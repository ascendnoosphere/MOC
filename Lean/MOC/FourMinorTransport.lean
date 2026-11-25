import MOC.FourEffectDecomposition
import MOC.Small
import Mathlib.Analysis.Convex.Combination

/-! Transport of three-dimensional row effects to the squared minors in order four. -/

open BigOperators Matrix
open scoped InnerProductSpace

namespace MOC

noncomputable section

private theorem squared_minor_complement {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) (I J : Finset ι) :
    subsetMinorSq U Iᶜ Jᶜ = subsetMinorSq U I J := by
  classical
  have hmap (σ : Equiv.Perm ι) : Jᶜ.map σ.toEmbedding = (J.map σ.toEmbedding)ᶜ := by
    ext i
    simp only [Finset.mem_map, Finset.mem_compl, Equiv.toEmbedding_apply]
    constructor
    · rintro ⟨j, hj, hji⟩ ⟨k, hk, hki⟩
      have hkj := σ.injective (hki.trans hji.symm)
      exact hj (hkj ▸ hk)
    · intro hi
      refine ⟨σ.symm i, ?_, σ.apply_symm_apply i⟩
      intro hj
      exact hi ⟨σ.symm i, hj, σ.apply_symm_apply i⟩
  have hfilter : (Finset.univ.filter (fun σ : Equiv.Perm ι => Jᶜ.map σ.toEmbedding = Iᶜ)) =
      Finset.univ.filter (fun σ : Equiv.Perm ι => J.map σ.toEmbedding = I) := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hmap, compl_inj_iff]
  apply Complex.ofReal_injective
  rw [← sum_signedWeight_image_eq_subsetMinorSq U hU Iᶜ Jᶜ,
    ← sum_signedWeight_image_eq_subsetMinorSq U hU I J, hfilter]

private theorem squared_minor_indexed {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (U : Matrix ι ι ℂ) (hU : IsUnitary U) (I J : Finset ι)
    (e : κ ≃ I) (f : κ ≃ J) :
    subsetMinorSq U I J = Complex.normSq (U.submatrix (Subtype.val ∘ e) (Subtype.val ∘ f)).det := by
  have h := sum_signedWeight_image_eq_minor U hU I J (e.symm.trans f)
  rw [sum_signedWeight_image_eq_subsetMinorSq U hU I J] at h
  let A := U.submatrix (fun i : I => (i : ι)) (fun i : I => (((e.symm.trans f) i : J) : ι))
  have hdet : A.det = (U.submatrix (Subtype.val ∘ e) (Subtype.val ∘ f)).det := by
    rw [← Matrix.det_submatrix_equiv_self e A]
    congr 1
    ext i j
    simp [A]
  apply Complex.ofReal_injective
  exact h.trans (congrArg (fun z : ℂ => (Complex.normSq z : ℂ)) hdet)

private theorem squared_minor_singleton {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) (i j : ι) :
    subsetMinorSq U {i} {j} = Complex.normSq (U i j) := by
  let e : Fin 1 ≃ ({i} : Finset ι) := Fintype.equivOfCardEq (by simp)
  let f : Fin 1 ≃ ({j} : Finset ι) := Fintype.equivOfCardEq (by simp)
  rw [squared_minor_indexed U hU _ _ e f, Matrix.det_fin_one]
  have hi : (e 0).val = i := Finset.mem_singleton.mp (e 0).property
  have hj : (f 0).val = j := Finset.mem_singleton.mp (f 0).property
  simpa only [Matrix.submatrix_apply, Function.comp_apply, hi, hj]

private theorem pair_equiv {ι : Type*} [DecidableEq ι] (i j : ι) (hij : i ≠ j) :
    ∃ e : Fin 2 ≃ ({i, j} : Finset ι), (e 0).val = i ∧ (e 1).val = j := by
  let f : Fin 2 → ({i, j} : Finset ι) :=
    ![⟨i, Finset.mem_insert_self _ _⟩, ⟨j, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩]
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      have hval := congrArg Subtype.val hab
      fin_cases a <;> fin_cases b <;> simp [f, hij, hij.symm] at hval ⊢
    · rintro ⟨k, hk⟩
      rcases Finset.mem_insert.mp hk with h | h
      · subst k
        exact ⟨0, Subtype.ext rfl⟩
      · have hkj := Finset.mem_singleton.mp h
        subst k
        exact ⟨1, Subtype.ext rfl⟩
  exact ⟨Equiv.ofBijective f hf, rfl, rfl⟩

private theorem squared_minor_pair {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) {i k j l : ι} (hi : i ≠ k) (hj : j ≠ l) :
    subsetMinorSq U {i, k} {j, l} = Complex.normSq (U i j * U k l - U i l * U k j) := by
  obtain ⟨e, e₀, e₁⟩ := pair_equiv i k hi
  obtain ⟨f, f₀, f₁⟩ := pair_equiv j l hj
  rw [squared_minor_indexed U hU _ _ e f, Matrix.det_fin_two]
  simp only [Matrix.submatrix_apply, Function.comp_apply, e₀, e₁, f₀, f₁]

private theorem squared_minor_empty {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) : subsetMinorSq U ∅ ∅ = 1 := by
  apply Complex.ofReal_injective
  rw [← sum_signedWeight_image_eq_subsetMinorSq U hU ∅ ∅, Complex.ofReal_one]
  simpa using sum_signedWeight U (det_ne_zero_of_unitary hU)

private theorem squared_minor_of_card_ne {ι : Type*} [DecidableEq ι]
    (U : Matrix ι ι ℂ) (I J : Finset ι) (h : I.card ≠ J.card) : subsetMinorSq U I J = 0 := by
  simp [subsetMinorSq, h]

/-- In order four, singleton minors and the two-minors containing one
prescribed row determine every squared minor. -/
theorem squared_minor_mixture_of_anchor {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (hcard : Fintype.card ι = 4) (r : ι) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (V : κ → Matrix ι ι ℂ) (hV : ∀ j, IsUnitary (V j)) (w : κ → ℝ) (hw : ∑ j, w j = 1)
    (hone : ∀ i j : ι, subsetMinorSq U {i} {j} = ∑ k, w k * subsetMinorSq (V k) {i} {j})
    (htwo : ∀ i j l : ι, r ≠ i → j ≠ l →
      subsetMinorSq U {r, i} {j, l} = ∑ k, w k * subsetMinorSq (V k) {r, i} {j, l}) :
    ∀ I J : Finset ι, subsetMinorSq U I J = ∑ k, w k * subsetMinorSq (V k) I J := by
  have hshort (I J : Finset ι) (hIJ : I.card = J.card) (hsmall : I.card ≤ 2)
      (hr : I.card = 2 → r ∈ I) :
      subsetMinorSq U I J = ∑ k, w k * subsetMinorSq (V k) I J := by
    by_cases h0 : I.card = 0
    · have hI := Finset.card_eq_zero.mp h0
      have hJ := Finset.card_eq_zero.mp (hIJ.symm.trans h0)
      simp [hI, hJ, squared_minor_empty U hU, fun k => squared_minor_empty (V k) (hV k), hw]
    by_cases h1 : I.card = 1
    · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp h1
      obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp (hIJ.symm.trans h1)
      exact hone i j
    have h2 : I.card = 2 := by omega
    have hri := hr h2
    obtain ⟨i, i', hi, hI⟩ := Finset.card_eq_two.mp h2
    obtain ⟨j, l, hj, rfl⟩ := Finset.card_eq_two.mp (hIJ.symm.trans h2)
    have hcase : r = i ∨ r = i' := by simpa [hI] using hri
    rcases hcase with h | h
    · subst i
      rw [hI]
      exact htwo _ _ _ hi hj
    · subst i'
      rw [hI, Finset.pair_comm i r]
      exact htwo _ _ _ hi.symm hj
  intro I J
  by_cases hIJ : I.card = J.card
  · by_cases hc : I.card ≤ 2 ∧ (I.card = 2 → r ∈ I)
    · exact hshort I J hIJ hc.1 hc.2
    have hbig : 2 ≤ I.card := by
      by_contra h
      exact hc ⟨by omega, fun h2 => (h (by omega)).elim⟩
    have hcIJ : Iᶜ.card = Jᶜ.card := by rw [Finset.card_compl, Finset.card_compl, hIJ]
    have hcSmall : Iᶜ.card ≤ 2 := by rw [Finset.card_compl, hcard]; omega
    have hcAnchor (h : Iᶜ.card = 2) : r ∈ Iᶜ := by
      rw [Finset.card_compl, hcard] at h
      apply Finset.mem_compl.mpr
      intro hr
      exact hc ⟨by omega, fun _ => hr⟩
    simpa only [squared_minor_complement U hU, fun k => squared_minor_complement (V k) (hV k)]
      using hshort Iᶜ Jᶜ hcIJ hcSmall hcAnchor
  · simp [squared_minor_of_card_ne U _ _ hIJ, fun k => squared_minor_of_card_ne (V k) I J hIJ]

private theorem exists_orthogonal_row {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → ℝ) (hv : ∑ j, v j * v j = 1) (r : ι) :
    ∃ P : Matrix.orthogonalGroup ι ℝ, ∀ j, P.val r j = v j := by
  let u := (WithLp.equiv 2 (ι → ℝ)).symm v
  have hu : ⟪u, u⟫_ℝ = 1 := by
    dsimp only [u]
    rw [EuclideanSpace.inner_piLp_equiv_symm]
    simpa [dotProduct] using hv
  let s : Set ι := {r}
  have horth : Orthonormal ℝ (s.restrict (fun _ : ι => u)) := by
    classical
    rw [orthonormal_iff_ite]
    intro i j
    have hi : (i : ι) = r := Set.mem_singleton_iff.mp i.property
    have hj : (j : ι) = r := Set.mem_singleton_iff.mp j.property
    have hij : i = j := Subtype.ext (hi.trans hj.symm)
    simpa [Set.restrict, hij] using hu
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (finrank_euclideanSpace (𝕜 := ℝ) (ι := ι)) horth
  let std := EuclideanSpace.basisFun ι ℝ
  let P : Matrix.orthogonalGroup ι ℝ :=
    ⟨std.toBasis.toMatrix b.toBasis, std.toMatrix_orthonormalBasis_mem_unitary b⟩
  refine ⟨star P, fun j => ?_⟩
  have h := congrArg (fun x : EuclideanSpace ℝ ι => WithLp.equiv 2 (ι → ℝ) x j)
    (hb r (Set.mem_singleton r))
  change star ((std.toBasis.toMatrix b.toBasis) j r) = v j
  simpa only [std, u, star_trivial, Basis.toMatrix_apply,
    OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.coe_toBasis,
    EuclideanSpace.basisFun_repr, Equiv.apply_symm_apply] using h

private theorem unitary_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U V : Matrix ι ι ℂ) (hU : IsUnitary U) (hV : IsUnitary V) : IsUnitary (U * V) := by
  have h : (U * V) * (U * V)ᴴ = 1 := calc
    _ = U * (V * Vᴴ) * Uᴴ := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = 1 := by rw [hV.1, Matrix.mul_one, hU.1]
  exact ⟨h, Matrix.mul_eq_one_comm.mp h⟩

abbrev FourRowIndices := Fin 1 ⊕ Fin 3

/-- Change coordinates by an orthogonal matrix whose first row is prescribed,
then use a three-dimensional unitary on the other rows. -/
def fixedRowMixer (P : Matrix FourRowIndices FourRowIndices ℝ)
    (W : Matrix (Fin 3) (Fin 3) ℂ) : Matrix FourRowIndices FourRowIndices ℂ :=
  fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℂ) 0 0 W * Complex.ofRealHom.mapMatrix P

/-- A unitary with a real first row factors through a real orthogonal
completion of that row and a unitary on the other three rows. -/
theorem exists_fixedRowMixer (U : Matrix FourRowIndices FourRowIndices ℂ) (hU : IsUnitary U)
    (v : FourRowIndices → ℝ) (hv : ∀ j, U (Sum.inl 0) j = (v j : ℂ)) :
    ∃ (P : Matrix.orthogonalGroup FourRowIndices ℝ) (W : Matrix (Fin 3) (Fin 3) ℂ),
      IsUnitary W ∧ (∀ j, P.val (Sum.inl 0) j = v j) ∧ U = fixedRowMixer P.val W := by
  have hv1 : ∑ j, v j * v j = 1 := by
    have h := congrArg (fun M : Matrix FourRowIndices FourRowIndices ℂ => (M (Sum.inl 0) (Sum.inl 0)).re)
      hU.1
    change ((U * Uᴴ) (Sum.inl 0) (Sum.inl 0)).re =
      ((1 : Matrix FourRowIndices FourRowIndices ℂ) (Sum.inl 0) (Sum.inl 0)).re at h
    rw [Matrix.mul_apply, Complex.re_sum, Matrix.one_apply_eq, Complex.one_re] at h
    simpa [Matrix.conjTranspose_apply, hv, Complex.star_def, Complex.mul_re] using h
  obtain ⟨P, hProw⟩ := exists_orthogonal_row v hv1 (Sum.inl 0)
  let Q := Complex.ofRealHom.mapMatrix P.val
  have hQ : IsUnitary Q := isUnitary_ofReal_orthogonal P
  let C := U * Qᴴ
  have hC : IsUnitary C := unitary_product _ _ hU ⟨by simpa using hQ.2, by simpa using hQ.1⟩
  have hentry (j : FourRowIndices) : U (Sum.inl 0) j = Q (Sum.inl 0) j := by
    rw [hv]
    change (v j : ℂ) = (P.val (Sum.inl 0) j : ℂ)
    rw [hProw]
  have hrow (i : Fin 1) (j : FourRowIndices) :
      C (Sum.inl i) j = (1 : Matrix FourRowIndices FourRowIndices ℂ) (Sum.inl i) j := by
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    calc
      _ = (Q * Qᴴ) (Sum.inl 0) j := by simp only [C, Matrix.mul_apply, hentry]
      _ = _ := by rw [hQ.1]
  have hcol (i : FourRowIndices) (j : Fin 1) :
      C i (Sum.inl j) = (1 : Matrix FourRowIndices FourRowIndices ℂ) i (Sum.inl j) := by
    calc
      C i (Sum.inl j) = (C * Cᴴ) i (Sum.inl j) := by
        rw [Matrix.mul_apply]
        simp [Matrix.conjTranspose_apply, hrow, Matrix.one_apply, apply_ite]
      _ = _ := by rw [hC.1]
  let W := C.toBlocks₂₂
  have hblock : C = fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℂ) 0 0 W := by
    ext (i | i) (j | j)
    · change C (Sum.inl i) (Sum.inl j) = (1 : Matrix (Fin 1) (Fin 1) ℂ) i j
      simpa [Matrix.one_apply] using hrow i (Sum.inl j)
    · change C (Sum.inl i) (Sum.inr j) = 0
      simpa [Matrix.one_apply] using hrow i (Sum.inr j)
    · change C (Sum.inr i) (Sum.inl j) = 0
      simpa [Matrix.one_apply] using hcol (Sum.inr i) j
    · rfl
  have hW : IsUnitary W := ((unitary_directSum_iff (U := (1 : Matrix (Fin 1) (Fin 1) ℂ))
    (V := W)).mp (hblock ▸ hC)).2
  refine ⟨P, W, hW, hProw, ?_⟩
  change U = fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℂ) 0 0 W * Q
  rw [← hblock]
  change U = (U * Qᴴ) * Q
  rw [Matrix.mul_assoc, hQ.2, Matrix.mul_one]

private theorem fixedRowMixer_first (P : Matrix FourRowIndices FourRowIndices ℝ)
    (W : Matrix (Fin 3) (Fin 3) ℂ) (i : Fin 1) (j : FourRowIndices) :
    fixedRowMixer P W (Sum.inl i) j = (P (Sum.inl i) j : ℂ) := by
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  rw [fixedRowMixer, Matrix.mul_apply, Fintype.sum_sum_type]
  simp [Matrix.one_apply, RingHom.mapMatrix_apply, Matrix.map_apply, apply_ite]

private theorem fixedRowMixer_other (P : Matrix FourRowIndices FourRowIndices ℝ)
    (W : Matrix (Fin 3) (Fin 3) ℂ) (i : Fin 3) (j : FourRowIndices) :
    fixedRowMixer P W (Sum.inr i) j = ∑ k : Fin 3, (P (Sum.inr k) j : ℂ) * W i k := by
  rw [fixedRowMixer, Matrix.mul_apply, Fintype.sum_sum_type]
  simp only [Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, RingHom.mapMatrix_apply,
    Matrix.map_apply, Complex.ofRealHom_eq_coe, Matrix.zero_apply, zero_mul, Finset.sum_const_zero,
    zero_add]
  apply Finset.sum_congr rfl
  intro k _
  exact mul_comm _ _

/-- The singleton in a nonfixed row is the effect evaluated on the real
coordinates of the corresponding column. -/
theorem fixedRowMixer_singleton_effect (P : Matrix FourRowIndices FourRowIndices ℝ)
    (W : Matrix (Fin 3) (Fin 3) ℂ) (i : Fin 3) (j : FourRowIndices) :
    let v : Fin 3 → ℝ := fun k => P (Sum.inr k) j
    Complex.normSq (fixedRowMixer P W (Sum.inr i) j) = v ⬝ᵥ realRowEffects W i *ᵥ v := by
  dsimp only
  rw [fixedRowMixer_other, realRowEffects_quadratic]

/-- The determinant of an anchored two-minor pairs the second row with the
corresponding real wedge of the fixed row and the two chosen columns. -/
theorem fixedRowMixer_anchored_effect (P : Matrix FourRowIndices FourRowIndices ℝ)
    (W : Matrix (Fin 3) (Fin 3) ℂ) (i : Fin 3) (j l : FourRowIndices) :
    let v : Fin 3 → ℝ := fun k =>
      P (Sum.inl 0) j * P (Sum.inr k) l - P (Sum.inl 0) l * P (Sum.inr k) j
    let U := fixedRowMixer P W
    Complex.normSq (U (Sum.inl 0) j * U (Sum.inr i) l - U (Sum.inl 0) l * U (Sum.inr i) j) =
      v ⬝ᵥ realRowEffects W i *ᵥ v := by
  dsimp only
  rw [realRowEffects_quadratic, fixedRowMixer_first, fixedRowMixer_first,
    fixedRowMixer_other, fixedRowMixer_other, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply congrArg Complex.normSq
  apply Finset.sum_congr rfl
  intro k _
  push_cast
  ring

private def extendFixedRowOrthogonal (P : Matrix.orthogonalGroup FourRowIndices ℝ)
    (Q : Matrix.orthogonalGroup (Fin 3) ℝ) : Matrix.orthogonalGroup FourRowIndices ℝ := by
  let B := fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 0 Q.valᵀ
  have hQ : Q.valᵀ * Q.val = 1 := (Matrix.mem_orthogonalGroup_iff' _ ℝ).mp Q.property
  have hB : B * Bᵀ = 1 := by
    simp [B, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, hQ, Matrix.fromBlocks_one]
  have hP : P.val * P.valᵀ = 1 := (Matrix.mem_orthogonalGroup_iff _ ℝ).mp P.property
  have hBP : (B * P.val) * (B * P.val)ᵀ = 1 := calc
    _ = B * (P.val * P.valᵀ) * Bᵀ := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = 1 := by rw [hP, Matrix.mul_one, hB]
  exact ⟨B * P.val, (Matrix.mem_orthogonalGroup_iff _ ℝ).mpr hBP⟩

private theorem extendFixedRowOrthogonal_cast (P : Matrix.orthogonalGroup FourRowIndices ℝ)
    (Q : Matrix.orthogonalGroup (Fin 3) ℝ) :
    Complex.ofRealHom.mapMatrix (extendFixedRowOrthogonal P Q).val =
      fixedRowMixer P.val (Complex.ofRealHom.mapMatrix Q.valᵀ) := by
  change Complex.ofRealHom.mapMatrix
      (fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 0 Q.valᵀ * P.val) = _
  rw [map_mul, fixedRowMixer]
  congr 1
  ext (i | i) (j | j) <;> simp [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.one_apply, apply_ite]

private theorem realRowEffects_ofReal_transpose (Q : Matrix.orthogonalGroup (Fin 3) ℝ) :
    realRowEffects (Complex.ofRealHom.mapMatrix Q.valᵀ) = orthogonalBasisEffects Q := by
  funext i
  ext j k
  change (star (Q.val j i : ℂ) * (Q.val k i : ℂ)).re = Q.val j i * Q.val k i
  rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re]

private def evaluateEffect (i : Fin 3) (v : Fin 3 → ℝ) :
    (Fin 3 → Matrix (Fin 3) (Fin 3) ℝ) →ₗ[ℝ] ℝ where
  toFun E := v ⬝ᵥ E i *ᵥ v
  map_add' E F := by simp [Matrix.add_mulVec, dotProduct_add]
  map_smul' c E := by simp [Matrix.smul_mulVec_assoc, dotProduct_smul]

private theorem isUnitary_fixedRowMixer (P : Matrix.orthogonalGroup FourRowIndices ℝ)
    (W : Matrix (Fin 3) (Fin 3) ℂ) (hW : IsUnitary W) : IsUnitary (fixedRowMixer P.val W) := by
  unfold fixedRowMixer
  exact unitary_product _ _ (unitary_directSum (by simp [IsUnitary]) hW)
    (isUnitary_ofReal_orthogonal P)

/-- A real row-effect mixture with prescribed coefficients lifts to the
same mixture of all squared minors, with no increase in the number of terms. -/
theorem fixedRowMixer_minor_sum_of_effect_sum {κ : Type*} [Fintype κ]
    (P : Matrix.orthogonalGroup FourRowIndices ℝ)
    (W : Matrix (Fin 3) (Fin 3) ℂ) (hW : IsUnitary W)
    (w : κ → ℝ) (Q : κ → Matrix.orthogonalGroup (Fin 3) ℝ) (hs : ∑ k, w k = 1)
    (he : realRowEffects W =
      ∑ k, w k • realRowEffects (Complex.ofRealHom.mapMatrix (Q k).valᵀ)) :
    ∀ I J : Finset FourRowIndices, subsetMinorSq (fixedRowMixer P.val W) I J =
      ∑ k, w k * subsetMinorSq
        (Complex.ofRealHom.mapMatrix (extendFixedRowOrthogonal P (Q k)).val) I J := by
  classical
  let O (k : κ) := extendFixedRowOrthogonal P (Q k)
  let V (k : κ) := Complex.ofRealHom.mapMatrix (O k).val
  let W' (k : κ) := Complex.ofRealHom.mapMatrix (Q k).valᵀ
  let U := fixedRowMixer P.val W
  have hU : IsUnitary U := isUnitary_fixedRowMixer P W hW
  have hV (k : κ) : IsUnitary (V k) := isUnitary_ofReal_orthogonal (O k)
  have hV' (k : κ) : V k = fixedRowMixer P.val (W' k) := extendFixedRowOrthogonal_cast P (Q k)
  have hEval (i : Fin 3) (v : Fin 3 → ℝ) :
      (v ⬝ᵥ realRowEffects W i *ᵥ v) = ∑ k, w k * (v ⬝ᵥ realRowEffects (W' k) i *ᵥ v) := by
    have h := congrArg (evaluateEffect i v) he
    rw [map_sum] at h
    simp only [map_smul, smul_eq_mul] at h
    exact h
  change ∀ I J : Finset FourRowIndices, subsetMinorSq U I J = ∑ k, w k * subsetMinorSq (V k) I J
  apply squared_minor_mixture_of_anchor (r := Sum.inl 0)
    (by simp [FourRowIndices, Fintype.card_sum]) U hU V hV w hs
  · intro i j
    simp_rw [squared_minor_singleton U hU, fun k => squared_minor_singleton (V k) (hV k)]
    cases i with
    | inl i =>
        simp_rw [show U = fixedRowMixer P.val W from rfl, hV', fixedRowMixer_first]
        rw [← Finset.sum_mul, hs, one_mul]
    | inr i =>
        simp_rw [show U = fixedRowMixer P.val W from rfl, hV', fixedRowMixer_singleton_effect]
        exact hEval i _
  · intro i j l hi hj
    simp_rw [squared_minor_pair U hU hi hj, fun k => squared_minor_pair (V k) (hV k) hi hj]
    cases i with
    | inl i => exact False.elim (hi (congrArg Sum.inl (Subsingleton.elim _ _)))
    | inr i =>
        simp_rw [show U = fixedRowMixer P.val W from rfl, hV', fixedRowMixer_anchored_effect]
        exact hEval i _


/-- A fixed-row mixer and the real completions of its three-dimensional
effect mixture have the same convex combination for every squared minor. -/
theorem fixedRowMixer_minor_mixture (P : Matrix.orthogonalGroup FourRowIndices ℝ)
    (W : Matrix (Fin 3) (Fin 3) ℂ) (hW : IsUnitary W) :
    ∃ (κ : Type) (_ : Fintype κ) (w : κ → ℝ) (O : κ → Matrix.orthogonalGroup FourRowIndices ℝ),
      (∀ k, 0 ≤ w k) ∧ (∑ k, w k) = 1 ∧
      ∀ I J : Finset FourRowIndices, subsetMinorSq (fixedRowMixer P.val W) I J =
        ∑ k, w k * subsetMinorSq (Complex.ofRealHom.mapMatrix (O k).val) I J := by
  classical
  obtain ⟨κ, inst, w, z, hw, hs, hz, he⟩ :=
    mem_convexHull_iff_exists_fintype.mp (realRowEffects_mem_convexHull W hW)
  letI : Fintype κ := inst
  choose Q hQ using hz
  have hE (k : κ) : realRowEffects (Complex.ofRealHom.mapMatrix (Q k).valᵀ) = z k :=
    (realRowEffects_ofReal_transpose (Q k)).trans (hQ k)
  refine ⟨κ, inst, w, (fun k => extendFixedRowOrthogonal P (Q k)), hw, hs,
    fixedRowMixer_minor_sum_of_effect_sum P W hW w Q hs ?_⟩
  simpa only [hE] using he.symm

/-- Every order-four unitary minor table is a convex mixture of real
orthogonal minor tables, expressed on the one-plus-three row decomposition. -/
theorem fourRow_minor_mixture (U : Matrix FourRowIndices FourRowIndices ℂ) (hU : IsUnitary U) :
    ∃ (κ : Type) (_ : Fintype κ) (w : κ → ℝ) (O : κ → Matrix.orthogonalGroup FourRowIndices ℝ),
      (∀ k, 0 ≤ w k) ∧ (∑ k, w k) = 1 ∧
      ∀ I J : Finset FourRowIndices, subsetMinorSq U I J =
        ∑ k, w k * subsetMinorSq (Complex.ofRealHom.mapMatrix (O k).val) I J := by
  obtain ⟨V, hV, hrow, hminor⟩ := exists_unitary_with_real_row U hU (Sum.inl 0)
  obtain ⟨P, W, hW, _, hfac⟩ := exists_fixedRowMixer V hV (fun j => ‖U (Sum.inl 0) j‖) hrow
  obtain ⟨κ, inst, w, O, hw, hs, hm⟩ := fixedRowMixer_minor_mixture P W hW
  refine ⟨κ, inst, w, O, hw, hs, fun I J => ?_⟩
  rw [← hminor, hfac]
  exact hm I J

private theorem holds_of_finite_minor_mixture {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (V : κ → Matrix ι ι ℂ) (hV : ∀ k, IsUnitary (V k)) (w : κ → ℝ)
    (hw : ∀ k, 0 ≤ w k) (hs : ∑ k, w k = 1) (h : ∀ k, Holds a b (V k))
    (hm : ∀ I J : Finset ι, subsetMinorSq U I J = ∑ k, w k * subsetMinorSq (V k) I J) :
    Holds a b U := by
  have hdet : ∑ k, w k • determinantValue a b (V k) = determinantValue a b U := by
    simp_rw [determinantValue_eq_sum_subsetMinors a b U hU,
      fun k => determinantValue_eq_sum_subsetMinors a b (V k) (hV k), Complex.real_smul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro J _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro I _
    rw [hm I J, Complex.ofReal_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    rw [Complex.ofReal_mul, mul_assoc]
  rw [Holds, ← hdet]
  exact (convex_convexHull ℝ _).sum_mem (fun k _ => hw k) hs (fun k _ => h k)

private theorem holds_fourRow_of_orthogonal (h : OrthogonalConjecture FourRowIndices) :
    Conjecture FourRowIndices := by
  intro a b U hU
  obtain ⟨κ, inst, w, O, hw, hs, hm⟩ := fourRow_minor_mixture U hU
  letI : Fintype κ := inst
  exact holds_of_finite_minor_mixture a b U hU
    (fun k => Complex.ofRealHom.mapMatrix (O k).val)
    (fun k => isUnitary_ofReal_orthogonal (O k)) w hw hs (fun k => h a b (O k)) hm

private def mappedSubsetEquiv {ι κ : Type*} (e : κ ≃ ι) (I : Finset κ) :
    I ≃ (I.map e.toEmbedding : Finset ι) where
  toFun i := ⟨e i, Finset.mem_map.mpr ⟨i, i.property, rfl⟩⟩
  invFun j := ⟨e.symm j, Finset.mem_map_equiv.mp j.property⟩
  left_inv i := Subtype.ext (e.symm_apply_apply i)
  right_inv j := Subtype.ext (e.apply_symm_apply j)

/-- Reindexing the two bases transports the row and column sets of each squared minor. -/
theorem squared_minor_reindex {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (eRow eCol : κ ≃ ι) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (I J : Finset κ) :
    subsetMinorSq (U.submatrix eRow eCol) I J =
      subsetMinorSq U (I.map eRow.toEmbedding) (J.map eCol.toEmbedding) := by
  by_cases h : I.card = J.card
  · let f : I ≃ J := Fintype.equivOfCardEq (by simpa using h)
    rw [squared_minor_indexed _ (unitary_reindex eRow eCol hU) I J (Equiv.refl I) f,
      squared_minor_indexed U hU _ _ (mappedSubsetEquiv eRow I) (f.trans (mappedSubsetEquiv eCol J))] <;>
      rfl
  · have hmap : (I.map eRow.toEmbedding).card ≠ (J.map eCol.toEmbedding).card := by
      simpa only [Finset.card_map] using h
    rw [squared_minor_of_card_ne _ _ _ h, squared_minor_of_card_ne _ _ _ hmap]

private def orthogonal_reindex {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (e : κ ≃ ι) (O : Matrix.orthogonalGroup ι ℝ) :
    Matrix.orthogonalGroup κ ℝ := by
  let P := O.val.submatrix e e
  have hO : O.val * O.valᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp O.property
  have hP : P * Pᴴ = 1 := by
    dsimp only [P]
    rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, hO, Matrix.submatrix_one_equiv]
  exact ⟨P, Matrix.mem_unitaryGroup_iff.mpr hP⟩

/-- All squared minors of an order-four unitary are one finite convex combination
of real orthogonal squared-minor tables. The same weights work for every pair of subsets. -/
theorem four_minor_mixture (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    ∃ (κ : Type) (_ : Fintype κ) (w : κ → ℝ) (O : κ → Matrix.orthogonalGroup (Fin 4) ℝ),
      (∀ k, 0 ≤ w k) ∧ (∑ k, w k) = 1 ∧
      ∀ I J : Finset (Fin 4), subsetMinorSq U I J =
        ∑ k, w k * subsetMinorSq (Complex.ofRealHom.mapMatrix (O k).val) I J := by
  let e : FourRowIndices ≃ Fin 4 := finSumFinEquiv
  have hW := unitary_reindex e e hU
  obtain ⟨κ, inst, w, O, hw, hs, hm⟩ := fourRow_minor_mixture (U.submatrix e e) hW
  letI : Fintype κ := inst
  refine ⟨κ, inst, w, fun k => orthogonal_reindex e.symm (O k), hw, hs, fun I J => ?_⟩
  have hback : (U.submatrix e e).submatrix e.symm e.symm = U := by
    ext i j
    change U (e (e.symm i)) (e (e.symm j)) = U i j
    simp
  have hleft := squared_minor_reindex e.symm e.symm (U.submatrix e e) hW I J
  rw [hback] at hleft
  rw [hleft, hm]
  apply Finset.sum_congr rfl
  intro k _
  have hV := squared_minor_reindex e.symm e.symm _ (isUnitary_ofReal_orthogonal (O k)) I J
  exact congrArg (w k * ·) hV.symm


/-- A two-basis decomposition of every compressed row-effect triple
gives a two-point interpolation of the entire order-four minor table.
This is the realification step in Zheng's Theorem 1.2
(preprint DOI: 10.13140/RG.2.2.36790.25923). -/
theorem four_minor_two_point_of_two_basis_effects
    (heffects : ∀ W : Matrix (Fin 3) (Fin 3) ℂ, IsUnitary W →
      ∃ (Q₀ Q₁ : Matrix.orthogonalGroup (Fin 3) ℝ) (θ : ℝ), 0 ≤ θ ∧ θ ≤ 1 ∧
        realRowEffects W = θ • orthogonalBasisEffects Q₀ + (1 - θ) • orthogonalBasisEffects Q₁)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    ∃ (O₀ O₁ : Matrix.orthogonalGroup (Fin 4) ℝ) (θ : ℝ), 0 ≤ θ ∧ θ ≤ 1 ∧
      ∀ I J : Finset (Fin 4), subsetMinorSq U I J =
        θ * subsetMinorSq (Complex.ofRealHom.mapMatrix O₀.val) I J +
        (1 - θ) * subsetMinorSq (Complex.ofRealHom.mapMatrix O₁.val) I J := by
  let e : FourRowIndices ≃ Fin 4 := finSumFinEquiv
  let A := U.submatrix e e
  have hA := unitary_reindex e e hU
  obtain ⟨V,hV,hrow,hminor⟩ := exists_unitary_with_real_row A hA (Sum.inl 0)
  obtain ⟨P,W,hW,_,hfac⟩ := exists_fixedRowMixer V hV (fun j => ‖A (Sum.inl 0) j‖) hrow
  obtain ⟨Q₀,Q₁,θ,hθ₀,hθ₁,hE⟩ := heffects W hW
  let B₀ := extendFixedRowOrthogonal P Q₀
  let B₁ := extendFixedRowOrthogonal P Q₁
  let w : Fin 2 → ℝ := ![θ,1-θ]
  let Q : Fin 2 → Matrix.orthogonalGroup (Fin 3) ℝ := ![Q₀,Q₁]
  have hs : ∑ i, w i = 1 := by simp [w, Fin.sum_univ_two]
  have he : realRowEffects W =
      ∑ i, w i • realRowEffects (Complex.ofRealHom.mapMatrix (Q i).valᵀ) := by
    simpa only [Fin.sum_univ_two, w, Q, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, realRowEffects_ofReal_transpose] using hE
  have hm (I J : Finset FourRowIndices) : subsetMinorSq A I J =
      θ * subsetMinorSq (Complex.ofRealHom.mapMatrix B₀.val) I J +
      (1-θ) * subsetMinorSq (Complex.ofRealHom.mapMatrix B₁.val) I J := by
    rw [← hminor, hfac]
    simpa only [Fin.sum_univ_two, w, Q, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, B₀, B₁] using fixedRowMixer_minor_sum_of_effect_sum P W hW w Q hs he I J
  refine ⟨orthogonal_reindex e.symm B₀, orthogonal_reindex e.symm B₁, θ, hθ₀,hθ₁,fun I J => ?_⟩
  have hback : A.submatrix e.symm e.symm = U := by ext i j; simp [A, Matrix.submatrix_apply]
  have hleft := squared_minor_reindex e.symm e.symm A hA I J
  rw [hback] at hleft
  rw [hleft, hm]
  have hr (O : Matrix.orthogonalGroup FourRowIndices ℝ) :
      subsetMinorSq (Complex.ofRealHom.mapMatrix (orthogonal_reindex e.symm O).val) I J =
        subsetMinorSq (Complex.ofRealHom.mapMatrix O.val) (I.map e.symm.toEmbedding) (J.map e.symm.toEmbedding) :=
    squared_minor_reindex e.symm e.symm _ (isUnitary_ofReal_orthogonal O) I J
  rw [hr B₀, hr B₁]

/-- Zheng's exact two-orthogonal interpolation of squared minor tables
(Theorem 1.2, preprint DOI: 10.13140/RG.2.2.36790.25923). This proof
uses real three-effect decomposition instead of the elliptic/Gale route. -/
theorem four_minor_two_point (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    ∃ (O₀ O₁ : Matrix.orthogonalGroup (Fin 4) ℝ) (θ : ℝ), 0 ≤ θ ∧ θ ≤ 1 ∧
      ∀ I J : Finset (Fin 4), subsetMinorSq U I J =
        θ * subsetMinorSq (Complex.ofRealHom.mapMatrix O₀.val) I J +
        (1 - θ) * subsetMinorSq (Complex.ofRealHom.mapMatrix O₁.val) I J :=
  four_minor_two_point_of_two_basis_effects realRowEffects_two_bases U hU

private theorem orthogonalConjecture_of_reindex {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (e : κ ≃ ι) (h : OrthogonalConjecture ι) :
    OrthogonalConjecture κ := by
  intro a b O
  let Q := orthogonal_reindex e.symm O
  have hminor := (holds_reindex_iff e e (a ∘ e.symm) (b ∘ e.symm)
    (Complex.ofRealHom.mapMatrix Q.val)).mpr (h _ _ Q)
  have ha : (a ∘ e.symm) ∘ e = a := by funext i; simp
  have hb : (b ∘ e.symm) ∘ e = b := by funext i; simp
  have hmat : (Complex.ofRealHom.mapMatrix Q.val).submatrix e e = Complex.ofRealHom.mapMatrix O.val := by
    ext i j
    change (O.val (e.symm (e i)) (e.symm (e j)) : ℂ) = (O.val i j : ℂ)
    simp
  simpa only [ha, hb, hmat] using hminor

/-- In order four it suffices to prove the inclusion for real orthogonal
relative eigenbases. The spectra remain arbitrary and complex. -/
theorem conjecture_four_iff_orthogonal : Conjecture (Fin 4) ↔ OrthogonalConjecture (Fin 4) := by
  constructor
  · intro h a b O
    exact h a b _ (isUnitary_ofReal_orthogonal O)
  · intro h
    let e : FourRowIndices ≃ Fin 4 := finSumFinEquiv
    exact (conjecture_reindex_iff e).mp
      (holds_fourRow_of_orthogonal (orthogonalConjecture_of_reindex e h))

end

end MOC
