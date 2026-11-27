import MOC.Singular
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.PosDef

open BigOperators Matrix
open scoped ComplexInnerProductSpace ComplexOrder

namespace MOC

noncomputable section

private theorem exists_linearIsometry_of_equal_norms
    {D E : Type*} [AddCommGroup D] [Module ℂ D]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (A B : D →ₗ[ℂ] E) (hn : ∀ v, ‖A v‖ = ‖B v‖) :
    ∃ L : E →ₗᵢ[ℂ] E, ∀ v, L (A v) = B v := by
  have hker : LinearMap.ker A ≤ LinearMap.ker B := by
    intro v hv
    have he := hn v
    rw [LinearMap.mem_ker.mp hv, norm_zero, eq_comm, norm_eq_zero] at he
    exact LinearMap.mem_ker.mpr he
  let M : LinearMap.range A →ₗ[ℂ] E :=
    ((LinearMap.ker A).liftQ B hker).comp A.quotKerEquivRange.symm.toLinearMap
  have hM (v : D) : M ⟨A v, LinearMap.mem_range_self A v⟩ = B v := by
    change (LinearMap.ker A).liftQ B hker (A.quotKerEquivRange.symm _) = _
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  let L : LinearMap.range A →ₗᵢ[ℂ] E :=
    { toLinearMap := M
      norm_map' := by
        rintro ⟨u, v, rfl⟩
        rw [show M ⟨A v, LinearMap.mem_range_self A v⟩ = B v from hM v]
        exact (hn v).symm }
  exact ⟨L.extend, fun v => (L.extend_apply ⟨A v, LinearMap.mem_range_self A v⟩).trans (hM v)⟩

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Rectangular complex matrices with equal column Gram matrices differ
by a unitary on the common ambient space. -/
theorem exists_unitary_mul_eq_of_conjTranspose_mul_eq (A B : Matrix ι κ ℂ)
    (h : Aᴴ * A = Bᴴ * B) :
    ∃ U : Matrix ι ι ℂ, IsUnitary U ∧ U * A = B := by
  let T := (WithLp.equiv 2 (ι → ℂ)).symm
  let E := EuclideanSpace ℂ ι
  let L₁ : (κ → ℂ) →ₗ[ℂ] E :=
    (WithLp.linearEquiv 2 ℂ (ι → ℂ)).symm.toLinearMap.comp A.toLin'
  let L₂ : (κ → ℂ) →ₗ[ℂ] E :=
    (WithLp.linearEquiv 2 ℂ (ι → ℂ)).symm.toLinearMap.comp B.toLin'
  have hL₁ (v : κ → ℂ) : L₁ v = T (A *ᵥ v) := by
    change T (A.toLin' v) = T (A *ᵥ v)
    rw [Matrix.toLin'_apply]
  have hL₂ (v : κ → ℂ) : L₂ v = T (B *ᵥ v) := by
    change T (B.toLin' v) = T (B *ᵥ v)
    rw [Matrix.toLin'_apply]
  have hi (a b : ι → ℂ) : ⟪T a, T b⟫ = star a ⬝ᵥ b :=
    (EuclideanSpace.inner_piLp_equiv_symm a b).trans (dotProduct_comm _ _)
  have hq (C : Matrix ι κ ℂ) (v : κ → ℂ) :
      star (C *ᵥ v) ⬝ᵥ (C *ᵥ v) = (star v ᵥ* (Cᴴ * C)) ⬝ᵥ v := by
    rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
  have hn (v : κ → ℂ) : ‖L₁ v‖ = ‖L₂ v‖ := by
    rw [hL₁, hL₂, norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ),
      hi, hi, hq, hq, h]
  obtain ⟨L, hL⟩ := exists_linearIsometry_of_equal_norms L₁ L₂ hn
  let e := LinearIsometryEquiv.ofSurjective L
    (LinearMap.surjective_of_injective (f := L.toLinearMap) L.injective)
  let b := EuclideanSpace.basisFun ι ℂ
  let U := LinearMap.toMatrix b.toBasis b.toBasis L.toLinearMap
  have hmat : U = b.toBasis.toMatrix (b.map e) := by
    ext i j
    rw [show U = LinearMap.toMatrix b.toBasis b.toBasis L.toLinearMap from rfl,
      LinearMap.toMatrix_apply, Basis.toMatrix_apply] <;> rfl
  have hU : U ∈ Matrix.unitaryGroup ι ℂ := by
    rw [hmat]
    exact b.toMatrix_orthonormalBasis_mem_unitary (b.map e)
  have hrepr (w : E) : (b.toBasis.repr w : ι → ℂ) = WithLp.equiv 2 (ι → ℂ) w := by
    funext i
    exact b.coe_toBasis_repr_apply w i
  have hmul (v : κ → ℂ) : U *ᵥ (A *ᵥ v) = B *ᵥ v := by
    have hL' := hL v
    rw [hL₁, hL₂] at hL'
    have hm := L.toLinearMap.toMatrix_mulVec_repr b.toBasis b.toBasis (T (A *ᵥ v))
    change U *ᵥ (b.toBasis.repr (T (A *ᵥ v)) : ι → ℂ) =
      (b.toBasis.repr (L (T (A *ᵥ v))) : ι → ℂ) at hm
    rw [hL', hrepr, hrepr] at hm
    exact hm
  refine ⟨U, ⟨Matrix.mem_unitaryGroup_iff.mp hU, Matrix.mem_unitaryGroup_iff'.mp hU⟩, ?_⟩
  ext i j
  have hm := congrFun (hmul (Pi.single j 1)) i
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at hm
  exact hm

/-- The first and second spectral moments of an orthonormal frame. -/
def matrixSpectralMomentPair (a : ι → ℂ) (X : Matrix ι κ ℂ) :
    Matrix κ κ ℂ × Matrix κ κ ℂ :=
  (Xᴴ * (diagonal a * X), Xᴴ * (diagonal (fun i => (Complex.normSq (a i) : ℂ)) * X))

/-- Matrix-valued spectral moments of all orthonormal frames. -/
def matrixSpectralMomentSet (a : ι → ℂ) : Set (Matrix κ κ ℂ × Matrix κ κ ℂ) :=
  {m | ∃ X : Matrix ι κ ℂ, Xᴴ * X = 1 ∧ matrixSpectralMomentPair a X = m}

private theorem matrixSpectralMomentPair_snd_eq_gram (a : ι → ℂ) (X : Matrix ι κ ℂ) :
    (matrixSpectralMomentPair a X).2 = (diagonal a * X)ᴴ * (diagonal a * X) := by
  have hdiag : (diagonal a)ᴴ * diagonal a =
      diagonal (fun i => (Complex.normSq (a i) : ℂ)) := by
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    exact congrArg Matrix.diagonal (funext fun i =>
      (Complex.normSq_eq_conj_mul_self (z := a i)).symm)
  change Xᴴ * (diagonal (fun i => (Complex.normSq (a i) : ℂ)) * X) = _
  rw [Matrix.conjTranspose_mul, ← hdiag]
  simp only [Matrix.mul_assoc]

private theorem frame_gram_eq_fromCols_iff (a c : ι → ℂ) (X Y : Matrix ι κ ℂ)
    (hX : Xᴴ * X = 1) (hY : Yᴴ * Y = 1) :
    (fromCols X (diagonal a * X))ᴴ * fromCols X (diagonal a * X) =
      (fromCols Y (diagonal c * Y))ᴴ * fromCols Y (diagonal c * Y) ↔
      matrixSpectralMomentPair a X = matrixSpectralMomentPair c Y := by
  simp only [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
    Matrix.fromRows_mul_fromCols, Matrix.fromBlocks_inj, hX, hY, true_and]
  constructor
  · rintro ⟨hfirst, _, hsecond⟩
    exact Prod.ext hfirst (by rwa [matrixSpectralMomentPair_snd_eq_gram,
      matrixSpectralMomentPair_snd_eq_gram])
  · intro h
    have hfirst := congrArg Prod.fst h
    change Xᴴ * (diagonal a * X) = Yᴴ * (diagonal c * Y) at hfirst
    refine ⟨hfirst, ?_, ?_⟩
    · simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] using
        congrArg Matrix.conjTranspose hfirst
    · have hs := congrArg Prod.snd h
      rwa [matrixSpectralMomentPair_snd_eq_gram, matrixSpectralMomentPair_snd_eq_gram] at hs

/-- The two matrix moment sets intersect exactly when a unitary can give
the indicated kernel frame in the difference of the two diagonal orbits. -/
theorem exists_unitary_kernelFrame_iff_inter_matrixSpectralMomentSets
    (a c : ι → ℂ) :
    (∃ (U : Matrix ι ι ℂ) (X : Matrix ι κ ℂ), IsUnitary U ∧ Xᴴ * X = 1 ∧
      (diagonal a - U * diagonal c * Uᴴ) * X = 0) ↔
      (matrixSpectralMomentSet (κ := κ) a ∩ matrixSpectralMomentSet c).Nonempty := by
  constructor
  · rintro ⟨U, X, hU, hX, hk⟩
    let Y := Uᴴ * X
    have hY : Yᴴ * Y = 1 := by
      rw [show Yᴴ = Xᴴ * U by simp only [Y, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose], Matrix.mul_assoc, ← Matrix.mul_assoc U Uᴴ,
        hU.1, Matrix.one_mul, hX]
    have hUY : U * Y = X := by rw [show Y = Uᴴ * X from rfl, ← Matrix.mul_assoc, hU.1, Matrix.one_mul]
    have hUC : U * (diagonal c * Y) = diagonal a * X := by
      exact (sub_eq_zero.mp (by simpa only [Y, Matrix.sub_mul, Matrix.mul_assoc] using hk)).symm
    have hM : U * fromCols Y (diagonal c * Y) = fromCols X (diagonal a * X) := by
      rw [Matrix.mul_fromCols, hUY, hUC]
    have hg := congrArg (fun Z : Matrix ι (κ ⊕ κ) ℂ => Zᴴ * Z) hM
    change (U * fromCols Y (diagonal c * Y))ᴴ * (U * fromCols Y (diagonal c * Y)) =
      (fromCols X (diagonal a * X))ᴴ * fromCols X (diagonal a * X) at hg
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U,
      hU.2, Matrix.one_mul] at hg
    have hm := (frame_gram_eq_fromCols_iff a c X Y hX hY).mp hg.symm
    exact ⟨matrixSpectralMomentPair a X, ⟨X, hX, rfl⟩, ⟨Y, hY, hm.symm⟩⟩
  · rintro ⟨m, ⟨X, hX, hXm⟩, ⟨Y, hY, hYm⟩⟩
    have hg := (frame_gram_eq_fromCols_iff a c X Y hX hY).mpr (hXm.trans hYm.symm)
    obtain ⟨U, hU, hM⟩ := exists_unitary_mul_eq_of_conjTranspose_mul_eq _ _ hg.symm
    rw [Matrix.mul_fromCols] at hM
    have hUY : U * Y = X := by simpa only [Matrix.toCols₁_fromCols] using congrArg Matrix.toCols₁ hM
    have hUC : U * (diagonal c * Y) = diagonal a * X := by
      simpa only [Matrix.toCols₂_fromCols] using congrArg Matrix.toCols₂ hM
    have hUX : Uᴴ * X = Y := by rw [← hUY, ← Matrix.mul_assoc, hU.2, Matrix.one_mul]
    refine ⟨U, X, hU, hX, ?_⟩
    simp only [Matrix.sub_mul, Matrix.mul_assoc, hUX, hUC, sub_self]

/-- A kernel contains a frame with `k` orthonormal columns exactly when
its complex dimension is at least `k`. -/
theorem le_finrank_ker_toEuclideanLin_iff (M : Matrix ι ι ℂ) (k : ℕ) :
    k ≤ Module.finrank ℂ (LinearMap.ker M.toEuclideanLin) ↔
      ∃ X : Matrix ι (Fin k) ℂ, Xᴴ * X = 1 ∧ M * X = 0 := by
  let L := M.toEuclideanLin
  change k ≤ Module.finrank ℂ (LinearMap.ker L) ↔ _
  constructor
  · intro hk
    let b := stdOrthonormalBasis ℂ (LinearMap.ker L)
    let e : Fin k ↪ Fin (Module.finrank ℂ (LinearMap.ker L)) := Fin.castLEEmb hk
    let X : Matrix ι (Fin k) ℂ := Matrix.of fun i j => WithLp.equiv 2 _ (b (e j)).val i
    refine ⟨X, ?_, ?_⟩
    · ext i j
      have h : ⟪(b (e i)).val, (b (e j)).val⟫ = (if i = j then 1 else 0) := by
        simpa only [e.injective.eq_iff] using orthonormal_iff_ite.mp b.orthonormal (e i) (e j)
      rw [Matrix.one_apply, ← h]
      rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
      rfl
    · ext i j
      have h := congrArg (fun v : EuclideanSpace ℂ ι => WithLp.equiv 2 (ι → ℂ) v i)
        (LinearMap.mem_ker.mp (b (e j)).property)
      simpa only [L, Matrix.piLp_equiv_toEuclideanLin_apply] using h
  · rintro ⟨X, hX, hMX⟩
    let F := X.toEuclideanLin
    have hF (v : EuclideanSpace ℂ (Fin k)) : F v ∈ LinearMap.ker L := by
      apply LinearMap.mem_ker.mpr
      apply (WithLp.equiv 2 (ι → ℂ)).injective
      change WithLp.equiv 2 (ι → ℂ) (L (F v)) = 0
      simp only [L, F, Matrix.piLp_equiv_toEuclideanLin_apply, Matrix.mulVec_mulVec,
        hMX, Matrix.zero_mulVec]
    have hFi : Function.Injective F := by
      intro u v huv
      apply (WithLp.equiv 2 (Fin k → ℂ)).injective
      have hc := congrArg (fun w => Xᴴ *ᵥ WithLp.equiv 2 (ι → ℂ) w) huv
      simpa only [F, Matrix.piLp_equiv_toEuclideanLin_apply, Matrix.mulVec_mulVec,
        hX, Matrix.one_mulVec] using hc
    let G := F.codRestrict (LinearMap.ker L) hF
    have hGi : Function.Injective G := fun u v h =>
      hFi (congrArg Subtype.val h)
    simpa only [finrank_euclideanSpace, Fintype.card_fin] using
      (LinearMap.finrank_le_finrank_of_injective hGi)

/-- The attainable rank-defect bound is equivalent to intersection of the
matrix-valued moment sets for the first spectrum and the reflected second spectrum. -/
theorem exists_unitary_rankDefect_iff_inter_matrixSpectralMomentSets
    (a b : ι → ℂ) (k : ℕ) :
    (∃ U : Matrix ι ι ℂ, IsUnitary U ∧
      k ≤ Module.finrank ℂ (LinearMap.ker ((diagonal a + U * diagonal b * Uᴴ).toEuclideanLin))) ↔
    (matrixSpectralMomentSet (κ := Fin k) a ∩ matrixSpectralMomentSet (fun i => -b i)).Nonempty := by
  have hdiff (U : Matrix ι ι ℂ) :
      diagonal a - U * diagonal (fun i => -b i) * Uᴴ =
        diagonal a + U * diagonal b * Uᴴ := by
    rw [← Matrix.diagonal_neg b, Matrix.mul_neg U (diagonal b),
      Matrix.neg_mul (U * diagonal b) Uᴴ, sub_neg_eq_add]
  rw [← exists_unitary_kernelFrame_iff_inter_matrixSpectralMomentSets]
  constructor
  · rintro ⟨U, hU, hk⟩
    obtain ⟨X, hX, hkX⟩ := (le_finrank_ker_toEuclideanLin_iff _ k).mp hk
    refine ⟨U, X, hU, hX, ?_⟩
    rw [hdiff U]
    exact hkX
  · rintro ⟨U, X, hU, hX, hkX⟩
    rw [hdiff U] at hkX
    exact ⟨U, hU, (le_finrank_ker_toEuclideanLin_iff _ k).mpr ⟨X, hX, hkX⟩⟩

private theorem posSemidef_rank_le_one_iff_outer (E : Matrix κ κ ℂ) :
    E.PosSemidef ∧ E.rank ≤ 1 ↔ ∃ v : κ → ℂ, E = vecMulVec (star v) v := by
  classical
  constructor
  · rintro ⟨hE, hrank⟩
    let eigenvalue := hE.1.eigenvalues
    let V : Matrix κ κ ℂ := hE.1.eigenvectorUnitary
    have hV (j l : κ) : E j l = ∑ i, V j i * (eigenvalue i : ℂ) * star (V l i) := by
      have he : E = V * diagonal (fun i => (eigenvalue i : ℂ)) * Vᴴ := by
        simpa only [Matrix.star_eq_conjTranspose] using hE.1.spectral_theorem
      calc
        _ = (V * diagonal (fun i => (eigenvalue i : ℂ)) * Vᴴ) j l := congrArg (fun A => A j l) he
        _ = _ := by
          rw [Matrix.mul_apply]
          simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
    by_cases h : ∃ i, eigenvalue i ≠ 0
    · obtain ⟨i, hi⟩ := h
      have hs : Subsingleton {j // eigenvalue j ≠ 0} :=
        Fintype.card_le_one_iff_subsingleton.mp (by rwa [← hE.1.rank_eq_card_non_zero_eigs])
      have hz (j : κ) (hj : j ≠ i) : eigenvalue j = 0 := by
        by_contra hnonzero
        exact hj (congrArg Subtype.val (hs.elim (⟨j, hnonzero⟩ : {l // eigenvalue l ≠ 0}) ⟨i, hi⟩))
      let r : ℝ := Real.sqrt (eigenvalue i)
      let v (j : κ) : ℂ := (r : ℂ) * star (V j i)
      have hr : (r : ℂ) * (r : ℂ) = (eigenvalue i : ℂ) := by
        rw [← Complex.ofReal_mul, ← pow_two, Real.sq_sqrt (hE.eigenvalues_nonneg i)]
      refine ⟨v, ?_⟩
      ext j l
      rw [hV, Finset.sum_eq_single i]
      · simp only [Matrix.vecMulVec_apply, Pi.star_apply, v, Complex.star_def, map_mul,
          Complex.conj_ofReal, Complex.conj_conj]
        calc
          _ = (r : ℂ) * (r : ℂ) * (V j i * (starRingEnd ℂ) (V l i)) := by rw [hr]; ring
          _ = _ := by ring
      · intro u _ hui
        simp [hz u hui]
      · simp
    · push_neg at h
      refine ⟨0, ?_⟩
      ext j l
      simp [hV, h, Matrix.vecMulVec_apply]
  · rintro ⟨v, rfl⟩
    let R : Matrix (Fin 1) κ ℂ := Matrix.of fun _ j => v j
    have hR : Rᴴ * R = vecMulVec (star v) v := by
      ext j l
      simp only [Matrix.mul_apply, Fin.sum_univ_one, Matrix.conjTranspose_apply,
        Matrix.vecMulVec_apply, Pi.star_apply, R, Matrix.of_apply]
    rw [← hR]
    refine ⟨Matrix.posSemidef_conjTranspose_mul_self R, ?_⟩
    exact (Matrix.rank_mul_le_left Rᴴ R).trans (by simpa using Matrix.rank_le_card_width Rᴴ)

private theorem sum_smul_rowOuter_eq_compression (X : Matrix ι κ ℂ) (w : ι → ℂ) :
    (∑ i, w i • vecMulVec (star (X i)) (X i)) = Xᴴ * (diagonal w * X) := by
  ext j l
  rw [Matrix.mul_apply]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply,
    Matrix.conjTranspose_apply, Pi.star_apply, Matrix.diagonal_mul]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

private theorem sum_rowOuter_eq_gram (X : Matrix ι κ ℂ) :
    (∑ i, vecMulVec (star (X i)) (X i)) = Xᴴ * X := by
  simpa only [one_smul, Matrix.diagonal_one, Matrix.one_mul] using
    sum_smul_rowOuter_eq_compression X (fun _ => 1)

/-- A frame moment pair is exactly a pair of moments of positive semidefinite
effects of rank at most one that sum to the identity. -/
theorem mem_matrixSpectralMomentSet_iff_effects (a : ι → ℂ) (m : Matrix κ κ ℂ × Matrix κ κ ℂ) :
    m ∈ matrixSpectralMomentSet a ↔
      ∃ E : ι → Matrix κ κ ℂ, (∀ i, (E i).PosSemidef ∧ (E i).rank ≤ 1) ∧
        (∑ i, E i) = 1 ∧
        (∑ i, a i • E i) = m.1 ∧ (∑ i, (Complex.normSq (a i) : ℂ) • E i) = m.2 := by
  constructor
  · rintro ⟨X, hX, hm⟩
    let E (i : ι) : Matrix κ κ ℂ := vecMulVec (star (X i)) (X i)
    refine ⟨E, (fun i => (posSemidef_rank_le_one_iff_outer (E i)).mpr ⟨X i, rfl⟩),
      (sum_rowOuter_eq_gram X).trans hX, ?_, ?_⟩
    · exact (sum_smul_rowOuter_eq_compression X a).trans (congrArg Prod.fst hm)
    · exact (sum_smul_rowOuter_eq_compression X (fun i => (Complex.normSq (a i) : ℂ))).trans
        (congrArg Prod.snd hm)
  · rintro ⟨E, hE, hsum, h₁, h₂⟩
    choose v hv using fun i => (posSemidef_rank_le_one_iff_outer (E i)).mp (hE i)
    let X : Matrix ι κ ℂ := Matrix.of v
    have hX (i : ι) : E i = vecMulVec (star (X i)) (X i) := hv i
    simp only [hX] at hsum h₁ h₂
    refine ⟨X, (sum_rowOuter_eq_gram X).symm.trans hsum, Prod.ext ?_ ?_⟩
    · exact (sum_smul_rowOuter_eq_compression X a).symm.trans h₁
    · exact (sum_smul_rowOuter_eq_compression X (fun i => (Complex.normSq (a i) : ℂ))).symm.trans h₂

end

end MOC
