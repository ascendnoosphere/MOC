import MOC.Realification
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.FinCases

/-! Linear algebra for the fixed-row realification in dimension four. -/

open BigOperators Matrix Module.End

namespace MOC

noncomputable section

/-- Column phases make a prescribed row real and nonnegative while preserving
the squared modulus of every minor. -/
theorem exists_unitary_with_real_row {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) (r : ι) :
    ∃ V : Matrix ι ι ℂ, IsUnitary V ∧ (∀ j, V r j = (‖U r j‖ : ℂ)) ∧
      ∀ I J : Finset ι, subsetMinorSq V I J = subsetMinorSq U I J := by
  let p (j : ι) : ℂ := if U r j = 0 then 1 else star (U r j) / (‖U r j‖ : ℂ)
  let V := U * diagonal p
  have hp (j : ι) : Complex.normSq (p j) = 1 := by
    by_cases h : U r j = 0
    · simp [p, h]
    · rw [show p j = _ from if_neg h, Complex.normSq_div, Complex.star_def,
        Complex.normSq_conj, Complex.normSq_ofReal, ← pow_two, ← Complex.normSq_eq_norm_sq]
      exact div_self (Complex.normSq_pos.mpr h).ne'
  have hstar (j : ι) : p j * star (p j) = 1 := by
    rw [Complex.star_def, Complex.mul_conj, hp, Complex.ofReal_one]
  have hD : diagonal p * (diagonal p)ᴴ = 1 := by
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    exact congrArg Matrix.diagonal (funext hstar)
  refine ⟨V, ?_, ?_, ?_⟩
  · have hVV : V * Vᴴ = 1 := by
      dsimp only [V]
      rw [Matrix.conjTranspose_mul, Matrix.mul_assoc U, ← Matrix.mul_assoc (diagonal p), hD,
        Matrix.one_mul, hU.1]
    exact ⟨hVV, Matrix.mul_eq_one_comm.mp hVV⟩
  · intro j
    rw [show V r j = (U * diagonal p) r j from rfl, Matrix.mul_diagonal]
    by_cases h : U r j = 0
    · simp [h]
    · have hn : (‖U r j‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr h)
      rw [show p j = _ from if_neg h, ← mul_div_assoc, Complex.star_def, Complex.mul_conj,
        Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
      exact (div_eq_iff hn).mpr (pow_two _)
  · intro I J
    by_cases h : I.card = J.card
    · simp only [subsetMinorSq, dif_pos h]
      let e : I ≃ J := Fintype.equivOfCardEq (by simpa using h)
      let S := U.submatrix (fun i : I => (i : ι)) (fun i : I => ((e i : J) : ι))
      let q (i : I) := p ((e i : J) : ι)
      have hS : V.submatrix (fun i : I => (i : ι)) (fun i : I => ((e i : J) : ι)) =
          S * diagonal q := by
        ext i j
        simp [V, S, q, Matrix.mul_diagonal]
      change Complex.normSq (V.submatrix _ (fun i : I => ((e i : J) : ι))).det =
        Complex.normSq S.det
      rw [hS, Matrix.det_mul, Complex.normSq_mul, Matrix.det_diagonal, map_prod]
      simp [q, hp]
    · simp [subsetMinorSq, h]

/-- A rank-one positive semidefinite effect of trace one is a projection. -/
theorem effect_rank_one_mul_self {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.PosSemidef) (hrank : A.rank = 1) (htrace : A.trace = 1) :
    A * A = A := by
  classical
  let eig := hA.isHermitian.eigenvalues
  let V := hA.isHermitian.eigenvectorUnitary
  let P : Matrix ι ι ℝ := V
  have hV : star P * P = 1 := Matrix.mem_unitaryGroup_iff'.mp V.property
  have hdiag : A = P * diagonal eig * star P := by
    simpa [P, V, eig, RCLike.ofReal_real_eq_id] using hA.isHermitian.spectral_theorem
  have hsum : ∑ i, eig i = 1 := by
    rw [← htrace, hdiag, Matrix.trace_mul_cycle, hV, Matrix.one_mul, Matrix.trace_diagonal]
  have hcard : Fintype.card {i // eig i ≠ 0} = 1 :=
    hA.isHermitian.rank_eq_card_non_zero_eigs.symm.trans hrank
  obtain ⟨i, hi⟩ := Fintype.card_eq_one_iff.mp hcard
  have hzero (j : ι) (hj : j ≠ i.val) : eig j = 0 := by
    by_contra hn
    exact hj (congrArg Subtype.val (hi ⟨j, hn⟩))
  have hone : eig i.val = 1 := by
    rwa [Finset.sum_eq_single_of_mem i.val (Finset.mem_univ _) (fun j _ hj => hzero j hj)] at hsum
  have hsquare : diagonal eig * diagonal eig = diagonal eig := by
    rw [Matrix.diagonal_mul_diagonal]
    apply congrArg Matrix.diagonal
    funext j
    by_cases hj : j = i.val
    · simp [hj, hone]
    · simp [hzero j hj]
  calc
    A * A = P * diagonal eig * (star P * P) * diagonal eig * star P := by
      rw [hdiag]
      simp only [Matrix.mul_assoc]
    _ = A := by
      rw [hV, Matrix.mul_one, Matrix.mul_assoc P, hsquare, ← hdiag]

/-- The other two positive effects annihilate the range of a projection
in a decomposition of the identity. -/
theorem effects_mul_projection_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B C : Matrix ι ι ℝ) (hProj : A * A = A) (hB : B.PosSemidef) (hC : C.PosSemidef)
    (hsum : A + B + C = 1) : B * A = 0 ∧ C * A = 0 := by
  have hBC : B + C = 1 - A := (eq_sub_iff_add_eq).mpr (by
    simpa [add_comm, add_left_comm, add_assoc] using hsum)
  have hperp (x : ι → ℝ) : B *ᵥ (A *ᵥ x) = 0 ∧ C *ᵥ (A *ᵥ x) = 0 := by
    let y := A *ᵥ x
    have hkill : (B + C) *ᵥ y = 0 := by
      rw [hBC, Matrix.sub_mulVec, Matrix.one_mulVec]
      dsimp only [y]
      rw [Matrix.mulVec_mulVec, hProj, sub_self]
    have hzero := congrArg (dotProduct (star y)) hkill
    rw [Matrix.add_mulVec, dotProduct_add, dotProduct_zero] at hzero
    have hbpos : 0 ≤ star y ⬝ᵥ B *ᵥ y := hB.2 y
    have hcpos : 0 ≤ star y ⬝ᵥ C *ᵥ y := hC.2 y
    exact ⟨(hB.dotProduct_mulVec_zero_iff y).mp (by linarith only [hzero, hbpos, hcpos]),
      (hC.dotProduct_mulVec_zero_iff y).mp (by linarith only [hzero, hbpos, hcpos])⟩
  constructor <;> apply Matrix.ext_of_mulVec_single <;> intro j
  · rw [← Matrix.mulVec_mulVec, Matrix.zero_mulVec]
    exact (hperp (Pi.single j 1)).1
  · rw [← Matrix.mulVec_mulVec, Matrix.zero_mulVec]
    exact (hperp (Pi.single j 1)).2

private theorem exists_real_joint_eigenbasis {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (A B : Module.End ℝ E)
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) (hAB : Commute A B) :
    ∃ (v : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E) (a b : Fin (Module.finrank ℝ E) → ℝ),
      ∀ j, A (v j) = a j • v j ∧ B (v j) = b j • v j := by
  classical
  let z (p : B.Eigenvalues × A.Eigenvalues) : ℝ × ℝ := (p.1.val, p.2.val)
  have hz : Function.Injective z := fun p q h =>
    Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))
  let V (p : B.Eigenvalues × A.Eigenvalues) := eigenspace A (z p).2 ⊓ eigenspace B (z p).1
  have hOrth : OrthogonalFamily ℝ (fun p => V p) (fun p => (V p).subtypeₗᵢ) :=
    (hA.orthogonalFamily_eigenspace_inf_eigenspace hB).comp hz
  have hTop : (⨆ p, V p) = ⊤ := by
    apply top_unique
    rw [← hA.iSup_iSup_eigenspace_inf_eigenspace_eq_top_of_commute hB hAB]
    refine iSup_le fun x => iSup_le fun y => ?_
    by_cases hx : A.HasEigenvalue x
    · by_cases hy : B.HasEigenvalue y
      · let p : B.Eigenvalues × A.Eigenvalues := (⟨y, hy⟩, ⟨x, hx⟩)
        change V p ≤ _
        exact le_iSup V p
      · rw [hasEigenvalue_iff, not_ne_iff] at hy
        rw [hy, inf_bot_eq]
        exact bot_le
    · rw [hasEigenvalue_iff, not_ne_iff] at hx
      rw [hx, bot_inf_eq]
      exact bot_le
  have hSum : DirectSum.IsInternal V :=
    hOrth.isInternal_iff.mpr (by rw [Submodule.orthogonal_eq_bot_iff, hTop])
  let hn : Module.finrank ℝ E = Module.finrank ℝ E := rfl
  let idx j := hSum.subordinateOrthonormalBasisIndex hn j hOrth
  refine ⟨hSum.subordinateOrthonormalBasis hn hOrth,
    fun j => (z (idx j)).2, fun j => (z (idx j)).1, fun j => ?_⟩
  have h := Submodule.mem_inf.mp (hSum.subordinateOrthonormalBasis_subordinate hn j hOrth)
  exact ⟨mem_eigenspace_iff.mp h.1, mem_eigenspace_iff.mp h.2⟩

private theorem exists_orthogonal_diagonalization_pair {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : Commute A B) :
    ∃ (O : Matrix.orthogonalGroup ι ℝ) (a b : ι → ℝ),
      A = O.val * diagonal a * O.valᴴ ∧ B = O.val * diagonal b * O.valᴴ := by
  let T := toEuclideanLin A
  let S := toEuclideanLin B
  have hT : T.IsSymmetric := isHermitian_iff_isSymmetric.mp hA
  have hS : S.IsSymmetric := isHermitian_iff_isSymmetric.mp hB
  have hTS : Commute T S := hAB.map (Matrix.toLinAlgEquiv (EuclideanSpace.basisFun ι ℝ).toBasis)
  obtain ⟨v₀, a₀, b₀, heig⟩ := exists_real_joint_eigenbasis T S hT hS hTS
  let e : Fin (Module.finrank ℝ (EuclideanSpace ℝ ι)) ≃ ι :=
    Fintype.equivOfCardEq (by rw [Fintype.card_fin, finrank_euclideanSpace])
  let v := v₀.reindex e
  let a j := a₀ (e.symm j)
  let b j := b₀ (e.symm j)
  let M := (EuclideanSpace.basisFun ι ℝ).toBasis.toMatrix v.toBasis
  let O : Matrix.orthogonalGroup ι ℝ := ⟨M,
    (EuclideanSpace.basisFun ι ℝ).toMatrix_orthonormalBasis_mem_unitary v⟩
  have hMM : M * Mᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp O.property
  have hdiag (Q : Matrix ι ι ℝ) (c : ι → ℝ)
      (hQ : ∀ j, toEuclideanLin Q (v j) = c j • v j) :
      Q = M * diagonal c * Mᴴ := by
    have hcomm : Q * M = M * diagonal c := by
      ext i j : 1
      have h := congrArg (fun x : EuclideanSpace ℝ ι => WithLp.equiv 2 (ι → ℝ) x i) (hQ j)
      change WithLp.equiv 2 (ι → ℝ) (toEuclideanLin Q (v j)) i = _ at h
      rw [Matrix.piLp_equiv_toEuclideanLin_apply] at h
      change (Q *ᵥ (fun k => v j k)) i = (c j • v j) i at h
      rw [Matrix.mul_diagonal, Matrix.mul_apply]
      simpa only [M, Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
        OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_repr, Matrix.mulVec, dotProduct,
        PiLp.smul_apply, smul_eq_mul, mul_comm (c j)] using h
    rw [← hcomm, Matrix.mul_assoc, hMM, Matrix.mul_one]
  refine ⟨O, a, b, hdiag A a (fun j => ?_), hdiag B b (fun j => ?_)⟩
  · simpa only [T, a, v, OrthonormalBasis.reindex_apply] using (heig (e.symm j)).1
  · simpa only [S, b, v, OrthonormalBasis.reindex_apply] using (heig (e.symm j)).2

/-- Once one effect has rank one, the other two are diagonal in the same
orthogonal basis. Their diagonal entries form a complementary pair on the
two remaining coordinates. -/
theorem rank_one_effects_complementary_diagonal
    (A B C : Matrix (Fin 3) (Fin 3) ℝ) (hA : A.PosSemidef) (hB : B.PosSemidef) (hC : C.PosSemidef)
    (htraceA : A.trace = 1) (htraceB : B.trace = 1) (hrankA : A.rank = 1) (hsum : A + B + C = 1) :
    ∃ (O : Matrix.orthogonalGroup (Fin 3) ℝ) (i : Fin 3) (b : Fin 3 → ℝ),
      (∀ j, 0 ≤ b j ∧ b j ≤ 1) ∧ b i = 0 ∧ (∑ j, b j) = 1 ∧
      A = O.val * diagonal (Pi.single i 1) * O.valᴴ ∧ B = O.val * diagonal b * O.valᴴ ∧
      C = O.val * diagonal (fun j => 1 - (Pi.single i 1 : Fin 3 → ℝ) j - b j) * O.valᴴ := by
  classical
  have hProj := effect_rank_one_mul_self A hA hrankA htraceA
  obtain ⟨hBA, _⟩ := effects_mul_projection_eq_zero A B C hProj hB hC hsum
  have hAB : A * B = 0 := by
    have hAH : Aᴴ = A := hA.isHermitian
    have hBH : Bᴴ = B := hB.isHermitian
    simpa only [Matrix.conjTranspose_mul, hAH, hBH,
      Matrix.conjTranspose_zero] using congrArg Matrix.conjTranspose hBA
  obtain ⟨O, a, b, ha, hb⟩ := exists_orthogonal_diagonalization_pair A B hA.isHermitian
    hB.isHermitian (show Commute A B from hAB.trans hBA.symm)
  let P := O.val
  have hPP : P * Pᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp O.property
  have hP'P : Pᴴ * P = 1 := Matrix.mem_unitaryGroup_iff'.mp O.property
  have conjugation (Q : Matrix (Fin 3) (Fin 3) ℝ) : Pᴴ * (P * Q * Pᴴ) * P = Q := by
    calc
      _ = (Pᴴ * P) * Q * (Pᴴ * P) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hP'P, Matrix.one_mul, Matrix.mul_one]
  have hDa : Pᴴ * A * P = diagonal a := by rw [ha]; exact conjugation _
  have hDb : Pᴴ * B * P = diagonal b := by rw [hb]; exact conjugation _
  have hbpos : (diagonal b).PosSemidef := hDb ▸ hB.conjTranspose_mul_mul_same P
  have hsumA : ∑ i, a i = 1 := by
    rw [← htraceA, ha, Matrix.trace_mul_cycle, hP'P, Matrix.one_mul, Matrix.trace_diagonal]
  have hsumB : ∑ i, b i = 1 := by
    rw [← htraceB, hb, Matrix.trace_mul_cycle, hP'P, Matrix.one_mul, Matrix.trace_diagonal]
  have hbnonneg (j : Fin 3) : 0 ≤ b j := by
    have h := hbpos.2 (Pi.single j 1)
    rwa [star_trivial, Matrix.diagonal_mulVec_single, single_dotProduct,
      Pi.single_eq_same, one_mul, mul_one] at h
  have hble (j : Fin 3) : b j ≤ 1 := by
    rw [← hsumB]
    exact Finset.single_le_sum (fun k _ => hbnonneg k) (Finset.mem_univ j)
  have hDmul (X Y : Matrix (Fin 3) (Fin 3) ℝ) :
      (Pᴴ * X * P) * (Pᴴ * Y * P) = Pᴴ * (X * Y) * P := by
    calc
      _ = Pᴴ * X * (P * Pᴴ) * Y * P := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hPP, Matrix.mul_one, Matrix.mul_assoc Pᴴ]
  have hDa' : diagonal a * diagonal a = diagonal a := by
    rw [← hDa, hDmul, hProj]
  have hDbDa : diagonal b * diagonal a = 0 := by
    rw [← hDa, ← hDb, hDmul, hBA, Matrix.mul_zero, Matrix.zero_mul]
  have haCases (j : Fin 3) : a j = 0 ∨ a j = 1 := by
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M j j) hDa'
    change (diagonal a * diagonal a) j j = (diagonal a) j j at h
    simp only [Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq] at h
    exact (mul_eq_zero.mp (show a j * (a j - 1) = 0 by nlinarith [h])).imp id sub_eq_zero.mp
  have haNonneg (j : Fin 3) : 0 ≤ a j := by
    rcases haCases j with h | h <;> simp [h]
  have hai : ∃ i, a i = 1 := by
    by_contra hnone
    have hz (j : Fin 3) : a j = 0 := (haCases j).resolve_right (fun hj => hnone ⟨j, hj⟩)
    simp [hz] at hsumA
  obtain ⟨i, hi⟩ := hai
  have haSingle : a = Pi.single i 1 := by
    funext j
    by_cases hj : j = i
    · subst j
      simpa using hi
    · have hz := Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ.erase i)
        (fun k _ => haNonneg k)
      have htail : ∑ k ∈ Finset.univ.erase i, a k = 0 := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), hi] at hsumA
        linarith
      simpa [Pi.single_eq_of_ne hj] using hz.mp htail j (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)
  have hbi : b i = 0 := by
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M i i) hDbDa
    change (diagonal b * diagonal a) i i = (0 : Matrix (Fin 3) (Fin 3) ℝ) i i at h
    simpa [Matrix.diagonal_mul_diagonal, hi] using h
  have hc : C = 1 - A - B := by
    apply (eq_sub_iff_add_eq).mpr
    apply (eq_sub_iff_add_eq).mpr
    simpa [add_comm, add_left_comm, add_assoc] using hsum
  refine ⟨O, i, b, (fun j => ⟨hbnonneg j, hble j⟩), hbi, hsumB, ?_, hb, ?_⟩
  · simpa only [haSingle] using ha
  · have hdiag : diagonal (fun j => 1 - (Pi.single i 1 : Fin 3 → ℝ) j - b j) =
        1 - diagonal (Pi.single i 1) - diagonal b := by
      rw [← Matrix.diagonal_one, ← Matrix.diagonal_sub, ← Matrix.diagonal_sub] <;> rfl
    rw [hdiag, hc, ha, hb, haSingle, Matrix.mul_sub, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_one, hPP]

/-- Six candidate trace-free perturbations of real symmetric `3 × 3`
matrices have a nontrivial combination with zero total perturbation. -/
theorem exists_zero_sum_trace_free_perturbation
    (A B : Fin 3 → Matrix (Fin 3) (Fin 3) ℝ)
    (hA : ∀ i, (A i)ᵀ = A i ∧ (A i).trace = 0)
    (hB : ∀ i, (B i)ᵀ = B i ∧ (B i).trace = 0) :
    ∃ x : Fin 3 × Fin 2 → ℝ, x ≠ 0 ∧
      (∑ i, (x (i, 0)) • A i + (x (i, 1)) • B i) = 0 := by
  let M : (Fin 3 × Fin 2 → ℝ) →ₗ[ℝ] Matrix (Fin 3) (Fin 3) ℝ :=
    ∑ i : Fin 3, (LinearMap.proj (i, (0 : Fin 2))).smulRight (A i) +
      (LinearMap.proj (i, (1 : Fin 2))).smulRight (B i)
  let slots : Fin 5 → Fin 3 × Fin 3 := ![(0, 0), (0, 1), (0, 2), (1, 1), (1, 2)]
  let entries : Matrix (Fin 3) (Fin 3) ℝ →ₗ[ℝ] (Fin 5 → ℝ) :=
    { toFun := fun H k => H (slots k).1 (slots k).2
      map_add' := by intro X Y; rfl
      map_smul' := by intro c X; rfl }
  let L := entries.comp M
  have hdim : Module.finrank ℝ (Fin 5 → ℝ) < Module.finrank ℝ (Fin 3 × Fin 2 → ℝ) := by
    rw [Module.finrank_pi, Module.finrank_pi, Fintype.card_prod]
    decide
  obtain ⟨x, hx, hne⟩ := (LinearMap.ker L).ne_bot_iff.mp (L.ker_ne_bot_of_finrank_lt hdim)
  have hL := LinearMap.mem_ker.mp hx
  change entries (M x) = 0 at hL
  have h00 : M x 0 0 = 0 := congrFun hL 0
  have h01 : M x 0 1 = 0 := congrFun hL 1
  have h02 : M x 0 2 = 0 := congrFun hL 2
  have h11 : M x 1 1 = 0 := congrFun hL 3
  have h12 : M x 1 2 = 0 := congrFun hL 4
  have hM : M x = ∑ i, (x (i, 0)) • A i + (x (i, 1)) • B i := by
    simp [M, LinearMap.sum_apply, LinearMap.smulRight_apply]
  have hsym : (M x)ᵀ = M x := by
    simp [hM, Matrix.transpose_sum, Matrix.transpose_add, Matrix.transpose_smul,
      fun i => (hA i).1, fun i => (hB i).1]
  have h10 : M x 1 0 = 0 := (congrFun (congrFun hsym 0) 1).trans h01
  have h20 : M x 2 0 = 0 := (congrFun (congrFun hsym 0) 2).trans h02
  have h21 : M x 2 1 = 0 := (congrFun (congrFun hsym 1) 2).trans h12
  have htrace : (M x).trace = 0 := by
    simp [hM, Matrix.trace_sum, Matrix.trace_add, Matrix.trace_smul,
      fun i => (hA i).2, fun i => (hB i).2]
  have h22 : M x 2 2 = 0 := by
    simpa [Matrix.trace, Fin.sum_univ_three, Matrix.diag, h00, h11] using htrace
  refine ⟨x, hne, ?_⟩
  rw [← hM]
  ext i j
  fin_cases i <;> fin_cases j <;> first
    | exact h00
    | exact h01
    | exact h02
    | exact h10
    | exact h11
    | exact h12
    | exact h20
    | exact h21
    | exact h22

end

end MOC
