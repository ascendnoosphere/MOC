import MOC.NewtonPolytopeModulus
import MOC.UnitaryPhaseCuts
import Mathlib.Data.Sym.Sym2
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Tactic.FinCases

/-! The graph-matching bound from the Pfaffian square identity and the
torus maximum-modulus inequality. -/

open BigOperators Matrix

namespace MOC

noncomputable section

/-- Vertices of an even-order matrix, indexed in consecutive pairs. -/
abbrev PfaffianIndex (n : ℕ) := Fin n × Fin 2

variable {n : ℕ}

private def pfaffianScale (n : ℕ) : ℂ := 2 ^ n * (n.factorial : ℂ)

private def pfaffianTerm (K : Matrix (PfaffianIndex n) (PfaffianIndex n) ℂ)
    (σ : Equiv.Perm (PfaffianIndex n)) : ℂ :=
  ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i : Fin n, K (σ (i, 0)) (σ (i, 1))

/-- The permutation formula for the Pfaffian, with the vertex orientation
given by consecutive pairs. -/
def complexPfaffian (K : Matrix (PfaffianIndex n) (PfaffianIndex n) ℂ) : ℂ :=
  (∑ σ, pfaffianTerm K σ) / pfaffianScale n

private abbrev PfaffianVector (n : ℕ) := PfaffianIndex n → ℂ

private theorem paired_bilinear_product_update (K : Matrix (PfaffianIndex n) (PfaffianIndex n) ℂ)
    (v : PfaffianIndex n → PfaffianVector n) (j : PfaffianIndex n) (x : PfaffianVector n) :
    (∏ i : Fin n, K.toBilin' (Function.update v j x (i, 0)) (Function.update v j x (i, 1))) =
      K.toBilin' (Function.update v j x (j.1, 0)) (Function.update v j x (j.1, 1)) *
        ∏ i ∈ Finset.univ.erase j.1, K.toBilin' (v (i, 0)) (v (i, 1)) := by
  let f (i : Fin n) : ℂ := K.toBilin' (Function.update v j x (i, 0)) (Function.update v j x (i, 1))
  change ∏ i, f i = f j.1 * _
  rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ j.1)]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  have hij : i ≠ j.1 := Finset.ne_of_mem_erase hi
  have h0 : (i, (0 : Fin 2)) ≠ j := fun h => hij (congrArg Prod.fst h)
  have h1 : (i, (1 : Fin 2)) ≠ j := fun h => hij (congrArg Prod.fst h)
  simp only [f, Function.update_of_ne h0, Function.update_of_ne h1]

private def pairedBilinearProduct (K : Matrix (PfaffianIndex n) (PfaffianIndex n) ℂ) :
    MultilinearMap ℂ (fun _ : PfaffianIndex n => PfaffianVector n) ℂ where
  toFun v := ∏ i : Fin n, K.toBilin' (v (i, 0)) (v (i, 1))
  map_update_add' v j x y := by
    simp only [paired_bilinear_product_update]
    rcases j with ⟨i, k⟩
    fin_cases k <;>
      simp [Function.update_apply, map_add, LinearMap.add_apply, add_mul]
  map_update_smul' v j c x := by
    simp only [paired_bilinear_product_update]
    rcases j with ⟨i, k⟩
    fin_cases k <;>
      simp [Function.update_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, mul_assoc]

private def pfaffianAlternating (K : Matrix (PfaffianIndex n) (PfaffianIndex n) ℂ) :
    AlternatingMap ℂ (PfaffianVector n) ℂ (PfaffianIndex n) :=
  MultilinearMap.alternatization (pairedBilinearProduct K)

private theorem pfaffianAlternating_apply (K : Matrix (PfaffianIndex n) (PfaffianIndex n) ℂ)
    (v : PfaffianIndex n → PfaffianVector n) :
    pfaffianAlternating K v = ∑ σ : Equiv.Perm (PfaffianIndex n),
      ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∏ i : Fin n, K.toBilin' (v (σ (i, 0))) (v (σ (i, 1))) := by
  rw [pfaffianAlternating, MultilinearMap.alternatization_apply]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Units.smul_def, zsmul_eq_mul] <;> rfl

private theorem pfaffianAlternating_basis (K : Matrix (PfaffianIndex n) (PfaffianIndex n) ℂ) :
    pfaffianAlternating K (Pi.basisFun ℂ (PfaffianIndex n)) = ∑ σ, pfaffianTerm K σ := by
  rw [pfaffianAlternating_apply]
  simp only [Pi.basisFun_apply, Matrix.toBilin'_single, pfaffianTerm]

/-- Congruence multiplies the Pfaffian by the determinant of the
change-of-basis matrix. Singular change-of-basis matrices are allowed. -/
theorem complexPfaffian_congr (K S : Matrix (PfaffianIndex n) (PfaffianIndex n) ℂ) :
    complexPfaffian (Sᵀ * K * S) = S.det * complexPfaffian K := by
  let b := Pi.basisFun ℂ (PfaffianIndex n)
  have hcomp (v : PfaffianIndex n → PfaffianVector n) :
      pfaffianAlternating (Sᵀ * K * S) v = pfaffianAlternating K (S.toLin' ∘ v) := by
    rw [pfaffianAlternating_apply, pfaffianAlternating_apply, ← Matrix.toBilin'_comp] <;> rfl
  have hdet : b.det (S.toLin' ∘ b) = S.det := by
    rw [Basis.det_comp, Basis.det_self, mul_one, Matrix.det_toLin']
  have h := congrArg (fun f : AlternatingMap ℂ (PfaffianVector n) ℂ (PfaffianIndex n) =>
    f (S.toLin' ∘ b)) ((pfaffianAlternating K).eq_smul_basis_det b)
  change pfaffianAlternating K (S.toLin' ∘ b) =
    pfaffianAlternating K b * b.det (S.toLin' ∘ b) at h
  rw [← hcomp, hdet, pfaffianAlternating_basis, pfaffianAlternating_basis] at h
  unfold complexPfaffian
  rw [h]
  ring

private def pfaffianWeighted (K : Matrix (PfaffianIndex n) (PfaffianIndex n) ℂ)
    (z : Sym2 (PfaffianIndex n) → ℂ) : Matrix (PfaffianIndex n) (PfaffianIndex n) ℂ :=
  Matrix.of fun i j => K i j * z (Sym2.mk (i, j))

private def pfaffianEdge (σ : Equiv.Perm (PfaffianIndex n)) (i : Fin n) :
    Sym2 (PfaffianIndex n) :=
  Sym2.mk (σ (i, 0), σ (i, 1))

private abbrev PfaffianMatching (K : Matrix (PfaffianIndex n) (PfaffianIndex n) ℂ) :=
  {σ : Equiv.Perm (PfaffianIndex n) // ∀ i : Fin n, K (σ (i, 0)) (σ (i, 1)) ≠ 0}

/-- The pairs of a vertex permutation partition the vertices into
edges with distinct endpoints. -/
theorem pfaffian_pairs_form_matching (σ : Equiv.Perm (PfaffianIndex n)) :
    (∀ i : Fin n, σ (i, 0) ≠ σ (i, 1)) ∧
      ∀ v, ∃! i : Fin n, σ (i, 0) = v ∨ σ (i, 1) = v := by
  constructor
  · intro i h
    exact (by decide : (0 : Fin 2) ≠ 1) (congrArg Prod.snd (σ.injective h))
  · intro v
    let w := σ.symm v
    have hw : σ (w.1, w.2) = v := σ.apply_symm_apply v
    refine ⟨w.1, ?_, ?_⟩
    · have h : w.2 = 0 ∨ w.2 = 1 := by omega
      rcases h with h | h
      · exact Or.inl (by simpa only [h] using hw)
      · exact Or.inr (by simpa only [h] using hw)
    · intro i hi
      rcases hi with hi | hi
      · exact congrArg Prod.fst (σ.injective (hi.trans hw.symm))
      · exact congrArg Prod.fst (σ.injective (hi.trans hw.symm))

/-- A singular skew matrix has zero Pfaffian. -/
theorem complexPfaffian_eq_zero_of_det_eq_zero
    (K : Matrix (PfaffianIndex n) (PfaffianIndex n) ℂ)
    (hskew : ∀ i j, K j i = -K i j) (hdet : K.det = 0) :
    complexPfaffian K = 0 := by
  classical
  obtain ⟨v, hv, hker⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  obtain ⟨k, hk⟩ : ∃ k, v k ≠ 0 := by
    by_contra! h
    exact hv (funext h)
  let S : Matrix (PfaffianIndex n) (PfaffianIndex n) ℂ := (1 : Matrix _ _ ℂ).updateCol k v
  have hScol (i : PfaffianIndex n) : S i k = v i := by simp [S]
  have hSdet : S.det = v k := by
    have hv' : (fun i => ∑ j, v j • (1 : Matrix _ _ ℂ) i j) = v := by
      funext i
      simp [Matrix.one_apply, smul_eq_mul]
    calc
      S.det = ((1 : Matrix _ _ ℂ).updateCol k
          (fun i => ∑ j, v j • (1 : Matrix _ _ ℂ) i j)).det := by rw [hv']
      _ = v k := by rw [Matrix.det_updateCol_sum, Matrix.det_one, smul_eq_mul, mul_one]
  let T := Sᵀ * K * S
  have hcol (i : PfaffianIndex n) : T i k = 0 := by
    have hKS (j : PfaffianIndex n) : (K * S) j k = 0 := by
      rw [Matrix.mul_apply]
      simp only [hScol]
      exact congrFun hker j
    rw [T, Matrix.mul_assoc, Matrix.mul_apply]
    simp only [hKS, mul_zero, Finset.sum_const_zero]
  have hTskew (i j : PfaffianIndex n) : T j i = -T i j := by
    have hKt : Kᵀ = -K := by
      ext a b : 1
      exact hskew a b
    have hTt : Tᵀ = -T := by
      simp only [T, Matrix.transpose_mul, Matrix.transpose_transpose, hKt,
        Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]
    exact congrArg (fun A : Matrix _ _ ℂ => A i j) hTt
  have hz (σ : Equiv.Perm (PfaffianIndex n)) : pfaffianTerm T σ = 0 := by
    obtain ⟨i, hi, _⟩ := (pfaffian_pairs_form_matching σ).2 k
    have he : T (σ (i, 0)) (σ (i, 1)) = 0 := by
      rcases hi with hi | hi
      · rw [hi, hTskew, hcol, neg_zero]
      · rw [hi, hcol]
    rw [pfaffianTerm, Finset.prod_eq_zero (Finset.mem_univ i) he, mul_zero]
  have hPf : complexPfaffian T = 0 := by simp [complexPfaffian, hz]
  rw [T, complexPfaffian_congr, hSdet] at hPf
  exact (mul_eq_zero.mp hPf).resolve_left hk

private theorem pfaffianTerm_eq_zero_of_not_supported
    (K : Matrix (PfaffianIndex n) (PfaffianIndex n) ℂ)
    {σ : Equiv.Perm (PfaffianIndex n)}
    (h : ¬∀ i : Fin n, K (σ (i, 0)) (σ (i, 1)) ≠ 0) :
    pfaffianTerm K σ = 0 := by
  push_neg at h
  obtain ⟨i, hi⟩ := h
  rw [pfaffianTerm, Finset.prod_eq_zero (Finset.mem_univ i) hi, mul_zero]

private theorem pfaffian_weighted_expansion
    (K : Matrix (PfaffianIndex n) (PfaffianIndex n) ℂ) (z : Sym2 (PfaffianIndex n) → ℂ) :
    complexPfaffian (pfaffianWeighted K z) / complexPfaffian K =
      ∑ σ : PfaffianMatching K,
        (pfaffianTerm K σ / pfaffianScale n / complexPfaffian K) *
          ∏ i, z (pfaffianEdge σ i) := by
  classical
  let p (σ : Equiv.Perm (PfaffianIndex n)) : Prop :=
    ∀ i : Fin n, K (σ (i, 0)) (σ (i, 1)) ≠ 0
  let f (σ : Equiv.Perm (PfaffianIndex n)) : ℂ :=
    (pfaffianTerm K σ / pfaffianScale n / complexPfaffian K) * ∏ i, z (pfaffianEdge σ i)
  change (∑ σ, pfaffianTerm (pfaffianWeighted K z) σ) /
    pfaffianScale n / complexPfaffian K = ∑ σ : {σ // p σ}, f σ
  rw [Finset.sum_div, Finset.sum_div]
  rw [← Finset.sum_subtype (p := p) (Finset.univ.filter p) (by simp) f, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro σ _
  have hterm : pfaffianTerm (pfaffianWeighted K z) σ =
      pfaffianTerm K σ * ∏ i, z (pfaffianEdge σ i) := by
    simp only [pfaffianTerm, pfaffianWeighted, Matrix.of_apply, Finset.prod_mul_distrib,
      pfaffianEdge, mul_assoc]
  rw [hterm]
  by_cases hp : p σ
  · rw [if_pos hp, f]
    ring
  · rw [if_neg hp, pfaffianTerm_eq_zero_of_not_supported K hp, zero_mul, zero_div, zero_div]

/-- The graph-Pfaffian modulus comparison under the square identity.
The displayed pairs of the resulting permutation form a perfect matching
in the support graph. -/
theorem pfaffian_norm_le_supported_matching_of_det_sq
    (J Z : Matrix (PfaffianIndex n) (PfaffianIndex n) ℂ) (hJ : IsUnitary J)
    (hskew : ∀ i j, J j i = -J i j) (hZ : ∀ i j, Z i j = Z j i)
    (hsquare : ∀ K : Matrix (PfaffianIndex n) (PfaffianIndex n) ℂ,
      (∀ i j, K j i = -K i j) → complexPfaffian K ^ 2 = K.det) :
    ∃ σ : Equiv.Perm (PfaffianIndex n),
      (∀ i : Fin n, J (σ (i, 0)) (σ (i, 1)) ≠ 0) ∧
      ‖complexPfaffian (Matrix.of fun i j => J i j * Z i j) / complexPfaffian J‖ ≤
        ‖∏ i : Fin n, Z (σ (i, 0)) (σ (i, 1))‖ := by
  classical
  letI : Fintype (Sym2 (PfaffianIndex n)) := Fintype.ofSurjective Sym2.mk Quot.mk_surjective
  have hJdet : Complex.normSq J.det = 1 := by
    have h := congrArg Matrix.det hJ.1
    rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one, Complex.star_def,
      Complex.mul_conj] at h
    exact_mod_cast h
  have hPf : ‖complexPfaffian J‖ = 1 := by
    have h := hJdet
    rw [← hsquare J hskew, map_pow] at h
    have hnonneg := Complex.normSq_nonneg (complexPfaffian J)
    have hsq := (sq_eq_sq₀ hnonneg zero_le_one).mp (by simpa only [one_pow] using h)
    apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    simpa only [Complex.sq_norm, one_pow] using hsq
  letI : Nonempty (PfaffianMatching J) := by
    by_contra h
    have hz (σ : Equiv.Perm (PfaffianIndex n)) : pfaffianTerm J σ = 0 := by
      apply pfaffianTerm_eq_zero_of_not_supported J
      intro hs
      exact h ⟨⟨σ, hs⟩⟩
    have hzero : complexPfaffian J = 0 := by simp [complexPfaffian, hz]
    rw [hzero, norm_zero] at hPf
    exact zero_ne_one hPf
  let α (σ : PfaffianMatching J) (e : Sym2 (PfaffianIndex n)) : ℕ :=
    (Finset.univ.filter fun i => pfaffianEdge σ i = e).card
  let c (σ : PfaffianMatching J) : ℂ := pfaffianTerm J σ / pfaffianScale n / complexPfaffian J
  have hmonomial (z : Sym2 (PfaffianIndex n) → ℂ) (σ : PfaffianMatching J) :
      ∏ e, z e ^ α σ e = ∏ i, z (pfaffianEdge σ i) := by
    simp_rw [α, ← Finset.prod_const]
    exact Finset.prod_fiberwise' Finset.univ (pfaffianEdge σ) z
  have hexp (z : Sym2 (PfaffianIndex n) → ℂ) :
      ‖∑ σ, c σ * ∏ e, z e ^ α σ e‖ =
        ‖complexPfaffian (pfaffianWeighted J z) / complexPfaffian J‖ := by
    rw [pfaffian_weighted_expansion]
    simp only [c, hmonomial]
  have htorus (z : Sym2 (PfaffianIndex n) → ℂ) (hz : ∀ e, ‖z e‖ = 1) :
      ‖∑ σ, c σ * ∏ e, z e ^ α σ e‖ ≤ 1 := by
    have hskew' (i j) : pfaffianWeighted J z j i = -pfaffianWeighted J z i j := by
      change J j i * z (Sym2.mk (j, i)) = -(J i j * z (Sym2.mk (i, j)))
      rw [hskew, Sym2.eq_swap, neg_mul]
    have hb := unitary_entrywise_polydisc_det_normSq_le_one J hJ
      (fun i j => z (Sym2.mk (i, j))) (fun i j => by
        rw [Complex.normSq_eq_norm_sq, hz, one_pow])
    change Complex.normSq (pfaffianWeighted J z).det ≤ 1 at hb
    rw [← hsquare _ hskew', map_pow] at hb
    have hb' := (sq_le_sq₀ (Complex.normSq_nonneg (complexPfaffian (pfaffianWeighted J z)))
      zero_le_one).mp (by simpa only [one_pow] using hb)
    rw [hexp, norm_div, hPf, div_one]
    apply (sq_le_sq₀ (norm_nonneg _) zero_le_one).mp
    simpa only [Complex.sq_norm, one_pow] using hb'
  let z : Sym2 (PfaffianIndex n) → ℂ := Sym2.lift ⟨fun i j => Z i j, hZ⟩
  obtain ⟨σ, hσ⟩ := norm_sum_monomials_le_of_torus_bound c α 1 htorus z
  refine ⟨σ, σ.property, ?_⟩
  rw [hexp, one_mul, hmonomial] at hσ
  have hweighted : pfaffianWeighted J z = Matrix.of (fun i j => J i j * Z i j) := by
    ext i j : 1
    simp only [z, pfaffianWeighted, Matrix.of_apply, Sym2.lift_mk]
  simpa only [hweighted, z, pfaffianEdge, Sym2.lift_mk] using hσ

end

end MOC
