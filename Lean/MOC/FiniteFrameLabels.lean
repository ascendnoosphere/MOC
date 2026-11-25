import MOC.ReducedTwoFrame
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.LinearAlgebra.Dimension.Constructions

open scoped BigOperators
open Matrix

namespace MOC

noncomputable section

/-- Conic Carathéodory on a slice defined by a strictly positive linear functional.
The representatives are selected from the original labels, not synthesized. -/
theorem finite_positive_conic_compression
    {I V : Type} [Fintype I] [AddCommGroup V] [Module ℝ V] [Module.Finite ℝ V]
    (v : I → V) (L : V →ₗ[ℝ] ℝ) (hL : ∀ i, 0 < L (v i))
    (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (hT : 0 < ∑ i, w i * L (v i)) :
    ∃ (J : Type) (_ : Fintype J) (e : J ↪ I) (u : J → ℝ),
      Fintype.card J ≤ Module.finrank ℝ V ∧ (∀ j, 0 < u j) ∧
        ∑ j, u j • v (e j) = ∑ i, w i • v i := by
  classical
  let T := ∑ i, w i * L (v i)
  let z (i : I) := (L (v i))⁻¹ • v i
  let y := T⁻¹ • ∑ i, w i • v i
  have hz (i : I) : L (z i) = 1 := by
    simp [z, smul_eq_mul, ne_of_gt (hL i)]
  have hy : y ∈ convexHull ℝ (Set.range z) := by
    refine mem_convexHull_of_exists_fintype (fun i : I => w i * L (v i) / T) z ?_ ?_ ?_ ?_
    · intro i
      exact div_nonneg (mul_nonneg (hw i) (hL i).le) hT.le
    · simp [← Finset.sum_div, T, ne_of_gt hT]
    · exact fun i => ⟨i, rfl⟩
    · dsimp [z, y]
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [smul_smul, smul_smul]
      congr 1
      field_simp [ne_of_gt (hL i), ne_of_gt hT]
      ring
  obtain ⟨J, hJ, p, c, hp, hind, hc, _, hsum⟩ := eq_pos_convex_span_of_mem_convexHull hy
  choose f hf using fun j => hp (Set.mem_range_self j)
  let e : J ↪ I := ⟨f, fun i j hij => hind.injective (by rw [← hf i, ← hf j, hij])⟩
  have hLp (j : J) : L (p j) = 1 := by rw [← hf j, hz]
  have hlin : LinearIndependent ℝ p := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have hzero : ∑ j, g j = 0 := by
      simpa [map_sum, map_smul, hLp] using congrArg L hg
    exact hind Finset.univ g hzero (by simpa [Finset.weightedVSub_apply, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hzero] using hg) j (Finset.mem_univ j)
  refine ⟨J, hJ, e, fun j => T * c j / L (v (e j)), hlin.fintype_card_le_finrank,
    fun j => div_pos (mul_pos hT (hc j)) (hL _), ?_⟩
  have h := congrArg (fun x : V => T • x) hsum
  dsimp [y] at h
  rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hT), one_smul, Finset.smul_sum] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro j _
  rw [← hf j]
  change _ = T • c j • ((L (v (e j)))⁻¹ • v (e j))
  rw [smul_smul, smul_smul]
  rfl


private abbrev Herm (K : Type) :=
  selfAdjoint.submodule ℝ (Matrix K K ℂ)

private theorem herm_finrank (K : Type) [Fintype K] :
    Module.finrank ℝ (Herm K) = Fintype.card K ^ 2 := by
  let e : Matrix K K ℂ ≃ₗ[ℝ] Herm K × Herm K :=
    { (realPart.prod imaginaryPart :
        Matrix K K ℂ →ₗ[ℝ] Herm K × Herm K) with
      invFun := fun p => (p.1 : Matrix K K ℂ) + Complex.I • (p.2 : Matrix K K ℂ)
      left_inv := realPart_add_I_smul_imaginaryPart
      right_inv := by
        rintro ⟨a, b⟩
        have ha : IsSelfAdjoint (a : Matrix K K ℂ) := a.property
        have hb : IsSelfAdjoint (b : Matrix K K ℂ) := b.property
        have ha' : realPart (a : Matrix K K ℂ) = a := Subtype.ext ha.coe_realPart
        have hb' : realPart (b : Matrix K K ℂ) = b := Subtype.ext hb.coe_realPart
        change (realPart ((a : Matrix K K ℂ) + Complex.I • (b : Matrix K K ℂ)),
          imaginaryPart ((a : Matrix K K ℂ) + Complex.I • (b : Matrix K K ℂ))) = (a, b)
        simp [map_add, realPart_I_smul, imaginaryPart_I_smul, ha', hb',
          ha.imaginaryPart, hb.imaginaryPart] }
  have h := e.finrank_eq
  rw [Module.finrank_matrix, Module.finrank_prod] at h
  have h2 : Module.finrank ℝ ℂ = 2 := by
    exact Module.finrank_eq_card_basis Complex.basisOneI
  rw [h2, ← pow_two] at h
  omega

private def frameRowGram {I K : Type} (F : Matrix I K ℂ) (i : I) : Herm K :=
  ⟨fun j k => star (F i j) * F i k, by
    change star (of fun j k => star (F i j) * F i k) = _
    ext j k
    simp [Matrix.star_apply, mul_comm]⟩

private def realHermTrace (K : Type) [Fintype K] : Herm K →ₗ[ℝ] ℝ :=
  Complex.reLm.comp ((Matrix.traceLinearMap K ℝ ℂ).comp (Herm K).subtype)

private theorem frameRowTrace (K I : Type) [Fintype K]
    (F : Matrix I K ℂ) (i : I) :
    realHermTrace K (frameRowGram F i) = ∑ j, ‖F i j‖ ^ 2 := by
  change Complex.reLm (∑ j : K, star (F i j) * F i j) = _
  rw [map_sum Complex.reLm]
  apply Finset.sum_congr rfl
  intro j _
  change (star (F i j) * F i j).re = _
  rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.sq_norm]


/-- A nonzero-dimensional isometric frame can be shortened to at most
(3k^2) existing spectral labels, preserving the entire compression.
The Hilbert-space geometry is exact; no labels or matrices are approximated.
The rank-one effect viewpoint is related to D'Ariano, Lo Presti and Perinotti,
DOI 10.1088/0305-4470/38/26/010; the three-moment reduction is the argument here. -/
theorem exists_sparse_frame_same_compression
    {I K : Type} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K] [Nonempty K]
    (F : Matrix I K ℂ) (hF : Fᴴ * F = 1) (x : I → ℂ) :
    ∃ (J : Type) (_ : Fintype J) (_ : DecidableEq J) (e : J ↪ I) (G : Matrix J K ℂ),
      Fintype.card J ≤ 3 * Fintype.card K ^ 2 ∧ Gᴴ * G = 1 ∧
      Gᴴ * diagonal (x ∘ e) * G = Fᴴ * diagonal x * F := by
  classical
  let R := {i : I // ∃ j, F i j ≠ 0}
  let v (i : R) : Herm K × (Herm K × Herm K) :=
    (frameRowGram F i, (x i).re • frameRowGram F i, (x i).im • frameRowGram F i)
  let L : (Herm K × (Herm K × Herm K)) →ₗ[ℝ] ℝ :=
    (realHermTrace K).comp (LinearMap.fst ℝ (Herm K) (Herm K × Herm K))
  have hL (i : R) : 0 < L (v i) := by
    change 0 < realHermTrace K (frameRowGram F i)
    rw [frameRowTrace]
    obtain ⟨j, hj⟩ := i.property
    exact Finset.sum_pos' (fun l _ => sq_nonneg _) ⟨j, Finset.mem_univ _, sq_pos_of_pos (norm_pos_iff.mpr hj)⟩
  have hR : Nonempty R := by
    by_contra! h
    have h0 : F = 0 := by
      ext i j
      by_contra hne
      exact h ⟨⟨i, j, hne⟩⟩
    obtain ⟨j⟩ := ‹Nonempty K›
    simpa [h0, Matrix.one_apply] using congrFun (congrFun hF j) j
  have ht : 0 < ∑ i : R, (1 : ℝ) * L (v i) := by
    simp only [one_mul]
    exact Finset.sum_pos (fun i _ => hL i) Finset.univ_nonempty
  obtain ⟨J, hJ, q, u, hcard, hu, hsum⟩ :=
    finite_positive_conic_compression v L hL (fun _ => 1) (fun _ => zero_le_one) ht
  let e : J ↪ I := q.trans ⟨Subtype.val, Subtype.val_injective⟩
  let G : Matrix J K ℂ := fun i j => (Real.sqrt (u i) : ℂ) * F (e i) j
  have he (i : J) : (q i : I) = e i := rfl
  have hscale (i : J) (j k : K) :
      star (G i j) * G i k = (u i : ℂ) * (star (F (e i) j) * F (e i) k) := by
    change star ((Real.sqrt (u i) : ℂ) * F (e i) j) * ((Real.sqrt (u i) : ℂ) * F (e i) k) = _
    rw [StarMul.star_mul, Complex.star_def, Complex.conj_ofReal]
    have hs : (Real.sqrt (u i) : ℂ)^2 = (u i : ℂ) := by
      exact_mod_cast Real.sq_sqrt (hu i).le
    calc
      _ = (Real.sqrt (u i) : ℂ)^2 * ((starRingEnd ℂ) (F (e i) j) * F (e i) k) := by ring
      _ = _ := by rw [hs]
  have hmom (d : I → ℝ)
      (H : ∀ j k : K, (∑ i : J, (u i : ℂ) * (d (e i) : ℂ) *
        (star (F (e i) j) * F (e i) k)) =
        ∑ i : R, (d i : ℂ) * (star (F i j) * F i k)) :
      ∀ j k : K, (∑ i : J, (d (e i) : ℂ) * (star (G i j) * G i k)) =
        ∑ i : I, (d i : ℂ) * (star (F i j) * F i k) := by
    intro j k
    trans ∑ i : J, (u i : ℂ) * (d (e i) : ℂ) * (star (F (e i) j) * F (e i) k)
    · apply Finset.sum_congr rfl
      intro i _
      rw [hscale]
      ring
    rw [H j k, ← Finset.sum_filter_add_sum_filter_not
      (s := (Finset.univ : Finset I)) (p := fun i => ∃ j, F i j ≠ 0)]
    have hzero : ∑ i ∈ Finset.univ.filter (fun i => ¬ ∃ j, F i j ≠ 0),
        (d i : ℂ) * (star (F i j) * F i k) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hf : F i j = 0 := by
        exact not_ne_iff.mp (fun hn => (Finset.mem_filter.mp hi).2 ⟨j, hn⟩)
      simp [hf]
    rw [hzero, add_zero]
    exact (Finset.sum_subtype (p := fun i : I => ∃ l, F i l ≠ 0)
      (Finset.univ.filter (fun i => ∃ l, F i l ≠ 0)) (by simp)
      (fun i : I => (d i : ℂ) * (star (F i j) * F i k))).symm
  let φ (j k : K) : Herm K →ₗ[ℝ] ℂ :=
    (LinearMap.proj k).comp ((LinearMap.proj j).comp (Herm K).subtype)
  let P := Herm K × (Herm K × Herm K)
  let P1 : P →ₗ[ℝ] Herm K := LinearMap.fst _ _ _
  let P2 : P →ₗ[ℝ] Herm K := (LinearMap.fst _ _ _).comp (LinearMap.snd _ _ _)
  let P3 : P →ₗ[ℝ] Herm K := (LinearMap.snd _ _ _).comp (LinearMap.snd _ _ _)
  have getMom (d : I → ℝ) (pr : P →ₗ[ℝ] Herm K)
      (hd : ∀ i : R, pr (v i) = d i • frameRowGram F i) :=
    hmom d (by
      intro j k
      have h := congrArg ((φ j k).comp pr) hsum
      simp only [map_sum, map_smul, one_smul, LinearMap.comp_apply, hd] at h
      simpa only [φ, LinearMap.comp_apply, LinearMap.proj_apply, Submodule.subtype_apply,
        Submodule.coe_smul, Matrix.smul_apply, frameRowGram, Complex.real_smul, he, mul_assoc] using h)
  have h1 := getMom (fun _ => 1) P1 (by intro i; change _ = (1 : ℝ) • _; rw [one_smul]; rfl)
  have hr := getMom (fun i => (x i).re) P2 (fun _ => rfl)
  have hi := getMom (fun i => (x i).im) P3 (fun _ => rfl)
  refine ⟨J, hJ, Classical.decEq J, e, G, ?_, ?_, ?_⟩
  · rw [Module.finrank_prod, Module.finrank_prod, herm_finrank] at hcard
    omega
  · rw [← hF]
    ext j k
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply] using h1 j k
  · ext j k
    have hx (i : I) (y z : ℂ) : star y * x i * z =
        (x i).re * (star y * z) + Complex.I * ((x i).im * (star y * z)) := by
      conv_lhs => rw [← Complex.re_add_im (x i)]
      ring
    rw [Matrix.mul_apply (M := Gᴴ * diagonal (x ∘ e)) (N := G) (i := j) (k := k),
      Matrix.mul_apply (M := Fᴴ * diagonal x) (N := F) (i := j) (k := k)]
    simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Function.comp_apply, hx,
      Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hr j k, hi j k]


/-- Restricting to old labels removes matching vertices. The optional zero
is retained only if both reduced sides still have spare labels. -/
theorem partialFrameVertices_restrict_subset
    {I J I' J' K : Type} [Fintype I] [Fintype J] [Fintype I'] [Fintype J'] [Fintype K]
    (x : I → ℂ) (y : J → ℂ) (e : I' ↪ I) (f : J' ↪ J) :
    partialFrameVertices (κ := K) (x ∘ e) (y ∘ f) ⊆
      partialFrameVertices (κ := K) x y := by
  intro z hz
  rcases hz with (⟨⟨p, q⟩, rfl⟩ | ⟨h0, hI, hJ⟩)
  · exact Or.inl ⟨(p.trans e, q.trans f), rfl⟩
  · exact Or.inr ⟨h0, hI.trans_le (Fintype.card_le_of_injective e e.injective),
      hJ.trans_le (Fintype.card_le_of_injective f f.injective)⟩

/-- A scalar frame counterexample of prescribed positive overlap has one
with at most (3k^2) labels on each side, and the same determinant.
This is a finite-label reduction, not a finite arithmetic test. -/
theorem exists_sparse_scalar_frame_counterexample
    {I J K : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype K] [DecidableEq K] [Nonempty K]
    (x : I → ℂ) (y : J → ℂ) (F : Matrix I K ℂ) (G : Matrix J K ℂ)
    (hF : Fᴴ * F = 1) (hG : Gᴴ * G = 1)
    (h : (Fᴴ * diagonal x * F + Gᴴ * diagonal y * G).det ∉
      convexHull ℝ (partialFrameVertices (κ := K) x y)) :
    ∃ (I' J' : Type) (_ : Fintype I') (_ : Fintype J')
      (_ : DecidableEq I') (_ : DecidableEq J')
      (e : I' ↪ I) (f : J' ↪ J) (F' : Matrix I' K ℂ) (G' : Matrix J' K ℂ),
      Fintype.card I' ≤ 3 * Fintype.card K ^ 2 ∧
      Fintype.card J' ≤ 3 * Fintype.card K ^ 2 ∧ F'ᴴ * F' = 1 ∧ G'ᴴ * G' = 1 ∧
      (F'ᴴ * diagonal (x ∘ e) * F' + G'ᴴ * diagonal (y ∘ f) * G').det =
        (Fᴴ * diagonal x * F + Gᴴ * diagonal y * G).det ∧
      (F'ᴴ * diagonal (x ∘ e) * F' + G'ᴴ * diagonal (y ∘ f) * G').det ∉
        convexHull ℝ (partialFrameVertices (κ := K) (x ∘ e) (y ∘ f)) := by
  obtain ⟨I', hi, di, e, F', hc, hFi, hA⟩ := exists_sparse_frame_same_compression F hF x
  obtain ⟨J', hj, dj, f, G', hd, hGj, hB⟩ := exists_sparse_frame_same_compression G hG y
  refine ⟨I', J', hi, hj, di, dj, e, f, F', G', hc, hd, hFi, hGj, by rw [hA, hB], ?_⟩
  rw [hA, hB]
  exact fun hm => h (convexHull_mono (partialFrameVertices_restrict_subset x y e f) hm)


/-- MOC through order (6k^2-k) implies the scalar frame law at overlap
(k), independently of the starting row counts. -/
theorem scalar_frame_law_of_bounded_orders
    {I J K : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype K] [DecidableEq K] [Nonempty K]
    (x : I → ℂ) (y : J → ℂ) (F : Matrix I K ℂ) (G : Matrix J K ℂ)
    (hF : Fᴴ * F = 1) (hG : Gᴴ * G = 1)
    (hMOC : ∀ m ≤ 6 * Fintype.card K ^ 2 - Fintype.card K, Conjecture (Fin m)) :
    (Fᴴ * diagonal x * F + Gᴴ * diagonal y * G).det ∈
      convexHull ℝ (partialFrameVertices (κ := K) x y) := by
  by_contra h
  obtain ⟨I', J', _, _, _, _, e, f, F', G', hI, hJ, hF', hG', _, h'⟩ :=
    exists_sparse_scalar_frame_counterexample x y F G hF hG h
  apply h'
  apply det_twoFrame_mem_partialFrameVertices_of_reducedOrder F' G' hF' hG' _ (x ∘ e) (y ∘ f)
  apply (conjecture_reindex_iff (Fintype.equivFin _)).mpr
  apply hMOC
  have hinj : Function.Injective (Matrix.toEuclideanLin G') :=
    Function.LeftInverse.injective (g := Matrix.toEuclideanLin G'ᴴ) (by
      intro v
      apply (WithLp.equiv 2 _).injective
      simp only [Matrix.piLp_equiv_toEuclideanLin_apply, Matrix.mulVec_mulVec, hG',
        Matrix.one_mulVec])
  have hfit : Fintype.card K ≤ Fintype.card J' := by
    simpa only [finrank_euclideanSpace] using LinearMap.finrank_le_finrank_of_injective hinj
  simp only [Fintype.card_sum, Fintype.card_fin]
  omega

end
end MOC
