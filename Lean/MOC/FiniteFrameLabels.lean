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

private theorem frameRowTrace_pos {I K : Type} [Fintype K]
    (F : Matrix I K ℂ) (i : I) (hi : ∃ j, F i j ≠ 0) :
    0 < realHermTrace K (frameRowGram F i) := by
  rw [frameRowTrace]
  obtain ⟨j,hj⟩ := hi
  exact Finset.sum_pos' (fun l _ => sq_nonneg _)
    ⟨j,Finset.mem_univ _,sq_pos_of_pos (norm_pos_iff.mpr hj)⟩

private theorem frameRow_support_nonempty {I K : Type} [Fintype I] [Fintype K]
    [DecidableEq K] [Nonempty K] (F : Matrix I K ℂ) (hF : Fᴴ * F = 1) :
    Nonempty {i : I // ∃ j, F i j ≠ 0} := by
  classical
  by_contra! h
  have h0 : F = 0 := by
    ext i j
    by_contra hn
    exact h ⟨⟨i,j,hn⟩⟩
  obtain ⟨j⟩ := ‹Nonempty K›
  simpa [h0, Matrix.one_apply] using congrFun (congrFun hF j) j

private theorem sum_nonzero_frame_rows
    {I K : Type} [Fintype I] (F : Matrix I K ℂ) [DecidablePred (fun i => ∃ l, F i l ≠ 0)]
    (x : I → ℂ) (j k : K) :
    (∑ i : {i : I // ∃ l, F i l ≠ 0}, x i * (star (F i j) * F i k)) =
      ∑ i : I, x i * (star (F i j) * F i k) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not
    (s := (Finset.univ : Finset I)) (p := fun i => ∃ l, F i l ≠ 0)]
  have hzero : ∑ i ∈ Finset.univ.filter (fun i => ¬ ∃ l, F i l ≠ 0),
      x i * (star (F i j) * F i k) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hf : F i j = 0 :=
      not_ne_iff.mp (fun hn => (Finset.mem_filter.mp hi).2 ⟨j,hn⟩)
    simp [hf]
  rw [hzero,add_zero]
  exact (Finset.sum_subtype (p := fun i : I => ∃ l, F i l ≠ 0)
    (Finset.univ.filter (fun i : I => ∃ l, F i l ≠ 0)) (by simp)
    (fun i : I => x i * (star (F i j) * F i k))).symm

private theorem sqrt_scaled_row_gram (u : ℝ) (hu : 0 ≤ u) (f g : ℂ) :
    star ((Real.sqrt u : ℂ) * f) * ((Real.sqrt u : ℂ) * g) =
      (u : ℂ) * (star f * g) := by
  rw [StarMul.star_mul, Complex.star_def, Complex.conj_ofReal]
  have hs : (Real.sqrt u : ℂ)^2 = (u : ℂ) := by exact_mod_cast Real.sq_sqrt hu
  calc
    _ = (Real.sqrt u : ℂ)^2 * ((starRingEnd ℂ) f * g) := by ring
    _ = _ := by rw [hs]

set_option maxHeartbeats 500000 in
/-- Joint compression spends two Hermitian moment constraints on the
two Gram identities and one full complex matrix constraint on the sum.
It keeps at most (4k^2) existing labels in total, with weights
absorbed into row norms. Separate complex compressions need not agree. -/
theorem exists_joint_sparse_frames_same_sum
    {I J K : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype K] [DecidableEq K] [Nonempty K]
    (x : I → ℂ) (y : J → ℂ) (F : Matrix I K ℂ) (G : Matrix J K ℂ)
    (hF : Fᴴ * F = 1) (hG : Gᴴ * G = 1) :
    ∃ (I' J' : Type) (_ : Fintype I') (_ : Fintype J')
      (_ : DecidableEq I') (_ : DecidableEq J')
      (e : I' ↪ I) (f : J' ↪ J) (F' : Matrix I' K ℂ) (G' : Matrix J' K ℂ),
      Fintype.card I' + Fintype.card J' ≤ 4 * Fintype.card K ^ 2 ∧
      F'ᴴ * F' = 1 ∧ G'ᴴ * G' = 1 ∧
      F'ᴴ * diagonal (x ∘ e) * F' + G'ᴴ * diagonal (y ∘ f) * G' =
        Fᴴ * diagonal x * F + Gᴴ * diagonal y * G := by
  classical
  let R := {i : I // ∃ l, F i l ≠ 0}
  let S := {j : J // ∃ l, G j l ≠ 0}
  let V := Herm K × (Herm K × Matrix K K ℂ)
  let v : R ⊕ S → V := fun
    | .inl i => (frameRowGram F i, 0, x i • (frameRowGram F i : Matrix K K ℂ))
    | .inr j => (0, frameRowGram G j, y j • (frameRowGram G j : Matrix K K ℂ))
  let L : V →ₗ[ℝ] ℝ :=
    ((realHermTrace K).comp (LinearMap.fst _ _ _)) +
      ((realHermTrace K).comp ((LinearMap.fst _ _ _).comp (LinearMap.snd _ _ _)))
  have hL (i : R ⊕ S) : 0 < L (v i) := by
    rcases i with i | i
    · change 0 < realHermTrace K (frameRowGram F i) + realHermTrace K 0
      simpa using frameRowTrace_pos F i i.property
    · change 0 < realHermTrace K 0 + realHermTrace K (frameRowGram G i)
      simpa using frameRowTrace_pos G i i.property
  letI : Nonempty R := frameRow_support_nonempty F hF
  have ht : 0 < ∑ i : R ⊕ S, (1 : ℝ) * L (v i) := by
    simp only [one_mul]
    exact Finset.sum_pos (fun i _ => hL i) Finset.univ_nonempty
  obtain ⟨T,hT,q,u,hcard,hu,hsum⟩ :=
    finite_positive_conic_compression v L hL (fun _ => 1) (fun _ => zero_le_one) ht
  let A := {i : R // Sum.inl i ∈ Set.range q}
  let B := {j : S // Sum.inr j ∈ Set.range q}
  let split : A ⊕ B ≃ T :=
    Equiv.subtypeSum.symm.trans (Equiv.ofInjective q q.injective).symm
  have hsplit (i : A ⊕ B) : q (split i) =
      Sum.map (fun i : A => (i : R)) (fun j : B => (j : S)) i := by
    have hh := congrArg Subtype.val ((Equiv.ofInjective q q.injective).apply_symm_apply
      (Equiv.subtypeSum.symm i))
    rcases i with i | i <;> exact hh
  let e : A ↪ I := ⟨fun i => i.val.val, Subtype.val_injective.comp Subtype.val_injective⟩
  let f : B ↪ J := ⟨fun j => j.val.val, Subtype.val_injective.comp Subtype.val_injective⟩
  let w (i : A) := u (split (.inl i))
  let z (j : B) := u (split (.inr j))
  let F' : Matrix A K ℂ := fun i k => (Real.sqrt (w i) : ℂ) * F (e i) k
  let G' : Matrix B K ℂ := fun j k => (Real.sqrt (z j) : ℂ) * G (f j) k
  have hF' (i : A) (j k : K) : star (F' i j) * F' i k =
      (w i : ℂ) * (star (F (e i) j) * F (e i) k) :=
    sqrt_scaled_row_gram _ (hu _).le _ _
  have hG' (i : B) (j k : K) : star (G' i j) * G' i k =
      (z i : ℂ) * (star (G (f i) j) * G (f i) k) :=
    sqrt_scaled_row_gram _ (hu _).le _ _
  have hsplitSum :
      (∑ i : A, w i • v (.inl i.val)) + (∑ j : B, z j • v (.inr j.val)) =
        (∑ i : R, v (.inl i)) + (∑ j : S, v (.inr j)) := by
    have hEq : (∑ i : A ⊕ B, u (split i) • v (q (split i))) =
        ∑ i : T, u i • v (q i) :=
      Fintype.sum_equiv split _ _ (fun _ => rfl)
    simp only [one_smul] at hsum
    have hh := hEq.trans hsum
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type] at hh
    simpa only [hsplit,Sum.map_inl,Sum.map_inr,w,z] using hh
  let ψ (j k : K) : Matrix K K ℂ →ₗ[ℝ] ℂ :=
    (LinearMap.proj k : (K → ℂ) →ₗ[ℝ] ℂ).comp
      (show Matrix K K ℂ →ₗ[ℝ] (K → ℂ) from LinearMap.proj j)
  let φ (j k : K) : Herm K →ₗ[ℝ] ℂ := (ψ j k).comp (Herm K).subtype
  let P1 : V →ₗ[ℝ] Herm K := LinearMap.fst _ _ _
  let P2 : V →ₗ[ℝ] Herm K := (LinearMap.fst _ _ _).comp (LinearMap.snd _ _ _)
  let P3 : V →ₗ[ℝ] Matrix K K ℂ := (LinearMap.snd _ _ _).comp (LinearMap.snd _ _ _)
  have hψ (j k : K) (M : Matrix K K ℂ) : ψ j k M = M j k := rfl
  have hφ (j k : K) (M : Herm K) : φ j k M = (M : Matrix K K ℂ) j k := rfl
  have h1 (p : V) : P1 p = p.1 := rfl
  have h2 (p : V) : P2 p = p.2.1 := rfl
  have h3 (p : V) : P3 p = p.2.2 := rfl
  refine ⟨A,B,inferInstance,inferInstance,inferInstance,inferInstance,e,f,F',G',?_,?_,?_,?_⟩
  · rw [← Fintype.card_sum, Fintype.card_congr split]
    have hcomplex : Module.finrank ℝ ℂ = 2 := Module.finrank_eq_card_basis Complex.basisOneI
    rw [Module.finrank_prod,Module.finrank_prod,herm_finrank,Module.finrank_matrix,hcomplex,
      ← pow_two] at hcard
    omega
  · rw [← hF]
    ext j k
    have mom := congrArg ((φ j k).comp P1) hsplitSum
    simp only [map_add,map_sum,map_smul,LinearMap.comp_apply,h1,v,Prod.fst,
      map_zero,smul_zero,Finset.sum_const_zero,add_zero,hφ,frameRowGram,
      Complex.real_smul,Submodule.coe_zero,Matrix.zero_apply] at mom
    rw [Matrix.mul_apply,Matrix.mul_apply]
    simp only [Matrix.conjTranspose_apply, hF']
    have hh := sum_nonzero_frame_rows F (fun _ => 1) j k
    simp only [one_mul] at hh
    rw [← hh]
    exact mom
  · rw [← hG]
    ext j k
    have mom := congrArg ((φ j k).comp P2) hsplitSum
    simp only [map_add,map_sum,map_smul,LinearMap.comp_apply,h2,v,Prod.fst,Prod.snd,
      map_zero,smul_zero,Finset.sum_const_zero,zero_add,hφ,frameRowGram,
      Complex.real_smul,Submodule.coe_zero,Matrix.zero_apply] at mom
    rw [Matrix.mul_apply,Matrix.mul_apply]
    simp only [Matrix.conjTranspose_apply,hG']
    have hh := sum_nonzero_frame_rows G (fun _ => 1) j k
    simp only [one_mul] at hh
    rw [← hh]
    exact mom
  · ext j k
    have mom := congrArg ((ψ j k).comp P3) hsplitSum
    simp only [map_add,map_sum,map_smul,LinearMap.comp_apply,h3,v,Prod.snd,
      hψ,Matrix.smul_apply,Pi.smul_apply,Complex.real_smul,smul_eq_mul,frameRowGram] at mom
    have entry {Q : Type} [Fintype Q] [DecidableEq Q] (H : Matrix Q K ℂ) (d : Q → ℂ) :
        (Hᴴ * diagonal d * H) j k = ∑ i, d i * (star (H i j) * H i k) := by
      rw [Matrix.mul_apply]
      simp only [Matrix.mul_diagonal,Matrix.conjTranspose_apply]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [Matrix.add_apply,Matrix.add_apply,entry F' (x ∘ e),entry G' (y ∘ f),
      entry F x,entry G y,← sum_nonzero_frame_rows F x j k,← sum_nonzero_frame_rows G y j k]
    calc
      _ = (∑ i : A, (w i : ℂ) * (x (e i) * (star (F (e i) j) * F (e i) k))) +
          (∑ i : B, (z i : ℂ) * (y (f i) * (star (G (f i) j) * G (f i) k))) := by
        congr 1
        · apply Finset.sum_congr rfl
          intro i _
          rw [Function.comp_apply,hF']
          ring
        · apply Finset.sum_congr rfl
          intro i _
          rw [Function.comp_apply,hG']
          ring
      _ = _ := mom

/-- Any strict scalar failure at positive overlap has a failure with at
most (4k^2) old labels in total and exactly the same determinant. -/
theorem exists_joint_sparse_scalar_frame_counterexample
    {I J K : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype K] [DecidableEq K] [Nonempty K]
    (x : I → ℂ) (y : J → ℂ) (F : Matrix I K ℂ) (G : Matrix J K ℂ)
    (hF : Fᴴ * F = 1) (hG : Gᴴ * G = 1)
    (h : (Fᴴ * diagonal x * F + Gᴴ * diagonal y * G).det ∉
      convexHull ℝ (partialFrameVertices (κ := K) x y)) :
    ∃ (I' J' : Type) (_ : Fintype I') (_ : Fintype J')
      (_ : DecidableEq I') (_ : DecidableEq J')
      (e : I' ↪ I) (f : J' ↪ J) (F' : Matrix I' K ℂ) (G' : Matrix J' K ℂ),
      Fintype.card I' + Fintype.card J' ≤ 4 * Fintype.card K ^ 2 ∧
      F'ᴴ * F' = 1 ∧ G'ᴴ * G' = 1 ∧
      (F'ᴴ * diagonal (x ∘ e) * F' + G'ᴴ * diagonal (y ∘ f) * G').det =
        (Fᴴ * diagonal x * F + Gᴴ * diagonal y * G).det ∧
      (F'ᴴ * diagonal (x ∘ e) * F' + G'ᴴ * diagonal (y ∘ f) * G').det ∉
        convexHull ℝ (partialFrameVertices (κ := K) (x ∘ e) (y ∘ f)) := by
  obtain ⟨I',J',hi,hj,di,dj,e,f,F',G',hIJ,hFi,hGj,hSum⟩ :=
    exists_joint_sparse_frames_same_sum x y F G hF hG
  refine ⟨I',J',hi,hj,di,dj,e,f,F',G',hIJ,hFi,hGj,congrArg Matrix.det hSum,?_⟩
  rw [hSum]
  exact fun hm => h (convexHull_mono (partialFrameVertices_restrict_subset x y e f) hm)

/-- MOC through order (4k^2-k) implies the scalar frame law at positive
overlap (k), regardless of the starting frame sizes. This is a
reduction to a bounded order, not an enumeration or a verification of MOC. -/
theorem scalar_frame_law_of_joint_bounded_orders
    {I J K : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype K] [DecidableEq K] [Nonempty K]
    (x : I → ℂ) (y : J → ℂ) (F : Matrix I K ℂ) (G : Matrix J K ℂ)
    (hF : Fᴴ * F = 1) (hG : Gᴴ * G = 1)
    (hMOC : ∀ m ≤ 4 * Fintype.card K ^ 2 - Fintype.card K, Conjecture (Fin m)) :
    (Fᴴ * diagonal x * F + Gᴴ * diagonal y * G).det ∈
      convexHull ℝ (partialFrameVertices (κ := K) x y) := by
  by_contra h
  obtain ⟨I',J',_,_,_,_,e,f,F',G',hIJ,hF',hG',_,h'⟩ :=
    exists_joint_sparse_scalar_frame_counterexample x y F G hF hG h
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

/-- Overlap three reduces to MOC through order 33. -/
theorem scalar_frame_overlap_three_of_orders_le_33
    {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (x : I → ℂ) (y : J → ℂ) (F : Matrix I (Fin 3) ℂ) (G : Matrix J (Fin 3) ℂ)
    (hF : Fᴴ * F = 1) (hG : Gᴴ * G = 1)
    (hMOC : ∀ m ≤ 33, Conjecture (Fin m)) :
    (Fᴴ * diagonal x * F + Gᴴ * diagonal y * G).det ∈
      convexHull ℝ (partialFrameVertices (κ := Fin 3) x y) := by
  exact scalar_frame_law_of_joint_bounded_orders x y F G hF hG (by
    simpa [Fintype.card_fin] using hMOC)


end
end MOC
