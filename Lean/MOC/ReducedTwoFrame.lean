import MOC.RankTwoOverlap
import MOC.Small
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! Normal reciprocal padding for the two-frame compression problem. -/

open BigOperators Matrix
open scoped InnerProductSpace

namespace MOC

noncomputable section

variable {ι κ ρ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype ρ] [DecidableEq ρ] [Fintype σ] [DecidableEq σ]

/-- Products over partial matchings with `κ` distinct slots. -/
def partialFrameMatching (x : ρ → ℂ) (y : σ → ℂ)
    (p : (κ ↪ ρ) × (κ ↪ σ)) : ℂ := ∏ k, (x (p.1 k) + y (p.2 k))

omit [DecidableEq ι] in
private theorem product_nonzero_subtype (a : ι → ℂ) :
    (∏ i, if a i = 0 then 1 else a i) = ∏ i : {i // a i ≠ 0}, a i := by
  apply Finset.prod_congr_set {i | a i ≠ 0}
  · intro i hi
    exact if_neg hi
  · intro i hi
    apply if_pos
    simpa using hi

/-- Include zero exactly when both padded spectra have at least one zero slot. -/
def partialFrameVertices (x : ρ → ℂ) (y : σ → ℂ) : Set ℂ :=
  Set.range (partialFrameMatching (κ := κ) x y) ∪
    {z | z = 0 ∧ Fintype.card κ < Fintype.card ρ ∧ Fintype.card κ < Fintype.card σ}

omit [DecidableEq ι] in
private theorem support_card_lt_of_zero (a : ι → ℂ) (i : ι) (hi : a i = 0) :
    (spectralSupport a).card < Fintype.card ι := by
  rw [← Finset.card_univ]
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, ?_⟩
  intro h
  have hm : i ∈ spectralSupport a := h.symm ▸ Finset.mem_univ i
  simp [spectralSupport, hi] at hm

omit [DecidableEq κ] in
/-- Every matching product of a reciprocal-padded pair either vanishes
or is a common nonzero factor times the product over its occupied
overlap slots. No completion of partial matchings is needed here. -/
theorem matchingProduct_zero_or_partialFrameReciprocal
    (a b : ι → ℂ) (τ : Equiv.Perm ι)
    (h : (spectralSupport a).card + (spectralSupport b).card =
      Fintype.card ι + Fintype.card κ) :
    let D := (∏ i : {i // a i ≠ 0}, a i) * ∏ j : {j // b j ≠ 0}, b j
    (matchingProduct a b τ = 0 ∧ (spectralSupport a).card < Fintype.card ι ∧
      (spectralSupport b).card < Fintype.card ι) ∨
      ∃ p : (κ ↪ {i // a i ≠ 0}) × (κ ↪ {j // b j ≠ 0}),
        matchingProduct a b τ = D *
          partialFrameMatching (fun i : {i // a i ≠ 0} => (a i)⁻¹) (fun j : {j // b j ≠ 0} => (b j)⁻¹) p := by
  classical
  intro D
  by_cases hcov : CoversSupports a b τ
  · right
    let J := spectralSupport (a ∘ τ) ∩ spectralSupport b
    have hcard : J.card = Fintype.card κ := by
      dsimp only [J]
      rw [cover_overlap_card a b τ hcov, h]
      omega
    have haJ (j : J) : a (τ j) ≠ 0 := by
      have hj := (Finset.mem_inter.mp j.property).1
      simpa [spectralSupport] using hj
    have hbJ (j : J) : b j ≠ 0 := by
      have hj := (Finset.mem_inter.mp j.property).2
      simpa [spectralSupport] using hj
    let e : κ ≃ J := Fintype.equivOfCardEq (by simpa using hcard.symm)
    let p : κ ↪ {i // a i ≠ 0} := ⟨fun k => ⟨τ (e k), haJ (e k)⟩, by
      intro i j h'; exact e.injective (Subtype.val_injective (τ.injective (congrArg (fun z : {i : ι // a i ≠ 0} => z.val) h')))⟩
    let q : κ ↪ {j // b j ≠ 0} := ⟨fun k => ⟨e k, hbJ (e k)⟩, by
      intro i j h'; exact e.injective (Subtype.val_injective (congrArg (fun z : {j : ι // b j ≠ 0} => z.val) h'))⟩
    refine ⟨(p,q), ?_⟩
    let f (j : ι) := (if a (τ j) = 0 then 1 else a (τ j)) * (if b j = 0 then 1 else b j)
    let g (j : ι) := if j ∈ J then (a (τ j))⁻¹ + (b j)⁻¹ else 1
    have hv (j : ι) : a (τ j) + b j = f j * g j := by
      by_cases ha : a (τ j) = 0 <;> by_cases hb : b j = 0
      · exact ((hcov j).elim (fun hne => hne ha) (fun hne => hne hb)).elim
      · simp [f, g, J, spectralSupport, ha, hb]
      · simp [f, g, J, spectralSupport, ha, hb]
      · simp [f, g, J, spectralSupport, ha, hb]
        field_simp
        ring
    have hf : (∏ j, f j) = D := by
      dsimp only [f, D]
      rw [Finset.prod_mul_distrib, Equiv.prod_comp τ (fun i => if a i = 0 then 1 else a i),
        product_nonzero_subtype a, product_nonzero_subtype b]
    have hg : (∏ j, g j) =
        partialFrameMatching (fun i : {i // a i ≠ 0} => (a i)⁻¹)
          (fun j : {j // b j ≠ 0} => (b j)⁻¹) (p,q) := by
      calc
        _ = ∏ j ∈ J, g j := by
          symm
          apply Finset.prod_subset (Finset.subset_univ _)
          intro j _ hj
          simp [g, hj]
        _ = ∏ j : J, g j := (Finset.prod_coe_sort J _).symm
        _ = ∏ k : κ, g (e k) := (Equiv.prod_comp e (fun j : J => g j)).symm
        _ = _ := by simp [g, partialFrameMatching, p, q]
    unfold matchingProduct
    simp only [hv, Finset.prod_mul_distrib, hf, hg]
  · left
    obtain ⟨j, hj⟩ := not_forall.mp hcov
    have hz : a (τ j) = 0 ∧ b j = 0 := by simpa using hj
    refine ⟨?_, support_card_lt_of_zero a (τ j) hz.1, support_card_lt_of_zero b j hz.2⟩
    unfold matchingProduct
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp [hz.1, hz.2]


/-- If the reciprocal padded spectral pair has the determinant-hull property,
then its overlap compression has the partial-matching convex law, provided the
support Gram has the maximal value. Thus no forward matching extension is needed. -/
theorem det_overlap_mem_partialFrameHull_of_holds
    (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hholds : Holds a b U)
    (h : (spectralSupport a).card + (spectralSupport b).card =
      Fintype.card ι + Fintype.card κ)
    (E : Matrix {i // a i ≠ 0} κ ℂ) (F : Matrix {j // b j ≠ 0} κ ℂ)
    (hE : Eᴴ * E = 1) (hF : Fᴴ * F = 1)
    (hcommon : (1 : Matrix ι ι ℂ).submatrix id Subtype.val * E =
      U.submatrix id Subtype.val * F)
    (hGram : let X := (1 : Matrix ι ι ℂ).submatrix id (Subtype.val : {i // a i ≠ 0} → ι)
      let Y := U.submatrix id (Subtype.val : {j // b j ≠ 0} → ι)
      (X * Xᴴ + Y * Yᴴ).det = (2 : ℂ) ^ Fintype.card κ) :
    (Eᴴ * diagonal (fun i : {i // a i ≠ 0} => (a i)⁻¹) * E +
      Fᴴ * diagonal (fun j : {j // b j ≠ 0} => (b j)⁻¹) * F).det ∈ convexHull ℝ
      (partialFrameVertices (κ := κ)
        (fun i : {i // a i ≠ 0} => (a i)⁻¹) (fun j : {j // b j ≠ 0} => (b j)⁻¹)) := by
  classical
  let ρ := {i // a i ≠ 0}
  let σ := {j // b j ≠ 0}
  let X : Matrix ι ρ ℂ := (1 : Matrix ι ι ℂ).submatrix id Subtype.val
  let Y : Matrix ι σ ℂ := U.submatrix id Subtype.val
  let a' : ρ → ℂ := fun i => a i
  let b' : σ → ℂ := fun j => b j
  let D := (∏ i, a' i) * ∏ j, b' j
  let G := X * Xᴴ + Y * Yᴴ
  let vertices := partialFrameVertices (κ := κ)
    (fun i : ρ => (a' i)⁻¹) (fun j : σ => (b' j)⁻¹)
  let z := (Eᴴ * diagonal (fun i => (a' i)⁻¹) * E +
      Fᴴ * diagonal (fun j => (b' j)⁻¹) * F).det
  change z ∈ convexHull ℝ vertices
  have hdet : determinantValue a b U = (X * diagonal a' * Xᴴ + Y * diagonal b' * Yᴴ).det := by
    unfold determinantValue
    rw [weighted_support_columns 1 a a (fun _ h₀ => h₀),
      weighted_support_columns U b b (fun _ h₀ => h₀), Matrix.one_mul,
      Matrix.conjTranspose_one, Matrix.mul_one]
  have hρ : Fintype.card ρ = (spectralSupport a).card := Fintype.card_of_subtype _ (by
    simp [spectralSupport])
  have hσ : Fintype.card σ = (spectralSupport b).card := Fintype.card_of_subtype _ (by
    simp [spectralSupport])
  let e : ι ⊕ κ ≃ ρ ⊕ σ := Fintype.equivOfCardEq (by
    rw [Fintype.card_sum, Fintype.card_sum, hρ, hσ, h])
  have htwo : (2 : ℂ) ^ Fintype.card κ ≠ 0 := pow_ne_zero _ (by norm_num)
  have hG : IsUnit G.det := isUnit_iff_ne_zero.mpr (by
    change G.det = _ at hGram
    rw [hGram]
    exact htwo)
  have hscaled : determinantValue a b U = D * z := by
    rw [hdet]
    have hp := det_support_frames e X Y E F hE hF hcommon hG a' b'
      (fun i => i.property) (fun j => j.property)
    change _ = D * (G.det / (2 : ℂ) ^ Fintype.card κ) * z at hp
    change G.det = _ at hGram
    simpa [hGram, div_self htwo] using hp
  have hD : D ≠ 0 := by
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => i.property))
      (Finset.prod_ne_zero_iff.mpr (fun j _ => j.property))
  let L : ℂ →ₗ[ℝ] ℂ := LinearMap.mulLeft ℝ D⁻¹
  have hinc : Set.range (matchingProduct a b) ⊆ L ⁻¹' (convexHull ℝ vertices) := by
    rintro _ ⟨τ, rfl⟩
    rcases matchingProduct_zero_or_partialFrameReciprocal (κ := κ) a b τ h with
      ⟨hz, ha, hb⟩ | ⟨p, hp⟩
    · change D⁻¹ * matchingProduct a b τ ∈ convexHull ℝ vertices
      rw [hz, mul_zero]
      apply subset_convexHull ℝ _
      right
      refine ⟨rfl, ?_, ?_⟩
      · rw [hρ]; omega
      · rw [hσ]; omega
    · change matchingProduct a b τ = D *
        partialFrameMatching (fun i : ρ => (a' i)⁻¹) (fun j : σ => (b' j)⁻¹) p at hp
      change D⁻¹ * matchingProduct a b τ ∈ convexHull ℝ vertices
      rw [hp, ← mul_assoc, inv_mul_cancel₀ hD, one_mul]
      exact subset_convexHull ℝ _ (Or.inl ⟨p, rfl⟩)
  have hm := convexHull_min hinc ((convex_convexHull ℝ _).linear_preimage L) hholds
  change D⁻¹ * determinantValue a b U ∈ convexHull ℝ vertices at hm
  simpa [hscaled, ← mul_assoc, inv_mul_cancel₀ hD] using hm


/-- Complete any rectangular isometry to a unitary at specified column labels. -/
theorem exists_unitary_retained_columns (c : ρ ↪ ι) (Y : Matrix ι ρ ℂ)
    (hY : Yᴴ * Y = 1) :
    ∃ U : Matrix ι ι ℂ, IsUnitary U ∧ U.submatrix id c = Y := by
  classical
  let v (k : ρ) : EuclideanSpace ℂ ι := (WithLp.equiv 2 _).symm (fun j => Y j k)
  have hv : Orthonormal ℂ v := by
    apply orthonormal_iff_ite.mpr
    intro k l
    have h := congrArg (fun M : Matrix ρ ρ ℂ => M k l) hY
    dsimp only [v]
    rw [EuclideanSpace.inner_piLp_equiv_symm]
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, dotProduct,
      Pi.star_apply, mul_comm] using h
  let e := Equiv.ofInjective c c.injective
  let s := Set.range c
  let f (i : ι) : EuclideanSpace ℂ ι := if hi : i ∈ s then v (e.symm ⟨i, hi⟩) else 0
  have hf_retained (k : ρ) : f (c k) = v k := by
    have hk : c k ∈ s := ⟨k, rfl⟩
    change (if hi : c k ∈ s then v (e.symm ⟨c k, hi⟩) else 0) = v k
    rw [dif_pos hk]
    exact congrArg v (e.symm_apply_apply k)
  have hf : Orthonormal ℂ (s.restrict f) := by
    have he : s.restrict f = v ∘ e.symm := by
      funext k
      change (if hi : k.val ∈ s then v (e.symm ⟨k.val, hi⟩) else 0) = _
      rw [dif_pos k.property]
      rfl
    rw [he]
    exact hv.comp _ e.symm.injective
  obtain ⟨B, hB⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (by simp : Module.finrank ℂ (EuclideanSpace ℂ ι) = Fintype.card ι) hf
  let U : Matrix ι ι ℂ := Matrix.of fun j k => B k j
  have hU : Uᴴ * U = 1 := by
    ext k l : 1
    have h := orthonormal_iff_ite.mp B.orthonormal k l
    rw [EuclideanSpace.inner_eq_star_dotProduct] at h
    change (∑ j, B l j * star (B k j)) = if k = l then (1 : ℂ) else 0 at h
    simpa only [U, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply, mul_comm] using h
  refine ⟨U, ⟨Matrix.mul_eq_one_comm.mp hU, hU⟩, ?_⟩
  ext j k : 1
  change B (c k) j = Y j k
  rw [hB _ ⟨k, rfl⟩, hf_retained]
  rfl

private theorem card_le_of_frame {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (A : Matrix β α ℂ) (hA : Aᴴ * A = 1) :
    Fintype.card α ≤ Fintype.card β := by
  have hi : Function.Injective (Matrix.toEuclideanLin A) :=
    Function.LeftInverse.injective (g := Matrix.toEuclideanLin Aᴴ) (by
      intro v
      apply (WithLp.equiv 2 _).injective
      simp only [Matrix.piLp_equiv_toEuclideanLin_apply, Matrix.mulVec_mulVec, hA,
        Matrix.one_mulVec])
  simpa only [finrank_euclideanSpace] using LinearMap.finrank_le_finrank_of_injective hi

/-- Complete a frame with an orthogonal complementary frame. -/
theorem exists_complementary_frame (F : Matrix σ κ ℂ) (hF : Fᴴ * F = 1) :
    ∃ Z : Matrix σ (Fin (Fintype.card σ - Fintype.card κ)) ℂ,
      Zᴴ * Z = 1 ∧ Fᴴ * Z = 0 ∧ F * Fᴴ + Z * Zᴴ = 1 := by
  classical
  have hle := card_le_of_frame F hF
  let κ' := Fin (Fintype.card σ - Fintype.card κ)
  let e : κ ⊕ κ' ≃ σ := Fintype.equivOfCardEq (by
    rw [Fintype.card_sum, Fintype.card_fin]
    omega)
  let c : κ ↪ σ := Function.Embedding.inl.trans e.toEmbedding
  obtain ⟨U, hU, hUF⟩ := exists_unitary_retained_columns c F hF
  let Z : Matrix σ κ' ℂ := U.submatrix id (fun i => e (Sum.inr i))
  let V : Matrix σ (κ ⊕ κ') ℂ := U.submatrix id e
  have hV : V = fromCols F Z := by
    rw [← hUF]
    ext i j
    cases j <;> rfl
  have hc : Vᴴ * V = 1 := by
    dsimp only [V]
    rw [Matrix.conjTranspose_submatrix, ← Matrix.submatrix_mul Uᴴ U e id e
      Function.bijective_id, hU.2, Matrix.submatrix_one_equiv]
  have hr : V * Vᴴ = 1 := by
    dsimp only [V]
    rw [Matrix.conjTranspose_submatrix, ← Matrix.submatrix_mul U Uᴴ id e id e.bijective,
      hU.1, Matrix.submatrix_id_id]
  rw [hV, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
    Matrix.fromRows_mul_fromCols] at hc
  rw [hV, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
    Matrix.fromCols_mul_fromRows] at hr
  rw [← Matrix.fromBlocks_one] at hc
  have h11 := congrArg Matrix.toBlocks₂₂ hc
  have h12 := congrArg Matrix.toBlocks₁₂ hc
  exact ⟨Z, by simpa only [Matrix.toBlocks_fromBlocks₂₂] using h11,
    by simpa only [Matrix.toBlocks_fromBlocks₁₂] using h12, hr⟩


/-- Realize a pair of frames as the shared part of two ambient isometries,
with left columns at the canonical labels and the Gram determinant maximal. -/
theorem exists_maximal_gram_realization
    (E : Matrix ρ κ ℂ) (F : Matrix σ κ ℂ) (hE : Eᴴ * E = 1) (hF : Fᴴ * F = 1) :
    let ι' := ρ ⊕ Fin (Fintype.card σ - Fintype.card κ)
    let X : Matrix ι' ρ ℂ := fromRows 1 0
    ∃ Y : Matrix ι' σ ℂ, Yᴴ * Y = 1 ∧ X * E = Y * F ∧
      (X * Xᴴ + Y * Yᴴ).det = (2 : ℂ) ^ Fintype.card κ := by
  classical
  dsimp
  obtain ⟨Z, hZ, hFZ, hdecomp⟩ := exists_complementary_frame F hF
  have hZF : Zᴴ * F = 0 := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_zero] using congrArg Matrix.conjTranspose hFZ
  let Y := fromRows (E * Fᴴ) Zᴴ
  refine ⟨Y, ?_, ?_, ?_⟩
  · dsimp only [Y]
    rw [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
      Matrix.fromCols_mul_fromRows, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc F, ← Matrix.mul_assoc Eᴴ, hE, Matrix.one_mul, hdecomp]
  · dsimp only [Y]
    rw [Matrix.fromRows_mul, Matrix.fromRows_mul, Matrix.one_mul, Matrix.zero_mul,
      Matrix.mul_assoc, hF, Matrix.mul_one, hZF]
  · dsimp only [Y]
    simp only [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
      Matrix.fromRows_mul_fromCols, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_one,
      Matrix.conjTranspose_zero, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul,
      Matrix.fromBlocks_add, add_zero, zero_add]
    have hFF : E * Fᴴ * (F * Eᴴ) = E * Eᴴ := by
      rw [Matrix.mul_assoc E, ← Matrix.mul_assoc Fᴴ, hF, Matrix.one_mul]
    have hFZ' : E * Fᴴ * Z = 0 := by rw [Matrix.mul_assoc, hFZ, Matrix.mul_zero]
    have hZF' : Zᴴ * (F * Eᴴ) = 0 := by rw [← Matrix.mul_assoc, hZF, Matrix.zero_mul]
    rw [hFF, hFZ', hZF', hZ, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one,
      Matrix.det_one_add_mul_comm, hE, ← two_smul ℂ (1 : Matrix κ κ ℂ),
      Matrix.det_smul, Matrix.det_one, mul_one]


private def paddedReciprocal {α β : Type*} (c : α ↪ β) (x : α → ℂ) (i : β) : ℂ := by
  classical
  exact
    if h : i ∈ Set.range c then (x ((Equiv.ofInjective c c.injective).symm ⟨i,h⟩))⁻¹ else 0

private theorem paddedReciprocal_at {α β : Type*} (c : α ↪ β) (x : α → ℂ) (i : α) :
    paddedReciprocal c x (c i) = (x i)⁻¹ := by
  classical
  unfold paddedReciprocal
  rw [dif_pos (show c i ∈ Set.range c from ⟨i, rfl⟩)]
  exact congrArg (fun j => (x j)⁻¹) ((Equiv.ofInjective c c.injective).symm_apply_apply i)

private theorem paddedReciprocal_mem {α β : Type*} (c : α ↪ β) (x : α → ℂ)
    (hx : ∀ i, x i ≠ 0) (i : β) :
    paddedReciprocal c x i ≠ 0 ↔ i ∈ Set.range c := by
  classical
  unfold paddedReciprocal
  by_cases hi : i ∈ Set.range c
  · rw [dif_pos hi]
    exact iff_of_true
      (inv_ne_zero (hx ((Equiv.ofInjective c c.injective).symm ⟨i, hi⟩))) hi
  · rw [dif_neg hi]
    exact iff_of_false (fun h => h rfl) hi

private def paddedReciprocalEquiv {α β : Type*} (c : α ↪ β) (x : α → ℂ)
    (hx : ∀ i, x i ≠ 0) :
    {i : β // paddedReciprocal c x i ≠ 0} ≃ α :=
  (Equiv.subtypeEquivRight (paddedReciprocal_mem c x hx)).trans
    (Equiv.ofInjective c c.injective).symm

private theorem paddedReciprocalEquiv_label {α β : Type*} (c : α ↪ β) (x : α → ℂ)
    (hx : ∀ i, x i ≠ 0) (i : {i : β // paddedReciprocal c x i ≠ 0}) :
    c (paddedReciprocalEquiv c x hx i) = i.val := by
  exact congrArg Subtype.val ((Equiv.ofInjective c c.injective).apply_symm_apply
    ⟨i.val, (paddedReciprocal_mem c x hx i).mp i.property⟩)

private theorem paddedReciprocalEquiv_value {α β : Type*} (c : α ↪ β) (x : α → ℂ)
    (hx : ∀ i, x i ≠ 0) (i : {i : β // paddedReciprocal c x i ≠ 0}) :
    (paddedReciprocal c x i)⁻¹ = x (paddedReciprocalEquiv c x hx i) := by
  let j := paddedReciprocalEquiv c x hx i
  change (paddedReciprocal c x i)⁻¹ = x j
  rw [← paddedReciprocalEquiv_label c x hx i, paddedReciprocal_at, inv_inv]

omit [Fintype ρ] in
private theorem diagonal_constant_eq_smul_identity (t : ℂ) :
    diagonal (fun _ : ρ => t) = t • (1 : Matrix ρ ρ ℂ) := by
  ext i j : 1
  by_cases h : i = j <;> simp [Matrix.diagonal_apply, Matrix.one_apply, h]

/-- An order-`card ρ + card σ - card κ` MOC result implies the
`κ`-edge two-frame compression law. A zero vertex may be included. -/
theorem det_twoFrame_mem_partialFrameVertices_of_reducedOrder
    (E : Matrix ρ κ ℂ) (F : Matrix σ κ ℂ) (hE : Eᴴ * E = 1) (hF : Fᴴ * F = 1)
    (hMOC : Conjecture (ρ ⊕ Fin (Fintype.card σ - Fintype.card κ)))
    (x₀ : ρ → ℂ) (y₀ : σ → ℂ) :
    (Eᴴ * diagonal x₀ * E + Fᴴ * diagonal y₀ * F).det ∈ convexHull ℝ
      (partialFrameVertices (κ := κ) x₀ y₀) := by
  classical
  let ι' := ρ ⊕ Fin (Fintype.card σ - Fintype.card κ)
  obtain ⟨t, ht⟩ := ((Set.finite_range (fun i => -x₀ i)).union
    (Set.finite_range y₀)).exists_not_mem
  let x (i : ρ) := x₀ i + t
  let y (j : σ) := y₀ j - t
  have hx (i : ρ) : x i ≠ 0 := fun he => ht (Or.inl ⟨i, (eq_neg_of_add_eq_zero_right he).symm⟩)
  have hy (j : σ) : y j ≠ 0 := fun he => ht (Or.inr ⟨j, sub_eq_zero.mp he⟩)
  have hvertices : partialFrameMatching (κ := κ) x₀ y₀ = partialFrameMatching x y := by
    funext p
    apply Finset.prod_congr rfl
    intro k _
    simp only [x, y]
    ring
  have hleft : Eᴴ * diagonal x * E = Eᴴ * diagonal x₀ * E + t • (1 : Matrix κ κ ℂ) := by
    rw [show diagonal x = diagonal x₀ + diagonal (fun _ : ρ => t) from
      (Matrix.diagonal_add x₀ _).symm,
      diagonal_constant_eq_smul_identity, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hE]
  have hright : Fᴴ * diagonal y * F = Fᴴ * diagonal y₀ * F - t • (1 : Matrix κ κ ℂ) := by
    rw [show diagonal y = diagonal y₀ - diagonal (fun _ : σ => t) from
      (Matrix.diagonal_sub y₀ _).symm,
      diagonal_constant_eq_smul_identity, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hF]
  have hmatrix : Eᴴ * diagonal x * E + Fᴴ * diagonal y * F =
      Eᴴ * diagonal x₀ * E + Fᴴ * diagonal y₀ * F := by rw [hleft, hright]; abel
  unfold partialFrameVertices
  rw [hvertices, ← hmatrix]
  obtain ⟨Y, hY, hcommon, hGram⟩ := exists_maximal_gram_realization E F hE hF
  let X : Matrix ι' ρ ℂ := fromRows 1 0
  change X * E = Y * F at hcommon
  change (X * Xᴴ + Y * Yᴴ).det = _ at hGram
  have hκσ := card_le_of_frame F hF
  have hκρ := card_le_of_frame E hE
  have hι' : Fintype.card ι' = Fintype.card ρ + (Fintype.card σ - Fintype.card κ) := by
    simp [ι']
  have hσι : Fintype.card σ ≤ Fintype.card ι' := by rw [hι']; omega
  let c : ρ ↪ ι' := Function.Embedding.inl
  let d : σ ↪ ι' := (Fintype.equivFin σ).toEmbedding.trans <|
    (Fin.castLEEmb hσι).trans (Fintype.equivFin ι').symm.toEmbedding
  obtain ⟨U, hU, hUY⟩ := exists_unitary_retained_columns d Y hY
  let a := paddedReciprocal c x
  let b := paddedReciprocal d y
  let e : {i // a i ≠ 0} ≃ ρ := paddedReciprocalEquiv c x hx
  let f : {j // b j ≠ 0} ≃ σ := paddedReciprocalEquiv d y hy
  let E' : Matrix {i // a i ≠ 0} κ ℂ := E.submatrix e id
  let F' : Matrix {j // b j ≠ 0} κ ℂ := F.submatrix f id
  have hc : (1 : Matrix ι' ι' ℂ).submatrix id c = X := by
    ext i j : 1
    cases i with
    | inl i =>
        simp only [c, Function.Embedding.inl_apply, X, Matrix.submatrix_apply, id_eq,
          Matrix.fromRows_apply_inl, Matrix.one_apply, Sum.inl.injEq]
        change (if (Sum.inl i : ι') = Sum.inl j then (1 : ℂ) else 0) = _
        simp
    | inr i =>
        simp only [c, Function.Embedding.inl_apply, X, Matrix.submatrix_apply, id_eq,
          Matrix.fromRows_apply_inr, Matrix.one_apply, reduceCtorEq, if_false, Matrix.zero_apply]
        change (if (Sum.inr i : ι') = Sum.inl j then (1 : ℂ) else 0) = _
        simp
  have hXe : (1 : Matrix ι' ι' ℂ).submatrix id
      (Subtype.val : {i // a i ≠ 0} → ι') = X.submatrix id e := by
    rw [← hc]
    ext i j : 1
    change (1 : Matrix ι' ι' ℂ) i j.val = (1 : Matrix ι' ι' ℂ) i (c (e j))
    rw [paddedReciprocalEquiv_label c x hx j]
  have hYf : U.submatrix id (Subtype.val : {j // b j ≠ 0} → ι') = Y.submatrix id f := by
    rw [← hUY]
    ext i j : 1
    change U i j.val = U i (d (f j))
    rw [paddedReciprocalEquiv_label d y hy j]
  have hsupport (w : ι' → ℂ) :
      (spectralSupport w).card = Fintype.card {i // w i ≠ 0} :=
    (Fintype.card_of_subtype _ (by simp [spectralSupport])).symm
  have hpad : (spectralSupport a).card + (spectralSupport b).card =
      Fintype.card ι' + Fintype.card κ := by
    rw [hsupport, hsupport, Fintype.card_congr e, Fintype.card_congr f, hι']
    omega
  have hE' : E'ᴴ * E' = 1 := by
    dsimp only [E']
    rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, hE]
    rfl
  have hF' : F'ᴴ * F' = 1 := by
    dsimp only [F']
    rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, hF]
    rfl
  have hcommon' : (1 : Matrix ι' ι' ℂ).submatrix id Subtype.val * E' =
      U.submatrix id Subtype.val * F' := by
    rw [hXe, hYf]
    dsimp only [E', F']
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, hcommon]
  let X' := (1 : Matrix ι' ι' ℂ).submatrix id (Subtype.val : {i // a i ≠ 0} → ι')
  let Y' := U.submatrix id (Subtype.val : {j // b j ≠ 0} → ι')
  have hGram' : (X' * X'ᴴ + Y' * Y'ᴴ).det = (2 : ℂ) ^ Fintype.card κ := by
    dsimp only [X', Y']
    rw [hXe, hYf, Matrix.conjTranspose_submatrix, Matrix.conjTranspose_submatrix,
      Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
    exact hGram
  have hax : (fun i : {i // a i ≠ 0} => (a i)⁻¹) = x ∘ e := by
    funext i
    exact paddedReciprocalEquiv_value c x hx i
  have hby : (fun j : {j // b j ≠ 0} => (b j)⁻¹) = y ∘ f := by
    funext j
    exact paddedReciprocalEquiv_value d y hy j
  have h := det_overlap_mem_partialFrameHull_of_holds a b U (hMOC a b U hU)
    hpad E' F' hE' hF' hcommon' hGram'
  rw [hax, hby] at h
  dsimp only [E', F'] at h
  rw [← Matrix.submatrix_diagonal_equiv x e, ← Matrix.submatrix_diagonal_equiv y f,
    Matrix.conjTranspose_submatrix, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv,
    Matrix.submatrix_mul_equiv] at h
  apply convexHull_mono _ h
  intro z hz
  rcases hz with ⟨p, rfl⟩ | ⟨hz, hp, hq⟩
  · exact Or.inl ⟨(p.1.trans e.toEmbedding, p.2.trans f.toEmbedding), rfl⟩
  · rw [Fintype.card_congr e] at hp
    rw [Fintype.card_congr f] at hq
    exact Or.inr ⟨hz, hp, hq⟩

/-- The same reduced-order compression law with zero included unconditionally. -/
theorem det_twoFrame_mem_partialFrameHull_of_reducedOrder
    (E : Matrix ρ κ ℂ) (F : Matrix σ κ ℂ) (hE : Eᴴ * E = 1) (hF : Fᴴ * F = 1)
    (hMOC : Conjecture (ρ ⊕ Fin (Fintype.card σ - Fintype.card κ)))
    (x : ρ → ℂ) (y : σ → ℂ) :
    (Eᴴ * diagonal x * E + Fᴴ * diagonal y * F).det ∈ convexHull ℝ
      (insert 0 (Set.range (partialFrameMatching (κ := κ) x y))) := by
  apply convexHull_mono _ (det_twoFrame_mem_partialFrameVertices_of_reducedOrder E F hE hF hMOC x y)
  rintro z (hz | ⟨rfl, _, _⟩)
  · exact Set.mem_insert_of_mem _ hz
  · exact Set.mem_insert _ _

/-- At full overlap one spectrum has no zero slots in the padded pair, so
the partial-matching products suffice without an added zero vertex. -/
theorem det_twoFrame_mem_partialFrameHull_of_reducedOrder_fullOverlap
    (E : Matrix ρ κ ℂ) (F : Matrix σ κ ℂ) (hE : Eᴴ * E = 1) (hF : Fᴴ * F = 1)
    (hMOC : Conjecture (ρ ⊕ Fin (Fintype.card σ - Fintype.card κ)))
    (hfull : Fintype.card κ = Fintype.card ρ ∨ Fintype.card κ = Fintype.card σ)
    (x : ρ → ℂ) (y : σ → ℂ) :
    (Eᴴ * diagonal x * E + Fᴴ * diagonal y * F).det ∈ convexHull ℝ
      (Set.range (partialFrameMatching (κ := κ) x y)) := by
  apply convexHull_mono _ (det_twoFrame_mem_partialFrameVertices_of_reducedOrder E F hE hF hMOC x y)
  rintro z (hz | ⟨_, hp, hq⟩)
  · exact hz
  · rcases hfull with hfull | hfull <;> omega


/-- Any positive-dimensional overlap compression follows from MOC in
orders strictly below the sum of its two support sizes. -/
theorem det_twoFrame_mem_partialFrameVertices_of_smallerOrders [Nonempty κ]
    (E : Matrix ρ κ ℂ) (F : Matrix σ κ ℂ) (hE : Eᴴ * E = 1) (hF : Fᴴ * F = 1)
    (hsmall : ∀ m < Fintype.card ρ + Fintype.card σ, Conjecture (Fin m))
    (x : ρ → ℂ) (y : σ → ℂ) :
    (Eᴴ * diagonal x * E + Fᴴ * diagonal y * F).det ∈ convexHull ℝ
      (partialFrameVertices (κ := κ) x y) := by
  apply det_twoFrame_mem_partialFrameVertices_of_reducedOrder E F hE hF _ x y
  let ι' := ρ ⊕ Fin (Fintype.card σ - Fintype.card κ)
  change Conjecture ι'
  apply (conjecture_reindex_iff (Fintype.equivFin ι')).mpr
  apply hsmall
  have hκ : 0 < Fintype.card κ := Fintype.card_pos
  have hκσ := card_le_of_frame F hF
  simp only [ι', Fintype.card_sum, Fintype.card_fin]
  omega

end

end MOC
