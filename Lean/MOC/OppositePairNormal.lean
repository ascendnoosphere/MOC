import MOC.OppositePair
import MOC.SupportedCompressionReduction

/-! When the two reciprocal compressions at a marked zero pair are normal,
the hull inclusion reduces to the conjecture two orders lower. -/

open BigOperators Matrix Finset

namespace MOC

noncomputable section

private theorem holds_normal_coisometry {n : ℕ} (hSmall : Conjecture (Fin n))
    (a : Fin n → ℂ) (b : Fin (n + 1) → ℂ) (Y : Matrix (Fin n) (Fin (n + 1)) ℂ)
    (hY : Y * Yᴴ = 1) (hNormal : IsStarNormal (Y * diagonal b * Yᴴ)) :
    (diagonal a + Y * diagonal b * Yᴴ).det ∈
      convexHull ℝ (Set.range (rectangularMatchingProduct a b)) := by
  let p : Fin (n + 1) := 0
  obtain ⟨V, hV, hrows⟩ := exists_unitary_retained_rows Y hY p
  have hcomp : (V * diagonal b * Vᴴ).submatrix p.succAbove p.succAbove = Y * diagonal b * Yᴴ := by
    rw [← hrows, Matrix.conjTranspose_submatrix,
      Matrix.submatrix_mul _ _ p.succAbove id p.succAbove Function.bijective_id,
      Matrix.submatrix_mul _ _ p.succAbove id id Function.bijective_id, Matrix.submatrix_id_id]
  have h := holds_normal_compression hSmall a b V hV p (hcomp.symm ▸ hNormal)
  rwa [hcomp] at h

private def twoSidedMatchingProduct {n : ℕ} {ρ σ : Type*} (a : ρ → ℂ) (b : σ → ℂ)
    (m : (Fin n ↪ ρ) × (Fin n ↪ σ)) : ℂ :=
  ∏ i, (a (m.1 i) + b (m.2 i))

private theorem det_two_normal_compressions_mem_hull {n : ℕ} (hSmall : Conjecture (Fin n))
    (a b : Fin (n + 1) → ℂ) (E F : Matrix (Fin (n + 1)) (Fin n) ℂ)
    (hE : Eᴴ * E = 1) (hF : Fᴴ * F = 1)
    (hA : IsStarNormal (Eᴴ * diagonal a * E)) (hB : IsStarNormal (Fᴴ * diagonal b * F)) :
    (Eᴴ * diagonal a * E + Fᴴ * diagonal b * F).det ∈
      convexHull ℝ (Set.range (twoSidedMatchingProduct (n := n) a b)) := by
  let A := Eᴴ * diagonal a * E
  let B := Fᴴ * diagonal b * F
  obtain ⟨u, V, hV, hdiag⟩ := exists_unitary_diagonalization A hA
  let X := Vᴴ * Eᴴ
  let Y := Vᴴ * Fᴴ
  have hco {G : Matrix (Fin n) (Fin (n + 1)) ℂ} (hG : G * Gᴴ = 1) :
      (Vᴴ * G) * (Vᴴ * G)ᴴ = 1 := by
    calc
      _ = Vᴴ * (G * Gᴴ) * V := by
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = _ := by rw [hG, Matrix.mul_one, hV.2]
  have hX : X * Xᴴ = 1 :=
    hco (G := Eᴴ) (by simpa only [Matrix.conjTranspose_conjTranspose] using hE)
  have hY : Y * Yᴴ = 1 :=
    hco (G := Fᴴ) (by simpa only [Matrix.conjTranspose_conjTranspose] using hF)
  have hxc : X * diagonal a * Xᴴ = diagonal u := by
    calc
      _ = Vᴴ * A * V := by
        simp only [X, A, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = (Vᴴ * V) * diagonal u * (Vᴴ * V) := by rw [hdiag]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hV.2, Matrix.one_mul, Matrix.mul_one]
  have hyc : Y * diagonal b * Yᴴ = Vᴴ * B * V := by
    simp only [Y, B, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  have hYn : IsStarNormal (Y * diagonal b * Yᴴ) := by
    rw [hyc]
    constructor
    change (Vᴴ * B * V)ᴴ * (Vᴴ * B * V) = (Vᴴ * B * V) * (Vᴴ * B * V)ᴴ
    calc
      _ = Vᴴ * (Bᴴ * (V * Vᴴ) * B) * V := by
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = Vᴴ * (B * (V * Vᴴ) * Bᴴ) * V := by
        simp only [hV.1, Matrix.mul_one, show Bᴴ * B = B * Bᴴ from hB.star_comm_self.eq]
      _ = _ := by
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  have hdet : (A + B).det = (diagonal u + Y * diagonal b * Yᴴ).det := by
    have hU : IsUnitary Vᴴ := ⟨by simpa using hV.2, by simpa using hV.1⟩
    rw [hyc, ← hxc]
    change _ = (X * diagonal a * Xᴴ + Vᴴ * B * V).det
    have hXc : X * diagonal a * Xᴴ = Vᴴ * A * V := by
      simp only [X, A, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [hXc, ← Matrix.add_mul, ← Matrix.mul_add]
    simpa only [Matrix.conjTranspose_conjTranspose] using (det_unitary_conjugation Vᴴ (A + B) hU).symm
  change (A + B).det ∈ _
  rw [hdet]
  apply convexHull_min _ (convex_convexHull ℝ _) (holds_normal_coisometry hSmall u b Y hY hYn)
  rintro _ ⟨f, rfl⟩
  have hdiagNormal : IsStarNormal (X * diagonal a * Xᴴ) := by
    rw [hxc]
    constructor
    change (diagonal u)ᴴ * diagonal u = diagonal u * (diagonal u)ᴴ
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    exact congrArg Matrix.diagonal (funext fun i => mul_comm _ _)
  have hv := holds_normal_coisometry hSmall (b ∘ f) a X hX hdiagNormal
  have hd : (diagonal (b ∘ f) + X * diagonal a * Xᴴ).det = rectangularMatchingProduct u b f := by
    rw [hxc, Matrix.diagonal_add, Matrix.det_diagonal]
    simp [rectangularMatchingProduct, add_comm]
  rw [hd] at hv
  apply convexHull_mono _ hv
  rintro _ ⟨g, rfl⟩
  exact ⟨(g, f), by simp [rectangularMatchingProduct, twoSidedMatchingProduct, add_comm]⟩

private theorem exists_matching_of_embeddings {n : ℕ} (i j : Fin (n + 2))
    (l r : Fin n ↪ Fin (n + 2)) (hl : ∀ k, l k ≠ i) :
    ∃ τ : Equiv.Perm (Fin (n + 2)), τ j ≠ i ∧ ∀ k, τ (r k) = l k := by
  classical
  let e := r.toEquivRange.symm.trans l.toEquivRange
  let τ := e.extendSubtype
  have hτ (k : Fin n) : τ (r k) = l k := by
    rw [show τ = e.extendSubtype from rfl, e.extendSubtype_apply_of_mem _ ⟨k, rfl⟩]
    change (l (r.toEquivRange.symm (r.toEquivRange k))) = l k
    rw [Equiv.symm_apply_apply]
  by_cases hz : τ j = i
  · let L := Finset.univ.map l
    have hi : i ∉ L := by
      rintro h
      obtain ⟨k, _, hk⟩ := Finset.mem_map.mp h
      exact hl k hk
    have hcard : (insert i L).card = n + 1 := by
      rw [Finset.card_insert_of_not_mem hi]
      simp [L]
    obtain ⟨k, hk⟩ : ∃ k, k ∉ insert i L := by
      by_contra! h
      rw [Finset.eq_univ_of_forall h, Finset.card_univ, Fintype.card_fin] at hcard
      omega
    have hki : k ≠ i := fun hk' => hk (by simp [hk'])
    refine ⟨τ.trans (Equiv.swap i k), ?_, fun t => ?_⟩
    · simpa only [Equiv.trans_apply, hz, Equiv.swap_apply_left] using hki
    · have htk : l t ≠ k := fun h => hk
        (Finset.mem_insert_of_mem (Finset.mem_map.mpr ⟨t, Finset.mem_univ _, h⟩))
      rw [Equiv.trans_apply, hτ, Equiv.swap_apply_of_ne_of_ne (hl t) htk]
  · exact ⟨τ, hz, hτ⟩

private theorem reciprocalOverlap_vertex {n : ℕ} (a b : Fin (n + 2) → ℂ)
    {i j : Fin (n + 2)} (ha : ∀ k, a k = 0 ↔ k = i) (hb : ∀ k, b k = 0 ↔ k = j)
    (hcard : (spectralSupport a).card + (spectralSupport b).card = Fintype.card (Fin (n + 2)) + n)
    (l : Fin n ↪ {i // a i ≠ 0}) (r : Fin n ↪ {j // b j ≠ 0}) :
    twoSidedMatchingProduct (fun k : {i // a i ≠ 0} => (a k)⁻¹)
      (fun k : {j // b j ≠ 0} => (b k)⁻¹) (l, r) ∈ Set.range (reciprocalOverlapProduct a b) := by
  classical
  let l' := l.trans (Function.Embedding.subtype fun k => a k ≠ 0)
  let r' := r.trans (Function.Embedding.subtype fun k => b k ≠ 0)
  obtain ⟨τ, hτ, hm⟩ := exists_matching_of_embeddings i j l' r'
    (fun k h => (l k).property ((ha _).mpr h))
  have hcover : CoversSupports a b τ := by
    intro k
    by_cases hk : k = j
    · subst k
      exact Or.inl fun hz => hτ ((ha _).mp hz)
    · exact Or.inr fun hz => hk ((hb _).mp hz)
  let S := spectralSupport (a ∘ τ) ∩ spectralSupport b
  have hS : S.card = n := by
    dsimp only [S]
    rw [cover_overlap_card a b τ hcover, hcard]
    omega
  have hmem (k : Fin n) : r' k ∈ S := by
    simp only [S, spectralSupport, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ,
      true_and, Function.comp_apply, hm]
    exact ⟨(l k).property, (r k).property⟩
  have heq : Finset.univ.map r' = S := by
    apply Finset.eq_of_subset_of_card_le
    · intro k hk
      obtain ⟨t, _, rfl⟩ := Finset.mem_map.mp hk
      exact hmem t
    · simp [hS]
  let g (k : Fin (n + 2)) : ℂ :=
    if a (τ k) ≠ 0 ∧ b k ≠ 0 then (a (τ k))⁻¹ + (b k)⁻¹ else 1
  have hprod : (∏ k ∈ S, g k) = ∏ k, g k := by
    apply Finset.prod_subset (Finset.subset_univ _)
    intro k _ hk
    exact if_neg (fun hz => hk (by simpa [S, spectralSupport] using hz))
  refine ⟨τ, ?_⟩
  rw [reciprocalOverlapProduct, if_pos hcover]
  change (∏ k, g k) = _
  rw [← hprod, ← heq, Finset.prod_map]
  unfold twoSidedMatchingProduct
  apply Finset.prod_congr rfl
  intro k _
  change (if a (τ (r' k)) ≠ 0 ∧ b (r' k) ≠ 0 then (a (τ (r' k)))⁻¹ + (b (r' k))⁻¹ else 1) = _
  rw [hm]
  change (if a (l k) ≠ 0 ∧ b (r k) ≠ 0 then (a (l k))⁻¹ + (b (r k))⁻¹ else 1) = _
  simp [(l k).property, (r k).property]

/-- The reciprocal diagonal weights restricted to the common space are normal
in any pair of aligned isometric frames. -/
def NormalSupportOverlap {n : ℕ} (a b : Fin (n + 2) → ℂ)
    (U : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) : Prop :=
  let X := (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ).submatrix id (Subtype.val : {i // a i ≠ 0} → _)
  let Y := U.submatrix id (Subtype.val : {j // b j ≠ 0} → _)
  ∀ (E : Matrix {i // a i ≠ 0} (Fin n) ℂ) (F : Matrix {j // b j ≠ 0} (Fin n) ℂ),
    Eᴴ * E = 1 → Fᴴ * F = 1 → X * E = Y * F →
    IsStarNormal (Eᴴ * diagonal (fun i : {i // a i ≠ 0} => (a i)⁻¹) * E) ∧
    IsStarNormal (Fᴴ * diagonal (fun j : {j // b j ≠ 0} => (b j)⁻¹) * F)

/-- Unique marked zeros and normal reciprocal compressions reduce the original
order by two. -/
theorem holds_of_unique_zero_pair_of_normal_overlap {n : ℕ} (hSmall : Conjecture (Fin n))
    (a b : Fin (n + 2) → ℂ) (U : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) (hU : IsUnitary U)
    {i j : Fin (n + 2)} (ha : ∀ k, a k = 0 ↔ k = i) (hb : ∀ k, b k = 0 ↔ k = j)
    (hNormal : NormalSupportOverlap a b U) : Holds a b U := by
  classical
  let ρ := {i // a i ≠ 0}
  let σ := {j // b j ≠ 0}
  let e : Fin (n + 1) ≃ ρ := (finSuccAboveEquiv i).trans
    (Equiv.subtypeEquivRight (fun k => (not_congr (ha k)).symm))
  let f : Fin (n + 1) ≃ σ := (finSuccAboveEquiv j).trans
    (Equiv.subtypeEquivRight (fun k => (not_congr (hb k)).symm))
  have hcard : (spectralSupport a).card + (spectralSupport b).card = Fintype.card (Fin (n + 2)) + n := by
    have hρ : Fintype.card ρ = (spectralSupport a).card := Fintype.card_of_subtype _ (by simp [spectralSupport])
    have hσ : Fintype.card σ = (spectralSupport b).card := Fintype.card_of_subtype _ (by simp [spectralSupport])
    have he := Fintype.card_congr e
    have hf := Fintype.card_congr f
    rw [Fintype.card_fin, hρ] at he
    rw [Fintype.card_fin, hσ] at hf
    rw [← he, ← hf, Fintype.card_fin]
    omega
  let X := (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ).submatrix id (Subtype.val : ρ → _)
  let Y := U.submatrix id (Subtype.val : σ → _)
  let x : ρ → ℂ := fun k => (a k)⁻¹
  let y : σ → ℂ := fun k => (b k)⁻¹
  have hzero : a i + b j = 0 := by simp [(ha i).mpr rfl, (hb j).mpr rfl]
  by_cases hG : (X * Xᴴ + Y * Yᴴ).det = 0
  · have hd := det_support_sum_eq_zero_of_gram X Y (fun k => a k) (fun k => b k) hG
    dsimp only [X, Y] at hd
    rw [weighted_support_columns 1 a a (fun _ h => h),
      weighted_support_columns U b b (fun _ h => h), Matrix.one_mul,
      Matrix.conjTranspose_one, Matrix.mul_one] at hd
    exact holds_of_singular_of_opposite_entries a b U hd hzero
  · obtain ⟨E, F, q, hE, hF, hcommon, hq₀, hq₁, hequiv⟩ :=
      exists_supportOverlap_hull_reduction a b U hU n hcard hG
    obtain ⟨hA, hB⟩ := hNormal E F hE hF hcommon
    let E' := E.submatrix e id
    let F' := F.submatrix f id
    have hE' : E'ᴴ * E' = 1 := by
      dsimp only [E']
      rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv _ _ id e id]
      exact hE
    have hF' : F'ᴴ * F' = 1 := by
      dsimp only [F']
      rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv _ _ id f id]
      exact hF
    have hA' : E'ᴴ * diagonal (x ∘ e) * E' = Eᴴ * diagonal x * E := by
      dsimp only [E']
      rw [Matrix.conjTranspose_submatrix, ← Matrix.submatrix_diagonal_equiv,
        Matrix.submatrix_mul_equiv _ _ id e e, Matrix.submatrix_mul_equiv _ _ id e id]; rfl
    have hB' : F'ᴴ * diagonal (y ∘ f) * F' = Fᴴ * diagonal y * F := by
      dsimp only [F']
      rw [Matrix.conjTranspose_submatrix, ← Matrix.submatrix_diagonal_equiv,
        Matrix.submatrix_mul_equiv _ _ id f f, Matrix.submatrix_mul_equiv _ _ id f id]; rfl
    have hv := det_two_normal_compressions_mem_hull hSmall (x ∘ e) (y ∘ f) E' F' hE' hF'
      (hA'.symm ▸ hA) (hB'.symm ▸ hB)
    rw [hA', hB'] at hv
    have hmem : (Eᴴ * diagonal x * E + Fᴴ * diagonal y * F).det ∈
        convexHull ℝ (Set.range (reciprocalOverlapProduct a b)) := by
      apply convexHull_mono _ hv
      rintro _ ⟨m, rfl⟩
      exact reciprocalOverlap_vertex a b ha hb hcard
        (m.1.trans e.toEmbedding) (m.2.trans f.toEmbedding)
    have hzero' : (0 : ℂ) ∈ Set.range (reciprocalOverlapProduct a b) := by
      let τ := Equiv.swap j i
      refine ⟨τ, if_neg ?_⟩
      intro hcov
      simpa [τ, (ha i).mpr rfl, (hb j).mpr rfl] using hcov j
    apply hequiv.mpr
    simpa using (convex_convexHull ℝ (Set.range (reciprocalOverlapProduct a b)))
      (subset_convexHull ℝ _ hzero') hmem (sub_nonneg.mpr hq₁) hq₀ (sub_add_cancel 1 q)

/-- In order five, a simple marked opposite pair and two normal reciprocal
compressions give the determinant inclusion by the order-three theorem. -/
theorem holds_five_of_unique_opposite_pair_of_normal_overlap (a b : Fin 5 → ℂ)
    (U : Matrix (Fin 5) (Fin 5) ℂ) (hU : IsUnitary U)
    {i j : Fin 5} (hij : a i + b j = 0)
    (ha : ∀ k, a k = a i ↔ k = i) (hb : ∀ k, b k = b j ↔ k = j)
    (hNormal : NormalSupportOverlap (n := 3) (fun k => a k + b j) (fun k => b k - b j) U) :
    Holds a b U := by
  apply (holds_shift_iff a b hU (b j)).mp
  apply holds_of_unique_zero_pair_of_normal_overlap (conjecture_le_three (by norm_num)) _ _ U hU
    (i := i) (j := j) _ _ hNormal
  · intro k
    change a k + b j = 0 ↔ k = i
    rw [← hij, add_right_cancel_iff, ha]
  · intro k
    exact sub_eq_zero.trans (hb k)

end

end MOC
