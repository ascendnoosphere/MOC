import MOC.LocalCircleSchurSpectrum
import MOC.LocalCircleSchurLift
import MOC.ReciprocalCircleChart

open BigOperators Matrix Filter
open scoped Topology

namespace MOC

noncomputable section

private theorem scalarSchurComplement_blockDiag {n : ℕ} {κ : Type*}
    [Fintype κ] [DecidableEq κ]
    (C : Matrix (Unit ⊕ Fin n) (Unit ⊕ Fin n) ℂ) (F : Matrix κ κ ℂ) (r : ℂ) :
    let e := (Equiv.sumAssoc Unit (Fin n) κ).symm
    let A := (fromBlocks C 0 0 F).submatrix e e
    scalarSchurComplement A r = fromBlocks (scalarSchurComplement C r) 0 0 F := by
  intro e A
  ext (i | i) (j | j) : 1 <;> simp [scalarSchurComplement, A, e, Matrix.toBlocks₁₂,
    Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.submatrix_apply, Matrix.mul_apply]

/-- For a regular local pivot, a single compressed determinant inclusion
suffices to lift the inclusion with the unchanged complementary block. -/
theorem exists_localCircleSchur_pivot {n : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    (h : Fin (n + 1) → ℂ) (W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hW : IsUnitary W) (r c d : ℂ) (lam : Fin (n + 1) → ℝ) (hmono : Monotone lam)
    (hd : d ≠ 0) (hh : ∀ i, h i + r ≠ 0)
    (hhl : ∀ i, (h i + r)⁻¹ = c + d * (lam i : ℂ))
    (ht : (W * diagonal h * Wᴴ) 0 0 + r ≠ 0)
    (F : Matrix κ κ ℂ) (B : Matrix (Fin n ⊕ κ) (Fin n ⊕ κ) ℂ)
    (g : κ → ℂ) (b : Fin n ⊕ κ → ℂ) :
    let C := (W * diagonal h * Wᴴ).submatrix (scalarSchurIndex n) (scalarSchurIndex n)
    let e := (Equiv.sumAssoc Unit (Fin n) κ).symm
    let A := (fromBlocks C 0 0 F).submatrix e e
    let bP := Sum.elim (Fin.cons r (b ∘ Sum.inl)) (b ∘ Sum.inr)
    ∃ (a : Fin n → ℂ) (δ : Fin n → ℝ) (V : Matrix (Fin n) (Fin n) ℂ),
      IsUnitary V ∧ (∀ i, lam i.castSucc ≤ δ i ∧ δ i ≤ lam i.succ) ∧
      (∀ i, a i + r ≠ 0) ∧ (∀ i, (a i + r)⁻¹ = c + d * (δ i : ℂ)) ∧
      scalarSchurComplement C r = V * diagonal a * Vᴴ ∧
      ((fromBlocks (scalarSchurComplement C r) 0 0 F + B).det ∈
          convexHull ℝ (Set.range (matchingProduct (Sum.elim a g) b)) →
        (A + fromBlocks (scalarBlock r) 0 0 B).det ∈
          convexHull ℝ (Set.range (matchingProduct (Sum.elim h g) bP))) := by
  intro C e A bP
  obtain ⟨a, δ, V, hV, hδ, har, hal, hspec, hprod⟩ :=
    exists_scalarSchurComplement_interlacing h W hW r c d lam hmono hh hhl ht
  refine ⟨a, δ, V, hV, hδ, har, hal, hspec, ?_⟩
  intro hchild
  let t := C (Sum.inl ()) (Sum.inl ()) + r
  have hAt : A (Sum.inl ()) (Sum.inl ()) + r = t := rfl
  rw [det_scalarSchurComplement A r B (hAt ▸ ht), hAt,
    scalarSchurComplement_blockDiag C F r]
  exact schurMatchingHull_subset h a g b r t c d lam δ
    (fun i => (hδ i).1) (fun i => (hδ i).2) hd hh har hhl hal hprod hchild

/-- A regular scalar pivot on a generalized circle preserves that circle
and lifts the determinant inclusion from the specific child pair. -/
theorem exists_localCircleSchur_pivot_of_generalizedCircle {n : ℕ} {κ ν : Type*}
    [Fintype κ] [DecidableEq κ]
    (h : Fin (n + 1) → ℂ) (W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hW : IsUnitary W) (r : ℂ) (ℓ : ν → ℂ)
    (hcircle : SpectrumOnGeneralizedCircle (Sum.elim h (Sum.elim ℓ (fun _ : Unit => -r))))
    (hh : ∀ i, h i + r ≠ 0) (ht : (W * diagonal h * Wᴴ) 0 0 + r ≠ 0)
    (F : Matrix κ κ ℂ) (B : Matrix (Fin n ⊕ κ) (Fin n ⊕ κ) ℂ)
    (g : κ → ℂ) (b : Fin n ⊕ κ → ℂ) :
    let C := (W * diagonal h * Wᴴ).submatrix (scalarSchurIndex n) (scalarSchurIndex n)
    let e := (Equiv.sumAssoc Unit (Fin n) κ).symm
    let A := (fromBlocks C 0 0 F).submatrix e e
    let bP := Sum.elim (Fin.cons r (b ∘ Sum.inl)) (b ∘ Sum.inr)
    ∃ (a : Fin n → ℂ) (V : Matrix (Fin n) (Fin n) ℂ), IsUnitary V ∧
      SpectrumOnGeneralizedCircle (Sum.elim a ℓ) ∧
      scalarSchurComplement C r = V * diagonal a * Vᴴ ∧
      ((fromBlocks (scalarSchurComplement C r) 0 0 F + B).det ∈
          convexHull ℝ (Set.range (matchingProduct (Sum.elim a g) b)) →
        (A + fromBlocks (scalarBlock r) 0 0 B).det ∈
          convexHull ℝ (Set.range (matchingProduct (Sum.elim h g) bP))) := by
  classical
  intro C e A bP
  obtain ⟨c, d, hd, hparam, hpres⟩ := exists_reciprocal_chart_preserving_generalizedCircle h ℓ r hcircle hh
  choose k hk using hparam
  let s := Tuple.sort k
  let W' := W.submatrix (Equiv.refl _) s
  have hW' : IsUnitary W' := unitary_reindex (Equiv.refl _) s hW
  have hmat : W' * diagonal (h ∘ s) * W'ᴴ = W * diagonal h * Wᴴ := by
    dsimp only [W']
    rw [Matrix.conjTranspose_submatrix, ← Matrix.submatrix_diagonal_equiv h s,
      Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
    rfl
  have ht' : (W' * diagonal (h ∘ s) * W'ᴴ) 0 0 + r ≠ 0 := by rwa [hmat]
  obtain ⟨a, δ, V, hV, _, ha, ha', hspec, hlift⟩ :=
    exists_localCircleSchur_pivot (h ∘ s) W' hW' r c d (k ∘ s) (Tuple.monotone_sort k)
      hd (fun i => hh (s i)) (fun i => hk (s i)) ht' F B g b
  have hC : (W' * diagonal (h ∘ s) * W'ᴴ).submatrix (scalarSchurIndex n) (scalarSchurIndex n) = C := by
    rw [hmat]
  rw [hC] at hspec hlift
  refine ⟨a, V, hV, hpres a ha (fun i => ⟨δ i, ha' i⟩), hspec, ?_⟩
  intro hchild
  have hparent := hlift hchild
  have hrel : (Sum.elim h g) ∘ (s.sumCongr (Equiv.refl κ)) = Sum.elim (h ∘ s) g := by
    funext i
    cases i <;> rfl
  change (A + fromBlocks (scalarBlock r) 0 0 B).det ∈
    convexHull ℝ (Set.range (matchingProduct (Sum.elim (h ∘ s) g) bP)) at hparent
  have hrange := matchingRange_relabel (Sum.elim h g) bP (s.sumCongr (Equiv.refl κ)) (Equiv.refl _)
  rw [hrel] at hrange
  exact hrange ▸ hparent

/-- The local circle pivot reduces a parent to child pairs in the same
circle class. Continuity includes singular pivots. -/
theorem det_mem_matchingHull_of_localCircleSchur {n : ℕ} {κ ν : Type*}
    [Fintype κ] [DecidableEq κ]
    (h : Fin (n + 1) → ℂ) (W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hW : IsUnitary W) (r : ℂ) (ℓ : ν → ℂ)
    (hcircle : SpectrumOnGeneralizedCircle (Sum.elim h (Sum.elim ℓ (fun _ : Unit => -r))))
    (F : Matrix κ κ ℂ) (B : Matrix (Fin n ⊕ κ) (Fin n ⊕ κ) ℂ)
    (g : κ → ℂ) (b : Fin n ⊕ κ → ℂ)
    (hchild : ∀ (a : Fin n → ℂ) (V : Matrix (Fin n) (Fin n) ℂ), IsUnitary V →
      SpectrumOnGeneralizedCircle (Sum.elim a ℓ) →
      (fromBlocks (V * diagonal a * Vᴴ) 0 0 F + B).det ∈
        convexHull ℝ (Set.range (matchingProduct (Sum.elim a g) b))) :
    let C := (W * diagonal h * Wᴴ).submatrix (scalarSchurIndex n) (scalarSchurIndex n)
    let e := (Equiv.sumAssoc Unit (Fin n) κ).symm
    let A := (fromBlocks C 0 0 F).submatrix e e
    (A + fromBlocks (scalarBlock r) 0 0 B).det ∈ convexHull ℝ (Set.range
      (matchingProduct (Sum.elim h g) (Sum.elim (Fin.cons r (b ∘ Sum.inl)) (b ∘ Sum.inr)))) := by
  classical
  intro C e A
  let D (s : ℂ) := (A + fromBlocks (scalarBlock s) 0 0 B).det
  let bP (s : ℂ) : Fin (n + 1) ⊕ κ → ℂ :=
    Sum.elim (Fin.cons s (b ∘ Sum.inl)) (b ∘ Sum.inr)
  let M (s : ℂ) := matchingProduct (Sum.elim h g) (bP s)
  change D r ∈ convexHull ℝ (Set.range (M r))
  rcases exists_generalizedCircle_pole_path_or_constant h ℓ r hcircle with hconst | ⟨P, hP, hinj, hP0, hpath⟩
  · have hspec : diagonal h = (-r) • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := by
      ext i j : 1
      simp [Matrix.diagonal_apply, Matrix.one_apply, hconst]
    have hC : C = (-r) • (1 : Matrix (Unit ⊕ Fin n) (Unit ⊕ Fin n) ℂ) := by
      dsimp only [C]
      rw [hspec, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hW.1]
      change (-r) • ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ).submatrix
        (scalarSchurIndex n) (scalarSchurIndex n)) = _
      rw [Matrix.submatrix_one_equiv]
    have hzero : D r = 0 := by
      apply Matrix.det_eq_zero_of_row_eq_zero (Sum.inl ())
      rintro (i | i | j)
      · cases i
        simp [A, e, Matrix.submatrix_apply, hC, scalarBlock]
      · simp [A, e, Matrix.submatrix_apply, hC]
      · simp [A, e, Matrix.submatrix_apply]
    rw [hzero]
    apply subset_convexHull ℝ _
    refine ⟨Equiv.refl _, ?_⟩
    apply Finset.prod_eq_zero (Finset.mem_univ (Sum.inl (0 : Fin (n + 1))))
    simp [bP, hconst]
  · have hnear (z : ℂ) : ∀ᶠ t in 𝓝[≠] (0 : ℝ), P t ≠ z := by
      by_cases hz : P 0 = z
      · filter_upwards [self_mem_nhdsWithin] with t ht
        exact fun he => ht (hinj (he.trans hz.symm))
      · exact (hP.continuousAt.eventually_ne hz).filter_mono nhdsWithin_le_nhds
    have hrs : ∀ᶠ t in 𝓝[≠] (0 : ℝ), ∀ i, h i + P t ≠ 0 := by
      apply Filter.eventually_all.mpr
      intro i
      exact (hnear (-h i)).mono fun _ hz he => hz (eq_neg_of_add_eq_zero_right he)
    have hrp : ∀ᶠ t in 𝓝[≠] (0 : ℝ), (W * diagonal h * Wᴴ) 0 0 + P t ≠ 0 :=
      (hnear (-(W * diagonal h * Wᴴ) 0 0)).mono fun _ hz he =>
        hz (eq_neg_of_add_eq_zero_right he)
    by_contra hf
    obtain ⟨L, q, hq, hD⟩ := geometric_hahn_banach_closed_point (convex_convexHull ℝ _)
      (Set.finite_range (M r)).isClosed_convexHull hf
    have hDcont : Continuous (fun t : ℝ => L (D (P t))) := by
      apply L.continuous.comp
      unfold D
      apply Continuous.matrix_det
      apply continuous_const.add
      apply continuous_matrix
      intro i j
      cases i <;> cases j <;> first | exact hP | exact continuous_const
    have hMcont (σ : Equiv.Perm (Fin (n + 1) ⊕ κ)) :
        Continuous (fun t : ℝ => L (M (P t) σ)) := by
      apply L.continuous.comp
      unfold M matchingProduct
      apply continuous_finset_prod
      intro i _
      apply continuous_const.add
      rcases i with i | i
      · cases i using Fin.cases
        · exact hP
        · exact continuous_const
      · exact continuous_const
    have hseparate : ∀ᶠ t in 𝓝[≠] (0 : ℝ), ∀ σ, L (M (P t) σ) < L (D (P t)) := by
      apply Filter.eventually_all.mpr
      intro σ
      have hlt : L (M (P 0) σ) < L (D (P 0)) := by
        rw [hP0]
        exact (hq _ (subset_convexHull ℝ _ ⟨σ, rfl⟩)).trans hD
      exact ((hMcont σ).continuousAt.eventually_lt hDcont.continuousAt hlt).filter_mono nhdsWithin_le_nhds
    obtain ⟨t, hsep, hh, ht⟩ := (hseparate.and (hrs.and hrp)).exists
    obtain ⟨a, V, hV, ha, hspec, hlift⟩ :=
      exists_localCircleSchur_pivot_of_generalizedCircle h W hW (P t) ℓ (hpath t)
        hh ht F B g b
    have hparent := hlift (by rw [hspec]; exact hchild a V hV ha)
    have hsep' : D (P t) ∈ {z | L z < L (D (P t))} := by
      apply convexHull_min _ (convex_halfSpace_lt L.toLinearMap.isLinear _) hparent
      rintro _ ⟨σ, rfl⟩
      exact hsep σ
    exact (lt_irrefl (L (D (P t)))) hsep'

end

end MOC
