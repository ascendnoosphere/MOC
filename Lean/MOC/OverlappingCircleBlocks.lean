import MOC.LocalCircleSchurPivot
import MOC.TwoCircleCover

open BigOperators Matrix

namespace MOC

noncomputable section

private theorem holds_of_two_circle_cover_on {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℂ) (s : Set ι)
    (ha : SpectrumOnGeneralizedCircle (Sum.elim a (fun i : s => -b i.val)))
    (hb : SpectrumOnGeneralizedCircle (fun i : {i // i ∉ s} => -b i.val))
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) : Holds a b U := by
  let e := (Fintype.equivFin ι).symm
  let t := e ⁻¹' s
  apply (holds_reindex_iff e e a b U).mp
  apply holds_of_two_circle_cover (a ∘ e) (b ∘ e) t _ _ _ (unitary_reindex e e hU)
  · have h := ha.comp (Sum.elim (fun i => Sum.inl (e i)) (fun i : t => Sum.inr ⟨e i.val, i.property⟩))
    convert h using 1
    funext i
    cases i <;> rfl
  · exact hb.comp (fun i : {i // i ∉ t} => ⟨e i.val, i.property⟩)

private theorem det_mem_hull_of_circle_blocks_no_left_private {n : ℕ} {κ : Type*}
    [Fintype κ] [DecidableEq κ]
    (a : Fin n → ℂ) (g : κ → ℂ) (b : Fin n ⊕ κ → ℂ)
    (V : Matrix (Fin n) (Fin n) ℂ) (U : Matrix (Fin n ⊕ κ) (Fin n ⊕ κ) ℂ)
    (hV : IsUnitary V) (hU : IsUnitary U)
    (ha : SpectrumOnGeneralizedCircle a)
    (hb : SpectrumOnGeneralizedCircle (Sum.elim (fun i => -b i) g)) :
    (fromBlocks (V * diagonal a * Vᴴ) 0 0 (diagonal g) + U * diagonal b * Uᴴ).det ∈
      convexHull ℝ (Set.range (matchingProduct (Sum.elim a g) b)) := by
  let s : Set (Fin n ⊕ κ) := Set.range Sum.inr
  have hfirst : SpectrumOnGeneralizedCircle (Sum.elim b (fun i : s => -Sum.elim a g i.val)) := by
    obtain ⟨q, u, v, c, hn, hs⟩ := spectrumOnGeneralizedCircle_neg hb
    refine ⟨q, u, v, c, hn, ?_⟩
    rintro (i | ⟨j, hj⟩)
    · simpa only [Sum.elim_inl, neg_neg] using hs (Sum.inl i)
    · obtain ⟨k, rfl⟩ := hj
      exact hs (Sum.inr k)
  have hrest : SpectrumOnGeneralizedCircle (fun i : {i // i ∉ s} => -Sum.elim a g i.val) := by
    obtain ⟨q, u, v, c, hn, hs⟩ := spectrumOnGeneralizedCircle_neg ha
    refine ⟨q, u, v, c, hn, ?_⟩
    rintro ⟨i | k, hk⟩
    · exact hs i
    · exact (hk ⟨k, rfl⟩).elim
  let T := fromBlocks V 0 0 (1 : Matrix κ κ ℂ)
  have hT : IsUnitary T := by
    constructor <;>
      simp [T, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
        Matrix.fromBlocks_one, hV.1, hV.2]
  have hA : fromBlocks (V * diagonal a * Vᴴ) 0 0 (diagonal g) =
      T * diagonal (Sum.elim a g) * Tᴴ := by
    rw [← Matrix.fromBlocks_diagonal]
    simp [T, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, -Matrix.fromBlocks_diagonal]
  have hrev := holds_of_two_circle_cover_on b (Sum.elim a g) s hfirst hrest (Uᴴ * T)
    (relative_unitary U T hU hT)
  have ht : (Tᴴ * U)ᴴ = Uᴴ * T := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rw [← ht] at hrev
  have h := (holds_swap_iff (Sum.elim a g) b (relative_unitary T U hT hU)).mp hrev
  rwa [hA, determinantValue_relative _ _ T U hT]

/-- The first `p` coordinates in the active block of the first matrix are
its private coordinates. -/
def isLeftPrivateCoordinate {n : ℕ} {κ : Type*} (p : ℕ) : Fin n ⊕ κ → Prop :=
  Sum.elim (fun i => i.val < p) (fun _ => False)

private theorem circle_of_no_left_private {n : ℕ} {κ : Type*} (p : ℕ)
    (b : Fin n ⊕ κ → ℂ) (g : κ → ℂ)
    (hnone : ∀ i : Fin n ⊕ κ, ¬ isLeftPrivateCoordinate p i)
    (hΔ : SpectrumOnGeneralizedCircle
      (Sum.elim (fun j : {i // ¬ isLeftPrivateCoordinate p i} => -b j.val) g)) :
    SpectrumOnGeneralizedCircle (Sum.elim (fun i => -b i) g) := by
  have h := hΔ.comp (Sum.elim (fun i => Sum.inl ⟨i, hnone i⟩) (Sum.inr : κ → _))
  convert h using 1
  funext i
  cases i <;> rfl

/-- Two normal active blocks with a common set of coordinates satisfy the
determinant inclusion under the indicated two generalized circle conditions. -/
theorem det_mem_matchingHull_of_overlapping_circle_blocks {n : ℕ} {κ : Type*}
    [Fintype κ] [DecidableEq κ] (p : ℕ)
    (a : Fin n → ℂ) (g : κ → ℂ) (b : Fin n ⊕ κ → ℂ)
    (V : Matrix (Fin n) (Fin n) ℂ) (U : Matrix (Fin n ⊕ κ) (Fin n ⊕ κ) ℂ)
    (hV : IsUnitary V) (hU : IsUnitary U)
    (hfix : ∀ j, isLeftPrivateCoordinate p j → ∀ i,
      U i j = (1 : Matrix (Fin n ⊕ κ) (Fin n ⊕ κ) ℂ) i j ∧
      U j i = (1 : Matrix (Fin n ⊕ κ) (Fin n ⊕ κ) ℂ) j i)
    (hΓ : SpectrumOnGeneralizedCircle
      (Sum.elim a (fun j : {i // isLeftPrivateCoordinate p i} => -b j.val)))
    (hΔ : SpectrumOnGeneralizedCircle
      (Sum.elim (fun j : {i // ¬ isLeftPrivateCoordinate p i} => -b j.val) g)) :
    (fromBlocks (V * diagonal a * Vᴴ) 0 0 (diagonal g) + U * diagonal b * Uᴴ).det ∈
      convexHull ℝ (Set.range (matchingProduct (Sum.elim a g) b)) := by
  classical
  induction n generalizing p with
  | zero =>
    have hnone (i : Fin 0 ⊕ κ) : ¬ isLeftPrivateCoordinate p i := by
      rcases i with i | j
      · exact Fin.elim0 i
      · exact id
    exact det_mem_hull_of_circle_blocks_no_left_private a g b V U hV hU
      (hΓ.comp Sum.inl)
      (circle_of_no_left_private p b g hnone hΔ)
  | succ n ih =>
    cases p with
    | zero =>
      have hnone (i : Fin (n + 1) ⊕ κ) : ¬ isLeftPrivateCoordinate 0 i := by
        cases i with
        | inl i => exact Nat.not_lt_zero _
        | inr j => exact id
      exact det_mem_hull_of_circle_blocks_no_left_private a g b V U hV hU
        (hΓ.comp Sum.inl)
        (circle_of_no_left_private 0 b g hnone hΔ)
    | succ p =>
      let f := (Equiv.sumAssoc Unit (Fin n) κ).symm
      let e : Unit ⊕ (Fin n ⊕ κ) ≃ Fin (n + 1) ⊕ κ :=
        f.trans ((scalarSchurIndex n).sumCongr (Equiv.refl κ))
      let e' : Fin n ⊕ κ → Fin (n + 1) ⊕ κ := e ∘ Sum.inr
      let j₀ : Fin (n + 1) ⊕ κ := Sum.inl 0
      let r : ℂ := b j₀
      let b' : Fin n ⊕ κ → ℂ := b ∘ e'
      let U' := U.submatrix e' e'
      have hfix₀ : isLeftPrivateCoordinate (p + 1) j₀ := Nat.zero_lt_succ _
      have he₀ : e (Sum.inl ()) = j₀ := rfl
      have he' : Function.Injective e' := e.injective.comp Sum.inr_injective
      have hn₀ (i : Fin n ⊕ κ) : e' i ≠ j₀ := by
        rw [← he₀]
        exact fun he => Sum.inr_ne_inl (e.injective he)
      have hpriv (i : Fin n ⊕ κ) :
          isLeftPrivateCoordinate (p + 1) (e' i) ↔ isLeftPrivateCoordinate p i := by
        cases i with
        | inl i =>
          change i.val + 1 < p + 1 ↔ i.val < p
          omega
        | inr j => rfl
      have hUre : U.submatrix e e = fromBlocks (1 : Matrix Unit Unit ℂ) 0 0 U' := by
        ext (i | i) (j | j) : 1
        · cases i
          cases j
          simpa [Matrix.submatrix_apply, he₀] using (hfix j₀ hfix₀ j₀).1
        · cases i
          simpa [Matrix.submatrix_apply, he₀, e', Matrix.one_apply_ne (Ne.symm (hn₀ j))]
            using (hfix j₀ hfix₀ (e' j)).2
        · cases j
          simpa [Matrix.submatrix_apply, he₀, e', Matrix.one_apply_ne (hn₀ i)]
            using (hfix j₀ hfix₀ (e' i)).1
        · rfl
      have hU' : IsUnitary U' := by
        have hu := unitary_reindex e e hU
        rw [hUre] at hu
        constructor
        · have hu' := congrArg Matrix.toBlocks₂₂ hu.1
          simpa [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
            using hu'
        · have hu' := congrArg Matrix.toBlocks₂₂ hu.2
          simpa [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
            using hu'
      have hfix' (j : Fin n ⊕ κ) (hj : isLeftPrivateCoordinate p j) (i : Fin n ⊕ κ) :
          U' i j = (1 : Matrix (Fin n ⊕ κ) (Fin n ⊕ κ) ℂ) i j ∧
          U' j i = (1 : Matrix (Fin n ⊕ κ) (Fin n ⊕ κ) ℂ) j i := by
        simpa only [U', Matrix.submatrix_apply, Matrix.one_apply, he'.eq_iff] using
          hfix (e' j) ((hpriv j).mpr hj) (e' i)
      have hΔ' : SpectrumOnGeneralizedCircle
          (Sum.elim (fun j : {i // ¬ isLeftPrivateCoordinate p i} => -b' j.val) g) := by
        have h := hΔ.comp (Sum.elim (fun j : {i // ¬ isLeftPrivateCoordinate p i} =>
          Sum.inl ⟨e' j.val, fun hj => j.property ((hpriv j.val).mp hj)⟩) (Sum.inr : κ → _))
        convert h using 1
        funext i
        cases i <;> rfl
      let ℓ (j : {i : Fin n ⊕ κ // isLeftPrivateCoordinate p i}) : ℂ := -b' j.val
      have hΓ' : SpectrumOnGeneralizedCircle (Sum.elim a (Sum.elim ℓ (fun _ : Unit => -r))) := by
        have h := hΓ.comp (Sum.elim Sum.inl (Sum.elim (fun j : {i // isLeftPrivateCoordinate p i} =>
          Sum.inr ⟨e' j.val, (hpriv j.val).mpr j.property⟩) (fun _ : Unit => Sum.inr ⟨j₀, hfix₀⟩)))
        convert h using 1
        funext i
        rcases i with i | i | i <;> rfl
      have hB : (U * diagonal b * Uᴴ).submatrix e e =
          fromBlocks (scalarBlock r) 0 0 (U' * diagonal b' * U'ᴴ) := by
        have hb : b ∘ e = Sum.elim (fun _ : Unit => r) b' := by
          funext i
          rcases i with i | i
          · cases i
            rfl
          · rfl
        have hr : diagonal (fun _ : Unit => r) = scalarBlock r := by
          ext i j : 1
          cases i
          cases j
          simp [scalarBlock]
        rw [← Matrix.submatrix_mul_equiv _ _ e e e, ← Matrix.submatrix_mul_equiv _ _ e e e,
          ← Matrix.conjTranspose_submatrix, Matrix.submatrix_diagonal_equiv, hb,
          ← Matrix.fromBlocks_diagonal, hr, hUre]
        simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
      let C :=
        (V * diagonal a * Vᴴ).submatrix (scalarSchurIndex n) (scalarSchurIndex n)
      have hA : (fromBlocks (V * diagonal a * Vᴴ) 0 0 (diagonal g)).submatrix e e =
          (fromBlocks C 0 0 (diagonal g)).submatrix f f := by
        ext (i | i | i) (j | j | j) : 1 <;> rfl
      have hspec : Sum.elim (Fin.cons r (b' ∘ Sum.inl)) (b' ∘ Sum.inr) = b := by
        funext i
        rcases i with i | j
        · cases i using Fin.cases <;> rfl
        · rfl
      have h := det_mem_matchingHull_of_localCircleSchur a V hV r ℓ hΓ'
        (diagonal g) (U' * diagonal b' * U'ᴴ) g b'
        (fun a' V' hV' hΓ'' => ih p a' b' V' U' hV' hU' hfix' hΓ'' hΔ')
      change ((fromBlocks C 0 0 (diagonal g)).submatrix f f +
        fromBlocks (scalarBlock r) 0 0 (U' * diagonal b' * U'ᴴ)).det ∈
          convexHull ℝ (Set.range (matchingProduct (Sum.elim a g)
            (Sum.elim (Fin.cons r (b' ∘ Sum.inl)) (b' ∘ Sum.inr)))) at h
      rw [hspec, ← hA, ← hB] at h
      change (Matrix.submatrix
        (fromBlocks (V * diagonal a * Vᴴ) 0 0 (diagonal g) + U * diagonal b * Uᴴ)
        e e).det ∈ _ at h
      rw [Matrix.det_submatrix_equiv_self] at h
      exact h

end

end MOC
