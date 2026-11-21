import MOC.TwoFrame
import MOC.Weights
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Topology.Instances.Matrix

/-! Rank-two compression proves MOC when one spectrum is constant off two labels. -/

open BigOperators Matrix Finset

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private def pairEmbedding (i j : ι) (h : i ≠ j) : Fin 2 ↪ ι where
  toFun := ![i, j]
  inj' := by
    intro k l hkl
    fin_cases k <;> fin_cases l
    · rfl
    · exact (h (by simpa using hkl)).elim
    · exact (h (by simpa using hkl.symm)).elim
    · rfl

private theorem extend_two_matching (e : Fin 2 ↪ ι) (m : TwoEdgeMatching (Fin 2) ι) :
    ∃ σ : Equiv.Perm ι, σ m.val.1.2 = e m.val.1.1 ∧ σ m.val.2.2 = e m.val.2.1 := by
  classical
  let f := pairEmbedding m.val.1.2 m.val.2.2 m.property.2
  let g := pairEmbedding (e m.val.1.1) (e m.val.2.1) (e.injective.ne m.property.1)
  let E := f.toEquivRange.symm.trans g.toEquivRange
  have h (k : Fin 2) : E.extendSubtype (f k) = g k := by
    rw [Equiv.extendSubtype_apply_of_mem _ _ (Set.mem_range_self k)]
    change (E (f.toEquivRange k) : ι) = g k
    simp [E]
  exact ⟨E.extendSubtype, h 0, h 1⟩

private theorem matchingProduct_two_reciprocals (a b : ι → ℂ) (e : Fin 2 ↪ ι)
    (m : TwoEdgeMatching (Fin 2) ι) (σ : Equiv.Perm ι)
    (hσ : σ m.val.1.2 = e m.val.1.1 ∧ σ m.val.2.2 = e m.val.2.1)
    (ha : ∀ i ∉ Set.range e, a i = 0) (hna : ∀ k, a (e k) ≠ 0)
    (hnb : ∀ j, b j ≠ 0) :
    matchingProduct a b σ =
      ((∏ k, a (e k)) * ∏ j, b j) *
        (((a (e m.val.1.1))⁻¹ + (b m.val.1.2)⁻¹) *
          ((a (e m.val.2.1))⁻¹ + (b m.val.2.2)⁻¹)) := by
  have hcols : m.val.2.2 ∈ (univ : Finset ι).erase m.val.1.2 :=
    mem_erase.mpr ⟨m.property.2.symm, mem_univ _⟩
  let R := ((univ : Finset ι).erase m.val.1.2).erase m.val.2.2
  have hsplit (f : ι → ℂ) :
      (∏ j, f j) = f m.val.1.2 * (f m.val.2.2 * ∏ j ∈ R, f j) := by
    rw [← Finset.mul_prod_erase univ f (mem_univ m.val.1.2),
      ← Finset.mul_prod_erase (univ.erase m.val.1.2) f hcols]
  have hrows : ({m.val.1.1, m.val.2.1} : Finset (Fin 2)) = univ :=
    Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by simp [m.property.1])
  have hrest : (∏ j ∈ R, (a (σ j) + b j)) = ∏ j ∈ R, b j := by
    apply Finset.prod_congr rfl
    intro j hj
    have hj₂ := (Finset.mem_erase.mp hj).1
    have hj₁ := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
    have hnot : σ j ∉ Set.range e := by
      rintro ⟨k, hk⟩
      have hmem : k ∈ ({m.val.1.1, m.val.2.1} : Finset (Fin 2)) := by rw [hrows]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h | h
      · rw [h] at hk
        exact hj₁ (σ.injective (hk.symm.trans hσ.1.symm))
      · rw [h] at hk
        exact hj₂ (σ.injective (hk.symm.trans hσ.2.symm))
    rw [ha _ hnot, zero_add]
  unfold matchingProduct
  rw [hsplit (fun j => a (σ j) + b j), hrest, hσ.1, hσ.2, hsplit b, ← hrows,
    Finset.prod_insert (by simp [m.property.1]), Finset.prod_singleton]
  field_simp [hna, hnb]
  ring

private theorem holds_of_two_supported (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) (e : Fin 2 ↪ ι) (ha : ∀ i ∉ Set.range e, a i = 0) :
    Holds a b U := by
  classical
  let P : Matrix ι (Fin 2) ℂ := (1 : Matrix ι ι ℂ).submatrix id e
  let F := Uᴴ * P
  have hP (i : ι) (k : Fin 2) : P i k = if e k = i then 1 else 0 := by
    simp [P, Matrix.one_apply, eq_comm]
  have hPt : Pᴴ = (1 : Matrix ι ι ℂ).submatrix e id := by
    ext k i : 1
    by_cases h : e k = i <;> simp [Matrix.conjTranspose_apply, Matrix.submatrix_apply,
      Matrix.one_apply, hP, h]
  have hPP : Pᴴ * P = 1 := by
    rw [hPt]
    change (1 : Matrix ι ι ℂ).submatrix e (Equiv.refl ι) * P = 1
    rw [Matrix.one_submatrix_mul]
    exact Matrix.submatrix_one_embedding (α := ℂ) e
  have hF : Fᴴ * F = 1 := by
    change (Uᴴ * P)ᴴ * (Uᴴ * P) = 1
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc
      (Pᴴ * U) * (Uᴴ * P) = Pᴴ * (U * Uᴴ) * P := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hU.1, Matrix.mul_one, hPP]
  obtain ⟨s, w, hw, hs, hval⟩ := exists_twoFrame_compression_weights
    (1 : Matrix (Fin 2) (Fin 2) ℂ) F (by simp) hF
  choose σ hσ using extend_two_matching e
  let A (t : ℂ) (i : ι) := if i ∈ Set.range e then a i + t else a i
  let B (t : ℂ) (j : ι) := b j + t
  let K : Set ℂ := Set.range (fun k : Fin 2 => -a (e k)) ∪ Set.range (fun j : ι => -b j)
  have hK : Dense Kᶜ :=
    ((Set.finite_range _).union (Set.finite_range _)).countable.dense_compl ℂ
  have hgen : Set.EqOn
      (fun t => ∑ m ∈ s, (w m : ℂ) * matchingProduct (A t) (B t) (σ m))
      (fun t => determinantValue (A t) (B t) U) Kᶜ := by
    intro t ht
    have haT (i : ι) (hi : i ∉ Set.range e) : A t i = 0 := by
      simpa only [A, if_neg hi] using ha i hi
    have hx (k : Fin 2) : A t (e k) ≠ 0 := by
      intro h
      have heq : t = -a (e k) := by
        have hh : a (e k) + t = 0 := by simpa [A, Set.mem_range_self k] using h
        linear_combination hh
      exact ht (Or.inl ⟨k, heq.symm⟩)
    have hy (j : ι) : B t j ≠ 0 := by
      intro h
      have heq : t = -b j := by change b j + t = 0 at h; linear_combination h
      exact ht (Or.inr ⟨j, heq.symm⟩)
    let x (k : Fin 2) := A t (e k)
    let y := B t
    let D := diagonal x
    let E := U * diagonal y * Uᴴ
    let C := U * diagonal (fun j => (y j)⁻¹) * Uᴴ
    let Dinv := diagonal (fun k => (x k)⁻¹)
    let Γ := (∏ k, x k) * ∏ j, y j
    have hD : P * D * Pᴴ = diagonal (A t) := by
      ext i j : 1
      rw [Matrix.mul_apply, Matrix.diagonal_apply]
      simp only [D, Matrix.mul_diagonal, Matrix.conjTranspose_apply, hP]
      by_cases hij : i = j
      · subst j
        by_cases hi : i ∈ Set.range e
        · obtain ⟨k, rfl⟩ := hi
          rw [Finset.sum_eq_single k]
          · simp [x]
          · intro l _ hl
            simp [e.injective.ne hl]
          · simp
        · have hn (k : Fin 2) : e k ≠ i := fun he => hi ⟨k, he⟩
          simp [hn, haT i hi]
      · rw [if_neg hij]
        apply Finset.sum_eq_zero
        intro k _
        by_cases hk : e k = i
        · have hj : e k ≠ j := fun h => hij (hk.symm.trans h)
          simp [hk, hj, hij]
        · simp [hk]
    have hEC : E * C = 1 := by
      calc
        _ = U * (diagonal y * (Uᴴ * U) * diagonal (fun j => (y j)⁻¹)) * Uᴴ := by
          simp only [E, C, Matrix.mul_assoc]
        _ = 1 := by
          rw [hU.2, Matrix.mul_one, Matrix.diagonal_mul_diagonal]
          simp [y, hy, mul_inv_cancel₀, hU.1]
    have hDD : D * Dinv = 1 := by
      simp [D, Dinv, x, Matrix.diagonal_mul_diagonal, hx, mul_inv_cancel₀]
    have hC : Pᴴ * C * P = Fᴴ * diagonal (fun j => (y j)⁻¹) * F := by
      simp only [C, F, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    have hbig : diagonal (A t) + E = E * (1 + (C * P) * (D * Pᴴ)) := by
      rw [Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc E (C * P),
        ← Matrix.mul_assoc E C, hEC, Matrix.one_mul, ← Matrix.mul_assoc P D, hD, add_comm]
    have hsmall : 1 + (D * Pᴴ) * (C * P) =
        D * (Dinv + Fᴴ * diagonal (fun j => (y j)⁻¹) * F) := by
      rw [Matrix.mul_add, hDD, ← hC]
      simp only [Matrix.mul_assoc]
    have hE_det : E.det = ∏ j, y j := by
      change (U * diagonal y * Uᴴ).det = _
      rw [det_unitary_conjugation U _ hU, Matrix.det_diagonal]
    have hD_det : D.det = ∏ k, x k := Matrix.det_diagonal
    have hdet : determinantValue (A t) (B t) U =
        Γ * (Dinv + Fᴴ * diagonal (fun j => (y j)⁻¹) * F).det := by
      change (diagonal (A t) + E).det = _
      rw [hbig, Matrix.det_mul E, Matrix.det_one_add_mul_comm (C * P) (D * Pᴴ),
        hsmall, Matrix.det_mul D, hE_det, hD_det]
      dsimp only [Γ]
      ring
    have hweights : (∑ m ∈ s, (w m : ℂ) *
        (((x m.val.1.1)⁻¹ + (y m.val.1.2)⁻¹) *
          ((x m.val.2.1)⁻¹ + (y m.val.2.2)⁻¹))) =
        (Dinv + Fᴴ * diagonal (fun j => (y j)⁻¹) * F).det := by
      simpa only [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one, Dinv] using
        hval (fun k => (x k)⁻¹) (fun j => (y j)⁻¹)
    change (∑ m ∈ s, (w m : ℂ) * matchingProduct (A t) (B t) (σ m)) = _
    rw [hdet, ← hweights, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    rw [matchingProduct_two_reciprocals _ _ e m _ (hσ m) haT hx hy]
    change (w m : ℂ) * (Γ * _) = Γ * ((w m : ℂ) * _)
    ring
  have hA : Continuous A := continuous_pi fun i => by
    by_cases hi : i ∈ Set.range e
    · simpa only [A, if_pos hi] using (continuous_const.add continuous_id :
        Continuous (fun t : ℂ => a i + t))
    · simpa only [A, if_neg hi] using (continuous_const : Continuous (fun _ : ℂ => a i))
  have hB : Continuous B := continuous_pi fun _ => continuous_const.add continuous_id
  have hcont₁ : Continuous (fun t => ∑ m ∈ s, (w m : ℂ) * matchingProduct (A t) (B t) (σ m)) := by
    apply continuous_finset_sum
    intro m _
    apply Continuous.const_mul
    unfold matchingProduct
    exact continuous_finset_prod _ fun j _ =>
      ((continuous_apply (σ m j)).comp hA).add ((continuous_apply j).comp hB)
  have hUconst : Continuous (fun _ : ℂ => U) := continuous_const
  have hUstar : Continuous (fun _ : ℂ => Uᴴ) := continuous_const
  have hcont₂ : Continuous (fun t => determinantValue (A t) (B t) U) :=
    (hA.matrix_diagonal.add
      ((hUconst.matrix_mul hB.matrix_diagonal).matrix_mul hUstar)).matrix_det
  have hzero := hgen.closure hcont₁ hcont₂ (hK 0)
  have hA₀ : A 0 = a := by funext i; by_cases hi : i ∈ Set.range e <;> simp [A, hi]
  have hB₀ : B 0 = b := by funext j; simp [B]
  change (∑ m ∈ s, (w m : ℂ) * matchingProduct (A 0) (B 0) (σ m)) =
    determinantValue (A 0) (B 0) U at hzero
  rw [hA₀, hB₀] at hzero
  let z (m : TwoEdgeMatching (Fin 2) ι) := matchingProduct a b (σ m)
  have hmem : s.centerMass w z ∈ convexHull ℝ (Set.range (matchingProduct a b)) :=
    s.centerMass_mem_convexHull hw (by rw [hs]; norm_num) (fun m _ => ⟨σ m, rfl⟩)
  rw [s.centerMass_eq_of_sum_1 z hs] at hmem
  simpa only [Holds, z, Complex.real_smul, hzero] using hmem

/-- MOC in any finite order when the first spectrum has a common value
outside at most two specified labels. -/
theorem holds_two_exceptions (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (i₀ i₁ : ι) (c : ℂ) (ha : ∀ i, i ≠ i₀ → i ≠ i₁ → a i = c) : Holds a b U := by
  by_cases hi : i₀ = i₁
  · subst i₁
    apply (holds_swap_iff a b hU).mp
    apply holds_one_exception b a Uᴴ ⟨by simpa using hU.2, by simpa using hU.1⟩ i₀ c
    exact fun i h => ha i h h
  · let e := pairEmbedding i₀ i₁ hi
    apply (holds_shift_iff a b hU (-c)).mp
    apply holds_of_two_supported _ _ U hU e
    intro i h
    have h₀ : i ≠ i₀ := fun he => h ⟨0, he.symm⟩
    have h₁ : i ≠ i₁ := fun he => h ⟨1, he.symm⟩
    simp [ha i h₀ h₁]

/-- The support-cardinality form also includes empty index types. -/
theorem holds_of_card_exceptions_le_two (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) (c : ℂ) (h : (univ.filter (fun i => a i ≠ c)).card ≤ 2) :
    Holds a b U := by
  by_cases hι : Nonempty ι
  · letI := hι
    let S := univ.filter (fun i => a i ≠ c)
    have hc : S.card ≤ 2 := h
    have hp : ∃ i j : ι, S ⊆ {i, j} := by
      by_cases htwo : S.card = 2
      · obtain ⟨i, j, _, heq⟩ := Finset.card_eq_two.mp htwo
        exact ⟨i, j, heq.le⟩
      · obtain ⟨i, hi⟩ := Finset.card_le_one_iff_subset_singleton.mp (show S.card ≤ 1 by omega)
        exact ⟨i, i, by simpa using hi⟩
    obtain ⟨i, j, hs⟩ := hp
    apply holds_two_exceptions a b U hU i j c
    intro k hki hkj
    by_contra hkc
    have hk : k ∈ S := by simp [S, hkc]
    simpa [hki, hkj] using hs hk
  · haveI : IsEmpty ι := not_nonempty_iff.mp hι
    exact conjecture_of_subsingleton a b U hU

/-- One repeated value in the first order-four spectrum leaves at most two exceptions. -/
theorem holds_four_of_repeated_left (a b : Fin 4 → ℂ) (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : IsUnitary U) (ha : ¬ Function.Injective a) : Holds a b U := by
  unfold Function.Injective at ha
  push_neg at ha
  obtain ⟨i, j, heq, hij⟩ := ha
  apply holds_of_card_exceptions_le_two a b U hU (a i)
  have hsub : univ.filter (fun k => a k ≠ a i) ⊆ ({i, j} : Finset (Fin 4))ᶜ := by
    intro k hk
    have hka := (Finset.mem_filter.mp hk).2
    rw [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton]
    rintro (rfl | rfl)
    · exact hka rfl
    · exact hka heq.symm
  simpa only [Finset.card_compl, Finset.card_pair hij, Fintype.card_fin] using
    Finset.card_le_card hsub

/-- The order-four conjecture holds when either spectrum has a repeated value. -/
theorem holds_four_of_repeated_spectrum (a b : Fin 4 → ℂ) (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : IsUnitary U) (h : ¬ Function.Injective a ∨ ¬ Function.Injective b) : Holds a b U := by
  rcases h with ha | hb
  · exact holds_four_of_repeated_left a b U hU ha
  · apply (holds_swap_iff a b hU).mp
    exact holds_four_of_repeated_left b a Uᴴ ⟨by simpa using hU.2, by simpa using hU.1⟩ hb

end

end MOC
