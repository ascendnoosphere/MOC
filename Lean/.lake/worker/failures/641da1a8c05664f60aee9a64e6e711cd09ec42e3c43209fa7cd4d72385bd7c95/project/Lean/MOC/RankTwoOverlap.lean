import MOC.RankSum
import MOC.TwoFrame
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Complementary-block compression of a sum supported on two frames. -/

open BigOperators Matrix
open scoped ComplexOrder InnerProductSpace

namespace MOC

noncomputable section

variable {ι κ ρ σ : Type*}
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype ρ] [DecidableEq ρ] [Fintype σ] [DecidableEq σ]

/-- Two frames for a common subspace give the reciprocal determinant on that
subspace. The change of column labels places the complementary blocks in a
single square matrix. -/
theorem det_support_frames (e : ι ⊕ κ ≃ ρ ⊕ σ)
    (X : Matrix ι ρ ℂ) (Y : Matrix ι σ ℂ)
    (E : Matrix ρ κ ℂ) (F : Matrix σ κ ℂ)
    (hE : Eᴴ * E = 1) (hF : Fᴴ * F = 1) (hcommon : X * E = Y * F)
    (hG : IsUnit (X * Xᴴ + Y * Yᴴ).det)
    (a : ρ → ℂ) (b : σ → ℂ) (ha : ∀ i, a i ≠ 0) (hb : ∀ j, b j ≠ 0) :
    (X * diagonal a * Xᴴ + Y * diagonal b * Yᴴ).det =
      ((∏ i, a i) * ∏ j, b j) * ((X * Xᴴ + Y * Yᴴ).det / (2 : ℂ) ^ Fintype.card κ) *
        (Eᴴ * diagonal (fun i => (a i)⁻¹) * E + Fᴴ * diagonal (fun j => (b j)⁻¹) * F).det := by
  let s : ℂ := ((1 / 2 : ℝ) : ℂ) + ((1 / 2 : ℝ) : ℂ) * Complex.I
  have hs₀ : star s * s = ((1 / 2 : ℝ) : ℂ) := by
    apply Complex.ext <;> norm_num [s, Complex.star_def, Complex.mul_re, Complex.mul_im]
  have hs : star s * s = (2 : ℂ)⁻¹ := by simpa [one_div, Complex.ofReal_inv] using hs₀
  have hs' : s * star s = (2 : ℂ)⁻¹ := (mul_comm _ _).trans hs
  let W₀ := fromBlocks X Y (star s • Eᴴ) ((-star s) • Fᴴ)
  let W := W₀.submatrix id e
  have hreindex (L : Matrix (ρ ⊕ σ) (ρ ⊕ σ) ℂ) :
      W * L.submatrix e e * Wᴴ = W₀ * L * W₀ᴴ := by
    dsimp only [W]
    rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_mul_equiv] <;> rfl
  have hupper : X * (s • E) + Y * ((-s) • F) = 0 := by
    simp only [Matrix.mul_smul, hcommon, neg_smul, Matrix.mul_neg, add_neg_cancel]
  have hlower : (star s • Eᴴ) * Xᴴ + ((-star s) • Fᴴ) * Yᴴ = 0 := by
    have h := congrArg Matrix.conjTranspose hupper
    simpa only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_smul,
      star_neg, Matrix.conjTranspose_zero] using h
  have hgram : W * Wᴴ = fromBlocks (X * Xᴴ + Y * Yᴴ) 0 0 (1 : Matrix κ κ ℂ) := by
    have h := hreindex (1 : Matrix (ρ ⊕ σ) (ρ ⊕ σ) ℂ)
    rw [Matrix.submatrix_one_equiv, Matrix.mul_one, Matrix.mul_one] at h
    rw [h]
    simp only [W₀, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_conjTranspose, star_neg, star_star, Matrix.fromBlocks_multiply,
      hupper, hlower]
    congr 1
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, neg_mul_neg, hs, hs', hE, hF,
      ← add_smul]
    norm_num
  have hblocks (c : ρ → ℂ) (d : σ → ℂ) :
      let L := (diagonal (Sum.elim c d)).submatrix e e
      (W * L * Wᴴ).toBlocks₁₁ = X * diagonal c * Xᴴ + Y * diagonal d * Yᴴ ∧
      (W * L * Wᴴ).toBlocks₂₂ =
        ((2 : ℂ)⁻¹) • (Eᴴ * diagonal c * E + Fᴴ * diagonal d * F) := by
    dsimp only
    rw [hreindex, ← Matrix.fromBlocks_diagonal]
    simp only [W₀, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_conjTranspose, star_neg, star_star, Matrix.fromBlocks_multiply,
      Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.toBlocks_fromBlocks₁₁,
      Matrix.toBlocks_fromBlocks₂₂, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      neg_mul_neg, hs, hs', ← smul_add, and_true, true_and]
  let c : ρ → ℂ := fun i => (a i)⁻¹
  let d : σ → ℂ := fun j => (b j)⁻¹
  let L := (diagonal (Sum.elim a b)).submatrix e e
  let Linv := (diagonal (Sum.elim c d)).submatrix e e
  have hL : L * Linv = 1 := by
    dsimp only [L, Linv]
    rw [Matrix.submatrix_mul_equiv, Matrix.diagonal_mul_diagonal, Matrix.submatrix_diagonal_equiv,
      ← Matrix.diagonal_one]
    apply congrArg Matrix.diagonal
    funext k
    cases he : e k <;> simp [he, c, d, ha, hb]
  have hdet : L.det = (∏ i, a i) * ∏ j, b j := by
    dsimp only [L]
    rw [Matrix.det_submatrix_equiv_self, Matrix.det_diagonal, Fintype.prod_sum_type] <;> rfl
  have h := det_compress_of_orthogonal_row_blocks W L Linv _ hgram hG hL
  rw [(hblocks a b).1, (hblocks c d).2, hdet, Matrix.det_smul] at h
  rw [h, inv_pow, div_eq_mul_inv]
  ring

/-- A spanning pair of isometries has a common frame of the dimension given
by the excess of its total number of columns over the ambient dimension. -/
theorem exists_overlap_frames (e : ι ⊕ κ ≃ ρ ⊕ σ)
    (X : Matrix ι ρ ℂ) (Y : Matrix ι σ ℂ) (hX : Xᴴ * X = 1) (hY : Yᴴ * Y = 1)
    (hG : IsUnit (X * Xᴴ + Y * Yᴴ).det) :
    ∃ (E : Matrix ρ κ ℂ) (F : Matrix σ κ ℂ), Eᴴ * E = 1 ∧ Fᴴ * F = 1 ∧ X * E = Y * F := by
  let T := fromCols X Y
  let G := X * Xᴴ + Y * Yᴴ
  have hTG : T * Tᴴ = G := by
    simp only [T, G, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
      Matrix.fromCols_mul_fromRows]
  have hInv : T * (Tᴴ * G⁻¹) = 1 := by
    rw [← Matrix.mul_assoc, hTG, Matrix.mul_nonsing_inv _ hG]
  let L := Matrix.toEuclideanLin T
  have hsurj : Function.Surjective L := by
    intro v
    refine ⟨(WithLp.equiv 2 _).symm ((Tᴴ * G⁻¹) *ᵥ WithLp.equiv 2 _ v), ?_⟩
    apply (WithLp.equiv 2 _).injective
    simp only [L, Matrix.piLp_equiv_toEuclideanLin_apply, Equiv.apply_symm_apply,
      Matrix.mulVec_mulVec, hInv, Matrix.one_mulVec]
  have hcard := Fintype.card_congr e
  have hdim := L.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top,
    finrank_euclideanSpace, finrank_euclideanSpace, Fintype.card_sum] at hdim
  rw [Fintype.card_sum, Fintype.card_sum] at hcard
  have hdim' : Module.finrank ℂ (LinearMap.ker L) = Fintype.card κ := by omega
  let b := (stdOrthonormalBasis ℂ (LinearMap.ker L)).reindex
    ((finCongr hdim').trans (Fintype.equivFin κ).symm)
  let K : Matrix (ρ ⊕ σ) κ ℂ := Matrix.of fun i j => WithLp.equiv 2 _ (b j).val i
  have hK : Kᴴ * K = 1 := by
    ext i j
    rw [Matrix.one_apply, ← orthonormal_iff_ite.mp b.orthonormal i j]
    change (Kᴴ * K) i j = ⟪(b i).val, (b j).val⟫_ℂ
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    rfl
  have hTK : T * K = 0 := by
    ext i j
    have h := congrArg (fun v => WithLp.equiv 2 _ v i) (LinearMap.mem_ker.mp (b j).property)
    simpa only [L, Matrix.piLp_equiv_toEuclideanLin_apply] using h
  let E₀ := K.toRows₁
  let F₀ := K.toRows₂
  have hK' : fromRows E₀ F₀ = K := Matrix.fromRows_toRows _
  have hsum : E₀ᴴ * E₀ + F₀ᴴ * F₀ = 1 := by
    rw [← hK, ← hK', Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
      Matrix.fromCols_mul_fromRows]
  have hz : X * E₀ + Y * F₀ = 0 := by
    rw [← hTK, ← hK', Matrix.fromCols_mul_fromRows]
  have hneg : X * E₀ = -(Y * F₀) := eq_neg_of_add_eq_zero_left hz
  have hEq : E₀ᴴ * E₀ = F₀ᴴ * F₀ := by
    have h (X : Matrix ι ρ ℂ) (E : Matrix ρ κ ℂ) (hX : Xᴴ * X = 1) :
        (X * E)ᴴ * (X * E) = Eᴴ * E := by
      rw [Matrix.conjTranspose_mul, Matrix.mul_assoc Eᴴ Xᴴ,
        ← Matrix.mul_assoc Xᴴ X, hX, Matrix.one_mul]
    have h' (Y : Matrix ι σ ℂ) (F : Matrix σ κ ℂ) (hY : Yᴴ * Y = 1) :
        (Y * F)ᴴ * (Y * F) = Fᴴ * F := by
      rw [Matrix.conjTranspose_mul, Matrix.mul_assoc Fᴴ Yᴴ,
        ← Matrix.mul_assoc Yᴴ Y, hY, Matrix.one_mul]
    rw [← h X E₀ hX, hneg, Matrix.conjTranspose_neg, neg_mul_neg, h' Y F₀ hY]
  let t : ℂ := 1 + Complex.I
  have ht : star t * t = (2 : ℂ) := by
    apply Complex.ext <;> norm_num [t, Complex.star_def, Complex.mul_re, Complex.mul_im]
  have ht' : t * star t = (2 : ℂ) := (mul_comm _ _).trans ht
  refine ⟨t • E₀, (-t) • F₀, ?_, ?_, ?_⟩
  · simpa only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      ht, ht', two_smul] using (by rw [hEq] at hsum; rw [hEq]; exact hsum :
        E₀ᴴ * E₀ + E₀ᴴ * E₀ = 1)
  · simpa only [Matrix.conjTranspose_smul, star_neg, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      neg_mul_neg, ht, ht', two_smul] using (hEq ▸ hsum : F₀ᴴ * F₀ + F₀ᴴ * F₀ = 1)
  · rw [Matrix.mul_smul, Matrix.mul_smul, hneg, smul_neg, neg_smul]

/-- Restricting a diagonal weight to the nonzero spectral entries discards
only zero contributions. -/
private theorem weighted_support_columns (U : Matrix ι ι ℂ) (a w : ι → ℂ)
    (hw : ∀ i, a i = 0 → w i = 0) :
    let X := U.submatrix id (Subtype.val : {i // a i ≠ 0} → ι)
    X * diagonal (fun i => w i.val) * Xᴴ = U * diagonal w * Uᴴ := by
  classical
  let X := U.submatrix id (Subtype.val : {i // a i ≠ 0} → ι)
  change X * diagonal (fun i => w i.val) * Xᴴ = _
  ext i j
  rw [Matrix.mul_apply (M := X * diagonal (fun i => w i.val)) (N := Xᴴ),
    Matrix.mul_apply (M := U * diagonal w) (N := Uᴴ)]
  simp only [X, Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.submatrix_apply, id_eq]
  symm
  apply Finset.sum_congr_set {k | a k ≠ 0}
  · intro k hk
    rfl
  · intro k hk
    have hk' : a k = 0 := by simpa using hk
    simp [hw k hk']

private def supportIndicator (a : ι → ℂ) (i : ι) : ℂ := if a i = 0 then 0 else 1

private theorem matchingProduct_supportIndicator (a b : ι → ℂ) (τ : Equiv.Perm ι) (k : ℕ)
    (h : (spectralSupport a).card + (spectralSupport b).card = Fintype.card ι + k) :
    matchingProduct (supportIndicator a) (supportIndicator b) τ =
      if CoversSupports a b τ then (2 : ℂ) ^ k else 0 := by
  classical
  by_cases hcov : CoversSupports a b τ
  · rw [if_pos hcov]
    let J := spectralSupport (a ∘ τ) ∩ spectralSupport b
    have hJ : J.card = k := by
      dsimp only [J]
      rw [cover_overlap_card a b τ hcov, h]
      omega
    let f := fun j => supportIndicator a (τ j) + supportIndicator b j
    change ∏ j, f j = _
    calc
      (∏ j, f j) = ∏ j ∈ J, f j := by
        symm
        apply Finset.prod_subset (Finset.subset_univ _)
        intro j _ hj
        rcases hcov j with ha | hb
        · have hb : b j = 0 := by
            by_contra hn
            exact hj (by simp [J, spectralSupport, ha, hn])
          simp [f, supportIndicator, ha, hb]
        · have ha : a (τ j) = 0 := by
            by_contra hn
            exact hj (by simp [J, spectralSupport, hn, hb])
          simp [f, supportIndicator, ha, hb]
      _ = (2 : ℂ) ^ J.card := by
        rw [← Finset.prod_const]
        apply Finset.prod_congr rfl
        intro j hj
        have hmem : a (τ j) ≠ 0 ∧ b j ≠ 0 := by simpa [J, spectralSupport] using hj
        norm_num [f, supportIndicator, hmem.1, hmem.2]
      _ = _ := by rw [hJ]
  · rw [if_neg hcov]
    obtain ⟨j, hj⟩ := not_forall.mp (show ¬ ∀ j, a (τ j) ≠ 0 ∨ b j ≠ 0 from hcov)
    have hz : a (τ j) = 0 ∧ b j = 0 := by simpa using hj
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [supportIndicator, hz.1, hz.2])

/-- The determinant of the sum of the support projections is the signed
cover mass scaled by two for every edge inside both supports. -/
private theorem determinantValue_supportIndicator (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (k : ℕ) (h : (spectralSupport a).card + (spectralSupport b).card = Fintype.card ι + k) :
    ∃ q : ℝ, 0 ≤ q ∧ q ≤ 1 ∧ (q = 1 ∨ (0 : ℂ) ∈ Set.range (matchingProduct a b)) ∧
      determinantValue (supportIndicator a) (supportIndicator b) U = (2 : ℂ) ^ k * (q : ℂ) := by
  classical
  obtain ⟨q, hq₀, hq₁, hq⟩ := signed_cover_mass_le_one a b U hU
  refine ⟨q, hq₀, hq₁, ?_, ?_⟩
  · by_cases hz : (0 : ℂ) ∈ Set.range (matchingProduct a b)
    · exact Or.inr hz
    left
    have hcov (τ : Equiv.Perm ι) : CoversSupports a b τ := by
      intro j
      by_contra hj
      obtain ⟨ha, hb⟩ : a (τ j) = 0 ∧ b j = 0 := by simpa using hj
      exact hz (zero_mem_matching_range a b (by rw [ha, hb, add_zero]))
    apply Complex.ofReal_injective
    rw [← hq, Complex.ofReal_one]
    calc
      _ = ∑ τ, signedWeight U τ := Finset.sum_congr rfl (fun τ _ => if_pos (hcov τ))
      _ = 1 := sum_signedWeight U (det_ne_zero_of_unitary hU)
  · rw [← signed_determinant _ _ U hU, ← hq, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro τ _
    rw [matchingProduct_supportIndicator a b τ k h]
    split_ifs <;> ring

private theorem exists_cover_with_two_edges (a b : ι → ℂ)
    (h : (spectralSupport a).card + (spectralSupport b).card = Fintype.card ι + 2)
    {i₀ i₁ j₀ j₁ : ι} (ha₀ : a i₀ ≠ 0) (ha₁ : a i₁ ≠ 0) (hi : i₀ ≠ i₁)
    (hb₀ : b j₀ ≠ 0) (hb₁ : b j₁ ≠ 0) (hj : j₀ ≠ j₁) :
    ∃ τ : Equiv.Perm ι, CoversSupports a b τ ∧ τ j₀ = i₀ ∧ τ j₁ = i₁ := by
  classical
  let A := ((spectralSupport a).erase i₀).erase i₁
  let B := spectralSupport b
  have hi₀ : i₀ ∈ spectralSupport a := by simp [spectralSupport, ha₀]
  have hi₁ : i₁ ∈ (spectralSupport a).erase i₀ := by simp [spectralSupport, ha₁, hi.symm]
  have hcard : A.card + B.card = Fintype.card ι := by
    dsimp [A, B]
    have h₀ := Finset.card_erase_add_one hi₀
    have h₁ := Finset.card_erase_add_one hi₁
    omega
  have hc (s : Finset ι) : Fintype.card {x // x ∉ s} = Fintype.card ι - s.card := by
    rw [Fintype.card_of_subtype (sᶜ) (by simp), Finset.card_compl]
  let f : B ≃ {x // x ∉ A} := Fintype.equivOfCardEq (by rw [Fintype.card_coe, hc]; omega)
  let g : {x // x ∉ B} ≃ A := Fintype.equivOfCardEq (by rw [Fintype.card_coe, hc]; omega)
  let x₀ : {x // x ∉ A} := ⟨i₀, by simp [A]⟩
  let x₁ : {x // x ∉ A} := ⟨i₁, by simp [A]⟩
  let y₀ : B := ⟨j₀, by simp [B, spectralSupport, hb₀]⟩
  let y₁ : B := ⟨j₁, by simp [B, spectralSupport, hb₁]⟩
  let f₀ := f.trans (Equiv.swap (f y₀) x₀)
  let f₁ := f₀.trans (Equiv.swap (f₀ y₁) x₁)
  have h₀ : f₀ y₀ = x₀ := by simp [f₀]
  have h₁ : f₁ y₁ = x₁ := by simp [f₁]
  have h₂ : f₁ y₀ = x₀ := by
    have hne₀ : x₀ ≠ f₀ y₁ := by
      rw [← h₀]
      exact fun hh => hj (congrArg Subtype.val (f₀.injective hh))
    have hne₁ : x₀ ≠ x₁ := fun hh => hi (congrArg Subtype.val hh)
    rw [show f₁ y₀ = Equiv.swap (f₀ y₁) x₁ (f₀ y₀) from rfl, h₀,
      Equiv.swap_apply_of_ne_of_ne hne₀ hne₁]
  let eA := Equiv.sumCompl (fun x => x ∈ A)
  let eB := Equiv.sumCompl (fun x => x ∈ B)
  let τ := eB.symm.trans ((Equiv.sumCongr f₁ g).trans ((Equiv.sumComm _ _).trans eA))
  have hf (x : B) : τ x = f₁ x := by
    change τ (eB (Sum.inl x)) = _
    simp only [τ, Equiv.trans_apply, Equiv.symm_apply_apply]
    rfl
  have hg (x : {x // x ∉ B}) : τ x = g x := by
    change τ (eB (Sum.inr x)) = _
    simp only [τ, Equiv.trans_apply, Equiv.symm_apply_apply]
    rfl
  refine ⟨τ, fun k => ?_, ?_, ?_⟩
  · by_cases hk : k ∈ B
    · exact Or.inr (by simpa [B, spectralSupport] using hk)
    · apply Or.inl
      have hmem : τ k ∈ A := by rw [hg ⟨k, hk⟩]; exact (g ⟨k, hk⟩).property
      have ha := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hmem)
      simpa [spectralSupport] using ha
  · exact (hf y₀).trans (congrArg Subtype.val h₂)
  · exact (hf y₁).trans (congrArg Subtype.val h₁)

private theorem two_edge_reciprocal_vertex (a b : ι → ℂ)
    (h : (spectralSupport a).card + (spectralSupport b).card = Fintype.card ι + 2)
    (m : TwoEdgeMatching {i // a i ≠ 0} {j // b j ≠ 0}) :
    let D := (∏ i : {i // a i ≠ 0}, a i) * ∏ j : {j // b j ≠ 0}, b j
    D * (((a m.val.1.1)⁻¹ + (b m.val.1.2)⁻¹) * ((a m.val.2.1)⁻¹ + (b m.val.2.2)⁻¹)) ∈
      Set.range (matchingProduct a b) := by
  classical
  dsimp only
  let i₀ : ι := m.val.1.1
  let i₁ : ι := m.val.2.1
  let j₀ : ι := m.val.1.2
  let j₁ : ι := m.val.2.2
  have hi : i₀ ≠ i₁ := fun he => m.property.1 (Subtype.ext he)
  have hj : j₀ ≠ j₁ := fun he => m.property.2 (Subtype.ext he)
  have ha₀ : a i₀ ≠ 0 := m.val.1.1.property
  have ha₁ : a i₁ ≠ 0 := m.val.2.1.property
  have hb₀ : b j₀ ≠ 0 := m.val.1.2.property
  have hb₁ : b j₁ ≠ 0 := m.val.2.2.property
  obtain ⟨τ, hcov, hτ₀, hτ₁⟩ := exists_cover_with_two_edges a b h ha₀ ha₁ hi hb₀ hb₁ hj
  let J := spectralSupport (a ∘ τ) ∩ spectralSupport b
  have hJ₀ : j₀ ∈ J := by simp [J, spectralSupport, hτ₀, ha₀, hb₀]
  have hJ₁ : j₁ ∈ J := by simp [J, spectralSupport, hτ₁, ha₁, hb₁]
  have hJ : J = {j₀, j₁} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact hJ₀
      · rw [Finset.mem_singleton.mp hk]
        exact hJ₁
    dsimp only [J]
    rw [cover_overlap_card a b τ hcov, h]
    simpa [hj]
  let f := fun j => (if a (τ j) = 0 then 1 else a (τ j)) * (if b j = 0 then 1 else b j)
  let g := fun j => if j ∈ J then (a (τ j))⁻¹ + (b j)⁻¹ else 1
  have hv (j : ι) : a (τ j) + b j = f j * g j := by
    by_cases ha : a (τ j) = 0 <;> by_cases hb : b j = 0
    · exact ((hcov j).elim (fun hne => hne ha) (fun hne => hne hb)).elim
    · simp [f, g, J, spectralSupport, ha, hb]
    · simp [f, g, J, spectralSupport, ha, hb]
    · simp [f, g, J, spectralSupport, ha, hb]
      field_simp
      ring
  have hf : (∏ j, f j) = (∏ i : {i // a i ≠ 0}, a i) * ∏ j : {j // b j ≠ 0}, b j := by
    have hp (c : ι → ℂ) : (∏ i, if c i = 0 then 1 else c i) = ∏ i : {i // c i ≠ 0}, c i := by
      apply Finset.prod_congr_set {i | c i ≠ 0}
      · intro i hi'
        exact if_neg hi'
      · intro i hi'
        apply if_pos
        simpa using hi'
    dsimp only [f]
    rw [Finset.prod_mul_distrib, Equiv.prod_comp τ (fun i => if a i = 0 then 1 else a i),
      hp a, hp b]
  have hg : (∏ j, g j) = ((a i₀)⁻¹ + (b j₀)⁻¹) * ((a i₁)⁻¹ + (b j₁)⁻¹) := by
    calc
      (∏ j, g j) = ∏ j ∈ J, g j := by
        symm
        apply Finset.prod_subset (Finset.subset_univ _)
        intro j _ hj'
        simp [g, hj']
      _ = _ := by rw [hJ, Finset.prod_pair hj]; simp [g, hJ₀, hJ₁, hτ₀, hτ₁]
  refine ⟨τ, ?_⟩
  unfold matchingProduct
  simp_rw [hv, Finset.prod_mul_distrib, hf, hg] <;> rfl

private theorem support_columns_isometry (U : Matrix ι ι ℂ) (hU : IsUnitary U) (a : ι → ℂ) :
    let X := U.submatrix id (Subtype.val : {i // a i ≠ 0} → ι)
    Xᴴ * X = 1 := by
  classical
  dsimp only
  rw [Matrix.conjTranspose_submatrix,
    ← Matrix.submatrix_mul Uᴴ U Subtype.val id Subtype.val Function.bijective_id,
    hU.2, Matrix.submatrix_one _ Subtype.val_injective]

private theorem det_support_sum_eq_zero_of_gram (X : Matrix ι ρ ℂ) (Y : Matrix ι σ ℂ)
    (a : ρ → ℂ) (b : σ → ℂ) (hG : (X * Xᴴ + Y * Yᴴ).det = 0) :
    (X * diagonal a * Xᴴ + Y * diagonal b * Yᴴ).det = 0 := by
  let T := fromCols X Y
  have hTG : T * Tᴴ = X * Xᴴ + Y * Yᴴ := by
    simp only [T, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
      Matrix.fromCols_mul_fromRows]
  obtain ⟨v, hv, hnull⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hG
  rw [← hTG] at hnull
  have hperp : Tᴴ *ᵥ v = 0 := (Matrix.self_mul_conjTranspose_mulVec_eq_zero T v).mp hnull
  have hsum : T * diagonal (Sum.elim a b) * Tᴴ = X * diagonal a * Xᴴ + Y * diagonal b * Yᴴ := by
    simp only [T, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
      ← Matrix.fromBlocks_diagonal, Matrix.fromCols_mul_fromBlocks, Matrix.mul_zero, add_zero,
      zero_add, Matrix.fromCols_mul_fromRows]
  apply Matrix.exists_mulVec_eq_zero_iff.mp
  refine ⟨v, hv, ?_⟩
  rw [← hsum, ← Matrix.mulVec_mulVec, hperp, Matrix.mulVec_zero]

/-- When the two support sizes exceed the matrix order by two, the
reciprocal compression has two columns and admits a two-edge matching law. -/
theorem holds_of_support_excess_two (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (h : (spectralSupport a).card + (spectralSupport b).card = Fintype.card ι + 2) : Holds a b U := by
  classical
  let ρ := {i // a i ≠ 0}
  let σ := {j // b j ≠ 0}
  let X : Matrix ι ρ ℂ := (1 : Matrix ι ι ℂ).submatrix id Subtype.val
  let Y : Matrix ι σ ℂ := U.submatrix id Subtype.val
  let a' : ρ → ℂ := fun i => a i
  let b' : σ → ℂ := fun j => b j
  let D := (∏ i, a' i) * ∏ j, b' j
  let G := X * Xᴴ + Y * Yᴴ
  let Hull := convexHull ℝ (Set.range (matchingProduct a b))
  have hdet : determinantValue a b U = (X * diagonal a' * Xᴴ + Y * diagonal b' * Yᴴ).det := by
    unfold determinantValue
    rw [weighted_support_columns 1 a a (fun _ h₀ => h₀),
      weighted_support_columns U b b (fun _ h₀ => h₀), Matrix.one_mul,
      Matrix.conjTranspose_one, Matrix.mul_one]
  have hflag (c : ι → ℂ) :
      diagonal (fun i : {i // c i ≠ 0} => supportIndicator c i) = 1 := by
    rw [← Matrix.diagonal_one]
    apply congrArg Matrix.diagonal
    funext i
    simp [supportIndicator, i.property]
  have hGram : G = diagonal (supportIndicator a) + U * diagonal (supportIndicator b) * Uᴴ := by
    calc
      _ = X * diagonal (fun i : ρ => supportIndicator a i) * Xᴴ +
          Y * diagonal (fun j : σ => supportIndicator b j) * Yᴴ := by
        rw [hflag, hflag, Matrix.mul_one, Matrix.mul_one]
      _ = _ := by
        rw [weighted_support_columns 1 a (supportIndicator a) (by simp [supportIndicator]),
          weighted_support_columns U b (supportIndicator b) (by simp [supportIndicator]),
          Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one]
  obtain ⟨q, hq₀, hq₁, hqvertex, hq⟩ := determinantValue_supportIndicator a b U hU 2 h
  have hGdet : G.det = (2 : ℂ) ^ 2 * (q : ℂ) := by rw [hGram]; exact hq
  by_cases hGzero : G.det = 0
  · have hqzero : (q : ℂ) = 0 :=
      (mul_eq_zero.mp (hGdet.symm.trans hGzero)).resolve_left (pow_ne_zero _ (by norm_num))
    have hqzero' : q = 0 := by exact_mod_cast hqzero
    have hz := hqvertex.resolve_left (by simp [hqzero'])
    unfold Holds
    rw [hdet, det_support_sum_eq_zero_of_gram X Y a' b' hGzero]
    exact subset_convexHull ℝ _ hz
  have hρ : Fintype.card ρ = (spectralSupport a).card := Fintype.card_of_subtype _ (by
    simp [spectralSupport])
  have hσ : Fintype.card σ = (spectralSupport b).card := Fintype.card_of_subtype _ (by
    simp [spectralSupport])
  let e : ι ⊕ Fin 2 ≃ ρ ⊕ σ := Fintype.equivOfCardEq (by
    rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_fin, hρ, hσ, h])
  have hX : Xᴴ * X = 1 := support_columns_isometry 1 (by simp [IsUnitary]) a
  have hY : Yᴴ * Y = 1 := support_columns_isometry U hU b
  have hGun : IsUnit G.det := isUnit_iff_ne_zero.mpr hGzero
  obtain ⟨E, F, hE, hF, hcommon⟩ := exists_overlap_frames e X Y hX hY hGun
  let x : ρ → ℂ := fun i => (a' i)⁻¹
  let y : σ → ℂ := fun j => (b' j)⁻¹
  let z := (Eᴴ * diagonal x * E + Fᴴ * diagonal y * F).det
  have hprod := det_support_frames e X Y E F hE hF hcommon hGun a' b'
    (fun i => i.property) (fun j => j.property)
  change (X * diagonal a' * Xᴴ + Y * diagonal b' * Yᴴ).det =
    D * (G.det / (2 : ℂ) ^ Fintype.card (Fin 2)) * z at hprod
  have hscaled : determinantValue a b U = q • (D * z) := by
    rw [hdet, hprod, hGdet, Fintype.card_fin, Complex.real_smul]
    field_simp <;> ring
  have hz := det_twoFrame_compression_mem_hull E F hE hF x y
  have hm : D * z ∈ Hull := by
    change z ∈ (LinearMap.mulLeft ℝ D) ⁻¹' Hull
    apply convexHull_min _ ((convex_convexHull ℝ _).linear_preimage (LinearMap.mulLeft ℝ D)) hz
    rintro _ ⟨m, rfl⟩
    exact subset_convexHull ℝ _ (two_edge_reciprocal_vertex a b h m)
  unfold Holds
  rw [hscaled]
  rcases hqvertex with rfl | hzero
  · simpa using hm
  · have hmem := (convex_convexHull ℝ (Set.range (matchingProduct a b)))
      (subset_convexHull ℝ _ hzero) hm (sub_nonneg.mpr hq₁) hq₀ (sub_add_cancel 1 q)
    simpa using hmem

/-- Opposite scalar shifts preserve the rank-two-overlap reduction. -/
theorem holds_of_shifted_support_le_card_add_two (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) (t : ℂ)
    (h : (spectralSupport (fun i => a i + t)).card + (spectralSupport (fun i => b i - t)).card ≤
      Fintype.card ι + 2) : Holds a b U := by
  rcases lt_or_eq_of_le h with hlt | heq
  · exact holds_of_shifted_support_le_card_add_one a b U hU t (by omega)
  · exact (holds_shift_iff a b hU t).mp (holds_of_support_excess_two _ _ U hU heq)

end

end MOC
