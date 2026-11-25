import MOC.RankSum
import MOC.CommonWeights
import MOC.TwoFrame
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Topology.Instances.Matrix

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
    have h := congrArg (fun v : EuclideanSpace ℂ ι => WithLp.equiv 2 (ι → ℂ) v i)
      (LinearMap.mem_ker.mp (b j).property)
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
    rw [← h X E₀ hX, hneg, Matrix.conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg,
      neg_neg, h' Y F₀ hY]
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
theorem weighted_support_columns (U : Matrix ι ι ℂ) (a w : ι → ℂ)
    (hw : ∀ i, a i = 0 → w i = 0) :
    let X := U.submatrix id (Subtype.val : {i // a i ≠ 0} → ι)
    X * diagonal (fun i => w i.val) * Xᴴ = U * diagonal w * Uᴴ := by
  classical
  let X := U.submatrix id (Subtype.val : {i // a i ≠ 0} → ι)
  change X * diagonal (fun i => w i.val) * Xᴴ = _
  ext i j
  change (∑ k : {i // a i ≠ 0}, (X * diagonal (fun l : {i // a i ≠ 0} => w l.val)) i k *
      Xᴴ k j) = ∑ k : ι, (U * diagonal w) i k * Uᴴ k j
  simp only [X, Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.submatrix_apply, id_eq]
  symm
  apply Finset.sum_congr_set {k | a k ≠ 0}
  · intro k hk
    rfl
  · intro k hk
    have hk' : a k = 0 := by simpa using hk
    simp [hw k hk']

def supportIndicator (a : ι → ℂ) (i : ι) : ℂ := if a i = 0 then 0 else 1

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

private theorem determinantValue_supportIndicator_cover (a b : ι → ℂ)
    (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (k : ℕ) (h : (spectralSupport a).card + (spectralSupport b).card = Fintype.card ι + k) :
    ∃ q : ℝ, 0 ≤ q ∧ q ≤ 1 ∧ (q = 1 ∨ ∃ τ, ¬ CoversSupports a b τ) ∧
      determinantValue (supportIndicator a) (supportIndicator b) U = (2 : ℂ) ^ k * (q : ℂ) := by
  classical
  obtain ⟨q, hq₀, hq₁, hq⟩ := signed_cover_mass_le_one a b U hU
  refine ⟨q, hq₀, hq₁, ?_, ?_⟩
  · by_cases hcov : ∀ τ, CoversSupports a b τ
    · left
      apply Complex.ofReal_injective
      rw [← hq, Complex.ofReal_one]
      calc
        _ = ∑ τ, signedWeight U τ := Finset.sum_congr rfl (fun τ _ => if_pos (hcov τ))
        _ = 1 := sum_signedWeight U (det_ne_zero_of_unitary hU)
    · exact Or.inr (not_forall.mp hcov)
  · rw [← signed_determinant _ _ U hU, ← hq, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro τ _
    rw [matchingProduct_supportIndicator a b τ k h]
    split_ifs <;> ring

private theorem supportNoncover_matchingProduct_eq_zero (a b : ι → ℂ)
    (τ : Equiv.Perm ι) (h : ¬ CoversSupports a b τ) : matchingProduct a b τ = 0 := by
  obtain ⟨j, hj⟩ := not_forall.mp
    (show ¬ ∀ j, a (τ j) ≠ 0 ∨ b j ≠ 0 from h)
  have hz : a (τ j) = 0 ∧ b j = 0 := by simpa only [not_or, not_not] using hj
  unfold matchingProduct
  exact Finset.prod_eq_zero (Finset.mem_univ j) (by rw [hz.1, hz.2, add_zero])

/-- The determinant of the sum of the support projections is the signed
cover mass scaled by two for every edge inside both supports. -/
theorem determinantValue_supportIndicator (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (k : ℕ) (h : (spectralSupport a).card + (spectralSupport b).card = Fintype.card ι + k) :
    ∃ q : ℝ, 0 ≤ q ∧ q ≤ 1 ∧ (q = 1 ∨ (0 : ℂ) ∈ Set.range (matchingProduct a b)) ∧
      determinantValue (supportIndicator a) (supportIndicator b) U = (2 : ℂ) ^ k * (q : ℂ) := by
  obtain ⟨q, hq₀, hq₁, hcover, hq⟩ := determinantValue_supportIndicator_cover a b U hU k h
  refine ⟨q, hq₀, hq₁, hcover.imp_right ?_, hq⟩
  rintro ⟨τ, hτ⟩
  exact ⟨τ, supportNoncover_matchingProduct_eq_zero a b τ hτ⟩

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

private theorem matchingProduct_eq_reciprocal_two_edges (a b : ι → ℂ)
    (h : (spectralSupport a).card + (spectralSupport b).card = Fintype.card ι + 2)
    (τ : Equiv.Perm ι) (hcov : CoversSupports a b τ)
    {i₀ i₁ j₀ j₁ : ι} (ha₀ : a i₀ ≠ 0) (ha₁ : a i₁ ≠ 0)
    (hb₀ : b j₀ ≠ 0) (hb₁ : b j₁ ≠ 0) (hj : j₀ ≠ j₁)
    (hτ₀ : τ j₀ = i₀) (hτ₁ : τ j₁ = i₁) :
    let D := (∏ i : {i // a i ≠ 0}, a i) * ∏ j : {j // b j ≠ 0}, b j
    matchingProduct a b τ = D * (((a i₀)⁻¹ + (b j₀)⁻¹) * ((a i₁)⁻¹ + (b j₁)⁻¹)) := by
  classical
  dsimp only
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
  unfold matchingProduct
  simp_rw [hv, Finset.prod_mul_distrib, hf, hg] <;> rfl

theorem support_columns_isometry (U : Matrix ι ι ℂ) (hU : IsUnitary U) (a : ι → ℂ) :
    let X := U.submatrix id (Subtype.val : {i // a i ≠ 0} → ι)
    Xᴴ * X = 1 := by
  classical
  dsimp only
  rw [Matrix.conjTranspose_submatrix,
    ← Matrix.submatrix_mul Uᴴ U Subtype.val id Subtype.val Function.bijective_id,
    hU.2, Matrix.submatrix_one _ Subtype.val_injective]

theorem det_support_sum_eq_zero_of_gram (X : Matrix ι ρ ℂ) (Y : Matrix ι σ ℂ)
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

private theorem push_permutation_law {κ : Type*} [Fintype κ]
    (p : κ → Equiv.Perm ι) (mass : κ → ℝ)
    (hm : ∀ k, 0 ≤ mass k) (hs : ∑ k, mass k = 1) :
    ∃ w : Equiv.Perm ι → ℝ, (∀ τ, 0 ≤ w τ) ∧ (∑ τ, w τ = 1) ∧
      ∀ f : Equiv.Perm ι → ℂ, (∑ τ, (w τ : ℂ) * f τ) =
        ∑ k, (mass k : ℂ) * f (p k) := by
  classical
  let w (τ : Equiv.Perm ι) := ∑ k ∈ Finset.univ.filter (fun k => p k = τ), mass k
  refine ⟨w, fun τ => Finset.sum_nonneg (fun k _ => hm k), ?_, fun f => ?_⟩
  · exact (Finset.sum_fiberwise Finset.univ p mass).trans hs
  · rw [← Finset.sum_fiberwise Finset.univ p]
    apply Finset.sum_congr rfl
    intro τ _
    dsimp only [w]
    rw [Complex.ofReal_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    rw [(Finset.mem_filter.mp hk).2]

private theorem support_equal_of_zero_iff (a a₀ : ι → ℂ) (ha : ∀ i, a i = 0 ↔ a₀ i = 0) :
    spectralSupport a = spectralSupport a₀ := by
  ext i
  simpa only [spectralSupport, Finset.mem_filter, Finset.mem_univ, true_and] using not_congr (ha i)

private theorem covers_of_zero_iff (a b a₀ b₀ : ι → ℂ) (τ : Equiv.Perm ι)
    (ha : ∀ i, a i = 0 ↔ a₀ i = 0) (hb : ∀ j, b j = 0 ↔ b₀ j = 0) :
    CoversSupports a b τ ↔ CoversSupports a₀ b₀ τ := by
  change (∀ j, a (τ j) ≠ 0 ∨ b j ≠ 0) ↔ (∀ j, a₀ (τ j) ≠ 0 ∨ b₀ j ≠ 0)
  exact forall_congr' fun j => or_congr (not_congr (ha (τ j))) (not_congr (hb j))

/-- For fixed support sets with total size two above the order, the
permutation law depends on the mixer and the sets alone. -/
theorem exists_common_weights_of_support_excess_two (a₀ b₀ : ι → ℂ)
    (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (h : (spectralSupport a₀).card + (spectralSupport b₀).card = Fintype.card ι + 2) :
    ∃ w : Equiv.Perm ι → ℝ, (∀ τ, 0 ≤ w τ) ∧ (∑ τ, w τ = 1) ∧
      ∀ a b : ι → ℂ, (∀ i, a i = 0 ↔ a₀ i = 0) → (∀ j, b j = 0 ↔ b₀ j = 0) →
        weightedMatchingValue a b w = determinantValue a b U := by
  classical
  let ρ := {i // a₀ i ≠ 0}
  let σ := {j // b₀ j ≠ 0}
  let X : Matrix ι ρ ℂ := (1 : Matrix ι ι ℂ).submatrix id Subtype.val
  let Y : Matrix ι σ ℂ := U.submatrix id Subtype.val
  let G := X * Xᴴ + Y * Yᴴ
  have hdet (a b : ι → ℂ) (ha : ∀ i, a i = 0 ↔ a₀ i = 0)
      (hb : ∀ j, b j = 0 ↔ b₀ j = 0) :
      determinantValue a b U =
        (X * diagonal (fun i : ρ => a i) * Xᴴ + Y * diagonal (fun j : σ => b j) * Yᴴ).det := by
    unfold determinantValue
    rw [weighted_support_columns 1 a₀ a (fun i hi => (ha i).mpr hi),
      weighted_support_columns U b₀ b (fun j hj => (hb j).mpr hj),
      Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one]
  have hflag (c : ι → ℂ) :
      diagonal (fun i : {i // c i ≠ 0} => supportIndicator c i) = 1 := by
    rw [← Matrix.diagonal_one]
    apply congrArg Matrix.diagonal
    funext i
    simp only [supportIndicator, if_neg i.property]
  have hGram : G = diagonal (supportIndicator a₀) + U * diagonal (supportIndicator b₀) * Uᴴ := by
    calc
      _ = X * diagonal (fun i : ρ => supportIndicator a₀ i) * Xᴴ +
          Y * diagonal (fun j : σ => supportIndicator b₀ j) * Yᴴ := by
        rw [hflag, hflag, Matrix.mul_one, Matrix.mul_one]
      _ = _ := by
        rw [weighted_support_columns 1 a₀ (supportIndicator a₀) (by simp [supportIndicator]),
          weighted_support_columns U b₀ (supportIndicator b₀) (by simp [supportIndicator]),
          Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one]
  obtain ⟨q, hq₀, hq₁, hqcover, hq⟩ := determinantValue_supportIndicator_cover a₀ b₀ U hU 2 h
  have hGdet : G.det = (2 : ℂ) ^ 2 * (q : ℂ) := by rw [hGram]; exact hq
  obtain ⟨τ₀, hτ₀⟩ : ∃ τ : Equiv.Perm ι, q = 1 ∨ ¬ CoversSupports a₀ b₀ τ := by
    rcases hqcover with hqone | ⟨τ, hτ⟩
    · exact ⟨1, Or.inl hqone⟩
    · exact ⟨τ, Or.inr hτ⟩
  have hresidual (a b : ι → ℂ) (ha : ∀ i, a i = 0 ↔ a₀ i = 0)
      (hb : ∀ j, b j = 0 ↔ b₀ j = 0) :
      ((1 - q : ℝ) : ℂ) * matchingProduct a b τ₀ = 0 := by
    rcases hτ₀ with hqone | hmiss
    · simp only [hqone, sub_self, Complex.ofReal_zero, zero_mul]
    · rw [supportNoncover_matchingProduct_eq_zero a b τ₀
        (fun hc => hmiss ((covers_of_zero_iff a b a₀ b₀ τ₀ ha hb).mp hc)), mul_zero]
  by_cases hGzero : G.det = 0
  · have hqzero : (q : ℂ) = 0 :=
      (mul_eq_zero.mp (hGdet.symm.trans hGzero)).resolve_left (pow_ne_zero _ (by norm_num))
    have hqzero' : q = 0 := by exact_mod_cast hqzero
    obtain ⟨w, hw, hs, hp⟩ := push_permutation_law (fun _ : Unit => τ₀) (fun _ => 1)
      (fun _ => zero_le_one) (by simp)
    refine ⟨w, hw, hs, fun a b ha hb => ?_⟩
    rw [weightedMatchingValue, hp, hdet a b ha hb,
      det_support_sum_eq_zero_of_gram X Y _ _ hGzero]
    simpa only [Fintype.sum_unique, Complex.ofReal_one, one_mul] using
      (by simpa only [hqzero', sub_zero, Complex.ofReal_one, one_mul] using hresidual a b ha hb :
        matchingProduct a b τ₀ = 0)
  have hρ : Fintype.card ρ = (spectralSupport a₀).card :=
    Fintype.card_of_subtype _ (by simp [spectralSupport])
  have hσ : Fintype.card σ = (spectralSupport b₀).card :=
    Fintype.card_of_subtype _ (by simp [spectralSupport])
  let e : ι ⊕ Fin 2 ≃ ρ ⊕ σ := Fintype.equivOfCardEq (by
    rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_fin, hρ, hσ, h])
  have hX : Xᴴ * X = 1 := support_columns_isometry 1 isUnitary_one a₀
  have hY : Yᴴ * Y = 1 := support_columns_isometry U hU b₀
  have hGun : IsUnit G.det := isUnit_iff_ne_zero.mpr hGzero
  obtain ⟨E, F, hE, hF, hcommon⟩ := exists_overlap_frames e X Y hX hY hGun
  obtain ⟨S, μ, hμ, hS, hval⟩ := exists_twoFrame_compression_weights E F hE hF
  let κ := TwoEdgeMatching ρ σ
  have hleft (m : κ) : (m.val.1.1 : ι) ≠ m.val.2.1 :=
    fun he => m.property.1 (Subtype.ext he)
  have hright (m : κ) : (m.val.1.2 : ι) ≠ m.val.2.2 :=
    fun he => m.property.2 (Subtype.ext he)
  have hcomplete (m : κ) :
      ∃ τ : Equiv.Perm ι, CoversSupports a₀ b₀ τ ∧
        τ m.val.1.2 = (m.val.1.1 : ι) ∧ τ m.val.2.2 = (m.val.2.1 : ι) :=
    exists_cover_with_two_edges a₀ b₀ h
      m.val.1.1.property m.val.2.1.property (hleft m)
      m.val.1.2.property m.val.2.2.property (hright m)
  let pick (m : κ) := Classical.choose (hcomplete m)
  let p : Unit ⊕ ↑S → Equiv.Perm ι := Sum.elim (fun _ => τ₀) (fun m => pick m.val)
  let mass : Unit ⊕ ↑S → ℝ := Sum.elim (fun _ => 1 - q) (fun m => q * μ m.val)
  have hmass (k : Unit ⊕ ↑S) : 0 ≤ mass k := by
    cases k with
    | inl _ => exact sub_nonneg.mpr hq₁
    | inr m => exact mul_nonneg hq₀ (hμ m.val m.property)
  have htotal : ∑ k, mass k = 1 := by
    rw [Fintype.sum_sum_type]
    simp only [mass, Sum.elim_inl, Sum.elim_inr, Fintype.sum_unique, ← Finset.mul_sum]
    rw [Finset.sum_coe_sort S μ, hS, mul_one, sub_add_cancel]
  obtain ⟨w, hw, hs, hp⟩ := push_permutation_law p mass hmass htotal
  refine ⟨w, hw, hs, fun a b ha hb => ?_⟩
  let x : ρ → ℂ := fun i => (a i)⁻¹
  let y : σ → ℂ := fun j => (b j)⁻¹
  let D := (∏ i : ρ, a i) * ∏ j : σ, b j
  have hprod_eq (c c₀ : ι → ℂ) (hc : ∀ i, c i = 0 ↔ c₀ i = 0) :
      (∏ i : {i // c i ≠ 0}, c i.val) = ∏ i : {i // c₀ i ≠ 0}, c i.val := by
    let e := Equiv.subtypeEquivRight (fun i => not_congr (hc i))
    exact Equiv.prod_comp e (fun i : {i // c₀ i ≠ 0} => c i.val)
  have hpoint (m : κ) :
      matchingProduct a b (pick m) =
        D * ((x m.val.1.1 + y m.val.1.2) * (x m.val.2.1 + y m.val.2.2)) := by
    obtain ⟨hc, hfirst, hsecond⟩ := Classical.choose_spec (hcomplete m)
    have hsupp : (spectralSupport a).card + (spectralSupport b).card = Fintype.card ι + 2 := by
      rw [support_equal_of_zero_iff a a₀ ha, support_equal_of_zero_iff b b₀ hb]
      exact h
    have hd := matchingProduct_eq_reciprocal_two_edges a b hsupp (pick m)
      ((covers_of_zero_iff a b a₀ b₀ (pick m) ha hb).mpr hc)
      (fun hi => m.val.1.1.property ((ha _).mp hi))
      (fun hi => m.val.2.1.property ((ha _).mp hi))
      (fun hi => m.val.1.2.property ((hb _).mp hi))
      (fun hi => m.val.2.2.property ((hb _).mp hi)) (hright m) hfirst hsecond
    simpa only [D, x, y, hprod_eq a a₀ ha, hprod_eq b b₀ hb] using hd
  have hdet' := det_support_frames e X Y E F hE hF hcommon hGun
    (fun i : ρ => a i) (fun j : σ => b j)
    (fun i hi => i.property ((ha _).mp hi)) (fun j hj => j.property ((hb _).mp hj))
  rw [weightedMatchingValue, hp, Fintype.sum_sum_type]
  simp only [p, mass, Sum.elim_inl, Sum.elim_inr, Fintype.sum_unique, hresidual a b ha hb,
    zero_add, Complex.ofReal_mul, hpoint]
  simp_rw [show ∀ m : ↑S,
    ((q : ℂ) * (μ m.val : ℂ)) *
        (D * ((x m.val.val.1.1 + y m.val.val.1.2) * (x m.val.val.2.1 + y m.val.val.2.2))) =
      (q : ℂ) * D * ((μ m.val : ℂ) *
        ((x m.val.val.1.1 + y m.val.val.1.2) * (x m.val.val.2.1 + y m.val.val.2.2)))
    from fun m => by ring]
  rw [← Finset.mul_sum, Finset.sum_coe_sort S (fun m =>
    (μ m : ℂ) * ((x m.val.1.1 + y m.val.1.2) * (x m.val.2.1 + y m.val.2.2))),
    hval x y, hdet a b ha hb, hdet', hGdet, Fintype.card_fin]
  change (q : ℂ) * D * (Eᴴ * diagonal x * E + Fᴴ * diagonal y * F).det =
    D * ((2 : ℂ) ^ 2 * (q : ℂ) / 2 ^ 2) * (Eᴴ * diagonal x * E + Fᴴ * diagonal y * F).det
  ring

private theorem common_weights_on_allowed_supports (a₀ b₀ : ι → ℂ)
    (U : Matrix ι ι ℂ) (w : Equiv.Perm ι → ℝ)
    (h : ∀ a b : ι → ℂ, (∀ i, a i = 0 ↔ a₀ i = 0) → (∀ j, b j = 0 ↔ b₀ j = 0) →
      weightedMatchingValue a b w = determinantValue a b U)
    (a b : ι → ℂ) (ha : spectralSupport a ⊆ spectralSupport a₀)
    (hb : spectralSupport b ⊆ spectralSupport b₀) :
    weightedMatchingValue a b w = determinantValue a b U := by
  classical
  have zero_outside (c c₀ : ι → ℂ) (hc : spectralSupport c ⊆ spectralSupport c₀)
      (i : ι) (hi : c₀ i = 0) : c i = 0 := by
    by_contra hne
    have hm := hc (show i ∈ spectralSupport c by simp [spectralSupport, hne])
    simpa [spectralSupport, hi] using hm
  let A (t : ℂ) (i : ι) := if a₀ i = 0 then 0 else a i + t
  let B (t : ℂ) (j : ι) := if b₀ j = 0 then 0 else b j + t
  let K : Set ℂ := Set.range (fun i => -a i) ∪ Set.range (fun j => -b j)
  have hdense : Dense Kᶜ := ((Set.finite_range _).union (Set.finite_range _)).countable.dense_compl ℂ
  have hA : Continuous A := continuous_pi fun i => by
    by_cases hi : a₀ i = 0
    · simpa only [A, if_pos hi] using (continuous_const : Continuous (fun _ : ℂ => (0 : ℂ)))
    · simpa only [A, if_neg hi] using (continuous_const.add continuous_id :
        Continuous (fun t : ℂ => a i + t))
  have hB : Continuous B := continuous_pi fun j => by
    by_cases hj : b₀ j = 0
    · simpa only [B, if_pos hj] using (continuous_const : Continuous (fun _ : ℂ => (0 : ℂ)))
    · simpa only [B, if_neg hj] using (continuous_const.add continuous_id :
        Continuous (fun t : ℂ => b j + t))
  have hclosed : IsClosed {t : ℂ | weightedMatchingValue (A t) (B t) w =
      determinantValue (A t) (B t) U} := by
    apply isClosed_eq
    · unfold weightedMatchingValue matchingProduct
      fun_prop
    · unfold determinantValue
      fun_prop
  have hreg : Kᶜ ⊆ {t : ℂ | weightedMatchingValue (A t) (B t) w =
      determinantValue (A t) (B t) U} := by
    intro t ht
    apply h
    · intro i
      by_cases hi : a₀ i = 0
      · simp only [A, if_pos hi, hi]
      · have hn : a i + t ≠ 0 := by
          intro hz
          have he : -a i = t := by linear_combination -hz
          exact ht (Or.inl ⟨i, he⟩)
        simp only [A, if_neg hi, hi, hn]
    · intro j
      by_cases hj : b₀ j = 0
      · simp only [B, if_pos hj, hj]
      · have hn : b j + t ≠ 0 := by
          intro hz
          have he : -b j = t := by linear_combination -hz
          exact ht (Or.inr ⟨j, he⟩)
        simp only [B, if_neg hj, hj, hn]
  have hzero := closure_minimal hreg hclosed (hdense 0)
  have ha₀ : A 0 = a := funext fun i => by
    by_cases hi : a₀ i = 0
    · rw [show A 0 i = 0 by simp only [A, if_pos hi], zero_outside a a₀ ha i hi]
    · simp only [A, if_neg hi, add_zero]
  have hb₀ : B 0 = b := funext fun j => by
    by_cases hj : b₀ j = 0
    · rw [show B 0 j = 0 by simp only [B, if_pos hj], zero_outside b b₀ hb j hj]
    · simp only [B, if_neg hj, add_zero]
  change weightedMatchingValue (A 0) (B 0) w = determinantValue (A 0) (B 0) U at hzero
  rwa [ha₀, hb₀] at hzero

/-- One probability law works for all spectra supported on the two specified
label sets when their total size is at most two above the matrix order. -/
theorem exists_common_weights_of_support_le_card_add_two (a₀ b₀ : ι → ℂ)
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) (hn : 2 ≤ Fintype.card ι)
    (h : (spectralSupport a₀).card + (spectralSupport b₀).card ≤ Fintype.card ι + 2) :
    ∃ w : Equiv.Perm ι → ℝ, (∀ τ, 0 ≤ w τ) ∧ (∑ τ, w τ = 1) ∧
      ∀ a b : ι → ℂ, spectralSupport a ⊆ spectralSupport a₀ →
        spectralSupport b ⊆ spectralSupport b₀ →
          weightedMatchingValue a b w = determinantValue a b U := by
  classical
  let A := spectralSupport a₀
  let B := spectralSupport b₀
  let r := max A.card 2
  let s := Fintype.card ι + 2 - r
  have hA : A.card ≤ Fintype.card ι := Finset.card_le_univ A
  have hB : B.card ≤ Fintype.card ι := Finset.card_le_univ B
  have hr₁ : A.card ≤ r := le_max_left _ _
  have hr₂ : r ≤ Fintype.card ι := max_le hA hn
  have hr₀ : 2 ≤ r := le_max_right _ _
  have hrs : r + B.card ≤ Fintype.card ι + 2 := by
    by_cases hA₂ : A.card ≤ 2
    · change max A.card 2 + B.card ≤ _
      rw [max_eq_right hA₂]
      omega
    · change max A.card 2 + B.card ≤ _
      rw [max_eq_left (by omega : 2 ≤ A.card)]
      exact h
  have hs₁ : B.card ≤ s := by dsimp only [s]; omega
  have hs₂ : s ≤ Fintype.card ι := by dsimp only [s]; omega
  obtain ⟨P, hP, _, hPr⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_univ A) hr₁ (by simpa only [Finset.card_univ] using hr₂)
  obtain ⟨Q, hQ, _, hQs⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_univ B) hs₁ (by simpa only [Finset.card_univ] using hs₂)
  let a₁ (i : ι) : ℂ := if i ∈ P then 1 else 0
  let b₁ (j : ι) : ℂ := if j ∈ Q then 1 else 0
  have ha₁ : spectralSupport a₁ = P := by
    ext i
    by_cases hi : i ∈ P <;> simp [spectralSupport, a₁, hi]
  have hb₁ : spectralSupport b₁ = Q := by
    ext j
    by_cases hj : j ∈ Q <;> simp [spectralSupport, b₁, hj]
  have hcard : (spectralSupport a₁).card + (spectralSupport b₁).card = Fintype.card ι + 2 := by
    rw [ha₁, hb₁, hPr, hQs]
    dsimp only [s]
    omega
  obtain ⟨w, hw, hsum, he⟩ := exists_common_weights_of_support_excess_two a₁ b₁ U hU hcard
  refine ⟨w, hw, hsum, fun a b ha hb => common_weights_on_allowed_supports a₁ b₁ U w he a b ?_ ?_⟩
  · rw [ha₁]
    exact ha.trans hP
  · rw [hb₁]
    exact hb.trans hQ

/-- The reciprocal two-edge law gives scalar containment at excess two. -/
theorem holds_of_support_excess_two (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (h : (spectralSupport a).card + (spectralSupport b).card = Fintype.card ι + 2) : Holds a b U := by
  obtain ⟨w, hw, hs, he⟩ := exists_common_weights_of_support_excess_two a b U hU h
  exact holds_of_weights w hw hs (he a b (fun _ => Iff.rfl) (fun _ => Iff.rfl))

/-- Opposite scalar shifts preserve the rank-two-overlap reduction. -/
theorem holds_of_shifted_support_le_card_add_two (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) (t : ℂ)
    (h : (spectralSupport (fun i => a i + t)).card + (spectralSupport (fun i => b i - t)).card ≤
      Fintype.card ι + 2) : Holds a b U := by
  rcases lt_or_eq_of_le h with hlt | heq
  · exact holds_of_shifted_support_le_card_add_one a b U hU t (by omega)
  · exact (holds_shift_iff a b hU t).mp (holds_of_support_excess_two _ _ U hU heq)

/-- The fixed-support law also works before the two opposite scalar shifts. -/
theorem exists_common_weights_of_shifted_support_le_card_add_two
    (a₀ b₀ : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (hn : 2 ≤ Fintype.card ι) (t : ℂ)
    (h : (spectralSupport a₀).card + (spectralSupport b₀).card ≤ Fintype.card ι + 2) :
    ∃ w : Equiv.Perm ι → ℝ, (∀ τ, 0 ≤ w τ) ∧ (∑ τ, w τ = 1) ∧
      ∀ a b : ι → ℂ, spectralSupport (fun i => a i + t) ⊆ spectralSupport a₀ →
        spectralSupport (fun j => b j - t) ⊆ spectralSupport b₀ →
          weightedMatchingValue a b w = determinantValue a b U := by
  obtain ⟨w, hw, hs, he⟩ := exists_common_weights_of_support_le_card_add_two a₀ b₀ U hU hn h
  refine ⟨w, hw, hs, fun a b ha hb => ?_⟩
  have hshift := he (fun i => a i + t) (fun j => b j - t) ha hb
  rw [determinantValue_shift a b hU t] at hshift
  simpa only [weightedMatchingValue, matchingProduct_shift] using hshift

/-- The scalar rank-sum condition with a fixed relative eigenbasis. -/
theorem holds_of_shifted_rank_le_card_add_two (a b : ι → ℂ)
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) (t : ℂ)
    (h : (diagonal (fun i => a i + t)).rank +
      (U * diagonal (fun i => b i - t) * Uᴴ).rank ≤ Fintype.card ι + 2) : Holds a b U := by
  apply holds_of_shifted_support_le_card_add_two a b U hU t
  simpa only [← spectralSupport_card_eq_rank_diagonal,
    ← spectralSupport_card_eq_rank_conjugated_diagonal _ U hU] using h

end

end MOC
