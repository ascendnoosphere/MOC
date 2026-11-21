import MOC.Weights
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Analysis.MeanInequalities
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! Spectral support reductions for the shifted rank-sum theorem. -/

open BigOperators Matrix Finset
open scoped ComplexOrder Pointwise

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The labels of the nonzero entries of a spectrum. -/
def spectralSupport (a : ι → ℂ) : Finset ι :=
  univ.filter fun i => a i ≠ 0

omit [DecidableEq ι] in
theorem spectralSupport_card_comp (a : ι → ℂ) (σ : Equiv.Perm ι) :
    (spectralSupport (a ∘ σ)).card = (spectralSupport a).card := by
  have hs : (spectralSupport (a ∘ σ)).map σ.toEmbedding = spectralSupport a := by
    ext i
    simp only [spectralSupport, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Function.comp_apply, Equiv.toEmbedding_apply]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact hj
    · intro hi
      exact ⟨σ.symm i, by simpa using hi, σ.apply_symm_apply i⟩
  rw [← hs, Finset.card_map]

/-- An opposite pair of spectral entries makes zero a permutation vertex. -/
theorem zero_mem_matching_range (a b : ι → ℂ) {i j : ι} (hij : a i + b j = 0) :
    (0 : ℂ) ∈ Set.range (matchingProduct a b) := by
  refine ⟨Equiv.swap j i, ?_⟩
  unfold matchingProduct
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  simpa using hij

theorem holds_of_singular_of_opposite_entries (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (hd : determinantValue a b U = 0) {i j : ι} (hij : a i + b j = 0) : Holds a b U := by
  unfold Holds
  rw [hd]
  exact subset_convexHull ℝ _ (zero_mem_matching_range a b hij)

theorem matchingProduct_eq_zero_of_support_deficit (a b : ι → ℂ)
    (h : (spectralSupport a).card + (spectralSupport b).card < Fintype.card ι)
    (σ : Equiv.Perm ι) : matchingProduct a b σ = 0 := by
  have hc : (spectralSupport (a ∘ σ) ∪ spectralSupport b).card < Fintype.card ι :=
    lt_of_le_of_lt (Finset.card_union_le _ _) (by rwa [spectralSupport_card_comp])
  have hex : ∃ j : ι, j ∉ spectralSupport (a ∘ σ) ∪ spectralSupport b := by
    by_contra! hall
    have he : (spectralSupport (a ∘ σ) ∪ spectralSupport b) = univ :=
      Finset.eq_univ_of_forall hall
    rw [he, Finset.card_univ] at hc
    exact (lt_irrefl _) hc
  obtain ⟨j, hj⟩ := hex
  have hz : a (σ j) = 0 ∧ b j = 0 := by
    simpa [spectralSupport] using hj
  unfold matchingProduct
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  simp [hz.1, hz.2]

/-- In the strict-deficit case the entire determinant range and permutation hull collapse to zero. -/
theorem det_and_vertices_eq_zero_of_support_deficit (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U)
    (h : (spectralSupport a).card + (spectralSupport b).card < Fintype.card ι) :
    determinantValue a b U = 0 ∧ (∀ σ, matchingProduct a b σ = 0) := by
  have hz := matchingProduct_eq_zero_of_support_deficit a b h
  exact ⟨by rw [← signed_determinant a b U hU]; simp [hz], hz⟩

omit [DecidableEq ι] in
private def supportFlag (a : ι → ℂ) (i : ι) : ℂ := if a i = 0 then 0 else 1

omit [DecidableEq ι] in
private def nonzeroProduct (a : ι → ℂ) : ℂ := ∏ i, if a i = 0 then 1 else a i

private theorem balanced_vertex (a b : ι → ℂ)
    (h : (spectralSupport a).card + (spectralSupport b).card = Fintype.card ι)
    (σ : Equiv.Perm ι) :
    let r := matchingProduct (supportFlag a) (supportFlag b) σ
    (r = 0 ∨ r = 1) ∧ matchingProduct a b σ = (nonzeroProduct a * nonzeroProduct b) * r := by
  dsimp only
  by_cases hcov : spectralSupport (a ∘ σ) ∪ spectralSupport b = univ
  · have hc := card_union_add_card_inter (spectralSupport (a ∘ σ)) (spectralSupport b)
    rw [hcov, card_univ, spectralSupport_card_comp, h] at hc
    have hinter : spectralSupport (a ∘ σ) ∩ spectralSupport b = ∅ :=
      Finset.card_eq_zero.mp (by omega)
    have hsplit (j : ι) :
        (a (σ j) = 0 ∧ b j ≠ 0) ∨ (a (σ j) ≠ 0 ∧ b j = 0) := by
      by_cases ha : a (σ j) = 0
      · have hj : j ∈ spectralSupport (a ∘ σ) ∪ spectralSupport b := by rw [hcov]; exact mem_univ _
        exact Or.inl ⟨ha, by simpa [spectralSupport, ha] using hj⟩
      · have hj : j ∉ spectralSupport (a ∘ σ) ∩ spectralSupport b := by simp [hinter]
        exact Or.inr ⟨ha, by simpa [spectralSupport, ha] using hj⟩
    have hflag : matchingProduct (supportFlag a) (supportFlag b) σ = 1 := by
      unfold matchingProduct
      apply Finset.prod_eq_one
      intro j _
      rcases hsplit j with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> simp [supportFlag, ha, hb]
    refine ⟨Or.inr hflag, ?_⟩
    rw [hflag, mul_one]
    calc
      matchingProduct a b σ =
          ∏ j, ((if a (σ j) = 0 then 1 else a (σ j)) * (if b j = 0 then 1 else b j)) := by
        apply Finset.prod_congr rfl
        intro j _
        rcases hsplit j with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> simp [ha, hb]
      _ = nonzeroProduct a * nonzeroProduct b := by
        rw [Finset.prod_mul_distrib,
          Equiv.prod_comp σ (fun i => if a i = 0 then 1 else a i)]
        rfl
  · have hnot : ∃ j : ι, j ∉ spectralSupport (a ∘ σ) ∪ spectralSupport b := by
      by_contra! hall
      exact hcov (Finset.eq_univ_of_forall hall)
    obtain ⟨j, hj⟩ := hnot
    have hz : a (σ j) = 0 ∧ b j = 0 := by simpa [spectralSupport] using hj
    have hflag : matchingProduct (supportFlag a) (supportFlag b) σ = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      simp [supportFlag, hz.1, hz.2]
    refine ⟨Or.inl hflag, ?_⟩
    rw [hflag, mul_zero]
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp [hz.1, hz.2]

private theorem det_bounded_of_posSemidef_of_trace_card {M : Matrix ι ι ℂ}
    (hM : M.PosSemidef) (htrace : M.trace = Fintype.card ι) :
    ∃ q : ℝ, 0 ≤ q ∧ q ≤ 1 ∧ M.det = (q : ℂ) := by
  by_cases hι : Nonempty ι
  · letI := hι
    let eig := hM.1.eigenvalues
    have heig (i : ι) : 0 ≤ eig i := hM.eigenvalues_nonneg i
    have hsum : ∑ i, eig i = (Fintype.card ι : ℝ) := by
      apply Complex.ofReal_injective
      rw [Complex.ofReal_sum, Complex.ofReal_natCast, ← htrace]
      conv_rhs => rw [hM.1.spectral_theorem]
      rw [Matrix.trace_mul_cycle, unitary.coe_star_mul_self, Matrix.one_mul, Matrix.trace_diagonal]
      rfl
    have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
    have hql : 0 ≤ ∏ i, eig i := Finset.prod_nonneg (fun i _ => heig i)
    refine ⟨∏ i, eig i, hql, ?_, ?_⟩
    · have hgm := Real.geom_mean_le_arith_mean (Finset.univ : Finset ι)
        (fun _ => (1 : ℝ)) eig (by simp) (by simpa using hn) (fun i _ => heig i)
      have hpow : (∏ i, eig i) ^ (Fintype.card ι : ℝ)⁻¹ ≤ 1 := by
        simpa [hsum, div_self hn.ne'] using hgm
      exact (Real.rpow_le_rpow_iff hql zero_le_one (inv_pos.mpr hn)).mp
        (by simpa [Real.one_rpow] using hpow)
    · rw [hM.1.det_eq_prod_eigenvalues, Complex.ofReal_prod]
      rfl
  · haveI : IsEmpty ι := not_nonempty_iff.mp hι
    exact ⟨1, zero_le_one, le_rfl, by simp⟩

/-- When the two supports have total size equal to the order, the normalization
by the product of their nonzero entries reduces to a positive contraction in the hull. -/
theorem holds_of_support_balance (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (h : (spectralSupport a).card + (spectralSupport b).card = Fintype.card ι) : Holds a b U := by
  let D := nonzeroProduct a * nonzeroProduct b
  have hclass (σ : Equiv.Perm ι) : matchingProduct a b σ = 0 ∨ matchingProduct a b σ = D := by
    obtain ⟨hz | hz, hd⟩ := balanced_vertex a b h σ
    · exact Or.inl (by rw [hd, hz, mul_zero])
    · exact Or.inr (by rw [hd, hz, mul_one])
  by_cases hconst : ∀ σ, matchingProduct a b σ = matchingProduct a b (Equiv.refl ι)
  · have hdet : determinantValue a b U = matchingProduct a b (Equiv.refl ι) := by
      rw [← signed_determinant a b U hU]
      simp only [hconst, ← Finset.sum_mul, sum_signedWeight U (det_ne_zero_of_unitary hU), one_mul]
    unfold Holds
    rw [hdet]
    exact matchingProduct_mem_hull _ _ _
  · obtain ⟨σ, hσ⟩ := not_forall.mp hconst
    have hboth : (0 : ℂ) ∈ Set.range (matchingProduct a b) ∧
        D ∈ Set.range (matchingProduct a b) := by
      rcases hclass σ with hs | hs <;> rcases hclass (Equiv.refl ι) with h0 | h0
      · exact (hσ (hs.trans h0.symm)).elim
      · exact ⟨⟨σ, hs⟩, ⟨_, h0⟩⟩
      · exact ⟨⟨_, h0⟩, ⟨σ, hs⟩⟩
      · exact (hσ (hs.trans h0.symm)).elim
    let M := diagonal (supportFlag a) + U * diagonal (supportFlag b) * Uᴴ
    have hpos (c : ι → ℂ) : (diagonal (supportFlag c)).PosSemidef := by
      apply Matrix.PosSemidef.diagonal
      intro i
      rcases eq_or_ne (c i) 0 with hi | hi <;> simp [supportFlag, hi]
    have hM : M.PosSemidef := (hpos a).add ((hpos b).mul_mul_conjTranspose_same U)
    have htrace : M.trace = Fintype.card ι := by
      have hflag (c : ι → ℂ) : ∑ i, supportFlag c i = ((spectralSupport c).card : ℂ) := by
        unfold spectralSupport supportFlag
        simpa only [ite_not] using (Finset.sum_boole (fun i => c i ≠ 0) (univ : Finset ι))
      dsimp [M]
      rw [Matrix.trace_add, Matrix.trace_mul_cycle, hU.2, Matrix.one_mul,
        Matrix.trace_diagonal, Matrix.trace_diagonal, hflag, hflag, ← Nat.cast_add, h]
    obtain ⟨q, hq0, hq1, hq⟩ := det_bounded_of_posSemidef_of_trace_card hM htrace
    have hdet : determinantValue a b U = (q : ℂ) * D := calc
      determinantValue a b U = ∑ σ, signedWeight U σ * matchingProduct a b σ :=
        (signed_determinant a b U hU).symm
      _ = D * determinantValue (supportFlag a) (supportFlag b) U := by
        rw [← signed_determinant (supportFlag a) (supportFlag b) U hU, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro τ _
        rw [(balanced_vertex a b h τ).2]
        dsimp [D]
        ring
      _ = _ := by
        change D * M.det = _
        rw [hq, mul_comm]
    have hconv := (convex_convexHull ℝ (Set.range (matchingProduct a b)))
      (subset_convexHull ℝ _ hboth.1) (subset_convexHull ℝ _ hboth.2)
      (sub_nonneg.mpr hq1) hq0 (sub_add_cancel 1 q)
    simpa [Holds, hdet, Complex.real_smul] using hconv

/-- The shifted rank-sum case through total support size equal to the order. -/
theorem holds_of_shifted_support_le_card (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) (t : ℂ)
    (h : (spectralSupport (fun i => a i + t)).card +
      (spectralSupport (fun i => b i - t)).card ≤ Fintype.card ι) :
    Holds a b U := by
  apply (holds_shift_iff a b hU t).mp
  rcases lt_or_eq_of_le h with h | h
  · obtain ⟨hd, hz⟩ :=
      det_and_vertices_eq_zero_of_support_deficit (fun i => a i + t) (fun i => b i - t) U hU h
    unfold Holds
    rw [hd, ← hz (Equiv.refl ι)]
    exact matchingProduct_mem_hull _ _ _
  · exact holds_of_support_balance _ _ U hU h

theorem spectralSupport_card_eq_rank_diagonal (a : ι → ℂ) :
    (spectralSupport a).card = (diagonal a).rank := by
  rw [Matrix.rank_diagonal]
  exact (Fintype.card_of_subtype _ (by simp [spectralSupport])).symm

theorem spectralSupport_card_eq_rank_conjugated_diagonal (a : ι → ℂ) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) : (spectralSupport a).card = (U * diagonal a * Uᴴ).rank := by
  have hU' : IsUnitary Uᴴ := ⟨by simpa using hU.2, by simpa using hU.1⟩
  rw [Matrix.rank_mul_eq_left_of_isUnit_det Uᴴ _
      (isUnit_iff_ne_zero.mpr (det_ne_zero_of_unitary hU')),
    Matrix.rank_mul_eq_right_of_isUnit_det U _
      (isUnit_iff_ne_zero.mpr (det_ne_zero_of_unitary hU)), spectralSupport_card_eq_rank_diagonal]

/-- The matrix rank form of the shifted support theorem. -/
theorem holds_of_shifted_rank_le_card (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (t : ℂ)
    (h : (diagonal (fun i => a i + t)).rank +
      (U * diagonal (fun i => b i - t) * Uᴴ).rank ≤ Fintype.card ι) : Holds a b U := by
  apply holds_of_shifted_support_le_card a b U hU t
  simpa only [← spectralSupport_card_eq_rank_diagonal,
    ← spectralSupport_card_eq_rank_conjugated_diagonal _ U hU] using h

/-- Jacobi's identity for complementary principal blocks, including a singular
upper-left block. -/
theorem det_principal_eq_mul_det_inverse_complement {κ : Type*} [Fintype κ] [DecidableEq κ]
    (M N : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ) (hMN : M * N = 1) :
    M.toBlocks₁₁.det = M.det * N.toBlocks₂₂.det := by
  have hprod := hMN
  rw [← Matrix.fromBlocks_toBlocks M, ← Matrix.fromBlocks_toBlocks N, Matrix.fromBlocks_multiply,
    ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj] at hprod
  have htri : M * Matrix.fromBlocks (1 : Matrix ι ι ℂ) N.toBlocks₁₂ 0 N.toBlocks₂₂ =
      Matrix.fromBlocks M.toBlocks₁₁ 0 M.toBlocks₂₁ (1 : Matrix κ κ ℂ) := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks M]
    simp [Matrix.fromBlocks_multiply, hprod.2.1, hprod.2.2.2]
  simpa [Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₁₂] using
    (congrArg Matrix.det htri).symm

/-- The determinant compression in equation (3) of the rank-sum proof.
The bottom rows of `W` are orthonormal and perpendicular to its top rows.
The upper Gram block `G` supplies the determinant factor. -/
theorem det_compress_of_orthogonal_row_blocks {κ : Type*} [Fintype κ] [DecidableEq κ]
    (W L Linv : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ) (G : Matrix ι ι ℂ)
    (hGram : W * Wᴴ = Matrix.fromBlocks G 0 0 (1 : Matrix κ κ ℂ))
    (hG : IsUnit G.det) (hL : L * Linv = 1) :
    (W * L * Wᴴ).toBlocks₁₁.det = L.det * G.det * (W * Linv * Wᴴ).toBlocks₂₂.det := by
  let R := Matrix.fromBlocks G⁻¹ 0 0 (1 : Matrix κ κ ℂ)
  have hright : W * Wᴴ * R = 1 := by
    rw [hGram]
    simp [R, Matrix.fromBlocks_multiply, Matrix.mul_nonsing_inv _ hG, Matrix.fromBlocks_one]
  have hleft : (Wᴴ * R) * W = 1 := Matrix.mul_eq_one_comm.mp (by
    rwa [← Matrix.mul_assoc])
  have hprod : (W * L * Wᴴ) * (R * (W * Linv * Wᴴ) * R) = 1 := calc
    _ = W * L * ((Wᴴ * R) * W) * Linv * Wᴴ * R := by simp only [Matrix.mul_assoc]
    _ = W * Wᴴ * R := by rw [hleft, Matrix.mul_one, Matrix.mul_assoc W L Linv, hL, Matrix.mul_one]
    _ = 1 := hright
  have hblock : (R * (W * Linv * Wᴴ) * R).toBlocks₂₂ = (W * Linv * Wᴴ).toBlocks₂₂ := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks (W * Linv * Wᴴ)]
    simp [R, Matrix.fromBlocks_multiply]
  have hdet : (W * L * Wᴴ).det = L.det * G.det := calc
    _ = L.det * (W * Wᴴ).det := by simp only [Matrix.det_mul]; ring
    _ = _ := by rw [hGram, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]
  rw [det_principal_eq_mul_det_inverse_complement _ _ hprod, hblock, hdet]

private theorem det_between_zero_and_one_of_posSemidef {M : Matrix ι ι ℂ}
    (hM : M.PosSemidef) (hI : (1 - M).PosSemidef) :
    ∃ q : ℝ, 0 ≤ q ∧ q ≤ 1 ∧ M.det = (q : ℂ) := by
  let eig := hM.isHermitian.eigenvalues
  have hnonneg (i : ι) : 0 ≤ eig i := hM.eigenvalues_nonneg i
  have hle (i : ι) : eig i ≤ 1 := by
    let x := hM.isHermitian.eigenvectorBasis i
    have heig : ((star (⇑x)) ⬝ᵥ (M *ᵥ ⇑x)).re = eig i :=
      (hM.isHermitian.eigenvalues_eq i).symm
    have hnorm : ((star (⇑x)) ⬝ᵥ ⇑x).re = 1 := by
      rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K,
        show ‖x‖ = 1 from (hM.isHermitian.eigenvectorBasis).orthonormal.1 i]
      norm_num
    have hx := hI.re_dotProduct_nonneg (⇑x)
    change 0 ≤ ((star (⇑x)) ⬝ᵥ ((1 - M) *ᵥ ⇑x)).re at hx
    rwa [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, Complex.sub_re, heig, hnorm,
      sub_nonneg] at hx
  refine ⟨∏ i, eig i, Finset.prod_nonneg (fun i _ => hnonneg i), ?_, ?_⟩
  · simpa using Finset.prod_le_prod (fun i _ => hnonneg i) (fun i _ => hle i)
  · rw [hM.isHermitian.det_eq_prod_eigenvalues, Complex.ofReal_prod]
    rfl

/-- A permutation covers the spectral supports if every pair contains a nonzero entry. -/
abbrev CoversSupports (a b : ι → ℂ) (σ : Equiv.Perm ι) : Prop :=
  ∀ j, a (σ j) ≠ 0 ∨ b j ≠ 0

/-- The signed mass of permutations covering the supports is a real contraction.
It is the determinant of the compression of the second spectral projection
to the rows outside the first support. -/
theorem signed_cover_mass_le_one (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U) :
    ∃ q : ℝ, 0 ≤ q ∧ q ≤ 1 ∧
      (∑ σ, if CoversSupports a b σ then signedWeight U σ else 0) = (q : ℂ) := by
  let M : Matrix ι ι ℂ := Matrix.of fun i j => if a i ≠ 0 ∨ b j ≠ 0 then U i j else 0
  let Q := U * diagonal (supportFlag b) * Uᴴ
  have hnz := det_ne_zero_of_unitary hU
  have hleib : M.det =
      ∑ σ, if CoversSupports a b σ then leibnizTerm U σ else 0 := by
    rw [Matrix.det_apply']
    apply Finset.sum_congr rfl
    intro σ _
    by_cases hσ : CoversSupports a b σ
    · rw [if_pos hσ]
      unfold leibnizTerm
      congr 1
      exact Finset.prod_congr rfl (fun j _ => if_pos (hσ j))
    · rw [if_neg hσ]
      obtain ⟨j, hj⟩ := not_forall.mp (show ¬ ∀ j, a (σ j) ≠ 0 ∨ b j ≠ 0 from hσ)
      have hzero : ∏ k, M (σ k) k = 0 := Finset.prod_eq_zero (mem_univ j) (if_neg hj)
      rw [hzero, mul_zero]
  have hsum : (∑ σ, if CoversSupports a b σ then signedWeight U σ else 0) = M.det / U.det := by
    rw [hleib, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro σ _
    by_cases hσ : CoversSupports a b σ
    · rw [if_pos hσ, if_pos hσ, signedWeight]
    · simp only [if_neg hσ, zero_div]
  have hdet : M.det / U.det = (M * Uᴴ).det := by
    symm
    apply (eq_div_iff hnz).mpr
    rw [← Matrix.det_mul, Matrix.mul_assoc, hU.2, Matrix.mul_one]
  let c : ι → ℂ := fun i => if a i = 0 then 1 else 0
  have hmat : M = diagonal (supportFlag a) * U + diagonal c * U * diagonal (supportFlag b) := by
    ext i j
    by_cases ha : a i = 0 <;> by_cases hb : b j = 0 <;>
      simp [M, Q, c, Matrix.diagonal_mul, Matrix.mul_diagonal, supportFlag, ha, hb]
  have hmul : M * Uᴴ = diagonal (supportFlag a) + diagonal c * Q := by
    rw [hmat, Matrix.add_mul, Matrix.mul_assoc (diagonal (supportFlag a)), hU.1, Matrix.mul_one]
    simp only [Q, Matrix.mul_assoc]
  have hpoint (i j : ι) : (M * Uᴴ) i j =
      if a i = 0 then Q i j else (1 : Matrix ι ι ℂ) i j := by
    rw [hmul]
    by_cases ha : a i = 0 <;> simp [c, supportFlag, Matrix.diagonal_mul, Matrix.diagonal_apply,
      Matrix.one_apply, ha]
  let e := Equiv.sumCompl (fun i : ι => a i ≠ 0)
  let N := (M * Uᴴ).submatrix e e
  let e₀ : {i // ¬ a i ≠ 0} → ι := Subtype.val
  let X := Q.submatrix e₀ e₀
  have hN11 : N.toBlocks₁₁ = 1 := by
    ext i j
    change (M * Uᴴ) i.val j.val = (1 : Matrix {i // a i ≠ 0} {i // a i ≠ 0} ℂ) i j
    simp [hpoint, i.property, Matrix.one_apply, Subtype.ext_iff]
  have hN12 : N.toBlocks₁₂ = 0 := by
    ext i j
    change (M * Uᴴ) i.val j.val = 0
    have hij : i.val ≠ j.val := fun h => j.property (h ▸ i.property)
    simp [hpoint, i.property, Matrix.one_apply, hij]
  have hN22 : N.toBlocks₂₂ = X := by
    ext i j
    change (M * Uᴴ) i.val j.val = Q i.val j.val
    simp [hpoint, not_ne_iff.mp i.property]
  have heq : (M * Uᴴ).det = X.det := by
    rw [← Matrix.det_submatrix_equiv_self e (M * Uᴴ)]
    change N.det = X.det
    rw [← Matrix.fromBlocks_toBlocks N, hN11, hN12, hN22, Matrix.det_fromBlocks_zero₁₂,
      Matrix.det_one, one_mul]
  have hQ : Q.PosSemidef := by
    apply Matrix.PosSemidef.mul_mul_conjTranspose_same
    apply Matrix.PosSemidef.diagonal
    intro i
    by_cases hi : b i = 0 <;> simp [supportFlag, hi]
  have hQc : (1 - Q).PosSemidef := by
    have hQcEq : 1 - Q = U * diagonal (fun i => 1 - supportFlag b i) * Uᴴ := by
      have hone : diagonal (fun _ : ι => (1 : ℂ)) = 1 := Matrix.diagonal_one
      rw [← Matrix.diagonal_sub, hone, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hU.1]
    rw [hQcEq]
    apply Matrix.PosSemidef.mul_mul_conjTranspose_same
    apply Matrix.PosSemidef.diagonal
    intro i
    by_cases hi : b i = 0 <;> simp [supportFlag, hi]
  have hX : X.PosSemidef := hQ.submatrix _
  have hXc : (1 - X).PosSemidef := by
    have hp := hQc.submatrix (Subtype.val : {i // ¬ a i ≠ 0} → ι)
    simp only [Matrix.submatrix_sub, Pi.sub_apply, Matrix.submatrix_one _ Subtype.val_injective] at hp
    exact hp
  rw [hsum, hdet, heq]
  exact det_between_zero_and_one_of_posSemidef hX hXc

omit [DecidableEq ι] in
private theorem matchingProduct_eq_zero_of_not_covers (a b : ι → ℂ) (σ : Equiv.Perm ι)
    (hσ : ¬ CoversSupports a b σ) : matchingProduct a b σ = 0 := by
  obtain ⟨j, hj⟩ := not_forall.mp hσ
  have hzero : a (σ j) = 0 ∧ b j = 0 := by simpa using hj
  unfold matchingProduct
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  simp [hzero.1, hzero.2]

/-- Coverage fixes the number of pairs joining two nonzero entries. -/
theorem cover_overlap_card (a b : ι → ℂ) (σ : Equiv.Perm ι) (hσ : CoversSupports a b σ) :
    (spectralSupport (a ∘ σ) ∩ spectralSupport b).card =
      (spectralSupport a).card + (spectralSupport b).card - Fintype.card ι := by
  have hu : spectralSupport (a ∘ σ) ∪ spectralSupport b = univ :=
    Finset.eq_univ_of_forall fun j => by simpa [spectralSupport] using hσ j
  have hh := Finset.card_union_add_card_inter (spectralSupport (a ∘ σ)) (spectralSupport b)
  rw [hu, Finset.card_univ, spectralSupport_card_comp] at hh
  omega

omit [Fintype ι] in
private theorem covers_update_left_iff (a b : ι → ℂ) (σ : Equiv.Perm ι) (i : ι) :
    CoversSupports (Function.update a i 0) b σ ↔ CoversSupports a b σ ∧ b (σ.symm i) ≠ 0 := by
  constructor
  · intro h
    refine ⟨fun j => ?_, ?_⟩
    · by_cases hj : σ j = i
      · exact Or.inr (by simpa [Function.update, hj] using h j)
      · simpa [Function.update, hj] using h j
    · have hi : Function.update a i 0 (σ (σ.symm i)) ≠ 0 ∨ b (σ.symm i) ≠ 0 :=
        h (σ.symm i)
      rw [σ.apply_symm_apply, Function.update_self] at hi
      exact hi.resolve_left (not_ne_iff.mpr rfl)
  · rintro ⟨h, hi⟩ j
    by_cases hj : σ j = i
    · have hj' : σ.symm i = j := by rw [← hj, σ.symm_apply_apply]
      exact Or.inr (hj' ▸ hi)
    · simpa [Function.update, hj] using h j

omit [Fintype ι] in
private theorem covers_update_right_iff (a b : ι → ℂ) (σ : Equiv.Perm ι) (j : ι) :
    CoversSupports a (Function.update b j 0) σ ↔ CoversSupports a b σ ∧ a (σ j) ≠ 0 := by
  constructor
  · intro h
    refine ⟨fun k => ?_, by simpa using h j⟩
    by_cases hk : k = j
    · exact Or.inl (by simpa [Function.update, hk] using h k)
    · simpa [Function.update, hk] using h k
  · rintro ⟨h, hj⟩ k
    by_cases hk : k = j
    · exact Or.inl (hk.symm ▸ hj)
    · simpa [Function.update, hk] using h k

private theorem overlap_one (a b : ι → ℂ) (σ : Equiv.Perm ι) (hσ : CoversSupports a b σ)
    (h : (spectralSupport a).card + (spectralSupport b).card = Fintype.card ι + 1) :
    ∃ j, a (σ j) ≠ 0 ∧ b j ≠ 0 ∧ (∀ k, a (σ k) ≠ 0 → b k ≠ 0 → k = j) := by
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp (by rw [cover_overlap_card a b σ hσ, h]; omega)
  have hjm : j ∈ spectralSupport (a ∘ σ) ∩ spectralSupport b := by rw [hj]; simp
  have hjnz : a (σ j) ≠ 0 ∧ b j ≠ 0 := by simpa [spectralSupport] using hjm
  refine ⟨j, hjnz.1, hjnz.2, fun k ha hb => ?_⟩
  have hkm : k ∈ spectralSupport (a ∘ σ) ∩ spectralSupport b := by
    simp [spectralSupport, ha, hb]
  simpa [hj] using hkm

private theorem matchingProduct_overlap_one (a b : ι → ℂ) (σ : Equiv.Perm ι)
    (hσ : CoversSupports a b σ) (j : ι) (ha : a (σ j) ≠ 0) (hb : b j ≠ 0)
    (hu : ∀ k, a (σ k) ≠ 0 → b k ≠ 0 → k = j) :
    matchingProduct a b σ =
      (nonzeroProduct a * nonzeroProduct b) * ((a (σ j))⁻¹ + (b j)⁻¹) := by
  let f : ι → ℂ := fun k =>
    (if a (σ k) = 0 then 1 else a (σ k)) * (if b k = 0 then 1 else b k)
  have hall : ∏ k, f k = nonzeroProduct a * nonzeroProduct b := by
    dsimp [f, nonzeroProduct]
    rw [Finset.prod_mul_distrib, Equiv.prod_comp σ (fun i => if a i = 0 then 1 else a i)]
  have hnorm : nonzeroProduct a * nonzeroProduct b =
      a (σ j) * b j * ∏ k ∈ univ.erase j, f k := by
    rw [← hall, ← Finset.mul_prod_erase _ _ (mem_univ j)]
    simp [f, ha, hb]
  have hv : a (σ j) + b j = a (σ j) * b j * ((a (σ j))⁻¹ + (b j)⁻¹) := by
    field_simp
    ring
  unfold matchingProduct
  rw [← Finset.mul_prod_erase _ _ (mem_univ j), hnorm]
  have he : ∏ k ∈ univ.erase j, (a (σ k) + b k) = ∏ k ∈ univ.erase j, f k := by
    apply Finset.prod_congr rfl
    intro k hk
    rcases hσ k with ha' | hb'
    · have hb' : b k = 0 := by
        by_contra hn
        exact (Finset.mem_erase.mp hk).1 (hu k ha' hn)
      simp [f, ha', hb']
    · have ha' : a (σ k) = 0 := by
        by_contra hn
        exact (Finset.mem_erase.mp hk).1 (hu k hn hb')
      simp [f, ha', hb']
  rw [he, hv]
  ring

private theorem exists_cover_with_overlap_one (a b : ι → ℂ)
    (h : (spectralSupport a).card + (spectralSupport b).card = Fintype.card ι + 1)
    {i j : ι} (hi : i ∈ spectralSupport a) (hj : j ∈ spectralSupport b) :
    ∃ σ, CoversSupports a b σ ∧ σ j = i := by
  let A := (spectralSupport a).erase i
  let B := spectralSupport b
  have hcard : A.card + B.card = Fintype.card ι := by
    have hpos := Finset.card_pos.mpr ⟨i, hi⟩
    dsimp [A, B]
    rw [Finset.card_erase_of_mem hi]
    omega
  have hc (s : Finset ι) : Fintype.card {x // x ∉ s} = Fintype.card ι - s.card := by
    rw [Fintype.card_of_subtype (sᶜ) (by simp), Finset.card_compl]
  let f : B ≃ {x // x ∉ A} := Fintype.equivOfCardEq (by rw [Fintype.card_coe, hc]; omega)
  let g : {x // x ∉ B} ≃ A := Fintype.equivOfCardEq (by rw [Fintype.card_coe, hc]; omega)
  let jj : B := ⟨j, hj⟩
  let ii : {x // x ∉ A} := ⟨i, Finset.not_mem_erase i _⟩
  let f' := f.trans (Equiv.swap (f jj) ii)
  let eA := Equiv.sumCompl (fun x => x ∈ A)
  let eB := Equiv.sumCompl (fun x => x ∈ B)
  let σ := eB.symm.trans ((Equiv.sumCongr f' g).trans ((Equiv.sumComm _ _).trans eA))
  have hf (x : B) : σ x = f' x := by
    change σ (eB (Sum.inl x)) = _
    simp only [σ, Equiv.trans_apply, Equiv.symm_apply_apply]
    rfl
  have hg (x : {x // x ∉ B}) : σ x = g x := by
    change σ (eB (Sum.inr x)) = _
    simp only [σ, Equiv.trans_apply, Equiv.symm_apply_apply]
    rfl
  refine ⟨σ, fun k => ?_, ?_⟩
  · by_cases hk : k ∈ B
    · exact Or.inr (by simpa [B, spectralSupport] using hk)
    · have hk' : σ k ∈ A := by
        rw [hg ⟨k, hk⟩]
        exact (g ⟨k, hk⟩).property
      exact Or.inl (by simpa [spectralSupport] using
        (Finset.mem_of_mem_erase hk' : σ k ∈ spectralSupport a))
  · calc
      σ j = f' jj := hf jj
      _ = i := by simp [f', ii]

private theorem excess_one_pointwise (a b : ι → ℂ)
    (h : (spectralSupport a).card + (spectralSupport b).card = Fintype.card ι + 1)
    (σ : Equiv.Perm ι) (w : ℂ) :
    let left (f : ι → ℂ) := ∑ i ∈ spectralSupport a,
      if CoversSupports (Function.update a i 0) b σ then f i else 0
    let right (f : ι → ℂ) := ∑ j ∈ spectralSupport b,
      if CoversSupports a (Function.update b j 0) σ then f j else 0
    left (fun _ => w) = (if CoversSupports a b σ then w else 0) ∧
    right (fun _ => w) = (if CoversSupports a b σ then w else 0) ∧
    w * matchingProduct a b σ = (nonzeroProduct a * nonzeroProduct b) *
      (left (fun i => w * (a i)⁻¹) + right (fun j => w * (b j)⁻¹)) := by
  dsimp only
  by_cases hcov : CoversSupports a b σ
  · obtain ⟨j, haj, hbj, huniq⟩ := overlap_one a b σ hcov h
    have hl (f : ι → ℂ) :
        (∑ i ∈ spectralSupport a,
          if CoversSupports (Function.update a i 0) b σ then f i else 0) = f (σ j) := by
      have hm : σ j ∈ spectralSupport a := by simpa [spectralSupport]
      rw [Finset.sum_eq_single_of_mem (σ j) hm]
      · rw [if_pos]
        exact (covers_update_left_iff a b σ (σ j)).mpr ⟨hcov, by simpa only [σ.symm_apply_apply]⟩
      · intro i hi hne
        rw [if_neg]
        intro hdel
        have hai : a (σ (σ.symm i)) ≠ 0 := by simpa [spectralSupport, σ.apply_symm_apply] using hi
        have hbi := ((covers_update_left_iff a b σ i).mp hdel).2
        exact hne (by simpa only [σ.apply_symm_apply] using congrArg σ (huniq _ hai hbi))
    have hr (f : ι → ℂ) :
        (∑ k ∈ spectralSupport b,
          if CoversSupports a (Function.update b k 0) σ then f k else 0) = f j := by
      have hm : j ∈ spectralSupport b := by simpa [spectralSupport]
      rw [Finset.sum_eq_single_of_mem j hm]
      · rw [if_pos ((covers_update_right_iff a b σ j).mpr ⟨hcov, haj⟩)]
      · intro k hk hne
        rw [if_neg]
        intro hdel
        have hak := ((covers_update_right_iff a b σ k).mp hdel).2
        exact hne (huniq _ hak (by simpa [spectralSupport] using hk))
    simp only [hl, hr, if_pos hcov, true_and, matchingProduct_overlap_one a b σ hcov j haj hbj huniq]
    ring
  · simp only [covers_update_left_iff, covers_update_right_iff, hcov, false_and, if_false,
      Finset.sum_const_zero, matchingProduct_eq_zero_of_not_covers a b σ hcov, mul_zero, add_zero,
      and_self]

/-- With one excess nonzero entry, the covering coefficients are two nonnegative
marginals of equal total mass. Their reciprocal averages give the determinant. -/
theorem holds_of_support_excess_one (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (h : (spectralSupport a).card + (spectralSupport b).card = Fintype.card ι + 1) : Holds a b U := by
  choose α hα₀ hα₁ hα using
    fun i : ι => signed_cover_mass_le_one (Function.update a i 0) b U hU
  choose β hβ₀ hβ₁ hβ using
    fun j : ι => signed_cover_mass_le_one a (Function.update b j 0) U hU
  obtain ⟨q, hq₀, hq₁, hq⟩ := signed_cover_mass_le_one a b U hU
  have hαsum : ∑ i ∈ spectralSupport a, α i = q := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_sum, ← hq]
    simp_rw [← hα]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun σ _ => (excess_one_pointwise a b h σ (signedWeight U σ)).1)
  have hβsum : ∑ j ∈ spectralSupport b, β j = q := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_sum, ← hq]
    simp_rw [← hβ]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun σ _ => (excess_one_pointwise a b h σ (signedWeight U σ)).2.1)
  let D := nonzeroProduct a * nonzeroProduct b
  have hvalue : determinantValue a b U = D *
      ((∑ i ∈ spectralSupport a, (α i : ℂ) * (a i)⁻¹) +
      ∑ j ∈ spectralSupport b, (β j : ℂ) * (b j)⁻¹) := by
    rw [← signed_determinant a b U hU]
    simp_rw [← hα, ← hβ, Finset.sum_mul, ite_mul, zero_mul]
    rw [Finset.sum_comm (s := spectralSupport a), Finset.sum_comm (s := spectralSupport b),
      ← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun σ _ => (excess_one_pointwise a b h σ (signedWeight U σ)).2.2)
  have hq_or_zero : q = 1 ∨ (0 : ℂ) ∈ Set.range (matchingProduct a b) := by
    by_cases hz : (0 : ℂ) ∈ Set.range (matchingProduct a b)
    · exact Or.inr hz
    left
    have hcov (σ : Equiv.Perm ι) : CoversSupports a b σ := by
      by_contra hn
      exact hz ⟨σ, matchingProduct_eq_zero_of_not_covers a b σ hn⟩
    apply Complex.ofReal_injective
    rw [Complex.ofReal_one, ← hq]
    calc
      _ = ∑ σ, signedWeight U σ := Finset.sum_congr rfl (fun σ _ => if_pos (hcov σ))
      _ = 1 := sum_signedWeight U (det_ne_zero_of_unitary hU)
  rcases eq_or_lt_of_le hq₀ with hqz | hqpos
  · have hA := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hα₀ i)).mp (hαsum.trans hqz.symm)
    have hB := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hβ₀ j)).mp (hβsum.trans hqz.symm)
    have hz : (0 : ℂ) ∈ Set.range (matchingProduct a b) :=
      hq_or_zero.resolve_left (by rw [← hqz]; exact zero_ne_one)
    have ha0 : ∑ i ∈ spectralSupport a, (α i : ℂ) * (a i)⁻¹ = 0 :=
      Finset.sum_eq_zero fun i hi => by simp [hA i hi]
    have hb0 : ∑ j ∈ spectralSupport b, (β j : ℂ) * (b j)⁻¹ = 0 :=
      Finset.sum_eq_zero fun j hj => by simp [hB j hj]
    unfold Holds
    rw [hvalue, ha0, hb0, add_zero, mul_zero]
    exact subset_convexHull ℝ _ hz
  · let L := (spectralSupport a).centerMass α (fun i => (a i)⁻¹)
    let R := (spectralSupport b).centerMass β (fun j => (b j)⁻¹)
    let S : Set ℂ := (fun i => (a i)⁻¹) '' (↑(spectralSupport a) : Set ι)
    let T : Set ℂ := (fun j => (b j)⁻¹) '' (↑(spectralSupport b) : Set ι)
    let K := convexHull ℝ (Set.range (matchingProduct a b))
    have hL : L ∈ convexHull ℝ S :=
      (spectralSupport a).centerMass_mem_convexHull (fun i _ => hα₀ i) (by rwa [hαsum])
        (fun i hi => ⟨i, hi, rfl⟩)
    have hR : R ∈ convexHull ℝ T :=
      (spectralSupport b).centerMass_mem_convexHull (fun j _ => hβ₀ j) (by rwa [hβsum])
        (fun j hj => ⟨j, hj, rfl⟩)
    have hLR : L + R ∈ convexHull ℝ (S + T) := by
      rw [convexHull_add]
      exact Set.add_mem_add hL hR
    have htarget : D * (L + R) ∈ K := by
      change L + R ∈ (LinearMap.mulLeft ℝ D) ⁻¹' K
      apply convexHull_min _ ((convex_convexHull ℝ _).linear_preimage (LinearMap.mulLeft ℝ D)) hLR
      intro z hz
      obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_add.mp hz
      obtain ⟨i, hi, rfl⟩ := hx
      obtain ⟨j, hj, rfl⟩ := hy
      obtain ⟨σ, hcov, hσ⟩ := exists_cover_with_overlap_one a b h hi hj
      obtain ⟨k, hak, hbk, hu⟩ := overlap_one a b σ hcov h
      have ha : a (σ j) ≠ 0 := by rw [hσ]; simpa [spectralSupport] using hi
      have hb : b j ≠ 0 := by simpa [spectralSupport] using hj
      have heq := hu j ha hb
      subst k
      have hprod := matchingProduct_overlap_one a b σ hcov j ha hb hu
      rw [hσ] at hprod
      exact subset_convexHull ℝ _ ⟨σ, hprod⟩
    have hscaled : determinantValue a b U = q • (D * (L + R)) := by
      rw [hvalue]
      simp only [L, R, Finset.centerMass, hαsum, hβsum, Complex.real_smul, Complex.ofReal_inv]
      field_simp [Complex.ofReal_ne_zero.mpr hqpos.ne']
    unfold Holds
    rw [hscaled]
    rcases hq_or_zero with hqeq | hz
    · simpa [hqeq] using htarget
    · have hc := (convex_convexHull ℝ (Set.range (matchingProduct a b)))
        (subset_convexHull ℝ _ hz) htarget (sub_nonneg.mpr hq₁) hq₀ (sub_add_cancel 1 q)
      simpa using hc

/-- The shifted rank-sum case through total support size one above the order. -/
theorem holds_of_shifted_support_le_card_add_one (a b : ι → ℂ)
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) (t : ℂ)
    (h : (spectralSupport (fun i => a i + t)).card +
      (spectralSupport (fun i => b i - t)).card ≤ Fintype.card ι + 1) : Holds a b U := by
  rcases lt_or_eq_of_le h with h | h
  · exact holds_of_shifted_support_le_card a b U hU t (Nat.lt_succ_iff.mp h)
  · exact (holds_shift_iff a b hU t).mp (holds_of_support_excess_one _ _ U hU h)

/-- The shifted rank-sum bound through one above the order, in matrix rank form. -/
theorem holds_of_shifted_rank_le_card_add_one (a b : ι → ℂ)
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) (t : ℂ)
    (h : (diagonal (fun i => a i + t)).rank +
      (U * diagonal (fun i => b i - t) * Uᴴ).rank ≤ Fintype.card ι + 1) : Holds a b U := by
  apply holds_of_shifted_support_le_card_add_one a b U hU t
  simpa only [← spectralSupport_card_eq_rank_diagonal,
    ← spectralSupport_card_eq_rank_conjugated_diagonal _ U hU] using h

end

end MOC
