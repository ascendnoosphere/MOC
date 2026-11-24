import MOC.FiniteMinorLaw

/-! A symbolic kernel for order-four common minor laws. The correction
is alternating permutation parity localized at one assigned entry. -/

open Finset BigOperators

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def parityReal (σ : Equiv.Perm ι) : ℝ := ((Equiv.Perm.sign σ : ℤ) : ℝ)

private theorem parityReal_mul_swap (σ : Equiv.Perm ι) {u v : ι}
    (huv : u ≠ v) : parityReal (σ * Equiv.swap u v) = -parityReal σ := by
  simp [parityReal, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap huv]

private theorem exists_swap_away_preserving (hcard : 4 ≤ Fintype.card ι)
    (j : ι) (J : Finset ι) :
    ∃ u v : ι, u ≠ v ∧ u ≠ j ∧ v ≠ j ∧ (u ∈ J ↔ v ∈ J) := by
  let S := J.erase j
  let T := Jᶜ.erase j
  have hU : S ∪ T = (univ : Finset ι).erase j := by
    ext x
    simp [S, T]
    tauto
  have hD : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro x hx hy
    exact (Finset.mem_compl.mp (Finset.mem_erase.mp hy).2) (Finset.mem_erase.mp hx).2
  have hc := Finset.card_union_of_disjoint hD
  rw [hU, Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ] at hc
  by_cases hS : 1 < S.card
  · obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hS
    obtain ⟨huj, huJ⟩ := Finset.mem_erase.mp hu
    obtain ⟨hvj, hvJ⟩ := Finset.mem_erase.mp hv
    exact ⟨u, v, huv, huj, hvj, iff_of_true huJ hvJ⟩
  · have hT : 1 < T.card := by omega
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hT
    obtain ⟨huj, huJ⟩ := Finset.mem_erase.mp hu
    obtain ⟨hvj, hvJ⟩ := Finset.mem_erase.mp hv
    exact ⟨u, v, huv, huj, hvj, iff_of_false (Finset.mem_compl.mp huJ)
      (Finset.mem_compl.mp hvJ)⟩

/-- The alternating law supported at a prescribed assignment has zero
marginal for every subset image. Pair permutations by a transposition
outside that assignment and inside one block of the source subset. -/
theorem sum_parity_at_assignment_subsetImage (hcard : 4 ≤ Fintype.card ι)
    (i j : ι) (I J : Finset ι) :
    ∑ σ : Equiv.Perm ι,
      (if σ j = i ∧ J.map σ.toEmbedding = I then parityReal σ else 0) = 0 := by
  classical
  obtain ⟨u, v, huv, huj, hvj, hmem⟩ := exists_swap_away_preserving hcard j J
  let τ : Equiv.Perm ι := Equiv.swap u v
  have hτj : τ j = j := Equiv.swap_apply_of_ne_of_ne (Ne.symm huj) (Ne.symm hvj)
  have hτJ : J.map τ.toEmbedding = J := by
    ext x
    rw [Finset.mem_map_equiv]
    change Equiv.swap u v x ∈ J ↔ x ∈ J
    by_cases hxu : x = u
    · subst x
      simpa using hmem.symm
    by_cases hxv : x = v
    · subst x
      simpa using hmem
    rw [Equiv.swap_apply_of_ne_of_ne hxu hxv]
  let f := fun σ : Equiv.Perm ι =>
    if σ j = i ∧ J.map σ.toEmbedding = I then parityReal σ else 0
  have hf (σ : Equiv.Perm ι) : f (σ * τ) = -f σ := by
    have hJ : J.map (σ * τ).toEmbedding = J.map σ.toEmbedding := by
      rw [show (σ * τ).toEmbedding = τ.toEmbedding.trans σ.toEmbedding from rfl,
        ← Finset.map_map, hτJ]
    dsimp [f]
    rw [hτj, hJ, parityReal_mul_swap σ huv]
    split_ifs <;> simp
  have he := Equiv.sum_comp (Equiv.mulRight τ) f
  change (∑ σ, f (σ * τ)) = ∑ σ, f σ at he
  simp_rw [hf, Finset.sum_neg_distrib] at he
  change ∑ σ, f σ = 0
  linarith

/-- Inequalities for the analytic near-balanced quaternion shape. -/
theorem nearBalancedParityCorrection {t : ℝ} (ht : 2/3 ≤ t) (ht' : t ≤ 1) :
    let w := (2-t)/4
    let v := (3*t-2)/4
    0 ≤ w ∧ 0 ≤ v ∧ 3*w+v = 1 ∧
      2*t*(w+w) ≤ 1 ∧ 2*t*(w+v) = t^2 := by
  dsimp
  refine ⟨by linarith, by linarith, by ring, ?_, by ring⟩
  nlinarith [sq_nonneg (1-t)]


/-- Signed correction coefficients are permitted. Only the corrected
translation and pair weights must be nonnegative. -/
theorem nearBalancedParityCorrection_signed {t : ℝ} (ht : 0 ≤ t)
    (ht' : t ≤ 1) (hc : 0 ≤ t^3+3*t-2) :
    let w := (2-t)/4
    let v := (3*t-2)/4
    3*w+v = 1 ∧ 0 ≤ 1+4*t*w ∧ 0 ≤ t^4+4*t*v ∧
      2*t*(w+w) ≤ 1 ∧ 2*t*(w+v) = t^2 := by
  dsimp
  have hw : 0 ≤ (2-t)/4 := by linarith
  refine ⟨by ring, by positivity, ?_, ?_, by ring⟩
  · calc
      _ = t*(t^3+3*t-2) := by ring
      _ ≥ 0 := mul_nonneg ht hc
  · nlinarith [sq_nonneg (1-t)]

/-- Add arbitrary real multiples of the pivot parity kernels to the signed law. -/
def parityCorrectedWeight (U : Matrix ι ι ℂ) (c : ι → ι → ℝ) (σ : Equiv.Perm ι) : ℝ :=
  realSignedWeight U σ + ∑ ij : ι × ι, if σ ij.2 = ij.1 then c ij.1 ij.2 * parityReal σ else 0

private theorem parityCorrectedWeights_minor (hcard : 4 ≤ Fintype.card ι)
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) (c : ι → ι → ℝ) (I J : Finset ι) :
    (∑ σ ∈ univ.filter (fun σ : Equiv.Perm ι => J.map σ.toEmbedding = I),
      parityCorrectedWeight U c σ) = subsetMinorSq U I J := by
  classical
  have hs := congrArg Complex.re (sum_signedWeight_image_eq_subsetMinorSq U hU I J)
  have hsr :
    (∑ σ ∈ univ.filter (fun σ : Equiv.Perm ι => J.map σ.toEmbedding = I),
      realSignedWeight U σ) = subsetMinorSq U I J := by
    simpa only [Complex.re_sum, Complex.ofReal_re, realSignedWeight] using hs
  unfold parityCorrectedWeight
  rw [Finset.sum_add_distrib, hsr, Finset.sum_comm]
  suffices he : (∑ ij : ι × ι, ∑ σ ∈ univ.filter
      (fun σ : Equiv.Perm ι => J.map σ.toEmbedding = I),
        if σ ij.2 = ij.1 then c ij.1 ij.2 * parityReal σ else 0) = 0 by rw [he, add_zero]
  apply Finset.sum_eq_zero
  intro ij _
  rw [Finset.sum_filter]
  calc
    _ = ∑ σ : Equiv.Perm ι, c ij.1 ij.2 *
          (if σ ij.2 = ij.1 ∧ J.map σ.toEmbedding = I then parityReal σ else 0) := by
      apply Finset.sum_congr rfl
      intro σ _
      by_cases h : σ ij.2 = ij.1 <;> by_cases h' : J.map σ.toEmbedding = I <;> simp [h, h']
    _ = 0 := by rw [← Finset.mul_sum, sum_parity_at_assignment_subsetImage hcard, mul_zero]

/-- A feasible parity correction certifies the full MOC value for every
choice of spectra, without invoking any order-four stationary hypothesis. -/
theorem holds_of_nonneg_parityCorrectedWeight (hcard : 4 ≤ Fintype.card ι)
    (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U) (c : ι → ι → ℝ)
    (hn : ∀ σ, 0 ≤ parityCorrectedWeight U c σ) : Holds a b U := by
  classical
  have hm := parityCorrectedWeights_minor hcard U hU c
  have hs : ∑ σ, parityCorrectedWeight U c σ = 1 := by
    have hmass := hm ∅ ∅
    simpa [subsetMinorSq] using hmass
  exact holds_of_indexed_minor_law a b U hU id (parityCorrectedWeight U c) hn hs
    (fun I J => (hm I J).symm)

end

end MOC
