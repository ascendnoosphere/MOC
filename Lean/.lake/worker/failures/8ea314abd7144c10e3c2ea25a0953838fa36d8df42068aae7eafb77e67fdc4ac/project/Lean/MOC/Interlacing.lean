import MOC.Blocks
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.Linarith

/-! The hull inclusion for interlacing lists in Shitov's determinant argument
(2025, Lemma 17, doi:10.4213/im9292e). -/

open BigOperators Matrix

namespace MOC

noncomputable section

/-- The convex hull of products obtained by matching every right label to a
different left label. -/
def partialMatchingHull {m n : ℕ} (a : Fin m → ℂ) (b : Fin n → ℂ) : Set ℂ :=
  convexHull ℝ (Set.range fun f : Fin n ↪ Fin m => ∏ i, (a (f i) + b i))

/-- A product over consecutive interlaces is in the hull of partial matchings
from the original list, even when adjacent endpoints coincide. -/
theorem interlacing_prod_mem_partialMatchingHull {n : ℕ}
    (a : Fin (n + 1) → ℝ) (α : Fin n → ℝ) (b : Fin n → ℂ)
    (hl : ∀ i, a i.castSucc ≤ α i) (hu : ∀ i, α i ≤ a i.succ) :
    (∏ i, ((α i : ℂ) + b i)) ∈ partialMatchingHull (fun i => (a i : ℂ)) b := by
  induction n with
  | zero =>
    exact subset_convexHull ℝ _ ⟨Fin.castSuccEmb, by simp⟩
  | succ n ih =>
    let K := partialMatchingHull (fun i => (a i : ℂ)) b
    let z : ℂ := ∏ i : Fin n, ((α i.castSucc : ℂ) + b i.castSucc)
    have hK : Convex ℝ K := convex_convexHull ℝ _
    have ha : Monotone a := Fin.monotone_iff_le_succ.mpr fun i => (hl i).trans (hu i)
    have hend (q : Fin (n + 2)) (hq : (Fin.last n).castSucc ≤ q) :
        z * ((a q : ℂ) + b (Fin.last n)) ∈ K := by
      have hl' (i : Fin n) : a (q.succAbove i.castSucc) ≤ α i.castSucc := by
        have hi : i.castSucc.castSucc < q :=
          (Fin.castSucc_lt_castSucc_iff.mpr (Fin.castSucc_lt_last i)).trans_le hq
        simpa only [Fin.succAbove_of_castSucc_lt q i.castSucc hi] using hl i.castSucc
      have hu' (i : Fin n) : α i.castSucc ≤ a (q.succAbove i.succ) := by
        apply (hu i.castSucc).trans
        apply ha
        rw [Fin.succ_castSucc]
        by_cases hi : i.succ.castSucc < q
        · rw [Fin.succAbove_of_castSucc_lt q i.succ hi]
        · rw [Fin.succAbove_of_le_castSucc q i.succ (le_of_not_gt hi)]
          exact Fin.castSucc_le_succ _
      have hz := ih (fun j => a (q.succAbove j)) (fun i => α i.castSucc)
        (fun i => b i.castSucc) hl' hu'
      let L := LinearMap.mulRight ℝ ((a q : ℂ) + b (Fin.last n))
      change z ∈ L ⁻¹' K
      apply convexHull_min _ (hK.linear_preimage L) hz
      rintro _ ⟨f, rfl⟩
      change (∏ i : Fin n, ((a (q.succAbove (f i)) : ℂ) + b i.castSucc)) *
        ((a q : ℂ) + b (Fin.last n)) ∈ K
      apply subset_convexHull ℝ _
      let g : Fin (n + 1) ↪ Fin (n + 2) :=
        finSuccEquivLast.toEmbedding.trans (f.optionMap.trans (finSuccEquiv' q).symm.toEmbedding)
      have hcast (i : Fin n) : g i.castSucc = q.succAbove (f i) := by
        change (finSuccEquiv' q).symm (Option.map f (finSuccEquivLast i.castSucc)) = _
        simp
      have hlast : g (Fin.last n) = q := by
        change (finSuccEquiv' q).symm (Option.map f (finSuccEquivLast (Fin.last n))) = _
        simp
      refine ⟨g, ?_⟩
      change (∏ i : Fin (n + 1), ((a (g i) : ℂ) + b i)) = _
      rw [Fin.prod_univ_castSucc, hlast]
      simp_rw [hcast]
    have hleft := hend (Fin.last n).castSucc le_rfl
    have hright := hend (Fin.last (n + 1)) (Fin.le_last _)
    have hsegment : α (Fin.last n) ∈
        segment ℝ (a (Fin.last n).castSucc) (a (Fin.last (n + 1))) := by
      apply Icc_subset_segment
      exact ⟨hl (Fin.last n), by simpa only [Fin.succ_last] using hu (Fin.last n)⟩
    obtain ⟨r, s, hr, hs, hrs, hval⟩ := hsegment
    simp only [smul_eq_mul] at hval
    have hval' := congrArg Complex.ofReal hval
    have hrs' := congrArg Complex.ofReal hrs
    simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_one] at hval' hrs'
    have hmem := hK hleft hright hr hs hrs
    have he :
        r • (z * ((a (Fin.last n).castSucc : ℂ) + b (Fin.last n))) +
          s • (z * ((a (Fin.last (n + 1)) : ℂ) + b (Fin.last n))) =
        z * ((α (Fin.last n) : ℂ) + b (Fin.last n)) := by
      calc
        _ = z * (((r : ℂ) * (a (Fin.last n).castSucc : ℂ) +
            (s : ℂ) * (a (Fin.last (n + 1)) : ℂ)) + ((r : ℂ) + (s : ℂ)) * b (Fin.last n)) := by
          simp only [Complex.real_smul]
          ring
        _ = _ := by rw [hval', hrs', one_mul]
    rw [he] at hmem
    rw [Fin.prod_univ_castSucc]
    exact hmem

/-- The full matching hull of the interlaced list is contained in the partial
matching hull of the original list. -/
theorem matchingHull_subset_partialMatchingHull_of_interlacing {n : ℕ}
    (a : Fin (n + 1) → ℝ) (α : Fin n → ℝ) (b : Fin n → ℂ)
    (hl : ∀ i, a i.castSucc ≤ α i) (hu : ∀ i, α i ≤ a i.succ) :
    convexHull ℝ (Set.range (matchingProduct (fun i => (α i : ℂ)) b)) ⊆
      partialMatchingHull (fun i => (a i : ℂ)) b := by
  apply convexHull_min _ (convex_convexHull ℝ _)
  rintro _ ⟨σ, rfl⟩
  have h := interlacing_prod_mem_partialMatchingHull a α (b ∘ σ.symm) hl hu
  unfold matchingProduct
  rw [← Equiv.prod_comp σ.symm (fun j => (α (σ j) : ℂ) + b j)]
  simp only [Equiv.apply_symm_apply]
  apply convexHull_mono _ h
  rintro _ ⟨f, rfl⟩
  refine ⟨σ.toEmbedding.trans f, ?_⟩
  change (∏ j, ((a (f (σ j)) : ℂ) + b j)) = ∏ j, ((a (f j) : ℂ) + b (σ.symm j))
  rw [← Equiv.prod_comp σ.symm (fun j => (a (f (σ j)) : ℂ) + b j)]
  simp only [Equiv.apply_symm_apply]

/-- An interior ball absorbs simultaneous perturbations of the vertices and
the tested point. The sum of the two error bounds must be less than the radius. -/
theorem mem_convexHull_range_of_close_vertices
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Finite ι] [Nonempty ι]
    {p q : ι → E} {x y : E} {r ε : ℝ}
    (hball : Metric.closedBall x r ⊆ convexHull ℝ (Set.range p))
    (hε : 0 ≤ ε) (hrε : 2 * ε < r)
    (hvertices : ∀ i, dist (p i) (q i) ≤ ε) (hpoint : dist y x ≤ ε) :
    y ∈ convexHull ℝ (Set.range q) := by
  classical
  by_contra hy
  have hclosed := (Set.finite_range q).isClosed_convexHull
  obtain ⟨f, d, hd, hdy⟩ :=
    geometric_hahn_banach_closed_point (convex_convexHull ℝ _) hclosed hy
  have hq (i : ι) : f (q i) < f y :=
    (hd _ (subset_convexHull ℝ _ ⟨i, rfl⟩)).trans hdy
  have hf : 0 < ‖f‖ := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    have hdist := f.dist_le_opNorm (q i) y
    have hpos : 0 < dist (f (q i)) (f y) := dist_pos.mpr (hq i).ne
    by_contra! hnonpos
    rw [le_antisymm hnonpos (norm_nonneg f), zero_mul] at hdist
    exact hpos.not_ge hdist
  have hr : 0 < r := by linarith
  have hlip {u v : E} (h : dist u v ≤ ε) : f u - f v ≤ ‖f‖ * ε :=
    (le_abs_self _).trans (by
      simpa only [Real.dist_eq] using
        (f.dist_le_opNorm u v).trans (mul_le_mul_of_nonneg_left h (norm_nonneg f)))
  have hbound : ∀ z ∈ convexHull ℝ (Set.range p), f z ≤ f x + 2 * ε * ‖f‖ := by
    apply convexHull_min _ (convex_halfSpace_le f.isLinear _)
    rintro _ ⟨i, rfl⟩
    nlinarith only [hlip (hvertices i), (hq i).le, hlip hpoint]
  have hball' (z : E) (hz : ‖z‖ ≤ r) : f z ≤ 2 * ε * ‖f‖ := by
    have hz' : x + z ∈ Metric.closedBall x r := by
      simpa only [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left] using hz
    simpa only [map_add, add_le_add_iff_left] using hbound _ (hball hz')
  have hnorm : ‖f‖ ≤ 2 * ε * ‖f‖ / r := by
    apply f.opNorm_le_bound' (div_nonneg
      (mul_nonneg (mul_nonneg zero_le_two hε) (norm_nonneg f)) hr.le)
    intro z hz
    have hz' : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg z) hz.symm
    let t := r / ‖z‖
    have ht : 0 ≤ t := div_nonneg hr.le hz'.le
    have hsize : ‖t • z‖ ≤ r := by
      rw [norm_smul, Real.norm_of_nonneg ht]
      change r / ‖z‖ * ‖z‖ ≤ r
      rw [div_mul_cancel₀ _ hz]
    have hup := hball' (t • z) hsize
    have hdown := hball' (-(t • z)) (by simpa only [norm_neg] using hsize)
    rw [map_neg] at hdown
    have hnorm' : ‖f (t • z)‖ ≤ 2 * ε * ‖f‖ := by
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨by linarith only [hdown], hup⟩
    rw [map_smul, smul_eq_mul, norm_mul, Real.norm_of_nonneg ht] at hnorm'
    have hmul : r * ‖f z‖ ≤ (2 * ε * ‖f‖) * ‖z‖ := by
      apply (div_le_iff₀ hz').mp
      simpa only [t, div_mul_eq_mul_div] using hnorm'
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hr).mpr (by simpa only [mul_comm ‖f z‖ r] using hmul)
  have habsurd := (le_div_iff₀ hr).mp hnorm
  have hlt := mul_pos hf (sub_pos.mpr hrε)
  nlinarith only [habsurd, hlt]

/-- Deleting one row and column of a unitary diagonalization produces a
determinant weighted by the squared moduli in the deleted row. -/
theorem det_principal_unitary_diagonalization {n : ℕ}
    (a : Fin (n + 1) → ℂ) {U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hU : IsUnitary U) (p : Fin (n + 1)) :
    ((U * diagonal a * Uᴴ).submatrix p.succAbove p.succAbove).det =
      ∑ i, (Complex.normSq (U p i) : ℂ) * ∏ j ∈ Finset.univ.erase i, a j := by
  let D := diagonal a
  have hadj (X Y : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hXY : X * Y = 1) :
      X.adjugate = X.det • Y := by
    calc
      X.adjugate = X.adjugate * (X * Y) := by rw [hXY, Matrix.mul_one]
      _ = (X.adjugate * X) * Y := (Matrix.mul_assoc _ _ _).symm
      _ = X.det • Y := by rw [Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
  have hconj : (U * D * Uᴴ).adjugate = U * D.adjugate * Uᴴ := by
    rw [Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib,
      hadj Uᴴ U hU.2, hadj U Uᴴ hU.1]
    calc
      _ = (Uᴴ).det • (U * (D.adjugate * (U.det • Uᴴ))) := by rw [Matrix.smul_mul]
      _ = ((Uᴴ).det * U.det) • (U * (D.adjugate * Uᴴ)) := by
        rw [Matrix.mul_smul, Matrix.mul_smul, smul_smul]
      _ = _ := by rw [← Matrix.det_mul, hU.2, Matrix.det_one, one_smul, Matrix.mul_assoc]
  have hsign : (-1 : ℂ) ^ ((p : ℕ) + (p : ℕ)) = 1 := by
    rw [← two_mul, pow_mul]
    norm_num
  have hp : (U * D * Uᴴ).adjugate p p = ((U * D * Uᴴ).submatrix p.succAbove p.succAbove).det := by
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix, hsign, one_mul]
  change ((U * D * Uᴴ).submatrix p.succAbove p.succAbove).det = _
  rw [← hp, hconj]
  unfold D
  rw [Matrix.adjugate_diagonal, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.normSq_eq_conj_mul_self, Complex.star_def]
  ring

end

end MOC
