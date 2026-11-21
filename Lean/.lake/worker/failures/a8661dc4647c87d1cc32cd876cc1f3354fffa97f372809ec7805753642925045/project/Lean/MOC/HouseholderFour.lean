import MOC.Householder
import MOC.HouseholderPacking
import Mathlib.Tactic.FinCases

/-! The four-coordinate Householder determinant is a positive combination of
matching products. -/

open BigOperators Matrix

namespace MOC

noncomputable section

private def fourPair : Fin 6 → Fin 4 × Fin 4 :=
  ![(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

private def fourSwap (j : Fin 6) : Equiv.Perm (Fin 4) :=
  Equiv.swap (fourPair j).1 (fourPair j).2

private def fourEdgeMass (p : Fin 4 → ℝ) (j : Fin 6) : ℝ :=
  4 * p (fourPair j).1 * p (fourPair j).2

private def fourSignedDet (a b : Fin 4 → ℂ) (p : Fin 4 → ℝ) : ℂ :=
  matchingProduct a b 1 + ∑ j : Fin 6, (fourEdgeMass p j : ℂ) *
    (matchingProduct a b (fourSwap j) - matchingProduct a b 1)

private theorem prod_pair_complement (i j : Fin 4) (hij : i ≠ j) (f : Fin 4 → ℂ) :
    (∏ k, f k) = f i * f j * (∏ k ∈ (Finset.univ.erase i).erase j, f k) := by
  rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ i),
    ← Finset.mul_prod_erase (Finset.univ.erase i) f
      (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩), mul_assoc]

private theorem det_four_rank_one_sum (A B C D : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : A.det = 0) (hB : B.det = 0) (hC : C.det = 0) (hD : D.det = 0) :
    (A + B + C + D).det =
      (A + B).det + (A + C).det + (A + D).det + (B + C).det + (B + D).det + (C + D).det := by
  have h :
      (A + B + C + D).det + 2 * (A.det + B.det + C.det + D.det) =
        (A + B).det + (A + C).det + (A + D).det + (B + C).det + (B + D).det + (C + D).det := by
    simp only [Matrix.det_fin_two, Matrix.add_apply]
    ring
  simpa only [hA, hB, hC, hD, add_zero, mul_zero] using h

private theorem determinantValue_householder_four_regular (a b v : Fin 4 → ℂ)
    (hv : ∑ i, star (v i) * v i = 1) (hreg : ∀ i, a i + b i ≠ 0) :
    determinantValue a b (rankOnePhase v (-1)) = fourSignedDet a b (fun i => Complex.normSq (v i)) := by
  let p (i : Fin 4) := Complex.normSq (v i)
  let m (i : Fin 4) := a i + b i
  let q (i : Fin 4) := (p i : ℂ) / m i
  let Q (i : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ :=
    !![q i * a i, q i; q i * a i * b i, q i * b i]
  have hp (i : Fin 4) : (p i : ℂ) = star (v i) * v i :=
    Complex.normSq_eq_conj_mul_self
  have hN : rankOneSpectralCompression a b v = ∑ i, Q i := by
    ext r s
    fin_cases r <;> fin_cases s <;>
      simp [rankOneSpectralCompression, Q, q, m, Matrix.sum_apply] <;>
      apply Finset.sum_congr rfl <;> intro k _ <;> rw [hp, starRingEnd_apply] <;> ring
  have hQ (i : Fin 4) : (Q i).det = 0 := by
    simp [Q, Matrix.det_fin_two] <;> ring
  have hpairs (i j : Fin 4) (hij : i ≠ j) :
      (∏ k, m k) * (Q i + Q j).det =
        (p i : ℂ) * (p j : ℂ) * (matchingProduct a b 1 - matchingProduct a b (Equiv.swap i j)) := by
    let R := ∏ k ∈ (Finset.univ.erase i).erase j, m k
    have hid : matchingProduct a b 1 = m i * m j * R := by
      simpa only [matchingProduct, Equiv.Perm.one_apply] using prod_pair_complement i j hij m
    have hswap : matchingProduct a b (Equiv.swap i j) =
        (a j + b i) * (a i + b j) * R := by
      unfold matchingProduct
      rw [prod_pair_complement i j hij,
        Equiv.swap_apply_left, Equiv.swap_apply_right]
      congr 1
      apply Finset.prod_congr rfl
      intro k hk
      rw [Equiv.swap_apply_of_ne_of_ne
        (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1 (Finset.mem_erase.mp hk).1]
    have hPairDet : (Q i + Q j).det = q i * q j * (a i - a j) * (b j - b i) := by
      simp [Q, Matrix.det_fin_two, Matrix.add_apply] <;> ring
    rw [hPairDet, hid, hswap, prod_pair_complement i j hij m]
    dsimp only [q, m]
    field_simp [hreg i, hreg j] <;> ring
  have hsum :
      (∏ k, m k) * (rankOneSpectralCompression a b v).det =
        ∑ e : Fin 6, (p (fourPair e).1 : ℂ) * (p (fourPair e).2 : ℂ) *
          (matchingProduct a b 1 - matchingProduct a b (fourSwap e)) := by
    rw [hN, Fin.sum_univ_four, det_four_rank_one_sum _ _ _ _ (hQ _) (hQ _) (hQ _) (hQ _)]
    simp only [mul_add, hpairs 0 1 (by decide), hpairs 0 2 (by decide), hpairs 0 3 (by decide),
      hpairs 1 2 (by decide), hpairs 1 3 (by decide), hpairs 2 3 (by decide), Fin.sum_univ_six] <;> rfl
  rw [determinantValue_rankOnePhase _ _ _ _ hv (by simp) hreg]
  calc
    _ = (∏ i, m i) - 4 * ((∏ i, m i) * (rankOneSpectralCompression a b v).det) := by
      simp only [star_neg, star_one]
      dsimp only [m]
      ring
    _ = _ := by
      rw [hsum]
      unfold fourSignedDet
      simp only [matchingProduct, Equiv.Perm.one_apply, Fin.sum_univ_six, fourEdgeMass,
        Complex.ofReal_mul, Complex.ofReal_ofNat]
      dsimp only [m, p]
      ring

private theorem determinantValue_householder_four (a b v : Fin 4 → ℂ)
    (hv : ∑ i, star (v i) * v i = 1) :
    determinantValue a b (rankOnePhase v (-1)) = fourSignedDet a b (fun i => Complex.normSq (v i)) := by
  let p (i : Fin 4) := Complex.normSq (v i)
  let A (t : ℂ) (i : Fin 4) := a i + t
  let K : Set ℂ := Set.range fun i : Fin 4 => -(a i + b i)
  have hK : Dense Kᶜ := (Set.finite_range _).countable.dense_compl ℂ
  let f (t : ℂ) := determinantValue (A t) b (rankOnePhase v (-1))
  let g (t : ℂ) := fourSignedDet (A t) b p
  have hfg : Set.EqOn f g Kᶜ := by
    intro t ht
    have hreg (i : Fin 4) : A t i + b i ≠ 0 := by
      intro he
      apply ht
      refine ⟨i, ?_⟩
      change a i + t + b i = 0 at he
      linear_combination -he
    exact determinantValue_householder_four_regular (A t) b v hv hreg
  have hcA : Continuous A := continuous_pi fun _ => continuous_const.add continuous_id
  have hm (σ : Equiv.Perm (Fin 4)) : Continuous fun t => matchingProduct (A t) b σ := by
    unfold matchingProduct
    exact continuous_finset_prod _ fun i _ =>
      ((continuous_apply (σ i)).comp hcA).add continuous_const
  have hf : Continuous f := by unfold f determinantValue; fun_prop
  have hg : Continuous g := by
    unfold g fourSignedDet
    exact (hm 1).add (continuous_finset_sum _ fun j _ =>
      continuous_const.mul ((hm (fourSwap j)).sub (hm 1)))
  have hzero := hfg.closure hf hg (hK 0)
  have hA : A 0 = a := by funext i; simp [A]
  simpa only [f, g, hA] using hzero

private def fourTriangleEdges (i : Fin 4) : Fin 3 → Fin 6 :=
  ![![3, 4, 5], ![1, 2, 5], ![0, 2, 4], ![0, 1, 3]] i

private def fourCycle (i : Fin 4) (reverse : Bool) : Equiv.Perm (Fin 4) :=
  let ij := fourSwap (fourTriangleEdges i 0)
  let jk := fourSwap (fourTriangleEdges i 2)
  if reverse then jk * ij else ij * jk

private theorem matchingProduct_threeCycle_sum
    (a b : Fin 4 → ℂ) (i j k : Fin 4) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    matchingProduct a b (Equiv.swap i j * Equiv.swap j k) +
        matchingProduct a b (Equiv.swap j k * Equiv.swap i j) =
      matchingProduct a b (Equiv.swap i j) + matchingProduct a b (Equiv.swap i k) +
        matchingProduct a b (Equiv.swap j k) - matchingProduct a b 1 := by
  let S : Finset (Fin 4) := {i, j, k}
  let R := ∏ l ∈ Sᶜ, (a l + b l)
  have hi : i ∈ S := by simp [S]
  have hj : j ∈ S := by simp [S]
  have hk : k ∈ S := by simp [S]
  have hfix (u v : Fin 4) (hu : u ∈ S) (hv : v ∈ S) (l : Fin 4) (hl : l ∈ Sᶜ) :
      Equiv.swap u v l = l := by
    have hn := Finset.mem_compl.mp hl
    exact Equiv.swap_apply_of_ne_of_ne (fun he => hn (he.symm ▸ hu)) (fun he => hn (he.symm ▸ hv))
  have split (σ : Equiv.Perm (Fin 4)) (hσ : ∀ l ∈ Sᶜ, σ l = l) :
      matchingProduct a b σ =
        R * ((a (σ i) + b i) * (a (σ j) + b j) * (a (σ k) + b k)) := by
    let f (l : Fin 4) := a (σ l) + b l
    have hR : (∏ l ∈ Sᶜ, f l) = R := by
      apply Finset.prod_congr rfl
      intro l hl
      change a (σ l) + b l = a l + b l
      rw [hσ l hl]
    have hS : (∏ l ∈ S, f l) = f i * f j * f k := by
      change (∏ l ∈ ({i, j, k} : Finset (Fin 4)), f l) = _
      rw [Finset.prod_insert (show i ∉ ({j, k} : Finset (Fin 4)) by simp [hij, hik]),
        Finset.prod_insert (show j ∉ ({k} : Finset (Fin 4)) by simp [hjk]),
        Finset.prod_singleton, mul_assoc]
    change (∏ l, f l) = R * (f i * f j * f k)
    rw [← Finset.prod_compl_mul_prod S f, hR, hS]
  have h₁ := split (Equiv.swap i j) (hfix i j hi hj)
  have h₂ := split (Equiv.swap i k) (hfix i k hi hk)
  have h₃ := split (Equiv.swap j k) (hfix j k hj hk)
  have h₀ := split 1 (by intro l _; rfl)
  have h₄ := split (Equiv.swap i j * Equiv.swap j k) (fun l hl => by
    simp only [Equiv.Perm.mul_apply, hfix j k hj hk l hl, hfix i j hi hj l hl])
  have h₅ := split (Equiv.swap j k * Equiv.swap i j) (fun l hl => by
    simp only [Equiv.Perm.mul_apply, hfix i j hi hj l hl, hfix j k hj hk l hl])
  rw [h₄, h₅, h₁, h₂, h₃, h₀]
  simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply, Equiv.swap_apply_left,
    Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hik.symm hjk.symm,
    Equiv.swap_apply_of_ne_of_ne hij.symm hjk, Equiv.swap_apply_of_ne_of_ne hij hik]
  ring

private theorem matchingProduct_fourCycle_sum (a b : Fin 4 → ℂ) (i : Fin 4) :
    matchingProduct a b (fourCycle i false) + matchingProduct a b (fourCycle i true) =
      (∑ j : Fin 3, matchingProduct a b (fourSwap (fourTriangleEdges i j))) -
        matchingProduct a b 1 := by
  rw [Fin.sum_univ_three]
  fin_cases i
  · exact matchingProduct_threeCycle_sum a b 1 2 3 (by decide) (by decide) (by decide)
  · exact matchingProduct_threeCycle_sum a b 0 2 3 (by decide) (by decide) (by decide)
  · exact matchingProduct_threeCycle_sum a b 0 1 3 (by decide) (by decide) (by decide)
  · exact matchingProduct_threeCycle_sum a b 0 1 2 (by decide) (by decide) (by decide)

/-- A Householder reflection in order four satisfies the determinant hull inclusion.
The weights from the triangle packing depend only on the reflecting vector. -/
theorem holds_householder_four (a b v : Fin 4 → ℂ) (hv : ∑ i, star (v i) * v i = 1) :
    Holds a b (rankOnePhase v (-1)) := by
  let p (i : Fin 4) := Complex.normSq (v i)
  have hp (i : Fin 4) : (p i : ℂ) = star (v i) * v i :=
    Complex.normSq_eq_conj_mul_self
  have hsum : ∑ i, p i = 1 := by
    have hcast : ((∑ i, p i : ℝ) : ℂ) = 1 := by
      simp only [Complex.ofReal_sum, hp, hv]
    simpa only [Complex.ofReal_re, Complex.one_re] using congrArg Complex.re hcast
  obtain ⟨t, ht, htotal, h01, h02, h03, h12, h13, h23⟩ :=
    exists_householder_triangle_packing_edges p (fun i => Complex.normSq_nonneg _) hsum
  let r : Fin 6 → ℝ := ![fourEdgeMass p 0 - t 2 - t 3, fourEdgeMass p 1 - t 1 - t 3,
    fourEdgeMass p 2 - t 1 - t 2, fourEdgeMass p 3 - t 0 - t 3,
    fourEdgeMass p 4 - t 0 - t 2, fourEdgeMass p 5 - t 0 - t 1]
  have hr (j : Fin 6) : 0 ≤ r j := by
    fin_cases j <;> simp [r, fourEdgeMass, fourPair] <;> linarith
  let wId := 1 - (∑ j : Fin 6, fourEdgeMass p j) + ∑ i, t i
  have hsum₂ : (p 0 + p 1 + p 2 + p 3) ^ 2 = 1 := by
    have h := congrArg (fun x : ℝ => x ^ 2) hsum
    simpa [Fin.sum_univ_four] using h
  have hgap : (∑ j : Fin 6, fourEdgeMass p j) - 1 = 1 - 2 * ∑ i, p i ^ 2 := by
    simp [Fin.sum_univ_four, Fin.sum_univ_six, fourEdgeMass, fourPair]
    nlinarith only [hsum₂]
  have hw0 : 0 ≤ wId := by
    dsimp only [wId]
    linarith only [hgap, htotal, le_max_right 0 (1 - 2 * ∑ i, p i ^ 2)]
  let w : Fin 15 → ℝ := ![wId, r 0, r 1, r 2, r 3, r 4, r 5, t 0, t 0, t 1, t 1, t 2, t 2, t 3, t 3]
  let σ : Fin 15 → Equiv.Perm (Fin 4) :=
    ![1, fourSwap 0, fourSwap 1, fourSwap 2, fourSwap 3, fourSwap 4, fourSwap 5,
      fourCycle 0 false, fourCycle 0 true, fourCycle 1 false, fourCycle 1 true,
      fourCycle 2 false, fourCycle 2 true, fourCycle 3 false, fourCycle 3 true]
  unfold Holds
  refine mem_convexHull_of_exists_fintype w (fun i => matchingProduct a b (σ i)) ?_ ?_
    (fun i => ⟨σ i, rfl⟩) ?_
  · intro i
    fin_cases i <;> first
      | exact hw0
      | exact hr 0
      | exact hr 1
      | exact hr 2
      | exact hr 3
      | exact hr 4
      | exact hr 5
      | exact ht 0
      | exact ht 1
      | exact ht 2
      | exact ht 3
  · simp [w, wId, r, Fin.sum_univ_succ, Fin.sum_univ_zero] <;> ring
  · rw [determinantValue_householder_four a b v hv]
    change _ = fourSignedDet a b p
    have C (i : Fin 4) :=
      congrArg (fun z : ℂ => (t i : ℂ) * z) (matchingProduct_fourCycle_sum a b i)
    have h₀ := C 0
    have h₁ := C 1
    have h₂ := C 2
    have h₃ := C 3
    simp only [Fin.sum_univ_three, fourTriangleEdges, Matrix.cons_val] at h₀ h₁ h₂ h₃
    simp [w, wId, σ, r, fourSignedDet, Fin.sum_univ_succ, Fin.sum_univ_zero, Complex.real_smul]
    linear_combination h₀ + h₁ + h₂ + h₃

/-- Every rank-one unitary phase change in order four satisfies the determinant
hull inclusion. -/
theorem holds_rankOnePhase_four (a b v : Fin 4 → ℂ) (z : ℂ)
    (hv : ∑ i, star (v i) * v i = 1) (hz : z * star z = 1) :
    Holds a b (rankOnePhase v z) :=
  holds_rankOnePhase_of_householder a b v z hv hz (holds_householder_four a b v hv)

end

end MOC
