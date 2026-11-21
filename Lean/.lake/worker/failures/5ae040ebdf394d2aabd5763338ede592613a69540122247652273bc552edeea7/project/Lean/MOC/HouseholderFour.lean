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
      simp [rankOneSpectralCompression, Q, q, m, Matrix.sum_apply, ← hp] <;>
      apply Finset.sum_congr rfl <;> intro k _ <;> ring
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

end

end MOC
