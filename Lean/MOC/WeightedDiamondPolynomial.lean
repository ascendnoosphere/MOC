import MOC.Support
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! The weighted middle row-set law and two singleton laws determine the
entire pole polynomial at a fixed real pencil parameter. -/

open BigOperators Finset Matrix

namespace MOC

noncomputable section

/-- Linear tests of the two singleton laws and the weighted middle law. -/
def weightedDiamondScore (t : ℝ) (f g : Fin 4 → ℝ) (h : Finset (Fin 4) → ℝ)
    (σ : Equiv.Perm (Fin 4)) : ℝ :=
  f (σ 0) + g (σ 3) + h (({0, 1} : Finset (Fin 4)).map σ.toEmbedding) +
    t * h (({0, 2} : Finset (Fin 4)).map σ.toEmbedding)

/-- The support inequalities for the weighted scores give one law for all
three groups of coefficients. -/
theorem exists_weights_of_weightedDiamond_support (t : ℝ)
    (v : Equiv.Perm (Fin 4) → ℝ)
    (hs : ∀ f g s, ∃ σ : Equiv.Perm (Fin 4),
      (∑ τ, v τ * weightedDiamondScore t f g s τ) ≤ weightedDiamondScore t f g s σ) :
    ∃ w : Equiv.Perm (Fin 4) → ℝ, (∀ σ, 0 ≤ w σ) ∧ (∑ σ, w σ = 1) ∧
      ∀ f g s, (∑ σ, w σ * weightedDiamondScore t f g s σ) =
        ∑ σ, v σ * weightedDiamondScore t f g s σ := by
  classical
  let ι := Fin 4 ⊕ (Fin 4 ⊕ Finset (Fin 4))
  let V := ι → ℝ
  let e (i : ι) : V := Pi.single i 1
  let b (σ : Equiv.Perm (Fin 4)) : V :=
    e (.inl (σ 0)) + e (.inr (.inl (σ 3))) +
      e (.inr (.inr (({0, 1} : Finset (Fin 4)).map σ.toEmbedding))) +
      t • e (.inr (.inr (({0, 2} : Finset (Fin 4)).map σ.toEmbedding)))
  have hpoint (L : V →ₗ[ℝ] ℝ) (σ : Equiv.Perm (Fin 4)) :
      L (b σ) = weightedDiamondScore t (fun i => L (e (.inl i)))
        (fun i => L (e (.inr (.inl i)))) (fun I => L (e (.inr (.inr I)))) σ := by
    simp only [b, weightedDiamondScore, map_add, map_smul, smul_eq_mul]
  let z : V := ∑ σ, v σ • b σ
  have hz : z ∈ convexHull ℝ (Set.range b) := by
    apply Classical.byContradiction
    intro hn
    have hclosed : IsClosed (convexHull ℝ (Set.range b)) := (Set.finite_range b).isClosed_convexHull
    obtain ⟨L, c, hc, hz⟩ :=
      geometric_hahn_banach_closed_point (convex_convexHull ℝ _) hclosed hn
    let P := L.toLinearMap
    obtain ⟨σ, hσ⟩ :=
      hs (fun i => P (e (.inl i))) (fun i => P (e (.inr (.inl i))))
        (fun I => P (e (.inr (.inr I))))
    have hP (τ : Equiv.Perm (Fin 4)) : L (b τ) =
        weightedDiamondScore t (fun i => P (e (.inl i))) (fun i => P (e (.inr (.inl i))))
          (fun I => P (e (.inr (.inr I)))) τ := hpoint P τ
    have he : L z ≤ L (b σ) := by
      simpa only [z, map_sum, map_smul, smul_eq_mul, hP] using hσ
    exact (lt_irrefl _) ((hc _ (subset_convexHull ℝ _ (Set.mem_range_self σ))).trans
      (hz.trans_le he))
  obtain ⟨κ, inst, a, y, ha, ha₁, hy, hsum⟩ := mem_convexHull_iff_exists_fintype.mp hz
  letI : Fintype κ := inst
  have hy' (i : κ) : ∃ σ, b σ = y i := hy i
  choose σ hσ using hy'
  let w (τ : Equiv.Perm (Fin 4)) : ℝ := ∑ i, if σ i = τ then a i else 0
  refine ⟨w, fun τ => Finset.sum_nonneg fun i _ => by split_ifs <;> simp [ha], ?_, ?_⟩
  · unfold w
    rw [Finset.sum_comm]
    simpa using ha₁
  · intro f g s
    let d : ι → ℝ := Sum.elim f (Sum.elim g s)
    let L : V →ₗ[ℝ] ℝ := ∑ i, d i • LinearMap.proj i
    have hL (i : ι) : L (e i) = d i := by
      unfold L
      rw [LinearMap.sum_apply]
      change (∑ j : ι, d j * e i j) = d i
      rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _) (fun j _ hj => by
        simp [e, Pi.single_eq_of_ne hj])]
      simp [e]
    have hb (τ : Equiv.Perm (Fin 4)) : L (b τ) = weightedDiamondScore t f g s τ := by
      simp only [hpoint, hL, d, Sum.elim_inl, Sum.elim_inr]
    have he := congrArg L hsum
    simp only [← hσ, z, map_sum, map_smul, smul_eq_mul, hb] at he
    calc
      _ = ∑ i, a i * weightedDiamondScore t f g s (σ i) := by
        simp_rw [w, Finset.sum_mul, ite_mul, zero_mul]
        rw [Finset.sum_comm]
        simp
      _ = _ := he

/-- Equality of the weighted scores gives equality of the homogeneous pole
polynomial for every choice of the first spectrum. -/
theorem sum_pole_polynomial_eq_of_weightedDiamondScores
    (t : ℝ) (w v : Equiv.Perm (Fin 4) → ℝ)
    (h : ∀ f g s, (∑ σ, w σ * weightedDiamondScore t f g s σ) =
      ∑ σ, v σ * weightedDiamondScore t f g s σ)
    (x y : Fin 4 → ℂ) :
    let p (σ : Equiv.Perm (Fin 4)) :=
      y (σ 0) * (x (σ 1) + y (σ 1)) * (x (σ 2) + (t : ℂ) * y (σ 2)) * x (σ 3)
    (∑ σ, (w σ : ℂ) * p σ) = ∑ σ, (v σ : ℂ) * p σ := by
  intro p
  let s (I : Finset (Fin 4)) := ∏ j, if j ∈ I then y j else x j
  let f (i : Fin 4) := s {i}
  let g (i : Fin 4) := (t : ℂ) * s ({i} : Finset (Fin 4))ᶜ
  have hreindex (σ : Equiv.Perm (Fin 4)) (I : Finset (Fin 4)) :
      s (I.map σ.toEmbedding) = ∏ j, if j ∈ I then y (σ j) else x (σ j) := by
    dsimp only [s]
    rw [← Equiv.prod_comp σ (fun j => if j ∈ I.map σ.toEmbedding then y j else x j)]
    apply Finset.prod_congr rfl
    intro j _
    simp only [Finset.mem_map_equiv, Equiv.symm_apply_apply]
  have hexpand (σ : Equiv.Perm (Fin 4)) :
      p σ = f (σ 0) + g (σ 3) + s (({0, 1} : Finset (Fin 4)).map σ.toEmbedding) +
        (t : ℂ) * s (({0, 2} : Finset (Fin 4)).map σ.toEmbedding) := by
    have h₀ : ({0} : Finset (Fin 4)).map σ.toEmbedding = {σ 0} := by
      simp only [Finset.map_singleton, Equiv.toEmbedding_apply]
    have h₃ : (({3} : Finset (Fin 4))ᶜ).map σ.toEmbedding = ({σ 3} : Finset (Fin 4))ᶜ := by
      ext j
      simp only [Finset.mem_map_equiv, Finset.mem_compl, Finset.mem_singleton, Equiv.symm_apply_eq]
    dsimp only [p, f, g]
    simp only [← h₀, ← h₃, hreindex, Fin.prod_univ_four]
    have h01 : (0 : Fin 4) ≠ 1 := by decide
    have h02 : (0 : Fin 4) ≠ 2 := by decide
    have h03 : (0 : Fin 4) ≠ 3 := by decide
    have h12 : (1 : Fin 4) ≠ 2 := by decide
    have h13 : (1 : Fin 4) ≠ 3 := by decide
    have h23 : (2 : Fin 4) ≠ 3 := by decide
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_compl, eq_self, h01, h02, h03, h12,
      h13, h23, Ne.symm h01, Ne.symm h02, Ne.symm h03, Ne.symm h12, Ne.symm h13, Ne.symm h23,
      true_or, false_or, or_true, or_false, not_true_eq_false, not_false_eq_true, if_true, if_false]
    ring
  simp_rw [hexpand]
  apply Complex.ext
  · simpa only [Complex.re_sum, Complex.re_ofReal_mul, Complex.add_re, weightedDiamondScore] using
      h (fun i => (f i).re) (fun i => (g i).re) (fun I => (s I).re)
  · simpa only [Complex.im_sum, Complex.im_ofReal_mul, Complex.add_im, weightedDiamondScore] using
      h (fun i => (f i).im) (fun i => (g i).im) (fun I => (s I).im)

/-- A law matching the normalized pole scores evaluates the determinant for
every first spectrum when the finite reciprocal labels normalize to 1, t, and 0. -/
theorem determinantValue_eq_of_weightedDiamondScores (a b : Fin 4 → ℂ) (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : IsUnitary U) (t : ℝ) (w : Equiv.Perm (Fin 4) → ℝ)
    (h : ∀ f g s, (∑ σ, w σ * weightedDiamondScore t f g s σ) =
      ∑ σ, realSignedWeight U σ * weightedDiamondScore t f g s σ)
    (hb : ∀ j ≠ 0, b j - b 0 ≠ 0)
    (hδ : (b 1 - b 0)⁻¹ - (b 3 - b 0)⁻¹ ≠ 0)
    (ht : (b 2 - b 0)⁻¹ - (b 3 - b 0)⁻¹ =
      (t : ℂ) * ((b 1 - b 0)⁻¹ - (b 3 - b 0)⁻¹)) :
    (∑ σ, (w σ : ℂ) * matchingProduct a b σ) = determinantValue a b U := by
  let A (i : Fin 4) := a i + b 0
  let B (j : Fin 4) := b j - b 0
  let δ := (B 1)⁻¹ - (B 3)⁻¹
  let X (i : Fin 4) := (1 + (B 3)⁻¹ * A i) / δ
  let c : Fin 4 → ℂ := ![0, 1, (t : ℂ), 0]
  have hnorm (j : Fin 4) (hj : j ≠ 0) : δ * c j = (B j)⁻¹ - (B 3)⁻¹ := by
    fin_cases j
    · exact (hj rfl).elim
    · change δ * 1 = (B 1)⁻¹ - (B 3)⁻¹
      rw [mul_one]
    · change δ * (t : ℂ) = (B 2)⁻¹ - (B 3)⁻¹
      exact (mul_comm _ _).trans ht.symm
    · change δ * 0 = (B 3)⁻¹ - (B 3)⁻¹
      rw [mul_zero, sub_self]
  have hfactor (σ : Equiv.Perm (Fin 4)) (j : Fin 4) (hj : j ≠ 0) :
      a (σ j) + b j = B j * (δ * (X (σ j) + c j * A (σ j))) := by
    have he : δ * X (σ j) = 1 + (B 3)⁻¹ * A (σ j) := by
      dsimp only [X]
      rw [mul_comm, div_mul_cancel₀ _ hδ]
    rw [mul_add δ, he, ← mul_assoc δ, hnorm j hj]
    have hcancel : 1 + (B 3)⁻¹ * A (σ j) + ((B j)⁻¹ - (B 3)⁻¹) * A (σ j) =
        1 + (B j)⁻¹ * A (σ j) := by ring
    rw [hcancel, mul_add, mul_one, ← mul_assoc, mul_inv_cancel₀ (hb j hj), one_mul]
    dsimp only [A, B]
    ring
  let C := B 1 * B 2 * B 3 * δ ^ 3
  have hprod (σ : Equiv.Perm (Fin 4)) :
      matchingProduct a b σ =
        C * (A (σ 0) * (X (σ 1) + A (σ 1)) * (X (σ 2) + (t : ℂ) * A (σ 2)) * X (σ 3)) := by
    rw [matchingProduct, Fin.prod_univ_four, hfactor σ 1 (by decide),
      hfactor σ 2 (by decide), hfactor σ 3 (by decide)]
    have h₁ : c 1 = 1 := rfl
    have h₂ : c 2 = (t : ℂ) := rfl
    have h₃ : c 3 = 0 := rfl
    simp only [h₁, h₂, h₃, one_mul, zero_mul, add_zero, C]
    change A (σ 0) * _ * _ * _ = _
    ring
  rw [← real_signed_determinant a b U hU]
  simp_rw [hprod, ← mul_left_comm C, ← Finset.mul_sum]
  change C * _ = C * _
  congr 1
  exact sum_pole_polynomial_eq_of_weightedDiamondScores t w (realSignedWeight U) h X A

end

end MOC
