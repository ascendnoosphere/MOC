import MOC.HouseholderFour
import MOC.Support
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! A four-label support reduction for the rank-one phase determinant. -/

open BigOperators Matrix

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem simplex_step (y : ι → Fin 3 → ℝ) (score p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hmass : ∑ i, p i = 1)
    (hlarge : 4 < (Finset.univ.filter fun i => p i ≠ 0).card) :
    ∃ q : ι → ℝ, (∀ i, 0 ≤ q i) ∧ (∑ i, q i) = 1 ∧
      (∀ j, (∑ i, q i * y i j) = ∑ i, p i * y i j) ∧
      (∑ i, p i * score i) ≤ (∑ i, q i * score i) ∧
      (Finset.univ.filter fun i => q i ≠ 0).card <
        (Finset.univ.filter fun i => p i ≠ 0).card := by
  classical
  let S := Finset.univ.filter fun i => p i ≠ 0
  let Y (i : ι) : Fin 4 → ℝ := Fin.cons 1 (y i)
  have hdep : ¬LinearIndependent ℝ (fun i : S => Y i) := by
    intro h
    have hc : S.card ≤ 4 := by
      simpa [Module.finrank_fin_fun] using h.fintype_card_le_finrank
    exact (not_le_of_gt hlarge) hc
  obtain ⟨g, hg, k, hk⟩ := Fintype.not_linearIndependent_iff.mp hdep
  let c (i : ι) := if h : i ∈ S then g ⟨i, h⟩ else 0
  have hcz (i : ι) (hi : i ∉ S) : c i = 0 := dif_neg hi
  have hcS : (∑ i, c i • Y i) = 0 := calc
    _ = ∑ i ∈ S, c i • Y i :=
      (Finset.sum_subset (Finset.subset_univ S)
        (fun i _ hi => by rw [hcz i hi, zero_smul])).symm
    _ = ∑ i : S, c i • Y i := (Finset.sum_coe_sort S (fun i => c i • Y i)).symm
    _ = ∑ i : S, g i • Y i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [show c (i : ι) = g i from dif_pos i.property]
    _ = 0 := hg
  have hcs : (∑ i, c i) = 0 := by
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Y, Fin.cons_zero, mul_one,
      Pi.zero_apply] using congrFun hcS 0
  have hcy (j : Fin 3) : (∑ i, c i * y i j) = 0 := by
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Y, Fin.cons_succ, Pi.zero_apply]
      using congrFun hcS j.succ
  let T : ℝ := ∑ i, c i * score i
  let r : ℝ := if 0 ≤ T then 1 else -1
  let d (i : ι) := r * c i
  have hr : r ≠ 0 := by dsimp [r]; split_ifs <;> norm_num
  have hds (f : ι → ℝ) : (∑ i, d i * f i) = r * ∑ i, c i * f i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => mul_assoc r (c i) (f i)
  have hd0 : (∑ i, d i) = 0 := by
    simpa only [mul_one, hcs, mul_zero] using hds (fun _ => 1)
  have hdy (j : Fin 3) : (∑ i, d i * y i j) = 0 := by rw [hds, hcy, mul_zero]
  have hdscore : 0 ≤ ∑ i, d i * score i := by
    rw [hds]
    change 0 ≤ r * T
    dsimp only [r]
    split_ifs with h
    · simpa using h
    · rw [neg_one_mul]
      exact neg_nonneg.mpr (le_of_not_ge h)
  have hdk : d k ≠ 0 := mul_ne_zero hr (by simpa only [c, dif_pos k.property] using hk)
  let D := Finset.univ.filter fun i => d i < 0
  have hD : D.Nonempty := by
    obtain ⟨i, hi⟩ : ∃ i, d i < 0 := by
      by_contra! h
      exact hdk ((Finset.sum_eq_zero_iff_of_nonneg (fun i _ => h i)).mp hd0 k (Finset.mem_univ _))
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  obtain ⟨i₀, hi₀, hmin⟩ := Finset.exists_min_image D (fun i => p i / -d i) hD
  have hi₀d : d i₀ < 0 := (Finset.mem_filter.mp hi₀).2
  have hi₀S : i₀ ∈ S := by
    by_contra h
    exact hi₀d.ne (by simp only [d, hcz i₀ h, mul_zero])
  let t := p i₀ / -d i₀
  have ht : 0 ≤ t := div_nonneg (hp i₀) (neg_nonneg.mpr hi₀d.le)
  let q (i : ι) := p i + t * d i
  have hq (i : ι) : 0 ≤ q i := by
    by_cases hi : d i < 0
    · have hti : t ≤ p i / -d i := hmin i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
      have hei := (le_div_iff₀ (neg_pos.mpr hi)).mp hti
      change 0 ≤ p i + t * d i
      linarith
    · exact add_nonneg (hp i) (mul_nonneg ht (le_of_not_gt hi))
  have hq₀ : q i₀ = 0 := by
    dsimp only [q, t]
    field_simp [hi₀d.ne] <;> ring
  have hqcard : (Finset.univ.filter fun i => q i ≠ 0).card < S.card := by
    apply lt_of_le_of_lt (Finset.card_le_card ?_) (Finset.card_erase_lt_of_mem hi₀S)
    intro i hi
    have hqi := (Finset.mem_filter.mp hi).2
    refine Finset.mem_erase.mpr ⟨?_, ?_⟩
    · intro hei
      subst i
      exact hqi hq₀
    · by_contra h
      have hpi : p i = 0 := by simpa [S] using h
      exact hqi (by simp only [q, d, hcz i h, hpi, mul_zero, add_zero])
  have hqsum (f : ι → ℝ) :
      (∑ i, q i * f i) = (∑ i, p i * f i) + t * ∑ i, d i * f i := by
    simp only [q, add_mul, mul_assoc, Finset.sum_add_distrib, Finset.mul_sum]
  refine ⟨q, hq, ?_, ?_, ?_, hqcard⟩
  · simpa only [mul_one, hmass, hd0, mul_zero, add_zero] using hqsum (fun _ => 1)
  · intro j
    rw [hqsum, hdy, mul_zero, add_zero]
  · rw [hqsum]
    exact le_add_of_nonneg_right (mul_nonneg ht hdscore)

/-- With three real moments fixed, a linear objective on the probability
simplex can be improved using at most four labels. -/
theorem exists_four_label_weights (y : ι → Fin 3 → ℝ) (score p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hmass : ∑ i, p i = 1) :
    ∃ q : ι → ℝ, (∀ i, 0 ≤ q i) ∧ (∑ i, q i) = 1 ∧
      (∀ j, (∑ i, q i * y i j) = ∑ i, p i * y i j) ∧
      (∑ i, p i * score i) ≤ (∑ i, q i * score i) ∧
      (Finset.univ.filter fun i => q i ≠ 0).card ≤ 4 := by
  classical
  let c (w : ι → ℝ) := (Finset.univ.filter fun i => w i ≠ 0).card
  generalize hc : c p = n
  induction n using Nat.strong_induction_on generalizing p with
  | h n ih =>
    by_cases hn : n ≤ 4
    · exact ⟨p, hp, hmass, fun _ => rfl, le_rfl, by change c p ≤ 4; rwa [hc]⟩
    · have hlarge : 4 < c p := by rw [hc]; omega
      obtain ⟨q, hq, hqmass, hqy, hqscore, hqcard⟩ := simplex_step y score p hp hmass hlarge
      have hqn : c q < n := by rw [← hc]; exact hqcard
      obtain ⟨w, hw, hwmass, hwy, hwscore, hwcard⟩ := ih (c q) hqn q hq hqmass rfl
      exact ⟨w, hw, hwmass, fun j => (hwy j).trans (hqy j), hqscore.trans hwscore, hwcard⟩

private def signed_mean_square (x y : ι → Fin 3 → ℝ) (p : ι → ℝ) : ℝ :=
  ∑ j, ((∑ i, p i * x i j)^2 - (∑ i, p i * y i j)^2)

/-- The support quadratic can be improved on a face supported on at most
four labels by fixing its three negative square coordinates. -/
private theorem exists_four_label_quadratic_weights (x y : ι → Fin 3 → ℝ) (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hmass : ∑ i, p i = 1) :
    ∃ q : ι → ℝ, (∀ i, 0 ≤ q i) ∧ (∑ i, q i) = 1 ∧
      signed_mean_square x y p ≤ signed_mean_square x y q ∧
      (Finset.univ.filter fun i => q i ≠ 0).card ≤ 4 := by
  let X (w : ι → ℝ) (j : Fin 3) := ∑ i, w i * x i j
  let score (i : ι) := ∑ j, X p j * x i j
  have hpair (w : ι → ℝ) :
      (∑ i, w i * score i) = ∑ j, X p j * X w j := by
    simp only [score, X, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    ring
  obtain ⟨q, hq, hqm, hqy, hscore, hqcard⟩ := exists_four_label_weights y score p hp hmass
  refine ⟨q, hq, hqm, ?_, hqcard⟩
  rw [hpair p, hpair q] at hscore
  have hs : 0 ≤ ∑ j, (X q j - X p j)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  unfold signed_mean_square
  simp only [hqy]
  change (∑ j, ((X p j)^2 - (∑ i, p i * y i j)^2)) ≤
    ∑ j, ((X q j)^2 - (∑ i, p i * y i j)^2)
  simp only [Fin.sum_univ_three] at hs hscore ⊢
  nlinarith

private def pairCompression (a b : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun i j => (if i = 0 then 1 else b) * (a + b)⁻¹ * (if j = 0 then a else 1)

private def traceCoordinates : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] (Fin 3 → ℂ) where
  toFun N := ![N 0 0 - N 1 1, N 0 1 + N 1 0, Complex.I * (N 0 1 - N 1 0)]
  map_add' A B := by
    funext j
    fin_cases j <;> simp [Matrix.add_apply, Pi.add_apply] <;> ring
  map_smul' c A := by
    funext j
    fin_cases j <;> simp [Matrix.smul_apply, Pi.smul_apply, smul_eq_mul] <;> ring

private theorem householder_support_squares (a b v : ι → ℂ) (η w : ℂ)
    (hw : w^2 = η * matchingProduct a b 1) (hv : ∑ i, star (v i) * v i = 1)
    (hreg : ∀ i, a i + b i ≠ 0) :
    let C (i : ι) (j : Fin 3) := w * traceCoordinates (pairCompression (a i) (b i)) j
    (η * determinantValue a b (rankOnePhase v (-1))).re =
      signed_mean_square (fun i j => (C i j).re) (fun i j => (C i j).im)
        (fun i => Complex.normSq (v i)) := by
  let C (i : ι) (j : Fin 3) := w * traceCoordinates (pairCompression (a i) (b i)) j
  let N := rankOneSpectralCompression a b v
  have hN : N = ∑ i, (Complex.normSq (v i) : ℂ) • pairCompression (a i) (b i) := by
    ext j k : 1
    simp only [N, rankOneSpectralCompression, pairCompression, Matrix.of_apply, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul, Complex.normSq_eq_conj_mul_self, starRingEnd_apply,
      div_eq_mul_inv]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hM (j : Fin 3) : w * traceCoordinates N j = ∑ i, (Complex.normSq (v i) : ℂ) * C i j := by
    rw [hN, map_sum]
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, C]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have htr : N 0 0 + N 1 1 = 1 := rankOneSpectralCompression_diagonal_sum a b v hv hreg
  have hQ : w^2 * (1 - 4 * N.det) = ∑ j, (w * traceCoordinates N j)^2 := by
    rw [Matrix.det_fin_two, Fin.sum_univ_three]
    change _ = (w * (N 0 0 - N 1 1))^2 + (w * (N 0 1 + N 1 0))^2 +
      (w * (Complex.I * (N 0 1 - N 1 0)))^2
    linear_combination -(w^2 * (N 0 0 + N 1 1 + 1)) * htr -
      (w^2 * (N 0 1 - N 1 0)^2) * Complex.I_sq
  have hdet : η * determinantValue a b (rankOnePhase v (-1)) =
      ∑ j, (w * traceCoordinates N j)^2 := by
    rw [determinantValue_rankOnePhase a b v (-1) hv (by simp) hreg, ← mul_assoc]
    change (η * matchingProduct a b 1) * _ = _
    rw [← hw, ← hQ]
    change w^2 * (1 - (2 - (-1) - star (-1)) * N.det) = _
    norm_num [star_neg, star_one]
  have hRe (j : Fin 3) :
      (w * traceCoordinates N j).re = ∑ i, Complex.normSq (v i) * (C i j).re := by
    rw [hM j]
    simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
  have hIm (j : Fin 3) :
      (w * traceCoordinates N j).im = ∑ i, Complex.normSq (v i) * (C i j).im := by
    rw [hM j]
    simp only [Complex.im_sum, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, mul_zero, zero_add, add_zero]
  change _ = signed_mean_square (fun i j => (C i j).re) (fun i j => (C i j).im)
    (fun i => Complex.normSq (v i))
  unfold signed_mean_square
  rw [hdet, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_two, Complex.mul_re, hRe, hIm, ← pow_two, ← pow_two]

private theorem holds_rankOnePhase_of_support (a b v : ι → ℂ) (z : ℂ) (S : Finset ι)
    (hS : S.card ≤ 4) (hv : ∑ i, star (v i) * v i = 1) (hz : z * star z = 1)
    (hzero : ∀ i ∉ S, v i = 0) : Holds a b (rankOnePhase v z) := by
  classical
  let T := {i : ι // i ∉ S}
  let e : S ⊕ T ≃ ι := Equiv.sumCompl (fun i => i ∈ S)
  let a₁ (i : S) := a i
  let b₁ (i : S) := b i
  let a₂ (i : T) := a i
  let b₂ (i : T) := b i
  let v₁ (i : S) := v i
  have hv₁ : ∑ i, star (v₁ i) * v₁ i = 1 := calc
    _ = ∑ i ∈ S, star (v i) * v i := Finset.sum_coe_sort _ _
    _ = ∑ i, star (v i) * v i := Finset.sum_subset (Finset.subset_univ S)
      (fun i _ hi => by simp [hzero i hi])
    _ = 1 := hv
  have hV : Holds a₁ b₁ (rankOnePhase v₁ z) :=
    holds_rankOnePhase_of_card_le_four _ _ _ _ (by simpa using hS) hv₁ hz
  have hblock : (rankOnePhase v z).submatrix e e =
      fromBlocks (rankOnePhase v₁ z) 0 0 (1 : Matrix T T ℂ) := by
    ext i j : 1
    rcases i with i | i <;> rcases j with j | j
    · change rankOnePhase v z (i : ι) (j : ι) = rankOnePhase v₁ z i j
      simp [v₁, rankOnePhase, Matrix.one_apply, Matrix.vecMulVec_apply, Subtype.ext_iff]
    · change rankOnePhase v z (i : ι) (j : ι) = 0
      have hn : (i : ι) ≠ j := fun h => j.property (h ▸ i.property)
      simp [rankOnePhase, Matrix.one_apply_ne hn, Matrix.vecMulVec_apply, hzero j j.property]
    · change rankOnePhase v z (i : ι) (j : ι) = 0
      have hn : (i : ι) ≠ j := fun h => i.property (h.symm ▸ j.property)
      simp [rankOnePhase, Matrix.one_apply_ne hn, Matrix.vecMulVec_apply, hzero i i.property]
    · change rankOnePhase v z (i : ι) (j : ι) = (1 : Matrix T T ℂ) i j
      simp [rankOnePhase, Matrix.one_apply, Matrix.vecMulVec_apply, Subtype.ext_iff,
        hzero i i.property]
  have ha : a ∘ e = Sum.elim a₁ a₂ := by funext j; cases j <;> rfl
  have hb : b ∘ e = Sum.elim b₁ b₂ := by funext j; cases j <;> rfl
  apply (holds_reindex_iff e e a b (rankOnePhase v z)).mp
  rw [ha, hb, hblock]
  exact holds_directSum _ _ _ _ _ _ hV (holds_identity a₂ b₂)

private theorem holds_householder_regular (a b v : ι → ℂ)
    (hv : ∑ i, star (v i) * v i = 1) (hreg : ∀ i, a i + b i ≠ 0) :
    Holds a b (rankOnePhase v (-1)) := by
  classical
  apply (holds_iff_directional a b _).mpr
  intro η
  let w : ℂ := (η * matchingProduct a b 1) ^ ((2 : ℂ)⁻¹)
  have hw : w^2 = η * matchingProduct a b 1 :=
    Complex.cpow_nat_inv_pow _ (by decide : (2 : ℕ) ≠ 0)
  let C (i : ι) (j : Fin 3) := w * traceCoordinates (pairCompression (a i) (b i)) j
  let x (i : ι) (j : Fin 3) := (C i j).re
  let y (i : ι) (j : Fin 3) := (C i j).im
  let p (i : ι) := Complex.normSq (v i)
  have hpMass : (∑ i, p i) = 1 := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_sum, Complex.ofReal_one]
    simpa only [p, Complex.normSq_eq_conj_mul_self, starRingEnd_apply] using hv
  obtain ⟨q, hq, hqMass, hqDom, hqCard⟩ := exists_four_label_quadratic_weights x y p
    (fun i => Complex.normSq_nonneg _) hpMass
  let u (i : ι) : ℂ := (Real.sqrt (q i) : ℝ)
  have huWeight (i : ι) : star (u i) * u i = (q i : ℂ) := by
    dsimp only [u]
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (hq i)]
  have huMass : ∑ i, star (u i) * u i = 1 := by
    simp_rw [huWeight, ← Complex.ofReal_sum, hqMass, Complex.ofReal_one]
  have huNormSq (i : ι) : Complex.normSq (u i) = q i := by
    apply Complex.ofReal_injective
    simpa only [Complex.normSq_eq_conj_mul_self, starRingEnd_apply] using huWeight i
  let S := Finset.univ.filter fun i => q i ≠ 0
  have huZero (i : ι) (hi : i ∉ S) : u i = 0 := by
    have hqi : q i = 0 := by simpa [S] using hi
    simp [u, hqi]
  have huH : Holds a b (rankOnePhase u (-1)) :=
    holds_rankOnePhase_of_support a b u (-1) S hqCard huMass (by simp) huZero
  have hdom : (η * determinantValue a b (rankOnePhase v (-1))).re ≤
      (η * determinantValue a b (rankOnePhase u (-1))).re := by
    rw [householder_support_squares a b v η w hw hv hreg,
      householder_support_squares a b u η w hw huMass hreg]
    change signed_mean_square x y p ≤ signed_mean_square x y (fun i => Complex.normSq (u i))
    simpa only [huNormSq] using hqDom
  obtain ⟨σ, hσ⟩ := (holds_iff_directional _ _ _).mp huH η
  exact ⟨σ, hdom.trans hσ⟩

/-- The determinant hull inclusion for an arbitrary-order Householder reflection. -/
theorem holds_householder (a b v : ι → ℂ) (hv : ∑ i, star (v i) * v i = 1) :
    Holds a b (rankOnePhase v (-1)) := by
  classical
  apply (holds_iff_directional a b _).mpr
  intro η
  by_contra! hbad
  let A (t : ℂ) (i : ι) := a i + t
  let U := rankOnePhase v (-1)
  let K : Set ℂ := Set.range fun i : ι => -(a i + b i)
  let O (σ : Equiv.Perm ι) : Set ℂ := {t |
    (η * matchingProduct (A t) b σ).re < (η * determinantValue (A t) b U).re}
  have hK : Dense Kᶜ := (Set.finite_range _).countable.dense_compl ℂ
  have hA : Continuous A := continuous_pi fun _ => continuous_const.add continuous_id
  have hA₀ : A 0 = a := by funext i; simp [A]
  have hO (σ : Equiv.Perm ι) : IsOpen (O σ) := by
    have hmatch : Continuous (fun t => matchingProduct (A t) b σ) := by
      unfold matchingProduct
      exact continuous_finset_prod _ fun i _ =>
        ((continuous_apply (σ i)).comp hA).add continuous_const
    have hdet : Continuous (fun t => determinantValue (A t) b U) := by
      unfold determinantValue
      fun_prop
    apply isOpen_lt <;> fun_prop
  have hOnonempty : (⋂ σ, O σ).Nonempty := ⟨0, Set.mem_iInter.mpr (fun σ => by
    change (η * matchingProduct (A 0) b σ).re < (η * determinantValue (A 0) b U).re
    rw [hA₀]
    exact hbad σ)⟩
  obtain ⟨t, htK, htO⟩ := hK.exists_mem_open (isOpen_iInter_of_finite hO) hOnonempty
  have hreg (i : ι) : A t i + b i ≠ 0 := by
    intro h
    apply htK
    refine ⟨i, ?_⟩
    change a i + t + b i = 0 at h
    linear_combination -h
  obtain ⟨σ, hσ⟩ := (holds_iff_directional _ _ _).mp
    (holds_householder_regular (A t) b v hv hreg) η
  have htO' : ∀ σ, t ∈ O σ := Set.mem_iInter.mp htO
  exact (not_le_of_gt (htO' σ)) hσ

/-- The determinant hull inclusion for every rank-one unitary phase update. -/
theorem holds_rankOnePhase (a b v : ι → ℂ) (z : ℂ)
    (hv : ∑ i, star (v i) * v i = 1) (hz : z * star z = 1) :
    Holds a b (rankOnePhase v z) :=
  holds_rankOnePhase_of_householder a b v z hv hz (holds_householder a b v hv)

end

end MOC
