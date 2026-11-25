import MOC.Collinear
import MOC.ReducingCommutant
import MOC.StationaryPhaseGraph
import MOC.StrongSupport

/-! At a least-order violation no support maximizer can have a normal sum. -/

open BigOperators Filter Matrix
open scoped Topology

namespace MOC

noncomputable section

private theorem two_labels_of_diagonal_support_maximum {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (h : ι → ℂ) (D : Matrix ι ι ℂ) (η : ℂ)
    (hD : D * Dᴴ = Dᴴ * D)
    (hA : (diagonal h - D) * (diagonal h - D)ᴴ = (diagonal h - D)ᴴ * (diagonal h - D))
    (hnz : ∀ i, h i ≠ 0) (hκ : (η * (diagonal h).det).re ≠ 0)
    (hwithin : ∀ i j, h i = h j → i ≠ j → D i j = 0)
    (hmax : ∀ R : Matrix ι ι ℂ, IsUnitary R →
      (η * (diagonal h - D + R * D * Rᴴ).det).re ≤ (η * (diagonal h).det).re)
    (hscalar : ∀ d : ι → ℂ, Commute (diagonal d) D → ∃ c : ℂ, ∀ i, d i = c) :
    ∃ x y : ℂ, ∀ i, h i = x ∨ h i = y := by
  classical
  have hne {i j : ι} (hij : i ≠ j) (hd : D i j ≠ 0) : h i ≠ h j :=
    fun he => hd (hwithin i j he hij)
  have hrev {i j : ι} (hij : i ≠ j) (hd : D i j ≠ 0) : D j i ≠ 0 := by
    intro hz
    have he := cross_entries_of_normal_diagonal_sum h D hD hA i j
    rw [hz, star_zero, zero_mul] at he
    exact mul_ne_zero (star_ne_zero.mpr (sub_ne_zero.mpr (hne hij hd))) hd he.symm
  let neighbor (i : ι) := if hi : ∃ j, j ≠ i ∧ D i j ≠ 0 then Classical.choose hi else i
  have hneighbor {i j : ι} (hij : i ≠ j) (hd : D i j ≠ 0) : h (neighbor i) = h j := by
    have hi : ∃ k, k ≠ i ∧ D i k ≠ 0 := ⟨j, hij.symm, hd⟩
    have hk := Classical.choose_spec hi
    change h (if h' : ∃ k, k ≠ i ∧ D i k ≠ 0 then Classical.choose h' else i) = h j
    rw [dif_pos hi]
    exact endpoints_eq_of_normal_diagonal_support_maximum h D η hD hA hnz hκ hmax
      (hne hk.1.symm hk.2).symm (hne hij hd) (hrev hk.1.symm hk.2) hd
      (fun l hl he => by rw [hwithin i l he hl.symm, zero_mul])
  have hcomm (f : ℂ → ℂ → ℂ) (hf : ∀ z w, f z w = f w z) :
      Commute (diagonal fun i => f (h i) (h (neighbor i))) D := by
    change diagonal (fun i => f (h i) (h (neighbor i))) * D =
      D * diagonal (fun i => f (h i) (h (neighbor i)))
    ext i j : 1
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hij : i = j
    · subst j
      exact mul_comm _ _
    by_cases hd : D i j = 0
    · simp [hd]
    · rw [hneighbor hij hd, hneighbor (Ne.symm hij) (hrev hij hd), hf (h i) (h j), mul_comm]
  obtain ⟨p, hp⟩ := hscalar _ (hcomm (· + ·) add_comm)
  obtain ⟨q, hq⟩ := hscalar _ (hcomm (· * ·) mul_comm)
  let k := Classical.choice (inferInstance : Nonempty ι)
  refine ⟨h k, h (neighbor k), fun i => ?_⟩
  have hs := (hp i).trans (hp k).symm
  have hm := (hq i).trans (hq k).symm
  have hr : (h i - h k) * (h i - h (neighbor k)) = 0 := by
    linear_combination h i * hs - hm
  exact (mul_eq_zero.mp hr).imp sub_eq_zero.mp sub_eq_zero.mp

private theorem scaled_skew_conj {ι : Type*} [Fintype ι]
    (c : ℂ) (W X : Matrix ι ι ℂ) :
    c • (W * X * Wᴴ) - star c • (W * X * Wᴴ)ᴴ =
      W * (c • X - star c • Xᴴ) * Wᴴ := by
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]

private theorem scaled_skew_diagonal {ι : Type*} [DecidableEq ι] (c : ℂ) (x : ι → ℂ) :
    c • diagonal x - star c • (diagonal x)ᴴ =
      diagonal (fun i => c * x i - star (c * x i)) := by
  rw [Matrix.diagonal_conjTranspose, ← Matrix.diagonal_smul, ← Matrix.diagonal_smul,
    Matrix.diagonal_sub]
  apply congrArg diagonal
  funext i
  simp [star_mul', mul_comm]

private theorem line_of_constant_scaled_skew {ι : Type*} (c : ℂ) (hc : c ≠ 0) (x : ι → ℂ)
    (μ : ℂ) (hμ : ∀ i, c * x i - star (c * x i) = μ) :
    x = fun i => c⁻¹ * ((c * x i).re : ℂ) + c⁻¹ * ((μ.im / 2 : ℝ) : ℂ) * Complex.I := by
  funext i
  have him := congrArg Complex.im (hμ i)
  simp only [Complex.sub_im, Complex.star_def, Complex.conj_im] at him
  have hi : (c * x i).im = μ.im / 2 := by linarith only [him]
  calc
    x i = c⁻¹ * (c * x i) := by rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    _ = _ := by
      conv_lhs => rw [← Complex.re_add_im (c * x i)]
      rw [hi]
      ring

/-- For an order whose smaller orders satisfy MOC, a normal orbit maximum
with nonzero real support satisfies the determinant hull inclusion. -/
theorem holds_of_normal_support_maximum_of_smaller_orders {n : ℕ} [Nonempty (Fin n)]
    (hbelow : ∀ m < n, Conjecture (Fin m)) (a b : Fin n → ℂ)
    {U : Matrix (Fin n) (Fin n) ℂ} (hU : IsUnitary U) (η : ℂ)
    (hC : IsStarNormal (diagonal a + U * diagonal b * Uᴴ))
    (hκ : (η * determinantValue a b U).re ≠ 0)
    (hmax : ∀ V : Matrix (Fin n) (Fin n) ℂ, IsUnitary V →
      (η * determinantValue a b V).re ≤ (η * determinantValue a b U).re) : Holds a b U := by
  classical
  by_contra hnot
  let A := diagonal a
  let B := U * diagonal b * Uᴴ
  have hB : Commute B Bᴴ :=
    commute_adjoint_of_commute_spectral_diagonalization b U B hU (Commute.refl B)
  have hA : Commute A Aᴴ := by
    change diagonal a * (diagonal a)ᴴ = (diagonal a)ᴴ * diagonal a
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    exact congrArg diagonal (funext fun i => mul_comm _ _)
  have hsup (R : Matrix (Fin n) (Fin n) ℂ) (hR : IsUnitary R) :
      (η * (A + R * B * Rᴴ).det).re ≤ (η * (A + B).det).re := by
    have hR' : IsUnitary Rᴴ := ⟨by simpa using hR.2, by simpa using hR.1⟩
    have hRU : IsUnitary (R * U) := by
      simpa only [Matrix.conjTranspose_conjTranspose] using relative_unitary Rᴴ U hR' hU
    simpa only [determinantValue, A, B, Matrix.conjTranspose_mul, Matrix.mul_assoc] using
      hmax (R * U) hRU
  have hscalar := scalar_of_commute_normal_pair_of_smaller_orders hbelow a b hU hnot
  obtain ⟨h, W, D, hW, hsum, hD, hAD, hwithin, hmax', hscalar'⟩ :=
    diagonal_chart_of_normal_support_maximum A B η hA.eq hB.eq hC hsup hscalar
  have hdet : determinantValue a b U = (diagonal h).det := by
    change (A + B).det = _
    rw [hsum, det_unitary_conjugation _ _ hW]
  have hκ' : (η * (diagonal h).det).re ≠ 0 := hdet ▸ hκ
  have hnz (i : Fin n) : h i ≠ 0 := by
    intro hz
    apply hκ'
    rw [Matrix.det_diagonal, Finset.prod_eq_zero (Finset.mem_univ i) hz, mul_zero]
    rfl
  obtain ⟨x, y, hxy⟩ := two_labels_of_diagonal_support_maximum h D η hD hAD hnz hκ'
    hwithin hmax' hscalar'
  have hline : ∃ c : ℂ, c ≠ 0 ∧ ∀ i, c * h i - star (c * h i) = c * y - star (c * y) := by
    by_cases he : x = y
    · refine ⟨1, one_ne_zero, fun i => ?_⟩
      rcases hxy i with hi | hi <;> simp [hi, he]
    · let c := (x - y)⁻¹
      have hc : c ≠ 0 := inv_ne_zero (sub_ne_zero.mpr he)
      have hx : c * x = c * y + 1 := by
        have hh : c * (x - y) = 1 := inv_mul_cancel₀ (sub_ne_zero.mpr he)
        rw [mul_sub] at hh
        linear_combination hh
      refine ⟨c, hc, fun i => ?_⟩
      rcases hxy i with hi | hi
      · rw [hi, hx, star_add, star_one]
        abel
      · rw [hi]
  obtain ⟨c, hc, hl⟩ := hline
  let ν := c * y - star (c * y)
  let skew (X : Matrix (Fin n) (Fin n) ℂ) := c • X - star c • Xᴴ
  have hdiag : skew (diagonal h) = ν • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    dsimp only [skew]
    rw [scaled_skew_diagonal, Matrix.smul_one_eq_diagonal]
    exact congrArg diagonal (funext hl)
  have hsumskew : skew A + skew B = ν • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    calc
      _ = skew (A + B) := by
        simp only [skew, Matrix.conjTranspose_add, smul_add]
        abel
      _ = W * skew (diagonal h) * Wᴴ := by rw [hsum]; exact scaled_skew_conj c W _
      _ = _ := by rw [hdiag, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hW.1]
  have hcomm (X : Matrix (Fin n) (Fin n) ℂ) (hX : Commute X Xᴴ) : Commute X (skew X) :=
    ((Commute.refl X).smul_right c).sub_right (hX.smul_right (star c))
  have hskewA : Commute A (skew B) := by
    rw [show skew B = ν • (1 : Matrix (Fin n) (Fin n) ℂ) - skew A by
      rw [← hsumskew]; abel]
    exact ((Commute.one_right A).smul_right ν).sub_right (hcomm A hA)
  obtain ⟨μ, hμ⟩ := hscalar (skew B) hskewA (hcomm B hB)
  have hμA : skew A = (ν - μ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [sub_smul, ← hsumskew, ← hμ, add_sub_cancel_right]
  have hda : ∀ i, c * a i - star (c * a i) = ν - μ := by
    rw [show skew A = _ from scaled_skew_diagonal c a, Matrix.smul_one_eq_diagonal] at hμA
    intro i
    simpa only [Matrix.diagonal_apply_eq] using congrArg (fun X : Matrix (Fin n) (Fin n) ℂ => X i i) hμA
  have hdb : ∀ i, c * b i - star (c * b i) = μ := by
    let E := diagonal fun i => c * b i - star (c * b i)
    have he : U * E * Uᴴ = μ • (1 : Matrix (Fin n) (Fin n) ℂ) := by
      dsimp only [E]
      rw [← scaled_skew_diagonal c b, ← scaled_skew_conj c U (diagonal b)]
      exact hμ
    have hE : E = μ • (1 : Matrix (Fin n) (Fin n) ℂ) := calc
      E = Uᴴ * (U * E * Uᴴ) * U := by
        rw [show Uᴴ * (U * E * Uᴴ) * U = (Uᴴ * U) * E * (Uᴴ * U) by
          simp only [Matrix.mul_assoc], hU.2, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by rw [he, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hU.2]
    rw [Matrix.smul_one_eq_diagonal] at hE
    intro i
    simpa only [E, Matrix.diagonal_apply_eq] using
      congrArg (fun X : Matrix (Fin n) (Fin n) ℂ => X i i) hE
  apply hnot
  rw [line_of_constant_scaled_skew c hc a (ν - μ) hda, line_of_constant_scaled_skew c hc b μ hdb]
  exact holds_of_parallel_affine_lines _ _ _ _ _ U hU

/-- A normal order-four support maximum with nonzero real support satisfies
the full determinant hull inclusion for those spectra and that unitary. -/
theorem holds_four_of_normal_support_maximum (a b : Fin 4 → ℂ)
    {U : Matrix (Fin 4) (Fin 4) ℂ} (hU : IsUnitary U) (η : ℂ)
    (hC : IsStarNormal (diagonal a + U * diagonal b * Uᴴ))
    (hκ : (η * determinantValue a b U).re ≠ 0)
    (hmax : ∀ V : Matrix (Fin 4) (Fin 4) ℂ, IsUnitary V →
      (η * determinantValue a b V).re ≤ (η * determinantValue a b U).re) : Holds a b U :=
  holds_of_normal_support_maximum_of_smaller_orders
    (fun m hm => conjecture_le_three (n := m) (Nat.le_of_lt_succ hm)) a b hU η hC hκ hmax

private theorem exists_nonzero_support_violation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℂ) {U : Matrix ι ι ℂ} (hU : IsUnitary U) (hbad : ¬ Holds a b U) :
    ∃ (V : Matrix ι ι ℂ) (η : ℂ), IsUnitary V ∧ (η * determinantValue a b V).re ≠ 0 ∧
      (∀ σ : Equiv.Perm ι, (η * matchingProduct a b σ).re < (η * determinantValue a b V).re) ∧
      (∀ W : Matrix ι ι ℂ, IsUnitary W →
        (η * determinantValue a b W).re ≤ (η * determinantValue a b V).re) := by
  rw [holds_iff_directional] at hbad
  push_neg at hbad
  obtain ⟨η, hsep⟩ := hbad
  obtain ⟨V, hV, hmax⟩ := exists_support_maximizer a b η
  have hs (σ : Equiv.Perm ι) := (hsep σ).trans_le (hmax U hU)
  by_cases hκ : (η * determinantValue a b V).re = 0
  · let d := determinantValue a b V
    have hd : d ≠ 0 := by
      intro hz
      obtain ⟨σ, hσ⟩ := (holds_iff_directional _ _ _).mp (holds_of_singular a b hV hz) η
      exact (not_le_of_gt (hs σ)) hσ
    let ξ (t : ℝ) := η + (t : ℂ) * star d
    have hnear : ∀ᶠ t : ℝ in 𝓝 0, ∀ σ : Equiv.Perm ι,
        (ξ t * matchingProduct a b σ).re < (ξ t * d).re := by
      apply eventually_all.mpr
      intro σ
      have h₁ : ContinuousAt (fun t : ℝ => (ξ t * matchingProduct a b σ).re) 0 := by
        unfold ξ
        fun_prop
      have h₂ : ContinuousAt (fun t : ℝ => (ξ t * d).re) 0 := by
        unfold ξ
        fun_prop
      exact h₁.eventually_lt h₂ (by simpa [ξ, d] using hs σ)
    obtain ⟨t, ht, htsep⟩ := ((frequently_gt_nhds (0 : ℝ)).and_eventually hnear).exists
    have hpos : 0 < (ξ t * d).re := by
      dsimp only [ξ]
      rw [add_mul, Complex.add_re, show (η * d).re = 0 from hκ, zero_add,
        mul_assoc, Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
        Complex.re_ofReal_mul, Complex.ofReal_re]
      exact mul_pos ht (Complex.normSq_pos.mpr hd)
    obtain ⟨W, hW, hmax'⟩ := exists_support_maximizer a b (ξ t)
    exact ⟨W, ξ t, hW, (hpos.trans_le (hmax' V hV)).ne',
      fun σ => (htsep σ).trans_le (hmax' V hV), hmax'⟩
  · exact ⟨V, η, hV, hκ, hs, hmax⟩

private theorem permutation_normal_realization {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℂ) (σ : Equiv.Perm ι) :
    ∃ U : Matrix ι ι ℂ, IsUnitary U ∧ IsStarNormal (diagonal a + U * diagonal b * Uᴴ) ∧
      determinantValue a b U = matchingProduct a b σ := by
  let U := Equiv.Perm.permMatrix ℂ σ.symm
  have hsum : diagonal a + U * diagonal b * Uᴴ = diagonal (a + b ∘ σ.symm) := by
    dsimp only [U]
    rw [permMatrix_conjugates, Matrix.submatrix_diagonal_equiv, Matrix.diagonal_add]
    rfl
  refine ⟨U, isUnitary_permMatrix σ.symm, ?_, ?_⟩
  · rw [hsum]
    constructor
    change (diagonal (a + b ∘ σ.symm))ᴴ * diagonal (a + b ∘ σ.symm) =
      diagonal (a + b ∘ σ.symm) * (diagonal (a + b ∘ σ.symm))ᴴ
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    exact congrArg diagonal (funext fun i => mul_comm _ _)
  · rw [determinantValue, hsum, Matrix.det_diagonal]
    simpa only [Pi.add_apply, Function.comp_apply, Equiv.symm_symm] using
      (matchingProduct_inverse a b σ.symm).symm

/-- In an order with all smaller orders proved, MOC is equivalent to existence
of a normal sum at some maximizer of each directional unitary orbit. -/
theorem conjecture_iff_exists_normal_support_maximizer_of_smaller_orders {n : ℕ}
    (hbelow : ∀ m < n, Conjecture (Fin m)) : Conjecture (Fin n) ↔
      ∀ (a b : Fin n → ℂ) (η : ℂ),
        ∃ U : Matrix (Fin n) (Fin n) ℂ, IsUnitary U ∧
          IsStarNormal (diagonal a + U * diagonal b * Uᴴ) ∧
          ∀ V : Matrix (Fin n) (Fin n) ℂ, IsUnitary V →
            (η * determinantValue a b V).re ≤ (η * determinantValue a b U).re := by
  classical
  constructor
  · intro h a b η
    obtain ⟨σ, _, hσ⟩ := Finset.exists_max_image Finset.univ
      (fun σ : Equiv.Perm (Fin n) => (η * matchingProduct a b σ).re) Finset.univ_nonempty
    obtain ⟨U, hU, hnormal, hdet⟩ := permutation_normal_realization a b σ
    refine ⟨U, hU, hnormal, fun V hV => ?_⟩
    obtain ⟨τ, hτ⟩ := (holds_iff_directional _ _ _).mp (h a b V hV) η
    rw [hdet]
    exact hτ.trans (hσ τ (Finset.mem_univ τ))
  · intro hex a b V hV
    by_cases hn : n = 0
    · subst n
      exact conjecture_le_three (by decide) a b V hV
    letI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
    by_contra hbad
    obtain ⟨W, η, hW, hκ, hsep, hmax⟩ := exists_nonzero_support_violation a b hV hbad
    obtain ⟨U, hU, hnormal, hmax'⟩ := hex a b η
    have heq := le_antisymm (hmax U hU) (hmax' W hW)
    have hκ' : (η * determinantValue a b U).re ≠ 0 := heq.symm ▸ hκ
    have hh := holds_of_normal_support_maximum_of_smaller_orders hbelow a b hU η hnormal hκ' hmax'
    obtain ⟨σ, hσ⟩ := (holds_iff_directional _ _ _).mp hh η
    exact (not_lt_of_ge (heq ▸ hσ)) (hsep σ)

/-- The order-four conjecture is equivalent to existence of a normal sum at
some maximizer of every directional unitary orbit. -/
theorem conjecture_four_iff_exists_normal_support_maximizer : Conjecture (Fin 4) ↔
    ∀ (a b : Fin 4 → ℂ) (η : ℂ),
      ∃ U : Matrix (Fin 4) (Fin 4) ℂ, IsUnitary U ∧
        IsStarNormal (diagonal a + U * diagonal b * Uᴴ) ∧
        ∀ V : Matrix (Fin 4) (Fin 4) ℂ, IsUnitary V →
          (η * determinantValue a b V).re ≤ (η * determinantValue a b U).re :=
  conjecture_iff_exists_normal_support_maximizer_of_smaller_orders
    (fun m hm => conjecture_le_three (n := m) (Nat.le_of_lt_succ hm))

/-- The conjecture in all orders is equivalent to existence of a normal sum
at some maximizer of every directional unitary orbit in orders at least four. -/
theorem mocIsTrue_iff_exists_normal_support_maximizer : MOCIsTrue ↔
    ∀ n : ℕ, 4 ≤ n → ∀ (a b : Fin n → ℂ) (η : ℂ),
      ∃ U : Matrix (Fin n) (Fin n) ℂ, IsUnitary U ∧
        IsStarNormal (diagonal a + U * diagonal b * Uᴴ) ∧
        ∀ V : Matrix (Fin n) (Fin n) ℂ, IsUnitary V →
          (η * determinantValue a b V).re ≤ (η * determinantValue a b U).re := by
  constructor
  · intro h n _
    exact (conjecture_iff_exists_normal_support_maximizer_of_smaller_orders
      (fun m _ => h m)).mp (h n)
  · intro h
    by_contra hbad
    obtain ⟨n, hn, hfail, hbelow⟩ := exists_least_bad_order hbad
    exact hfail ((conjecture_iff_exists_normal_support_maximizer_of_smaller_orders
      hbelow).mpr (h n hn))

end

end MOC
