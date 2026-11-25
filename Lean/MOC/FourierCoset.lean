import MOC.CyclicFourier
import Mathlib.Tactic.LinearCombination

/-! For a full cyclic character coset on one side, Fourier mixing turns that
spectrum into a single weighted shift. Uniform cyclic matchings attain its
determinant after the intermediate character powers cancel. -/

open BigOperators Finset Matrix

namespace MOC

noncomputable section

variable {n : ℕ} [NeZero n]

/-- A full cyclic root-of-unity coset, including the common scalar. -/
def cyclicRootCoset (γ : ℂ) (j : ZMod n) : ℂ := γ * ZMod.stdAddChar j

private def cyclicShift (γ : ℂ) : Matrix (ZMod n) (ZMod n) ℂ :=
  fun i j => if i = j - 1 then γ else 0

private theorem fourier_conj_cyclicRootCoset (γ : ℂ) :
    cyclicFourier n * diagonal (cyclicRootCoset γ) * (cyclicFourier n)ᴴ = cyclicShift γ := by
  ext i k : 1
  let c : ℂ := ((Real.sqrt (n : ℝ))⁻¹ : ℝ)
  have hc : star c = c := Complex.conj_ofReal _
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have ht (j : ZMod n) :
      cyclicFourier n i j * cyclicRootCoset γ j * star (cyclicFourier n k j) =
        ((n : ℂ)⁻¹ * γ) * ZMod.stdAddChar (j * (i + 1 - k)) := by
    change c * ZMod.stdAddChar (i*j) * (γ * ZMod.stdAddChar j) *
      star (c * ZMod.stdAddChar (k*j)) = _
    simp only [star_mul', hc, cyclicCharacter_conj]
    calc
      _ = (c * c) * γ * ((ZMod.stdAddChar (i * j) * ZMod.stdAddChar j) *
          ZMod.stdAddChar (-(k * j))) := by ring
      _ = _ := by
        rw [show c * c = (n : ℂ)⁻¹ from cyclicFourier_scale_mul n,
          ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
        rw [show i*j+j+(-(k*j)) = j*(i+1-k) by ring]
  rw [Matrix.mul_apply]
  simp_rw [Matrix.mul_diagonal, Matrix.conjTranspose_apply, ht]
  rw [← Finset.mul_sum, AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar n)]
  have hk : i + 1 - k = 0 ↔ i = k - 1 := by rw [sub_eq_zero, eq_sub_iff_add_eq]
  by_cases h : i = k - 1
  · rw [if_pos (hk.mpr h), ZMod.card, cyclicShift, if_pos h]
    calc
      _ = ((n : ℂ)⁻¹ * n) * γ := by ring
      _ = γ := by rw [inv_mul_cancel₀ hn, one_mul]
  · simp [hk, h, cyclicShift]

private theorem cyclic_self_ne_prev [Fact (1 < n)] (j : ZMod n) : j ≠ j - 1 := by
  intro h
  apply (one_ne_zero : (1 : ZMod n) ≠ 0)
  linear_combination h

private theorem perm_eq_id_or_prev [Fact (1 < n)] (p : Equiv.Perm (ZMod n))
    (h : ∀ j, p j = j ∨ p j = j - 1) :
    p = 1 ∨ p = Equiv.addRight (-1) := by
  by_cases hfix : ∀ j, p j = j
  · exact Or.inl (Equiv.ext hfix)
  obtain ⟨j, hj⟩ := not_forall.mp hfix
  have hstep (k : ZMod n) (hk : p k = k - 1) : p (k - 1) = k - 1 - 1 := by
    refine (h (k - 1)).resolve_left ?_
    intro hfix'
    exact cyclic_self_ne_prev k (p.injective (hk.trans hfix'.symm))
  have hnat (m : ℕ) : p (j - (m : ZMod n)) = j - (m : ZMod n) - 1 := by
    induction m with
    | zero => simpa using (h j).resolve_left hj
    | succ m hm =>
      rw [Nat.cast_succ, sub_add_eq_sub_sub]
      exact hstep _ hm
  right
  ext x
  have hx : j - ((j - x).val : ZMod n) = x := by
    rw [ZMod.natCast_zmod_val]
    ring
  have hnx := hnat (j-x).val
  rw [hx] at hnx
  change p x = x + -1
  simpa only [sub_eq_add_neg] using hnx

private theorem det_add_weighted_cyclicShift [Fact (1 < n)] (a c : ZMod n → ℂ) (γ : ℂ) :
    (diagonal a + diagonal c * cyclicShift γ).det =
      (∏ i, a i) + (∏ i, c i) * (cyclicShift (n := n) γ).det := by
  classical
  let τ : Equiv.Perm (ZMod n) := Equiv.addRight (-1)
  let ε (p : Equiv.Perm (ZMod n)) : ℂ := ((Equiv.Perm.sign p : ℤ) : ℂ)
  let M := diagonal a + diagonal c * cyclicShift γ
  have hτ (j : ZMod n) : τ j = j - 1 := by
    change j + -1 = j - 1
    rw [sub_eq_add_neg]
  have hne : (1 : Equiv.Perm (ZMod n)) ≠ τ := by
    intro h
    have e : (0 : ZMod n) = 0 - 1 := by
      simpa only [hτ, Equiv.Perm.one_apply] using congrArg (fun p : Equiv.Perm (ZMod n) => p 0) h
    exact cyclic_self_ne_prev _ e
  have hshift : (cyclicShift (n := n) γ).det = ε τ * ∏ j : ZMod n, γ := by
    rw [Matrix.det_apply', Finset.sum_eq_single τ]
    · simp only [cyclicShift, hτ, if_true, ε]
    · intro p _ hp
      have hex : ∃ j : ZMod n, p j ≠ j - 1 := by
        by_contra! h
        exact hp (Equiv.ext (fun j => (h j).trans (hτ j).symm))
      obtain ⟨j, hj⟩ := hex
      rw [Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj), mul_zero]
    · simp
  have hmixed (p : Equiv.Perm (ZMod n)) (hp : p ∉ ({1,τ} : Finset (Equiv.Perm (ZMod n)))) :
      ε p * (∏ j, M (p j) j) = 0 := by
    have hex : ∃ j : ZMod n, p j ≠ j ∧ p j ≠ j - 1 := by
      by_contra h
      have hs (j : ZMod n) : p j = j ∨ p j = j - 1 := by
        by_cases h₀ : p j = j
        · exact Or.inl h₀
        by_cases h₁ : p j = j - 1
        · exact Or.inr h₁
        exact (h ⟨j, h₀, h₁⟩).elim
      exact hp (by simpa only [Finset.mem_insert, Finset.mem_singleton] using perm_eq_id_or_prev p hs)
    obtain ⟨j, h1, h2⟩ := hex
    rw [Finset.prod_eq_zero (Finset.mem_univ j)
      (by simp [M, Matrix.diagonal_mul, cyclicShift, h1, h2]), mul_zero]
  have hpass : (∑ p ∈ ({1,τ} : Finset (Equiv.Perm (ZMod n))), ε p * ∏ j, M (p j) j) =
      ∑ p, ε p * ∏ j, M (p j) j := by
    apply Finset.sum_subset (Finset.subset_univ _)
    exact fun p _ hp => hmixed p hp
  have hdiag (j : ZMod n) : M j j = a j := by
    simp [M, Matrix.diagonal_mul, cyclicShift, cyclic_self_ne_prev]
  have hmove (j : ZMod n) : M (τ j) j = c (τ j) * γ := by
    simp [M, Matrix.diagonal_mul, cyclicShift, hτ, (cyclic_self_ne_prev j).symm]
  change M.det = _
  rw [Matrix.det_apply', ← hpass, hshift]
  simp [ε, hne, hdiag, hmove, Finset.prod_mul_distrib, Equiv.prod_comp τ c]
  <;> ring

private theorem det_add_cyclicShift [Fact (1 < n)] (a : ZMod n → ℂ) (γ : ℂ) :
    (diagonal a + cyclicShift γ).det = (∏ i, a i) + (cyclicShift (n := n) γ).det := by
  simpa [Matrix.diagonal_one] using det_add_weighted_cyclicShift a (fun _ => 1) γ

private theorem sum_shifted_cyclic_products (a c : ZMod n → ℂ) (γ : ℂ) :
    (∑ t : ZMod n, ∏ j : ZMod n, (a (j+t) + c (j+t) * cyclicRootCoset γ j)) =
      (n : ℂ) * ((∏ i, a i) + (∏ i, c i) * (∏ j : ZMod n, cyclicRootCoset γ j)) := by
  let b : ZMod n → ℂ := cyclicRootCoset γ
  let T (J : Finset (ZMod n)) := (∏ j ∈ J, c j * b j) * ∏ i ∈ Jᶜ, a i
  change (∑ t : ZMod n, ∏ j : ZMod n, (a (j+t) + c (j+t) * b j)) =
    (n : ℂ) * ((∏ i, a i) + (∏ i, c i) * (∏ j, b j))
  have hshift (t i : ZMod n) : b (i + -t) = ZMod.stdAddChar (-t) * b i := by
    simp only [b, cyclicRootCoset, AddChar.map_add_eq_mul]
    ring
  have hprod (t : ZMod n) : (∏ j : ZMod n, (a (j+t) + c (j+t) * b j)) =
      ∑ J : Finset (ZMod n), ZMod.stdAddChar ((J.card : ZMod n) * (-t)) * T J := by
    have hraw : (∏ j : ZMod n, (a (j+t) + c (j+t) * b j)) =
        ∏ i : ZMod n, (ZMod.stdAddChar (-t) * (c i * b i) + a i) := by
      rw [← Equiv.prod_comp (Equiv.addRight (-t)) (fun j : ZMod n => a (j+t) + c (j+t) * b j)]
      apply Finset.prod_congr rfl
      intro i _
      change a (i + -t + t) + c (i + -t + t) * b (i + -t) = _
      rw [neg_add_cancel_right, hshift]
      ring
    rw [hraw, Fintype.prod_add]
    apply Finset.sum_congr rfl
    intro J _
    rw [Finset.prod_mul_distrib, Finset.prod_const, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]
    simp only [T, mul_assoc]
  have hchars (J : Finset (ZMod n)) :
      (∑ t : ZMod n, ZMod.stdAddChar ((J.card : ZMod n) * (-t))) =
      if (J.card : ZMod n) = 0 then (n : ℂ) else 0 := by
    have ht (t : ZMod n) : (J.card : ZMod n) * (-t) = t * (-(J.card : ZMod n)) := by ring
    simp_rw [ht]
    simpa only [neg_eq_zero, ZMod.card, Nat.cast_ite, Nat.cast_zero] using
      AddChar.sum_mulShift (-(J.card : ZMod n)) (ZMod.isPrimitive_stdAddChar n)
  simp_rw [hprod]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, hchars]
  let s : Finset (Finset (ZMod n)) := {∅, univ}
  have hproper (J : Finset (ZMod n)) (hJ : J ∉ s) : (J.card : ZMod n) ≠ 0 := by
    have hz : J ≠ ∅ := fun h => hJ (by simp [s, h])
    have hu : J ≠ univ := fun h => hJ (by simp [s, h])
    have hcard := Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hu)
    rw [Finset.card_univ, ZMod.card] at hcard
    intro hd
    exact hcard.not_le (Nat.le_of_dvd (Nat.pos_of_ne_zero (fun h => hz (Finset.card_eq_zero.mp h)))
      ((ZMod.natCast_zmod_eq_zero_iff_dvd J.card n).mp hd))
  have hsub :
      (∑ J ∈ s, (if (J.card : ZMod n) = 0 then (n : ℂ) else 0) * T J) =
      ∑ J : Finset (ZMod n), (if (J.card : ZMod n) = 0 then (n : ℂ) else 0) * T J := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro J _ hJ
    rw [if_neg (hproper J hJ), zero_mul]
  rw [← hsub]
  have hset : (∅ : Finset (ZMod n)) ≠ univ := by
    intro h
    have hi := Finset.mem_univ (0 : ZMod n)
    rw [← h] at hi
    simpa using hi
  simp [s, T, hset, ZMod.card, ZMod.natCast_self, mul_add, Finset.prod_mul_distrib]

private theorem sum_cyclic_coset_matchings (a : ZMod n → ℂ) (γ : ℂ) :
    (∑ t : ZMod n, matchingProduct a (cyclicRootCoset γ) (Equiv.addRight t)) =
      (n : ℂ) * ((∏ i, a i) + ∏ j : ZMod n, cyclicRootCoset γ j) := by
  simpa [matchingProduct, Equiv.addRight] using sum_shifted_cyclic_products a (fun _ => 1) γ

/-- A Fourier root-coset sum in order greater than one has only the two pure
products in its determinant. -/
theorem determinantValue_cyclicFourier_rootCoset [Fact (1 < n)] (a : ZMod n → ℂ) (γ : ℂ) :
    determinantValue a (cyclicRootCoset γ) (cyclicFourier n) =
      (∏ i, a i) + ∏ j : ZMod n, cyclicRootCoset γ j := by
  rw [determinantValue, fourier_conj_cyclicRootCoset, det_add_cyclicShift,
    ← fourier_conj_cyclicRootCoset, det_unitary_conjugation _ _ (cyclicFourier_unitary n),
    Matrix.det_diagonal]

private theorem cyclicFourier_order_one : cyclicFourier 1 = 1 := by
  ext i j : 1
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst i
  subst j
  simp [cyclicFourier, AddChar.map_zero_eq_one]

/-- Fourier mixing satisfies Marcus–de Oliveira in any positive order when
one spectrum is a common multiple of all the cyclic roots of unity in that
order. The other spectrum is arbitrary. -/
theorem holds_cyclicFourier_rootCoset (a : ZMod n → ℂ) (γ : ℂ) :
    Holds a (cyclicRootCoset γ) (cyclicFourier n) := by
  by_cases hdim : 1 < n
  · letI : Fact (1 < n) := ⟨hdim⟩
    let b : ZMod n → ℂ := cyclicRootCoset γ
    have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
    unfold Holds
    refine mem_convexHull_of_exists_fintype (fun _ : ZMod n => (n : ℝ)⁻¹)
      (fun t => matchingProduct a b (Equiv.addRight t))
      (fun _ => inv_nonneg.mpr (Nat.cast_nonneg _)) ?_ (fun t => ⟨Equiv.addRight t, rfl⟩) ?_
    · simp [ZMod.card, nsmul_eq_mul, hn]
    · simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast]
      rw [← Finset.mul_sum]
      change (n : ℂ)⁻¹ * (∑ t : ZMod n, matchingProduct a (cyclicRootCoset γ) (Equiv.addRight t)) = _
      rw [sum_cyclic_coset_matchings, determinantValue_cyclicFourier_rootCoset]
      have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
      rw [← mul_assoc, inv_mul_cancel₀ hnC, one_mul]
  · have hn : n = 1 := by have hn0 := NeZero.ne n; omega
    subst n
    rw [cyclicFourier_order_one]
    exact holds_identity _ _

/-- A fractional-linear image of the cyclic roots, in their Fourier order. -/
def fractionalRootCoset (p q r s : ℂ) (j : ZMod n) : ℂ :=
  (p * cyclicRootCoset 1 j + q) / (r * cyclicRootCoset 1 j + s)

/-- Clearing the denominators of a fractional root coset leaves a diagonal
plus a row-weighted cyclic shift. Its determinant has only two terms. -/
theorem determinantValue_cyclicFourier_fractionalRootCoset [Fact (1 < n)]
    (a : ZMod n → ℂ) (p q r s : ℂ) (h : ∀ j : ZMod n, r * cyclicRootCoset 1 j + s ≠ 0) :
    determinantValue a (fractionalRootCoset p q r s) (cyclicFourier n) =
      ((∏ i, (s * a i + q)) + (∏ i, (r * a i + p)) * (∏ j : ZMod n, cyclicRootCoset 1 j)) /
        (∏ j : ZMod n, (r * cyclicRootCoset 1 j + s)) := by
  let U := cyclicFourier n
  let x : ZMod n → ℂ := cyclicRootCoset 1
  let d (j : ZMod n) := r * x j + s
  let e (j : ZMod n) := p * x j + q
  let b : ZMod n → ℂ := fractionalRootCoset p q r s
  let D := U * diagonal d * Uᴴ
  let E := U * diagonal e * Uᴴ
  let X : Matrix (ZMod n) (ZMod n) ℂ := cyclicShift 1
  have hU : IsUnitary U := cyclicFourier_unitary n
  have hdiag : diagonal b * diagonal d = diagonal e := by
    rw [Matrix.diagonal_mul_diagonal]
    apply congrArg Matrix.diagonal
    funext j
    exact div_mul_cancel₀ (e j) (h j)
  have hmul : (diagonal a + U * diagonal b * Uᴴ) * D = diagonal a * D + E := by
    rw [Matrix.add_mul]
    congr 1
    change (U * diagonal b * Uᴴ) * (U * diagonal d * Uᴴ) = E
    calc
      _ = U * ((diagonal b * (Uᴴ * U)) * diagonal d) * Uᴴ := by simp only [Matrix.mul_assoc]
      _ = E := by rw [hU.2, Matrix.mul_one, hdiag]
  have haffine (u v : ℂ) : U * diagonal (fun j => u * x j + v) * Uᴴ = u • X + v • 1 := by
    have ht : diagonal (fun j => u * x j + v) =
        u • diagonal x + v • (1 : Matrix (ZMod n) (ZMod n) ℂ) := by
      ext i j : 1
      by_cases hij : i = j
      · subst j
        simp [smul_eq_mul]
      · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
    have hshift : U * diagonal x * Uᴴ = X := fourier_conj_cyclicRootCoset 1
    rw [ht]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, hshift, hU.1]
  have hnum : diagonal a * D + E = diagonal (fun i => s * a i + q) +
      diagonal (fun i => r * a i + p) * X := by
    rw [show D = r • X + s • 1 from haffine r s, show E = p • X + q • 1 from haffine p q,
      Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one]
    ext i j : 1
    by_cases hij : i = j
    · subst j
      simp [Matrix.diagonal_mul, smul_eq_mul]
      ring
    · simp [Matrix.diagonal_mul, smul_eq_mul, Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
      ring
  have hden : D.det = ∏ j, d j := by
    dsimp only [D]
    rw [det_unitary_conjugation U _ hU, Matrix.det_diagonal]
  have hx : X.det = ∏ j, x j := by
    dsimp only [X, x]
    rw [← fourier_conj_cyclicRootCoset, det_unitary_conjugation _ _ hU, Matrix.det_diagonal]
  apply (eq_div_iff (Finset.prod_ne_zero_iff.mpr (fun j _ => h j))).mpr
  have he := congrArg Matrix.det hmul
  rw [Matrix.det_mul, hden, hnum] at he
  change (diagonal a + U * diagonal b * Uᴴ).det * (∏ j, d j) =
    (diagonal (fun i => s * a i + q) + diagonal (fun i => r * a i + p) * cyclicShift 1).det at he
  rw [det_add_weighted_cyclicShift, show (cyclicShift (n := n) 1).det = ∏ j, x j from hx] at he
  exact he

private theorem holds_cyclicFourier_fractionalRootCoset_aux [Fact (1 < n)]
    (a : ZMod n → ℂ) (p q r s : ℂ) (h : ∀ j : ZMod n, r * cyclicRootCoset 1 j + s ≠ 0) :
    Holds a (fractionalRootCoset p q r s) (cyclicFourier n) := by
  let v (j : ZMod n) := r * cyclicRootCoset 1 j + s
  let b : ZMod n → ℂ := fractionalRootCoset p q r s
  let l (i : ZMod n) := s * a i + q
  let m (i : ZMod n) := r * a i + p
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hm (t : ZMod n) : matchingProduct a b (Equiv.addRight t) =
      (∏ j : ZMod n, (l (j+t) + m (j+t) * cyclicRootCoset 1 j)) / (∏ j, v j) := by
    rw [matchingProduct, ← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro j _
    change a (j+t) + (p * cyclicRootCoset 1 j + q) / v j =
      (l (j+t) + m (j+t) * cyclicRootCoset 1 j) / v j
    field_simp [show v j ≠ 0 from h j]
    dsimp only [v, l, m]
    ring
  unfold Holds
  refine mem_convexHull_of_exists_fintype (fun _ : ZMod n => (n : ℝ)⁻¹)
    (fun t => matchingProduct a b (Equiv.addRight t))
    (fun _ => inv_nonneg.mpr (Nat.cast_nonneg _)) ?_ (fun t => ⟨Equiv.addRight t, rfl⟩) ?_
  · simp [ZMod.card, nsmul_eq_mul, hn]
  · simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast, hm]
    rw [← Finset.mul_sum, ← Finset.sum_div, sum_shifted_cyclic_products]
    rw [determinantValue_cyclicFourier_fractionalRootCoset a p q r s h]
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
    rw [← mul_div_assoc, ← mul_assoc, inv_mul_cancel₀ hnC, one_mul]

/-- Uniform cyclic matchings give the determinant for a fractional root
coset. Only the denominators on that coset need to be nonzero. -/
theorem holds_cyclicFourier_fractionalRootCoset
    (a : ZMod n → ℂ) (p q r s : ℂ) (h : ∀ j : ZMod n, r * cyclicRootCoset 1 j + s ≠ 0) :
    Holds a (fractionalRootCoset p q r s) (cyclicFourier n) := by
  by_cases hdim : 1 < n
  · letI : Fact (1 < n) := ⟨hdim⟩
    exact holds_cyclicFourier_fractionalRootCoset_aux a p q r s h
  · have hn : n = 1 := by have hn0 := NeZero.ne n; omega
    subst n
    rw [cyclicFourier_order_one]
    exact holds_identity _ _

/-- An adjacent pair of unequal first-spectrum entries makes the Fourier
root-coset sum nonnormal in order at least three. -/
theorem not_isStarNormal_cyclicFourier_rootCoset (hn : 2 < n)
    (a : ZMod n → ℂ) (γ : ℂ) (hγ : γ ≠ 0) (i : ZMod n) (ha : a i ≠ a (i + 1)) :
    ¬ IsStarNormal (diagonal a +
      cyclicFourier n * diagonal (cyclicRootCoset γ) * (cyclicFourier n)ᴴ) := by
  rw [fourier_conj_cyclicRootCoset]
  letI : Fact (1 < n) := ⟨by omega⟩
  let C : Matrix (ZMod n) (ZMod n) ℂ := cyclicShift γ
  let j : ZMod n := i + 1
  have hij : i ≠ j := by
    intro h
    apply (one_ne_zero : (1 : ZMod n) ≠ 0)
    change i = i + 1 at h
    linear_combination -h
  have htwo : (2 : ZMod n) ≠ 0 := by
    intro h
    exact hn.not_le (Nat.le_of_dvd (by decide : 0 < 2)
      ((ZMod.natCast_zmod_eq_zero_iff_dvd 2 n).mp h))
  have hji : j ≠ i - 1 := by
    intro h
    apply htwo
    change i + 1 = i - 1 at h
    linear_combination h
  have hc : C i j = γ := by simp [C, j, cyclicShift]
  have hc' : C j i = 0 := by simp [C, cyclicShift, hji]
  have hcc : (C * Cᴴ) i j = 0 := by
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases h : i = k - 1
    · have h' : j ≠ k - 1 := fun he => hij (h.trans he.symm)
      have hz : C j k = 0 := if_neg h'
      rw [Matrix.conjTranspose_apply, hz, star_zero, mul_zero]
    · simp [C, cyclicShift, h]
  have hcc' : (Cᴴ * C) i j = 0 := by
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases h : k = i - 1
    · have h' : k ≠ j - 1 := by
        intro he
        apply hij
        linear_combination he - h
      have hz : C k j = 0 := if_neg h'
      rw [hz, mul_zero]
    · simp [C, cyclicShift, Matrix.conjTranspose_apply, h]
  intro hnormal
  have he := congrArg (fun M : Matrix (ZMod n) (ZMod n) ℂ => M i j)
    hnormal.star_comm_self.eq
  change ((diagonal a + C)ᴴ * (diagonal a + C)) i j =
    ((diagonal a + C) * (diagonal a + C)ᴴ) i j at he
  have he' : star (a i) * γ = γ * star (a j) := by
    simpa [Matrix.conjTranspose_add, Matrix.diagonal_conjTranspose, Matrix.add_mul,
      Matrix.mul_add, Matrix.add_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul,
      Matrix.mul_diagonal, Matrix.diagonal_apply_ne _ hij, hc, hc', hcc, hcc'] using he
  exact ha (star_injective (mul_left_cancel₀ hγ (by simpa [mul_comm] using he')))

private theorem prod_cyclicCharacter {ι : Type*} (s : Finset ι) (v : ι → ZMod n) :
    (∏ i ∈ s, ZMod.stdAddChar (v i)) = ZMod.stdAddChar (∑ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [hi, ih, AddChar.map_add_eq_mul]

/-- The two full fifth-root spectra have zero first and third moments and a
nonnormal Fourier sum. Every matching product is real, and the determinant
equals two, so the containing matching hull has empty planar interior. -/
theorem cyclicFourier_five_rootCosets_real_matching (a : ZMod 5 → ℂ)
    (ha : a = cyclicRootCoset 1) :
    (∑ i, a i) = 0 ∧ (∑ i, (a i)^3) = 0 ∧
    ¬ IsStarNormal (diagonal a + cyclicFourier 5 * diagonal a * (cyclicFourier 5)ᴴ) ∧
    (∀ σ : Equiv.Perm (ZMod 5), (matchingProduct a a σ).im = 0) ∧
    determinantValue a a (cyclicFourier 5) = 2 := by
  subst a
  let χ : AddChar (ZMod 5) ℂ := ZMod.stdAddChar
  have hchar : ∀ j : ZMod 5, cyclicRootCoset 1 j = χ j := by simp [cyclicRootCoset, χ]
  have hsum : (∑ j : ZMod 5, j) = 0 := by decide +kernel
  have hpow (j : ZMod 5) : χ j ^ 3 = χ (j * 3) := by
    simpa [nsmul_eq_mul, mul_comm] using (AddChar.map_nsmul_eq_pow χ 3 j).symm
  have hfirst : (∑ j : ZMod 5, χ j) = 0 := by
    simpa [χ, Nat.cast_ite] using AddChar.sum_mulShift (ψ := ZMod.stdAddChar) (1 : ZMod 5)
      (ZMod.isPrimitive_stdAddChar 5)
  have hthird : (∑ j : ZMod 5, χ j ^ 3) = 0 := by
    simp_rw [hpow]
    simpa [χ, Nat.cast_ite, show (3 : ZMod 5) ≠ 0 by decide] using
      AddChar.sum_mulShift (ψ := ZMod.stdAddChar) (3 : ZMod 5)
        (ZMod.isPrimitive_stdAddChar 5)
  simp only [hchar]
  refine ⟨hfirst, hthird, ?_, ?_, ?_⟩
  · apply not_isStarNormal_cyclicFourier_rootCoset (n := 5) (by decide) _ 1 one_ne_zero 0
    simpa only [hchar, zero_add] using
      (fun h : χ 0 = χ 1 => (show (0 : ZMod 5) ≠ 1 by decide) (ZMod.injective_stdAddChar h))
  · intro σ
    apply Complex.conj_eq_iff_im.mp
    change (starRingEnd ℂ) (matchingProduct (cyclicRootCoset 1) (cyclicRootCoset 1) σ) = _
    simp only [matchingProduct, hchar, map_prod, map_add, starRingEnd_apply]
    have hfactor (i j : ZMod 5) : star (χ i) + star (χ j) =
        χ (-i-j) * (χ i + χ j) := by
      simp only [χ, cyclicCharacter_conj, mul_add, ← AddChar.map_add_eq_mul]
      rw [show -i-j+i = -j by ring, show -i-j+j = -i by ring]
      exact add_comm _ _
    simp_rw [hfactor, Finset.prod_mul_distrib]
    have hzero : (∑ j : ZMod 5, (-(σ j)-j)) = 0 := by
      simp [Finset.sum_sub_distrib, Finset.sum_neg_distrib, Equiv.sum_comp σ (fun j => j), hsum]
    change (∏ j : ZMod 5, ZMod.stdAddChar (-σ j-j)) * _ = _
    rw [prod_cyclicCharacter univ (fun j : ZMod 5 => -(σ j)-j), hzero,
      AddChar.map_zero_eq_one, one_mul]
  · letI : Fact (1 < 5) := ⟨by decide⟩
    have hdet := determinantValue_cyclicFourier_rootCoset (n := 5) (cyclicRootCoset 1) 1
    simp only [hchar] at hdet
    have he : (∏ j : ZMod 5, χ j) = 1 := by
      change (∏ j : ZMod 5, ZMod.stdAddChar ((fun x : ZMod 5 => x) j)) = 1
      rw [prod_cyclicCharacter univ (fun j : ZMod 5 => j), hsum, AddChar.map_zero_eq_one]
    rw [hdet, he] <;> norm_num

end

end MOC
