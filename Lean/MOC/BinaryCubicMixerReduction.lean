import MOC.TwoByTwoTensorPermutationLaw

/-! The binary cubic mixer reduces to a one-real-parameter rotation
for the determinant hull comparison. At squared sine two fifths it lies
outside the common-minor permutation polytope. -/

open BigOperators Finset Matrix

namespace MOC

noncomputable section

private def cubicEntries {R : Type*} [CommRing R] (r a b c d : R) :
    Matrix (Fin 4) (Fin 4) R :=
  !![a^3, r*a^2*b, r*a*b^2, b^3;
    r*a^2*c, a^2*d + 2*a*b*c, 2*a*b*d + b^2*c, r*b^2*d;
    r*a*c^2, 2*a*c*d + b*c^2, a*d^2 + 2*b*c*d, r*b*d^2;
    c^3, r*c^2*d, r*c*d^2, d^3]

/-- The symmetric cube written in the basis
`x³, √3 x²y, √3 xy², y³` of normalized monomials. -/
def binaryCubicMixer (G : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  cubicEntries (Real.sqrt 3 : ℝ) (G 0 0) (G 0 1) (G 1 0) (G 1 1)

private def cubicRotation (c s : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  cubicEntries (Real.sqrt 3) c s (-s) c

/-- The real binary cubic induced by `[[c,s],[-s,c]]`. -/
def realBinaryCubicMixer (c s : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Complex.ofRealHom.mapMatrix (cubicRotation c s)

private theorem sqrtThree_sq : (Real.sqrt 3)^2 = 3 := by
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

private theorem cubic_map_real (r a b c d : ℝ) :
    Complex.ofRealHom.mapMatrix (cubicEntries r a b c d) =
      cubicEntries (r : ℂ) (a : ℂ) (b : ℂ) (c : ℂ) (d : ℂ) := by
  ext i j : 1
  fin_cases i <;> fin_cases j <;>
    simp [cubicEntries, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
      Matrix.cons_val, Complex.ofRealHom_eq_coe, Complex.ofReal_add, Complex.ofReal_mul,
      Complex.ofReal_pow, Complex.ofReal_ofNat]

private theorem cubicRotation_gram (c s : ℝ) :
    cubicRotation c s * (cubicRotation c s)ᵀ =
      (c^2+s^2)^3 • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  have h := sqrtThree_sq
  ext i j : 1
  fin_cases i <;> fin_cases j <;>
    norm_num [cubicRotation, cubicEntries, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.smul_apply, Matrix.one_apply, Fin.sum_univ_four, Matrix.of_apply,
      Matrix.cons_val, smul_eq_mul] <;> first
      | ring
      | linear_combination c^2*s^2*(c^2+s^2) * h

theorem realBinaryCubicMixer_unitary (c s : ℝ) (h : c^2+s^2 = 1) :
    IsUnitary (realBinaryCubicMixer c s) := by
  have hstar : (realBinaryCubicMixer c s)ᴴ = Complex.ofRealHom.mapMatrix (cubicRotation c s)ᵀ := by
    ext i j : 1
    simp [realBinaryCubicMixer, Matrix.conjTranspose_apply, RingHom.mapMatrix_apply,
      Matrix.map_apply, Matrix.transpose_apply, Complex.star_def]
  have hg : cubicRotation c s * (cubicRotation c s)ᵀ = 1 := by
    rw [cubicRotation_gram, h, one_pow, one_smul]
  have hU : realBinaryCubicMixer c s * (realBinaryCubicMixer c s)ᴴ = 1 := by
    rw [hstar, realBinaryCubicMixer, ← Complex.ofRealHom.mapMatrix.map_mul, hg, map_one]
  exact ⟨hU, Matrix.mul_eq_one_comm.mp hU⟩

private theorem unitary_two_by_two_coordinates (G : Matrix (Fin 2) (Fin 2) ℂ)
    (hG : IsUnitary G) (hdet : G.det = 1) :
    G 1 0 = -star (G 0 1) ∧ G 1 1 = star (G 0 0) ∧
    Complex.normSq (G 0 0) + Complex.normSq (G 0 1) = 1 := by
  let K : Matrix (Fin 2) (Fin 2) ℂ := !![G 1 1, -G 0 1; -G 1 0, G 0 0]
  have h : G 0 0 * G 1 1 - G 0 1 * G 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using hdet
  have hKG : K * G = 1 := by
    ext i j : 1
    fin_cases i <;> fin_cases j <;>
      norm_num [K, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_two, Matrix.of_apply,
        Matrix.cons_val] <;> first | ring | linear_combination h
  have hK : K = Gᴴ := calc
    K = K * (G * Gᴴ) := by rw [hG.1, Matrix.mul_one]
    _ = Gᴴ := by rw [← Matrix.mul_assoc, hKG, Matrix.one_mul]
  have h₀ : -(G 0 1) = star (G 1 0) :=
    congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) hK
  have h₁ : G 1 1 = star (G 0 0) :=
    congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) hK
  have hrow : G 0 0 * star (G 0 0) + G 0 1 * star (G 0 1) = 1 := by
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq, Fin.sum_univ_two]
      using congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) hG.1
  refine ⟨?_, h₁, ?_⟩
  · simpa only [star_star, star_neg] using (congrArg star h₀).symm
  · apply Complex.ofReal_injective
    rw [Complex.ofReal_add, Complex.ofReal_one, Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_conj_mul_self]
    simpa only [Complex.star_def, mul_comm] using hrow

private def cubeRowScale (z : ℂ) : Fin 4 → ℂ := ![1,z,z^2,z^3]

private def cubeColumnScale (u v : ℂ) : Fin 4 → ℂ := ![u^3,u^2*v,u*v^2,v^3]

private theorem cubic_phase_covariance (r a b c d z u v : ℂ) :
    cubicEntries r (a*u) (b*v) (z*c*u) (z*d*v) =
      diagonal (cubeRowScale z) * cubicEntries r a b c d * diagonal (cubeColumnScale u v) := by
  ext i j : 1
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;>
    simp [cubicEntries, cubeRowScale, cubeColumnScale, Matrix.of_apply, Matrix.cons_val] <;> ring

private theorem phase_mul_star_self (x : ℂ) (h : Complex.normSq x = 1) : star x * x = 1 := by
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, h, Complex.ofReal_one]

private theorem complexCube_diag_phase (G : Matrix (Fin 2) (Fin 2) ℂ)
    (hG : IsUnitary G) (hdet : G.det = 1) :
    ∃ (c s : ℝ) (l r : Fin 4 → ℂ), 0 ≤ c ∧ 0 ≤ s ∧ c^2+s^2 = 1 ∧
      (∀ i, Complex.normSq (l i) = 1) ∧ (∀ i, Complex.normSq (r i) = 1) ∧
      binaryCubicMixer G = diagonal l * realBinaryCubicMixer c s * diagonal r := by
  obtain ⟨hg10, hg11, hnorm⟩ := unitary_two_by_two_coordinates G hG hdet
  obtain ⟨u, hu, hg00⟩ := scalar_phase (G 0 0)
  obtain ⟨v, hv, hg01⟩ := scalar_phase (G 0 1)
  let c := ‖G 0 0‖
  let s := ‖G 0 1‖
  let z := star v * star u
  have hz : Complex.normSq z = 1 := by
    simp only [z, Complex.star_def, Complex.normSq_mul, Complex.normSq_conj, hu, hv, one_mul]
  have hzu : z * u = star v := by rw [z, mul_assoc, phase_mul_star_self u hu, mul_one]
  have hzv : z * v = star u := by
    rw [z, mul_comm (star v) (star u), mul_assoc, phase_mul_star_self v hv, mul_one]
  have hg10' : G 1 0 = z * (-(s : ℂ)) * u := calc
    G 1 0 = -(s : ℂ) * star v := by
      rw [hg10, hg01, star_mul', Complex.star_def, Complex.conj_ofReal, neg_mul]
    _ = z * (-(s : ℂ)) * u := by rw [← hzu]; ring
  have hg11' : G 1 1 = z * (c : ℂ) * v := calc
    G 1 1 = (c : ℂ) * star u := by rw [hg11, hg00, star_mul', Complex.star_def, Complex.conj_ofReal]
    _ = z * (c : ℂ) * v := by rw [← hzv]; ring
  refine ⟨c, s, cubeRowScale z, cubeColumnScale u v, norm_nonneg _, norm_nonneg _, ?_, ?_, ?_, ?_⟩
  · simpa only [c, s, Complex.normSq_eq_norm_sq] using hnorm
  · intro i
    fin_cases i <;> simp [cubeRowScale, Matrix.cons_val, map_pow, hz]
  · intro i
    fin_cases i <;> simp [cubeColumnScale, Matrix.cons_val, Complex.normSq_mul, map_pow, hu, hv]
  · rw [binaryCubicMixer, hg00, hg01, hg10', hg11', realBinaryCubicMixer,
      cubicRotation, cubic_map_real, Complex.ofReal_neg]
    exact cubic_phase_covariance (Real.sqrt 3 : ℝ) (c : ℂ) (s : ℂ)
      (-(s : ℂ)) (c : ℂ) z u v

/-- The all-spectra claim for the symmetric cube of complex special
unitaries is equivalent to the claim on the real first-quadrant chart. -/
theorem binaryCubicMixer_holds_iff_real_chart :
    (∀ (G : Matrix (Fin 2) (Fin 2) ℂ), IsUnitary G → G.det = 1 →
      ∀ a b : Fin 4 → ℂ, Holds a b (binaryCubicMixer G)) ↔
    (∀ (c s : ℝ), 0 ≤ c → 0 ≤ s → c^2+s^2 = 1 →
      ∀ a b : Fin 4 → ℂ, Holds a b (realBinaryCubicMixer c s)) := by
  constructor
  · intro h c s _ _ hs a b
    let G : Matrix (Fin 2) (Fin 2) ℂ := !![(c : ℂ), (s : ℂ); -(s : ℂ), (c : ℂ)]
    have hsC : (c : ℂ)^2 + (s : ℂ)^2 = 1 := by exact_mod_cast hs
    have hGG : G * Gᴴ = 1 := by
      ext i j : 1
      fin_cases i <;> fin_cases j <;>
        norm_num [G, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
          Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val, Complex.star_def] <;>
        first | ring | linear_combination hsC
    have hdet : G.det = 1 := by
      norm_num [G, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val] <;> linear_combination hsC
    have hcubic : binaryCubicMixer G = realBinaryCubicMixer c s := by
      rw [binaryCubicMixer, realBinaryCubicMixer, cubicRotation, cubic_map_real, Complex.ofReal_neg] <;> rfl
    rw [← hcubic]
    exact h G ⟨hGG, Matrix.mul_eq_one_comm.mp hGG⟩ hdet a b
  · intro h G hG hdet a b
    obtain ⟨c, s, l, r, hc, hs, hn, hl, hr, he⟩ := complexCube_diag_phase G hG hdet
    unfold Holds
    rw [he, determinant_two_phases a b l r (realBinaryCubicMixer c s) hl hr]
    exact h c s hc hs hn a b

private theorem cubic_pair_square (c s : ℝ) (h : c^2+s^2 = 1)
    {i j k l : Fin 4} (hij : i ≠ j) (hkl : k ≠ l) :
    subsetMinorSq (realBinaryCubicMixer c s) {i,j} {k,l} =
      (cubicRotation c s i k * cubicRotation c s j l -
        cubicRotation c s i l * cubicRotation c s j k)^2 := by
  rw [subsetMinorSq_pair _ (realBinaryCubicMixer_unitary c s h) hij hkl]
  change Complex.normSq ((cubicRotation c s i k : ℂ) * (cubicRotation c s j l : ℂ) -
    (cubicRotation c s i l : ℂ) * (cubicRotation c s j k : ℂ)) = _
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.normSq_ofReal, ← pow_two]

private def cubicIndicator (p : Equiv.Perm (Fin 4)) (I J : Finset (Fin 4)) : ℤ :=
  if J.map p.toEmbedding = I then 1 else 0

private theorem cubic_facet_perm (p : Equiv.Perm (Fin 4)) :
    cubicIndicator p {0,1} {0,3} + cubicIndicator p {1,2} {0,3} +
      cubicIndicator p {2,3} {1,3} + cubicIndicator p {2,3} {0,3} -
      cubicIndicator p {0,2} {2,3} ≤ 1 := by
  have hb : ∀ i j k l : Fin 4, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
      (if ({i,l} : Finset (Fin 4)) = {0,1} then (1 : ℤ) else 0) +
      (if ({i,l} : Finset (Fin 4)) = {1,2} then 1 else 0) +
      (if ({j,l} : Finset (Fin 4)) = {2,3} then 1 else 0) +
      (if ({i,l} : Finset (Fin 4)) = {2,3} then 1 else 0) -
      (if ({k,l} : Finset (Fin 4)) = {0,2} then 1 else 0) ≤ 1 := by
    decide +kernel
  simpa only [cubicIndicator, Finset.map_insert, Finset.map_singleton, Equiv.toEmbedding_apply]
    using hb (p 0) (p 1) (p 2) (p 3)
      (p.injective.ne (by decide)) (p.injective.ne (by decide)) (p.injective.ne (by decide))
      (p.injective.ne (by decide)) (p.injective.ne (by decide)) (p.injective.ne (by decide))

private def cubicTwoFifths : Matrix (Fin 4) (Fin 4) ℂ :=
  realBinaryCubicMixer (Real.sqrt (3/5)) (Real.sqrt (2/5))

private theorem cubic_facet_value :
    subsetMinorSq cubicTwoFifths {0,1} {0,3} +
      subsetMinorSq cubicTwoFifths {1,2} {0,3} +
      subsetMinorSq cubicTwoFifths {2,3} {1,3} +
      subsetMinorSq cubicTwoFifths {2,3} {0,3} -
      subsetMinorSq cubicTwoFifths {0,2} {2,3} = 132/125 := by
  let c := Real.sqrt (3/5)
  let s := Real.sqrt (2/5)
  let r := Real.sqrt 3
  have hc : c^2 = 3/5 := Real.sq_sqrt (by norm_num)
  have hs : s^2 = 2/5 := Real.sq_sqrt (by norm_num)
  have hr : r^2 = 3 := sqrtThree_sq
  have hcs : c^2+s^2 = 1 := by rw [hc, hs]; norm_num
  let A := cubicRotation c s
  have h₁ : A 0 0 * A 1 3 - A 0 3 * A 1 0 = c^2*r*s^2 := by
    simp only [A, cubicRotation, cubicEntries, Matrix.of_apply, Matrix.cons_val]
    linear_combination c^2*r*s^2*hcs
  have h₂ : A 1 0 * A 2 3 - A 1 3 * A 2 0 = -3*c^2*s^2 := by
    simp only [A, cubicRotation, cubicEntries, Matrix.of_apply, Matrix.cons_val]
    linear_combination -r^2*c^2*s^2*hcs - c^2*s^2*hr
  have h₃ : A 2 1 * A 3 3 - A 2 3 * A 3 1 = -2*c^3*s := by
    simp only [A, cubicRotation, cubicEntries, Matrix.of_apply, Matrix.cons_val]
    linear_combination -2*c^3*s*hcs - c^3*s^3*hr
  have h₄ : A 2 0 * A 3 3 - A 2 3 * A 3 0 = c^2*r*s^2 := by
    simp only [A, cubicRotation, cubicEntries, Matrix.of_apply, Matrix.cons_val]
    linear_combination c^2*r*s^2*hcs
  have h₅ : A 0 2 * A 2 3 - A 0 3 * A 2 2 = 2*c*s^3 := by
    simp only [A, cubicRotation, cubicEntries, Matrix.of_apply, Matrix.cons_val]
    linear_combination 2*c*s^3*hcs + c^3*s^3*hr
  change subsetMinorSq (realBinaryCubicMixer c s) {0,1} {0,3} +
      subsetMinorSq (realBinaryCubicMixer c s) {1,2} {0,3} +
      subsetMinorSq (realBinaryCubicMixer c s) {2,3} {1,3} +
      subsetMinorSq (realBinaryCubicMixer c s) {2,3} {0,3} -
      subsetMinorSq (realBinaryCubicMixer c s) {0,2} {2,3} = 132/125
  rw [cubic_pair_square c s hcs (i := 0) (j := 1) (k := 0) (l := 3) (by decide) (by decide), h₁,
    cubic_pair_square c s hcs (i := 1) (j := 2) (k := 0) (l := 3) (by decide) (by decide), h₂,
    cubic_pair_square c s hcs (i := 2) (j := 3) (k := 1) (l := 3) (by decide) (by decide), h₃,
    cubic_pair_square c s hcs (i := 2) (j := 3) (k := 0) (l := 3) (by decide) (by decide), h₄,
    cubic_pair_square c s hcs (i := 0) (j := 2) (k := 2) (l := 3) (by decide) (by decide), h₅]
  calc
    _ = (c^2)^2*r^2*(s^2)^2 + 9*(c^2)^2*(s^2)^2 + 4*(c^2)^3*s^2 +
      (c^2)^2*r^2*(s^2)^2 - 4*c^2*(s^2)^3 := by ring
    _ = _ := by rw [hc, hs, hr]; norm_num

/-- At squared sine `2/5`, no probability law on permutations reproduces
all squared minors of the binary cubic mixer. -/
theorem no_binaryCubic_twoFifths_minor_law :
    ¬ ∃ w : Equiv.Perm (Fin 4) → ℝ,
      (∀ p, 0 ≤ w p) ∧ (∑ p, w p) = 1 ∧
      ∀ I J : Finset (Fin 4),
        subsetMinorSq (realBinaryCubicMixer (Real.sqrt (3/5)) (Real.sqrt (2/5))) I J =
          ∑ p ∈ univ.filter (fun p => J.map p.toEmbedding = I), w p := by
  intro ⟨w, hw, hs, hm⟩
  let δ (p : Equiv.Perm (Fin 4)) (I J : Finset (Fin 4)) : ℝ := cubicIndicator p I J
  have hsum (I J : Finset (Fin 4)) : ∑ p, w p * δ p I J = subsetMinorSq cubicTwoFifths I J := by
    change ∑ p, w p * δ p I J = subsetMinorSq
      (realBinaryCubicMixer (Real.sqrt (3/5)) (Real.sqrt (2/5))) I J
    rw [hm I J, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : J.map p.toEmbedding = I <;> simp [δ, cubicIndicator, hp]
  let F (p : Equiv.Perm (Fin 4)) := δ p {0,1} {0,3} + δ p {1,2} {0,3} +
      δ p {2,3} {1,3} + δ p {2,3} {0,3} - δ p {0,2} {2,3}
  have hF (p : Equiv.Perm (Fin 4)) : F p ≤ 1 := by
    dsimp only [F, δ]
    exact_mod_cast cubic_facet_perm p
  have hupper : ∑ p, w p * F p ≤ 1 := calc
    _ ≤ ∑ p, w p * 1 := Finset.sum_le_sum (fun p _ => mul_le_mul_of_nonneg_left (hF p) (hw p))
    _ = 1 := by simpa only [mul_one] using hs
  have he : ∑ p, w p * F p = 132/125 := by
    simp only [F, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, hsum]
    exact cubic_facet_value
  rw [he] at hupper
  norm_num at hupper

/-- A signed expansion with one negative coefficient places a strictly
violating nonnegative cost in the simplex region that has a positive
anchor coefficient. -/
theorem cubic_negative_cost_normalization {ι : Type*} [Fintype ι]
    (w r h : ι → ℝ) (p anchor : ℝ) (hp : p < 0) (hr : ∀ i, 0 < r i)
    (hbudget : ∀ i, 0 ≤ r i*w i+p) (hh : ∀ i, 0 ≤ h i) (ha : 0 ≤ anchor)
    (hneg : (∑ i, w i*h i) + (p/2)*anchor < 0) :
    0 < anchor ∧ (∀ i, 0 ≤ 2*h i/anchor) ∧ ∑ i, (2*h i/anchor)/r i < 1 := by
  have hw (i : ι) : 0 ≤ w i := by
    by_contra! hn
    have hprod : r i * w i < 0 := mul_neg_of_pos_of_neg (hr i) hn
    linarith only [hprod, hbudget i, hp]
  have hsum : 0 ≤ ∑ i, w i*h i :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (hh i))
  have hap : 0 < anchor := by
    by_contra! hn
    have ha0 : anchor = 0 := le_antisymm hn ha
    rw [ha0, mul_zero, add_zero] at hneg
    exact (not_lt_of_ge hsum) hneg
  have hpoint (i : ι) : -p * (h i/r i) ≤ w i*h i := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (hr i)).mpr
    have hm : -p ≤ r i*w i := by linarith only [hbudget i]
    calc
      _ ≤ (r i*w i)*h i := mul_le_mul_of_nonneg_right hm (hh i)
      _ = _ := by ring
  have hupper : (∑ i, w i*h i) < -p*(anchor/2) := by
    linarith only [hneg]
  have htotal : -p * (∑ i, h i/r i) ≤ ∑ i, w i*h i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => hpoint i)
  have hfrac : (∑ i, h i/r i) < anchor/2 :=
    (mul_lt_mul_left (neg_pos.mpr hp)).mp (htotal.trans_lt hupper)
  refine ⟨hap, fun i => div_nonneg (mul_nonneg (by norm_num) (hh i)) hap.le, ?_⟩
  have hs (i : ι) : (2*h i/anchor)/r i = (2/anchor)*(h i/r i) := by ring
  simp_rw [hs, ← Finset.mul_sum]
  calc
    _ < (2/anchor)*(anchor/2) := mul_lt_mul_of_pos_left hfrac (div_pos (by norm_num) hap)
    _ = 1 := by field_simp [hap.ne'] <;> ring

end

end MOC
