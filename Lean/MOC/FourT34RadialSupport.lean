import MOC.FourContactCones
import MOC.FourT34HessianReduction
import MOC.FourT34PolynomialCertificate
import MOC.FourT34QuaternionGram
import MOC.ZeroHeight

/-! The T34 radial and response reductions expose the remaining
determinant factor identity. -/

namespace MOC

open Matrix

noncomputable section

/-- The two weighted-minor inequalities share the anchor coefficient.
Splitting the mixed coefficient in the donor ratio gives the scalar bound. -/
theorem fourT34_scalar_response_nonneg {a b c d A B C F : ℝ}
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (hM : 0 < b + c)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hAB : 0 ≤ F + A + 2 * √(A * B))
    (hAC : 0 ≤ F + A + 2 * √(A * C))
    (hcapacity : d + d ^ 2 / (b + c) ≤ a) :
    0 ≤ a * A + b * B + c * C + d * F := by
  let M := b + c
  let share (x : ℝ) := d * x / M
  let anchor (x : ℝ) := share x + share x ^ 2 / x
  have hMne : M ≠ 0 := hM.ne'
  have hpiece (x V : ℝ) (hx : 0 ≤ x) (hV : 0 ≤ V)
      (hF : 0 ≤ F + A + 2 * √(A * V)) :
      0 ≤ share x * F + x * V + anchor x * A := by
    rcases eq_or_lt_of_le hx with hzero | hpos
    · subst x
      simp [anchor, share]
    · have hshare : 0 ≤ share x := div_nonneg (mul_nonneg hd hx) hM.le
      have hF' : 0 ≤ F + A + 2 * √(V * A) := by simpa only [mul_comm V A] using hF
      have hp := two_mixed_rays_nonneg_of_donor_budget
        (α := share x) (β := 0) (c := anchor x) (f₁ := F) (f₂ := F)
        hpos hshare (by norm_num) hV hA (by simp [anchor]) hF' hF'
      simpa only [zero_mul, add_zero] using hp
  have hsplit : share b + share c = d := by
    dsimp only [share]
    rw [← add_div, ← mul_add]
    change d * M / M = d
    exact mul_div_cancel_right₀ _ hMne
  have hcost (x : ℝ) : share x ^ 2 / x = d ^ 2 * x / M ^ 2 := by
    by_cases hx : x = 0
    · simp [hx, share]
    · dsimp only [share]
      field_simp [hx, hMne]
      <;> ring
  have hanchors : anchor b + anchor c = d + d ^ 2 / M := by
    dsimp only [anchor]
    rw [hcost b, hcost c]
    calc
      _ = (share b + share c) + (d ^ 2 * b / M ^ 2 + d ^ 2 * c / M ^ 2) := by ring
      _ = d + d ^ 2 / M := by
        rw [hsplit, ← add_div, ← mul_add]
        change d + d ^ 2 * M / M ^ 2 = _
        field_simp [hMne]
        <;> ring
  have hextra := mul_nonneg
    (sub_nonneg.mpr (show d + d ^ 2 / M ≤ a from hcapacity)) hA
  nlinarith only [hpiece b B hb hB hAB, hpiece c C hc hC hAC, hextra,
    congrArg (fun x : ℝ => x * F) hsplit, congrArg (fun x : ℝ => x * A) hanchors]

/-- The determinant factor identity at the height fixed by the cubic. -/
def t34RadialFactorIdentity (p r a b c q d s : ℝ) : Prop :=
  let Q := t34RadialQ a b c d r s
  let C := t34RadialC p r a b c q d s
  let R := FourT34PolynomialCertificate.radialPolynomial p r a b c q d s
  Q ^ 3 * (fourMatchingHessian (t34HeightLift p r a b c q d s (-C / Q))).det =
    -4 * Q * R ^ 2

/-- The radial determinant identity is homogeneous of degree twenty. -/
theorem t34RadialFactorIdentity_of_normalized (p r a b c q d s : ℝ)
    (hd : d ≠ 0) (hQ : t34RadialQ a b c d r s ≠ 0)
    (hn : t34RadialFactorIdentity (p / d) (r / d) (a / d) (b / d) (c / d) (q / d) 1 (s / d)) :
    t34RadialFactorIdentity p r a b c q d s := by
  have hD := t34_hessian_at_radial_height_normalize p r a b c q d s hd hQ
  have hR := FourT34PolynomialCertificate.radialPolynomial_normalize p r a b c q d s hd
  dsimp only at hD
  dsimp only [t34RadialFactorIdentity] at hn ⊢
  rw [hD, t34_radialQ_normalize a b c d r s hd, hR] at hn
  have scaleCancel (Q D R : ℝ)
      (hz : (Q / d ^ 2) ^ 3 * (d⁻¹ ^ 14 * D) = -4 * (Q / d ^ 2) * (d⁻¹ ^ 9 * R) ^ 2) :
      Q ^ 3 * D = -4 * Q * R ^ 2 := by
    apply mul_left_cancel₀ (pow_ne_zero 20 (inv_ne_zero hd))
    calc
      _ = (Q / d ^ 2) ^ 3 * (d⁻¹ ^ 14 * D) := by field_simp [hd] <;> ring
      _ = -4 * (Q / d ^ 2) * (d⁻¹ ^ 9 * R) ^ 2 := hz
      _ = _ := by field_simp [hd] <;> ring
  exact scaleCancel _ _ _ hn

/-- For positive leading pivots, a five-dimensional determinant identity
implies the normalized radial factor identity. -/
theorem t34RadialFactorIdentity_normalized_of_reduced (p r a b c q s : ℝ)
    (hp : 0 ≤ p) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hq : 0 ≤ q) (hs : 0 ≤ s)
    (hred :
      let Q := t34RadialQ a b c 1 r s
      let C := t34RadialC p r a b c q 1 s
      let H := fourMatchingHessian (t34HeightLift p r a b c q 1 s (-C / Q))
      let S := t34HessianSchur H
      let R := FourT34PolynomialCertificate.radialPolynomial p r a b c q 1 s
      (a + 1) ^ 2 * (q + s + 1) ^ 2 * Q ^ 3 * (leadingPivotMinor S).det =
        -4 * (S 0 0) ^ 4 * Q * R ^ 2) :
    t34RadialFactorIdentity p r a b c q 1 s := by
  let Q := t34RadialQ a b c 1 r s
  let C := t34RadialC p r a b c q 1 s
  let H := fourMatchingHessian (t34HeightLift p r a b c q 1 s (-C / Q))
  let S := t34HessianSchur H
  let R := FourT34PolynomialCertificate.radialPolynomial p r a b c q 1 s
  have hpivot : S 0 0 ≠ 0 := by
    change t34HessianSchur H 0 0 ≠ 0
    rw [show t34HessianSchur H 0 0 = _ from
      t34Hessian_schur_zero_zero p r a b c q s (-C / Q) ha hq hs]
    positivity
  have hD : H.det = (a + 1) ^ 2 * (q + s + 1) ^ 2 * S.det :=
    t34Hessian_det_eq_schur p r a b c q s (-C / Q) ha hq hs
  have hE : (leadingPivotMinor S).det = (S 0 0) ^ 4 * S.det :=
    det_leadingPivotMinor S hpivot
  change Q ^ 3 * H.det = -4 * Q * R ^ 2
  apply mul_left_cancel₀ (pow_ne_zero 4 hpivot)
  calc
    _ = (a + 1) ^ 2 * (q + s + 1) ^ 2 * Q ^ 3 * (leadingPivotMinor S).det := by
      rw [hD, hE]
      ring
    _ = -4 * (S 0 0) ^ 4 * Q * R ^ 2 := hred
    _ = _ := by ring

/-- A certificate using five scaled inverse columns gives the radial root
condition directly on the singular normalized Hessian. -/
theorem t34_radial_root_of_scaled_right_columns (p r a b c q s : ℝ)
    (hp : 0 ≤ p) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hq : 0 ≤ q) (hs : 0 ≤ s)
    (hQ : t34RadialQ a b c 1 r s ≠ 0)
    (hD :
      let Q := t34RadialQ a b c 1 r s
      let C := t34RadialC p r a b c q 1 s
      (fourMatchingHessian (t34HeightLift p r a b c q 1 s (-C / Q))).det = 0)
    (W : Matrix (Fin 14) (Fin 5) ℝ)
    (hW :
      let Q := t34RadialQ a b c 1 r s
      let C := t34RadialC p r a b c q 1 s
      let R := FourT34PolynomialCertificate.radialPolynomial p r a b c q 1 s
      let A := fourMatchingHessian (t34HeightLift p r a b c q 1 s (-C / Q))
      (Q • A) * W = fun i j => if i = t34HessianTrailingIndices j then -4 * Q ^ 2 * R else 0) :
    FourT34PolynomialCertificate.radialPolynomial p r a b c q 1 s = 0 := by
  let Q := t34RadialQ a b c 1 r s
  let C := t34RadialC p r a b c q 1 s
  let R := FourT34PolynomialCertificate.radialPolynomial p r a b c q 1 s
  let A := fourMatchingHessian (t34HeightLift p r a b c q 1 s (-C / Q))
  change (Q • A) * W =
    (fun i j => if i = t34HessianTrailingIndices j then -4 * Q ^ 2 * R else 0) at hW
  rw [Matrix.smul_mul] at hW
  have hprod : A * W = fun i j => if i = t34HessianTrailingIndices j then -4 * Q * R else 0 := by
    ext i j : 1
    apply mul_left_cancel₀ hQ
    have hij := congrFun (congrFun hW i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at hij
    rw [hij]
    split_ifs <;> ring
  change R = 0
  by_contra hR
  have hscalar : -4 * Q * R ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hQ) hR
  exact (t34Hessian_det_ne_zero_of_right_columns p r a b c q s (-C / Q) _
    hp ha hb hc hq hs hscalar W hprod) hD

/-- Given the determinant factor identity, the degree-nine radial
polynomial of the actual T34 matching gaps vanishes. -/
theorem fourT34_radial_root_of_factor (α β : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
    (hn : ∀ i, H ≤ (η * matchingProduct α β (fourPerm i).symm).re)
    (hc : ∀ i ∈ fourT34ContactIndices, (η * matchingProduct α β (fourPerm i).symm).re = H)
    (hd : H < (η * matchingProduct α β (fourPerm 11).symm).re)
    (hfactor :
      let g := fun i => (η * matchingProduct α β (fourPerm i).symm).re - H
      t34RadialFactorIdentity (g 18) (g 16) (g 13) (g 8) (g 4) (g 14) (g 11) (g 7)) :
    let g := fun i => (η * matchingProduct α β (fourPerm i).symm).re - H
    FourT34PolynomialCertificate.radialPolynomial (g 18) (g 16) (g 13)
      (g 8) (g 4) (g 14) (g 11) (g 7) = 0 := by
  let g := fun i => (η * matchingProduct α β (fourPerm i).symm).re - H
  let Q := t34RadialQ (g 13) (g 8) (g 4) (g 11) (g 16) (g 7)
  let C := t34RadialC (g 18) (g 16) (g 13) (g 8) (g 4) (g 14) (g 11) (g 7)
  let R := FourT34PolynomialCertificate.radialPolynomial (g 18) (g 16) (g 13)
    (g 8) (g 4) (g 14) (g 11) (g 7)
  have hQ : Q ≠ 0 := fourT34_radialQ_ne_zero_of_contacts α β η H hn hc hd
  have hdH : (fourMatchingHessian (t34HeightLift (g 18) (g 16) (g 13) (g 8)
      (g 4) (g 14) (g 11) (g 7) (-C / Q))).det = 0 :=
    fourT34_hessian_at_radial_height_eq_zero α β η H hn hc hd
  have hzero : -4 * Q * R ^ 2 = 0 := by
    change Q ^ 3 * (fourMatchingHessian (t34HeightLift (g 18) (g 16) (g 13) (g 8)
      (g 4) (g 14) (g 11) (g 7) (-C / Q))).det = -4 * Q * R ^ 2 at hfactor
    rw [hdH, mul_zero] at hfactor
    exact hfactor.symm
  change R = 0
  by_contra hne
  exact (mul_ne_zero (mul_ne_zero (by norm_num) hQ) (pow_ne_zero _ hne)) hzero

/-- Given the degree-nine determinant factor identity, the actual T34
matching gaps satisfy one of the three response thresholds. -/
theorem fourT34_safe_budget_of_radial_factor (α β : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
    (hn : ∀ i, H ≤ (η * matchingProduct α β (fourPerm i).symm).re)
    (hc : ∀ i ∈ fourT34ContactIndices, (η * matchingProduct α β (fourPerm i).symm).re = H)
    (hd : H < (η * matchingProduct α β (fourPerm 11).symm).re)
    (hM : 0 < ((η * matchingProduct α β (fourPerm 4).symm).re - H) +
      ((η * matchingProduct α β (fourPerm 8).symm).re - H))
    (hfactor :
      let g := fun i => (η * matchingProduct α β (fourPerm i).symm).re - H
      t34RadialFactorIdentity (g 18) (g 16) (g 13) (g 8) (g 4) (g 14) (g 11) (g 7)) :
    let g := fun i => (η * matchingProduct α β (fourPerm i).symm).re - H
    g 11 + g 11 ^ 2 / (g 8 + g 4) ≤ g 13 ∨
      (0 < g 18 ∧ 0 < g 8 ∧ g 11 ^ 2 / g 18 + g 11 ^ 2 / g 8 ≤ g 13) ∨
      (0 < g 4 ∧ 0 < g 14 ∧ g 11 ^ 2 / g 4 + g 11 ^ 2 / g 14 ≤ g 13) := by
  let g := fun i => (η * matchingProduct α β (fourPerm i).symm).re - H
  have hg (i : Fin 24) : 0 ≤ g i := sub_nonneg.mpr (hn i)
  have hM' : 0 < g 8 + g 4 := by simpa only [g, add_comm] using hM
  exact FourT34PolynomialCertificate.safe_disjunction_of_radial_root_scaled
    (hg 18) (hg 16) (hg 13) (hg 8) (hg 4) (hg 14) (hg 7)
    (sub_pos.mpr hd) hM' (fourT34_radial_root_of_factor α β η H hn hc hd hfactor)

/-- A nonnegative T34 budget with radial polynomial zero has a nonnegative
special orthogonal response. -/
theorem fourT34_response_nonneg_of_radial_root (O : Matrix (Fin 4) (Fin 4) ℝ)
    (hO : Oᵀ * O = 1) (hdet : O.det = 1) {p r a b c q d s : ℝ}
    (hp : 0 ≤ p) (hr : 0 ≤ r) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hq : 0 ≤ q)
    (hd : 0 < d) (hs : 0 ≤ s) (hM : 0 < b + c)
    (hroot : FourT34PolynomialCertificate.radialPolynomial p r a b c q d s = 0) :
    let f := FourT34QuaternionGram.doubleResponse O
    0 ≤ p * f 0 + r * f 1 + a * f 2 + b * f 3 + c * f 4 + q * f 5 + d * f 6 + s * f 7 := by
  let f := FourT34QuaternionGram.doubleResponse O
  have hf0 : 0 ≤ f 0 := by simp [f, FourT34QuaternionGram.doubleResponse] <;> positivity
  have hf1 : 0 ≤ f 1 := by simp [f, FourT34QuaternionGram.doubleResponse] <;> positivity
  have hf2 : 0 ≤ f 2 := by simp [f, FourT34QuaternionGram.doubleResponse] <;> positivity
  have hf3 : 0 ≤ f 3 := by simp [f, FourT34QuaternionGram.doubleResponse] <;> positivity
  have hf4 : 0 ≤ f 4 := by simp [f, FourT34QuaternionGram.doubleResponse] <;> positivity
  have hf5 : 0 ≤ f 5 := by simp [f, FourT34QuaternionGram.doubleResponse] <;> positivity
  have hf7 : 0 ≤ f 7 := by simp [f, FourT34QuaternionGram.doubleResponse] <;> positivity
  obtain ⟨hAB, hAC⟩ := FourT34QuaternionGram.scalar_donor_bounds O hO hdet
  change 0 ≤ p * f 0 + r * f 1 + a * f 2 + b * f 3 + c * f 4 + q * f 5 + d * f 6 + s * f 7
  rcases FourT34PolynomialCertificate.safe_disjunction_of_radial_root_scaled
    hp hr ha hb hc hq hs hd hM hroot with h | ⟨hp', hb', h⟩ | ⟨hc', hq', h⟩
  · have hmain := fourT34_scalar_response_nonneg hb hc hd.le hM hf2 hf3 hf4 hAB hAC h
    linarith only [hmain, mul_nonneg hp hf0, mul_nonneg hr hf1, mul_nonneg hq hf5, mul_nonneg hs hf7]
  · have hmain : 0 ≤ p * f 0 + a * f 2 + b * f 3 + d * f 6 :=
      FourT34QuaternionGram.pathPB_specialOrthogonal_nonneg O hO hdet hp' hb' hd.le h
    linarith only [hmain, mul_nonneg hr hf1, mul_nonneg hc hf4, mul_nonneg hq hf5, mul_nonneg hs hf7]
  · have hmain : 0 ≤ a * f 2 + c * f 4 + q * f 5 + d * f 6 :=
      FourT34QuaternionGram.pathCQ_specialOrthogonal_nonneg O hO hdet hc' hq' hd.le h
    linarith only [hmain, mul_nonneg hp hf0, mul_nonneg hr hf1, mul_nonneg hb hf3, mul_nonneg hs hf7]

end

end MOC
