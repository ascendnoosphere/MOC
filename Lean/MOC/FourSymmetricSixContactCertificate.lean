import MOC.FourSymmetricSixContactPencil
import MOC.SparsePolynomialCertificate

/-! Exact coefficient signs of the order-nine inverse pencil on the
regions where a compensator budget could fail. -/

open BigOperators Matrix

namespace MOC

open SparsePolynomialCertificate

private abbrev Terms := SparsePolynomialCertificate.Polynomial 7

private def sparseDet : (n : ℕ) → (Fin n → Fin n → Terms) → Terms
  | 0, _ => constant 7 1
  | n + 1, A => normalize (sum fun j =>
      if (A 0 j).isEmpty then [] else
        mul (constant 7 ((-1) ^ j.val))
          (mul (A 0 j) (sparseDet n fun i k => A i.succ (j.succAbove k))))

private theorem eval_sparseDet (x : Fin 7 → ℝ) (n : ℕ) (A : Fin n → Fin n → Terms) :
    eval x (sparseDet n A) = (fun i j => eval x (A i j) : Matrix (Fin n) (Fin n) ℝ).det := by
  induction n with
  | zero => rw [sparseDet, eval_constant, Matrix.det_fin_zero, Int.cast_one]
  | succ n ih =>
    rw [sparseDet, eval_normalize, eval_sum, Matrix.det_succ_row_zero]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : A 0 j = []
    · simp [hj]
    · have hnot : (A 0 j).isEmpty = false := by
        cases h : A 0 j with
        | nil => exact False.elim (hj h)
        | cons a as => rfl
      simp only [hnot, Bool.false_eq_true, if_false, eval_mul, eval_constant, ih, Int.cast_pow,
        Int.cast_neg, Int.cast_one]
      change (-1 : ℝ) ^ j.val * (eval x (A 0 j) *
        (fun i k => eval x (A i.succ (j.succAbove k)) : Matrix (Fin n) (Fin n) ℝ).det) = _
      exact (mul_assoc _ _ _).symm

private def affineEntry (i j : Fin 9) : Terms :=
  normalize (constant 7 (symmetricSixContactRayPencil 1 i j +
    symmetricSixContactRayPencil 2 i j + symmetricSixContactRayPencil 7 i j -
    symmetricSixContactRayPencil 8 i j) ++ sum (fun k : Fin 7 =>
      mul (constant 7 (symmetricSixContactRayPencil (Fin.castLE (by decide) k) i j))
        (indeterminate k)))

private theorem eval_affineEntry (x : Fin 7 → ℝ) (i j : Fin 9) :
    eval x (affineEntry i j) = symmetricSixContactPencil x 1 i j := by
  simp only [affineEntry, eval_normalize, eval_append, eval_constant, eval_sum, eval_mul,
    eval_indeterminate, Int.cast_add, Int.cast_sub, symmetricSixContactPencil,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]
  ring

private def pencilDeterminant : Terms := sparseDet 9 affineEntry

private theorem eval_pencilDeterminant (x : Fin 7 → ℝ) :
    eval x pencilDeterminant = (symmetricSixContactPencil x 1).det := by
  rw [pencilDeterminant, eval_sparseDet]
  exact congrArg Matrix.det (funext fun i => funext fun j => eval_affineEntry x i j)

private def boundedPowers (t : Term 7) : Bool :=
  decide (t.powers 4 ≤ 2) && decide (t.powers 5 ≤ 2) && decide (t.powers 6 ≤ 2)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem determinantPowers_bound : pencilDeterminant.all boundedPowers = true := by
  decide +kernel

private theorem powers_bound (t : Term 7) (ht : t ∈ pencilDeterminant) :
    t.powers 4 ≤ 2 ∧ t.powers 5 ≤ 2 ∧ t.powers 6 ≤ 2 := by
  have hp := List.all_eq_true.mp determinantPowers_bound t ht
  simpa only [boundedPowers, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using hp

private def onePlus (i : Fin 7) : Terms := constant 7 1 ++ indeterminate i

private def cubeTerm (t : Term 7) : Terms :=
  mul [t]
    (mul (pow (onePlus 4) (2 - t.powers 4))
      (mul (pow (onePlus 5) (2 - t.powers 5)) (pow (onePlus 6) (2 - t.powers 6))))

private def cubePolynomial : Terms := normalize (pencilDeterminant.flatMap cubeTerm)

private def strictCoefficientSigns (p : Terms) : Bool :=
  p.all (fun t => decide (0 ≤ t.coefficient)) &&
    p.any (fun t => decide (0 < t.coefficient) && (List.ofFn t.powers).all (· == 0))

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem cubeCoefficientSigns : strictCoefficientSigns cubePolynomial = true := by
  decide +kernel

private theorem eval_pos_of_signs (x : Fin 7 → ℝ) (hx : ∀ i, 0 ≤ x i) (p : Terms)
    (hp : strictCoefficientSigns p = true) : 0 < eval x p := by
  have hs := Bool.and_eq_true.mp hp
  have hnonneg (t : Term 7) (ht : t ∈ p) : 0 ≤ t.coefficient :=
    of_decide_eq_true (List.all_eq_true.mp hs.1 t ht)
  obtain ⟨t, ht, hterm⟩ := List.any_eq_true.mp hs.2
  have hd : 0 < t.coefficient := of_decide_eq_true (Bool.and_eq_true.mp hterm).1
  have hz (i : Fin 7) : t.powers i = 0 := by
    have hm : t.powers i ∈ List.ofFn t.powers := List.mem_ofFn.mpr ⟨i, rfl⟩
    exact eq_of_beq (List.all_eq_true.mp (Bool.and_eq_true.mp hterm).2 _ hm)
  have htermpos : 0 < t.eval x := by
    simp only [Term.eval, hz, pow_zero, Finset.prod_const_one, mul_one]
    exact Int.cast_pos.mpr hd
  have hle (q : Terms) (hmem : t ∈ q)
      (hn : ∀ u ∈ q, 0 ≤ u.coefficient) : t.eval x ≤ eval x q := by
    induction q with
    | nil => exact False.elim (by simpa using hmem)
    | cons u q ih =>
      rw [eval_cons]
      rcases List.mem_cons.mp hmem with he | hq
      · subst u
        exact le_add_of_nonneg_right (eval_nonneg x hx q (fun w hw => hn w (List.mem_cons_of_mem _ hw)))
      · have hhead : 0 ≤ u.eval x :=
          mul_nonneg (Int.cast_nonneg.mpr (hn u (List.mem_cons_self ..)))
            (Finset.prod_nonneg (fun i _ => pow_nonneg (hx i) _))
        exact (ih hq (fun w hw => hn w (List.mem_cons_of_mem _ hw))).trans
          (le_add_of_nonneg_left hhead)
  exact htermpos.trans_le (hle p ht hnonneg)

private theorem frac_power_cancel (x s : ℝ) (hs : s ≠ 0) {m n : ℕ} (hmn : m ≤ n) :
    s ^ n * (x / s) ^ m = x ^ m * s ^ (n - m) := by
  calc
    _ = (s ^ (n - m) * s ^ m) * (x ^ m / s ^ m) := by
      rw [← pow_add, Nat.sub_add_cancel hmn, div_pow]
    _ = x ^ m * s ^ (n - m) := by field_simp [hs] <;> ring

private theorem scaled_eval_flatMap (x y : Fin 7 → ℝ) (s : ℝ) (p : Terms)
    (f : Term 7 → Terms) (h : ∀ t ∈ p, eval y (f t) = s * t.eval x) :
    eval y (normalize (p.flatMap f)) = s * eval x p := by
  rw [eval_normalize]
  induction p with
  | nil => simp only [List.flatMap_nil, eval_nil, mul_zero]
  | cons t p ih =>
    rw [List.flatMap_cons, eval_append, eval_cons, h t (List.mem_cons_self ..),
      ih (fun u hu => h u (List.mem_cons_of_mem t hu)), mul_add]

private theorem cube_eval (a b c d x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    eval (![a,b,c,d,x,y,z] : Fin 7 → ℝ) cubePolynomial =
      ((1 + x)^2 * (1 + y)^2 * (1 + z)^2) *
        eval (![a,b,c,d,x/(1+x),y/(1+y),z/(1+z)] : Fin 7 → ℝ) pencilDeterminant := by
  apply scaled_eval_flatMap
  intro t ht
  obtain ⟨hi, hj, hk⟩ := powers_bound t ht
  have hn₁ : 1 + x ≠ 0 := by positivity
  have hn₂ : 1 + y ≠ 0 := by positivity
  have hn₃ : 1 + z ≠ 0 := by positivity
  simp only [cubeTerm, eval_mul, eval_cons, eval_nil, add_zero, eval_pow, onePlus, eval_append,
    eval_constant, eval_indeterminate, Int.cast_one, Term.eval, Fin.prod_univ_succ,
    Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]
  calc
    _ = (t.coefficient : ℝ) * (a ^ t.powers 0 * b ^ t.powers 1 *
        c ^ t.powers 2 * d ^ t.powers 3) *
        (x ^ t.powers 4 * (1+x) ^ (2 - t.powers 4)) *
        (y ^ t.powers 5 * (1+y) ^ (2 - t.powers 5)) *
        (z ^ t.powers 6 * (1+z) ^ (2 - t.powers 6)) := by ring
    _ = _ := by
      rw [← frac_power_cancel x (1+x) hn₁ hi, ← frac_power_cancel y (1+y) hn₂ hj,
        ← frac_power_cancel z (1+z) hn₃ hk]
      ring

private theorem det_pos_in_cube (u : Fin 7 → ℝ) (hu : ∀ i, 0 ≤ u i)
    (hp : u 4 < 1) (hq : u 5 < 1) (hr : u 6 < 1) :
    0 < (symmetricSixContactPencil u 1).det := by
  let x := u 4 / (1 - u 4)
  let y := u 5 / (1 - u 5)
  let z := u 6 / (1 - u 6)
  have hx : 0 ≤ x := div_nonneg (hu 4) (sub_nonneg.mpr hp.le)
  have hy : 0 ≤ y := div_nonneg (hu 5) (sub_nonneg.mpr hq.le)
  have hz : 0 ≤ z := div_nonneg (hu 6) (sub_nonneg.mpr hr.le)
  have reco (t : ℝ) (ht : t < 1) : (t / (1-t)) / (1 + t / (1-t)) = t := by
    have hn : 1 - t ≠ 0 := sub_ne_zero.mpr ht.ne'
    rw [show 1 + t / (1-t) = 1 / (1-t) by apply (eq_div_iff hn).mpr; field_simp; ring]
    rw [div_div_div_cancel_right₀ hn, div_one]
  have he : (![u 0,u 1,u 2,u 3,x/(1+x),y/(1+y),z/(1+z)] : Fin 7 → ℝ) = u := by
    funext i
    rw [show x / (1+x) = u 4 from reco (u 4) hp, show y / (1+y) = u 5 from reco (u 5) hq,
      show z / (1+z) = u 6 from reco (u 6) hr]
    fin_cases i <;> rfl
  have hpositive := eval_pos_of_signs (![u 0,u 1,u 2,u 3,x,y,z] : Fin 7 → ℝ)
    (by intro i; fin_cases i <;> first | exact hu _ | exact hx | exact hy | exact hz)
    cubePolynomial cubeCoefficientSigns
  rw [cube_eval (u 0) (u 1) (u 2) (u 3) x y z hx hy hz, he,
    eval_pencilDeterminant] at hpositive
  exact pos_of_mul_pos_left hpositive (by positivity)

private def compensatorIndex (k : Fin 3) (i : Fin 3) : Fin 7 :=
  (![![4,5,6], ![5,4,6], ![6,4,5]] : Fin 3 → Fin 3 → Fin 7) k i

private def starCoordinates (k : Fin 3) (a b c d p q r : ℝ) : Fin 7 → ℝ :=
  (![![a,b,c,d,p,q,r], ![a,b,c,d,q,p,r], ![a,b,c,d,q,r,p]] : Fin 3 → Fin 7 → ℝ) k

private def starLine : Terms := onePlus 5 ++ indeterminate 6

private def starTerm (k : Fin 3) (t : Term 7) : Terms :=
  let i := t.powers (compensatorIndex k 0)
  let j := t.powers (compensatorIndex k 1)
  let l := t.powers (compensatorIndex k 2)
  mul [⟨t.coefficient, ![t.powers 0,t.powers 1,t.powers 2,t.powers 3,0,j,l]⟩]
    (mul (pow (onePlus 4) (4 + i - j - l)) (pow starLine (4 - j - l)))

private def starPolynomial (k : Fin 3) : Terms :=
  normalize (pencilDeterminant.flatMap (starTerm k))

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem starCoefficientSigns : ∀ k : Fin 3, strictCoefficientSigns (starPolynomial k) = true := by
  decide +kernel

private theorem star_power_identity (S L x y : ℝ) {i j k : ℕ}
    (hS : S ≠ 0) (hL : L ≠ 0) (hjk : j + k ≤ 4) :
    S ^ 4 * L ^ 4 * (S ^ i * (x / (S * L)) ^ j * (y / (S * L)) ^ k) =
      S ^ (4 + i - j - k) * x ^ j * y ^ k * L ^ (4 - j - k) := by
  have hden : S * L ≠ 0 := mul_ne_zero hS hL
  have hfrac : (x / (S * L)) ^ j * (y / (S * L)) ^ k =
      (x ^ j * y ^ k) / (S * L) ^ (j + k) := by
    rw [div_pow, div_pow, div_mul_div_comm, ← pow_add]
  have hex₁ : 4 + i - j - k = i + (4 - (j + k)) := by omega
  have hex₂ : 4 - j - k = 4 - (j + k) := by omega
  rw [hex₁, hex₂, pow_add]
  calc
    _ = S ^ i * ((S * L) ^ 4 * ((x / (S * L)) ^ j * (y / (S * L)) ^ k)) := by
      rw [mul_pow]
      ring
    _ = S ^ i * ((x ^ j * y ^ k) * (S * L) ^ (4 - (j + k))) := by
      rw [hfrac]
      have hcancel : (S * L) ^ 4 * ((x ^ j * y ^ k) / (S * L) ^ (j + k)) =
          (x ^ j * y ^ k) * (S * L) ^ (4 - (j + k)) := by
        calc
          _ = ((S * L) ^ (4 - (j + k)) * (S * L) ^ (j + k)) *
              ((x ^ j * y ^ k) / (S * L) ^ (j + k)) := by
            rw [← pow_add, Nat.sub_add_cancel hjk]
          _ = _ := by field_simp [hden] <;> ring
      rw [hcancel]
    _ = _ := by rw [mul_pow]; ring

private theorem star_eval (k : Fin 3) (a b c d s x y : ℝ)
    (hs : 0 ≤ s) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    eval (![a,b,c,d,s,x,y] : Fin 7 → ℝ) (starPolynomial k) =
      (((1+s)^4 * (1+x+y)^4) *
        eval (starCoordinates k a b c d (1+s) (x/((1+s)*(1+x+y))) (y/((1+s)*(1+x+y))))
          pencilDeterminant) := by
  apply scaled_eval_flatMap
  intro t ht
  obtain ⟨h4, h5, h6⟩ := powers_bound t ht
  have h1 : t.powers (compensatorIndex k 1) ≤ 2 := by
    fin_cases k <;> first | exact h4 | exact h5 | exact h6
  have h2 : t.powers (compensatorIndex k 2) ≤ 2 := by
    fin_cases k <;> first | exact h4 | exact h5 | exact h6
  have hS : 1 + s ≠ 0 := by positivity
  have hL : 1 + x + y ≠ 0 := by positivity
  have h := star_power_identity (1+s) (1+x+y) x y
    (i := t.powers (compensatorIndex k 0)) (j := t.powers (compensatorIndex k 1))
    (k := t.powers (compensatorIndex k 2)) hS hL (by omega)
  have hprod :
      t.eval (starCoordinates k a b c d (1+s) (x/((1+s)*(1+x+y))) (y/((1+s)*(1+x+y)))) =
        (t.coefficient : ℝ) * (a^t.powers 0*b^t.powers 1*c^t.powers 2*d^t.powers 3) *
          ((1+s)^t.powers (compensatorIndex k 0) *
            (x/((1+s)*(1+x+y)))^t.powers (compensatorIndex k 1) *
            (y/((1+s)*(1+x+y)))^t.powers (compensatorIndex k 2)) := by
    fin_cases k <;>
      simp only [Term.eval, starCoordinates, compensatorIndex, Fin.prod_univ_succ, Fin.prod_univ_zero,
        Matrix.cons_val_zero, Matrix.cons_val_succ] <;>
      ring
  rw [hprod]
  simp only [starTerm, eval_mul, eval_cons, eval_nil, add_zero, eval_pow, starLine, onePlus,
    eval_append, eval_constant, eval_indeterminate, Int.cast_one, Term.eval, Fin.prod_univ_succ,
    Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, pow_zero, mul_one]
  calc
    _ = (t.coefficient : ℝ) * (a^t.powers 0*b^t.powers 1*c^t.powers 2*d^t.powers 3) *
        ((1+s) ^ (4 + t.powers (compensatorIndex k 0) - t.powers (compensatorIndex k 1) -
          t.powers (compensatorIndex k 2)) * x^t.powers (compensatorIndex k 1) *
          y^t.powers (compensatorIndex k 2) *
          (1+x+y) ^ (4 - t.powers (compensatorIndex k 1) - t.powers (compensatorIndex k 2))) := by
      ring
    _ = _ := by rw [← h]; ring

private theorem det_pos_in_star (u : Fin 7 → ℝ) (hu : ∀ i, 0 ≤ u i) (k : Fin 3)
    (hP : 1 ≤ u (compensatorIndex k 0))
    (hstar : u (compensatorIndex k 0) * (u (compensatorIndex k 1) + u (compensatorIndex k 2)) < 1) :
    0 < (symmetricSixContactPencil u 1).det := by
  let p := u (compensatorIndex k 0)
  let q := u (compensatorIndex k 1)
  let r := u (compensatorIndex k 2)
  let D := 1 - p * (q + r)
  let s := p - 1
  let x := p * q / D
  let y := p * r / D
  change 1 ≤ p at hP
  have hp : 0 < p := zero_lt_one.trans_le hP
  have hD : 0 < D := sub_pos.mpr hstar
  have hs : 0 ≤ s := sub_nonneg.mpr hP
  have hx : 0 ≤ x := div_nonneg (mul_nonneg hp.le (hu (compensatorIndex k 1))) hD.le
  have hy : 0 ≤ y := div_nonneg (mul_nonneg hp.le (hu (compensatorIndex k 2))) hD.le
  have hS : 1 + s = p := by dsimp only [s]; ring
  have hL : 1 + x + y = 1 / D := by
    apply (eq_div_iff hD.ne').mpr
    dsimp only [x, y]
    field_simp [hD.ne']
    dsimp only [D]
    ring
  have hq : x / ((1+s)*(1+x+y)) = q := by
    rw [hS, hL]
    dsimp only [x]
    field_simp [hD.ne', hp.ne']
    <;> ring
  have hr : y / ((1+s)*(1+x+y)) = r := by
    rw [hS, hL]
    dsimp only [y]
    field_simp [hD.ne', hp.ne']
    <;> ring
  have he : starCoordinates k (u 0) (u 1) (u 2) (u 3) (1+s)
      (x/((1+s)*(1+x+y))) (y/((1+s)*(1+x+y))) = u := by
    rw [hq, hr, hS]
    funext i
    fin_cases k <;> fin_cases i <;> rfl
  have hpositive := eval_pos_of_signs (![u 0,u 1,u 2,u 3,s,x,y] : Fin 7 → ℝ)
    (by intro i; fin_cases i <;> first | exact hu _ | exact hs | exact hx | exact hy)
    (starPolynomial k) (starCoefficientSigns k)
  rw [star_eval k (u 0) (u 1) (u 2) (u 3) s x y hs hx hy, he,
    eval_pencilDeterminant] at hpositive
  exact pos_of_mul_pos_left hpositive (by positivity)

private theorem pencil_singularity_forces_compensation (u : Fin 7 → ℝ) (hu : ∀ i, 0 ≤ u i)
    (hz : (symmetricSixContactPencil u 1).det = 0) :
    1 ≤ u 4 * (u 5 + u 6) ∨ 1 ≤ u 5 * (u 4 + u 6) ∨ 1 ≤ u 6 * (u 4 + u 5) := by
  by_contra! h
  by_cases hbig : ∃ k : Fin 3, 1 ≤ u (compensatorIndex k 0)
  · obtain ⟨k, hk⟩ := hbig
    have hsmall :
        u (compensatorIndex k 0) * (u (compensatorIndex k 1) + u (compensatorIndex k 2)) < 1 := by
      fin_cases k <;> first | exact h.1 | exact h.2.1 | exact h.2.2
    exact (det_pos_in_star u hu k hk hsmall).ne' hz
  · push_neg at hbig
    exact (det_pos_in_cube u hu (hbig 0) (hbig 1) (hbig 2)).ne' hz

private theorem normalized_gap (a c : Fin 4 → ℂ) (η : ℂ) (b : Fin 7 → ℝ) (mixedWeight h : ℝ)
    (hMixedWeight : mixedWeight ≠ 0)
    (hgap : ∀ i, (η * matchingProduct a c (fourPerm i).symm).re + h =
      symmetricSixContactProfile b mixedWeight i) (i : Fin 24) :
    ((η / (mixedWeight : ℂ)) * matchingProduct a c (fourPerm i).symm).re + h / mixedWeight =
      symmetricSixContactProfile (fun j => b j / mixedWeight) 1 i := by
  have hw (k : Fin 9) : symmetricSixContactWeights (fun j => b j / mixedWeight) 1 k =
      symmetricSixContactWeights b mixedWeight k / mixedWeight := by
    fin_cases k <;>
      simp only [symmetricSixContactWeights, Matrix.cons_val_zero, Matrix.cons_val_succ] <;>
      field_simp [hMixedWeight] <;> ring
  rw [div_mul_eq_mul_div, Complex.div_ofReal_re, ← add_div, hgap i]
  simp only [symmetricSixContactProfile, hw, Finset.sum_div, ite_div, zero_div]

/-- On the full seven-parameter symmetric six-contact family, the
spectral condition forces one of the three compensator budgets. -/
theorem symmetricSixContact_spectral_compensation (a c : Fin 4 → ℂ) (η : ℂ)
    (b : Fin 7 → ℝ) {mixedWeight h : ℝ} (hb : ∀ k, 0 ≤ b k) (hMixedWeight : 0 ≤ mixedWeight)
    (hgap : ∀ i, (η * matchingProduct a c (fourPerm i).symm).re + h =
      symmetricSixContactProfile b mixedWeight i) :
    mixedWeight ^ 2 ≤ b 4 * (b 5 + b 6) ∨
      mixedWeight ^ 2 ≤ b 5 * (b 4 + b 6) ∨ mixedWeight ^ 2 ≤ b 6 * (b 4 + b 5) := by
  by_cases hz : mixedWeight = 0
  · left
    rw [hz, zero_pow (by decide : 2 ≠ (0 : ℕ))]
    exact mul_nonneg (hb 4) (add_nonneg (hb 5) (hb 6))
  let u (k : Fin 7) := b k / mixedWeight
  have hp : 0 < mixedWeight := lt_of_le_of_ne hMixedWeight hz.symm
  have hu (k : Fin 7) : 0 ≤ u k := div_nonneg (hb k) hMixedWeight
  have hs := symmetricSixContact_spectralPencil_singular a c (η / (mixedWeight : ℂ)) u 1 (h / mixedWeight)
    (normalized_gap a c η b mixedWeight h hz hgap)
  have hscale (i j k : Fin 7) (hc : 1 ≤ u i * (u j + u k)) :
      mixedWeight ^ 2 ≤ b i * (b j + b k) := by
    have he : u i * (u j + u k) = (b i * (b j + b k)) / mixedWeight ^ 2 := by
      dsimp only [u]
      field_simp [hz] <;> ring
    rw [he] at hc
    simpa only [one_mul] using (le_div_iff₀ (pow_pos hp 2)).mp hc
  rcases pencil_singularity_forces_compensation u hu hs with hp | hq | hr
  · exact Or.inl (hscale 4 5 6 hp)
  · exact Or.inr (Or.inl (hscale 5 4 6 hq))
  · exact Or.inr (Or.inr (hscale 6 4 5 hr))

/-- The lower determinant support bound for every point of the symmetric
six-contact family with seven independent ordinary weights. -/
theorem symmetricSixContact_support (a c : Fin 4 → ℂ) (η : ℂ) (b : Fin 7 → ℝ) {mixedWeight h : ℝ}
    (hb : ∀ k, 0 ≤ b k) (hMixedWeight : 0 ≤ mixedWeight)
    (hgap : ∀ i, (η * matchingProduct a c (fourPerm i).symm).re + h =
      symmetricSixContactProfile b mixedWeight i)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    -h ≤ (η * determinantValue a c U).re :=
  symmetricSixContact_support_of_compensator_budget a c η b hb hMixedWeight hgap
    (symmetricSixContact_spectral_compensation a c η b hb hMixedWeight hgap) U hU

end MOC
