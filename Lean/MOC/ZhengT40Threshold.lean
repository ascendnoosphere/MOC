import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! The sign argument for the positive eight-contact T40 overlap in
Zheng's order-four reduction (DOI: 10.13140/RG.2.2.36790.25923).
The exact secant polynomial in the hypothesis comes from the matching
cubic Hessian; that determinant identity is not assumed proved in Lean
by this module. -/

namespace MOC
namespace ZhengT40Threshold

def groupedB (Y R : ℝ) : ℝ := Y + 1 + R
def groupedG (X Y R : ℝ) : ℝ := (X + 1) * groupedB Y R
def groupedK (X Y P R : ℝ) : ℝ := groupedG X Y R + P * (Y + 1)
def leadingF (X Y P R : ℝ) : ℝ :=
  X * (X + 1) * (groupedB Y R) ^ 2 -
    P * (X + Y + 2) * groupedB Y R - P ^ 2 * (4 * R + 3 * Y + 2)
def linearF (X Y P R : ℝ) : ℝ :=
  groupedK X Y P R * (groupedG X Y R + P * (4 * R + 3 * Y + 1))
def secantF (X Y P R A : ℝ) : ℝ :=
  leadingF X Y P R * A ^ 2 + linearF X Y P R * A + (groupedK X Y P R) ^ 2

noncomputable def constantRoot (X Y P R : ℝ) : ℝ := Y + 1 + groupedG X Y R / P

/-- Evaluation at the lower end of the forbidden height interval, in
the exact factored form used for its sign. -/
theorem secant_at_constantRoot {X Y P R : ℝ} (hP : P ≠ 0) :
    P ^ 2 * secantF X Y P R (constantRoot X Y P R) =
      groupedB Y R * (groupedK X Y P R) ^ 2 *
        (X * groupedG X Y R - P * (Y + 1)) := by
  unfold constantRoot secantF leadingF linearF groupedK groupedG groupedB
  field_simp
  ring

private theorem grouped_support_signs {p q r s : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    0 < groupedB (r+s) (r*s) ∧ 0 < groupedG (p+q) (r+s) (r*s) ∧
    p*q * (r+s+1) < (p+q) * groupedG (p+q) (r+s) (r*s) := by
  have hY : 0 ≤ r+s := add_nonneg hr hs
  have hR : 0 ≤ r*s := mul_nonneg hr hs
  have hX : 0 < p+q := add_pos hp hq
  have hP : 0 < p*q := mul_pos hp hq
  have hB : 0 < groupedB (r+s) (r*s) := by
    unfold groupedB
    linarith
  have hG : 0 < groupedG (p+q) (r+s) (r*s) := by
    exact mul_pos (by linarith) hB
  have hM : p*q < (p+q)*(p+q+1) := by nlinarith [sq_nonneg (p-q)]
  have hSm : p*q*(r+s+1) < (p+q)*(p+q+1)*(r+s+1) :=
    mul_lt_mul_of_pos_right hM (by linarith)
  have hcoef : 0 ≤ (p+q)*(p+q+1) := mul_nonneg hX.le (by linarith)
  have hBg : r+s+1 ≤ groupedB (r+s) (r*s) := by
    unfold groupedB
    linarith
  refine ⟨hB,hG,?_⟩
  have hp' := mul_le_mul_of_nonneg_left hBg hcoef
  have he := lt_of_lt_of_le hSm hp'
  unfold groupedG
  simpa only [mul_assoc] using he

/-- The two coefficients of the cubic with respect to height cannot
vanish simultaneously with these positive arm coordinates. -/
theorem not_constant_and_height_zero {p q r s A : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    let X := p+q; let Y := r+s; let P := p*q; let R := r*s
    ¬ (P*(A-Y-1) - groupedG X Y R = 0 ∧ X*(A-Y-1) - (Y+1) = 0) := by
  dsimp only
  intro ⟨hC,hQ⟩
  obtain ⟨_,_,hineq⟩ := grouped_support_signs hp hq hr hs
  have he : (p+q)*groupedG (p+q) (r+s) (r*s) = p*q*(r+s+1) := by
    linear_combination -(p+q)*hC + (p*q)*hQ
  linarith

/-- A positive root of the exact secant equation lies above the
constant-coefficient root. In particular the compensation is strong
enough for the weighted orthogonal inequality. -/
theorem compensation_of_secant {p q r s A : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hr : 0 ≤ r) (hs : 0 ≤ s) (hA : 0 < A)
    (hsec : secantF (p+q) (r+s) (p*q) (r*s) A = 0) :
    1 + 1 / min p q < A := by
  let X := p+q
  let Y := r+s
  let P := p*q
  let R := r*s
  let L := leadingF X Y P R
  let M := linearF X Y P R
  let K := groupedK X Y P R
  let T := constantRoot X Y P R
  have hX : 0 < X := add_pos hp hq
  have hY : 0 ≤ Y := add_nonneg hr hs
  have hP : 0 < P := mul_pos hp hq
  have hR : 0 ≤ R := mul_nonneg hr hs
  obtain ⟨hB,hG,hineq⟩ := grouped_support_signs hp hq hr hs
  change 0 < groupedB Y R at hB
  change 0 < groupedG X Y R at hG
  change P*(Y+1) < X*groupedG X Y R at hineq
  have hK : 0 < K := by
    unfold K groupedK
    exact add_pos_of_pos_of_nonneg hG (mul_nonneg hP.le (by linarith))
  have hM : 0 < M := by
    unfold M linearF
    exact mul_pos hK (add_pos_of_pos_of_nonneg hG
      (mul_nonneg hP.le (by linarith)))
  have hT : 0 < T := by
    unfold T constantRoot
    linarith [div_pos hG hP]
  have hFpos : 0 < L * T^2 + M*T + K^2 := by
    have hh := secant_at_constantRoot (X:=X) (Y:=Y) (R:=R) hP.ne'
    change P^2 * (L*T^2+M*T+K^2) =
      groupedB Y R * K^2 * (X * groupedG X Y R - P*(Y+1)) at hh
    have hPos := mul_pos (mul_pos hB (pow_pos hK 2)) (sub_pos.mpr hineq)
    rw [← hh] at hPos
    exact pos_of_mul_pos_right hPos (sq_nonneg P)
  have hFzero : L*A^2+M*A+K^2 = 0 := hsec
  have hL : L < 0 := by
    by_contra hn
    have hLn : 0 ≤ L := le_of_not_gt hn
    linarith [mul_nonneg hLn (sq_nonneg A), mul_pos hM hA, sq_nonneg K]
  have hTA : T < A := by
    by_contra hn
    have hAT : A ≤ T := le_of_not_gt hn
    have hATmul : L*T ≤ L*A := mul_le_mul_of_nonpos_left hAT hL.le
    have hATdiv : K^2/T ≤ K^2/A := div_le_div_of_nonneg_left (sq_nonneg K) hA hAT
    have hzero : L*A+M+K^2/A = 0 := by
      have he : (L*A+M+K^2/A)*A = L*A^2+M*A+K^2 := by
        field_simp
        ring
      rw [hFzero] at he
      exact (mul_eq_zero.mp he).resolve_right hA.ne'
    have hpos : 0 < L*T+M+K^2/T := by
      have he : (L*T+M+K^2/T)*T = L*T^2+M*T+K^2 := by
        field_simp
        ring
      have hp : 0 < (L*T+M+K^2/T)*T := he.symm ▸ hFpos
      exact pos_of_mul_pos_left hp hT.le
    linarith
  have hXG : X < groupedG X Y R := by
    unfold groupedG groupedB
    nlinarith [mul_nonneg hX.le hY, mul_nonneg hX.le hR]
  have hdiv : X/P < groupedG X Y R / P :=
    div_lt_div_of_pos_right hXG hP
  have hTP : 1 + X/P < T := by
    unfold T constantRoot
    linarith
  have hXdiv : X/P = 1/p + 1/q := by
    unfold X P
    field_simp
    ring
  rw [hXdiv] at hTP
  have hmin : 1+1/min p q ≤ 1+1/p+1/q := by
    rcases le_total p q with h | h
    · rw [min_eq_left h]
      linarith [one_div_nonneg.mpr hq.le]
    · rw [min_eq_right h]
      linarith [one_div_nonneg.mpr hp.le]
  linarith

private theorem groupedG_pos {X Y R : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hR : 0 ≤ R) : 0 < groupedG X Y R := by
  unfold groupedG groupedB
  exact mul_pos (by linarith) (by linarith)

/-- The height coefficient cannot vanish even if more arms are active
and one of the two compensated coefficients is zero. -/
theorem not_constant_and_height_zero_nonneg {p q r s A : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    let X := p+q; let Y := r+s; let P := p*q; let R := r*s
    ¬ (P*(A-Y-1) - groupedG X Y R = 0 ∧ X*(A-Y-1) - (Y+1) = 0) := by
  by_cases hP : p*q = 0
  · dsimp only
    intro ⟨hC,_⟩
    rw [hP,zero_mul] at hC
    linarith [groupedG_pos (add_nonneg hp hq) (add_nonneg hr hs) (mul_nonneg hr hs)]
  · have hp' : 0 < p := lt_of_le_of_ne hp (fun he => hP (by rw [← he,zero_mul]))
    have hq' : 0 < q := lt_of_le_of_ne hq (fun he => hP (by rw [← he,mul_zero]))
    exact not_constant_and_height_zero hp' hq' hr hs

/-- At a nonnegative lift solving the exact secant equation, the two
compensating arm gaps are automatically positive. Therefore the
positive T40 overlap closes even if other arms are also in contact. -/
theorem compensation_or_impossible {p q r s A : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) (hs : 0 ≤ s) (hA : 0 ≤ A)
    (hsec : secantF (p+q) (r+s) (p*q) (r*s) A = 0) :
    0 < p ∧ 0 < q ∧ 0 < A ∧ 1 + 1 / min p q < A := by
  have hG : 0 < groupedG (p+q) (r+s) (r*s) :=
    groupedG_pos (add_nonneg hp hq) (add_nonneg hr hs) (mul_nonneg hr hs)
  have hP : p*q ≠ 0 := by
    intro he
    rw [he] at hsec
    unfold secantF leadingF linearF groupedK at hsec
    simp only [zero_mul,zero_pow (by decide : (2 : ℕ) ≠ 0),sub_zero,add_zero] at hsec
    have hfirst : 0 ≤ (p+q)*(p+q+1)*groupedB (r+s) (r*s)^2*A^2 :=
      mul_nonneg (mul_nonneg (mul_nonneg (add_nonneg hp hq) (by linarith))
        (sq_nonneg _)) (sq_nonneg A)
    linarith [hfirst, mul_nonneg (mul_nonneg hG.le hG.le) hA, pow_pos hG 2]
  have hp' : 0 < p := lt_of_le_of_ne hp (fun he => hP (by rw [← he,zero_mul]))
  have hq' : 0 < q := lt_of_le_of_ne hq (fun he => hP (by rw [← he,mul_zero]))
  have hA' : 0 < A := by
    by_contra hn
    have he : A = 0 := le_antisymm (le_of_not_gt hn) hA
    rw [he] at hsec
    unfold secantF at hsec
    simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, zero_add] at hsec
    have hK : 0 < groupedK (p+q) (r+s) (p*q) (r*s) := by
      unfold groupedK
      exact add_pos_of_pos_of_nonneg hG
        (mul_nonneg (mul_nonneg hp hq) (by linarith))
    exact (pow_ne_zero _ hK.ne') hsec
  exact ⟨hp',hq',hA',compensation_of_secant hp' hq' hr hs hA' hsec⟩

/-- The secant equation for the boundary with one vanishing row-arm
gap gives exactly the product threshold for the dual Gram norm. -/
theorem product_compensation_of_boundary {X T A : ℝ}
    (hX : 0 ≤ X) (hA : 0 ≤ A)
    (hsec : (T-X)*A^2+(X+1)*(T-1)*A-(X+1) = 0) :
    1 ≤ A*T := by
  have hp : 0 < A+X+1 := by linarith
  have hq : 0 ≤ X*A*(A+1) :=
    mul_nonneg (mul_nonneg hX hA) (by linarith)
  have hid : (A*T-1)*(A+X+1) = X*A*(A+1) := by
    linear_combination hsec
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_left (hid.symm ▸ hq) hp)


/-- A linear interpolation in the product compensation (AT) is
controlled by its two positive endpoints. -/
theorem split_compensation_of_endpoints {Z K U W A A₀ τ : ℝ}
    (hA : 0 < A) (hτ : 0 ≤ τ) (hτ₁ : τ < 1)
    (hK : 0 < K) (hU : 0 < U + τ*W)
    (h₀ : 0 < Z*A₀ + K*U + K^2/A₀)
    (h₁ : 0 < Z*A₀ + K*(U+W))
    (hsec : Z*A + K*(U+τ*W) + K^2*(1-τ)/A = 0) :
    A₀ < A := by
  have hC : 0 < K^2*(1-τ) := mul_pos (pow_pos hK 2) (by linarith)
  have hZ : Z < 0 := by
    by_contra! hn
    linarith [mul_nonneg hn hA.le, mul_pos hK hU, div_pos hC hA]
  have he : Z*A₀ + K*(U+τ*W) + K^2*(1-τ)/A₀ =
      (1-τ)*(Z*A₀ + K*U + K^2/A₀) + τ*(Z*A₀ + K*(U+W)) := by ring
  have hpos : 0 < Z*A₀ + K*(U+τ*W) + K^2*(1-τ)/A₀ := by
    rw [he]
    exact add_pos_of_pos_of_nonneg (mul_pos (by linarith) h₀) (mul_nonneg hτ h₁.le)
  by_contra! hn
  linarith [mul_le_mul_of_nonpos_left hn hZ.le,
    div_le_div_of_nonneg_left hC.le hA hn]

/-- Strict positivity at the (AT=1) endpoint of canonical T55+20's
Gamma-7 secant polynomial. The coefficients are grouped by powers of
the remaining arm gap, not by a test on any choice of spectra. -/
theorem gamma7_endpoint_one_pos {p q Y : ℝ}
    (hp : 0 < p) (hq : 0 ≤ q) (hY : 0 ≤ Y) :
    let X := p+q; let P := p*q; let V := Y+1
    let K := V*(P+X+1)
    let Z := leadingF X Y P 0
    0 < Z*(1+1/p) + K*(X*V+P*(3*V-1)) := by
  dsimp only
  let D := p*(2*p+1)*(p+1)
  let c₂ := D+q^2*(3*p^3+4*p^2+2*p+1)+q*(4*p^3+6*p^2+3*p+1)
  let c₁ := 2*D+q^2*(2*p^3+3*p^2+3*p+2)+q*(6*p^3+9*p^2+5*p+2)
  let c₀ := D+q^2*(p+1)+q*(2*p^3+3*p^2+2*p+1)
  have he : p*(leadingF (p+q) Y (p*q) 0*(1+1/p) +
      ((Y+1)*(p*q+(p+q)+1))*((p+q)*(Y+1)+p*q*(3*(Y+1)-1))) =
        c₂*Y^2+c₁*Y+c₀ := by
    dsimp [c₂,c₁,c₀,D,leadingF,groupedB]
    field_simp
    ring
  have hc₂ : 0 < c₂ := by dsimp [c₂,D]; positivity
  have hc₁ : 0 < c₁ := by dsimp [c₁,D]; positivity
  have hc₀ : 0 < c₀ := by dsimp [c₀,D]; positivity
  have hsum : 0 < c₂*Y^2+c₁*Y+c₀ :=
    add_pos_of_nonneg_of_pos
      (add_nonneg (mul_nonneg hc₂.le (sq_nonneg _)) (mul_nonneg hc₁.le hY)) hc₀
  exact pos_of_mul_pos_right (he.symm ▸ hsum) hp.le


/-- With negative leading coefficient, the normalized quadratic stays
positive at every positive argument below the cubic constant-root. -/
theorem secant_div_pos_below_constantRoot {p q r s A : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hr : 0 ≤ r) (hs : 0 ≤ s) (hA : 0 < A)
    (hL : leadingF (p+q) (r+s) (p*q) (r*s) < 0)
    (hAT : A ≤ constantRoot (p+q) (r+s) (p*q) (r*s)) :
    0 < leadingF (p+q) (r+s) (p*q) (r*s) * A +
      linearF (p+q) (r+s) (p*q) (r*s) +
      (groupedK (p+q) (r+s) (p*q) (r*s))^2 / A := by
  let X := p+q
  let Y := r+s
  let P := p*q
  let R := r*s
  let L := leadingF X Y P R
  let M := linearF X Y P R
  let K := groupedK X Y P R
  let T := constantRoot X Y P R
  have hP : 0 < P := mul_pos hp hq
  obtain ⟨hB,hG,hi⟩ := grouped_support_signs hp hq hr hs
  change 0 < groupedB Y R at hB
  change 0 < groupedG X Y R at hG
  change P*(Y+1) < X*groupedG X Y R at hi
  have hY : 0 ≤ Y := add_nonneg hr hs
  have hK : 0 < K := by
    exact add_pos_of_pos_of_nonneg hG (mul_nonneg hP.le (by linarith))
  have hT : 0 < T := hA.trans_le hAT
  have he := secant_at_constantRoot (X:=X) (Y:=Y) (R:=R) hP.ne'
  have hpos := mul_pos (mul_pos hB (pow_pos hK 2)) (sub_pos.mpr hi)
  rw [← he] at hpos
  have hFT : 0 < L*T^2+M*T+K^2 := pos_of_mul_pos_right hpos (sq_nonneg P)
  have hfactor : (L*T+M+K^2/T)*T = L*T^2+M*T+K^2 := by
    field_simp
    ring
  rw [← hfactor] at hFT
  have hFT' : 0 < L*T+M+K^2/T := pos_of_mul_pos_left hFT hT.le
  change A ≤ T at hAT
  change L < 0 at hL
  have hATmul : L*T ≤ L*A := mul_le_mul_of_nonpos_left hAT hL.le
  have hATdiv : K^2/T ≤ K^2/A := div_le_div_of_nonneg_left (sq_nonneg K) hA hAT
  change 0 < L*A+M+K^2/A
  linarith

/-- The cubic constant-root strictly exceeds the smaller-arm threshold. -/
theorem min_threshold_lt_constantRoot {p q r s : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    1+1/min p q < constantRoot (p+q) (r+s) (p*q) (r*s) := by
  have hX : 0 < p+q := add_pos hp hq
  have hY : 0 ≤ r+s := add_nonneg hr hs
  have hR : 0 ≤ r*s := mul_nonneg hr hs
  have hXG : p+q < groupedG (p+q) (r+s) (r*s) := by
    unfold groupedG groupedB
    nlinarith [mul_nonneg hX.le hY, mul_nonneg hX.le hR]
  have hdiv := div_lt_div_of_pos_right hXG (mul_pos hp hq)
  have hXdiv : (p+q)/(p*q) = 1/p+1/q := by
    field_simp
    ring
  rw [hXdiv] at hdiv
  have hmin : 1+1/min p q ≤ 1+1/p+1/q := by
    rcases le_total p q with h | h
    · rw [min_eq_left h]
      linarith [one_div_nonneg.mpr hq.le]
    · rw [min_eq_right h]
      linarith [one_div_nonneg.mpr hp.le]
  unfold constantRoot
  linarith


/-- The canonical T55+20 Gamma-7 boundary has either product
compensation or smaller-arm compensation. The secant polynomial
identity supplying the equation is separate from this sign proof. -/
theorem gamma7_compensation_of_secant {p q Y A T : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hY : 0 ≤ Y) (hA : 0 ≤ A) (hT : 0 ≤ T)
    (hsec : let X := p+q; let P := p*q; let V := Y+1
            let K := V*(P+X+1); let τ := A*T
            leadingF X Y P 0*A^2 +
              A*K*((X+1)*V+P*(3*V-2)+τ*(P-V)) + K^2*(1-τ) = 0) :
    1 ≤ A*T ∨ (0 < p ∧ 0 < q ∧ 1+1/min p q < A) := by
  classical
  by_cases hτ₁ : 1 ≤ A*T
  · exact Or.inl hτ₁
  right
  let X := p+q
  let P := p*q
  let V := Y+1
  let K := V*(P+X+1)
  let τ := A*T
  let Z := leadingF X Y P 0
  let U := (X+1)*V+P*(3*V-2)
  let W := P-V
  have hX : 0 ≤ X := add_nonneg hp hq
  have hP : 0 ≤ P := mul_nonneg hp hq
  have hV : 1 ≤ V := by dsimp [V]; linarith
  have hτ : 0 ≤ τ := mul_nonneg hA hT
  have hτ₁ : τ < 1 := lt_of_not_ge hτ₁
  have hK : 0 < K := mul_pos (by linarith) (by linarith)
  have hC : 0 < K^2*(1-τ) := mul_pos (pow_pos hK 2) (by linarith)
  have hU : 0 < U+τ*W := by
    have he : U+τ*W = V*(X+1-τ)+P*(3*V-2+τ) := by dsimp [U,W]; ring
    rw [he]
    exact add_pos_of_pos_of_nonneg (mul_pos (by linarith) (by linarith))
      (mul_nonneg hP (by linarith))
  change Z*A^2+A*K*(U+τ*W)+K^2*(1-τ) = 0 at hsec
  have hA' : 0 < A := by
    by_contra! hn
    have he := le_antisymm hn hA
    rw [he] at hsec
    simp only [zero_pow (by decide : (2 : ℕ) ≠ 0),mul_zero,zero_mul,zero_add] at hsec
    exact hC.ne' hsec
  have hZ : Z < 0 := by
    by_contra hn
    linarith [mul_nonneg (le_of_not_gt hn) (sq_nonneg A), mul_pos (mul_pos hA' hK) hU]
  have hP' : 0 < P := by
    by_contra hn
    have he := le_antisymm (le_of_not_gt hn) hP
    unfold Z leadingF at hZ
    rw [he] at hZ
    simp at hZ
    exact (not_lt_of_ge (mul_nonneg (mul_nonneg hX (by linarith)) (sq_nonneg _))) hZ
  have hp' := pos_of_mul_pos_left (show 0 < p*q from hP') hq
  have hq' := pos_of_mul_pos_right (show 0 < p*q from hP') hp
  refine ⟨hp',hq',?_⟩
  let A₀ := 1+1/min p q
  have hA₀ : 0 < A₀ := by
    dsimp [A₀]
    exact add_pos_of_pos_of_nonneg zero_lt_one (one_div_nonneg.mpr (le_min hp hq))
  have h₀ : 0 < Z*A₀+K*U+K^2/A₀ := by
    have hh := secant_div_pos_below_constantRoot hp' hq' (le_refl 0) hY hA₀
      (by simpa [Z,X,P] using hZ)
      (min_threshold_lt_constantRoot hp' hq' (le_refl 0) hY).le
    simp only [zero_add,zero_mul] at hh
    have hK' : groupedK X Y P 0 = K := by
      dsimp [groupedK,groupedG,groupedB,K,V]; ring
    have hM' : linearF X Y P 0 = K*U := by
      unfold linearF
      rw [hK']
      dsimp [groupedG,groupedB,U,V]; ring
    change 0 < Z*A₀+linearF X Y P 0+groupedK X Y P 0 ^ 2/A₀ at hh
    rw [hM',hK'] at hh
    exact hh
  have h₁ : 0 < Z*A₀+K*(U+W) := by
    have he : U+W = X*V+P*(3*V-1) := by dsimp [U,W]; ring
    rw [he]
    rcases le_total p q with h | h
    · simpa only [A₀,min_eq_left h] using gamma7_endpoint_one_pos hp' hq hY
    · have hh := gamma7_endpoint_one_pos hq' hp hY
      dsimp only at hh
      rw [add_comm q p,mul_comm q p] at hh
      simpa only [A₀,min_eq_right h] using hh
  have hdiv : Z*A+K*(U+τ*W)+K^2*(1-τ)/A = 0 := by
    have he : (Z*A+K*(U+τ*W)+K^2*(1-τ)/A)*A =
        Z*A^2+A*K*(U+τ*W)+K^2*(1-τ) := by
      field_simp
      ring
    rw [hsec] at he
    exact (mul_eq_zero.mp he).resolve_right hA'.ne'
  exact split_compensation_of_endpoints hA' hτ hτ₁ hK hU h₀ h₁ hdiv


end ZhengT40Threshold
end MOC
