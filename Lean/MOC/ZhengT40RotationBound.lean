import MOC.ZhengT40Threshold
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-! The rotation inequality for the positive-height T40 overlap in
Zheng (preprint DOI: 10.13140/RG.2.2.36790.25923, Section 5).
The hypotheses are the displayed cofactor identities and norm bounds
of a real special orthogonal three-by-three matrix. -/

namespace MOC.ZhengT40RotationBound

/-- The entries and identities used from an oriented three-dimensional
rotation. Each identity is a cofactor or an immediate row/column bound. -/
structure Entries where
  l : ℝ -- entry 00
  u : ℝ -- entry 01
  z : ℝ -- entry 02
  p : ℝ -- entry 10
  j : ℝ -- entry 11
  w : ℝ -- entry 12
  c : ℝ -- entry 20
  b : ℝ -- entry 21
  v : ℝ -- entry 22
  cofactor21 : b = z*p - l*w
  cofactor12 : w = c*u - l*b
  cofactor00 : w*b = -l + j*v
  column2 : z^2 + w^2 + v^2 = 1
  column1 : j^2 + b^2 ≤ 1
  row2 : c^2 ≤ 1
  row0 : l^2 + z^2 ≤ 1

/-- An oriented orthogonal matrix supplies the Gram inputs by the
adjugate identity and the Euclidean row and column norms. -/
def Entries.ofMatrix (M : Matrix (Fin 3) (Fin 3) ℝ)
    (hcol : M.transpose * M = 1) (hrow : M * M.transpose = 1)
    (hdet : M.det = 1) : Entries := by
  have hadj : M.adjugate = M.transpose := by
    calc
      M.adjugate = M.adjugate * 1 := (Matrix.mul_one _).symm
      _ = M.adjugate * (M * M.transpose) := by rw [hrow]
      _ = M.adjugate * M * M.transpose := (Matrix.mul_assoc _ _ _).symm
      _ = M.transpose := by rw [Matrix.adjugate_mul,hdet,one_smul,Matrix.one_mul]
  have ha (i j : Fin 3) := congrArg (fun N : Matrix (Fin 3) (Fin 3) ℝ => N i j) hadj
  have hn (i : Fin 3) :=
    congrArg (fun N : Matrix (Fin 3) (Fin 3) ℝ => N i i) hcol
  have hm (i : Fin 3) :=
    congrArg (fun N : Matrix (Fin 3) (Fin 3) ℝ => N i i) hrow
  refine ⟨M 0 0,M 0 1,M 0 2,M 1 0,M 1 1,M 1 2,M 2 0,M 2 1,M 2 2,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := ha 1 2
    simp [Matrix.adjugate_fin_three,Matrix.transpose_apply] at h
    linarith only [h]
  · have h := ha 2 1
    simp [Matrix.adjugate_fin_three,Matrix.transpose_apply] at h
    linarith only [h]
  · have h := ha 0 0
    simp [Matrix.adjugate_fin_three,Matrix.transpose_apply] at h
    linarith only [h]
  · have h := hn 2
    simp [Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,pow_two,add_assoc] at h ⊢
    exact h
  · have h := hn 1
    simp [Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ] at h
    nlinarith only [h,sq_nonneg (M 0 1)]
  · have h := hm 2
    simp [Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ] at h
    nlinarith only [h,sq_nonneg (M 2 1),sq_nonneg (M 2 2)]
  · have h := hm 0
    simp [Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ] at h
    nlinarith only [h,sq_nonneg (M 0 1)]

private theorem six_cs (x₀ x₁ x₂ x₃ x₄ x₅ y₀ y₁ y₂ y₃ y₄ y₅ : ℝ) :
    (x₀*y₀ + x₁*y₁ + x₂*y₂ + x₃*y₃ + x₄*y₄ + x₅*y₅)^2 ≤
      (x₀^2 + x₁^2 + x₂^2 + x₃^2 + x₄^2 + x₅^2) *
      (y₀^2 + y₁^2 + y₂^2 + y₃^2 + y₄^2 + y₅^2) := by
  let x : Fin 6 → ℝ := ![x₀,x₁,x₂,x₃,x₄,x₅]
  let y : Fin 6 → ℝ := ![y₀,y₁,y₂,y₃,y₄,y₅]
  simpa [x,y, Fin.sum_univ_succ,add_assoc] using
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x y)

set_option maxHeartbeats 1600000 in
/-- The difference of the (2,1) entries is controlled by the available
positive two-minor terms. The constant `T` includes the unit contribution
already present in the mixed ray. -/
theorem rotation_bound (L R : Entries) {T m : ℝ}
    (hm : 0 < m) (hT : 2 + 1/m ≤ T) :
    (L.b-R.b)^2 ≤ (L.l-R.l)^2 + 2*(L.p^2+R.p^2) +
      T*(L.w-R.w)^2 + 2*m*(L.u^2+R.u^2) := by
  let l := (L.l+R.l)/2
  let w := (L.w+R.w)/2
  let B := (L.b+R.b)/2
  let d := L.l-R.l
  let a := L.w-R.w
  let b := L.b-R.b
  let B₀ := (L.v^2+R.v^2)/2+a^2/4
  let e := (L.j*L.v+R.j*R.v)/2-a*b/4
  let θ := -l/T
  have hT₀ : 0 < T := by linarith [one_div_pos.mpr hm]
  have hT₁ : 1 ≤ T := by linarith [one_div_pos.mpr hm]
  have hB₀ : 0 ≤ B₀ := by dsimp [B₀]; positivity
  have heq₀ : B₀ = 1-w^2-(L.z^2+R.z^2)/2 := by
    dsimp [B₀,w,a]; nlinarith only [L.column2,R.column2]
  have heq₁ : w*B = -l+e := by
    dsimp [w,B,e,l,a,b]; nlinarith only [L.cofactor00,R.cofactor00]
  have hJ : (L.j^2+R.j^2)/2+b^2/4 ≤ 1 := by
    dsimp [b]
    nlinarith only [L.column1,R.column1,sq_nonneg (L.b+R.b)]
  have hB₂ : B^2 ≤ 1 := by
    dsimp [B]
    nlinarith only [L.column1,R.column1,sq_nonneg L.j,sq_nonneg R.j,
      sq_nonneg (L.b-R.b)]
  have he : e^2 ≤ B₀ := by
    have hCS : e^2 ≤ ((L.j^2+R.j^2)/2+b^2/4)*B₀ := by
      dsimp [e,B₀]
      have hs : 0 ≤ (L.j*R.v-R.j*L.v)^2/4 +
          (L.j*a+b*L.v)^2/8 + (R.j*a+b*R.v)^2/8 := by positivity
      have heq : ((L.j^2+R.j^2)/2+b^2/4)*((L.v^2+R.v^2)/2+a^2/4) -
          ((L.j*L.v+R.j*R.v)/2-a*b/4)^2 =
          (L.j*R.v-R.j*L.v)^2/4 + (L.j*a+b*L.v)^2/8 + (R.j*a+b*R.v)^2/8 := by
        ring
      linarith only [hs,heq]
    exact hCS.trans (by simpa using mul_le_mul_of_nonneg_right hJ hB₀)
  have hb₁ : b = L.z*L.p-R.z*R.p-w*d-l*a := by
    dsimp [b,w,d,l,a]
    nlinarith only [L.cofactor21,R.cofactor21]
  have hb₂ : a = L.c*L.u-R.c*R.u-B*d-l*b := by
    dsimp [a,B,d,l,b]
    nlinarith only [L.cofactor12,R.cofactor12]
  have hlinear :
      (1-θ*l)*b = (-w+θ*B)*d+L.z*L.p-R.z*R.p+
        (-l+θ)*a-θ*L.c*L.u+θ*R.c*R.u := by
    nlinarith only [hb₁, congrArg (fun x : ℝ => θ*x) hb₂]
  let N := (-w+θ*B)^2 + L.z^2/2 + R.z^2/2 +
    (-l+θ)^2/T + θ^2*L.c^2/(2*m) + θ^2*R.c^2/(2*m)
  have hnorm :
      (1-θ*l)^2 - N = B₀-l^2/T + 2*θ*(-(2-1/T)*l+e) +
        θ^2*(l^2-B^2-1/T-(L.c^2+R.c^2)/(2*m)) := by
    dsimp [N]
    simp only [div_eq_mul_inv, mul_inv_rev]
    linear_combination -heq₀ + (2*θ)*heq₁
  have hrow : (L.c^2+R.c^2)/(2*m) ≤ 1/m := by
    rw [div_le_iff₀ (by positivity : 0 < 2*m)]
    have hm' : m ≠ 0 := ne_of_gt hm
    field_simp [hm']
    nlinarith only [L.row2,R.row2]
  have hcross : -B₀-θ^2 ≤ 2*θ*e := by nlinarith only [he,sq_nonneg (θ+e)]
  have hcoeff : 0 ≤ 3*T-4-1/T-1/m := by
    have ht : 1/T ≤ 1 := (div_le_iff₀ hT₀).2 (by simpa using hT₁)
    linarith [one_div_pos.mpr hm]
  have hN : N ≤ (1-θ*l)^2 := by
    have hq : -(1+1/T+1/m) ≤ l^2-B^2-1/T-(L.c^2+R.c^2)/(2*m) := by
      linarith [sq_nonneg l]
    have hqb := mul_le_mul_of_nonneg_left hq (sq_nonneg θ)
    have hlow : (l/T)^2*(3*T-4-1/T-1/m) ≤ (1-θ*l)^2-N := by
      have heq : -l^2/T + 2*θ*(-(2-1/T)*l) -
          θ^2*(2+1/T+1/m) = (l/T)^2*(3*T-4-1/T-1/m) := by
        dsimp [θ]
        have hne : T ≠ 0 := ne_of_gt hT₀
        field_simp [hne]
        ring
      rw [← heq, hnorm]
      have hs := add_le_add hcross hqb
      have hshift := add_le_add_left hs (B₀-l^2/T+2*θ*(-(2-1/T)*l))
      convert hshift using 1 <;> ring
    exact sub_nonneg.mp ((mul_nonneg (sq_nonneg (l/T)) hcoeff).trans hlow)
  let s₂ := Real.sqrt 2
  let sT := Real.sqrt T
  let sm := Real.sqrt (2*m)
  have hs₂ : 0 < s₂ := Real.sqrt_pos.2 (by norm_num)
  have hsT : 0 < sT := Real.sqrt_pos.2 hT₀
  have hsm : 0 < sm := Real.sqrt_pos.2 (by positivity)
  have hs₂q : s₂^2 = 2 := Real.sq_sqrt (by norm_num)
  have hsTq : sT^2 = T := Real.sq_sqrt hT₀.le
  have hsmq : sm^2 = 2*m := Real.sq_sqrt (by positivity)
  have hcs := six_cs (-w+θ*B) (L.z/s₂) (-R.z/s₂) ((-l+θ)/sT)
    (-θ*L.c/sm) (θ*R.c/sm) d (s₂*L.p) (s₂*R.p) (sT*a) (sm*L.u) (sm*R.u)
  have hx : (-w+θ*B)*d + (L.z/s₂)*(s₂*L.p) + (-R.z/s₂)*(s₂*R.p) +
      ((-l+θ)/sT)*(sT*a) + (-θ*L.c/sm)*(sm*L.u) +
      (θ*R.c/sm)*(sm*R.u) = (1-θ*l)*b := by
    rw [hlinear]
    field_simp [ne_of_gt hs₂,ne_of_gt hsT,ne_of_gt hsm]
    ring
  have hy : (-w+θ*B)^2 + (L.z/s₂)^2 + (-R.z/s₂)^2 + ((-l+θ)/sT)^2 +
      (-θ*L.c/sm)^2 + (θ*R.c/sm)^2 = N := by
    simp only [N,div_pow,hs₂q,hsTq,hsmq]
    ring
  have hz : d^2 + (s₂*L.p)^2 + (s₂*R.p)^2 + (sT*a)^2 + (sm*L.u)^2 +
      (sm*R.u)^2 = d^2 + 2*(L.p^2+R.p^2)+T*a^2+2*m*(L.u^2+R.u^2) := by
    simp only [mul_pow,hs₂q,hsTq,hsmq]
    ring
  rw [hx,hy,hz,mul_pow] at hcs
  have hp : 0 < (1-θ*l)^2 := by
    have hp' : 0 ≤ l^2/T := div_nonneg (sq_nonneg _) hT₀.le
    have heq : 1-θ*l = 1+l^2/T := by dsimp [θ]; ring
    rw [heq]; positivity
  have h := hcs.trans (mul_le_mul_of_nonneg_right hN (by positivity :
    0 ≤ d^2 + 2*(L.p^2+R.p^2)+T*a^2+2*m*(L.u^2+R.u^2)))
  exact (mul_le_mul_left hp).1 h

/-- The signed two-minor expression after the self-dual and anti-self-dual
decomposition, multiplied by four. Its nonnegativity retains all five
ordinary coefficients of the center-and-split T40 overlap. -/
theorem weighted_signed_minors (L R : Entries) {A p q r s : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hA : 1 + 1 / min p q ≤ A) :
    0 ≤ (1+s)*(L.p+R.p)^2 + (1+r)*(L.p-R.p)^2 +
      (1+A)*(L.w-R.w)^2 + (L.l-R.l)^2 +
      q*(L.u+R.u)^2+p*(L.u-R.u)^2-(L.b-R.b)^2 := by
  let m := min p q
  have hm : 0 < m := lt_min hp hq
  have hT : 2 + 1/m ≤ 1+A := by
    change 1 + 1/m ≤ A at hA
    linarith
  have h := rotation_bound L R hm hT
  have hq' : 0 ≤ q-m := sub_nonneg.mpr (min_le_right _ _)
  have hp' : 0 ≤ p-m := sub_nonneg.mpr (min_le_left _ _)
  have hn : 0 ≤ s*(L.p+R.p)^2 + r*(L.p-R.p)^2 +
      (q-m)*(L.u+R.u)^2 + (p-m)*(L.u-R.u)^2 := by positivity
  calc
    0 ≤ (L.l-R.l)^2 + 2*(L.p^2+R.p^2) +
        (1+A)*(L.w-R.w)^2 + 2*m*(L.u^2+R.u^2)-(L.b-R.b)^2 +
        (s*(L.p+R.p)^2+r*(L.p-R.p)^2+
          (q-m)*(L.u+R.u)^2+(p-m)*(L.u-R.u)^2) :=
        add_nonneg (sub_nonneg.mpr h) hn
    _ = _ := by ring

/-- The exact secant polynomial suffices for the full signed comparison
in the normalized center-and-split T40 overlap. The derivation of
that polynomial from actual spectra is separate from this theorem. -/
theorem weighted_of_secant (L R : Entries) {A p q r s : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) (hs : 0 ≤ s) (hA : 0 ≤ A)
    (hsec : ZhengT40Threshold.secantF (p+q) (r+s) (p*q) (r*s) A = 0) :
    0 ≤ (1+s)*(L.p+R.p)^2 + (1+r)*(L.p-R.p)^2 +
      (1+A)*(L.w-R.w)^2 + (L.l-R.l)^2 +
      q*(L.u+R.u)^2+p*(L.u-R.u)^2-(L.b-R.b)^2 := by
  obtain ⟨hp',hq',_,hcomp⟩ :=
    ZhengT40Threshold.compensation_or_impossible hp hq hr hs hA hsec
  exact weighted_signed_minors L R hp' hq' hr hs hcomp.le

/-- A coefficient on the defect minor can replace the two small
off-diagonal terms. The reciprocal-weight test reduces to \`A*D ≥ 1\`. -/
theorem rotation_bound_of_defect (L R : Entries) {A D : ℝ}
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hAD : 1 ≤ A*D) :
    (L.b-R.b)^2 ≤ (1+D)*(L.l-R.l)^2 +
      2*(L.p^2+R.p^2) + (1+A)*(L.w-R.w)^2 := by
  let l := (L.l+R.l)/2
  let w := (L.w+R.w)/2
  let Z := (L.z^2+R.z^2)/2
  have hZ : 0 ≤ 1-Z := by
    dsimp [Z]
    nlinarith only [L.row0,R.row0,sq_nonneg L.l,sq_nonneg R.l]
  have hl : l^2 ≤ 1-Z := by
    dsimp [l,Z]
    nlinarith only [L.row0,R.row0,sq_nonneg (L.l-R.l)]
  have hw : w^2 ≤ 1-Z := by
    dsimp [w,Z]
    nlinarith only [L.column2,R.column2,sq_nonneg L.v,sq_nonneg R.v,
      sq_nonneg (L.w-R.w)]
  have hAp : 0 < 1+A := by positivity
  have hDp : 0 < 1+D := by positivity
  have hinv : 1/(1+D)+1/(1+A) ≤ 1 := by
    rw [div_add_div _ _ hDp.ne' hAp.ne', div_le_iff₀ (mul_pos hDp hAp)]
    linarith only [show 1*(1+A)+1*(1+D) ≤ 1*((1+D)*(1+A)) by nlinarith only [hAD]]
  have hn : w^2/(1+D)+l^2/(1+A)+Z ≤ 1 := by
    calc
      _ ≤ (1-Z)/(1+D)+(1-Z)/(1+A)+Z :=
        add_le_add_right (add_le_add (div_le_div_of_nonneg_right hw hDp.le)
          (div_le_div_of_nonneg_right hl hAp.le)) _
      _ = (1-Z)*(1/(1+D)+1/(1+A))+Z := by ring
      _ ≤ (1-Z)*1+Z := add_le_add_right (mul_le_mul_of_nonneg_left hinv hZ) _
      _ = 1 := by ring
  let s₂ := Real.sqrt 2
  let sA := Real.sqrt (1+A)
  let sD := Real.sqrt (1+D)
  have hs₂ : 0 < s₂ := Real.sqrt_pos.2 (by norm_num)
  have hsA : 0 < sA := Real.sqrt_pos.2 hAp
  have hsD : 0 < sD := Real.sqrt_pos.2 hDp
  have hs₂q : s₂^2 = 2 := Real.sq_sqrt (by norm_num)
  have hsAq : sA^2 = 1+A := Real.sq_sqrt hAp.le
  have hsDq : sD^2 = 1+D := Real.sq_sqrt hDp.le
  have hf : L.b-R.b = -w*(L.l-R.l)-l*(L.w-R.w)+L.z*L.p-R.z*R.p := by
    dsimp [w,l]
    nlinarith only [L.cofactor21,R.cofactor21]
  have hx : (-w/sD)*(sD*(L.l-R.l))+(-l/sA)*(sA*(L.w-R.w))+
      (L.z/s₂)*(s₂*L.p)+(-R.z/s₂)*(s₂*R.p)+0*0+0*0 = L.b-R.b := by
    rw [hf]
    field_simp [hsD.ne',hsA.ne',hs₂.ne']
    ring
  have hy : (-w/sD)^2+(-l/sA)^2+(L.z/s₂)^2+(-R.z/s₂)^2+0^2+0^2 =
      w^2/(1+D)+l^2/(1+A)+Z := by
    simp only [Z,div_pow,hs₂q,hsAq,hsDq]
    ring
  have hz : (sD*(L.l-R.l))^2+(sA*(L.w-R.w))^2+(s₂*L.p)^2+(s₂*R.p)^2+0^2+0^2 =
      (1+D)*(L.l-R.l)^2+2*(L.p^2+R.p^2)+(1+A)*(L.w-R.w)^2 := by
    simp only [mul_pow,hs₂q,hsAq,hsDq]
    ring
  have h := six_cs (-w/sD) (-l/sA) (L.z/s₂) (-R.z/s₂) 0 0
    (sD*(L.l-R.l)) (sA*(L.w-R.w)) (s₂*L.p) (s₂*R.p) 0 0
  rw [hx,hy,hz] at h
  exact h.trans (by simpa using mul_le_mul_of_nonneg_right hn (by positivity :
    0 ≤ (1+D)*(L.l-R.l)^2+2*(L.p^2+R.p^2)+(1+A)*(L.w-R.w)^2))

set_option maxHeartbeats 1200000 in
/-- The complementary minor of the negative entry can replace the
defect term when its coefficient \(B\) and the other split coefficient
\(A\) satisfy \(AB\ge 1\). -/
theorem rotation_bound_of_complement (L R : Entries) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hAB : 1 ≤ A*B) :
    (L.b-R.b)^2 ≤ (L.l-R.l)^2 + 2*(L.p^2+R.p^2) +
      (1+A)*(L.w-R.w)^2+B*(L.b+R.b)^2 := by
  let l := (L.l+R.l)/2
  let w := (L.w+R.w)/2
  let K := (L.b+R.b)/2
  let d := L.l-R.l
  let a := L.w-R.w
  let b := L.b-R.b
  let c := L.b+R.b
  let B₀ := (L.v^2+R.v^2)/2+a^2/4
  let e := (L.j*L.v+R.j*R.v)/2-a*b/4
  have hB₀ : 0 ≤ B₀ := by dsimp [B₀]; positivity
  have heq₀ : B₀ = 1-w^2-(L.z^2+R.z^2)/2 := by
    dsimp [B₀,w,a]; nlinarith only [L.column2,R.column2]
  have heq₁ : w*K = -l+e := by
    dsimp [w,K,e,l,a,b]; nlinarith only [L.cofactor00,R.cofactor00]
  have hJ : (L.j^2+R.j^2)/2+b^2/4 ≤ 1 := by
    dsimp [b]
    nlinarith only [L.column1,R.column1,sq_nonneg (L.b+R.b)]
  have he : e^2 ≤ B₀ := by
    have hCS : e^2 ≤ ((L.j^2+R.j^2)/2+b^2/4)*B₀ := by
      dsimp [e,B₀]
      have hs : 0 ≤ (L.j*R.v-R.j*L.v)^2/4 +
          (L.j*a+b*L.v)^2/8 + (R.j*a+b*R.v)^2/8 := by positivity
      have heq : ((L.j^2+R.j^2)/2+b^2/4)*((L.v^2+R.v^2)/2+a^2/4) -
          ((L.j*L.v+R.j*R.v)/2-a*b/4)^2 =
          (L.j*R.v-R.j*L.v)^2/4 + (L.j*a+b*L.v)^2/8 + (R.j*a+b*R.v)^2/8 := by
        ring
      linarith only [hs,heq]
    exact hCS.trans (by simpa using mul_le_mul_of_nonneg_right hJ hB₀)
  have hb₀ : b = L.z*L.p-R.z*R.p-w*d-l*a := by
    dsimp [b,w,d,l,a]
    nlinarith only [L.cofactor21,R.cofactor21]
  have hf : b-w*K*a = L.z*L.p-R.z*R.p-w*d-e*a := by
    linear_combination hb₀-a*heq₁
  let E := d^2+2*(L.p^2+R.p^2)+a^2
  have hEn : 0 ≤ E := by dsimp [E]; positivity
  have hcauchy : (b-w*K*a)^2 ≤ E := by
    let s₂ := Real.sqrt 2
    have hs₂ : 0 < s₂ := Real.sqrt_pos.2 (by norm_num)
    have hs₂q : s₂^2 = 2 := Real.sq_sqrt (by norm_num)
    have h := six_cs (L.z/s₂) (-R.z/s₂) (-w) (-e) 0 0
      (s₂*L.p) (s₂*R.p) d a 0 0
    have hx : (L.z/s₂)*(s₂*L.p)+(-R.z/s₂)*(s₂*R.p)+(-w)*d+(-e)*a+0*0+0*0 =
        b-w*K*a := by
      rw [hf]
      field_simp [hs₂.ne']
      ring
    have hy : (L.z/s₂)^2+(-R.z/s₂)^2+(-w)^2+(-e)^2+0^2+0^2 =
        w^2+(L.z^2+R.z^2)/2+e^2 := by
      simp only [div_pow,hs₂q]
      ring
    have hz : (s₂*L.p)^2+(s₂*R.p)^2+d^2+a^2+0^2+0^2 = E := by
      simp only [E,mul_pow,hs₂q]
      ring
    rw [hx,hy,hz] at h
    have hn : w^2+(L.z^2+R.z^2)/2+e^2 ≤ 1 := by
      calc
        _ ≤ w^2+(L.z^2+R.z^2)/2+B₀ := add_le_add_left he _
        _ = 1 := by rw [heq₀]; ring
    exact h.trans (by simpa using mul_le_mul_of_nonneg_right hn hEn)
  have hw : |w| ≤ 1 := by
    rw [abs_le]
    have h₀ : w^2 ≤ 1 := by
      have hz : 0 ≤ (L.z^2+R.z^2)/2 := by positivity
      calc
        w^2 ≤ w^2+(L.z^2+R.z^2)/2+B₀ := by
          exact le_trans (le_add_of_nonneg_right hz) (le_add_of_nonneg_right hB₀)
        _ = 1 := by rw [heq₀]; ring
    constructor <;> nlinarith only [h₀,sq_nonneg (w-1),sq_nonneg (w+1)]
  have hb : |b| ≤ 2 := by
    rw [abs_le]
    have h₀ : b^2 ≤ 4 := by
      have hj : 0 ≤ (L.j^2+R.j^2)/2 := by positivity
      have hbq : b^2/4 ≤ 1 := le_trans (le_add_of_nonneg_left hj) hJ
      simpa using (div_le_iff₀ (by norm_num : 0 < (4 : ℝ))).1 hbq
    constructor <;> nlinarith only [h₀,sq_nonneg (b-2),sq_nonneg (b+2)]
  have hwb : |w*b| ≤ 2 := by
    rw [abs_mul]
    exact le_trans (mul_le_mul_of_nonneg_right hw (abs_nonneg b)) (by simpa using hb)
  have hcross : w*K*a*b*2 ≤ 2*|a*c| := by
    have h₁ := mul_le_mul_of_nonneg_right hwb (abs_nonneg (a*c))
    rw [← abs_mul] at h₁
    have h₂ := le_abs_self ((w*b)*(a*c))
    have h₃ : w*K*a*b*2 = (w*b)*(a*c) := by dsimp [K,c]; ring
    rw [h₃]
    exact h₂.trans h₁
  have hAy : 2*|a*c| ≤ A*a^2+B*c^2 := by
    let sA := Real.sqrt A
    let sB := Real.sqrt B
    have hsqA : sA^2 = A := Real.sq_sqrt hA
    have hsqB : sB^2 = B := Real.sq_sqrt hB
    have hp : 1 ≤ sA*sB := by
      refine le_of_pow_le_pow_left₀ (by decide : (2 : ℕ) ≠ 0) (by positivity : 0 ≤ sA*sB) ?_
      simpa [mul_pow,hsqA,hsqB] using hAB
    have h := sq_nonneg (sA*|a|-sB*|c|)
    have heq : (sA*|a|-sB*|c|)^2 = A*a^2+B*c^2-2*(sA*sB)*|a*c| := by
      rw [abs_mul]
      linear_combination
        (norm := ring_nf)
        |a|^2*hsqA+|c|^2*hsqB+
        A*(sq_abs a)+B*(sq_abs c)
    have hmul := mul_le_mul_of_nonneg_right hp (abs_nonneg (a*c))
    linarith only [h,heq,hmul]
  have hmain : b^2 ≤ E+A*a^2+B*c^2 := by
    have hq := sq_nonneg (w*K*a)
    nlinarith only [hcauchy,hq,hcross,hAy]
  calc
    _ ≤ E+A*a^2+B*c^2 := hmain
    _ = _ := by dsimp [E,d,a,c]; ring

end MOC.ZhengT40RotationBound
