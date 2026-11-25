import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The paired-cofactor comparison for T15 of Zheng, Appendix E,
DOI 10.13140/RG.2.2.36790.25923. Row and column norm constraints
suffice; no spectral or mixer enumeration is involved. -/

namespace MOC.ZhengT15

private theorem square_le_of_abs_le {a b : ℝ} (h : |a| ≤ b) : a^2 ≤ b^2 := by
  have hb : 0 ≤ b := (abs_nonneg a).trans h
  have hh := mul_le_mul h h (abs_nonneg a) hb
  simpa [← pow_two, sq_abs] using hh

private theorem nonneg_le_of_sq_le {a b : ℝ} (_ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a^2 ≤ b^2) : a ≤ b := by
  by_contra! e
  have hp := mul_pos (sub_pos.mpr e) (add_pos_of_pos_of_nonneg (hb.trans_lt e) hb)
  nlinarith only [h,hp]

/-- Two complementary cofactors have a deficit controlled by the
product of their two diagonal differences. -/
theorem cofactor_pair_deficit (u v p q a b c d : ℝ)
    (huc : u^2+c^2 ≤ 1) (hpc : p^2+c^2 ≤ 1)
    (hvd : v^2+d^2 ≤ 1) (hqd : q^2+d^2 ≤ 1) :
    ((u*p-a*c)-(v*q-b*d))^2 ≤
      (u-v)^2+(p-q)^2+2*(a^2+b^2)+2*|u-v| * |p-q| := by
  let m := max |(u+v)/2| |(p+q)/2|
  let n := Real.sqrt ((c^2+d^2)/2)
  let D := |u-v|+|p-q|
  let F := Real.sqrt (2*(a^2+b^2))
  have hn : n^2 = (c^2+d^2)/2 := by dsimp [n]; apply Real.sq_sqrt; positivity
  have hF : F^2 = 2*(a^2+b^2) := by dsimp [F]; apply Real.sq_sqrt; positivity
  have hnorm : m^2+n^2 ≤ 1 := by
    rw [hn]
    unfold m
    rcases le_total |(u+v)/2| |(p+q)/2| with h | h
    · rw [max_eq_right h,sq_abs]
      nlinarith only [sq_nonneg (p-q),hpc,hqd]
    · rw [max_eq_left h,sq_abs]
      nlinarith only [sq_nonneg (u-v),huc,hvd]
  have ha : |(p+q)/2*(u-v)+(u+v)/2*(p-q)| ≤ m*D := by
    calc
      _ ≤ |(p+q)/2*(u-v)|+|(u+v)/2*(p-q)| := abs_add_le _ _
      _ ≤ m*|u-v|+m*|p-q| := by
        simp only [abs_mul]
        exact add_le_add
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _))
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
      _ = _ := by dsimp only [D]; ring
  have hb : |a*c-b*d| ≤ n*F := by
    apply nonneg_le_of_sq_le (abs_nonneg _) (by dsimp [n,F]; positivity)
    rw [sq_abs,mul_pow,hn,hF]
    nlinarith only [sq_nonneg (a*d+b*c)]
  have hdiff : (u*p-a*c)-(v*q-b*d) =
      ((p+q)/2*(u-v)+(u+v)/2*(p-q)) + -(a*c-b*d) := by ring
  have habs : |(u*p-a*c)-(v*q-b*d)| ≤ m*D+n*F := by
    rw [hdiff]
    calc
      _ ≤ |(p+q)/2*(u-v)+(u+v)/2*(p-q)|+|-(a*c-b*d)| := abs_add_le _ _
      _ ≤ m*D+n*F := by rw [abs_neg]; exact add_le_add ha hb
  have hcs : (m*D+n*F)^2 ≤ (m^2+n^2)*(D^2+F^2) := by
    nlinarith only [sq_nonneg (m*F-n*D)]
  have hmain := (square_le_of_abs_le habs).trans
    (hcs.trans (le_of_eq_of_le rfl (by
      simpa using mul_le_mul_of_nonneg_right hnorm
        (add_nonneg (sq_nonneg D) (sq_nonneg F)))))
  rw [hF] at hmain
  unfold D at hmain
  nlinarith only [hmain,sq_abs (u-v),sq_abs (p-q)]

/-- A product bound on the two surplus coefficients absorbs the full
cofactor deficit. -/
theorem weighted_cofactor_pair (u v p q a b c d E C G : ℝ)
    (huc : u^2+c^2 ≤ 1) (hpc : p^2+c^2 ≤ 1)
    (hvd : v^2+d^2 ≤ 1) (hqd : q^2+d^2 ≤ 1)
    (hE : 0 ≤ E) (hC : 0 ≤ C) (hG : 0 ≤ G) (hCG : E^2 ≤ C*G) :
    E*((u*p-a*c)-(v*q-b*d))^2 ≤
      (E+C)*(u-v)^2+(E+G)*(p-q)^2+2*E*(a^2+b^2) := by
  let x := Real.sqrt C
  let y := Real.sqrt G
  have hx : x^2=C := Real.sq_sqrt hC
  have hy : y^2=G := Real.sq_sqrt hG
  have hxy : E ≤ x*y := by
    apply nonneg_le_of_sq_le hE (by dsimp [x,y]; positivity)
    rwa [mul_pow,hx,hy]
  have hcross := mul_le_mul_of_nonneg_right hxy
    (mul_nonneg (abs_nonneg (u-v)) (abs_nonneg (p-q)))
  have hs : 2*E*|u-v| * |p-q| ≤ C*(u-v)^2+G*(p-q)^2 := by
    have h := sq_nonneg (x*|u-v|-y*|p-q|)
    nlinarith only [h,hx,hy,hcross,
      mul_le_mul_of_nonneg_left (le_of_eq (sq_abs (u-v))) hC,
      mul_le_mul_of_nonneg_left (le_of_eq (sq_abs (u-v)).symm) hC,
      mul_le_mul_of_nonneg_left (le_of_eq (sq_abs (p-q))) hG,
      mul_le_mul_of_nonneg_left (le_of_eq (sq_abs (p-q)).symm) hG,
      congrArg (fun K => K*|u-v|^2) hx,
      congrArg (fun K => K*|p-q|^2) hy]
  have h := mul_le_mul_of_nonneg_left (cofactor_pair_deficit u v p q a b c d huc hpc hvd hqd) hE
  nlinarith only [h,hs]

end MOC.ZhengT15
