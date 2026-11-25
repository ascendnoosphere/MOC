import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! Exact symbolic sign certificate for the T55+20 overlap with gap 23
zero in Zheng, DOI: 10.13140/RG.2.2.36790.25923.
The Hessian computation identifying the following secant factor is
separate. This file checks its sign on the two parameter boxes algebraically. -/

namespace MOC.ZhengT55Boundary23
noncomputable section

private def f0 (p q X Y : ℝ) : ℝ :=
    ((p + 1)^2*(X + Y + 1)^2) * q^0 +
    ((p + 1)*(X + Y + 1)*(X*p + X + 3*Y*p + Y + p + 1)) * q^1 +
    (X^2*p^2 + 2*X^2*p + X^2 - X*Y*p - X*Y + X*p^2 + 2*X*p + X - 3*Y^2*p - 2*Y^2 - Y*p^2 - 3*Y*p - 2*Y) * q^2
private def f1 (p q X Y : ℝ) : ℝ :=
    ((p + 1)^2*(X + Y + 1)^2) * q^0 +
    (-X*p*(p + 1)*(X + Y + 1)) * q^1 +
    (X^2*p + X^2 + X*Y*p - X*p^2 - X*p - Y^2 - 2*Y*p - 2*Y - p^2 - 2*p - 1) * q^2
private def f2 (p q X Y : ℝ) : ℝ :=
    (p*(p + 1)*(X + Y + 1)^2) * q^0 +
    ((X + Y + 1)*(-X*p - X - 2*Y*p - Y + p^2 - 1)) * q^1 +
    (-(X + Y + 1)*(-Y + p + 1)) * q^2

def secantFactor (p q r s A : ℝ) : ℝ :=
    f0 p q (r+s) (r*s) + A * f1 p q (r+s) (r*s) + A^2 * f2 p q (r+s) (r*s)

private def c0 (p q r s : ℝ) : ℝ := q^2 * f0 p q (r+s) (r*s)
private def c1 (p q r s : ℝ) : ℝ := c0 p q r s + q * f1 p q (r+s) (r*s) / 2
private def c2 (p q r s : ℝ) : ℝ := c0 p q r s + q * f1 p q (r+s) (r*s) + f2 p q (r+s) (r*s)

private theorem secant_bernstein (p q r s A : ℝ) :
    q^2 * secantFactor p q r s A =
       (1-A*q)^2 * c0 p q r s + 2*(A*q)*(1-A*q)*c1 p q r s +
       (A*q)^2 * c2 p q r s := by
  unfold secantFactor c1 c2 c0
  ring

set_option maxHeartbeats 2000000 in
private theorem low_c0 (p q r s : ℝ) (hp : 0 ≤ p) (hq : 0 < q)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hqp : q ≤ p+1) : 0 < c0 p q r s := by
  have hqr : 0 ≤ p+1-q := sub_nonneg.mpr hqp
  have h : (p+1)^4 * c0 p q r s =
    ((p + 1)^4*(r + 1)^2*(s + 1)^2) * q^2 * (p+1-q)^2 +
    ((p + 1)^4*(r + 1)*(s + 1)*(3*p*r*s + p*r + p*s + p + 3*r*s + 3*r + 3*s + 3)) * q^3 * (p+1-q)^1 +
    ((p + 1)^4*(p^2*r^2 + p^2*r*s + p^2*r + p^2*s^2 + p^2*s + 3*p*r^2*s + 3*p*r^2 + 3*p*r*s^2 + 7*p*r*s + 4*p*r + 3*p*s^2 + 4*p*s + p + 3*r^2*s + 3*r^2 + 3*r*s^2 + 8*r*s + 5*r + 3*s^2 + 5*s + 2)) * q^4 * (p+1-q)^0 := by
    unfold c0 f0
    ring
  have hm : 0 < (p+1)^4 * c0 p q r s := by rw [h]; positivity
  have hscale : 0 < (p+1)^4 := by positivity
  exact pos_of_mul_pos_right hm hscale.le

set_option maxHeartbeats 2000000 in
private theorem low_c1 (p q r s : ℝ) (hp : 0 ≤ p) (hq : 0 < q)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hqp : q ≤ p+1) : 0 ≤ c1 p q r s := by
  have hqr : 0 ≤ p+1-q := sub_nonneg.mpr hqp
  have h : (p+1)^4 * c1 p q r s =
    ((p + 1)^3*(r + 1)^2*(s + 1)^2/2) * q^1 * (p+1-q)^3 +
    ((p + 1)^3*(r + 1)*(s + 1)*(2*p*r*s + p*r + p*s + 2*p + 5*r*s + 5*r + 5*s + 5)/2) * q^2 * (p+1-q)^2 +
    ((p + 1)^3*(6*p^2*r^2*s^2 + 8*p^2*r^2*s + 2*p^2*r^2 + 8*p^2*r*s^2 + 12*p^2*r*s + 3*p^2*r + 2*p^2*s^2 + 3*p^2*s + p^2 + 12*p*r^2*s^2 + 19*p*r^2*s + 7*p*r^2 + 19*p*r*s^2 + 32*p*r*s + 13*p*r + 7*p*s^2 + 13*p*s + 6*p + 8*r^2*s^2 + 18*r^2*s + 10*r^2 + 18*r*s^2 + 36*r*s + 18*r + 10*s^2 + 18*s + 8)/2) * q^3 * (p+1-q)^1 +
    ((p + 1)^3*(2*p^3*r^2 + 2*p^3*r*s + 2*p^3*r + 2*p^3*s^2 + 2*p^3*s + 6*p^2*r^2*s + 8*p^2*r^2 + 6*p^2*r*s^2 + 16*p^2*r*s + 9*p^2*r + 8*p^2*s^2 + 9*p^2*s + p^2 + 12*p*r^2*s + 12*p*r^2 + 12*p*r*s^2 + 28*p*r*s + 16*p*r + 12*p*s^2 + 16*p*s + 4*p + 8*r^2*s + 8*r^2 + 8*r*s^2 + 20*r*s + 12*r + 8*s^2 + 12*s + 4)/2) * q^4 * (p+1-q)^0 := by
    unfold c1 c0 f0 f1
    ring
  have hm : 0 ≤ (p+1)^4 * c1 p q r s := by rw [h]; positivity
  have hscale : 0 < (p+1)^4 := by positivity
  exact nonneg_of_mul_nonneg_right hm hscale

set_option maxHeartbeats 2000000 in
private theorem low_c2 (p q r s : ℝ) (hp : 0 ≤ p) (hq : 0 < q)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hqp : q ≤ p+1) : 0 ≤ c2 p q r s := by
  have hqr : 0 ≤ p+1-q := sub_nonneg.mpr hqp
  have h : (p+1)^4 * c2 p q r s =
    (p*(p + 1)*(r + 1)^2*(s + 1)^2) * q^0 * (p+1-q)^4 +
    (p*(p + 1)*(r + 1)*(s + 1)*(p*r*s + p*r + p*s + 2*p + 4*r*s + 5*r + 5*s + 6)) * q^1 * (p+1-q)^3 +
    ((p + 1)*(r + 1)*(s + 1)*(p^3*r*s + p^3 + 6*p^2*r*s + 4*p^2*r + 4*p^2*s + 8*p^2 + 10*p*r*s + 11*p*r + 11*p*s + 13*p + 2*r*s + r + s)) * q^2 * (p+1-q)^2 +
    ((p + 1)*(3*p^4*r^2*s^2 + 4*p^4*r^2*s + p^4*r^2 + 4*p^4*r*s^2 + 6*p^4*r*s + p^4*r + p^4*s^2 + p^4*s + 12*p^3*r^2*s^2 + 17*p^3*r^2*s + 5*p^3*r^2 + 17*p^3*r*s^2 + 26*p^3*r*s + 7*p^3*r + 5*p^3*s^2 + 7*p^3*s + 2*p^3 + 20*p^2*r^2*s^2 + 34*p^2*r^2*s + 14*p^2*r^2 + 34*p^2*r*s^2 + 59*p^2*r*s + 24*p^2*r + 14*p^2*s^2 + 24*p^2*s + 10*p^2 + 16*p*r^2*s^2 + 34*p*r^2*s + 18*p*r^2 + 34*p*r*s^2 + 64*p*r*s + 30*p*r + 18*p*s^2 + 30*p*s + 12*p + 4*r^2*s^2 + 8*r^2*s + 4*r^2 + 8*r*s^2 + 12*r*s + 4*r + 4*s^2 + 4*s)) * q^3 * (p+1-q)^1 +
    ((p + 1)*(p^5*r^2 + p^5*r*s + p^5*r + p^5*s^2 + p^5*s + 3*p^4*r^2*s + 6*p^4*r^2 + 3*p^4*r*s^2 + 10*p^4*r*s + 6*p^4*r + 6*p^4*s^2 + 6*p^4*s + 12*p^3*r^2*s + 15*p^3*r^2 + 12*p^3*r*s^2 + 30*p^3*r*s + 16*p^3*r + 15*p^3*s^2 + 16*p^3*s + p^3 + 20*p^2*r^2*s + 21*p^2*r^2 + 20*p^2*r*s^2 + 46*p^2*r*s + 25*p^2*r + 21*p^2*s^2 + 25*p^2*s + 4*p^2 + 16*p*r^2*s + 16*p*r^2 + 16*p*r*s^2 + 36*p*r*s + 20*p*r + 16*p*s^2 + 20*p*s + 4*p + 4*r^2*s + 4*r^2 + 4*r*s^2 + 8*r*s + 4*r + 4*s^2 + 4*s)) * q^4 * (p+1-q)^0 := by
    unfold c2 c0 f0 f1 f2
    ring
  have hm : 0 ≤ (p+1)^4 * c2 p q r s := by rw [h]; positivity
  have hscale : 0 < (p+1)^4 := by positivity
  exact nonneg_of_mul_nonneg_right hm hscale

set_option maxHeartbeats 2500000 in
private theorem high_c0 (p t r s : ℝ) (hp : 0 ≤ p) (ht : 0 < t)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hrb : (p+t)*r < 1) : 0 < c0 p (p+1+t) r s := by
  have hu : 0 < p+t := by positivity
  have hρ : 0 ≤ (p+t)*r := by positivity
  have hρ' : 0 < 1-(p+t)*r := sub_pos.mpr hrb
  have h : (p+t)^2 * c0 p (p+1+t) r s =
      (1-(p+t)*r)^2 * (((p + 1)^2*(p + t)^2*(p + t + 1)^2*(p + t + 2))*s^0 +
       ((p + 1)^2*(p + t)^2*(p + t + 1)^2*(p^2 + 2*p*t + 4*p + t^2 + 4*t + 5))*s^1 +
       ((p + 1)^2*(p + t)^2*(p + t + 1)^2*(p^2 + 2*p*t + 3*p + t^2 + 3*t + 3))*s^2) +
      2*((p+t)*r)*(1-(p+t)*r)*(((p + 1)^2*(p + t)*(p + t + 1)^3*(3*p + 3*t + 5)/2)*s^0 +
       ((p + 1)*(p + t)*(p + t + 1)^3*(2*p^3 + 4*p^2*t + 9*p^2 + 2*p*t^2 + 11*p*t + 17*p + 2*t^2 + 6*t + 8)/2)*s^1 +
       ((p + 1)*(p + t)*(p + t + 1)^3*(2*p^3 + 4*p^2*t + 6*p^2 + 2*p*t^2 + 8*p*t + 9*p + 2*t^2 + 3*t + 3)/2)*s^2) +
      ((p+t)*r)^2*(((p + 1)^2*(p + t + 1)^4*(2*p + 2*t + 3))*s^0 +
       ((p + 1)*(p + t + 1)^4*(p^3 + 2*p^2*t + 4*p^2 + p*t^2 + 5*p*t + 8*p + t^2 + 2*t + 3))*s^1 +
       ((p + t + 1)^4*(p^4 + 2*p^3*t + 3*p^3 + p^2*t^2 + 5*p^2*t + 6*p^2 + 2*p*t^2 + 3*p*t + 3*p + t^2))*s^2) := by
    unfold c0 f0
    ring
  have hm : 0 < (p+t)^2 * c0 p (p+1+t) r s := by rw [h]; positivity
  have hscale : 0 < (p+t)^2 := by positivity
  exact pos_of_mul_pos_right hm hscale.le

set_option maxHeartbeats 2500000 in
private theorem high_c1 (p t r s : ℝ) (hp : 0 ≤ p) (ht : 0 < t)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hrb : (p+t)*r < 1) : 0 ≤ c1 p (p+1+t) r s := by
  have hu : 0 < p+t := by positivity
  have hρ : 0 ≤ (p+t)*r := by positivity
  have hρ' : 0 < 1-(p+t)*r := sub_pos.mpr hrb
  have h : (p+t)^2 * c1 p (p+1+t) r s =
      (1-(p+t)*r)^2 * (((p + 1)^2*(p + t)^2*(p + t + 1)*(p + t + 2)^2/2)*s^0 +
       ((p + 1)*(p + t)^2*(p + t + 1)*(p + t + 2)*(2*p^3 + 4*p^2*t + 7*p^2 + 2*p*t^2 + 9*p*t + 11*p + 2*t^2 + 6*t + 6)/2)*s^1 +
       ((p + 1)*(p + t)^2*(p + t + 1)*(p + t + 2)*(2*p^3 + 4*p^2*t + 6*p^2 + 2*p*t^2 + 8*p*t + 8*p + 2*t^2 + 5*t + 4)/2)*s^2) +
      2*((p+t)*r)*(1-(p+t)*r)*(((p + 1)*(p + t)*(p + t + 1)^2*(p + t + 2)*(4*p^2 + 4*p*t + 9*p + 4*t + 6)/4)*s^0 +
       ((p + 1)*(p + t)*(p + t + 1)^2*(p^4 + 3*p^3*t + 5*p^3 + 3*p^2*t^2 + 11*p^2*t + 12*p^2 + p*t^3 + 7*p*t^2 + 16*p*t + 13*p + t^3 + 4*t^2 + 7*t + 5))*s^1 +
       ((p + t)*(p + t + 1)^2*(4*p^5 + 12*p^4*t + 20*p^4 + 12*p^3*t^2 + 48*p^3*t + 46*p^3 + 4*p^2*t^3 + 36*p^2*t^2 + 78*p^2*t + 58*p^2 + 8*p*t^3 + 36*p*t^2 + 57*p*t + 36*p + 4*t^3 + 12*t^2 + 14*t + 8)/4)*s^2) +
      ((p+t)*r)^2*(((p + 1)*(p + t + 1)^3*(p + t + 2)*(3*p^2 + 3*p*t + 6*p + 3*t + 4)/2)*s^0 +
       ((p + t + 1)^3*(2*p^5 + 6*p^4*t + 11*p^4 + 6*p^3*t^2 + 26*p^3*t + 32*p^3 + 2*p^2*t^3 + 19*p^2*t^2 + 49*p^2*t + 46*p^2 + 4*p*t^3 + 19*p*t^2 + 39*p*t + 32*p + 2*t^3 + 6*t^2 + 10*t + 8)/2)*s^1 +
       ((p + t + 1)^3*(2*p^5 + 6*p^4*t + 8*p^4 + 6*p^3*t^2 + 20*p^3*t + 18*p^3 + 2*p^2*t^3 + 16*p^2*t^2 + 29*p^2*t + 20*p^2 + 4*p*t^3 + 13*p*t^2 + 14*p*t + 8*p + 2*t^3 + 3*t^2)/2)*s^2) := by
    unfold c1 c0 f0 f1
    ring
  have hm : 0 ≤ (p+t)^2 * c1 p (p+1+t) r s := by rw [h]; positivity
  have hscale : 0 < (p+t)^2 := by positivity
  exact nonneg_of_mul_nonneg_right hm hscale

set_option maxHeartbeats 2500000 in
private theorem high_c2 (p t r s : ℝ) (hp : 0 ≤ p) (ht : 0 < t)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hrb : (p+t)*r < 1) : 0 ≤ c2 p (p+1+t) r s := by
  have hu : 0 < p+t := by positivity
  have hρ : 0 ≤ (p+t)*r := by positivity
  have hρ' : 0 < 1-(p+t)*r := sub_pos.mpr hrb
  have h : (p+t)^2 * c2 p (p+1+t) r s =
      (1-(p+t)*r)^2 * ((p*(p + 1)*(p + t)^2*(p + t + 2)^2)*s^0 +
       ((p + 1)*(p + t)^2*(p + t + 2)^2*(p^3 + 2*p^2*t + 2*p^2 + p*t^2 + 3*p*t + 4*p + t^2 + 2*t + 1))*s^1 +
       ((p + 1)*(p + t)^2*(p + t + 2)^2*(p^3 + 2*p^2*t + 2*p^2 + p*t^2 + 3*p*t + 3*p + t^2 + 2*t + 1))*s^2) +
      2*((p+t)*r)*(1-(p+t)*r)*(((p + 1)*(p + t)*(p + t + 1)*(p + t + 2)^2*(p^2 + p*t + 3*p + t + 1)/2)*s^0 +
       ((p + t)*(p + t + 1)*(2*p^6 + 8*p^5*t + 13*p^5 + 12*p^4*t^2 + 43*p^4*t + 42*p^4 + 8*p^3*t^3 + 51*p^3*t^2 + 107*p^3*t + 80*p^3 + 2*p^2*t^4 + 25*p^2*t^3 + 90*p^2*t^2 + 141*p^2*t + 86*p^2 + 4*p*t^4 + 27*p*t^3 + 71*p*t^2 + 88*p*t + 44*p + 2*t^4 + 10*t^3 + 20*t^2 + 20*t + 8)/2)*s^1 +
       ((p + t)*(p + t + 1)*(2*p^6 + 8*p^5*t + 12*p^5 + 12*p^4*t^2 + 40*p^4*t + 33*p^4 + 8*p^3*t^3 + 48*p^3*t^2 + 87*p^3*t + 54*p^3 + 2*p^2*t^4 + 24*p^2*t^3 + 77*p^2*t^2 + 102*p^2*t + 52*p^2 + 4*p*t^4 + 25*p*t^3 + 57*p*t^2 + 58*p*t + 24*p + 2*t^4 + 9*t^3 + 15*t^2 + 12*t + 4)/2)*s^2) +
      ((p+t)*r)^2*(((p + 1)^2*(p + t + 1)^3*(p + t + 2)^2)*s^0 +
       ((p + t + 1)^2*(p^6 + 4*p^5*t + 6*p^5 + 6*p^4*t^2 + 20*p^4*t + 20*p^4 + 4*p^3*t^3 + 24*p^3*t^2 + 50*p^3*t + 38*p^3 + p^2*t^4 + 12*p^2*t^3 + 41*p^2*t^2 + 64*p^2*t + 40*p^2 + 2*p*t^4 + 12*p*t^3 + 30*p*t^2 + 38*p*t + 20*p + t^4 + 4*t^3 + 7*t^2 + 8*t + 4))*s^1 +
       ((p + t + 1)^2*(p^6 + 4*p^5*t + 5*p^5 + 6*p^4*t^2 + 17*p^4*t + 13*p^4 + 4*p^3*t^3 + 21*p^3*t^2 + 34*p^3*t + 20*p^3 + p^2*t^4 + 11*p^2*t^3 + 30*p^2*t^2 + 34*p^2*t + 16*p^2 + 2*p*t^4 + 10*p*t^3 + 17*p*t^2 + 12*p*t + 4*p + t^4 + 3*t^3 + 2*t^2))*s^2) := by
    unfold c2 c0 f0 f1 f2
    ring
  have hm : 0 ≤ (p+t)^2 * c2 p (p+1+t) r s := by rw [h]; positivity
  have hscale : 0 < (p+t)^2 := by positivity
  exact nonneg_of_mul_nonneg_right hm hscale

private theorem strict_of_controls (p q r s A : ℝ) (hq : 0 < q) (hA : 0 ≤ A)
    (hAq : A*q < 1) (h0 : 0 < c0 p q r s) (h1 : 0 ≤ c1 p q r s) (h2 : 0 ≤ c2 p q r s) :
    0 < secantFactor p q r s A := by
  have hθ : 0 ≤ A*q := by positivity
  have hθ' : 0 < 1-A*q := sub_pos.mpr hAq
  have h : 0 < q^2 * secantFactor p q r s A := by rw [secant_bernstein]; positivity
  exact pos_of_mul_pos_right h (sq_nonneg q)

/-- No positive secant root below the product threshold in the lower
coefficient branch. -/
theorem secantFactor_pos_of_le (p q r s A : ℝ) (hp : 0 ≤ p) (hq : 0 < q)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hA : 0 ≤ A) (hAq : A*q < 1) (hqp : q ≤ p+1) :
    0 < secantFactor p q r s A :=
  strict_of_controls p q r s A hq hA hAq (low_c0 p q r s hp hq hr hs hqp)
    (low_c1 p q r s hp hq hr hs hqp) (low_c2 p q r s hp hq hr hs hqp)

/-- No positive secant root below both thresholds in the upper branch.
The roles of r and s can be exchanged because the factor depends on
them only through r+s and r*s. -/
theorem secantFactor_pos_of_gt (p q r s A : ℝ) (hp : 0 ≤ p)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hA : 0 ≤ A) (hAq : A*q < 1) (hqp : p+1 < q)
    (hrb : (q-1)*r < 1) :
    0 < secantFactor p q r s A := by
  let t := q-p-1
  have ht : 0 < t := by dsimp [t]; linarith
  have hq : q = p+1+t := by dsimp [t]; ring
  have hrb' : (p+t)*r < 1 := by convert hrb using 1; dsimp [t]; ring
  apply strict_of_controls p q r s A (by linarith) hA hAq
  · rw [hq]
    exact high_c0 p t r s hp ht hr hs hrb'
  · rw [hq]
    exact high_c1 p t r s hp ht hr hs hrb'
  · rw [hq]
    exact high_c2 p t r s hp ht hr hs hrb'

end

end MOC.ZhengT55Boundary23
