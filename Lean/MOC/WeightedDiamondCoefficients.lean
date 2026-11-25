import MOC.WeightedDiamondTransitions

/-! Integer coefficient arithmetic for symbolic ray certificates. Trailing zero
coefficients are permitted. The real parameter in a certificate chart is positive. -/

namespace MOC
namespace RayCoefficients

abbrev Poly := List ℤ

def eval (t : ℝ) : Poly → ℝ
  | [] => 0
  | a :: p => (a : ℝ) + t * eval t p

def add : Poly → Poly → Poly
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a + b) :: add p q

def scale (a : ℤ) (p : Poly) : Poly := p.map (a * ·)

def sub (p q : Poly) : Poly := add p (scale (-1) q)

def mul : Poly → Poly → Poly
  | [], _ => []
  | a :: p, q => add (scale a q) (0 :: mul p q)

/-- Compare coefficients, allowing either representation to omit trailing zeros. -/
def equal : Poly → Poly → Bool
  | [], q => q.all (· == 0)
  | a :: p, [] => (a :: p).all (· == 0)
  | a :: p, b :: q => a == b && equal p q

def zero (p : Poly) : Bool := p.all (· == 0)

def nonneg (p : Poly) : Bool := p.all fun a => decide (0 ≤ a)

def positive (p : Poly) : Bool := nonneg p && p.any fun a => decide (0 < a)

def negative (p : Poly) : Bool := positive (scale (-1) p)

theorem eval_add (t : ℝ) (p q : Poly) :
    eval t (add p q) = eval t p + eval t q := by
  induction p generalizing q with
  | nil => simp [add, eval]
  | cons a p ih =>
    cases q with
    | nil => simp [add, eval]
    | cons b q => simp only [add, eval, ih, Int.cast_add]; ring

theorem eval_scale (t : ℝ) (a : ℤ) (p : Poly) :
    eval t (scale a p) = (a : ℝ) * eval t p := by
  induction p with
  | nil => simp [scale, eval]
  | cons b p ih => simp only [scale, List.map_cons, eval, Int.cast_mul] at ih ⊢; rw [ih]; ring

theorem eval_sub (t : ℝ) (p q : Poly) :
    eval t (sub p q) = eval t p - eval t q := by
  simp [sub, eval_add, eval_scale, sub_eq_add_neg]

theorem eval_mul (t : ℝ) (p q : Poly) :
    eval t (mul p q) = eval t p * eval t q := by
  induction p with
  | nil => simp [mul, eval]
  | cons a p ih => simp only [mul, eval_add, eval_scale, eval, ih, Int.cast_zero]; ring

theorem eval_zero_of_check (t : ℝ) {p : Poly} (h : zero p = true) : eval t p = 0 := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [zero, List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    simp only [eval, h.1, Int.cast_zero, ih h.2, mul_zero, add_zero]

theorem eval_eq_of_check (t : ℝ) {p q : Poly} (h : equal p q = true) :
    eval t p = eval t q := by
  induction p generalizing q with
  | nil => exact (eval_zero_of_check t h).symm
  | cons a p ih =>
    cases q with
    | nil => exact eval_zero_of_check t h
    | cons b q =>
      simp only [equal, Bool.and_eq_true, beq_iff_eq] at h
      simp only [eval, h.1, ih h.2]

theorem eval_nonneg_of_check {t : ℝ} (ht : 0 ≤ t) {p : Poly}
    (h : nonneg p = true) : 0 ≤ eval t p := by
  induction p with
  | nil => exact le_rfl
  | cons a p ih =>
    simp only [nonneg, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    exact add_nonneg (Int.cast_nonneg.mpr h.1) (mul_nonneg ht (ih h.2))

theorem eval_pos_of_check {t : ℝ} (ht : 0 < t) {p : Poly}
    (h : positive p = true) : 0 < eval t p := by
  simp only [positive, Bool.and_eq_true] at h
  obtain ⟨hn, hp⟩ := h
  induction p with
  | nil => simp at hp
  | cons a p ih =>
    simp only [nonneg, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hn
    simp only [List.any_cons, Bool.or_eq_true, decide_eq_true_eq] at hp
    rcases hp with hp | hp
    · exact add_pos_of_pos_of_nonneg (Int.cast_pos.mpr hp)
        (mul_nonneg ht.le (eval_nonneg_of_check ht.le hn.2))
    · exact add_pos_of_nonneg_of_pos (Int.cast_nonneg.mpr hn.1) (mul_pos ht (ih hn.2 hp))

theorem eval_neg_of_check {t : ℝ} (ht : 0 < t) {p : Poly}
    (h : negative p = true) : eval t p < 0 := by
  have hp := eval_pos_of_check ht h
  rw [eval_scale, Int.cast_neg, Int.cast_one, neg_one_mul, neg_pos] at hp
  exact hp

end RayCoefficients
end MOC
