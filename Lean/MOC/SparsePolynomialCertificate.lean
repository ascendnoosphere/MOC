import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.Ring

/-! A sparse integer polynomial identity can be checked by normalization
and then evaluated in any commutative ring. -/

namespace MOC.SparsePolynomialCertificate

open BigOperators

/-- A signed coefficient and the exponents of a monomial. -/
structure Term (n : ℕ) where
  coefficient : ℤ
  powers : Fin n → ℕ
  deriving DecidableEq

abbrev Polynomial (n : ℕ) := List (Term n)

def Term.eval {R : Type*} [CommRing R] {n : ℕ} (x : Fin n → R) (t : Term n) : R :=
  (t.coefficient : R) * ∏ i, x i ^ t.powers i

def eval {R : Type*} [CommRing R] {n : ℕ} (x : Fin n → R) (p : Polynomial n) : R :=
  (p.map (Term.eval x)).sum

@[simp] theorem eval_nil {R : Type*} [CommRing R] {n : ℕ} (x : Fin n → R) :
    eval x [] = 0 := rfl

@[simp] theorem eval_cons {R : Type*} [CommRing R] {n : ℕ}
    (x : Fin n → R) (a : Term n) (p : Polynomial n) :
    eval x (a :: p) = a.eval x + eval x p := rfl

@[simp] theorem eval_append {R : Type*} [CommRing R] {n : ℕ}
    (x : Fin n → R) (p q : Polynomial n) :
    eval x (p ++ q) = eval x p + eval x q := by simp [eval, List.sum_append]

def constant (n : ℕ) (c : ℤ) : Polynomial n := [⟨c, fun _ => 0⟩]

def indeterminate {n : ℕ} (i : Fin n) : Polynomial n :=
  [⟨1, fun j => if j = i then 1 else 0⟩]

@[simp] theorem eval_constant {R : Type*} [CommRing R] {n : ℕ}
    (x : Fin n → R) (c : ℤ) : eval x (constant n c) = c := by
  simp [constant, Term.eval]

@[simp] theorem eval_indeterminate {R : Type*} [CommRing R] {n : ℕ}
    (x : Fin n → R) (i : Fin n) : eval x (indeterminate i) = x i := by
  simp only [indeterminate, eval_cons, eval_nil, add_zero, Term.eval, Int.cast_one, one_mul]
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

private def Term.mul {n : ℕ} (a b : Term n) : Term n :=
  ⟨a.coefficient * b.coefficient, fun i => a.powers i + b.powers i⟩

def mul {n : ℕ} (p q : Polynomial n) : Polynomial n :=
  p.flatMap (fun a => q.map (a.mul))

@[simp] private theorem eval_term_mul {R : Type*} [CommRing R] {n : ℕ}
    (x : Fin n → R) (a b : Term n) : (a.mul b).eval x = a.eval x * b.eval x := by
  simp only [Term.mul, Term.eval, Int.cast_mul, pow_add, Finset.prod_mul_distrib]
  ring

private theorem eval_map_term_mul {R : Type*} [CommRing R] {n : ℕ}
    (x : Fin n → R) (a : Term n) (q : Polynomial n) :
    eval x (q.map (a.mul)) = a.eval x * eval x q := by
  induction q with
  | nil => simp
  | cons b q ih => simp [ih, mul_add]

@[simp] theorem eval_mul {R : Type*} [CommRing R] {n : ℕ}
    (x : Fin n → R) (p q : Polynomial n) : eval x (mul p q) = eval x p * eval x q := by
  induction p with
  | nil => simp [mul]
  | cons a p ih =>
      change eval x (q.map (a.mul) ++ mul p q) = (a.eval x + eval x p) * eval x q
      rw [eval_append, eval_map_term_mul, ih, add_mul]

def pow {n : ℕ} (p : Polynomial n) : ℕ → Polynomial n
  | 0 => constant n 1
  | k + 1 => mul p (pow p k)

@[simp] theorem eval_pow {R : Type*} [CommRing R] {n : ℕ}
    (x : Fin n → R) (p : Polynomial n) (k : ℕ) : eval x (pow p k) = eval x p ^ k := by
  induction k with
  | zero => simp [pow]
  | succ k ih => simp [pow, ih, pow_succ']

def substitute {n m : ℕ} (p : Polynomial n) (coordinates : Fin n → Polynomial m) : Polynomial m :=
  p.flatMap fun t =>
    (List.ofFn fun i => pow (coordinates i) (t.powers i)).foldr mul (constant m t.coefficient)

private theorem eval_foldr_mul {R : Type*} [CommRing R] {n : ℕ}
    (x : Fin n → R) (ps : List (Polynomial n)) (q : Polynomial n) :
    eval x (ps.foldr mul q) = (ps.map (eval x)).prod * eval x q := by
  induction ps with
  | nil => simp
  | cons p ps ih => simp [ih, mul_assoc]

@[simp] theorem eval_substitute {R : Type*} [CommRing R] {n m : ℕ}
    (x : Fin m → R) (p : Polynomial n) (coordinates : Fin n → Polynomial m) :
    eval x (substitute p coordinates) = eval (fun i => eval x (coordinates i)) p := by
  induction p with
  | nil => simp [substitute]
  | cons t p ih =>
      change eval x ((List.ofFn fun i => pow (coordinates i) (t.powers i)).foldr mul
          (constant m t.coefficient) ++ substitute p coordinates) =
        t.eval (fun i => eval x (coordinates i)) + eval (fun i => eval x (coordinates i)) p
      rw [eval_append, eval_foldr_mul, ih]
      simp [Term.eval, List.map_ofFn, Fin.prod_ofFn, mul_comm]

private def before : List ℕ → List ℕ → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a = b then before as bs else decide (a < b)

private def mergeTerms {n : ℕ} : ℕ → Polynomial n → Polynomial n → Polynomial n
  | 0, p, q => p ++ q
  | _ + 1, [], q => q
  | _ + 1, p, [] => p
  | fuel + 1, a :: p, b :: q =>
      if List.ofFn a.powers = List.ofFn b.powers then
        if a.coefficient + b.coefficient = 0 then mergeTerms fuel p q
        else ⟨a.coefficient + b.coefficient, a.powers⟩ :: mergeTerms fuel p q
      else if before (List.ofFn a.powers) (List.ofFn b.powers) then
        a :: mergeTerms fuel p (b :: q)
      else b :: mergeTerms fuel (a :: p) q

private theorem eval_mergeTerms {R : Type*} [CommRing R] {n : ℕ}
    (x : Fin n → R) (fuel : ℕ) (p q : Polynomial n) :
    eval x (mergeTerms fuel p q) = eval x p + eval x q := by
  induction fuel generalizing p q with
  | zero => simp [mergeTerms]
  | succ fuel ih =>
      cases p with
      | nil => simp [mergeTerms]
      | cons a p =>
          cases q with
          | nil => simp [mergeTerms]
          | cons b q =>
              by_cases he : List.ofFn a.powers = List.ofFn b.powers
              · have hp : a.powers = b.powers := List.ofFn_injective he
                have hadd : (⟨a.coefficient + b.coefficient, a.powers⟩ : Term n).eval x =
                    a.eval x + b.eval x := by
                  simp [Term.eval, hp, add_mul]
                by_cases hz : a.coefficient + b.coefficient = 0
                · have hzero : a.eval x + b.eval x = 0 := by
                    rw [← hadd]
                    simp [Term.eval, hz]
                  simp only [mergeTerms, he, hz, if_true, ih, eval_cons]
                  calc
                    _ = (a.eval x + b.eval x) + (eval x p + eval x q) := by rw [hzero, zero_add]
                    _ = _ := by ring
                · simp only [mergeTerms, he, hz, if_true, if_false, eval_cons, ih, hadd]
                  ring
              · by_cases hb : before (List.ofFn a.powers) (List.ofFn b.powers) = true <;>
                  simp only [mergeTerms, he, hb, Bool.false_eq_true, if_false, if_true, ih,
                    eval_cons] <;> ring

private def mergeTermPairs {n : ℕ} : List (Polynomial n) → List (Polynomial n)
  | p :: q :: rest => mergeTerms (p.length + q.length) p q :: mergeTermPairs rest
  | rest => rest

private theorem eval_mergeTermPairs {R : Type*} [CommRing R] {n : ℕ}
    (x : Fin n → R) (ps : List (Polynomial n)) :
    eval x (mergeTermPairs ps).flatten = eval x ps.flatten := by
  match ps with
  | [] => rfl
  | [_] => rfl
  | p :: q :: rest =>
      simp only [mergeTermPairs, List.flatten_cons, eval_append, eval_mergeTerms,
        eval_mergeTermPairs x rest, add_assoc]

private def mergeTermRounds {n : ℕ} : ℕ → List (Polynomial n) → Polynomial n
  | 0, ps => ps.flatten
  | _ + 1, [] => []
  | _ + 1, [p] => p
  | fuel + 1, p :: q :: ps => mergeTermRounds fuel (mergeTermPairs (p :: q :: ps))

private theorem eval_mergeTermRounds {R : Type*} [CommRing R] {n : ℕ}
    (x : Fin n → R) (fuel : ℕ) (ps : List (Polynomial n)) :
    eval x (mergeTermRounds fuel ps) = eval x ps.flatten := by
  induction fuel generalizing ps with
  | zero => rfl
  | succ fuel ih =>
      cases ps with
      | nil => rfl
      | cons p ps =>
          cases ps with
          | nil => simp [mergeTermRounds]
          | cons q ps => simp only [mergeTermRounds, ih, eval_mergeTermPairs]

/-- Merge equal powers and discard terms whose coefficients cancel. -/
def normalize {n : ℕ} (p : Polynomial n) : Polynomial n :=
  mergeTermRounds p.length (p.map fun t => if t.coefficient = 0 then [] else [t])

theorem eval_normalize {R : Type*} [CommRing R] {n : ℕ}
    (x : Fin n → R) (p : Polynomial n) : eval x (normalize p) = eval x p := by
  rw [normalize, eval_mergeTermRounds]
  induction p with
  | nil => rfl
  | cons a p ih =>
      by_cases ha : a.coefficient = 0 <;> simp [ha, ih, Term.eval]

theorem eval_eq_of_normalize_eq {R : Type*} [CommRing R] {n : ℕ}
    (x : Fin n → R) {p q : Polynomial n} (h : normalize p = normalize q) :
    eval x p = eval x q := by rw [← eval_normalize x p, h, eval_normalize]

private def Term.key {n : ℕ} (a : Term n) : ℤ × List ℕ :=
  (a.coefficient, List.ofFn a.powers)

private theorem Term.key_injective {n : ℕ} : Function.Injective (Term.key (n := n)) := by
  rintro ⟨a, p⟩ ⟨b, q⟩ h
  have hab : a = b := congrArg Prod.fst h
  have hpq : p = q := List.ofFn_injective (congrArg Prod.snd h)
  subst b
  subst q
  rfl

/-- The normalized integer coefficients and ordinary exponent lists. -/
def normalizedKeys {n : ℕ} (p : Polynomial n) : List (ℤ × List ℕ) :=
  (normalize p).map Term.key

/-- Comparing normalized keys is sound for evaluation. -/
theorem eval_eq_of_normalizedKeys_eq {R : Type*} [CommRing R] {n : ℕ}
    (x : Fin n → R) {p q : Polynomial n}
    (h : (normalizedKeys p == normalizedKeys q) = true) : eval x p = eval x q :=
  eval_eq_of_normalize_eq x (List.map_injective_iff.mpr Term.key_injective (eq_of_beq h))

theorem eval_homogeneous {R : Type*} [CommRing R] {n : ℕ}
    (x : Fin n → R) (s : R) (p : Polynomial n) (degree : ℕ)
    (hp : ∀ a ∈ p, ∑ i, a.powers i = degree) :
    eval (fun i => s * x i) p = s ^ degree * eval x p := by
  induction p with
  | nil => simp
  | cons a p ih =>
      have hdeg := hp a (by simp)
      have ha : a.eval (fun i => s * x i) = s ^ degree * a.eval x := by
        simp only [Term.eval, mul_pow, Finset.prod_mul_distrib]
        rw [Finset.prod_pow_eq_pow_sum, hdeg]
        ring
      rw [eval_cons, eval_cons, ha, ih (fun t ht => hp t (by simp [ht])), mul_add]

theorem eval_nonneg {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] {n : ℕ}
    (x : Fin n → R) (hx : ∀ i, 0 ≤ x i) (p : Polynomial n)
    (hp : ∀ a ∈ p, 0 ≤ a.coefficient) :
    0 ≤ eval x p := by
  induction p with
  | nil => simp
  | cons a p ih =>
      rw [eval_cons]
      have ha : (0 : R) ≤ (a.coefficient : R) := Int.cast_nonneg.mpr (hp a (by simp))
      exact add_nonneg (mul_nonneg ha (Finset.prod_nonneg (fun i _ => pow_nonneg (hx i) _)))
        (ih (fun t ht => hp t (by simp [ht])))

def sum {n m : ℕ} (p : Fin n → Polynomial m) : Polynomial m :=
  (List.ofFn p).flatten

@[simp] theorem eval_sum {R : Type*} [CommRing R] {n m : ℕ}
    (x : Fin m → R) (p : Fin n → Polynomial m) :
    eval x (sum p) = ∑ i, eval x (p i) := by
  have hflatten (q : List (Polynomial m)) : eval x q.flatten = (q.map (eval x)).sum := by
    induction q with
    | nil => rfl
    | cons a q ih => simp [ih]
  unfold sum
  rw [hflatten, List.map_ofFn, Fin.sum_ofFn] <;> rfl

end MOC.SparsePolynomialCertificate
