import MOC.DruryPencilPartition
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! A polynomial root condition on conjugate parameter pairs determines the
root partition of every specialization of the pencil. -/

open BigOperators Polynomial
open scoped Polynomial

namespace MOC

noncomputable section

private theorem monic_dvd_pow_of_roots_subset {p q : ℂ[X]} (hp : p.Monic)
    {N : ℕ} (hN : p.natDegree ≤ N) (hNpos : 0 < N)
    (h : ∀ x : ℂ, p.eval x = 0 → q.eval x = 0) : p ∣ q ^ N := by
  classical
  by_cases hq : q = 0
  · rw [hq, zero_pow hNpos.ne']
    exact dvd_zero p
  · apply (IsAlgClosed.splits p).dvd_of_roots_le_roots hp.ne_zero
    rw [Polynomial.roots_pow, Multiset.le_iff_count]
    intro x
    rw [Multiset.count_nsmul]
    by_cases hx : x ∈ p.roots
    · have hxq : x ∈ q.roots :=
        (Polynomial.mem_roots hq).mpr (h x ((Polynomial.mem_roots hp.ne_zero).mp hx))
      calc
        p.roots.count x ≤ p.roots.card := Multiset.count_le_card _ _
        _ ≤ p.natDegree := Polynomial.card_roots' p
        _ ≤ N := hN
        _ ≤ N * q.roots.count x := Nat.le_mul_of_pos_right _ (Multiset.count_pos.mpr hxq)
    · rw [Multiset.count_eq_zero.mpr hx]
      exact Nat.zero_le _

private theorem eval_parameter_comp (z w : ℂ) (i : Fin 2) :
    (MvPolynomial.eval ![z, w]).comp
      (Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X i)) =
      Polynomial.evalRingHom (![z, w] i) := by
  apply Polynomial.ringHom_ext
  · intro c
    simp
  · simp

/-- If each root of a monic polynomial family at `z` matches a root at `star z`
either directly or after multiplication by `star z / z`, then the same two
choices apply for every comparison parameter `w`. Taking `w = 1` partitions the
roots into values at `1` and their multiples by `z`. -/
theorem polynomial_roots_specialize_of_conjugate_pairs (P : Polynomial (ℂ[X]))
    (hP : P.Monic)
    (h : ∀ z : ℂ, z ≠ 0 → ∀ x : ℂ, (P.map (Polynomial.evalRingHom z)).eval x = 0 →
      (P.map (Polynomial.evalRingHom (star z))).eval x = 0 ∨
        (P.map (Polynomial.evalRingHom (star z))).eval ((star z / z) * x) = 0)
    (z w : ℂ) (hz : z ≠ 0) (x : ℂ)
    (hx : (P.map (Polynomial.evalRingHom z)).eval x = 0) :
    (P.map (Polynomial.evalRingHom w)).eval x = 0 ∨
      (P.map (Polynomial.evalRingHom w)).eval ((w / z) * x) = 0 := by
  let Z : MvPolynomial (Fin 2) ℂ := MvPolynomial.X 0
  let W : MvPolynomial (Fin 2) ℂ := MvPolynomial.X 1
  let pZ := P.map (Polynomial.eval₂RingHom MvPolynomial.C Z)
  let pW := P.map (Polynomial.eval₂RingHom MvPolynomial.C W)
  let N := P.natDegree
  let Q : (MvPolynomial (Fin 2) ℂ)[X] := ∑ j ∈ Finset.range (N + 1),
    Polynomial.C (pW.coeff j * W ^ j * Z ^ (N - j)) * X ^ j
  let e (z w : ℂ) := MvPolynomial.eval ![z, w]
  have hpZ : pZ.Monic := hP.map _
  have hmapZ (z w : ℂ) : pZ.map (e z w) = P.map (Polynomial.evalRingHom z) := by
    rw [show pZ.map (e z w) = P.map ((e z w).comp
      (Polynomial.eval₂RingHom MvPolynomial.C Z)) from Polynomial.map_map _ _ P]
    rw [show (e z w).comp (Polynomial.eval₂RingHom MvPolynomial.C Z) =
      Polynomial.evalRingHom z from eval_parameter_comp z w 0]
  have hmapW (z w : ℂ) : pW.map (e z w) = P.map (Polynomial.evalRingHom w) := by
    rw [show pW.map (e z w) = P.map ((e z w).comp
      (Polynomial.eval₂RingHom MvPolynomial.C W)) from Polynomial.map_map _ _ P]
    rw [show (e z w).comp (Polynomial.eval₂RingHom MvPolynomial.C W) =
      Polynomial.evalRingHom w from eval_parameter_comp z w 1]
  have hQ (z w : ℂ) (hz : z ≠ 0) (x : ℂ) :
      (Q.map (e z w)).eval x = z ^ N * (P.map (Polynomial.evalRingHom w)).eval ((w / z) * x) := by
    have hZ : e z w Z = z := MvPolynomial.eval_X 0
    have hW : e z w W = w := MvPolynomial.eval_X 1
    have hcoeff (j : ℕ) : e z w (pW.coeff j) = (P.map (Polynomial.evalRingHom w)).coeff j := by
      simpa only [Polynomial.coeff_map] using congrArg (fun p : ℂ[X] => p.coeff j) (hmapW z w)
    have hdeg : (P.map (Polynomial.evalRingHom w)).natDegree < N + 1 :=
      Nat.lt_succ_of_le Polynomial.natDegree_map_le
    rw [Polynomial.eval_map, Polynomial.eval_eq_sum_range' hdeg, Finset.mul_sum]
    simp only [Q, Polynomial.eval₂_finset_sum, Polynomial.eval₂_mul, Polynomial.eval₂_C,
      Polynomial.eval₂_pow, Polynomial.eval₂_X, map_mul, map_pow, hcoeff, hZ, hW]
    apply Finset.sum_congr rfl
    intro j hj
    have hjN : j ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have hpow : z ^ N = z ^ (N - j) * z ^ j := by rw [← pow_add, Nat.sub_add_cancel hjN]
    rw [hpow, mul_pow (w / z), div_pow]
    field_simp [pow_ne_zero j hz] <;> ring
  have hcompare (z w : ℂ) (hz : z ≠ 0) (x : ℂ) :
      ((pW * Q).map (e z w)).eval x =
        (P.map (Polynomial.evalRingHom w)).eval x *
          (z ^ N * (P.map (Polynomial.evalRingHom w)).eval ((w / z) * x)) := by
    rw [Polynomial.map_mul, Polynomial.eval_mul, hmapW, hQ z w hz x]
  have hdiv : pZ ∣ (pW * Q) ^ (N + 1) := by
    apply polynomial_dvd_of_conjugate_specializations pZ _ hpZ
    intro v hv
    change pZ.map (e v (star v)) ∣ ((pW * Q) ^ (N + 1)).map (e v (star v))
    rw [Polynomial.map_pow]
    have hdeg : (pZ.map (e v (star v))).natDegree ≤ N + 1 := by
      rw [hmapZ]
      exact Polynomial.natDegree_map_le.trans (Nat.le_succ _)
    apply monic_dvd_pow_of_roots_subset (hpZ.map _) hdeg (Nat.succ_pos _)
    intro y hy
    rw [hmapZ] at hy
    rw [hcompare v (star v) hv y]
    rcases h v hv y hy with h₁ | h₂
    · rw [h₁, zero_mul]
    · rw [h₂, mul_zero, mul_zero]
  have hdiv' : pZ.map (e z w) ∣ ((pW * Q).map (e z w)) ^ (N + 1) := by
    have he := (Polynomial.mapRingHom (e z w)).map_dvd hdiv
    change pZ.map (e z w) ∣ ((pW * Q) ^ (N + 1)).map (e z w) at he
    simpa only [Polynomial.map_pow] using he
  obtain ⟨B, hB⟩ := hdiv'
  have heval := congrArg (Polynomial.eval x) hB
  simp only [Polynomial.eval_pow, Polynomial.eval_mul, hmapZ, hx, zero_mul] at heval
  have hzero : ((pW * Q).map (e z w)).eval x = 0 := by
    by_contra hn
    exact pow_ne_zero _ hn heval
  rw [hcompare z w hz x] at hzero
  rcases mul_eq_zero.mp hzero with h₁ | h₂
  · exact Or.inl h₁
  · exact Or.inr ((mul_eq_zero.mp h₂).resolve_left (pow_ne_zero _ hz))

end

end MOC
