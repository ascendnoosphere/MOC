import MOC.SpectralKKT
import Mathlib.Logic.Relation

/-! Independent supported trace-zero directions for real row effects.
This is the graph-algebra core of a fixed-anchor obstruction in order five.
For the general idea of testing extremality with supported perturbations,
see D'Ariano–Lo Presti–Perinotti, DOI: 10.1088/0305-4470/38/26/010;
the trace-one constraints here are additional. -/

open Matrix BigOperators

namespace MOC

variable {V : Type*} [Fintype V] [DecidableEq V]

private def axis (i j : V) : ℝ := if i = j then 1 else 0

private def adjacency (E : V → V → Prop) [DecidableRel E] (i j : V) : ℝ :=
  if E i j then 1 else 0

/-- The first traceless direction supported by the coordinate axis
and the adjacency row. -/
noncomputable def graphEffectA (E : V → V → Prop) [DecidableRel E]
    (i : V) : Matrix V V ℝ :=
  fun j k => (∑ l, adjacency E i l) * axis i j * axis i k -
    adjacency E i j * adjacency E i k

/-- The second, off-diagonal, traceless direction on the same plane. -/
noncomputable def graphEffectB (E : V → V → Prop) [DecidableRel E]
    (i : V) : Matrix V V ℝ :=
  fun j k => axis i j * adjacency E i k + adjacency E i j * axis i k

/-- A connected graph containing a triangle and a nonadjacent pair
with a common neighbor yields independent supported directions.
The nonedge tests the Laplacian's constant mode that diagonal entries
alone cannot detect. -/
theorem graphEffect_linear_combination_zero (E : V → V → Prop) [DecidableRel E]
    (hconn : ∀ i j, Relation.ReflTransGen E i j)
    (hsym : Symmetric E) (hirr : Irreflexive E)
    {p q k r s t : V} (hpq : p ≠ q) (hnpq : ¬ E p q)
    (hkp : E k p) (hkq : E k q)
    (hrs : E r s) (hst : E s t) (htr : E t r)
    (α β : V → ℝ)
    (h : (∑ i, α i • graphEffectA E i) + (∑ i, β i • graphEffectB E i) = 0) :
    α = 0 ∧ β = 0 := by
  classical
  let a := adjacency E
  have hadj (i j : V) : a i j = if E i j then 1 else 0 := rfl
  have hnonneg (i j : V) : 0 ≤ a i j := by rw [hadj]; split_ifs <;> positivity
  have hBdiag (i j : V) : (graphEffectB E i) j j = 0 := by
    by_cases he : i = j
    · subst j
      simp [graphEffectB, axis, adjacency, hirr i]
    · simp [graphEffectB, axis, he]
  have hAdiag (i j : V) :
      (graphEffectA E i) j j = (if i = j then (∑ l, a j l) else 0) -
        (if E j i then 1 else 0) := by
    change _ = _
    by_cases he : i = j
    · subst j
      simp [graphEffectA, axis, adjacency, a, hirr i]
    · by_cases ha : E j i
      · simp [graphEffectA, axis, he, adjacency, ha, (hsym ha)]
      · have hb : ¬ E i j := fun hh => ha (hsym hh)
        simp [graphEffectA, axis, he, adjacency, ha, hb]
  have hentry (j l : V) :
      (∑ i, α i * (graphEffectA E i) j l) +
        (∑ i, β i * (graphEffectB E i) j l) = 0 := by
    have hh := congrArg (fun M : Matrix V V ℝ => M j l) h
    simpa only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.zero_apply] using hh
  have hmean (j : V) : (∑ i, a j i * (α j - α i)) = 0 := by
    have hh := hentry j j
    simp only [hBdiag, hAdiag, mul_zero, Finset.sum_const_zero, add_zero, mul_sub,
      Finset.sum_sub_distrib, mul_ite, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hh
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    simpa only [hadj, mul_comm, mul_ite, ite_mul, zero_mul, mul_zero] using hh
  obtain ⟨m,_,hm⟩ := Finset.exists_max_image Finset.univ α ⟨p,Finset.mem_univ _⟩
  have hstep (i j : V) (hi : α i = α m) (hij : E i j) : α j = α m := by
    have hnn (l : V) (_ : l ∈ Finset.univ) : 0 ≤ a i l * (α i - α l) :=
      mul_nonneg (hnonneg i l) (sub_nonneg.mpr (by rw [hi]; exact hm l (Finset.mem_univ _)))
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp (hmean i) j (Finset.mem_univ j)
    rw [hadj, if_pos hij, one_mul, sub_eq_zero] at hz
    exact hz.symm.trans hi
  have hαm (i : V) : α i = α m := by
    induction hconn m i with
    | refl => rfl
    | tail _ hj hij => exact hstep _ _ hij hj
  have hα (i j : V) : α i = α j := (hαm i).trans (hαm j).symm
  have hfirst (i j l : V) (hjl : j ≠ l) :
      (∑ l, a i l) * axis i j * axis i l = 0 := by
    by_cases hij : i = j
    · subst j
      simp [axis, hjl]
    · simp [axis,hij]
  have hBsum (j l : V) (hjl : j ≠ l) :
      (∑ i, β i * (graphEffectB E i) j l) =
        β j * a j l + β l * a l j := by
    change (∑ i, β i * (axis i j * a i l + a i j * axis i l)) = _
    simp only [mul_add, Finset.sum_add_distrib, axis, ite_mul, mul_ite, one_mul,
      mul_one, mul_zero, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hnon : 0 < ∑ i, a i p * a i q := by
    have hk : 0 < a k p * a k q := by simp [hadj, hkp, hkq]
    exact hk.trans_le (Finset.single_le_sum
      (fun i _ => mul_nonneg (hnonneg i p) (hnonneg i q)) (Finset.mem_univ k))
  have hαp : α p = 0 := by
    have hh := hentry p q
    rw [hBsum p q hpq, hadj p q, if_neg hnpq, hadj q p, if_neg (fun he => hnpq (hsym he)),
      mul_zero, mul_zero, add_zero, add_zero] at hh
    change ∑ i, α i * ((∑ l, a i l) * axis i p * axis i q - a i p * a i q) = 0 at hh
    simp only [hfirst _ _ _ hpq, zero_sub, hα _ p, mul_neg, Finset.sum_neg_distrib,
      ← Finset.mul_sum] at hh
    exact (mul_eq_zero.mp (neg_eq_zero.mp hh)).resolve_right hnon.ne'
  have hα0 (i : V) : α i = 0 := (hα i p).trans hαp
  have hβedge (i j : V) (hij : E i j) : β i + β j = 0 := by
    have hh := hentry i j
    simp only [hα0, zero_mul, Finset.sum_const_zero, zero_add] at hh
    rw [hBsum i j (fun he => hirr j (he ▸ hij)), hadj i j, if_pos hij, hadj j i, if_pos (hsym hij),
      mul_one, mul_one] at hh
    exact hh
  have hβr : β r = 0 := by linarith [hβedge r s hrs, hβedge s t hst, hβedge t r htr]
  have hβ0 (i : V) : β i = 0 := by
    induction hconn r i with
    | refl => exact hβr
    | tail _ hj hij => linarith [hβedge _ _ hj]
  exact ⟨funext hα0,funext hβ0⟩

end MOC
