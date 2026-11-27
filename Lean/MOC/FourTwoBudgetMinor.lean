import MOC.FourQuaternionMinor
import MOC.FourMinorTransport
import MOC.FourTwoBudget
import MOC.ContactCensus

/-! Transport the order-four two-budget certificate to complex unitary
minor tables, including the relabelings used in paper cases negative-defect pattern and mixed-budget pattern. -/

open BigOperators Matrix

namespace MOC

noncomputable section

private def twoBudgetForm (a b c : ℝ) (m : Finset (Fin 4) → Finset (Fin 4) → ℝ) : ℝ :=
  a * m {0, 1} {2, 3} + b * m {0, 3} {1, 2} +
    c * (m {0} {2} + m {1} {3} + m {1, 3} {1, 2} - m {1, 2} {1, 3})

private theorem twoBudgetForm_orthogonal {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hcap : c ^ 2 ≤ a * b)
    (O : Matrix.orthogonalGroup (Fin 4) ℝ) :
    0 ≤ twoBudgetForm a b c (subsetMinorSq (Complex.ofRealHom.mapMatrix O.val)) := by
  obtain ⟨p, q, hp, hq, hsingle, hpair⟩ := exists_quaternionRotation_same_squaredMinors O
  have h := quaternionRotation_two_budget_nonneg ha hb hc hcap p q
    (by simpa only [Fin.sum_univ_four] using hp) (by simpa only [Fin.sum_univ_four] using hq)
  rw [twoBudgetForm, hsingle 0 2, hsingle 1 3,
    hpair 0 1 2 3 (by decide) (by decide), hpair 0 3 1 2 (by decide) (by decide),
    hpair 1 3 1 2 (by decide) (by decide), hpair 1 2 1 3 (by decide) (by decide)]
  exact h

/-- The canonical two-budget inequality for all order-four unitaries. -/
theorem four_two_budget_minor_nonneg {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hcap : c ^ 2 ≤ a * b)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    let m := subsetMinorSq U
    0 ≤ a * m {0, 1} {2, 3} + b * m {0, 3} {1, 2} +
      c * (m {0} {2} + m {1} {3} + m {1, 3} {1, 2} - m {1, 2} {1, 3}) := by
  obtain ⟨κ, inst, w, O, hw, _, hm⟩ := four_minor_mixture U hU
  letI : Fintype κ := inst
  let m (k : κ) := subsetMinorSq (Complex.ofRealHom.mapMatrix (O k).val)
  let f : (Finset (Fin 4) → Finset (Fin 4) → ℝ) →ₗ[ℝ] ℝ := {
    toFun := twoBudgetForm a b c
    map_add' := by intro v z; dsimp only [twoBudgetForm, Pi.add_apply]; ring
    map_smul' := by
      intro k v
      change twoBudgetForm a b c (k • v) = k * twoBudgetForm a b c v
      dsimp only [twoBudgetForm, Pi.smul_apply, smul_eq_mul]
      ring }
  have hm' : subsetMinorSq U = ∑ k, w k • m k := by
    funext I J
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hm I J
  have hn (k : κ) : 0 ≤ f (m k) := twoBudgetForm_orthogonal ha hb hc hcap (O k)
  change 0 ≤ f (subsetMinorSq U)
  rw [hm', map_sum]
  exact Finset.sum_nonneg (fun k _ => by simpa only [map_smul, smul_eq_mul] using mul_nonneg (hw k) (hn k))

private theorem four_two_budget_minor_nonneg_reindex {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hcap : c ^ 2 ≤ a * b)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) (r s : FourPerm) :
    let m := subsetMinorSq U
    0 ≤ a * m {r 0, r 1} {s 2, s 3} + b * m {r 0, r 3} {s 1, s 2} +
      c * (m {r 0} {s 2} + m {r 1} {s 3} + m {r 1, r 3} {s 1, s 2} - m {r 1, r 2} {s 1, s 3}) := by
  let V := U.submatrix r s
  have hV : IsUnitary V := unitary_reindex r s hU
  have hsingle (i j : Fin 4) : subsetMinorSq V {i} {j} = subsetMinorSq U {r i} {s j} := by
    rw [subsetMinorSq_singleton V hV, subsetMinorSq_singleton U hU] <;> rfl
  have hpair {i k j l : Fin 4} (hi : i ≠ k) (hj : j ≠ l) :
      subsetMinorSq V {i, k} {j, l} = subsetMinorSq U {r i, r k} {s j, s l} := by
    rw [subsetMinorSq_pair V hV hi hj, subsetMinorSq_pair U hU
      (fun h => hi (r.injective h)) (fun h => hj (s.injective h))] <;> rfl
  have h := four_two_budget_minor_nonneg ha hb hc hcap V hV
  dsimp only at h
  rw [hsingle 0 2, hsingle 1 3,
    hpair (i := 0) (k := 1) (j := 2) (l := 3) (by decide) (by decide),
    hpair (i := 0) (k := 3) (j := 1) (l := 2) (by decide) (by decide),
    hpair (i := 1) (k := 3) (j := 1) (l := 2) (by decide) (by decide),
    hpair (i := 1) (k := 2) (j := 1) (l := 3) (by decide) (by decide)] at h
  exact h

/-- The two-budget response for historical facets `f1`, `f11`, and `f17`
in the negative-defect pattern matching labels. -/
theorem four_two_budget_minor_nonneg_negative_defect {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hcap : c ^ 2 ≤ a * b)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    let m := subsetMinorSq U
    0 ≤ a * m {0, 1} {3, 2} + b * m {0, 2} {2, 1} +
      c * (m {0} {2} + m {2} {1} + m {2, 1} {3, 2} - m {2, 3} {3, 1}) := by
  let r := fourPerm 3
  let s := fourPerm 5
  have hr₀ : r 0 = 0 := by decide +kernel
  have hr₁ : r 1 = 2 := by decide +kernel
  have hr₂ : r 2 = 3 := by decide +kernel
  have hr₃ : r 3 = 1 := by decide +kernel
  have hs₁ : s 1 = 3 := by decide +kernel
  have hs₂ : s 2 = 2 := by decide +kernel
  have hs₃ : s 3 = 1 := by decide +kernel
  have h := four_two_budget_minor_nonneg_reindex hb ha hc (by rwa [mul_comm]) U hU r s
  simp only [hr₀, hr₁, hr₂, hr₃, hs₁, hs₂, hs₃] at h
  dsimp only at h ⊢
  convert h using 1 <;> ring

/-- The two-budget response for historical facets `f5`, `f2`, and `f54`
in the mixed-budget pattern matching labels. -/
theorem four_two_budget_minor_nonneg_mixed_budget {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hcap : c ^ 2 ≤ a * b)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    let m := subsetMinorSq U
    0 ≤ a * m {0, 1} {3, 1} + b * m {0, 2} {2, 3} +
      c * (m {0} {3} + m {1} {1} + m {1, 2} {2, 3} - m {1, 3} {2, 1}) := by
  let r := fourPerm 1
  let s := fourPerm 3
  have hr₀ : r 0 = 0 := by decide +kernel
  have hr₁ : r 1 = 1 := by decide +kernel
  have hr₂ : r 2 = 3 := by decide +kernel
  have hr₃ : r 3 = 2 := by decide +kernel
  have hs₁ : s 1 = 2 := by decide +kernel
  have hs₂ : s 2 = 3 := by decide +kernel
  have hs₃ : s 3 = 1 := by decide +kernel
  simpa only [hr₀, hr₁, hr₂, hr₃, hs₁, hs₂, hs₃] using
    four_two_budget_minor_nonneg_reindex ha hb hc hcap U hU r s

end

end MOC
