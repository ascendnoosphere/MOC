import MOC.FourBudgetResponse
import MOC.FourMinorTransport
import MOC.FourQuaternionMinor
import MOC.FiniteMinorLaw

/-! Transport of the four-budget certificate to unitary minor tables. -/

open BigOperators Matrix

namespace MOC

noncomputable section

private def fourBudgetMinorForm (a b c d : ℝ) (m : Finset (Fin 4) → Finset (Fin 4) → ℝ) : ℝ :=
  a * m {0} {3} + b * m {3} {0} + c * m {0, 2} {1, 3} +
    d * (m {0} {3} + m {3} {0} + m {0, 2} {0, 2} - m {0, 1} {2, 3})

private theorem fourBudgetMinorForm_orthogonal {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hcapacity : d ^ 2 * (a + b + c + d) ≤ a * b * (c - d))
    (O : Matrix.orthogonalGroup (Fin 4) ℝ) :
    0 ≤ fourBudgetMinorForm a b c d (subsetMinorSq (Complex.ofRealHom.mapMatrix O.val)) := by
  obtain ⟨p, q, hp, hq, hsingle, hpair⟩ := exists_quaternionRotation_same_squaredMinors O
  have hGram := quaternionRotation_four_budget_nonneg ha hb hc hd hcapacity p q
    (by simpa only [Fin.sum_univ_four] using hp) (by simpa only [Fin.sum_univ_four] using hq)
  rw [fourBudgetMinorForm, hsingle 0 3, hsingle 3 0,
    hpair 0 2 1 3 (by decide) (by decide), hpair 0 2 0 2 (by decide) (by decide),
    hpair 0 1 2 3 (by decide) (by decide)]
  exact hGram

/-- A four-budget minor inequality valid on all order-four unitary matrices.
This is the uniform Gram bound used by the T4 and T5 contact certificates. -/
theorem four_budget_minor_nonneg {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hcapacity : d ^ 2 * (a + b + c + d) ≤ a * b * (c - d))
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    let m := subsetMinorSq U
    0 ≤ a * m {0} {3} + b * m {3} {0} + c * m {0, 2} {1, 3} +
      d * (m {0} {3} + m {3} {0} + m {0, 2} {0, 2} - m {0, 1} {2, 3}) := by
  obtain ⟨κ, inst, w, O, hw, _, hm⟩ := four_minor_mixture U hU
  letI : Fintype κ := inst
  let m (k : κ) := subsetMinorSq (Complex.ofRealHom.mapMatrix (O k).val)
  let f : (Finset (Fin 4) → Finset (Fin 4) → ℝ) →ₗ[ℝ] ℝ := {
    toFun := fourBudgetMinorForm a b c d
    map_add' := by intro v z; dsimp only [fourBudgetMinorForm, Pi.add_apply]; ring
    map_smul' := by
      intro k v
      change fourBudgetMinorForm a b c d (k • v) = k * fourBudgetMinorForm a b c d v
      dsimp only [fourBudgetMinorForm, Pi.smul_apply, smul_eq_mul]
      ring }
  have hm' : subsetMinorSq U = ∑ k, w k • m k := by
    funext I J
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hm I J
  have hn (k : κ) : 0 ≤ f (m k) := fourBudgetMinorForm_orthogonal ha hb hc hd hcapacity (O k)
  change 0 ≤ f (subsetMinorSq U)
  rw [hm', map_sum]
  exact Finset.sum_nonneg (fun k _ => by simpa only [map_smul, smul_eq_mul] using mul_nonneg (hw k) (hn k))

/-- The same four-budget certificate in T4's row and column labels. -/
theorem four_budget_minor_nonneg_t4 {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hcapacity : d ^ 2 * (a + b + c + d) ≤ a * b * (c - d))
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    let m := subsetMinorSq U
    0 ≤ a * m {3} {0} + b * m {0} {3} + c * m {0, 1} {1, 3} +
      d * (m {0} {3} - m {0, 2} {2, 3} + m {3} {0} + m {0, 1} {0, 2}) := by
  let p : Equiv.Perm (Fin 4) := Equiv.swap 1 2
  let V := Uᵀ.submatrix (Equiv.refl _) p
  have htrans : IsUnitary Uᵀ := by
    have ht : (Uᵀ)ᴴ = (Uᴴ)ᵀ := by ext i j; rfl
    constructor
    · rw [ht, ← Matrix.transpose_mul, hU.2, Matrix.transpose_one]
    · rw [ht, ← Matrix.transpose_mul, hU.1, Matrix.transpose_one]
  have hV : IsUnitary V := unitary_reindex (Equiv.refl _) p htrans
  have hp₀ : p 0 = 0 := by decide +kernel
  have hp₁ : p 1 = 2 := by decide +kernel
  have hp₂ : p 2 = 1 := by decide +kernel
  have hp₃ : p 3 = 3 := by decide +kernel
  have hv (i j : Fin 4) : V i j = U (p j) i := rfl
  have h₀ : subsetMinorSq V {0} {3} = subsetMinorSq U {3} {0} := by
    rw [subsetMinorSq_singleton V hV, subsetMinorSq_singleton U hU, hv, hp₃]
  have h₁ : subsetMinorSq V {3} {0} = subsetMinorSq U {0} {3} := by
    rw [subsetMinorSq_singleton V hV, subsetMinorSq_singleton U hU, hv, hp₀]
  have h₂ : subsetMinorSq V {0, 2} {1, 3} = subsetMinorSq U {0, 1} {1, 3} := by
    have he : subsetMinorSq U {2, 3} {0, 2} = subsetMinorSq U {0, 1} {1, 3} := by
      have hh := subsetMinorSq_compl U hU {0, 1} {1, 3}
      rwa [show ({0, 1} : Finset (Fin 4))ᶜ = {2, 3} by decide +kernel,
        show ({1, 3} : Finset (Fin 4))ᶜ = {0, 2} by decide +kernel] at hh
    rw [← he, subsetMinorSq_pair V hV (by decide) (by decide),
      subsetMinorSq_pair U hU (by decide) (by decide)]
    simp only [hv, hp₁, hp₃, mul_comm]
  have h₃ : subsetMinorSq V {0, 2} {0, 2} = subsetMinorSq U {0, 1} {0, 2} := by
    rw [subsetMinorSq_pair V hV (by decide) (by decide),
      subsetMinorSq_pair U hU (by decide) (by decide)]
    simp only [hv, hp₀, hp₂, mul_comm]
  have h₄ : subsetMinorSq V {0, 1} {2, 3} = subsetMinorSq U {0, 2} {2, 3} := by
    have he : subsetMinorSq U {1, 3} {0, 1} = subsetMinorSq U {0, 2} {2, 3} := by
      have hh := subsetMinorSq_compl U hU {0, 2} {2, 3}
      rwa [show ({0, 2} : Finset (Fin 4))ᶜ = {1, 3} by decide +kernel,
        show ({2, 3} : Finset (Fin 4))ᶜ = {0, 1} by decide +kernel] at hh
    rw [← he, subsetMinorSq_pair V hV (by decide) (by decide),
      subsetMinorSq_pair U hU (by decide) (by decide)]
    simp only [hv, hp₂, hp₃, mul_comm]
  have hs := four_budget_minor_nonneg ha hb hc hd hcapacity V hV
  dsimp only at hs ⊢
  rw [h₀, h₁, h₂, h₃, h₄] at hs
  convert hs using 1 <;> ring

end

end MOC
