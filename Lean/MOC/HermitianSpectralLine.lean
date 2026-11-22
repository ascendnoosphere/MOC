import MOC.HermitianByNormal
import MOC.TwoValues
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-! Coefficient hulls for a Hermitian spectrum and a complex line of partners. -/

open BigOperators Matrix Polynomial

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A diagonal partner on the complex line through two real lists. -/
def partnerOnSpectralLine (x v : ι → ℝ) (z : ℂ) (i : ι) : ℂ :=
  (x i : ℂ) + (v i : ℂ) * z

def matchingLinePolynomial (h x v : ι → ℝ) (σ : Equiv.Perm ι) : ℝ[X] :=
  ∏ i, (C (h (σ i) + x i) + C (v i) * X)

/-- The determinant along the line has real coefficients by the real signed law. -/
def determinantLinePolynomial (h x v : ι → ℝ) (U : Matrix ι ι ℂ) : ℝ[X] :=
  ∑ σ, C (realSignedWeight U σ) * matchingLinePolynomial h x v σ

@[simp] theorem eval_matchingLinePolynomial (h x v : ι → ℝ) (σ : Equiv.Perm ι) (z : ℂ) :
    (matchingLinePolynomial h x v σ).eval₂ Complex.ofRealHom z =
      matchingProduct (fun i => (h i : ℂ)) (partnerOnSpectralLine x v z) σ := by
  simp only [matchingLinePolynomial, eval₂_finset_prod, eval₂_add, eval₂_mul, eval₂_C,
    eval₂_X, Complex.ofRealHom_eq_coe, Complex.ofReal_add, matchingProduct,
    partnerOnSpectralLine, add_assoc]

@[simp] theorem eval_determinantLinePolynomial (h x v : ι → ℝ) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) (z : ℂ) :
    (determinantLinePolynomial h x v U).eval₂ Complex.ofRealHom z =
      determinantValue (fun i => (h i : ℂ)) (partnerOnSpectralLine x v z) U := by
  simp only [determinantLinePolynomial, eval₂_finset_sum, eval₂_mul, eval₂_C,
    Complex.ofRealHom_eq_coe, eval_matchingLinePolynomial, real_signed_determinant _ _ U hU]

private theorem natDegree_line_factor_le (a b : ℝ) : (C a + C b * X).natDegree ≤ 1 := by
  rw [natDegree_C_add]
  exact (natDegree_C_mul_le b X).trans natDegree_X_le

theorem natDegree_matchingLinePolynomial_le (h x v : ι → ℝ) (σ : Equiv.Perm ι) :
    (matchingLinePolynomial h x v σ).natDegree ≤ Fintype.card ι := by
  unfold matchingLinePolynomial
  apply (natDegree_prod_le Finset.univ _).trans
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] using
    (Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
      natDegree_line_factor_le (h (σ i) + x i) (v i))

theorem coeff_matchingLinePolynomial_card (h x v : ι → ℝ) (σ : Equiv.Perm ι) :
    (matchingLinePolynomial h x v σ).coeff (Fintype.card ι) = ∏ i, v i := by
  unfold matchingLinePolynomial
  simpa only [Finset.card_univ, mul_one, coeff_add, coeff_C, coeff_C_mul, coeff_X_one,
    Nat.one_ne_zero, if_false, zero_add] using
    (coeff_prod_of_natDegree_le (s := Finset.univ)
      (fun i => C (h (σ i) + x i) + C (v i) * X) 1
      (fun i _ => natDegree_line_factor_le (h (σ i) + x i) (v i)))

private theorem weightedLinePolynomial_degree_le {κ : Type*} [Fintype κ]
    (h x v : ι → ℝ) (σ : κ → Equiv.Perm ι) (w : κ → ℝ) :
    (∑ i, C (w i) * matchingLinePolynomial h x v (σ i)).natDegree ≤ Fintype.card ι :=
  natDegree_sum_le_of_forall_le Finset.univ _ fun i _ =>
    (natDegree_C_mul_le _ _).trans (natDegree_matchingLinePolynomial_le h x v (σ i))

private theorem weightedLinePolynomial_coeff_card {κ : Type*} [Fintype κ]
    (h x v : ι → ℝ) (σ : κ → Equiv.Perm ι) (w : κ → ℝ) (hw : ∑ i, w i = 1) :
    (∑ i, C (w i) * matchingLinePolynomial h x v (σ i)).coeff (Fintype.card ι) =
      ∏ i, v i := by
  simp only [finset_sum_coeff, coeff_C_mul, coeff_matchingLinePolynomial_card]
  rw [← Finset.sum_mul, hw, one_mul]

/-- The coefficient vector with the common top-degree coefficient omitted. -/
def spectralLineCoefficients (ι : Type*) [Fintype ι] (p : ℝ[X]) : Fin (Fintype.card ι) → ℝ :=
  fun i => p.coeff i

/-- A support certificate may combine nonnegative squared-minor terms and a
table whose expectation under the signed determinant law is nonnegative. -/
theorem determinantLine_support_of_certificate {κ : Type*} [Fintype κ]
    (h x v : ι → ℝ) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (f : (Fin (Fintype.card ι) → ℝ) →ₗ[ℝ] ℝ) (bound : ℝ)
    (I J : κ → Finset ι) (w : κ → ℝ) (hw : ∀ k, 0 ≤ w k)
    (g : Equiv.Perm ι → ℝ) (hg : 0 ≤ ∑ σ, realSignedWeight U σ * g σ)
    (hcert : ∀ σ, bound - f (spectralLineCoefficients ι (matchingLinePolynomial h x v σ)) =
      g σ + ∑ k, if (J k).map σ.toEmbedding = I k then w k else 0) :
    f (spectralLineCoefficients ι (determinantLinePolynomial h x v U)) ≤ bound := by
  classical
  let p := spectralLineCoefficients ι (determinantLinePolynomial h x v U)
  let vertex σ := spectralLineCoefficients ι (matchingLinePolynomial h x v σ)
  have hp : p = ∑ σ, realSignedWeight U σ • vertex σ := by
    funext i
    simp only [p, vertex, spectralLineCoefficients, determinantLinePolynomial, finset_sum_coeff,
      coeff_C_mul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hminor (k : κ) :
      (∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm ι => (J k).map σ.toEmbedding = I k),
        realSignedWeight U σ) = subsetMinorSq U (I k) (J k) := by
    simpa only [realSignedWeight, Complex.re_sum, Complex.ofReal_re] using
      congrArg Complex.re (sum_signedWeight_image_eq_subsetMinorSq U hU (I k) (J k))
  change f p ≤ bound
  apply sub_nonneg.mp
  calc
    0 ≤ (∑ σ, realSignedWeight U σ * g σ) + ∑ k, subsetMinorSq U (I k) (J k) * w k :=
      add_nonneg hg (Finset.sum_nonneg fun k _ => mul_nonneg (subsetMinorSq_nonneg U _ _) (hw k))
    _ = ∑ σ, realSignedWeight U σ * (bound - f (vertex σ)) := by
      symm
      simp_rw [show ∀ σ, bound - f (vertex σ) =
        g σ + ∑ k, if (J k).map σ.toEmbedding = I k then w k else 0 from hcert,
        mul_add, Finset.mul_sum]
      rw [Finset.sum_add_distrib, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      simp_rw [mul_ite, mul_zero, ← Finset.sum_filter, ← Finset.sum_mul]
      rw [hminor k]
    _ = bound - f p := by
      rw [hp, map_sum]
      simp_rw [map_smul, smul_eq_mul, mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, sum_realSignedWeight U hU, one_mul]

/-- Coefficient hull membership is equivalent to a common law on the entire
complex line. The law needs at most one more assignment than the matrix order. -/
theorem determinantLine_coefficients_mem_hull_iff (h x v : ι → ℝ)
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) :
    spectralLineCoefficients ι (determinantLinePolynomial h x v U) ∈
      convexHull ℝ (Set.range (fun σ => spectralLineCoefficients ι (matchingLinePolynomial h x v σ))) ↔
    ∃ k : ℕ, k ≤ Fintype.card ι + 1 ∧
      ∃ (σ : Fin k → Equiv.Perm ι) (w : Fin k → ℝ), (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧
        ∀ z : ℂ, (∑ i, (w i : ℂ) *
          matchingProduct (fun j => (h j : ℂ)) (partnerOnSpectralLine x v z) (σ i)) =
          determinantValue (fun j => (h j : ℂ)) (partnerOnSpectralLine x v z) U := by
  classical
  let p := determinantLinePolynomial h x v U
  let vertex (σ : Equiv.Perm ι) := spectralLineCoefficients ι (matchingLinePolynomial h x v σ)
  change spectralLineCoefficients ι p ∈ convexHull ℝ (Set.range vertex) ↔ _
  constructor
  · intro hp
    obtain ⟨κ, hκ, g, w, hg, hind, hw, hmass, hsum⟩ := eq_pos_convex_span_of_mem_convexHull hp
    letI : Fintype κ := hκ
    have hg' (i : κ) : ∃ σ, vertex σ = g i := hg ⟨i, rfl⟩
    choose σ hσ using hg'
    have hcard : Fintype.card κ ≤ Fintype.card ι + 1 := by
      have hbound := hind.card_le_finrank_succ.trans (Nat.add_le_add_right (Submodule.finrank_le _) 1)
      simpa only [Module.finrank_pi, Fintype.card_fin] using hbound
    let q : ℝ[X] := ∑ i, C (w i) * matchingLinePolynomial h x v (σ i)
    have hqp : q = p := by
      apply Polynomial.ext
      intro n
      rcases lt_trichotomy n (Fintype.card ι) with hn | rfl | hn
      · have he := congrFun hsum (⟨n, hn⟩ : Fin (Fintype.card ι))
        simpa only [q, finset_sum_coeff, coeff_C_mul, Finset.sum_apply, Pi.smul_apply,
          ← hσ, vertex, spectralLineCoefficients, smul_eq_mul] using he
      · exact (weightedLinePolynomial_coeff_card h x v σ w hmass).trans
          (weightedLinePolynomial_coeff_card h x v id (realSignedWeight U)
            (sum_realSignedWeight U hU)).symm
      · exact (coeff_eq_zero_of_natDegree_lt
          ((weightedLinePolynomial_degree_le h x v σ w).trans_lt hn)).trans
          (coeff_eq_zero_of_natDegree_lt
            ((weightedLinePolynomial_degree_le h x v id (realSignedWeight U)).trans_lt hn)).symm
    let e := Fintype.equivFin κ
    refine ⟨Fintype.card κ, hcard, fun i => σ (e.symm i), fun i => w (e.symm i),
      fun i => (hw (e.symm i)).le, (Equiv.sum_comp e.symm w).trans hmass, ?_⟩
    intro z
    rw [Equiv.sum_comp e.symm (fun i => (w i : ℂ) * matchingProduct (fun j => (h j : ℂ))
      (partnerOnSpectralLine x v z) (σ i))]
    simpa only [q, p, eval₂_finset_sum, eval₂_mul, eval₂_C, Complex.ofRealHom_eq_coe,
      eval_matchingLinePolynomial, eval_determinantLinePolynomial _ _ _ _ hU] using
      congrArg (fun d : ℝ[X] => d.eval₂ Complex.ofRealHom z) hqp
  · rintro ⟨k, _, σ, w, hw, hmass, hrep⟩
    let q : ℝ[X] := ∑ i, C (w i) * matchingLinePolynomial h x v (σ i)
    have hpq : q = p := by
      apply Polynomial.funext
      intro r
      have he : q.eval₂ Complex.ofRealHom (Complex.ofRealHom r) =
          p.eval₂ Complex.ofRealHom (Complex.ofRealHom r) := by
        simpa only [q, p, eval₂_finset_sum, eval₂_mul, eval₂_C, Complex.ofRealHom_eq_coe,
          eval_matchingLinePolynomial, eval_determinantLinePolynomial _ _ _ _ hU] using hrep (r : ℂ)
      exact Complex.ofReal_injective (by simpa only [eval₂_at_apply] using he)
    refine mem_convexHull_of_exists_fintype w (fun i => vertex (σ i)) hw hmass
      (fun i => ⟨σ i, rfl⟩) ?_
    funext i
    rw [← hpq]
    simp only [q, vertex, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, spectralLineCoefficients,
      finset_sum_coeff, coeff_C_mul]

/-- A uniform coefficient-hull theorem for all real triples implies the
Hermitian-by-normal inclusion, by evaluating at the imaginary unit. -/
theorem hermitianByNormal_of_line_coefficientHulls
    (hull : ∀ (h x v : ι → ℝ) (U : Matrix ι ι ℂ), IsUnitary U →
      spectralLineCoefficients ι (determinantLinePolynomial h x v U) ∈
        convexHull ℝ (Set.range (fun σ =>
          spectralLineCoefficients ι (matchingLinePolynomial h x v σ)))) :
    HermitianByNormal ι := by
  intro h b U hU
  let x (i : ι) := (b i).re
  let v (i : ι) := (b i).im
  obtain ⟨k, _, σ, w, hw, hmass, hrep⟩ :=
    (determinantLine_coefficients_mem_hull_iff h x v U hU).mp (hull h x v U hU)
  have hb : partnerOnSpectralLine x v Complex.I = b := funext fun i => Complex.re_add_im (b i)
  unfold Holds
  refine mem_convexHull_of_exists_fintype w (fun i => matchingProduct (fun j => (h j : ℂ)) b (σ i))
    hw hmass (fun i => ⟨σ i, rfl⟩) ?_
  simpa only [hb, Complex.real_smul] using hrep Complex.I

def orderFiveHermitianSpectrum : Fin 5 → ℝ := ![-23, -13, 1, 17, 31]
def orderFiveLineBase : Fin 5 → ℝ := ![14, 37, 48, 91, 123]
def orderFiveLineSlope : Fin 5 → ℝ := ![32, 48, -58, 110, -107]

set_option maxRecDepth 4096 in
/-- The coefficient-hull input for the explicit order-five line yields one
law on at most six permutations, simultaneously for every complex parameter. -/
theorem orderFiveLine_common_weights_of_coefficientHull
    (U : Matrix (Fin 5) (Fin 5) ℂ) (hU : IsUnitary U)
    (hull : spectralLineCoefficients (Fin 5) (determinantLinePolynomial
      orderFiveHermitianSpectrum orderFiveLineBase orderFiveLineSlope Uᴴ) ∈
      convexHull ℝ (Set.range (fun σ => spectralLineCoefficients (Fin 5)
        (matchingLinePolynomial orderFiveHermitianSpectrum orderFiveLineBase orderFiveLineSlope σ)))) :
    ∃ k : ℕ, k ≤ 6 ∧ ∃ (σ : Fin k → Equiv.Perm (Fin 5)) (w : Fin k → ℝ),
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧ ∀ z : ℂ,
        (∑ i, (w i : ℂ) * matchingProduct (fun j => (orderFiveHermitianSpectrum j : ℂ))
          (partnerOnSpectralLine orderFiveLineBase orderFiveLineSlope z) (σ i)) =
        (U * diagonal (fun j => (orderFiveHermitianSpectrum j : ℂ)) * Uᴴ +
          diagonal (partnerOnSpectralLine orderFiveLineBase orderFiveLineSlope z)).det := by
  have hU' : IsUnitary Uᴴ := ⟨by simpa using hU.2, by simpa using hU.1⟩
  obtain ⟨k, hk, σ, w, hw, hmass, hrep⟩ :=
    (determinantLine_coefficients_mem_hull_iff _ _ _ Uᴴ hU').mp hull
  refine ⟨k, by simpa only [Fintype.card_fin] using hk, σ, w, hw, hmass, fun z => ?_⟩
  exact (hrep z).trans (determinantValue_left_conjugation
    (fun j => (orderFiveHermitianSpectrum j : ℂ))
    (partnerOnSpectralLine orderFiveLineBase orderFiveLineSlope z) U hU).symm

end

end MOC
