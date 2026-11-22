import MOC.SpectralGap
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Coordinate stationarity at a positive normalized spectral support maximum. -/

open BigOperators Filter Matrix
open scoped ComplexConjugate InnerProductSpace Topology

namespace MOC

noncomputable section

private theorem active_gradient_radial_combination
    {E J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [Finite J]
    (f : J → E → ℝ) (gradient : J → E) (x : E) (g radial : ℝ)
    (hx : ‖x‖ = 1)
    (hmin : ∀ j, g ≤ f j x)
    (hmax : ∀ y, ‖y‖ ≤ 1 → ∃ j, f j y ≤ g)
    (hderiv : ∀ j (c : ℝ → E) v, c 0 = x → HasDerivAt c v 0 →
      HasDerivAt (fun t => f j (c t)) (⟪gradient j, v⟫_ℝ) 0)
    (hradial : ∀ j, f j x = g → ⟪gradient j, x⟫_ℝ = radial) :
    ∃ (s : Finset {j // f j x = g}) (w : {j // f j x = g} → ℝ),
      (∀ j ∈ s, 0 ≤ w j) ∧ ∑ j ∈ s, w j = 1 ∧
      ∑ j ∈ s, w j • gradient j.1 = radial • x := by
  let tangent (v : E) := v - ⟪x, v⟫_ℝ • x
  let projected (j : J) := gradient j - ⟪gradient j, x⟫_ℝ • x
  let denominator (v : E) (t : ℝ) := 1 + t ^ 2 * ‖tangent v‖ ^ 2
  let c (v : E) (t : ℝ) := (denominator v t)⁻¹ • (x + t • tangent v)
  have hself : ⟪x, x⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hx, one_pow]
  have htangent (v : E) : ⟪x, tangent v⟫_ℝ = 0 := by
    simp [tangent, inner_sub_right, real_inner_smul_right, hself]
  have hden (v : E) (t : ℝ) : 1 ≤ denominator v t := by
    exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg t) (sq_nonneg ‖tangent v‖))
  have hfeasible (v : E) (t : ℝ) : ‖c v t‖ ≤ 1 := by
    have hp : 0 < denominator v t := zero_lt_one.trans_le (hden v t)
    have hnorm : ‖x + t • tangent v‖ ^ 2 = denominator v t := by
      rw [norm_add_sq_real, hx, one_pow, real_inner_smul_right, htangent, mul_zero, mul_zero,
        add_zero, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    apply (sq_le_sq₀ (norm_nonneg _) zero_le_one).mp
    change ‖(denominator v t)⁻¹ • (x + t • tangent v)‖ ^ 2 ≤ (1 : ℝ) ^ 2
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp), mul_pow, hnorm, one_pow]
    have he : (denominator v t)⁻¹ ^ 2 * denominator v t = (denominator v t)⁻¹ := by
      field_simp [hp.ne'] <;> ring
    rw [he]
    exact inv_le_one_of_one_le₀ (hden v t)
  have hc₀ (v : E) : c v 0 = x := by simp [c, denominator]
  have hc' (v : E) : HasDerivAt (c v) (tangent v) 0 := by
    have hden' : HasDerivAt (denominator v) 0 0 := by
      simpa [denominator] using
        (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (‖tangent v‖ ^ 2)).const_add 1
    have hinv : HasDerivAt (fun t => (denominator v t)⁻¹) 0 0 := by
      simpa [denominator] using hden'.inv (by simp [denominator])
    have hlinear : HasDerivAt (fun t : ℝ => x + t • tangent v) (tangent v) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (tangent v)).const_add x
    simpa [c, denominator] using hinv.smul hlinear
  have hpair (j : J) (v : E) : ⟪gradient j, tangent v⟫_ℝ = ⟪projected j, v⟫_ℝ := by
    simp only [tangent, projected, inner_sub_right, inner_sub_left,
      real_inner_smul_right, real_inner_smul_left]
    ring
  have hproj := zero_mem_convexHull_of_active_gradients (fun j => f j x) projected
    (fun j v t => f j (c v t)) g hmin (fun j v => congrArg (f j) (hc₀ v))
    (fun j v => hpair j v ▸ hderiv j (c v) (tangent v) (hc₀ v) (hc' v))
    (fun v => Eventually.of_forall fun t => hmax (c v t) (hfeasible v t))
  rw [convexHull_range_eq_exists_affineCombination] at hproj
  obtain ⟨s, w, hw, hw₁, hsum⟩ := hproj
  rw [Finset.affineCombination_eq_linear_combination _ _ _ hw₁] at hsum
  have hactive (j : {j // f j x = g}) : projected j.1 = gradient j.1 - radial • x := by
    simp only [projected, hradial _ j.2]
  simp_rw [hactive, smul_sub] at hsum
  rw [Finset.sum_sub_distrib, ← Finset.sum_smul, hw₁, one_smul] at hsum
  exact ⟨s, w, hw, hw₁, sub_eq_zero.mp hsum⟩

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private abbrev SpectrumSpace (ι : Type*) := EuclideanSpace ℂ (ι ⊕ ι)

/-- The coefficient of a single spectral coordinate in a matching product. -/
def matchingCoordinateCoefficient (a b : ι → ℂ) (σ : Equiv.Perm ι) : ι ⊕ ι → ℂ
  | .inl i => ∏ j ∈ Finset.univ.erase (σ.symm i), (a (σ j) + b j)
  | .inr j => ∏ k ∈ Finset.univ.erase j, (a (σ k) + b k)

/-- The coefficient of a single spectral coordinate in the signed determinant expansion. -/
def determinantCoordinateCoefficient (a b : ι → ℂ) (U : Matrix ι ι ℂ) (k : ι ⊕ ι) : ℂ :=
  ∑ σ : Equiv.Perm ι, signedWeight U σ * matchingCoordinateCoefficient a b σ k

private theorem matchingCoordinate_sum (a b : ι → ℂ) (σ : Equiv.Perm ι) (v : SpectrumSpace ι) :
    (∑ k, matchingCoordinateCoefficient a b σ k * v k) =
      ∑ j, (∏ l ∈ Finset.univ.erase j, (a (σ l) + b l)) * (v (.inl (σ j)) + v (.inr j)) := by
  rw [Fintype.sum_sum_type, ← Equiv.sum_comp σ
    (fun i => matchingCoordinateCoefficient a b σ (.inl i) * v (.inl i))]
  simp only [matchingCoordinateCoefficient, Equiv.symm_apply_apply, mul_add, Finset.sum_add_distrib]

private theorem determinantCoordinate_sum (a b : ι → ℂ) (U : Matrix ι ι ℂ) (v : SpectrumSpace ι) :
    (∑ σ : Equiv.Perm ι, signedWeight U σ * ∑ k, matchingCoordinateCoefficient a b σ k * v k) =
      ∑ k, determinantCoordinateCoefficient a b U k * v k := by
  simp only [determinantCoordinateCoefficient, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

private theorem coordinate_deriv {c : ℝ → SpectrumSpace ι} {v : SpectrumSpace ι}
    (hc : HasDerivAt c v 0) (k : ι ⊕ ι) : HasDerivAt (fun t => c t k) (v k) 0 :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι ⊕ ι => ℂ) k).hasFDerivAt.comp_hasDerivAt 0 hc

private theorem matchingProduct_deriv (a b : ι → ℂ) (σ : Equiv.Perm ι)
    {c : ℝ → SpectrumSpace ι} {v : SpectrumSpace ι}
    (ha : ∀ i, c 0 (.inl i) = a i) (hb : ∀ j, c 0 (.inr j) = b j)
    (hc : HasDerivAt c v 0) :
    HasDerivAt (fun t => matchingProduct (fun i => c t (.inl i)) (fun j => c t (.inr j)) σ)
      (∑ k, matchingCoordinateCoefficient a b σ k * v k) 0 := by
  rw [matchingCoordinate_sum]
  have hp := HasDerivAt.finset_prod (u := Finset.univ)
    (fun j _ => (coordinate_deriv hc (.inl (σ j))).add (coordinate_deriv hc (.inr j)))
  simpa only [matchingProduct, Finset.prod_apply, smul_eq_mul, ha, hb] using hp

private theorem determinantValue_deriv (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    {c : ℝ → SpectrumSpace ι} {v : SpectrumSpace ι}
    (ha : ∀ i, c 0 (.inl i) = a i) (hb : ∀ j, c 0 (.inr j) = b j)
    (hc : HasDerivAt c v 0) :
    HasDerivAt (fun t => determinantValue (fun i => c t (.inl i)) (fun j => c t (.inr j)) U)
      (∑ k, determinantCoordinateCoefficient a b U k * v k) 0 := by
  have hd := HasDerivAt.sum (u := Finset.univ) (fun σ _ =>
    (matchingProduct_deriv a b σ ha hb hc).const_mul (signedWeight U σ))
  simpa only [Finset.sum_apply, signed_determinant _ _ U hU, determinantCoordinate_sum] using hd

private theorem matchingCoordinate_radial (a b : ι → ℂ) (σ : Equiv.Perm ι)
    (x : SpectrumSpace ι) (ha : ∀ i, x (.inl i) = a i) (hb : ∀ j, x (.inr j) = b j) :
    (∑ k, matchingCoordinateCoefficient a b σ k * x k) =
      (Fintype.card ι : ℂ) * matchingProduct a b σ := by
  rw [matchingCoordinate_sum]
  simp only [ha, hb]
  simp_rw [Finset.prod_erase_mul _ _ (Finset.mem_univ _)]
  simp [matchingProduct, nsmul_eq_mul]

private theorem determinantCoordinate_radial (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (x : SpectrumSpace ι) (ha : ∀ i, x (.inl i) = a i) (hb : ∀ j, x (.inr j) = b j) :
    (∑ k, determinantCoordinateCoefficient a b U k * x k) =
      (Fintype.card ι : ℂ) * determinantValue a b U := by
  rw [← determinantCoordinate_sum, ← signed_determinant a b U hU, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [matchingCoordinate_radial a b σ x ha hb, mul_left_comm]

/-- At a normalized spectral gap maximum, one distribution on the active matchings
satisfies all coordinate equations and has weighted complex gap `g`. -/
theorem exists_active_matching_coordinate_balance [Nonempty ι]
    (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U) (η : ℂ) (g : ℝ)
    (henergy : spectralEnergy a b = 1)
    (hgap : ∀ σ : Equiv.Perm ι, g ≤ (η * (determinantValue a b U - matchingProduct a b σ)).re)
    (hmax : ∀ (c d : ι → ℂ), spectralEnergy c d ≤ 1 →
      ∃ σ : Equiv.Perm ι, (η * (determinantValue c d U - matchingProduct c d σ)).re ≤ g) :
    let active := {σ : Equiv.Perm ι //
      (η * (determinantValue a b U - matchingProduct a b σ)).re = g}
    ∃ (s : Finset active) (w : active → ℝ), (∀ σ ∈ s, 0 ≤ w σ) ∧ ∑ σ ∈ s, w σ = 1 ∧
      (∑ σ ∈ s, (w σ : ℂ) * (η * (determinantValue a b U - matchingProduct a b σ.1))) = g ∧
      ∀ k : ι ⊕ ι,
        ∑ σ ∈ s, (w σ : ℂ) * (η * (determinantCoordinateCoefficient a b U k -
          matchingCoordinateCoefficient a b σ.1 k)) =
          (((Fintype.card ι : ℝ) * g : ℝ) : ℂ) * conj (Sum.elim a b k) := by
  let x : SpectrumSpace ι := (WithLp.equiv 2 _).symm (Sum.elim a b)
  let f (σ : Equiv.Perm ι) (y : SpectrumSpace ι) : ℝ :=
    (η * (determinantValue (fun i => y (.inl i)) (fun j => y (.inr j)) U -
      matchingProduct (fun i => y (.inl i)) (fun j => y (.inr j)) σ)).re
  let R (σ : Equiv.Perm ι) (k : ι ⊕ ι) : ℂ :=
    η * (determinantCoordinateCoefficient a b U k - matchingCoordinateCoefficient a b σ k)
  let grad (σ : Equiv.Perm ι) : SpectrumSpace ι := (WithLp.equiv 2 _).symm (fun k => conj (R σ k))
  have hxcoord (k : ι ⊕ ι) : x k = Sum.elim a b k := rfl
  have hf₀ (σ : Equiv.Perm ι) :
      f σ x = (η * (determinantValue a b U - matchingProduct a b σ)).re := rfl
  have hnorm (y : SpectrumSpace ι) :
      ‖y‖ ^ 2 = spectralEnergy (fun i => y (.inl i)) (fun j => y (.inr j)) := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [spectralEnergy, Fintype.sum_sum_type, Complex.normSq_eq_norm_sq]
  have hx : ‖x‖ = 1 :=
    (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp (by simpa only [hnorm, one_pow] using henergy)
  have hgrad (σ : Equiv.Perm ι) (v : SpectrumSpace ι) :
      ⟪grad σ, v⟫_ℝ = (∑ k, R σ k * v k).re := by
    simp only [grad, PiLp.inner_apply, Complex.inner, WithLp.equiv_symm_pi_apply,
      Complex.conj_conj, Complex.re_sum, mul_comm]
  have hR (σ : Equiv.Perm ι) (v : SpectrumSpace ι) :
      (∑ k, R σ k * v k) =
        η * ((∑ k, determinantCoordinateCoefficient a b U k * v k) -
          ∑ k, matchingCoordinateCoefficient a b σ k * v k) := by
    simp only [R, Finset.mul_sum, ← Finset.sum_sub_distrib, sub_mul, mul_sub, mul_assoc]
  have hf' (σ : Equiv.Perm ι) (c : ℝ → SpectrumSpace ι) (v : SpectrumSpace ι)
      (hc₀ : c 0 = x) (hc : HasDerivAt c v 0) :
      HasDerivAt (fun t => f σ (c t)) (⟪grad σ, v⟫_ℝ) 0 := by
    have ha (i : ι) : c 0 (.inl i) = a i := by rw [hc₀]; rfl
    have hb (j : ι) : c 0 (.inr j) = b j := by rw [hc₀]; rfl
    have hz := ((determinantValue_deriv a b U hU ha hb hc).sub
      (matchingProduct_deriv a b σ ha hb hc)).const_mul η
    have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 hz
    simpa only [hgrad, hR, f, Function.comp_apply, Complex.reCLM_apply] using hr
  have hEuler (σ : Equiv.Perm ι) : (∑ k, R σ k * x k) =
      (Fintype.card ι : ℂ) * (η * (determinantValue a b U - matchingProduct a b σ)) := by
    have ha (i : ι) : x (.inl i) = a i := rfl
    have hb (j : ι) : x (.inr j) = b j := rfl
    rw [hR, determinantCoordinate_radial a b U hU x ha hb,
      matchingCoordinate_radial a b σ x ha hb, ← mul_sub, mul_left_comm η]
  have hradial (σ : Equiv.Perm ι) (hσ : f σ x = g) :
      ⟪grad σ, x⟫_ℝ = (Fintype.card ι : ℝ) * g := by
    rw [hgrad, hEuler,
      ← Complex.ofReal_natCast, Complex.re_ofReal_mul, ← hf₀, hσ]
  have hmax' (y : SpectrumSpace ι) (hy : ‖y‖ ≤ 1) : ∃ σ, f σ y ≤ g := by
    apply hmax
    rw [← hnorm]
    simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg y) hy 2
  obtain ⟨s, w, hw, hw₁, hsum⟩ :=
    active_gradient_radial_combination f grad x g _ hx (fun σ => (hf₀ σ).symm ▸ hgap σ)
      hmax' hf' hradial
  have hcoord (k : ι ⊕ ι) : (∑ σ ∈ s, (w σ : ℂ) * R σ.1 k) =
      (((Fintype.card ι : ℝ) * g : ℝ) : ℂ) * conj (x k) := by
    let ev : SpectrumSpace ι →L[ℝ] ℂ := PiLp.proj 2 (fun _ : ι ⊕ ι => ℂ) k
    have he := congrArg (fun y : SpectrumSpace ι => conj (ev y)) hsum
    simpa only [map_sum, map_smul, ev, PiLp.proj_apply, Complex.real_smul, map_mul,
      Complex.conj_ofReal, grad, WithLp.equiv_symm_pi_apply, Complex.conj_conj] using he
  refine ⟨s, w, hw, hw₁, ?_, fun k => ?_⟩
  · have hcontract := congrArg (fun v : ι ⊕ ι → ℂ => ∑ k, v k * x k) (funext hcoord)
    change (∑ k, (∑ σ ∈ s, (w σ : ℂ) * R σ.1 k) * x k) =
      ∑ k, ((((Fintype.card ι : ℝ) * g : ℝ) : ℂ) * conj (x k)) * x k at hcontract
    simp only [Finset.sum_mul, mul_assoc, ← Complex.normSq_eq_conj_mul_self] at hcontract
    rw [Finset.sum_comm] at hcontract
    simp_rw [← Finset.mul_sum, hEuler, ← mul_left_comm (Fintype.card ι : ℂ)] at hcontract
    rw [← Finset.mul_sum, ← Complex.ofReal_sum, Fintype.sum_sum_type, Complex.ofReal_mul,
      Complex.ofReal_natCast] at hcontract
    have he : (∑ i, Complex.normSq (x (.inl i))) + ∑ j, Complex.normSq (x (.inr j)) = 1 := henergy
    rw [he, Complex.ofReal_one, mul_one] at hcontract
    exact mul_left_cancel₀ (by exact_mod_cast (Fintype.card_ne_zero : Fintype.card ι ≠ 0)) hcontract
  · simpa only [R, hxcoord] using hcoord k

/-- A violating orbit gives a balanced nonnormal positive gap maximum whose active
matching distribution satisfies the spectral coordinate equations. -/
theorem exists_stationary_support_gap_of_not_holds [Nonempty ι]
    (a₀ b₀ : ι → ℂ) (U₀ : Matrix ι ι ℂ) (hU₀ : IsUnitary U₀) (hbad : ¬ Holds a₀ b₀ U₀) :
    ∃ (a b : ι → ℂ) (U : Matrix ι ι ℂ) (η : ℂ) (g : ℝ),
      IsUnitary U ∧ spectralEnergy a b = 1 ∧ Complex.normSq η = 1 ∧ 0 < g ∧
      (∑ i, a i) = (∑ i, b i) ∧
      (∑ i, (Complex.normSq (a i) : ℂ) * a i) =
        (∑ i, (Complex.normSq (b i) : ℂ) * b i) ∧
      ¬ IsStarNormal (diagonal a + U * diagonal b * Uᴴ) ∧
      (∀ σ : Equiv.Perm ι, g ≤ (η * (determinantValue a b U - matchingProduct a b σ)).re) ∧
      let active := {σ : Equiv.Perm ι //
        (η * (determinantValue a b U - matchingProduct a b σ)).re = g}
      ∃ (s : Finset active) (w : active → ℝ), (∀ σ ∈ s, 0 ≤ w σ) ∧ ∑ σ ∈ s, w σ = 1 ∧
        (∑ σ ∈ s, (w σ : ℂ) * (η * (determinantValue a b U - matchingProduct a b σ.1))) = g ∧
        ∀ k : ι ⊕ ι,
          ∑ σ ∈ s, (w σ : ℂ) * (η * (determinantCoordinateCoefficient a b U k -
            matchingCoordinateCoefficient a b σ.1 k)) =
            (((Fintype.card ι : ℝ) * g : ℝ) : ℂ) * conj (Sum.elim a b k) := by
  obtain ⟨a, b, U, η, g, hU, henergy, hη, hg, htrace, hcubic, hnormal, hgap, hglobal⟩ :=
    exists_balanced_support_gap_maximizer a₀ b₀ U₀ hU₀ hbad
  exact ⟨a, b, U, η, g, hU, henergy, hη, hg, htrace, hcubic, hnormal, hgap,
    exists_active_matching_coordinate_balance a b U hU η g henergy hgap
      (fun c d he => hglobal c d U η he hU hη)⟩

end

end MOC
