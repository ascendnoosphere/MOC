import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.Algebra.Polynomial.ofFn
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Topology.Algebra.Module.Cardinality

/-! Polynomial bounds for roots along finite affine projections. -/

open Polynomial
open scoped BigOperators

namespace MOC

private theorem norm_eval_le_polynomial_growth (p : ℂ[X]) (z : ℂ) :
    ‖p.eval z‖ ≤ (∑ k ∈ Finset.range (p.natDegree + 1), ‖p.coeff k‖) *
      (1 + ‖z‖) ^ p.natDegree := by
  rw [eval_eq_sum_range, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
  rw [norm_mul, norm_pow]
  have hk' : k ≤ p.natDegree := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  gcongr
  calc
    ‖z‖ ^ k ≤ (1 + ‖z‖) ^ k := by gcongr; linarith
    _ ≤ (1 + ‖z‖) ^ p.natDegree := pow_le_pow_right₀ (by linarith [norm_nonneg z]) hk'

/-- Every root of a specialized monic polynomial is bounded by one polynomial
growth estimate in the parameter. The bound is uniform across all branches
and includes the exceptional fibers. -/
theorem exists_uniform_polynomial_growth_of_monic_family_roots
    (P : Polynomial (Polynomial ℂ)) (hP : P.Monic) :
    ∃ C : ℝ, 0 < C ∧ ∃ d : ℕ, ∀ z w : ℂ,
      (P.map (Polynomial.evalRingHom z)).IsRoot w → ‖w‖ ≤ C * (1 + ‖z‖) ^ d := by
  classical
  let s := Finset.range P.natDegree
  let d := s.sup (fun k => (P.coeff k).natDegree)
  let A (k : ℕ) : ℝ :=
    ∑ i ∈ Finset.range ((P.coeff k).natDegree + 1), ‖(P.coeff k).coeff i‖
  let C : ℝ := 1 + ∑ k ∈ s, A k
  have hA (k : ℕ) : 0 ≤ A k := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hC : 0 < C := by
    dsimp [C]
    linarith [Finset.sum_nonneg (s := s) (fun k _ => hA k)]
  refine ⟨C, hC, d, fun z w hw => ?_⟩
  let Q := P.map (Polynomial.evalRingHom z)
  have hQ : Q.Monic := hP.map _
  have hd : Q.natDegree = P.natDegree := hP.natDegree_map _
  have hb (k : ℕ) (hk : k ∈ s) : ‖Q.coeff k‖ ≤ (C - 1) * (1 + ‖z‖) ^ d := by
    have hk' : (P.coeff k).natDegree ≤ d := Finset.le_sup (f := fun k => (P.coeff k).natDegree) hk
    change ‖(P.map (Polynomial.evalRingHom z)).coeff k‖ ≤ _
    rw [coeff_map, coe_evalRingHom]
    calc
      _ ≤ A k * (1 + ‖z‖) ^ (P.coeff k).natDegree := norm_eval_le_polynomial_growth _ _
      _ ≤ (C - 1) * (1 + ‖z‖) ^ d := by
        have hak : A k ≤ C - 1 := by
          dsimp only [C]
          have hsum := Finset.single_le_sum (f := A) (fun i _ => hA i) hk
          linarith
        exact mul_le_mul hak (pow_le_pow_right₀ (by linarith [norm_nonneg z]) hk') (by positivity)
          ((hA k).trans hak)
  have hroot := hw.norm_lt_cauchyBound hQ.ne_zero
  have hD : 0 ≤ (C - 1) * (1 + ‖z‖) ^ d := by
    have hp : 0 ≤ C - 1 := by
      dsimp only [C]
      linarith [Finset.sum_nonneg (s := s) (fun k _ => hA k)]
    positivity
  have hsup : (Finset.range Q.natDegree).sup (fun k => ‖Q.coeff k‖₊) ≤
      ⟨(C - 1) * (1 + ‖z‖) ^ d, hD⟩ := by
    apply Finset.sup_le
    intro k hk
    exact hb k (by simpa only [hd] using hk)
  have hbound : Q.cauchyBound ≤ ⟨(C - 1) * (1 + ‖z‖) ^ d, hD⟩ + 1 := by
    simpa only [cauchyBound, hQ.leadingCoeff, nnnorm_one, div_one] using add_le_add_right hsup 1
  have hr : ‖w‖ ≤ (C - 1) * (1 + ‖z‖) ^ d + 1 :=
    (hroot.le.trans hbound : ‖w‖₊ ≤ _)
  have hpow : 1 ≤ (1 + ‖z‖) ^ d := one_le_pow₀ (by linarith [norm_nonneg z])
  exact hr.trans (by linarith)

open scoped NNReal

/-- An entire function of polynomial growth is a polynomial. The proof bounds
each Cauchy coefficient above the growth order by a constant divided by an
arbitrarily large radius. -/
theorem exists_polynomial_eval_of_entire_growth
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (C : ℝ) (hC : 0 ≤ C) (d : ℕ)
    (hb : ∀ z, ‖f z‖ ≤ C * (1 + ‖z‖) ^ d) :
    ∃ p : ℂ[X], ∀ z, p.eval z = f z := by
  let a (n : ℕ) := cauchyPowerSeries f 0 1 n (fun _ => 1)
  have hF := hf.hasFPowerSeriesOnBall 0 (R := 1) (by norm_num)
  have hvanish (n : ℕ) (hn : d < n) : a n = 0 := by
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    apply le_of_forall_gt_imp_ge_of_dense
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (max (1 : ℝ) (C * 2 ^ d / ε))
    let R : ℝ≥0 := N
    have hR1 : 1 < (R : ℝ) := (le_max_left _ _).trans_lt hN
    have hR : 0 < (R : ℝ) := zero_lt_one.trans hR1
    have hR' : 0 < R := NNReal.coe_pos.mp hR
    have heq := hF.hasFPowerSeriesAt.eq_formalMultilinearSeries
      (hf.hasFPowerSeriesOnBall 0 hR').hasFPowerSeriesAt
    have har : a n = cauchyPowerSeries f 0 (R : ℝ) n (fun _ => 1) :=
      congrArg (fun p => p n (fun _ => 1)) heq
    rw [har, cauchyPowerSeries_apply]
    have hcircle (z : ℂ) (hz : z ∈ Metric.sphere (0 : ℂ) (R : ℝ)) :
        ‖((1 : ℂ) / (z - 0)) ^ n • (z - 0)⁻¹ • f z‖ ≤
          (C * 2 ^ d * (R : ℝ) ^ d) / (R : ℝ) ^ (n + 1) := by
      have hz' : ‖z‖ = (R : ℝ) := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
      rw [norm_smul, norm_smul, norm_pow, norm_div, norm_one, norm_inv, sub_zero, hz']
      have hfc : ‖f z‖ ≤ C * 2 ^ d * (R : ℝ) ^ d := by
        have h := hb z
        rw [hz'] at h
        have hr : 1 + (R : ℝ) ≤ 2 * (R : ℝ) := by linarith
        have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hr d) hC
        rw [mul_pow, ← mul_assoc] at hh
        exact h.trans hh
      calc
        _ ≤ (1 / (R : ℝ)) ^ n * ((R : ℝ)⁻¹ * (C * 2 ^ d * (R : ℝ) ^ d)) := by gcongr
        _ = _ := by rw [one_div, inv_pow, pow_succ]; field_simp
    calc
      _ ≤ (R : ℝ) * ((C * 2 ^ d * (R : ℝ) ^ d) / (R : ℝ) ^ (n + 1)) :=
        circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hR.le hcircle
      _ = (C * 2 ^ d * (R : ℝ) ^ d) / (R : ℝ) ^ n := by
        rw [pow_succ]; field_simp; ring
      _ ≤ (C * 2 ^ d) / (R : ℝ) := by
        apply (div_le_div_iff₀ (pow_pos hR _) hR).2
        rw [mul_assoc, ← pow_succ]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hR1.le (Nat.succ_le_of_lt hn)) (by positivity)
      _ ≤ ε := by
        apply (div_le_iff₀ hR).2
        have hh := (div_lt_iff₀ hε).1 ((le_max_right _ _).trans_lt hN)
        change C * 2 ^ d ≤ ε * (N : ℝ)
        simpa [mul_comm] using hh.le
  let p : ℂ[X] := ∑ n ∈ Finset.range (d + 1), Polynomial.C (a n) * X ^ n
  refine ⟨p, fun z => ?_⟩
  have hz : z ∈ EMetric.ball (0 : ℂ) ⊤ := EMetric.mem_ball.mpr (edist_lt_top ..)
  have hs := (hF.hasSum_sub hz).tsum_eq
  change (∑' n : ℕ, cauchyPowerSeries f 0 (1 : ℝ) n (fun _ => z - 0)) = f z at hs
  have hterm (n : ℕ) :
      cauchyPowerSeries f 0 1 n (fun _ => z - 0) = a n * z ^ n := by
    simp only [a, cauchyPowerSeries, ContinuousMultilinearMap.mkPiRing_apply, Fin.prod_const,
      sub_zero, one_pow, one_smul, smul_eq_mul]
    ring
  simp only [hterm] at hs
  rw [tsum_eq_sum (s := Finset.range (d + 1))] at hs
  · simpa only [p, eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X] using hs
  · intro n hn
    rw [hvanish n (by simpa using hn), zero_mul]

open Filter Set
open scoped Topology

/-- A holomorphic coefficient function on the complement of finitely many
parameter values is polynomial if it has a uniform polynomial growth bound
there. In particular, the omitted values need no local branch choices. -/
theorem exists_polynomial_eval_off_finite_of_growth
    {S : Set ℂ} (hS : S.Finite) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f Sᶜ) (C : ℝ) (hC : 0 ≤ C) (d : ℕ)
    (hb : ∀ z ∈ Sᶜ, ‖f z‖ ≤ C * (1 + ‖z‖) ^ d) :
    ∃ p : ℂ[X], ∀ z ∈ Sᶜ, p.eval z = f z := by
  classical
  let F (z : ℂ) := if z ∈ S then limUnder (𝓝[≠] z) f else f z
  have hEq : EqOn F f Sᶜ := fun z hz => if_neg (show z ∉ S from hz)
  have hOpen : IsOpen Sᶜ := hS.isClosed.isOpen_compl
  have hF : Differentiable ℂ F := by
    intro x
    by_cases hx : x ∈ S
    · let T : Set ℂ := (S \ {x})ᶜ ∩ {z | ‖z‖ < ‖x‖ + 1}
      have hT : T ∈ 𝓝 x := by
        have h1 : IsOpen (S \ {x})ᶜ := hS.diff.isClosed.isOpen_compl
        have h2 : IsOpen {z : ℂ | ‖z‖ < ‖x‖ + 1} :=
          isOpen_lt continuous_norm continuous_const
        exact (h1.inter h2).mem_nhds ⟨by simp, by simp⟩
      have hlocal (z : ℂ) (hz : z ∈ T \ {x}) : z ∈ Sᶜ :=
        fun he => hz.1.1 ⟨he, hz.2⟩
      have hd : DifferentiableOn ℂ f (T \ {x}) := hf.mono hlocal
      have hh : BddAbove (norm ∘ f '' (T \ {x})) := by
        use C * ((1 + (‖x‖ + 1)) ^ d)
        rintro _ ⟨z, hz, rfl⟩
        have hz' := (hb z (hlocal z hz))
        have hzn : ‖z‖ < ‖x‖ + 1 := hz.1.2
        exact hz'.trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) (by linarith) d) hC)
      have hupdate := Complex.differentiableOn_update_limUnder_of_bddAbove hT hd hh
      apply (hupdate.differentiableAt hT).congr_of_eventuallyEq
      filter_upwards [hT] with z hz
      by_cases he : z = x
      · subst z
        simp [F, hx]
      · have hs : z ∈ Sᶜ := hlocal z ⟨hz, he⟩
        rw [hEq hs, Function.update_of_ne he]
    · apply (hf.differentiableAt (hOpen.mem_nhds hx)).congr_of_eventuallyEq
      filter_upwards [hOpen.mem_nhds hx] with z hz
      exact hEq hz
  have hclosed : IsClosed {z : ℂ | ‖F z‖ ≤ C * (1 + ‖z‖) ^ d} :=
    isClosed_le hF.continuous.norm (continuous_const.mul ((continuous_const.add continuous_norm).pow d))
  have hdense : Dense Sᶜ := hS.countable.dense_compl ℂ
  have hB (z : ℂ) : ‖F z‖ ≤ C * (1 + ‖z‖) ^ d := by
    apply hclosed.closure_subset_iff.mpr _ (hdense z)
    intro w hw
    simpa only [Set.mem_setOf_eq, hEq hw] using hb w hw
  obtain ⟨p, hp⟩ := exists_polynomial_eval_of_entire_growth hF C hC d hB
  exact ⟨p, fun z hz => (hp z).trans (hEq hz)⟩

private theorem norm_coeff_prod_roots_le (s : Multiset ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hroot : ∀ w ∈ s, ‖w‖ ≤ B) (k : ℕ) :
    ‖((s.map fun w => (X : ℂ[X]) - C w).prod).coeff k‖ ≤ (1 + B) ^ s.card := by
  induction s using Multiset.induction_on generalizing k with
  | empty =>
    simp only [Multiset.map_zero, Multiset.prod_zero, Multiset.card_zero, pow_zero, coeff_one]
    split <;> simp
  | cons w s ih =>
    have hw : ‖w‖ ≤ B := hroot w (Multiset.mem_cons_self _ _)
    have hs (j : ℕ) := ih (fun u hu => hroot u (Multiset.mem_cons_of_mem hu)) j
    let Q : ℂ[X] := (s.map fun w => (X : ℂ[X]) - C w).prod
    have hprod (j : ℕ) : ‖w * Q.coeff j‖ ≤ B * (1 + B) ^ s.card := by
      rw [norm_mul]
      exact mul_le_mul hw (hs j) (norm_nonneg _) hB
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ, sub_mul, coeff_sub,
      coeff_C_mul]
    cases k with
    | zero =>
      rw [coeff_X_mul_zero, zero_sub, norm_neg]
      exact (hprod 0).trans (by nlinarith [show 0 ≤ (1 + B) ^ s.card by positivity])
    | succ k =>
      rw [coeff_X_mul]
      exact (norm_sub_le ..).trans ((add_le_add (hs k) (hprod (k + 1))).trans (by ring_nf; rfl))

/-- Every coefficient of every monic factor of a specialized family has
one common polynomial growth bound in the parameter. -/
theorem exists_uniform_polynomial_growth_of_monic_family_factor_coeffs
    (P : Polynomial (Polynomial ℂ)) (hP : P.Monic) :
    ∃ A : ℝ, 0 < A ∧ ∃ D : ℕ, ∀ (z : ℂ) (Q : ℂ[X]),
      Q.Monic → Q ∣ P.map (Polynomial.evalRingHom z) →
      ∀ k, ‖Q.coeff k‖ ≤ A * (1 + ‖z‖) ^ D := by
  obtain ⟨C, hC, d, hb⟩ := exists_uniform_polynomial_growth_of_monic_family_roots P hP
  refine ⟨(1 + C) ^ P.natDegree, by positivity, d * P.natDegree, fun z Q hQ hdiv k => ?_⟩
  let E := P.map (Polynomial.evalRingHom z)
  have hE : E.Monic := hP.map _
  let B : ℝ := C * (1 + ‖z‖) ^ d
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hs := IsAlgClosed.splits Q
  have hroots (w : ℂ) (hw : w ∈ Q.roots) : ‖w‖ ≤ B := by
    have hr := (mem_roots hQ.ne_zero).mp hw
    rcases hdiv with ⟨W, hW⟩
    apply hb z w
    change (P.map (Polynomial.evalRingHom z)).eval w = 0
    rw [hW, eval_mul, hr, zero_mul]
  have hcard : Q.roots.card = Q.natDegree := splits_iff_card_roots.1 hs
  have hn : Q.natDegree ≤ P.natDegree := (natDegree_le_of_dvd hdiv hE.ne_zero).trans
    (hP.natDegree_map _).le
  have hcoeff := norm_coeff_prod_roots_le Q.roots B hB hroots k
  rw [← eq_prod_roots_of_monic_of_splits_id hQ hs, hcard] at hcoeff
  have hpow : 1 ≤ (1 + ‖z‖) ^ d := one_le_pow₀ (by linarith [norm_nonneg z])
  calc
    _ ≤ (1 + B) ^ Q.natDegree := hcoeff
    _ ≤ (1 + B) ^ P.natDegree := pow_le_pow_right₀ (by linarith) hn
    _ ≤ ((1 + C) * (1 + ‖z‖) ^ d) ^ P.natDegree := by
      apply pow_le_pow_left₀ (by positivity) _ _
      dsimp [B]
      rw [add_mul, one_mul]
      linarith
    _ = _ := by rw [mul_pow, pow_mul]

/-- A holomorphic family of monic factors of a specialized monic polynomial
over a finitely punctured plane has polynomial coefficients. -/
theorem exists_polynomial_family_of_holomorphic_monic_factors
    (P : Polynomial (Polynomial ℂ)) (hP : P.Monic)
    {S : Set ℂ} (hS : S.Finite) (F : ℂ → ℂ[X])
    (hm : ∀ z ∈ Sᶜ, (F z).Monic)
    (hd : ∀ z ∈ Sᶜ, F z ∣ P.map (Polynomial.evalRingHom z))
    (hh : ∀ k ≤ P.natDegree, DifferentiableOn ℂ (fun z => (F z).coeff k) Sᶜ) :
    ∃ Q : Polynomial (Polynomial ℂ), ∀ z ∈ Sᶜ, Q.map (Polynomial.evalRingHom z) = F z := by
  classical
  obtain ⟨A, hA, D, hb⟩ := exists_uniform_polynomial_growth_of_monic_family_factor_coeffs P hP
  have hv (k : Fin (P.natDegree + 1)) :
      ∃ p : ℂ[X], ∀ z ∈ Sᶜ, p.eval z = (F z).coeff k :=
    exists_polynomial_eval_off_finite_of_growth hS (hh k (Nat.le_of_lt_succ k.isLt))
      A hA.le D (fun z hz => hb z (F z) (hm z hz) (hd z hz) k)
  choose b hb using hv
  refine ⟨Polynomial.ofFn (P.natDegree + 1) b, fun z hz => ?_⟩
  ext k
  rw [coeff_map, coe_evalRingHom]
  by_cases hk : k < P.natDegree + 1
  · rw [ofFn_coeff_eq_val_of_lt b hk]
    exact hb ⟨k, hk⟩ z hz
  · rw [ofFn_coeff_eq_zero_of_ge b (Nat.le_of_not_gt hk), eval_zero]
    symm
    apply coeff_eq_zero_of_natDegree_lt
    have hdeg := (natDegree_le_of_dvd (hd z hz) (hP.map (evalRingHom z)).ne_zero).trans
      (hP.natDegree_map (evalRingHom z)).le
    omega

/-- A nontrivial holomorphic factorization over a finitely punctured plane
forces an algebraic factorization of the original two-variable polynomial. -/
theorem not_irreducible_of_holomorphic_monic_factorization
    (P : Polynomial (Polynomial ℂ)) (hP : P.Monic)
    {S : Set ℂ} (hS : S.Finite) (F G : ℂ → ℂ[X])
    (hmF : ∀ z ∈ Sᶜ, (F z).Monic) (hmG : ∀ z ∈ Sᶜ, (G z).Monic)
    (hfg : ∀ z ∈ Sᶜ, P.map (Polynomial.evalRingHom z) = F z * G z)
    (hhF : ∀ k ≤ P.natDegree, DifferentiableOn ℂ (fun z => (F z).coeff k) Sᶜ)
    (hhG : ∀ k ≤ P.natDegree, DifferentiableOn ℂ (fun z => (G z).coeff k) Sᶜ)
    {z₀ : ℂ} (hz₀ : z₀ ∈ Sᶜ) (hF₀ : 0 < (F z₀).natDegree)
    (hG₀ : 0 < (G z₀).natDegree) : ¬ Irreducible P := by
  obtain ⟨Q, hQ⟩ := exists_polynomial_family_of_holomorphic_monic_factors P hP hS F hmF
    (fun z hz => ⟨G z, hfg z hz⟩) hhF
  obtain ⟨T, hT⟩ := exists_polynomial_family_of_holomorphic_monic_factors P hP hS G hmG
    (fun z hz => ⟨F z, (hfg z hz).trans (mul_comm _ _)⟩) hhG
  have hQTeq : P = Q * T := by
    apply Polynomial.ext
    intro k
    apply eq_of_infinite_eval_eq
    have hi : Sᶜ.Infinite := (Set.infinite_univ.diff hS).mono (fun _ hz => hz.2)
    apply hi.mono
    intro z hz
    have he : P.map (evalRingHom z) = (Q * T).map (evalRingHom z) := by
      rw [Polynomial.map_mul, hQ z hz, hT z hz, hfg z hz]
    simpa only [coeff_map, coe_evalRingHom]
      using congrArg (fun V : ℂ[X] => V.coeff k) he
  intro h
  rcases h.isUnit_or_isUnit hQTeq with hq | ht
  · have hu : IsUnit (F z₀) := (hQ z₀ hz₀) ▸ hq.map (Polynomial.mapRingHom (evalRingHom z₀))
    exact (Nat.ne_of_gt hF₀) (natDegree_eq_zero_of_isUnit hu)
  · have hu : IsUnit (G z₀) := (hT z₀ hz₀) ▸ ht.map (Polynomial.mapRingHom (evalRingHom z₀))
    exact (Nat.ne_of_gt hG₀) (natDegree_eq_zero_of_isUnit hu)

end MOC
