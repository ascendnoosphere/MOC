import MOC.Weights
import MOC.Support
import MOC.ContactTransfer
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Roots

/-! The translation-line obstruction in arbitrary-order contact reduction.
   The contact-count strategy extends Zheng, Theorem 3.6,
   DOI: 10.13140/RG.2.2.36790.25923. -/

open scoped BigOperators Manifold Topology
open Polynomial

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem matchingProduct_swap_cross (a b : ι → ℂ) (σ : Equiv.Perm ι)
    {o j : ι} (h : o ≠ j) :
    matchingProduct a b σ * ((a (σ j) + b o) * (a (σ o) + b j)) =
      matchingProduct a b (σ * Equiv.swap o j) * ((a (σ o) + b o) * (a (σ j) + b j)) := by
  let S : Finset ι := {o, j}
  let R := ∏ m ∈ Sᶜ, (a (σ m) + b m)
  have hf (τ : Equiv.Perm ι) (he : ∀ m ∈ Sᶜ, τ m = σ m) :
      matchingProduct a b τ = R * ((a (τ o) + b o) * (a (τ j) + b j)) := by
    let f (m : ι) := a (τ m) + b m
    have hR : (∏ m ∈ Sᶜ, f m) = R := by
      apply Finset.prod_congr rfl
      intro m hm
      simp only [f, he m hm]
    change (∏ m, f m) = _
    rw [← Finset.prod_compl_mul_prod S f, hR]
    congr 1
    simp [S, f, Finset.prod_insert, h]
  have hs (m : ι) (hm : m ∈ Sᶜ) : Equiv.swap o j m = m := by
    have h' : m ≠ o ∧ m ≠ j := by simpa [S, not_or] using Finset.mem_compl.mp hm
    exact Equiv.swap_apply_of_ne_of_ne h'.1 h'.2
  rw [hf σ (fun _ _ => rfl), hf (σ * Equiv.swap o j) (fun m hm => by
    simp [Equiv.Perm.mul_apply, hs m hm])]
  simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
  ring

private def anchorPlus (o j i : ι) : Equiv.Perm ι :=
  if j = o ∨ i = o then 1 else Equiv.swap j i

private def anchorMinus (o j i : ι) : Equiv.Perm ι :=
  if j = o ∨ i = o then 1 else Equiv.swap j i * Equiv.swap o j

private theorem anchored_cross (a b : ι → ℂ) (o j i : ι) :
    matchingProduct a b (anchorPlus o j i) * ((a i + b o) * (a o + b j)) =
      matchingProduct a b (anchorMinus o j i) * ((a o + b o) * (a i + b j)) := by
  by_cases h : j = o ∨ i = o
  · rcases h with rfl | rfl <;> simp [anchorPlus, anchorMinus, mul_comm]
  · have hj : j ≠ o := fun hj => h (Or.inl hj)
    have hi : i ≠ o := fun hi => h (Or.inr hi)
    simpa [anchorPlus, anchorMinus, h, Equiv.swap_apply_of_ne_of_ne hj.symm hi.symm,
      Equiv.swap_apply_left] using matchingProduct_swap_cross a b (Equiv.swap j i) hj.symm

private theorem translation_eval_relation (a b : ι → ℂ) (o : ι)
    (hnz : ∀ σ, matchingProduct a b σ ≠ 0) (σ : Equiv.Perm ι) :
    matchingProduct a b σ *
      ((∏ j, matchingProduct a b (anchorMinus o j (σ j))) *
        ∏ j, matchingProduct a b (anchorPlus o j j)) =
    matchingProduct a b 1 *
      ((∏ j, matchingProduct a b (anchorPlus o j (σ j))) *
        ∏ j, matchingProduct a b (anchorMinus o j j)) := by
  let x (τ : Equiv.Perm ι) := ∏ j, matchingProduct a b (anchorPlus o j (τ j))
  let y (τ : Equiv.Perm ι) := ∏ j, matchingProduct a b (anchorMinus o j (τ j))
  let d := (∏ i, (a i + b o)) * ∏ j, (a o + b j)
  let c := ∏ _ : ι, (a o + b o)
  have hentry (i j : ι) : a i + b j ≠ 0 := by
    simpa using (Finset.prod_ne_zero_iff.mp (hnz (Equiv.swap j i)) j (Finset.mem_univ j))
  have hd : d ≠ 0 := mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => hentry i o)
    (Finset.prod_ne_zero_iff.mpr fun j _ => hentry o j)
  have he (τ : Equiv.Perm ι) : x τ * d = y τ * (c * matchingProduct a b τ) := by
    have hh := Equiv.prod_comp τ (fun i => a i + b o)
    simpa only [x, y, d, c, matchingProduct, Finset.prod_mul_distrib, hh]
      using (Finset.prod_congr (show (Finset.univ : Finset ι) = Finset.univ from rfl)
        (fun j (_ : j ∈ Finset.univ) => anchored_cross a b o j (τ j)))
  change matchingProduct a b σ * (y σ * x 1) = matchingProduct a b 1 * (x σ * y 1)
  apply mul_right_cancel₀ hd
  calc
    _ = matchingProduct a b σ * y σ * (x 1 * d) := by ring
    _ = matchingProduct a b 1 * y 1 * (x σ * d) := by rw [he σ, he 1]; ring
    _ = _ := by ring

private noncomputable def lin (z : ℂ) : ℂ[X] := 1 + C z * X

private theorem coeff_one_prod_lin {κ : Type*} (s : Finset κ) (f : κ → ℂ) :
    (∏ j ∈ s, lin (f j)).coeff 1 = ∑ j ∈ s, f j := by
  classical
  have hzero (s : Finset κ) : (∏ j ∈ s, lin (f j)).coeff 0 = 1 := by
    rw [coeff_zero_eq_eval_zero, eval_prod]
    simp [lin]
  induction s using Finset.induction_on with
  | empty => simp [coeff_one]
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj, mul_coeff_one]
    have h0 : (lin (f j)).coeff 0 = 1 := by simp [lin, coeff_one]
    have h1 : (lin (f j)).coeff 1 = f j := by simp [lin, coeff_one]
    rw [h0, h1, hzero s, ih, one_mul, mul_one, add_comm]

/-- If infinitely many constant translates of a profile are realizable by additive complex
spectra, the profile is affine-linear in the singleton assignment indicators. -/
theorem singleton_expansion_of_infinite_matching_translates
    (p : Equiv.Perm ι → ℂ)
    (hline : Set.Infinite {t : ℂ | ∃ a b : ι → ℂ, ∀ σ, matchingProduct a b σ = p σ + t}) :
    ∃ c : ℂ, ∃ Q : ι → ι → ℂ, ∀ σ, p σ = c + ∑ j, Q j (σ j) := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl hempty =>
    letI := hempty
    exact ⟨p 1, 0, fun σ => by rw [Subsingleton.elim σ 1]; simp⟩
  | inr hne =>
    letI := hne
    let o : ι := Classical.choice hne
    let A (j i : ι) := p (anchorPlus o j i)
    let B (j i : ι) := p (anchorMinus o j i)
    let Q (j i : ι) := A j i - B j i
    have heq (σ : Equiv.Perm ι) :
        lin (p σ) * ((∏ j, lin (B j (σ j))) * ∏ j, lin (A j j)) =
        lin (p 1) * ((∏ j, lin (A j (σ j))) * ∏ j, lin (B j j)) := by
      let F := lin (p σ) * ((∏ j, lin (B j (σ j))) * ∏ j, lin (A j j)) -
        lin (p 1) * ((∏ j, lin (A j (σ j))) * ∏ j, lin (B j j))
      have hfinite : ({0} ∪ Set.range (fun τ : Equiv.Perm ι => -p τ) : Set ℂ).Finite :=
        (Set.finite_singleton 0).union (Set.finite_range _)
      apply sub_eq_zero.mp
      change F = 0
      apply eq_zero_of_infinite_isRoot F
      apply ((hline.diff hfinite).image (f := fun x : ℂ => x⁻¹) (fun _ _ _ _ h => inv_injective h)).mono
      rintro _ ⟨s, hs, rfl⟩
      let t := s⁻¹
      have hs0 : s ≠ 0 := fun he => hs.2 (Or.inl he)
      have ht0 : t ≠ 0 := inv_ne_zero hs0
      have hnonzero (τ : Equiv.Perm ι) : p τ + s ≠ 0 := by
        intro he
        exact hs.2 (Or.inr ⟨τ, (eq_neg_of_add_eq_zero_right he).symm⟩)
      obtain ⟨a, b, hab⟩ := hs.1
      have hs_eq : s = t⁻¹ := by simp [t]
      obtain ⟨k, hk⟩ := IsAlgClosed.exists_pow_nat_eq t (Fintype.card_pos_iff.mpr hne)
      let a' := fun i => k * a i
      let b' := fun i => k * b i
      have heval (τ : Equiv.Perm ι) : matchingProduct a' b' τ = (lin (p τ)).eval t := by
        simp only [a', b', matchingProduct_scale, hk, hab, lin, eval_add, eval_mul, eval_C,
          eval_X, eval_one, hs_eq, mul_add, mul_inv_cancel₀ ht0]
        ring
      have hi (τ : Equiv.Perm ι) : matchingProduct a' b' τ ≠ 0 := by
        simpa only [a', b', matchingProduct_scale, hk, hab] using mul_ne_zero ht0 (hnonzero τ)
      change F.eval t = 0
      simp only [F, eval_sub, eval_mul, eval_prod, A, B, ← heval]
      exact sub_eq_zero.mpr (translation_eval_relation a' b' o hi σ)
    have hz (x : ℂ) : (lin x).coeff 0 = 1 := by simp [lin, coeff_one]
    have hzo (f : ι → ℂ) : (∏ j, lin (f j)).coeff 0 = 1 := by
      rw [coeff_zero_eq_eval_zero, eval_prod]
      simp [lin]
    have ho (x : ℂ) : (lin x).coeff 1 = x := by simp [lin, coeff_one]
    refine ⟨p 1 - ∑ j, Q j j, Q, fun σ => ?_⟩
    have hc := congrArg (fun P : ℂ[X] => P.coeff 1) (heq σ)
    simp only [mul_coeff_one, mul_coeff_zero, hz, hzo, ho, coeff_one_prod_lin,
      one_mul, mul_one] at hc
    simp only [Q, Finset.sum_sub_distrib]
    linear_combination hc

/-- The full constant translation line is a special case of infinite realizability. -/
theorem singleton_expansion_of_matching_translation_line
    (p : Equiv.Perm ι → ℂ)
    (hline : ∀ t : ℂ, ∃ a b : ι → ℂ, ∀ σ, matchingProduct a b σ = p σ + t) :
    ∃ c : ℂ, ∃ Q : ι → ι → ℂ, ∀ σ, p σ = c + ∑ j, Q j (σ j) :=
  singleton_expansion_of_infinite_matching_translates p (Set.infinite_univ.mono (fun t _ => hline t))

/-- An exact matching profile supporting the full constant translation line
already satisfies MOC for every relative unitary. -/
theorem holds_of_matching_translation_line
    (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (hline : ∀ t : ℂ, ∃ a' b' : ι → ℂ,
      ∀ σ, matchingProduct a' b' σ = matchingProduct a b σ + t) :
    Holds a b U := by
  obtain ⟨c, Q, hQ⟩ := singleton_expansion_of_matching_translation_line _ hline
  exact holds_of_singleton_expansion a b U hU c Q hQ

/-- The complex gap on the profile space, linear in the matching differences. -/
noncomputable def matchingProfileDetGap
    (U : Matrix ι ι ℂ) (η : ℂ) (r : Equiv.Perm ι) (p : Equiv.Perm ι → ℂ) : ℂ :=
  ∑ σ, (realSignedWeight U σ : ℂ) * (η * (p σ - p r))

theorem matchingProfileDetGap_matchingProduct
    (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U) (η : ℂ) (r : Equiv.Perm ι) :
    matchingProfileDetGap U η r (matchingProduct a b) =
      η * (determinantValue a b U - matchingProduct a b r) := by
  have hs : ∑ σ, (realSignedWeight U σ : ℂ) = 1 := by
    exact_mod_cast sum_realSignedWeight U hU
  unfold matchingProfileDetGap
  simp_rw [← mul_left_comm η]
  rw [← Finset.mul_sum]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, real_signed_determinant a b U hU,
    ← Finset.sum_mul, hs, one_mul]
  exact mul_sub _ _ _

/-- Along a compactified profile curve that fixes the old complex contact
differences and the complex signed determinant gap, a varying difference
forces a new contact without changing the strict violation. The curve is
required to lie in the exact matching-profile image only off its finite
set of omitted points; it does not need differentiable spectral lifts. -/
theorem exists_strictly_violating_profile_with_more_contacts_on_curve
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ, ℂ) 1 M] [CompactSpace M] [ConnectedSpace M]
    {S : Set M} (hS : S.Finite) (hconn : IsPreconnected Sᶜ)
    (P : M → Equiv.Perm ι → ℂ)
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) (η : ℂ) (r : Equiv.Perm ι)
    (J : Finset (Equiv.Perm ι))
    (hexact : ∀ x ∈ Sᶜ, ∃ a b : ι → ℂ, matchingProduct a b = P x)
    (hhol : ∀ σ ∈ J, MDifferentiableOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
      (fun x => η * (P x r - P x σ)) Sᶜ)
    {x₀ : M} (hx₀ : x₀ ∈ Sᶜ)
    (hold : ∀ x ∈ Sᶜ, ∀ σ ∉ J, P x r - P x σ = P x₀ r - P x₀ σ)
    (hold₀ : ∀ σ ∉ J, (η * (P x₀ r - P x₀ σ)).re = 0)
    (hgap : ∀ x ∈ Sᶜ, matchingProfileDetGap U η r (P x) =
      matchingProfileDetGap U η r (P x₀))
    (hstrict : 0 < (matchingProfileDetGap U η r (P x₀)).re)
    (hstart : ∀ σ ∈ J, 0 < (η * (P x₀ r - P x₀ σ)).re)
    (hvar : ∃ σ ∈ J, ∃ x ∈ Sᶜ, ∃ y ∈ Sᶜ, η * (P x r - P x σ) ≠ η * (P y r - P y σ)) :
    ∃ (z : M), z ∈ Sᶜ ∧ ∃ a b : ι → ℂ, matchingProduct a b = P z ∧
      (∀ σ, 0 ≤ matchingGap a b η r σ) ∧
      (∀ σ ∉ J, matchingGap a b η r σ = 0) ∧
      (∃ σ ∈ J, matchingGap a b η r σ = 0) ∧
      ∀ σ, (η * matchingProduct a b σ).re < (η * determinantValue a b U).re := by
  let H (σ : Equiv.Perm ι) (x : M) := η * (P x r - P x σ)
  obtain ⟨z, hz, hnonneg, j, hj, hjz⟩ :=
    exists_new_contact_on_curve J hS hconn H hhol hx₀ hstart hvar
  obtain ⟨a, b, hab⟩ := hexact z hz
  have hH (σ : Equiv.Perm ι) : (H σ z).re = matchingGap a b η r σ := by
    simp only [H, ← hab, matchingGap, mul_sub, Complex.sub_re]
  have hall (σ : Equiv.Perm ι) : 0 ≤ matchingGap a b η r σ := by
    rw [← hH]
    by_cases hσ : σ ∈ J
    · exact hnonneg σ hσ
    · simpa only [H, hold z hz σ hσ, hold₀ σ hσ] using le_refl (0 : ℝ)
  have hstrict' : (η * matchingProduct a b r).re <
      (η * determinantValue a b U).re := by
    rw [← sub_pos, ← Complex.sub_re, ← mul_sub, ← matchingProfileDetGap_matchingProduct a b U hU,
      hab, hgap z hz]
    exact hstrict
  exact ⟨z, hz, a, b, hab, hall, fun σ hσ => by
    rw [← hH]
    exact congrArg (fun u : ℂ => (η * u).re) (hold z hz σ hσ) |>.trans (hold₀ σ hσ),
    ⟨j, hj, (hH j).symm.trans hjz⟩, fun σ => (sub_nonneg.mp (hall σ)).trans_lt hstrict'⟩

/-- A genuine counterexample can have only finitely many realizable constant
translates. In particular, a nonconstant exact profile curve through the
counterexample cannot vary solely by constant translation. -/
theorem finite_matching_translates_of_not_holds
    (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U) (hbad : ¬ Holds a b U) :
    Set.Finite {t : ℂ | ∃ a' b' : ι → ℂ,
      ∀ σ, matchingProduct a' b' σ = matchingProduct a b σ + t} := by
  contrapose! hbad
  obtain ⟨c, Q, hQ⟩ := singleton_expansion_of_infinite_matching_translates _ hbad
  exact holds_of_singleton_expansion a b U hU c Q hQ

/-- For the geometric input to the arbitrary-order contact step, an infinite
exact profile image suffices. Constancy of all complex differences would
give infinitely many realizable translates of a strict counterexample. -/
theorem exists_varying_matching_difference_of_infinite_profile_image
    {M : Type*} {D : Set M} {x₀ : M} (hx₀ : x₀ ∈ D)
    (P : M → Equiv.Perm ι → ℂ)
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) (η : ℂ) (r : Equiv.Perm ι)
    (J : Finset (Equiv.Perm ι))
    (hexact : ∀ x ∈ D, ∃ a b : ι → ℂ, matchingProduct a b = P x)
    (hold : ∀ x ∈ D, ∀ σ ∉ J, P x r - P x σ = P x₀ r - P x₀ σ)
    (hsupport : ∀ σ, (η * (P x₀ r - P x₀ σ)).re ≥ 0)
    (hstrict : 0 < (matchingProfileDetGap U η r (P x₀)).re)
    (hinf : (P '' D).Infinite) :
    ∃ σ ∈ J, ∃ x ∈ D, ∃ y ∈ D, η * (P x r - P x σ) ≠ η * (P y r - P y σ) := by
  obtain ⟨a, b, hab⟩ := hexact x₀ hx₀
  have hη : η ≠ 0 := by
    rintro rfl
    simp [matchingProfileDetGap] at hstrict
  have hbad : ¬ Holds a b U := by
    intro hh
    obtain ⟨σ, hσ⟩ := (holds_iff_directional a b U).mp hh η
    have hl := hsupport σ
    rw [← hab, mul_sub, Complex.sub_re] at hl
    rw [← hab, matchingProfileDetGap_matchingProduct a b U hU, mul_sub, Complex.sub_re] at hstrict
    linarith
  by_contra! hconst
  let T : Set ℂ := {t : ℂ | ∃ a' b' : ι → ℂ,
    ∀ σ, matchingProduct a' b' σ = matchingProduct a b σ + t}
  have hfin := (finite_matching_translates_of_not_holds a b U hU hbad).image
    (fun t σ => matchingProduct a b σ + t)
  apply hinf
  apply hfin.subset
  rintro _ ⟨x, hx, rfl⟩
  have he (σ : Equiv.Perm ι) : P x r - P x σ = P x₀ r - P x₀ σ := by
    by_cases hσ : σ ∈ J
    · exact mul_left_cancel₀ hη (hconst σ hσ x hx x₀ hx₀)
    · exact hold x hx σ hσ
  let t := P x r - P x₀ r
  have ht (σ : Equiv.Perm ι) : P x σ = matchingProduct a b σ + t := by
    rw [hab]
    dsimp [t]
    linear_combination -(he σ)
  obtain ⟨a', b', hab'⟩ := hexact x hx
  exact ⟨t, ⟨a', b', fun σ => (congrFun hab' σ).trans (ht σ)⟩, (funext ht).symm⟩

/-- The arbitrary-order contact step on an infinite exact profile curve.
The geometric input must give a compactified curve through the starting
profile after fixing the old complex differences and one complex
determinant-gap value. No separate varying-difference input is needed. -/
theorem exists_strictly_violating_profile_with_more_contacts_of_infinite_image
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ, ℂ) 1 M] [CompactSpace M] [ConnectedSpace M]
    {S : Set M} (hS : S.Finite) (hconn : IsPreconnected Sᶜ)
    (P : M → Equiv.Perm ι → ℂ)
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) (η : ℂ) (r : Equiv.Perm ι)
    (J : Finset (Equiv.Perm ι))
    (hexact : ∀ x ∈ Sᶜ, ∃ a b : ι → ℂ, matchingProduct a b = P x)
    (hhol : ∀ σ ∈ J, MDifferentiableOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
      (fun x => η * (P x r - P x σ)) Sᶜ)
    {x₀ : M} (hx₀ : x₀ ∈ Sᶜ)
    (hold : ∀ x ∈ Sᶜ, ∀ σ ∉ J, P x r - P x σ = P x₀ r - P x₀ σ)
    (hold₀ : ∀ σ ∉ J, (η * (P x₀ r - P x₀ σ)).re = 0)
    (hgap : ∀ x ∈ Sᶜ, matchingProfileDetGap U η r (P x) =
      matchingProfileDetGap U η r (P x₀))
    (hstrict : 0 < (matchingProfileDetGap U η r (P x₀)).re)
    (hstart : ∀ σ ∈ J, 0 < (η * (P x₀ r - P x₀ σ)).re)
    (hinf : (P '' Sᶜ).Infinite) :
    ∃ (z : M), z ∈ Sᶜ ∧ ∃ a b : ι → ℂ, matchingProduct a b = P z ∧
      (∀ σ, 0 ≤ matchingGap a b η r σ) ∧
      (∀ σ ∉ J, matchingGap a b η r σ = 0) ∧
      (∃ σ ∈ J, matchingGap a b η r σ = 0) ∧
      ∀ σ, (η * matchingProduct a b σ).re < (η * determinantValue a b U).re := by
  have hsupport (σ : Equiv.Perm ι) : 0 ≤ (η * (P x₀ r - P x₀ σ)).re := by
    by_cases hσ : σ ∈ J
    · exact (hstart σ hσ).le
    · exact (hold₀ σ hσ).ge
  have hvar :=
    exists_varying_matching_difference_of_infinite_profile_image hx₀ P U hU η r J
      hexact hold hsupport hstrict hinf
  exact exists_strictly_violating_profile_with_more_contacts_on_curve hS hconn P U hU η r J
    hexact hhol hx₀ hold hold₀ hgap hstrict hstart hvar

end MOC
