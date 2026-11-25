import MOC.SmallSpectralPerturbation
import MOC.PolynomialRealQuotient
import MOC.AssignmentSphere
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Tactic.LinearCombination

/-! Moving the pole of a fractional linear map gives generic assignment
sums for any two prescribed simple spectral lists. -/

open Finset Polynomial
open scoped BigOperators ComplexConjugate Topology

namespace MOC
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private def poleNumerator (x b : ι → ℂ) (p : Equiv.Perm ι) : ℂ[X] :=
  ∑ j, C (x (p j)) * ∏ k ∈ univ.erase j, (X - C (b k))

private theorem poleNumerator_at_pole (x b : ι → ℂ)
    (p : Equiv.Perm ι) (j : ι) :
    (poleNumerator x b p).eval (b j) = x (p j) * ∏ k ∈ univ.erase j, (b j - b k) := by
  simp only [poleNumerator, eval_finset_sum, eval_mul, eval_C, eval_prod, eval_sub, eval_X]
  apply sum_eq_single j
  · intro k _ hkj
    have hj : j ∈ univ.erase k := mem_erase.mpr ⟨Ne.symm hkj, mem_univ _⟩
    rw [prod_eq_zero hj (sub_self _), mul_zero]
  · simp

private theorem pole_difference_ne (x b : ι → ℂ) (hx : Function.Injective x)
    (hb : Function.Injective b) {p q : Equiv.Perm ι} (hpq : p ≠ q) :
    poleNumerator x b p - poleNumerator x b q ≠ 0 := by
  intro he
  apply hpq
  ext j
  apply hx
  have h := congrArg (fun P : ℂ[X] => P.eval (b j)) (sub_eq_zero.mp he)
  simp only [poleNumerator_at_pole x b] at h
  have hn : (∏ k ∈ univ.erase j, (b j - b k)) ≠ 0 := by
    exact prod_ne_zero_iff.mpr fun k hk => sub_ne_zero.mpr (hb.ne (mem_erase.mp hk).1.symm)
  exact mul_right_cancel₀ hn h

private theorem poleNumerator_eq (x b : ι → ℂ) (p : Equiv.Perm ι) (z : ℂ)
    (hz : ∀ j, z ≠ b j) :
    (poleNumerator x b p).eval z =
      reciprocalAssignmentSum x (fun j => (z - b j)⁻¹) p * ∏ k, (z - b k) := by
  simp only [poleNumerator, eval_finset_sum, eval_mul, eval_C, eval_prod, eval_sub, eval_X,
    reciprocalAssignmentSum, sum_mul]
  apply sum_congr rfl
  intro j _
  rw [← mul_prod_erase univ (fun k => z - b k) (mem_univ j)]
  field_simp [sub_ne_zero.mpr (hz j)]
  ring

private theorem polynomial_nonzero_dense (P : ℂ[X]) (hP : P ≠ 0) :
    Dense {z : ℂ | P.eval z ≠ 0} := by
  rw [dense_iff_inter_open]
  intro S hS hne
  by_contra h
  obtain ⟨z, hz⟩ := hne
  apply hP
  apply P.eq_zero_of_infinite_isRoot
  apply (infinite_of_mem_nhds z (hS.mem_nhds hz)).mono
  intro w hw
  by_contra hc
  exact h ⟨w, hw, hc⟩

private theorem all_open_dense {κ : Type*} [Finite κ] (F : κ → Set ℂ)
    (ho : ∀ k, IsOpen (F k)) (hd : ∀ k, Dense (F k)) :
    IsOpen {z : ℂ | ∀ k, z ∈ F k} ∧ Dense {z : ℂ | ∀ k, z ∈ F k} := by
  rw [Set.setOf_forall]
  exact ⟨isOpen_iInter_of_finite ho, dense_iInter_of_isOpen ho hd⟩

private theorem collinear_projection (u v η : ℂ) (hη : η ≠ 0)
    (hu : (η * u).re = 0) (hv : (η * v).re = 0) : (u * conj v).im = 0 := by
  simp only [Complex.mul_re] at hu hv
  simp only [Complex.mul_im, Complex.conj_im, Complex.conj_re]
  by_cases hr : η.re = 0
  · have hi : η.im ≠ 0 := fun h => hη (Complex.ext hr h)
    apply (mul_eq_zero.mp (show η.im * (u.re * -v.im + u.im * v.re) = 0 by
      linear_combination v.re * (-hu) + u.re * hv)).resolve_left hi
  · apply (mul_eq_zero.mp (show η.re * (u.re * -v.im + u.im * v.re) = 0 by
      linear_combination -v.im * hu + u.im * hv)).resolve_left hr


private theorem pole_triple_dense (x b : ι → ℂ) (hx : Function.Injective x)
    (hb : Function.Injective b) (p q r : Equiv.Perm ι)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    let P := poleNumerator x b p - poleNumerator x b q
    let Q := poleNumerator x b p - poleNumerator x b r
    Dense {z : ℂ | (P.eval z * conj (Q.eval z)).im ≠ 0} := by
  intro P Q
  rw [dense_iff_inter_open]
  intro S hS hne
  by_contra h
  have hr : ∀ z ∈ S, (P.eval z * conj (Q.eval z)).im = 0 := by
    intro z hz
    by_contra hh
    exact h ⟨z, hz, hh⟩
  obtain ⟨c, hc⟩ := polynomial_eq_real_mul_of_im_mul_conj_eq_zero hS hne
    (pole_difference_ne x b hx hb hpr) hr
  apply perm_sub_not_real_multiple x hx p q r hpq hpr hqr c
  intro j
  let d := ∏ k ∈ univ.erase j, (b j - b k)
  have hd : d ≠ 0 :=
    prod_ne_zero_iff.mpr fun k hk => sub_ne_zero.mpr (hb.ne (mem_erase.mp hk).1.symm)
  have he := congrArg (fun f : ℂ[X] => f.eval (b j)) hc
  simp only [P, Q, eval_mul, eval_C, eval_sub, poleNumerator_at_pole] at he
  apply mul_right_cancel₀ hd
  dsimp only [d]
  linear_combination he

private abbrev DistinctPair (κ : Type*) := {p : κ × κ // p.1 ≠ p.2}
private abbrev DistinctTriple (κ : Type*) :=
  {p : κ × κ × κ // p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2 ∧ p.2.1 ≠ p.2.2}

/-- In every order, the permitted poles contain a dense open set. Each
permitted pole gives distinct assignment sums with no three collinear. -/
theorem denseOpen_reciprocal_assignment_poles (x b : ι → ℂ) (hx : Function.Injective x)
    (hb : Function.Injective b) :
    ∃ S : Set ℂ, IsOpen S ∧ Dense S ∧ ∀ z ∈ S,
      (∀ j, z ≠ b j) ∧ ReciprocalAssignmentsInGeneralPosition x (fun j => (z - b j)⁻¹) := by
  classical
  let N := poleNumerator x b
  let F (j : ι) : Set ℂ := {z | z ≠ b j}
  let G (k : DistinctPair (Equiv.Perm ι)) : Set ℂ :=
    {z | ((N k.val.1 - N k.val.2).eval z) ≠ 0}
  let T (k : DistinctTriple (Equiv.Perm ι)) : Set ℂ :=
    {z | (((N k.val.1 - N k.val.2.1).eval z) *
      conj ((N k.val.1 - N k.val.2.2).eval z)).im ≠ 0}
  obtain ⟨hoF, hdF⟩ := all_open_dense F
    (fun j => isOpen_ne_fun continuous_id continuous_const) (fun j => dense_compl_singleton (b j))
  obtain ⟨hoG, hdG⟩ := all_open_dense G
    (fun k => isOpen_ne_fun (N k.val.1 - N k.val.2).continuous continuous_const)
    (fun k => polynomial_nonzero_dense _ (pole_difference_ne x b hx hb k.property))
  have ho (k : DistinctTriple (Equiv.Perm ι)) : IsOpen (T k) := by
    apply isOpen_ne_fun _ continuous_const
    exact Complex.continuous_im.comp ((N k.val.1 - N k.val.2.1).continuous.mul
      (Complex.continuous_conj.comp (N k.val.1 - N k.val.2.2).continuous))
  obtain ⟨hoT, hdT⟩ := all_open_dense T ho
    (fun k => pole_triple_dense x b hx hb _ _ _ k.property.1 k.property.2.1 k.property.2.2)
  refine ⟨_, (hoF.inter hoG).inter hoT,
    (hdF.inter_of_isOpen_right hdG hoG).inter_of_isOpen_right hdT hoT, ?_⟩
  intro z hz
  obtain ⟨⟨hzF, hzG⟩, hzT⟩ := hz
  let d := ∏ j, (z - b j)
  have hd : d ≠ 0 := prod_ne_zero_iff.mpr fun j _ => sub_ne_zero.mpr (hzF j)
  let A := reciprocalAssignmentSum x (fun j => (z - b j)⁻¹)
  have hN (p : Equiv.Perm ι) : (N p).eval z = A p * d := poleNumerator_eq x b p z hzF
  refine ⟨hzF, ?_, ?_⟩
  · intro p q he
    by_contra hpq
    have hh := hzG ⟨(p,q), hpq⟩
    change ((N p - N q).eval z) ≠ 0 at hh
    apply hh
    rw [eval_sub, hN, hN, show A p = A q from he, sub_self]
  · intro η hη p q r hpq hpr hqr hp hq
    have hh := hzT ⟨(p,q,r), hpq, hpr, hqr⟩
    change (((N p - N q).eval z) * conj ((N p - N r).eval z)).im ≠ 0 at hh
    apply hh
    apply collinear_projection _ _ (η / d) (div_ne_zero hη hd)
    all_goals rw [eval_sub, hN, hN, ← sub_mul, div_mul_comm, mul_div_cancel_right₀ _ hd,
      mul_comm _ η, mul_sub, Complex.sub_re, sub_eq_zero]
    · exact hp
    · exact hq

/-- Fix two arbitrary simple spectral lists. A dense open set of poles
gives a positive radius for the second list. Every unitary mixer works
throughout the disk. For nonzero scale, the second list is a fractional
linear image of its prescribed values. -/
theorem holds_small_fractional_linear_spectrum (a b : ι → ℂ)
    (ha : Function.Injective a) (ha₀ : ∀ i, a i ≠ 0) (hb : Function.Injective b) :
    ∃ S : Set ℂ, IsOpen S ∧ Dense S ∧ ∀ z ∈ S, (∀ j, z ≠ b j) ∧
      ∃ r : ℝ, 0 < r ∧ ∀ t : ℂ, ‖t‖ < r → ∀ U : Matrix ι ι ℂ, IsUnitary U →
        Holds a (fun j => t / (z - b j)) U := by
  obtain ⟨S, ho, hd, h⟩ := denseOpen_reciprocal_assignment_poles
    (fun i => (a i)⁻¹) b (inv_injective.comp ha) hb
  refine ⟨S, ho, hd, ?_⟩
  intro z hz
  obtain ⟨hn, hg⟩ := h z hz
  refine ⟨hn, ?_⟩
  simpa only [div_eq_mul_inv] using
    holds_small_spectral_parameter a (fun j => (z - b j)⁻¹) ha₀ hg


/-- Either spectral list may contain zero. Each center that avoids the
negatives of the first list admits a dense open set of suitable poles. -/
theorem holds_small_shifted_fractional_linear_spectrum (a b : ι → ℂ)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (c : ℂ) (hc : ∀ i, a i + c ≠ 0) :
    ∃ S : Set ℂ, IsOpen S ∧ Dense S ∧ ∀ z ∈ S, (∀ j, z ≠ b j) ∧
      ∃ r : ℝ, 0 < r ∧ ∀ t : ℂ, ‖t‖ < r → ∀ U : Matrix ι ι ℂ, IsUnitary U →
        Holds a (fun j => c + t / (z - b j)) U := by
  have hinj : Function.Injective (fun i => a i + c) :=
    fun _ _ h => ha (add_right_cancel h)
  obtain ⟨S, ho, hd, h⟩ := holds_small_fractional_linear_spectrum
    (fun i => a i + c) b hinj hc hb
  refine ⟨S, ho, hd, ?_⟩
  intro z hz
  obtain ⟨hn, r, hr, ht⟩ := h z hz
  refine ⟨hn, r, hr, ?_⟩
  intro t htr U hU
  apply (holds_shift_iff a (fun j => c + t / (z - b j)) hU c).mp
  simpa only [add_sub_cancel_left] using ht t htr U hU


omit [DecidableEq ι] in
private theorem reciprocalAssignmentSum_swap (x y : ι → ℂ) (p : Equiv.Perm ι) :
    reciprocalAssignmentSum x y p = reciprocalAssignmentSum y x p.symm := by
  unfold reciprocalAssignmentSum
  rw [← Equiv.sum_comp p (fun k => y (p.symm k) * x k)]
  simp only [Equiv.symm_apply_apply, mul_comm]

omit [DecidableEq ι] in
private theorem reciprocalAssignments_general_swap (x y : ι → ℂ)
    (h : ReciprocalAssignmentsInGeneralPosition x y) : ReciprocalAssignmentsInGeneralPosition y x := by
  obtain ⟨hinj, hdir⟩ := h
  constructor
  · intro p q he
    simp only [reciprocalAssignmentSum_swap y x] at he
    exact Equiv.symm_bijective.injective (hinj he)
  · intro η hη p q r hpq hpr hqr hp
    simp only [reciprocalAssignmentSum_swap y x] at hp ⊢
    exact hdir η hη p.symm q.symm r.symm
      (Equiv.symm_bijective.injective.ne hpq) (Equiv.symm_bijective.injective.ne hpr)
      (Equiv.symm_bijective.injective.ne hqr) hp

/-- For any two simple spectral lists, keep the first list fixed. A
dense open set of centers admits a disk of complex scales on which the
translated and scaled second list works for every unitary mixer. -/
theorem holds_small_affine_spectrum (a b : ι → ℂ)
    (ha : Function.Injective a) (hb : Function.Injective b) :
    ∃ S : Set ℂ, IsOpen S ∧ Dense S ∧ ∀ z ∈ S, (∀ j, a j + z ≠ 0) ∧
      ∃ r : ℝ, 0 < r ∧ ∀ t : ℂ, ‖t‖ < r → ∀ U : Matrix ι ι ℂ, IsUnitary U →
        Holds a (fun j => z + t * b j) U := by
  have hneg : Function.Injective (fun i => -a i) := neg_injective.comp ha
  obtain ⟨S, ho, hd, h⟩ := denseOpen_reciprocal_assignment_poles b (fun i => -a i) hb hneg
  refine ⟨S, ho, hd, ?_⟩
  intro z hz
  obtain ⟨hn, hg⟩ := h z hz
  have hreg (j : ι) : a j + z ≠ 0 := by
    intro he
    apply hn j
    linear_combination he
  have hgen : ReciprocalAssignmentsInGeneralPosition (fun i => (a i + z)⁻¹) b := by
    simpa only [sub_neg_eq_add, add_comm z] using reciprocalAssignments_general_swap _ _ hg
  obtain ⟨r, hr, ht⟩ := holds_small_spectral_parameter (fun i => a i + z) b hreg hgen
  refine ⟨hreg, r, hr, ?_⟩
  intro t htr U hU
  apply (holds_shift_iff a (fun j => z + t * b j) hU z).mp
  simpa only [add_sub_cancel_left] using ht t htr U hU

end
end MOC
