import MOC.ReciprocalSpectralPerturbation
import MOC.UniformExteriorShift
import MOC.AssignmentOrientation
import MOC.PolynomialLineDensity

/-! For each fixed simple spectrum, an open dense set of partner lists
admits a uniform exterior radius for all unitary mixers. -/

open Finset Polynomial
open scoped BigOperators Topology ComplexConjugate

namespace MOC

noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private def orientation (u v : ℂ) : ℝ := (u * conj v).im

private theorem orientation_expand (u v d e : ℂ) (t : ℝ) :
    orientation (u + (t : ℂ) * d) (v + (t : ℂ) * e) =
      orientation u v + (orientation d v + orientation u e) * t +
        orientation d e * t ^ 2 := by
  simp only [orientation, map_add, map_mul, Complex.conj_ofReal, Complex.mul_im, Complex.mul_re,
    Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

private theorem orientation_self_I (u : ℂ) (hu : u ≠ 0) :
    orientation u (Complex.I * u) ≠ 0 := by
  have he : orientation u (Complex.I * u) = -Complex.normSq u := by
    simp [orientation, Complex.mul_im, Complex.mul_re, Complex.normSq_apply]
  rw [he]
  exact neg_ne_zero.mpr (Complex.normSq_eq_zero.not.mpr hu)

omit [Fintype ι] [DecidableEq ι] in
private theorem dense_orientation_along (v : ι → ℂ) (F G : (ι → ℂ) → ℂ)
    (hF : ∀ b t, F (fun j => b j + (t : ℂ) * v j) = F b + (t : ℂ) * F v)
    (hG : ∀ b t, G (fun j => b j + (t : ℂ) * v j) = G b + (t : ℂ) * G v)
    (hv : orientation (F v) (G v) ≠ 0) : Dense {b | orientation (F b) (G b) ≠ 0} := by
  rw [dense_iff_inter_open]
  intro S hS hne
  obtain ⟨b, hb⟩ := hne
  let Q : ℝ[X] := C (orientation (F b) (G b)) +
    C (orientation (F v) (G b) + orientation (F b) (G v)) * X +
    C (orientation (F v) (G v)) * X ^ 2
  have hQ : Q ≠ 0 := by
    intro he
    apply hv
    have hh := congrArg (fun P : ℝ[X] => P.coeff 2) he
    simpa [Q, coeff_add, coeff_C_mul, coeff_X, coeff_X_pow] using hh
  obtain ⟨t, ht, hval⟩ := exists_polynomial_nonroot_on_line S hS b v hb Q hQ
  refine ⟨_, ht, ?_⟩
  change orientation (F _) (G _) ≠ 0
  rw [hF, hG, orientation_expand]
  simpa only [Q, eval_add, eval_mul, eval_C, eval_X, eval_pow] using hval

private def assignmentDiff (a : ι → ℂ) (p q : Equiv.Perm ι) (b : ι → ℂ) : ℂ :=
  reciprocalAssignmentSum a b p - reciprocalAssignmentSum a b q

omit [DecidableEq ι] in
private theorem assignmentDiff_add (a b v : ι → ℂ) (p q : Equiv.Perm ι) (t : ℂ) :
    assignmentDiff a p q (fun j => b j + t * v j) =
      assignmentDiff a p q b + t * assignmentDiff a p q v := by
  have h (π : Equiv.Perm ι) :
      reciprocalAssignmentSum a (fun j => b j + t * v j) π =
      reciprocalAssignmentSum a b π + t * reciprocalAssignmentSum a v π := by
    simp only [reciprocalAssignmentSum, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [assignmentDiff, h, h]
  unfold assignmentDiff
  ring

omit [DecidableEq ι] in
private theorem assignmentDiff_continuous (a : ι → ℂ) (p q : Equiv.Perm ι) :
    Continuous (assignmentDiff a p q) := by
  unfold assignmentDiff reciprocalAssignmentSum
  fun_prop

omit [DecidableEq ι] in
private theorem generic_orientation {a b : ι → ℂ} (h : ReciprocalAssignmentsInGeneralPosition a b)
    (p q r : Equiv.Perm ι) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    orientation (assignmentDiff a p q b) (assignmentDiff a p r b) ≠ 0 :=
  (no_three_tied_projections_iff_orientation h.1).mp h.2 p q r hpq hpr hqr

omit [DecidableEq ι] in
private theorem all_open_dense_assignments {κ : Type*} [Finite κ] (F : κ → Set (ι → ℂ))
    (ho : ∀ k, IsOpen (F k)) (hd : ∀ k, Dense (F k)) :
    IsOpen {b : ι → ℂ | ∀ k, b ∈ F k} ∧ Dense {b : ι → ℂ | ∀ k, b ∈ F k} := by
  rw [Set.setOf_forall]
  exact ⟨isOpen_iInter_of_finite ho, dense_iInter_of_isOpen ho hd⟩

/-- For every fixed simple list, the partner lists with distinct assignment
values and no collinear triple form an open dense set. -/
theorem isOpen_dense_assignment_generalPosition (a : ι → ℂ) (ha : Function.Injective a) :
    IsOpen {b | ReciprocalAssignmentsInGeneralPosition a b} ∧
      Dense {b | ReciprocalAssignmentsInGeneralPosition a b} := by
  classical
  obtain ⟨_, _, hd, hz⟩ := denseOpen_reciprocal_assignment_poles a a ha ha
  obtain ⟨z, hzs⟩ := hd.nonempty
  let v (j : ι) := (z - a j)⁻¹
  have hv : ReciprocalAssignmentsInGeneralPosition a v := (hz z hzs).2
  let Pair := {k : Equiv.Perm ι × Equiv.Perm ι // k.1 ≠ k.2}
  let Triple := {k : Equiv.Perm ι × Equiv.Perm ι × Equiv.Perm ι //
    k.1 ≠ k.2.1 ∧ k.1 ≠ k.2.2 ∧ k.2.1 ≠ k.2.2}
  let F (k : Pair) : Set (ι → ℂ) := {b | assignmentDiff a k.val.1 k.val.2 b ≠ 0}
  let G (k : Triple) : Set (ι → ℂ) := {b |
    orientation (assignmentDiff a k.val.1 k.val.2.1 b) (assignmentDiff a k.val.1 k.val.2.2 b) ≠ 0}
  have hf (k : Pair) : Dense (F k) := by
    let f := assignmentDiff a k.val.1 k.val.2
    have hh (b : ι → ℂ) (t : ℂ) := assignmentDiff_add a b v k.val.1 k.val.2 t
    have hh' (b : ι → ℂ) (t : ℂ) :
        Complex.I * f (fun j => b j + t * v j) = Complex.I * f b + t * (Complex.I * f v) := by
      change Complex.I * assignmentDiff _ _ _ _ = _
      rw [hh]
      dsimp only [f]
      ring
    have hden := dense_orientation_along v f (fun b => Complex.I * f b) hh hh'
      (orientation_self_I _ (sub_ne_zero.mpr (hv.1.ne k.property)))
    apply hden.mono
    intro b hbf he
    change orientation (f b) (Complex.I * f b) ≠ 0 at hbf
    change f b = 0 at he
    exact hbf (by rw [he]; simp [orientation])
  have hg (k : Triple) : Dense (G k) :=
    dense_orientation_along v _ _ (fun b t => assignmentDiff_add a b v _ _ t)
      (fun b t => assignmentDiff_add a b v _ _ t)
      (generic_orientation hv _ _ _ k.property.1 k.property.2.1 k.property.2.2)
  obtain ⟨hoF, hdF⟩ := all_open_dense_assignments F
    (fun _ => isOpen_ne_fun (assignmentDiff_continuous _ _ _) continuous_const) hf
  have hgo (k : Triple) : IsOpen (G k) :=
    isOpen_ne_fun (Complex.continuous_im.comp ((assignmentDiff_continuous _ _ _).mul
      (Complex.continuous_conj.comp (assignmentDiff_continuous _ _ _)))) continuous_const
  obtain ⟨hoG, hdG⟩ := all_open_dense_assignments G hgo hg
  have heq : {b | ReciprocalAssignmentsInGeneralPosition a b} =
      {b | ∀ k, b ∈ F k} ∩ {b | ∀ k, b ∈ G k} := by
    ext b
    constructor
    · intro hb
      refine ⟨fun k => sub_ne_zero.mpr (hb.1.ne k.property), ?_⟩
      exact fun k => generic_orientation hb _ _ _ k.property.1 k.property.2.1 k.property.2.2
    · rintro ⟨h1, h2⟩
      have hinj : Function.Injective (reciprocalAssignmentSum a b) := fun {p q} hp => by
        by_contra hneq
        exact h1 ⟨(p,q),hneq⟩ (sub_eq_zero.mpr hp)
      exact ⟨hinj, (no_three_tied_projections_iff_orientation hinj).mpr
        fun p q r hpq hpr hqr => h2 ⟨(p,q,r),hpq,hpr,hqr⟩⟩
  rw [heq]
  exact ⟨hoF.inter hoG, hdF.inter_of_isOpen_right hdG hoG⟩

/-- For each simple first spectrum, an open dense set of partner spectra
has one exterior radius for all complex shifts and all unitary mixers. -/
theorem generic_partners_uniform_exterior_shift (a : ι → ℂ) (ha : Function.Injective a) :
    ∃ S : Set (ι → ℂ), IsOpen S ∧ Dense S ∧ ∀ b ∈ S, ∃ R : ℝ, 0 < R ∧
      ∀ z : ℂ, R < ‖z‖ → ∀ U : Matrix ι ι ℂ, IsUnitary U →
        Holds (fun i => a i + z) b U := by
  obtain ⟨ho, hd⟩ := isOpen_dense_assignment_generalPosition a ha
  exact ⟨_, ho, hd, fun b hb => holds_uniform_exterior_shift a b hb⟩

end
end MOC
