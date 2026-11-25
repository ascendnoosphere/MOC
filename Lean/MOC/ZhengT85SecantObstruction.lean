import MOC.FourContactCertificate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FinCases
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic.FunProp

/-! Nonlinear realizability tests for the positive mixed-coefficient side of
Zheng's `T85` decomposition, DOI 10.13140/RG.2.2.36790.25923, §5.3.
The height variable here is the imaginary pivot value as used in (5.10),
which is the negative of the upper support height. The geometric secant rank
input is Zheng's Corollary C.5, also following from Howard--Millson--Snowden--Vakil
(DOI: 10.1112/plms/pds016); it is not formalized here. -/

open Matrix Filter Topology

namespace MOC
namespace ZhengT85SecantObstruction

/-- The imaginary part of (5.10), with ordinary coefficients
`a,p,r,u,q,s,v`, mixed coefficient `b`, and imaginary pivot `h`. -/
def lift (a p r u q s v b h : ℝ) : Fin 14 → ℝ :=
  ![-u-v, p+u+q+b, -b, -p, v, r+s+v+b, a-p-r-q-s-b, -r, u, -a+p+r,
    -r-v-b, -p-u-b, u+v+b, a+b+h]

def heightCoeff (a u v X Y b : ℝ) : ℝ :=
  (u-Y)*(X-v)-b*(X+Y+b)-a*(u+v)

def constantCoeff (a p r u q s v b : ℝ) : ℝ :=
  (u-(r+s)-b)*p*q+(v-(p+q)-b)*r*s-b*(p+q+b)*(r+s+b)-a*u*v

/-- Grouped coefficients of the lifted constant and height terms. -/
theorem cubic_factor (a p r u q s v b h : ℝ) :
    fourMatchingCubic (lift a p r u q s v b h) =
      constantCoeff a p r u q s v b + h * heightCoeff a u v (p+q) (r+s) b := by
  simp [fourMatchingCubic, lift, constantCoeff, heightCoeff]
  ring

/-- The pure mixed ray can satisfy the cubic, at exactly the negative of its
mixed coefficient. Thus the cubic alone does not exclude the ray. -/
theorem pure_cubic_iff {b h : ℝ} (hb : b ≠ 0) :
    fourMatchingCubic (lift 0 0 0 0 0 0 0 b h) = 0 ↔ h = -b := by
  rw [cubic_factor]
  have he : constantCoeff 0 0 0 0 0 0 0 b + h * heightCoeff 0 0 0 0 0 b =
      -b^2*(h+b) := by
    simp [constantCoeff,heightCoeff]
    ring
  simp [he, hb, add_eq_zero_iff_eq_neg]

/-- A polarized Hessian of the cubic, expressed as a symmetric trilinear form. -/
def hessForm (m y z : Fin 14 → ℝ) : ℝ :=
  fourMatchingCubic (m+y+z) - fourMatchingCubic (m+y) -
    fourMatchingCubic (m+z) - fourMatchingCubic (y+z) +
    fourMatchingCubic m + fourMatchingCubic y + fourMatchingCubic z

noncomputable def unit (i : Fin 14) : Fin 14 → ℝ := fun j => if j=i then 1 else 0

/-- The matrix of the polarized Hessian in the matching basis. -/
noncomputable def hess (m : Fin 14 → ℝ) : Matrix (Fin 14) (Fin 14) ℝ :=
  fun i j => hessForm m (unit j) (unit i)

private def pureRow (y : Fin 14 → ℝ) : Fin 14 → ℝ :=
  ![-y 13+y 3+y 7, -y 10-y 13-y 2-y 9, -y 1+y 12-y 5-y 6-y 9,
    y 0+y 11+y 12+y 7+y 8, y 7, -y 11-y 13-y 2-y 9, y 12-y 2,
    y 0+y 10+y 12+y 3+y 4, y 3, -y 1+y 12-y 2-y 5, -y 1-y 11+y 7,
    -y 10+y 3-y 5, y 2+y 3+y 6+y 7+y 9, -y 0-y 1-y 5]

set_option maxHeartbeats 600000 in
private theorem pure_hess_form (y z : Fin 14 → ℝ) :
    hessForm (lift 0 0 0 0 0 0 0 1 (-1)) y z = ∑ i, pureRow y i * z i := by
  let m := lift 0 0 0 0 0 0 0 1 (-1)
  change hessForm m y z = _
  have m0 : m 0 = 0 := by norm_num [m,lift]
  have m1 : m 1 = 1 := by norm_num [m,lift]
  have m2 : m 2 = -1 := by norm_num [m,lift]; rfl
  have m3 : m 3 = 0 := by norm_num [m,lift]; rfl
  have m4 : m 4 = 0 := by norm_num [m,lift]; rfl
  have m5 : m 5 = 1 := by norm_num [m,lift]; rfl
  have m6 : m 6 = -1 := by norm_num [m,lift]; rfl
  have m7 : m 7 = 0 := by norm_num [m,lift]; rfl
  have m8 : m 8 = 0 := by norm_num [m,lift]; rfl
  have m9 : m 9 = 0 := by norm_num [m,lift]; rfl
  have m10 : m 10 = -1 := by norm_num [m,lift]; rfl
  have m11 : m 11 = -1 := by norm_num [m,lift]; rfl
  have m12 : m 12 = 1 := by norm_num [m,lift]; rfl
  have m13 : m 13 = 0 := by norm_num [m,lift]; rfl
  simp only [hessForm, fourMatchingCubic, Pi.add_apply, m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13]
  simp only [Fin.sum_univ_succ]
  simp [pureRow]
  ring

private theorem pureRow_add (y z : Fin 14 → ℝ) : pureRow (y+z) = pureRow y + pureRow z := by
  funext i
  fin_cases i <;> simp [pureRow, Pi.add_apply] <;> ring

private theorem pureRow_smul (t : ℝ) (y : Fin 14 → ℝ) : pureRow (t • y) = t • pureRow y := by
  funext i
  fin_cases i <;> simp [pureRow] <;> ring

private theorem unit_coord (v : Fin 14 → ℝ) (i : Fin 14) :
    (∑ j, v j * unit i j) = v i := by
  classical
  simp [unit, mul_ite, Finset.sum_ite_eq']

private theorem pure_row_formula (y : Fin 14 → ℝ) :
    hess (lift 0 0 0 0 0 0 0 1 (-1)) *ᵥ y = pureRow y := by
  classical
  have hs (S : Finset (Fin 14)) :
      pureRow (∑ j ∈ S, y j • unit j) = ∑ j ∈ S, y j • pureRow (unit j) := by
    induction S using Finset.induction_on with
    | empty =>
      simp
      funext i
      fin_cases i <;> simp [pureRow]
    | @insert i S hi ih =>
      simp [Finset.sum_insert hi, pureRow_add, pureRow_smul, ih]
  have he : (∑ j, y j • unit j) = y := by
    funext i
    simp [unit, Finset.sum_apply, Finset.sum_ite_eq]
  funext i
  unfold Matrix.mulVec dotProduct hess
  simp only [pure_hess_form, unit_coord]
  calc
    (∑ j, pureRow (unit j) i * y j) =
        (∑ j, y j * pureRow (unit j) i) := by simp only [mul_comm]
    _ = pureRow (∑ j, y j • unit j) i := by
      rw [hs]
      simp [Finset.sum_apply]
    _ = pureRow y i := by rw [he]

/-- The normalized synthetic ray has an injective Hessian. The proof uses
the kernel equations, not a numerical rank or a determinant calculation. -/
private theorem pure_hess_kernel (y : Fin 14 → ℝ)
    (hy : hess (lift 0 0 0 0 0 0 0 1 (-1)) *ᵥ y = 0) : y = 0 := by
  rw [pure_row_formula] at hy
  have e (i : Fin 14) := congrFun hy i
  have e0 := e 0
  have e1 := e 1
  have e2 := e 2
  have e3 := e 3
  have e4 := e 4
  have e5 := e 5
  have e6 := e 6
  have e7 := e 7
  have e8 := e 8
  have e9 := e 9
  have e10 := e 10
  have e11 := e 11
  have e12 := e 12
  have e13 := e 13
  simp [pureRow] at e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13
  have h7 : y 7 = 0 := e4
  have h3 : y 3 = 0 := e8
  have h13 : y 13 = 0 := by linarith only [e0,h3,h7]
  have h19 : y 1 = y 2 + y 9 := by linarith only [e5,e10,h13,h7]
  have h59 : y 5 = y 2 + y 9 := by linarith only [e1,e11,h13,h3]
  have h29 : y 2 + y 9 = 0 := by linarith only [e6,e9,h19,h59]
  have h1 : y 1 = 0 := by linarith only [h19,h29]
  have h5 : y 5 = 0 := by linarith only [h59,h29]
  have h6 : y 6 = 0 := by linarith only [e12,h3,h7,h29]
  have h2 : y 2 = 0 := by linarith only [e2,e6,h1,h5,h6,h29]
  have h9 : y 9 = 0 := by linarith only [h2,h29]
  have h12 : y 12 = 0 := by linarith only [e6,h2]
  have h10 : y 10 = 0 := by linarith only [e1,h13,h2,h9]
  have h11 : y 11 = 0 := by linarith only [e5,h13,h2,h9]
  have h0 : y 0 = 0 := by linarith only [e13,h1,h5]
  have h4 : y 4 = 0 := by linarith only [e7,h0,h10,h12,h3]
  have h8 : y 8 = 0 := by linarith only [e3,h0,h11,h12,h7]
  funext i
  fin_cases i <;> simp only [Pi.zero_apply] <;>
    (first | exact h0 | exact h1 | exact h2 | exact h3 | exact h4 | exact h5 | exact h6 |
      exact h7 | exact h8 | exact h9 | exact h10 | exact h11 | exact h12 | exact h13)


theorem pure_hess_injective :
    Function.Injective (fun y => hess (lift 0 0 0 0 0 0 0 1 (-1)) *ᵥ y) := by
  intro x y h
  change hess (lift 0 0 0 0 0 0 0 1 (-1)) *ᵥ x =
    hess (lift 0 0 0 0 0 0 0 1 (-1)) *ᵥ y at h
  apply sub_eq_zero.mp
  apply pure_hess_kernel
  rw [Matrix.mulVec_sub, h, sub_self]

/-- The Hessian is nonsingular at the only cubic point on the normalized
pure mixed ray. -/
theorem pure_hess_det_ne_zero :
    (hess (lift 0 0 0 0 0 0 0 1 (-1))).det ≠ 0 := by
  rw [← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det]
  exact Matrix.mulVec_injective_iff_isUnit.mp pure_hess_injective

def normLift (α : Fin 7 → ℝ) (h : ℝ) : Fin 14 → ℝ :=
  lift (α 0) (α 1) (α 2) (α 3) (α 4) (α 5) (α 6) 1 h

private def normQ (α : Fin 7 → ℝ) : ℝ :=
  heightCoeff (α 0) (α 3) (α 6) (α 1 + α 4) (α 2 + α 5) 1

private def normC (α : Fin 7 → ℝ) : ℝ :=
  constantCoeff (α 0) (α 1) (α 2) (α 3) (α 4) (α 5) (α 6) 1

private noncomputable def rootHeight (α : Fin 7 → ℝ) : ℝ := -normC α / normQ α

private theorem normQ_zero : normQ 0 = -1 := by
  norm_num [normQ, heightCoeff]

private theorem rootHeight_zero : rootHeight 0 = -1 := by
  norm_num [rootHeight, normC, normQ_zero, constantCoeff]

noncomputable def detHess (m : Fin 14 → ℝ) := (hess m).det

private theorem continuous_det_hess : Continuous detHess := by
  unfold detHess
  apply Continuous.matrix_det
  refine continuous_pi (fun i => continuous_pi (fun j => ?_))
  unfold hess hessForm fourMatchingCubic
  simp only [Pi.add_apply]
  fun_prop

private theorem continuous_normQ : Continuous normQ := by
  unfold normQ heightCoeff
  fun_prop

private theorem continuousAt_rootHeight : ContinuousAt rootHeight 0 := by
  have hc : Continuous normC := by
    unfold normC constantCoeff
    fun_prop
  exact (hc.neg.continuousAt).div continuous_normQ.continuousAt (by norm_num [normQ_zero])

private theorem continuousAt_recovered : ContinuousAt (fun α => normLift α (rootHeight α)) 0 := by
  have hc := continuousAt_rootHeight
  have hp (i : Fin 7) : ContinuousAt (fun α : Fin 7 → ℝ => α i) 0 :=
    (continuous_apply i).continuousAt
  have h0 := hp 0
  have h1 := hp 1
  have h2 := hp 2
  have h3 := hp 3
  have h4 := hp 4
  have h5 := hp 5
  have h6 := hp 6
  rw [continuousAt_pi]
  intro i
  fin_cases i <;> simp [normLift, lift] <;>
    first
    | exact h1.neg
    | exact h2.neg
    | exact h6
    | exact h3
    | exact (h0.add continuousAt_const).add hc
    | fun_prop

private noncomputable def recovered (α : Fin 7 → ℝ) : Fin 14 → ℝ :=
  normLift α (rootHeight α)

private noncomputable def normDet : (Fin 7 → ℝ) → ℝ := detHess ∘ recovered

/-- In a neighborhood of the pure mixed coefficients, no real lift with
mixed coefficient one belongs to the simultaneous cubic/Hessian locus.
In particular the neighborhood is uniform over the support height. -/
theorem excludes_neighborhood :
    ∀ᶠ α : Fin 7 → ℝ in 𝓝 (0 : Fin 7 → ℝ), ∀ h : ℝ,
      fourMatchingCubic (normLift α h) = 0 → detHess (normLift α h) ≠ 0 := by
  have hQ : ∀ᶠ α in 𝓝 (0 : Fin 7 → ℝ), normQ α ≠ 0 :=
    continuous_normQ.continuousAt.eventually_ne (by norm_num [normQ_zero])
  have hf : ContinuousAt recovered 0 := continuousAt_recovered
  have hg : ContinuousAt detHess (recovered 0) := continuous_det_hess.continuousAt
  have hc : ContinuousAt normDet 0 := hg.comp hf
  have hn0 : normDet 0 ≠ 0 := by
    have he : recovered 0 = lift 0 0 0 0 0 0 0 1 (-1) := by
      unfold recovered
      rw [rootHeight_zero]
      rfl
    change detHess (recovered 0) ≠ 0
    rw [he]
    exact pure_hess_det_ne_zero
  have hd : ∀ᶠ α in 𝓝 (0 : Fin 7 → ℝ), normDet α ≠ 0 := hc.eventually_ne hn0
  filter_upwards [hQ,hd] with α hQ hd h hC
  have hn : normC α + h * normQ α = 0 := by
    simpa [normLift,normC,normQ,cubic_factor] using hC
  have hh : h = rootHeight α := (eq_div_iff hQ).2 (by linarith)
  rw [hh]
  simpa only [normDet, Function.comp_apply, recovered] using hd

end ZhengT85SecantObstruction
end MOC
