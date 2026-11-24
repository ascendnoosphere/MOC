import MOC.ContactCurveGeometry
import MOC.GeneralContactReduction
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.Eval

/-! The normalized anchored rank-one profile is a polynomial chart
with one scale coordinate and no redundant factor coordinate. -/

open Finset BigOperators MvPolynomial

namespace MOC.PolynomialContactChart

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev Rows (o i₀ : ι) := {i : ι // i ≠ o ∧ i ≠ i₀}
abbrev Cols (o : ι) := {j : ι // j ≠ o}
abbrev Var (o i₀ : ι) := Unit ⊕ (Rows o i₀ ⊕ Cols o)
abbrev Poly (o i₀ : ι) := MvPolynomial (Var o i₀) ℂ
abbrev Point (o i₀ : ι) := Var o i₀ → ℂ

/-- One scale, n−2 free rows, and n−1 free columns. -/
theorem card_var {o i₀ : ι} (h : i₀ ≠ o) :
    Fintype.card (Var o i₀) = 2 * Fintype.card ι - 2 := by
  have hmem : i₀ ∈ (univ : Finset ι).erase o := mem_erase.mpr ⟨h, mem_univ _⟩
  have hr : Fintype.card (Rows o i₀) = Fintype.card ι - 1 - 1 := by
    rw [Fintype.card_of_subtype ((univ.erase o).erase i₀) (by
      intro i
      simp only [mem_erase, mem_univ, and_true]
      exact and_comm), card_erase_of_mem hmem, card_erase_of_mem (mem_univ _), card_univ]
  have hc : Fintype.card (Cols o) = Fintype.card ι - 1 := by
    rw [Fintype.card_of_subtype (univ.erase o) (by simp), card_erase_of_mem (mem_univ _), card_univ]
  have hn : 2 ≤ Fintype.card ι := (Finset.card_le_univ ({i₀,o} : Finset ι)).trans' (by simp [h])
  change Fintype.card (Unit ⊕ (Rows o i₀ ⊕ Cols o)) = _
  rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_unit, hr, hc]
  omega

def scale (o i₀ : ι) : Poly o i₀ := X (.inl ())

def row (o i₀ i : ι) : Poly o i₀ :=
  if hi : i=o then 0 else if hp : i=i₀ then 1 else X (.inr (.inl ⟨i, hi, hp⟩))

def col (o i₀ j : ι) : Poly o i₀ :=
  if hj : j=o then 0 else X (.inr (.inr ⟨j, hj⟩))

def kernel (o i₀ i j : ι) : Poly o i₀ := 1 + row o i₀ i * col o i₀ j

/-- Every matching coordinate is a polynomial in the chart variables. -/
def profilePolynomial (o i₀ : ι) (σ : Equiv.Perm ι) : Poly o i₀ :=
  scale o i₀ * ∏ j, kernel o i₀ (σ j) j

def profile (o i₀ : ι) (x : Point o i₀) (σ : Equiv.Perm ι) : ℂ :=
  eval x (profilePolynomial o i₀ σ)

def rowAt (o i₀ : ι) (x : Point o i₀) (i : ι) : ℂ := eval x (row o i₀ i)
def colAt (o i₀ : ι) (x : Point o i₀) (j : ι) : ℂ := eval x (col o i₀ j)

theorem profile_evaluation (o i₀ : ι) (x : Point o i₀) (σ : Equiv.Perm ι) :
    profile o i₀ x σ = x (.inl ()) *
      ∏ j, (1 + rowAt o i₀ x (σ j) * colAt o i₀ x j) := by
  simp [profile, profilePolynomial, scale, kernel, rowAt, colAt]

omit [Fintype ι] in
@[simp] theorem rowAt_anchor (o i₀ : ι) (x : Point o i₀) : rowAt o i₀ x o = 0 := by
  simp [rowAt, row]

omit [Fintype ι] in
@[simp] theorem colAt_anchor (o i₀ : ι) (x : Point o i₀) : colAt o i₀ x o = 0 := by
  simp [colAt, col]

omit [Fintype ι] in
theorem rowAt_pivot {o i₀ : ι} (h : i₀ ≠ o) (x : Point o i₀) :
    rowAt o i₀ x i₀ = 1 := by simp [rowAt, row, h]

/-- Coefficients of one factor, the other factor, and the common scale
are jointly recovered on the nonvanishing chart. -/
theorem profile_injective_on_nonzero {o i₀ j₀ : ι} (hi : i₀ ≠ o) {x y : Point o i₀}
    (hcol : colAt o i₀ x j₀ ≠ 0) (hnz : ∀ σ, profile o i₀ x σ ≠ 0)
    (hxy : profile o i₀ x = profile o i₀ y) : x = y := by
  obtain ⟨hd, hu, hv⟩ := pivot_normalized_matching_profile_chart_injective o i₀ j₀
    (x (.inl ())) (y (.inl ())) (rowAt o i₀ x) (colAt o i₀ x) (rowAt o i₀ y) (colAt o i₀ y)
    (rowAt_anchor _ _ _) (colAt_anchor _ _ _) (rowAt_anchor _ _ _) (colAt_anchor _ _ _)
    (rowAt_pivot hi x) (rowAt_pivot hi y) hcol _ (profile_evaluation _ _ _)
    (fun σ => (congrFun hxy σ).trans (profile_evaluation _ _ _ _)) hnz
  funext k
  rcases k with (_|k)
  · exact hd
  rcases k with (i|j)
  · simpa [rowAt, row, i.property.1, i.property.2] using congrFun hu i.val
  · simpa [colAt, col, j.property] using congrFun hv j.val

def encode (o i₀ : ι) (d : ℂ) (u v : ι → ℂ) : Point o i₀
  | .inl _ => d
  | .inr (.inl i) => u i.val
  | .inr (.inr j) => v j.val

/-- A normalized factorization is represented by the polynomial chart
with no loss in any matching coordinate. -/
theorem profile_encode {o i₀ : ι} (d : ℂ) (u v : ι → ℂ)
    (hu : u o=0) (hv : v o=0) (hp : u i₀=1) (σ : Equiv.Perm ι) :
    profile o i₀ (encode o i₀ d u v) σ = d * ∏ j, (1 + u (σ j) * v j) := by
  have hr (i : ι) : rowAt o i₀ (encode o i₀ d u v) i = u i := by
    by_cases hi : i=o
    · subst i
      simp [hu]
    by_cases hj : i=i₀
    · subst i
      simp [rowAt, row, hi, hp]
    simp [rowAt, row, hi, hj, encode]
  have hc (j : ι) : colAt o i₀ (encode o i₀ d u v) j = v j := by
    by_cases hj : j=o
    · subst j
      simp [hv]
    simp [colAt, col, hj, encode]
  simp [profile_evaluation, encode, hr, hc]

/-- A supplied rank-one profile whose chosen residual pivot is nonzero
can always be entered in this normalized chart. -/
theorem exists_normalized_point {o i₀ j₀ : ι} (d : ℂ) (u v : ι → ℂ)
    (hu : u o=0) (hv : v o=0) (h : u i₀ * v j₀ ≠ 0) :
    ∃ x : Point o i₀, colAt o i₀ x j₀ ≠ 0 ∧
      ∀ σ, profile o i₀ x σ = d * ∏ j, (1+u (σ j)*v j) := by
  have h0 : u i₀ ≠ 0 := left_ne_zero_of_mul h
  have hj : j₀ ≠ o := by
    intro he
    subst j₀
    exact h (by rw [hv, mul_zero])
  let uu := fun i => u i / u i₀
  let vv := fun j => u i₀ * v j
  have hu' : uu o = 0 := by simp [uu, hu]
  have hv' : vv o = 0 := by simp [vv, hv]
  have hp : uu i₀ = 1 := div_self h0
  refine ⟨encode o i₀ d uu vv, ?_, ?_⟩
  · simpa [colAt, col, hj, encode, vv] using h
  · intro σ
    rw [profile_encode d uu vv hu' hv' hp]
    congr 1
    apply prod_congr rfl
    intro j _
    dsimp [uu, vv]
    field_simp
    ring


/-- The fixed-mixer complex determinant gap is polynomial in the chart
variables. Its evaluation is the exact gap from contact transfer. -/
def gapPolynomial (o i₀ : ι) (U : Matrix ι ι ℂ) (η : ℂ) (r : Equiv.Perm ι) : Poly o i₀ :=
  ∑ σ, C (realSignedWeight U σ : ℂ) *
    (C η * (profilePolynomial o i₀ σ - profilePolynomial o i₀ r))

theorem gapPolynomial_evaluation (o i₀ : ι) (x : Point o i₀)
    (U : Matrix ι ι ℂ) (η : ℂ) (r : Equiv.Perm ι) :
    eval x (gapPolynomial o i₀ U η r) = matchingProfileDetGap U η r (profile o i₀ x) := by
  simp [gapPolynomial, matchingProfileDetGap, profile]

/-- One localizer suffices for all nonzero chart requirements. It uses
the entries of the anchored kernel, rather than multiplying the
factorially many matching polynomials. -/
def localizer (o i₀ j₀ : ι) : Poly o i₀ :=
  scale o i₀ * col o i₀ j₀ * ∏ i, ∏ j, kernel o i₀ i j

/-- Localizing the explicit entry product is exactly the open chart
of the normalized column pivot and all nonzero matching coordinates. -/
theorem eval_localizer_ne_zero_iff (o i₀ j₀ : ι) (x : Point o i₀) :
    eval x (localizer o i₀ j₀) ≠ 0 ↔
      colAt o i₀ x j₀ ≠ 0 ∧ ∀ σ, profile o i₀ x σ ≠ 0 := by
  classical
  have he : eval x (localizer o i₀ j₀) =
      x (.inl ()) * colAt o i₀ x j₀ *
        ∏ i, ∏ j, (1 + rowAt o i₀ x i * colAt o i₀ x j) := by
    simp [localizer, scale, kernel, rowAt, colAt]
  rw [he]
  simp only [mul_ne_zero_iff, Finset.prod_ne_zero_iff, Finset.mem_univ, forall_const]
  constructor
  · rintro ⟨⟨hd, hv⟩, hk⟩
    refine ⟨hv, fun σ => ?_⟩
    rw [profile_evaluation]
    exact mul_ne_zero hd (Finset.prod_ne_zero_iff.mpr fun j _ => hk (σ j) j)
  · rintro ⟨hv, hp⟩
    have hd : x (.inl ()) ≠ 0 := by
      have h := hp 1
      rw [profile_evaluation] at h
      exact left_ne_zero_of_mul h
    refine ⟨⟨hd, hv⟩, fun i j => ?_⟩
    have h := hp (Equiv.swap j i)
    rw [profile_evaluation] at h
    have hj := Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul h) j (Finset.mem_univ j)
    simpa only [Equiv.swap_apply_left] using hj

abbrev VarLocalized (o i₀ : ι) := Unit ⊕ Var o i₀

theorem card_varLocalized {o i₀ : ι} (h : i₀ ≠ o) :
    Fintype.card (VarLocalized o i₀) = 2 * Fintype.card ι - 2 + 1 := by
  rw [Fintype.card_sum, Fintype.card_unit, card_var h, Nat.add_comm]

/-- The auxiliary coordinate is the reciprocal of the localizer. -/
def inverseEquation (o i₀ j₀ : ι) : MvPolynomial (VarLocalized o i₀) ℂ :=
  X (.inl ()) * rename Sum.inr (localizer o i₀ j₀) - 1

def adjoin (o i₀ : ι) (x : Point o i₀) (z : ℂ) : VarLocalized o i₀ → ℂ
  | .inl _ => z
  | .inr k => x k

theorem inverseEquation_evaluation (o i₀ j₀ : ι) (x : Point o i₀) (z : ℂ) :
    eval (adjoin o i₀ x z) (inverseEquation o i₀ j₀) =
      z * eval x (localizer o i₀ j₀) - 1 := by
  simp [inverseEquation, adjoin, eval_rename, Function.comp_def]

/-- The algebraic inverse constraint projects exactly to the permitted
open chart, and the inverse coordinate is uniquely forced. -/
theorem existsUnique_inverseEquation_iff (o i₀ j₀ : ι) (x : Point o i₀) :
    (∃! z, eval (adjoin o i₀ x z) (inverseEquation o i₀ j₀) = 0) ↔
      colAt o i₀ x j₀ ≠ 0 ∧ ∀ σ, profile o i₀ x σ ≠ 0 := by
  rw [← eval_localizer_ne_zero_iff]
  simp only [inverseEquation_evaluation, sub_eq_zero]
  constructor
  · rintro ⟨z, hz, _⟩ hzero
    rw [hzero, mul_zero] at hz
    exact zero_ne_one hz
  · intro h
    refine ⟨(eval x (localizer o i₀ j₀))⁻¹, inv_mul_cancel₀ h, ?_⟩
    intro z hz
    exact mul_right_cancel₀ h (hz.trans (inv_mul_cancel₀ h).symm)


/-- Every permitted polynomial point is a realizable matching profile,
not merely a tuple satisfying the prescribed contact relations. -/
theorem exists_spectra_on_nonzero (o i₀ : ι) (x : Point o i₀)
    (hnz : ∀ σ, profile o i₀ x σ ≠ 0) :
    ∃ a b : ι → ℂ, matchingProduct a b = profile o i₀ x := by
  apply (nonzero_additive_profile_iff_anchored o _ hnz).mpr
  have hd : x (.inl ()) ≠ 0 := by
    have h := hnz 1
    rw [profile_evaluation] at h
    exact left_ne_zero_of_mul h
  refine ⟨x (.inl ()), hd, rowAt o i₀ x, colAt o i₀ x,
    rowAt_anchor _ _ _, colAt_anchor _ _ _, fun σ => ?_⟩
  simpa only [kernelMatchingProduct, anchoredMatchingKernel, Matrix.of_apply] using
    profile_evaluation o i₀ x σ

/-- A nonconstant realizable nonzero matching profile has an initial
point in some normalized pivot chart over any chosen anchor. -/
theorem exists_point_of_nonconstant_profile (o : ι) (p : Equiv.Perm ι → ℂ)
    (hp : ∃ a b : ι → ℂ, matchingProduct a b = p)
    (hnz : ∀ σ, p σ ≠ 0) (hconst : ¬ ∀ σ, p σ = p 1) :
    ∃ i₀ j₀ : ι, i₀ ≠ o ∧ ∃ x : Point o i₀,
      colAt o i₀ x j₀ ≠ 0 ∧ profile o i₀ x = p := by
  obtain ⟨d, _, u, v, hu, hv, he⟩ := (nonzero_additive_profile_iff_anchored o p hnz).mp hp
  have he' (σ : Equiv.Perm ι) : p σ = d * ∏ j, (1+u (σ j)*v j) := by
    simpa only [kernelMatchingProduct, anchoredMatchingKernel, Matrix.of_apply] using he σ
  have hex : ∃ i j, u i * v j ≠ 0 := by
    by_contra! h
    apply hconst
    intro σ
    simp [he', h]
  obtain ⟨i₀, j₀, h⟩ := hex
  have hi : i₀ ≠ o := by
    intro e
    subst i₀
    exact h (by simp [hu])
  obtain ⟨x, hx, hx'⟩ := exists_normalized_point d u v hu hv h
  exact ⟨i₀, j₀, hi, x, hx, funext fun σ => (hx' σ).trans (he' σ).symm⟩

end

end MOC.PolynomialContactChart
