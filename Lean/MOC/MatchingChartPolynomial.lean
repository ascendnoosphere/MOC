import MOC.AnchoredChart
import MOC.MatchingQuartet
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Fintype.Option
import Mathlib.Tactic.LinearCombination

/-! Polynomial equations for the regular anchored chart in arbitrary order.
The chart for order `n + 2` has one scale, `n` left coordinates, and `n + 1`
right coordinates. An active set of size `k` imposes `k` polynomial equations
when the complex determinant deficit is held fixed. -/

open BigOperators

namespace MOC

/-- Free normalized matching-chart coordinates in order `n + 2`. -/
abbrev MatchingChartVariable (n : ℕ) := Unit ⊕ (Fin n ⊕ Fin (n + 1))

theorem card_matchingChartVariable (n : ℕ) :
    Fintype.card (MatchingChartVariable n) = 2 * (n + 2) - 2 := by
  simp only [MatchingChartVariable, Fintype.card_sum, Fintype.card_unit, Fintype.card_fin]
  omega

/-- The two reserved left entries are `0` and `1`. -/
def matchingChartLeft {n : ℕ} {R : Type*} [Zero R] [One R]
    (z : MatchingChartVariable n → R) : Fin (n + 2) → R :=
  Fin.cases 0 (Fin.cases 1 fun i => z (.inr (.inl i)))

/-- The reserved right entry is `0`. -/
def matchingChartRight {n : ℕ} {R : Type*} [Zero R]
    (z : MatchingChartVariable n → R) : Fin (n + 2) → R :=
  Fin.cases 0 fun j => z (.inr (.inr j))

private theorem map_matchingChartLeft {n : ℕ} {R S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (z : MatchingChartVariable n → R) (i : Fin (n + 2)) :
    f (matchingChartLeft z i) = matchingChartLeft (f ∘ z) i := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
  · exact map_zero f
  · exact map_one f
  · rfl

private theorem map_matchingChartRight {n : ℕ} {R S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (z : MatchingChartVariable n → R) (i : Fin (n + 2)) :
    f (matchingChartRight z i) = matchingChartRight (f ∘ z) i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact map_zero f
  · rfl

noncomputable section

variable {n : ℕ}

/-- A matching product in free coordinates, including its common scale. -/
def matchingChartCoordinate (z : MatchingChartVariable n → ℂ)
    (σ : Equiv.Perm (Fin (n + 2))) : ℂ :=
  anchoredMatchingCoordinate (z (.inl ())) (matchingChartLeft z) (matchingChartRight z) σ

/-- Matching products are polynomial functions of the free chart coordinates. -/
def matchingChartPolynomial (σ : Equiv.Perm (Fin (n + 2))) :
    MvPolynomial (MatchingChartVariable n) ℂ :=
  MvPolynomial.X (.inl ()) * ∏ j,
    (1 - matchingChartLeft MvPolynomial.X (σ j) * matchingChartRight MvPolynomial.X j)

theorem eval_matchingChartPolynomial (z : MatchingChartVariable n → ℂ)
    (σ : Equiv.Perm (Fin (n + 2))) :
    MvPolynomial.eval z (matchingChartPolynomial σ) = matchingChartCoordinate z σ := by
  have hcomp : MvPolynomial.eval z ∘ MvPolynomial.X = z := by
    funext i
    exact MvPolynomial.eval_X i
  simp only [matchingChartPolynomial, matchingChartCoordinate, anchoredMatchingCoordinate,
    map_mul, map_prod, map_sub, map_one, MvPolynomial.eval_X, map_matchingChartLeft,
    map_matchingChartRight, hcomp]

/-- Every chart point is realized by finite spectra. -/
theorem exists_spectra_of_matchingChartCoordinate (z : MatchingChartVariable n → ℂ) :
    ∃ a b : Fin (n + 2) → ℂ, ∀ σ, matchingProduct a b σ = matchingChartCoordinate z σ :=
  exists_spectra_of_anchoredMatchingCoordinate (z (.inl ()))
    (matchingChartLeft z) (matchingChartRight z)

/-- The matching vector recovers the free coordinates on the chart where
all products and the right pivot are nonzero. -/
theorem matchingChart_eq_of_coordinates_eq (z w : MatchingChartVariable n → ℂ)
    (hpiv : z (.inr (.inr 0)) ≠ 0) (hnz : ∀ σ, matchingChartCoordinate z σ ≠ 0)
    (he : ∀ σ, matchingChartCoordinate z σ = matchingChartCoordinate w σ) : z = w := by
  let p : Fin (n + 2) := (0 : Fin (n + 1)).succ
  obtain ⟨hc, hl, hr⟩ := anchored_chart_eq_of_matchingCoordinates_eq
    (z (.inl ())) (w (.inl ())) (matchingChartLeft z) (matchingChartRight z)
    (matchingChartLeft w) (matchingChartRight w) 0 0 p p rfl rfl rfl rfl rfl rfl hpiv hnz he
  funext i
  rcases i with u | (j | j)
  · cases u
    exact hc
  · exact congrFun hl j.succ.succ
  · exact congrFun hr j.succ

/-- Nonopposite spectra with distinct anchor and pivot eigenvalues belong to
the normalized polynomial chart with nonzero products. -/
theorem exists_matchingChartCoordinate_of_nonopposite (a b : Fin (n + 2) → ℂ)
    (hnz : ∀ i j, a i + b j ≠ 0)
    (ha : a (0 : Fin (n + 1)).succ ≠ a 0) (hb : b (0 : Fin (n + 1)).succ ≠ b 0) :
    ∃ z : MatchingChartVariable n → ℂ, z (.inr (.inr 0)) ≠ 0 ∧
      (∀ σ, matchingChartCoordinate z σ ≠ 0) ∧
      ∀ σ, matchingProduct a b σ = matchingChartCoordinate z σ := by
  let p : Fin (n + 2) := (0 : Fin (n + 1)).succ
  obtain ⟨c, x, y, hx, hy, hxp, hyp, hprod, hmatch⟩ :=
    exists_anchored_chart_of_nonopposite_spectra a b 0 0 p p hnz ha hb
  let z : MatchingChartVariable n → ℂ :=
    Sum.elim (fun _ => c) (Sum.elim (fun i => x i.succ.succ) (fun j => y j.succ))
  have hleft : matchingChartLeft z = x := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
    · exact hx.symm
    · exact hxp.symm
    · rfl
  have hright : matchingChartRight z = y := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hy.symm
    · rfl
  refine ⟨z, hyp, ?_, ?_⟩
  · simpa only [matchingChartCoordinate, hleft, hright] using hprod
  · simpa only [matchingChartCoordinate, hleft, hright] using hmatch

/-- The exact complex determinant deficit relative to a reference matching. -/
def matchingChartDeficitPolynomial (U : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)
    (r : Equiv.Perm (Fin (n + 2))) : MvPolynomial (MatchingChartVariable n) ℂ :=
  (∑ σ, MvPolynomial.C (signedWeight U σ) * matchingChartPolynomial σ) -
    matchingChartPolynomial r

theorem eval_matchingChartDeficitPolynomial (z : MatchingChartVariable n → ℂ)
    (a b : Fin (n + 2) → ℂ) (U : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) (hU : IsUnitary U)
    (r : Equiv.Perm (Fin (n + 2))) (h : ∀ σ, matchingProduct a b σ = matchingChartCoordinate z σ) :
    MvPolynomial.eval z (matchingChartDeficitPolynomial U r) =
      determinantValue a b U - matchingProduct a b r := by
  simp only [matchingChartDeficitPolynomial, map_sub, map_sum, map_mul, MvPolynomial.eval_C,
    eval_matchingChartPolynomial, ← h, signed_determinant a b U hU]

/-- The fiber constraints consist of a determinant deficit and one complex
matching difference for each old contact other than the reference. -/
def matchingChartContactPolynomial (U : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)
    (T : Finset (Equiv.Perm (Fin (n + 2)))) (r : Equiv.Perm (Fin (n + 2))) :
    Option ↥(T.erase r) → MvPolynomial (MatchingChartVariable n) ℂ
  | none => matchingChartDeficitPolynomial U r
  | some σ => matchingChartPolynomial r - matchingChartPolynomial σ.val

theorem card_matchingChartContactConstraints (T : Finset (Equiv.Perm (Fin (n + 2))))
    (r : Equiv.Perm (Fin (n + 2))) (hr : r ∈ T) :
    Fintype.card (Option ↥(T.erase r)) = T.card := by
  simpa only [Fintype.card_option, Fintype.card_coe] using Finset.card_erase_add_one hr

/-- The regular chart is the nonvanishing set of a single polynomial. -/
def matchingChartRegularPolynomial (n : ℕ) : MvPolynomial (MatchingChartVariable n) ℂ :=
  let I := {p : Equiv.Perm (Fin (n + 2)) × Equiv.Perm (Fin (n + 2)) // p.1 ≠ p.2}
  MvPolynomial.X (.inr (.inr 0)) * (∏ σ, matchingChartPolynomial σ) *
    ∏ p : I, (matchingChartPolynomial p.val.1 - matchingChartPolynomial p.val.2)

theorem eval_matchingChartRegularPolynomial_ne_zero (z : MatchingChartVariable n → ℂ) :
    MvPolynomial.eval z (matchingChartRegularPolynomial n) ≠ 0 ↔
      z (.inr (.inr 0)) ≠ 0 ∧ (∀ σ, matchingChartCoordinate z σ ≠ 0) ∧
        Function.Injective (matchingChartCoordinate z) := by
  simp only [matchingChartRegularPolynomial, map_mul, map_prod, map_sub, MvPolynomial.eval_X,
    eval_matchingChartPolynomial, mul_ne_zero_iff, Finset.prod_ne_zero_iff, Finset.mem_univ,
    true_implies, sub_ne_zero]
  constructor
  · rintro ⟨⟨hp, hprod⟩, hdiff⟩
    refine ⟨hp, hprod, fun σ τ h => ?_⟩
    exact Classical.byContradiction fun hne => hdiff ⟨(σ, τ), hne⟩ h
  · rintro ⟨hp, hprod, hinj⟩
    exact ⟨⟨hp, hprod⟩, fun p => hinj.ne p.property⟩

/-- On the regular chart, the matching differences recover all chart
coordinates as soon as two disjoint transpositions are available. -/
theorem matchingChart_eq_of_differences_eq (z w : MatchingChartVariable n → ℂ)
    (hz : MvPolynomial.eval z (matchingChartRegularPolynomial n) ≠ 0)
    (r : Equiv.Perm (Fin (n + 2))) (i j k l : Fin (n + 2))
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (h : ∀ σ, matchingChartCoordinate z r - matchingChartCoordinate z σ =
      matchingChartCoordinate w r - matchingChartCoordinate w σ) : z = w := by
  obtain ⟨hpiv, hnz, hinj⟩ := (eval_matchingChartRegularPolynomial_ne_zero z).mp hz
  obtain ⟨a, b, hz'⟩ := exists_spectra_of_matchingChartCoordinate z
  obtain ⟨a', b', hw'⟩ := exists_spectra_of_matchingChartCoordinate w
  let e : Equiv.Perm (Fin (n + 2)) := 1
  let p := e * Equiv.swap i j
  let q := e * Equiv.swap k l
  let pq := e * Equiv.swap i j * Equiv.swap k l
  have hdiag : matchingChartCoordinate z e * matchingChartCoordinate z pq =
      matchingChartCoordinate z p * matchingChartCoordinate z q := by
    simpa only [hz', p, q, pq] using
      matchingProduct_disjoint_swaps_identity a b e i j k l hij hik hil hjk hjl hkl
  have hdiag' : matchingChartCoordinate w e * matchingChartCoordinate w pq =
      matchingChartCoordinate w p * matchingChartCoordinate w q := by
    simpa only [hw', p, q, pq] using
      matchingProduct_disjoint_swaps_identity a' b' e i j k l hij hik hil hjk hjl hkl
  have hne (a b : Fin (n + 2)) (hab : a ≠ b) : e ≠ e * Equiv.swap a b := by
    intro he
    exact hab (by simpa [e] using congrArg (fun σ : Equiv.Perm (Fin (n + 2)) => σ a) he)
  have hΓ : matchingChartCoordinate z e + matchingChartCoordinate z pq -
      matchingChartCoordinate z p - matchingChartCoordinate z q ≠ 0 := by
    intro hzero
    have he := mul_ne_zero (sub_ne_zero.mpr (hinj.ne (hne i j hij)))
      (sub_ne_zero.mpr (hinj.ne (hne k l hkl)))
    apply he
    change (matchingChartCoordinate z e - matchingChartCoordinate z p) *
      (matchingChartCoordinate z e - matchingChartCoordinate z q) = 0
    linear_combination matchingChartCoordinate z e * hzero - hdiag
  let c := matchingChartCoordinate w r - matchingChartCoordinate z r
  have htranslate (σ : Equiv.Perm (Fin (n + 2))) :
      matchingChartCoordinate w σ = matchingChartCoordinate z σ + c := by
    dsimp only [c]
    linear_combination h σ
  have hc : c = 0 := eq_zero_of_matching_quartet_translation hdiag hΓ
    (by simpa only [htranslate] using hdiag')
  exact matchingChart_eq_of_coordinates_eq z w hpiv hnz
    (fun σ => by simpa only [hc, add_zero] using (htranslate σ).symm)

end

end MOC
