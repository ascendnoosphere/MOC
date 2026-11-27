import MOC.Core
import Mathlib.Tactic.FinCases

/-! A four-dimensional spectral pair for which every duplicated pair of
labels enlarges the support in the positive real direction. -/

namespace MOC.DuplicateAnchor


private abbrev Pair := ℤ × ℤ

private def add (x y : Pair) : Pair := (x.1 + y.1, x.2 + y.2)

private def mul (x y : Pair) : Pair :=
  (x.1 * y.1 - x.2 * y.2, x.1 * y.2 + x.2 * y.1)

private def toComplex (x : Pair) : ℂ := ⟨x.1, x.2⟩

private def prod : {n : ℕ} → (Fin n → Pair) → Pair
  | 0, _ => (1, 0)
  | _ + 1, f => mul (f 0) (prod (fun j => f j.succ))

private def left : Fin 4 → Pair := ![(2, 1), (0, 2), (-2, 2), (2, -2)]
private def right : Fin 4 → Pair := ![(1, 0), (1, -2), (-1, -1), (-2, 0)]

/-- The first spectral list, in column-to-row matching convention. -/
def leftSpectrum (j : Fin 4) : ℂ := toComplex (left j)

/-- The second spectral list. -/
def rightSpectrum (j : Fin 4) : ℂ := toComplex (right j)

/-- Append a copy of the entry at position `i`. -/
def duplicate {α : Type*} (f : Fin 4 → α) (i : Fin 4) : Fin 5 → α :=
  ![f 0, f 1, f 2, f 3, f i]

private def witness : Fin 4 → Fin 4 → Fin 5 → Fin 5 :=
  ![![![1, 0, 4, 3, 2], ![0, 2, 4, 1, 3], ![0, 3, 1, 4, 2], ![1, 0, 4, 2, 3]],
    ![![0, 2, 1, 4, 3], ![1, 0, 2, 4, 3], ![1, 4, 0, 2, 3], ![1, 4, 0, 2, 3]],
    ![![0, 2, 4, 1, 3], ![2, 0, 3, 4, 1], ![2, 1, 0, 4, 3], ![2, 3, 4, 0, 1]],
    ![![1, 0, 3, 4, 2], ![2, 0, 3, 4, 1], ![3, 4, 1, 0, 2], ![3, 4, 2, 0, 1]]]

set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 4096 in
private theorem witness_bijective (i j : Fin 4) : Function.Bijective (witness i j) := by
  have h : ∀ i j : Fin 4, ∀ k l : Fin 5, witness i j k = witness i j l → k = l := by
    decide +kernel
  exact ⟨h i j, Finite.injective_iff_surjective.mp (h i j)⟩

private def orig (f : Fin 4 → Fin 4) : Pair := prod (fun k => add (left (f k)) (right k))

set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 4096 in
private theorem orig_bound (σ : Equiv.Perm (Fin 4)) : (orig σ).1 ≤ 5 := by
  have h : ∀ a b c d : Fin 4, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      (orig ![a, b, c, d]).1 ≤ 5 := by decide +kernel
  have hσ : (![σ 0, σ 1, σ 2, σ 3] : Fin 4 → Fin 4) = σ := by
    funext k
    fin_cases k <;> rfl
  rw [← hσ]
  apply h <;> exact σ.injective.ne (by decide)

private def pad (i j : Fin 4) : Pair :=
  prod (fun k => add (duplicate left i (witness i j k)) (duplicate right j k))

set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 4096 in
private theorem pad_strict : ∀ i j : Fin 4,
    let z := pad i j
    let s := add (left i) (right j)
    0 < s.1 * s.1 + s.2 * s.2 ∧
    5 * (s.1 * s.1 + s.2 * s.2) < z.1 * s.1 + z.2 * s.2 := by decide +kernel

set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 4096 in
private theorem map_add (x y : Pair) :
    toComplex (add x y) = toComplex x + toComplex y := by
  apply Complex.ext <;> simp [toComplex, add, Complex.add_re, Complex.add_im]

set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 4096 in
private theorem map_mul (x y : Pair) :
    toComplex (mul x y) = toComplex x * toComplex y := by
  apply Complex.ext <;> simp [toComplex, mul, Complex.mul_re, Complex.mul_im]

set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 4096 in
private theorem map_prod {n : ℕ} (f : Fin n → Pair) :
    toComplex (prod f) = ∏ k, toComplex (f k) := by
  induction n with
  | zero =>
    rw [Finset.univ_eq_empty, Finset.prod_empty]
    apply Complex.ext <;> norm_num [prod, toComplex]
  | succ n ih =>
    rw [Fin.prod_univ_succ, prod, map_mul, ih]

set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 4096 in
private theorem map_duplicate (f : Fin 4 → Pair) (i : Fin 4) (k : Fin 5) :
    toComplex (duplicate f i k) = duplicate (fun t => toComplex (f t)) i k := by
  fin_cases k <;> rfl

set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 4096 in
private theorem map_orig (σ : Equiv.Perm (Fin 4)) :
    toComplex (orig σ) = matchingProduct leftSpectrum rightSpectrum σ := by
  unfold orig matchingProduct
  rw [map_prod]
  simp only [map_add, leftSpectrum, rightSpectrum]

set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 4096 in
/-- Every original matching has real part at most five. -/
theorem original_support_bound (σ : Equiv.Perm (Fin 4)) :
    (matchingProduct leftSpectrum rightSpectrum σ).re ≤ 5 := by
  rw [← map_orig]
  change ((orig σ).1 : ℝ) ≤ 5
  exact_mod_cast orig_bound σ

set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 4096 in
/-- The reverse permutation attains the support bound. -/
theorem original_support_attained :
    (matchingProduct leftSpectrum rightSpectrum Fin.revPerm).re = 5 := by
  rw [← map_orig]
  change ((orig Fin.revPerm).1 : ℝ) = 5
  exact_mod_cast (by decide +kernel : (orig Fin.revPerm).1 = 5)

set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 4096 in
/-- Every pair of duplicate labels creates a normalized matching with real
part greater than five. The denominator is nonzero for each pair. -/
theorem duplicate_support_exceeds (i j : Fin 4) :
    leftSpectrum i + rightSpectrum j ≠ 0 ∧ ∃ τ : Equiv.Perm (Fin 5),
      5 < (matchingProduct (duplicate leftSpectrum i) (duplicate rightSpectrum j) τ /
        (leftSpectrum i + rightSpectrum j)).re := by
  let τ := Equiv.ofBijective (witness i j) (witness_bijective i j)
  let z := pad i j
  let s := add (left i) (right j)
  have hs : leftSpectrum i + rightSpectrum j = toComplex s := (map_add _ _).symm
  have hz : matchingProduct (duplicate leftSpectrum i) (duplicate rightSpectrum j) τ =
      toComplex z := by
    unfold matchingProduct
    change _ = toComplex (prod _)
    rw [map_prod]
    simp only [map_add, map_duplicate]
    rfl
  obtain ⟨hpos, hgt⟩ := pad_strict i j
  have hpos' : 0 < Complex.normSq (toComplex s) := by
    rw [Complex.normSq_apply]
    change (0 : ℝ) < (s.1 : ℝ) * s.1 + (s.2 : ℝ) * s.2
    exact_mod_cast hpos
  constructor
  · rw [hs]
    exact fun h => (ne_of_gt hpos') (by rw [h, Complex.normSq_zero])
  · refine ⟨τ, ?_⟩
    rw [hz, hs, Complex.div_re, ← add_div, lt_div_iff₀ hpos', Complex.normSq_apply]
    change (5 : ℝ) * ((s.1 : ℝ) * s.1 + (s.2 : ℝ) * s.2) <
      (z.1 : ℝ) * s.1 + (z.2 : ℝ) * s.2
    exact_mod_cast hgt

end MOC.DuplicateAnchor
