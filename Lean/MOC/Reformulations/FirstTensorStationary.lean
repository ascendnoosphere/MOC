import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-! Atlas 022: an exact counterexample for the native Z-eigenvalue product
of binary symmetric quartics. The mixer is the identity. -/

open BigOperators

namespace MOC.Reformulations
noncomputable section

def binaryQuarticOnCircle (A B C u : ℝ) : ℝ := A * u ^ 2 + B * u + C

/-- The two contractions of the symmetric binary tensor for
`A(x²-y²)² + B(x²-y²)(x²+y²) + C(x²+y²)²`. -/
def binaryQuarticContractX (A B C x y : ℝ) : ℝ :=
  (A + B + C) * x ^ 3 + (C - A) * x * y ^ 2

def binaryQuarticContractY (A B C x y : ℝ) : ℝ :=
  (A - B + C) * y ^ 3 + (C - A) * x ^ 2 * y

/-- The two claimed sum coefficients are for the actual sum of the tensors. -/
theorem binaryQuartic_exampleContracts_add (x y : ℝ) :
    binaryQuarticContractX (-2) (-2) (-1) x y + binaryQuarticContractX (-1) 1 0 x y =
      binaryQuarticContractX (-3) (-1) (-1) x y ∧
    binaryQuarticContractY (-2) (-2) (-1) x y + binaryQuarticContractY (-1) 1 0 x y =
      binaryQuarticContractY (-3) (-1) (-1) x y := by
  constructor <;> simp only [binaryQuarticContractX, binaryQuarticContractY] <;> ring

def binaryQuarticZValues (A B C : ℝ) : Set ℝ :=
  {lam | ∃ x y : ℝ, x ^ 2 + y ^ 2 = 1 ∧
    binaryQuarticContractX A B C x y = lam * x ∧
    binaryQuarticContractY A B C x y = lam * y}

private theorem binaryQuartic_zcondition (A B C x y lam : ℝ)
    (hs : x ^ 2 + y ^ 2 = 1) :
    (binaryQuarticContractX A B C x y = lam * x ∧
      binaryQuarticContractY A B C x y = lam * y) ↔
    (binaryQuarticOnCircle A B C (x ^ 2 - y ^ 2) = lam ∧
      x * y * (2 * A * (x ^ 2 - y ^ 2) + B) = 0) := by
  let X := binaryQuarticContractX A B C x y
  let Y := binaryQuarticContractY A B C x y
  have hrad : x * X + y * Y = binaryQuarticOnCircle A B C (x ^ 2 - y ^ 2) := by
    unfold X Y binaryQuarticContractX binaryQuarticContractY binaryQuarticOnCircle
    linear_combination (B * (x ^ 2 - y ^ 2) + C * (x ^ 2 + y ^ 2 + 1)) * hs
  have htan : x * Y - y * X = -(x * y * (2 * A * (x ^ 2 - y ^ 2) + B)) := by
    unfold X Y binaryQuarticContractX binaryQuarticContractY
    linear_combination (-B * x * y) * hs
  change (X = lam * x ∧ Y = lam * y) ↔ _
  constructor
  · rintro ⟨hx, hy⟩
    rw [hx, hy] at hrad htan
    constructor
    · linear_combination lam * hs - hrad
    · linear_combination htan
  · rintro ⟨hq, ht⟩
    rw [hq] at hrad
    rw [ht, neg_zero] at htan
    constructor
    · linear_combination x * hrad - y * htan - X * hs
    · linear_combination y * hrad + x * htan - Y * hs

/-- Exact Z-value set when the sole interior critical point lies on the
reachable interval. The endpoints come from the coordinate axes. -/
theorem binaryQuartic_zValues_eq (A B C : ℝ) (hA : A ≠ 0)
    (hlo : -1 ≤ -B / (2 * A)) (hhi : -B / (2 * A) ≤ 1) :
    binaryQuarticZValues A B C =
      {binaryQuarticOnCircle A B C 1, binaryQuarticOnCircle A B C (-1),
        binaryQuarticOnCircle A B C (-B / (2 * A))} := by
  ext lam
  change (∃ x y : ℝ, x ^ 2 + y ^ 2 = 1 ∧
    binaryQuarticContractX A B C x y = lam * x ∧
    binaryQuarticContractY A B C x y = lam * y) ↔ _
  rw [Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
  have hden : 2 * A ≠ 0 := mul_ne_zero (by norm_num) hA
  constructor
  · rintro ⟨x, y, hs, hx, hy⟩
    obtain ⟨hv, ht⟩ := (binaryQuartic_zcondition A B C x y lam hs).mp ⟨hx, hy⟩
    rcases mul_eq_zero.mp ht with hxy | hcrit
    · rcases mul_eq_zero.mp hxy with hx0 | hy0
      · right; left
        have hu : x ^ 2 - y ^ 2 = -1 := by rw [hx0] at hs ⊢; nlinarith only [hs]
        simpa only [hu] using hv.symm
      · left
        have hu : x ^ 2 - y ^ 2 = 1 := by rw [hy0] at hs ⊢; nlinarith only [hs]
        simpa only [hu] using hv.symm
    · right; right
      have hu : x ^ 2 - y ^ 2 = -B / (2 * A) := by
        apply (eq_div_iff hden).mpr
        linear_combination hcrit
      simpa only [hu] using hv.symm
  · rintro (rfl | rfl | rfl)
    · have hs : (1 : ℝ) ^ 2 + (0 : ℝ) ^ 2 = 1 := by norm_num
      exact ⟨1, 0, hs, (binaryQuartic_zcondition A B C 1 0 _ hs).mpr (by norm_num)⟩
    · have hs : (0 : ℝ) ^ 2 + (1 : ℝ) ^ 2 = 1 := by norm_num
      exact ⟨0, 1, hs, (binaryQuartic_zcondition A B C 0 1 _ hs).mpr (by norm_num)⟩
    · let u := -B / (2 * A)
      let x := Real.sqrt ((1 + u) / 2)
      let y := Real.sqrt ((1 - u) / 2)
      have hx : x ^ 2 = (1 + u) / 2 := Real.sq_sqrt (by dsimp [u]; linarith)
      have hy : y ^ 2 = (1 - u) / 2 := Real.sq_sqrt (by dsimp [u]; linarith)
      have hs : x ^ 2 + y ^ 2 = 1 := by linarith
      have hu : x ^ 2 - y ^ 2 = u := by linarith
      refine ⟨x, y, hs, (binaryQuartic_zcondition A B C x y _ hs).mpr ?_⟩
      rw [hu]
      constructor
      · rfl
      · have ht : 2 * A * u + B = 0 := by dsimp [u]; field_simp [hA]; ring
        rw [ht, mul_zero]

theorem binaryQuartic_exampleZValues :
    binaryQuarticZValues (-2) (-2) (-1) = {(-1 : ℝ), -5, -1 / 2} ∧
    binaryQuarticZValues (-1) 1 0 = {(-2 : ℝ), 0, 1 / 4} ∧
    binaryQuarticZValues (-3) (-1) (-1) = {(-3 : ℝ), -5, -11 / 12} := by
  constructor
  · rw [binaryQuartic_zValues_eq _ _ _ (by norm_num) (by norm_num) (by norm_num)]
    norm_num [binaryQuarticOnCircle, Set.insert_comm]
  constructor
  · rw [binaryQuartic_zValues_eq _ _ _ (by norm_num) (by norm_num) (by norm_num)]
    norm_num [binaryQuarticOnCircle, Set.insert_comm]
  · rw [binaryQuartic_zValues_eq _ _ _ (by norm_num) (by norm_num) (by norm_num)]
    norm_num [binaryQuarticOnCircle, Set.insert_comm]

private def quarticLeftValues (i : Fin 3) : ℝ :=
  if i.val = 0 then -1 else if i.val = 1 then -5 else -1 / 2
private def quarticRightValues (i : Fin 3) : ℝ :=
  if i.val = 0 then -2 else if i.val = 1 then 0 else 1 / 4

private def quarticRowBound (i : Fin 3) : ℝ := -quarticLeftValues i
private def quarticColFactor (y : ℝ) : ℝ := max (1 + 2 * y) (1 + y / 5)
private def quarticColBound (j : Fin 3) : ℝ := quarticColFactor (-quarticRightValues j)

private theorem ite_mem_interval {p : Prop} [Decidable p] {a b lo hi : ℝ}
    (ha : lo ≤ a ∧ a ≤ hi) (hb : lo ≤ b ∧ b ≤ hi) :
    lo ≤ (if p then a else b) ∧ (if p then a else b) ≤ hi :=
  ⟨(le_inf ha.1 hb.1).trans (inf_le_ite a b p),
    (ite_le_sup a b p).trans (sup_le ha.2 hb.2)⟩

/-- The two endpoint slopes bound the factor uniformly on the whole row
interval. The coefficients are nonnegative and add up to the row factor. -/
private theorem quarticUniformBound (x y : ℝ) (hxlo : 1 / 2 ≤ x) (hxhi : x ≤ 5)
    (hy : -1 / 4 ≤ y) : 0 ≤ x + y ∧ x + y ≤ x * quarticColFactor y := by
  constructor
  · linarith
  let a : ℝ := (5 - x) / 9
  let b : ℝ := (10 * x - 5) / 9
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have hb : 0 ≤ b := by dsimp [b]; linarith
  unfold quarticColFactor
  calc
    x + y = a * (1 + 2 * y) + b * (1 + y / 5) := by dsimp [a, b]; ring
    _ ≤ a * max (1 + 2 * y) (1 + y / 5) + b * max (1 + 2 * y) (1 + y / 5) :=
      add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
        (mul_le_mul_of_nonneg_left (le_max_right _ _) hb)
    _ = x * max (1 + 2 * y) (1 + y / 5) := by dsimp [a, b]; ring

/-- One uniform algebraic majorant bounds all entries, hence every matching. -/
private theorem quarticRankOneBound (i j : Fin 3) :
    0 ≤ -(quarticLeftValues i + quarticRightValues j) ∧
      -(quarticLeftValues i + quarticRightValues j) ≤ quarticRowBound i * quarticColBound j := by
  have hx : -5 ≤ quarticLeftValues i ∧ quarticLeftValues i ≤ -1 / 2 := by
    unfold quarticLeftValues
    exact ite_mem_interval (by norm_num) (ite_mem_interval (by norm_num) (by norm_num))
  have hy : -2 ≤ quarticRightValues j ∧ quarticRightValues j ≤ 1 / 4 := by
    unfold quarticRightValues
    exact ite_mem_interval (by norm_num) (ite_mem_interval (by norm_num) (by norm_num))
  unfold quarticRowBound quarticColBound
  rw [neg_add_rev, add_comm]
  exact quarticUniformBound _ _ (by linarith [hx.2]) (by linarith [hx.1]) (by linarith [hy.2])

/-- Every matching product exceeds the product of the summed tensor's
three distinct Z-values. -/
theorem binaryQuartic_product_not_mem_hull :
    (-3 : ℝ) * (-5) * (-11 / 12) ∉ convexHull ℝ
      (Set.range fun σ : Equiv.Perm (Fin 3) =>
        ∏ i, (quarticLeftValues i + quarticRightValues (σ i))) := by
  let value : ℝ := (-3 : ℝ) * (-5) * (-11 / 12)
  have hvertex (σ : Equiv.Perm (Fin 3)) :
      value < ∏ i, (quarticLeftValues i + quarticRightValues (σ i)) := by
    have hb : (∏ i, -(quarticLeftValues i + quarticRightValues (σ i))) ≤
        ∏ i, (quarticRowBound i * quarticColBound (σ i)) :=
      Finset.prod_le_prod (fun i _ => (quarticRankOneBound i (σ i)).1)
        (fun i _ => (quarticRankOneBound i (σ i)).2)
    rw [Finset.prod_mul_distrib, Equiv.prod_comp σ quarticColBound] at hb
    have hbound : (∏ i, quarticRowBound i) * (∏ j, quarticColBound j) = 95 / 8 := by
      rw [Fin.prod_univ_three, Fin.prod_univ_three]
      change (-(-1 : ℝ) * -(-5 : ℝ) * -(-1 / 2 : ℝ)) *
        (quarticColFactor (-(-2)) * quarticColFactor (-0) * quarticColFactor (-(1 / 4))) =
          95 / 8
      norm_num [quarticColFactor, max_def]
    have hsign : (∏ i, -(quarticLeftValues i + quarticRightValues (σ i))) =
        -(∏ i, (quarticLeftValues i + quarticRightValues (σ i))) := by
      simp only [Fin.prod_univ_three]
      ring
    rw [hbound, hsign] at hb
    dsimp [value]
    linarith
  have hset : (Set.range fun σ : Equiv.Perm (Fin 3) =>
        ∏ i, (quarticLeftValues i + quarticRightValues (σ i))) ⊆ Set.Ioi value := by
    rintro z ⟨σ, rfl⟩
    exact hvertex σ
  intro h
  have he := (convexHull_min hset (convex_Ioi (𝕜 := ℝ) value)) h
  change value < value at he
  exact (lt_irrefl _) he

end
end MOC.Reformulations
