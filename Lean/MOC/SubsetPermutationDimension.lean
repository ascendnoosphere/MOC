import MOC.SegreConvexity
import MOC.MiddleSubsetMatchingSpan
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.Matrix.Rank
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Trace

/-! Subset permutation operators, their coefficient space, and the two-row dimension sum. -/

open Matrix Finset

namespace MOC

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]

/-- The columns are the permutation operators in the basis indexed by subsets. -/
def subsetPermutationIncidence (ι K : Type*) [Fintype ι] [DecidableEq ι] [Zero K] [One K] :
    Matrix (Finset ι × Finset ι) (Equiv.Perm ι) K :=
  Matrix.of fun s σ => subsetPermutationOperator (R := K) σ s.1 s.2

/-- The dimension of the operator span equals the rank of the subset incidence matrix. -/
theorem finrank_subsetPermutationSpan_eq_rank :
    Module.finrank K (Submodule.span K (Set.range (subsetPermutationOperator (ι := ι) (R := K)))) =
      (subsetPermutationIncidence ι K).rank := by
  classical
  let A := subsetPermutationIncidence ι K
  let e := LinearEquiv.curry K K (Finset ι) (Finset ι)
  have he : e.toLinearMap '' Set.range A.col =
      Set.range (subsetPermutationOperator (ι := ι) (R := K)) := by
    rw [← Set.range_comp]
    rfl
  rw [← he, ← Submodule.map_span, LinearEquiv.finrank_map_eq,
    Matrix.rank_eq_finrank_span_cols]

/-- Subset indicators as functions on permutations have the same dimension as the operators. -/
theorem finrank_subsetPermutationSpan_eq_indicatorSpan :
    Module.finrank K (Submodule.span K (Set.range (subsetPermutationOperator (ι := ι) (R := K)))) =
      Module.finrank K (Submodule.span K (Set.range (subsetPermutationIncidence ι K).row)) := by
  rw [finrank_subsetPermutationSpan_eq_rank, Matrix.rank_eq_finrank_span_row]

/-- On the lower half of Pascal's row this is the two-row ballot number.
The reflected binomial makes the zero term at index minus one explicit. -/
def twoRowBinomialDifference (n j : ℕ) : ℤ :=
  (n.choose j : ℤ) - n.choose (n + 1 - j)

private theorem choose_convolution (n k : ℕ) :
    (∑ j ∈ range (k + 1), (n.choose j : ℤ) * n.choose (k - j)) =
      (2 * n).choose k := by
  have hn := Nat.add_choose_eq n n k
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => n.choose i * n.choose j)] at hn
  rw [two_mul]
  exact_mod_cast hn.symm

private theorem choose_square_sum (n : ℕ) :
    (∑ j ∈ range (n + 2), (n.choose j : ℤ) ^ 2) = n.centralBinom := by
  rw [sum_range_succ, Nat.choose_eq_zero_of_lt (Nat.lt_succ_self n)]
  simp only [Nat.cast_zero, zero_pow (by decide : 2 ≠ 0), add_zero]
  rw [Nat.centralBinom_eq_two_mul_choose, ← choose_convolution n n]
  refine sum_congr rfl fun j hj => ?_
  have hle : j ≤ n := by have := mem_range.mp hj; omega
  rw [Nat.choose_symm hle, pow_two]

private theorem binomialDifference_reflect (n j : ℕ) (hj : j ≤ n + 1) :
    twoRowBinomialDifference n (n + 1 - j) = -twoRowBinomialDifference n j := by
  unfold twoRowBinomialDifference
  rw [show n + 1 - (n + 1 - j) = j by omega]
  ring

private theorem binomialDifference_full_square_sum (n : ℕ) :
    (∑ j ∈ range (n + 2), twoRowBinomialDifference n j ^ 2) =
      2 * ((n.centralBinom : ℤ) - (2 * n).choose (n + 1)) := by
  have href : (∑ j ∈ range (n + 2), (n.choose (n + 1 - j) : ℤ) ^ 2) =
      ∑ j ∈ range (n + 2), (n.choose j : ℤ) ^ 2 := by
    simpa using sum_range_reflect (fun j => (n.choose j : ℤ) ^ 2) (n + 2)
  have expand (j : ℕ) : twoRowBinomialDifference n j ^ 2 =
      (n.choose j : ℤ) ^ 2 + (n.choose (n + 1 - j) : ℤ) ^ 2 -
        2 * ((n.choose j : ℤ) * n.choose (n + 1 - j)) := by
    unfold twoRowBinomialDifference
    ring
  simp_rw [expand]
  rw [sum_sub_distrib, sum_add_distrib, ← mul_sum, href, choose_square_sum,
    choose_convolution]
  ring

private theorem centralBinom_sub_choose_succ (n : ℕ) :
    (n.centralBinom : ℤ) - (2 * n).choose (n + 1) = catalan n := by
  have hc : catalan n * (n + 1) = n.centralBinom := by
    rw [catalan_eq_centralBinom_div, Nat.div_mul_cancel (Nat.succ_dvd_centralBinom n)]
  have hn := Nat.choose_succ_right_eq (2 * n) n
  rw [← Nat.centralBinom_eq_two_mul_choose, show 2 * n - n = n by omega] at hn
  have hci : (catalan n : ℤ) * (n + 1) = n.centralBinom := by exact_mod_cast hc
  have hni : ((2 * n).choose (n + 1) : ℤ) * (n + 1) = n.centralBinom * (n : ℤ) := by
    exact_mod_cast hn
  apply mul_right_cancel₀ (by positivity : (n : ℤ) + 1 ≠ 0)
  linear_combination hni * (-1) + (-hci)

/-- The sum of the squares of the two-row ballot numbers is the Catalan number. -/
theorem sum_twoRowBinomialDifference_sq (n : ℕ) :
    (∑ j ∈ range (n / 2 + 1), twoRowBinomialDifference n j ^ 2) = catalan n := by
  let m := n / 2 + 1
  let f := fun j => twoRowBinomialDifference n j ^ 2
  have htail : (∑ j ∈ range m, f (n + 2 - m + j)) = ∑ j ∈ range m, f j := by
    rw [← sum_range_reflect f m]
    apply sum_congr rfl
    intro j hj
    have hj' := mem_range.mp hj
    have h : n + 2 - m + j = n + 1 - (m - 1 - j) := by dsimp [m] at *; omega
    dsimp [f]
    rw [h, binomialDifference_reflect _ _ (by dsimp [m]; omega), neg_sq]
  have hmid : (∑ j ∈ range (n + 2 - m), f j) = ∑ j ∈ range m, f j := by
    rcases (show n + 2 - m = m ∨ n + 2 - m = m + 1 by dsimp [m]; omega) with h | h
    · rw [h]
    · have hm : n + 1 - m = m := by dsimp [m] at *; omega
      rw [h, sum_range_succ]
      simp only [f, twoRowBinomialDifference, hm, sub_self, zero_pow (by decide : 2 ≠ 0), add_zero]
  have hall : (∑ j ∈ range (n + 2), f j) = 2 * (∑ j ∈ range m, f j) := by
    conv_lhs => rw [show n + 2 = (n + 2 - m) + m by dsimp [m]; omega, sum_range_add]
    rw [htail, hmid, two_mul]
  have h := binomialDifference_full_square_sum n
  rw [centralBinom_sub_choose_succ] at h
  change (∑ j ∈ range m, f j) = (catalan n : ℤ)
  linarith

/-- Coordinates for signed transversal vectors of perfect matchings on twice as many labels. -/
abbrev MiddleSubset (n : ℕ) := {S : Finset (Fin (2 * n)) // S.card = n}

/-- The normalized reciprocal-binomial kernel on the middle subset level. -/
def middleSubsetKernel (n : ℕ) : Matrix (MiddleSubset n) (MiddleSubset n) ℚ :=
  Matrix.of fun S T =>
    (-1 : ℚ) ^ (S.val \ T.val).card /
      ((n + 1 : ℚ) * n.choose (S.val \ T.val).card)

theorem middleSubsetKernel_trace (n : ℕ) :
    (middleSubsetKernel n).trace = (catalan n : ℚ) := by
  have hcard : Fintype.card (MiddleSubset n) = n.centralBinom := by
    rw [Fintype.card_finset_len, Fintype.card_fin, Nat.centralBinom_eq_two_mul_choose]
  have hdiv : catalan n * (n + 1) = n.centralBinom := by
    rw [catalan_eq_centralBinom_div, Nat.div_mul_cancel (Nat.succ_dvd_centralBinom n)]
  have hd (S : MiddleSubset n) : middleSubsetKernel n S S = 1 / (n + 1 : ℚ) := by
    simp [middleSubsetKernel]
  rw [Matrix.trace]
  change (∑ S, middleSubsetKernel n S S) = _
  simp only [hd, sum_const, card_univ, nsmul_eq_mul, hcard, ← hdiv, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one]
  field_simp

/-- Expansion over all transversals of an oriented matching. A common scalar shift cancels
on every pair. Taking the two endpoint values in each pair to be zero or one gives the
signed transversal evaluation at each binary state. -/
theorem signed_transversal_shift_sum {R α : Type*} [CommRing R] [Fintype α] [DecidableEq α]
    (x y : α → R) (t : R) :
    (∑ J : Finset α, (∏ i ∈ J, (x i - t)) * ∏ i ∈ Jᶜ, (t - y i)) =
      ∏ i, (x i - y i) := by
  rw [← Fintype.prod_add]
  exact Finset.prod_congr rfl fun i _ => by ring

/-- The signed vectors of all matchings between two equal classes span a space of Catalan
dimension on the middle subset level. -/
theorem finrank_middleSubsetMatchingSpan [CharZero K] (n : ℕ) (L R : Finset ι)
    (hl : L.card = n) (hr : R.card = n) (hd : Disjoint L R) (hu : L ∪ R = univ) :
    Module.finrank K (middleSubsetMatchingSpan K n L R) = catalan n := by
  classical
  cases n with
  | zero =>
    have hL := card_eq_zero.mp hl
    have hR := card_eq_zero.mp hr
    subst L
    subst R
    let E : SubsetsOfSize ι 0 := ⟨∅, card_empty⟩
    have htop : middleSubsetMatchingSpan K 0 (∅ : Finset ι) ∅ = ⊤ := by
      apply top_unique
      intro f _
      have hmem : (fun _ : SubsetsOfSize ι 0 => (1 : K)) ∈
          middleSubsetMatchingSpan K 0 (∅ : Finset ι) ∅ :=
        Submodule.subset_span ⟨⟨[], SubsetMatchingList.nil⟩, rfl⟩
      have hf : f = f E • (fun _ : SubsetsOfSize ι 0 => (1 : K)) := by
        funext S
        have he : S = E := Subtype.ext (card_eq_zero.mp S.property)
        rw [he]
        simp
      rw [hf]
      exact Submodule.smul_mem _ _ hmem
    rw [htop, finrank_top, Module.finrank_pi, Fintype.card_finset_len, Nat.choose_zero, catalan_zero]
  | succ k =>
    have hc := congrArg Finset.card hu
    rw [card_union_of_disjoint hd, hl, hr, card_univ] at hc
    have hN : Fintype.card ι = 2 * (k + 1) := by omega
    rw [middleSubsetMatchingSpan_eq_ker L R hl hr hd hu,
      finrank_subsetIncidenceDown_ker k (by omega), hN]
    have hs : (2 * (k + 1)).choose k = (2 * (k + 1)).choose (k + 2) :=
      Nat.choose_symm_of_eq_add (by omega)
    rw [hs, ← Nat.centralBinom_eq_two_mul_choose]
    have hv := centralBinom_sub_choose_succ (k + 1)
    omega

private abbrev leftLabels (ι : Type*) [Fintype ι] : Finset (ι ⊕ ι) :=
  (univ : Finset ι).map Function.Embedding.inl

private abbrev rightLabels (ι : Type*) [Fintype ι] : Finset (ι ⊕ ι) :=
  (univ : Finset ι).map Function.Embedding.inr

private abbrev MatchingLevel (ι : Type*) [Fintype ι] :=
  SubsetsOfSize (ι ⊕ ι) (Fintype.card ι)

private def matchingLevelIndex (I J : Finset ι) (h : I.card = J.card) : MatchingLevel ι :=
  ⟨I.disjSum Jᶜ, by rw [card_disjSum, h, card_add_card_compl]⟩

private def matchingLevelSign (S : MatchingLevel ι) : K :=
  (-1 : K) ^ (rightLabels ι ∩ S.val).card

/-- Restore the two subset indices of an operator. Coordinates of different sizes vanish. -/
private def matchingLevelToMatrix :
    (MatchingLevel ι → K) →ₗ[K] Matrix (Finset ι) (Finset ι) K where
  toFun f := Matrix.of fun I J => if h : I.card = J.card then
    matchingLevelSign (matchingLevelIndex I J h) * f (matchingLevelIndex I J h) else 0
  map_add' f g := by ext I J; by_cases h : I.card = J.card <;> simp [h, mul_add]
  map_smul' c f := by ext I J; by_cases h : I.card = J.card <;> simp [h, mul_left_comm]

private theorem matchingLevelToMatrix_injective :
    Function.Injective (matchingLevelToMatrix (ι := ι) (K := K)) := by
  intro f g he
  funext S
  have hh := S.val.card_toLeft_add_card_toRight
  have hc := S.val.toRight.card_add_card_compl
  have h : S.val.toLeft.card = S.val.toRightᶜ.card := by rw [S.property] at hh; omega
  have hi : matchingLevelIndex S.val.toLeft S.val.toRightᶜ h = S := by
    apply Subtype.ext
    simp only [matchingLevelIndex, compl_compl, toLeft_disjSum_toRight]
  have he' := congrFun (congrFun he S.val.toLeft) S.val.toRightᶜ
  change (if h' : S.val.toLeft.card = S.val.toRightᶜ.card then
      matchingLevelSign (matchingLevelIndex _ _ h') * f (matchingLevelIndex _ _ h') else 0) =
    (if h' : S.val.toLeft.card = S.val.toRightᶜ.card then
      matchingLevelSign (matchingLevelIndex _ _ h') * g (matchingLevelIndex _ _ h') else 0) at he'
  simp only [dif_pos h, hi] at he'
  exact mul_left_cancel₀ (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) he'

private theorem matchingList_covers_right {α : Type*} [DecidableEq α]
    {L R : Finset α} {p : List (α × α)} (hp : SubsetMatchingList L R p)
    {r : α} (hr : r ∈ R) : ∃ l, (l,r) ∈ p := by
  induction hp with
  | nil => simp at hr
  | cons hl hr' hp ih =>
    rcases mem_insert.mp hr with rfl | ha
    · exact ⟨_, by simp⟩
    · obtain ⟨l, hlp⟩ := ih ha
      exact ⟨l, List.mem_cons_of_mem _ hlp⟩

private theorem matchingList_extends {α : Type*} [DecidableEq α]
    {L R : Finset α} {p : List (α × α)} (hp : SubsetMatchingList L R p) :
    ∃ e : Equiv.Perm α, ∀ v ∈ p, e v.2 = v.1 := by
  induction hp with
  | nil => exact ⟨1, by simp⟩
  | @cons L R l r p hl hr hp ih =>
    obtain ⟨e, he⟩ := ih
    refine ⟨e.trans (Equiv.swap (e r) l), ?_⟩
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · simp
    · have h1 : v.1 ≠ l := fun h => hl (h ▸ (hp.endpoints hv).1)
      have h2 : e v.2 ≠ e r := fun h => hr (e.injective h ▸ (hp.endpoints hv).2)
      have h3 : e v.2 ≠ l := (he v hv).trans_ne h1
      simpa only [Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne h2 h3] using he v hv

private def RealizesPairs (p : List ((ι ⊕ ι) × (ι ⊕ ι))) (σ : Equiv.Perm ι) : Prop :=
  ∀ v ∈ p, ∃ j, v = (Sum.inl (σ j), Sum.inr j)

private theorem matchingList_realizes_perm {p : List ((ι ⊕ ι) × (ι ⊕ ι))}
    (hp : SubsetMatchingList (leftLabels ι) (rightLabels ι) p) :
    ∃ σ : Equiv.Perm ι, RealizesPairs p σ := by
  classical
  obtain ⟨e, he⟩ := matchingList_extends hp
  have ex (j : ι) : ∃ i : ι, e (.inr j) = .inl i := by
    obtain ⟨l, hl⟩ := matchingList_covers_right hp (r := Sum.inr j) (by simp [rightLabels])
    obtain ⟨i, _, hi⟩ := mem_map.mp (hp.endpoints hl).1
    exact ⟨i, (he _ hl).trans hi.symm⟩
  choose q hq using ex
  have hinj : Function.Injective q := by
    intro i j hij
    exact Sum.inr.inj (e.injective ((hq i).trans ((congrArg Sum.inl hij).trans (hq j).symm)))
  refine ⟨Equiv.ofBijective q ⟨hinj, Finite.surjective_of_injective hinj⟩, ?_⟩
  intro v hv
  obtain ⟨j, _, hj⟩ := mem_map.mp (hp.endpoints hv).2
  change Sum.inr j = v.2 at hj
  exact ⟨j, Prod.ext (((he _ hv).symm.trans ((congrArg e hj.symm).trans (hq j)))) hj.symm⟩

private theorem exists_matchingList_for_perm (σ : Equiv.Perm ι) :
    ∃ p, SubsetMatchingList (leftLabels ι) (rightLabels ι) p ∧ RealizesPairs p σ := by
  classical
  let a : ι ↪ ι ⊕ ι := σ.toEmbedding.trans Function.Embedding.inl
  have aux (J : Finset ι) : ∃ p, SubsetMatchingList (J.map a) (J.map .inr) p ∧
      RealizesPairs p σ := by
    induction J using Finset.induction_on with
    | empty => exact ⟨[], by simpa using (SubsetMatchingList.nil (α := ι ⊕ ι)), by simp [RealizesPairs]⟩
    | @insert j J hj ih =>
      obtain ⟨p, hp, hσ⟩ := ih
      refine ⟨(Sum.inl (σ j), Sum.inr j) :: p, ?_, ?_⟩
      · rw [map_insert, map_insert]
        exact SubsetMatchingList.cons (by simpa only [mem_map' a] using hj)
          (by simpa only [mem_map' Function.Embedding.inr] using hj) hp
      · intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact ⟨j, rfl⟩
        · exact hσ _ hv
  obtain ⟨p, hp, hσ⟩ := aux univ
  have ha : univ.map a = leftLabels ι := by
    change univ.map (σ.toEmbedding.trans Function.Embedding.inl) =
      (univ : Finset ι).map Function.Embedding.inl
    rw [← map_map]
    simp
  rw [ha] at hp
  exact ⟨p, hp, hσ⟩

private theorem matchingLevelToMatrix_coefficient {p : List ((ι ⊕ ι) × (ι ⊕ ι))}
    (hp : SubsetMatchingList (leftLabels ι) (rightLabels ι) p) {σ : Equiv.Perm ι}
    (hσ : RealizesPairs p σ) :
    matchingLevelToMatrix (fun S : MatchingLevel ι => subsetMatchingCoefficient (K := K) p S.val) =
      subsetPermutationOperator σ := by
  ext I J
  have hm : (∀ v ∈ p, (v.1 ∈ I.disjSum Jᶜ ↔ v.2 ∉ I.disjSum Jᶜ)) ↔ J.map σ.toEmbedding = I := by
    constructor
    · intro h
      ext i
      obtain ⟨j, rfl⟩ := σ.surjective i
      obtain ⟨l, hl⟩ := matchingList_covers_right hp (r := Sum.inr j) (by simp [rightLabels])
      obtain ⟨j', hj⟩ := hσ _ hl
      have he : j = j' := Sum.inr.inj (congrArg Prod.snd hj)
      subst j'
      have hv := h (Sum.inl (σ j), Sum.inr j) (hj ▸ hl)
      simpa [mem_map' σ.toEmbedding] using hv.symm
    · intro h v hv
      obtain ⟨j, rfl⟩ := hσ _ hv
      simp [← h, mem_map' σ.toEmbedding]
  change (if h : I.card = J.card then matchingLevelSign (matchingLevelIndex I J h) *
      subsetMatchingCoefficient (K := K) p (matchingLevelIndex I J h).val else 0) =
    (if J.map σ.toEmbedding = I then 1 else 0)
  by_cases h : I.card = J.card
  · rw [dif_pos h, hp.coefficient_formula]
    change (-1 : K) ^ (rightLabels ι ∩ I.disjSum Jᶜ).card *
      (if ∀ v ∈ p, v.1 ∈ I.disjSum Jᶜ ↔ v.2 ∉ I.disjSum Jᶜ
       then (-1 : K) ^ (rightLabels ι ∩ I.disjSum Jᶜ).card else 0) = _
    rw [propext hm]
    by_cases he : J.map σ.toEmbedding = I
    · simp only [if_pos he]
      rw [← mul_pow]
      simp
    · simp only [if_neg he, mul_zero]
  · have hne : J.map σ.toEmbedding ≠ I := by
      intro he
      exact h (by rw [← he, card_map])
    rw [dif_neg h, if_neg hne]

/-- The dimension of the permutation algebra in the two-state tensor basis is the
Catalan number. A permutation operator maps the subset J onto its image. -/
theorem finrank_subsetPermutationSpan [CharZero K] :
    Module.finrank K (Submodule.span K (Set.range (subsetPermutationOperator (ι := ι) (R := K)))) =
      catalan (Fintype.card ι) := by
  classical
  let W := middleSubsetMatchingSpan K (Fintype.card ι) (leftLabels ι) (rightLabels ι)
  let F := matchingLevelToMatrix (ι := ι) (K := K)
  have hmap : W.map F = Submodule.span K (Set.range (subsetPermutationOperator (ι := ι) (R := K))) := by
    dsimp only [W, middleSubsetMatchingSpan]
    rw [Submodule.map_span]
    apply congrArg (Submodule.span K)
    ext m
    constructor
    · rintro ⟨_, ⟨p, rfl⟩, rfl⟩
      obtain ⟨σ, hσ⟩ := matchingList_realizes_perm p.property
      exact ⟨σ, (matchingLevelToMatrix_coefficient p.property hσ).symm⟩
    · rintro ⟨σ, rfl⟩
      obtain ⟨p, hp, hσ⟩ := exists_matchingList_for_perm σ
      exact ⟨_, ⟨⟨p, hp⟩, rfl⟩, matchingLevelToMatrix_coefficient hp hσ⟩
  rw [← hmap, ← (Submodule.equivMapOfInjective F matchingLevelToMatrix_injective W).finrank_eq]
  apply finrank_middleSubsetMatchingSpan
  · simp [leftLabels]
  · simp [rightLabels]
  · exact disjoint_map_inl_map_inr _ _
  · ext s
    cases s <;> simp [leftLabels, rightLabels]

theorem finrank_subsetIndicatorSpan [CharZero K] :
    Module.finrank K (Submodule.span K (Set.range (subsetPermutationIncidence ι K).row)) =
      catalan (Fintype.card ι) := by
  rw [← finrank_subsetPermutationSpan_eq_indicatorSpan, finrank_subsetPermutationSpan]

end MOC
