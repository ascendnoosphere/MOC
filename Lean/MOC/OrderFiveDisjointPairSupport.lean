import MOC.OrderFivePairCost
import MOC.TransportGapCertificate
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-! Disjoint pairs in order five have a joint minor law by complementing
one side of a nested two-to-three minor law. This gives additional linear
constraints on the doubleton assignment problem and an exact certificate
for one spectral direction. The nested law uses the finite shadow argument
of Lyons, *Determinantal Probability Measures*, Theorem 6.2
(https://www.numdam.org/item/10.1007/s10240-003-0016-0.pdf). -/

open BigOperators Finset Matrix

namespace MOC

noncomputable section

/-- Squared-minor distributions for disjoint column sets have a coupling on
disjoint row sets. This is a two-marginal statement. -/
theorem exists_disjoint_minor_transport {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : IsUnitary U) (J K : Finset (Fin n)) (hJK : Disjoint J K) :
    ∃ μ : Finset (Fin n) → Finset (Fin n) → ℝ,
      (∀ I L, 0 ≤ μ I L) ∧ (∀ I L, μ I L ≠ 0 → Disjoint I L) ∧
      (∀ I, ∑ L, μ I L = subsetMinorSq U I J) ∧
      (∀ L, ∑ I, μ I L = subsetMinorSq U L K) := by
  classical
  have hsub : J ⊆ Kᶜ := fun i hi =>
    Finset.mem_compl.mpr (fun hk => Finset.disjoint_left.mp hJK hi hk)
  obtain ⟨μ, hμ, hs, hr, hc⟩ := exists_nested_minor_transport U hU J Kᶜ hsub
  let e : Equiv.Perm (Finset (Fin n)) := ⟨compl, compl, compl_compl, compl_compl⟩
  refine ⟨fun I L => μ I Lᶜ, fun I L => hμ I Lᶜ, ?_, ?_, ?_⟩
  · intro I L h
    exact Finset.disjoint_left.mpr (fun _ hi hl =>
      Finset.mem_compl.mp (hs I Lᶜ h hi) hl)
  · intro I
    exact (Equiv.sum_comp e (μ I)).trans (hr I)
  · intro L
    exact (hc Lᶜ).trans (subsetMinorSq_compl U hU L K)

/-- Potentials on the two row sets give a valid minor inequality when their
sum is nonnegative on every size-compatible disjoint pair. -/
theorem disjointMinorReducedCost_nonneg {n : ℕ}
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U)
    (J K : Finset (Fin n)) (hJK : Disjoint J K) (p q : Finset (Fin n) → ℝ)
    (hcost : ∀ I L, Disjoint I L → I.card = J.card → L.card = K.card → 0 ≤ p I + q L) :
    0 ≤ (∑ I, subsetMinorSq U I J * p I) + ∑ L, subsetMinorSq U L K * q L := by
  obtain ⟨μ, hμ, hs, hr, hc⟩ := exists_disjoint_minor_transport U hU J K hJK
  have hsize (f : Finset (Fin n) → ℝ) (hf : ∀ L, 0 ≤ f L)
      (I J : Finset (Fin n)) (hm : ∑ L, f L = subsetMinorSq U I J)
      (L : Finset (Fin n)) (hL : f L ≠ 0) : I.card = J.card := by
    by_contra h
    have hz : ∑ L, f L = 0 := by rw [hm]; simp [subsetMinorSq, h]
    exact hL ((Finset.sum_eq_zero_iff_of_nonneg (fun L _ => hf L)).mp hz L (mem_univ L))
  have hsized (I L : Finset (Fin n)) (h : μ I L ≠ 0) :
      Disjoint I L ∧ I.card = J.card ∧ L.card = K.card :=
    ⟨hs I L h, hsize (μ I) (hμ I) I J (hr I) L h,
      hsize (fun I => μ I L) (fun I => hμ I L) L K (hc L) I h⟩
  exact (transportReducedCost_nonneg_and_zero _ _ _ p q μ hμ hsized hr hc
    (fun I L h => hcost I L h.1 h.2.1 h.2.2)).1

/-- A disjoint pair of column sets cannot both assign mass one to
intersecting row sets. In order five this cuts off doubleton assignment
permutations that fail to preserve disjointness. -/
theorem subsetMinorSq_add_le_one_of_disjoint_columns {n : ℕ}
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U)
    (I L J K : Finset (Fin n)) (hJK : Disjoint J K) (hIL : ¬ Disjoint I L) :
    subsetMinorSq U I J + subsetMinorSq U L K ≤ 1 := by
  let p (X : Finset (Fin n)) : ℝ := if X = I then -1 else 0
  let q (Y : Finset (Fin n)) : ℝ := if Y = L then 0 else 1
  have hcost (X Y : Finset (Fin n)) (hXY : Disjoint X Y) :
      0 ≤ p X + q Y := by
    by_cases hX : X = I
    · subst X
      have hY : Y ≠ L := fun h => hIL (h ▸ hXY)
      simp [p, q, hY]
    · by_cases hY : Y = L <;> simp [p, q, hX, hY]
  have hp : ∑ X, subsetMinorSq U X J * p X = -subsetMinorSq U I J := by
    simp [p, mul_ite]
  have hq : ∑ Y, subsetMinorSq U Y K * q Y = 1 - subsetMinorSq U L K := by
    calc
      _ = (∑ Y, subsetMinorSq U Y K) -
          ∑ Y, if Y = L then subsetMinorSq U Y K else 0 := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro Y _
        by_cases hY : Y = L <;> simp [q, hY]
      _ = _ := by rw [sum_subsetMinorSq U hU K]; simp
  have h := disjointMinorReducedCost_nonneg U hU J K hJK p q (fun X Y hXY _ _ => hcost X Y hXY)
  rw [hp, hq] at h
  linarith only [h]

private theorem signed_expectation_image_potential {n : ℕ}
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U)
    (J : Finset (Fin n)) (p : Finset (Fin n) → ℝ) :
    (∑ σ : Equiv.Perm (Fin n), realSignedWeight U σ * p (J.map σ.toEmbedding)) =
      ∑ I, p I * subsetMinorSq U I J := by
  classical
  simpa [subsetImageEvent, mul_ite] using
    signed_expectation_subsetImageCombo U hU (fun I => I) (fun _ => J) p

/-- Every pair of disjoint column pairs gives a valid signed expectation.
The potentials need only have nonnegative sum on disjoint row pairs. -/
theorem signed_expectation_disjoint_image_potentials {n : ℕ}
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U)
    (J K : Finset (Fin n)) (hJK : Disjoint J K) (p q : Finset (Fin n) → ℝ)
    (hcost : ∀ I L, Disjoint I L → I.card = J.card → L.card = K.card → 0 ≤ p I + q L) :
    0 ≤ ∑ σ : Equiv.Perm (Fin n), realSignedWeight U σ *
      (p (J.map σ.toEmbedding) + q (K.map σ.toEmbedding)) := by
  simp_rw [mul_add, Finset.sum_add_distrib, signed_expectation_image_potential U hU]
  simpa only [mul_comm] using disjointMinorReducedCost_nonneg U hU J K hJK p q hcost

local notation "Pair₅" => SubsetLayer (Fin 5) 2

/-- One disjoint-pair constraint compares two columns of the order-five
doubleton table. Its potentials are arbitrary real functions of the rows. -/
structure OrderFiveDisjointPairCut where
  first : Pair₅
  second : Pair₅
  disjoint : Disjoint first.val second.val
  leftCost : Finset (Fin 5) → ℝ
  rightCost : Finset (Fin 5) → ℝ
  nonneg : ∀ I L : Pair₅, Disjoint I.val L.val → 0 ≤ leftCost I.val + rightCost L.val

/-- The entrywise cost adjustment from one disjoint-pair constraint. -/
def OrderFiveDisjointPairCut.adjustment (t : OrderFiveDisjointPairCut) (I J : Pair₅) : ℝ :=
  (if J = t.first then t.leftCost I.val else 0) +
    (if J = t.second then t.rightCost I.val else 0)

private theorem sum_pair_layer (U : Matrix (Fin 5) (Fin 5) ℂ) (J : Pair₅)
    (f : Finset (Fin 5) → ℝ) :
    (∑ I : Pair₅, f I.val * subsetMinorSq U I.val J.val) =
      ∑ I : Finset (Fin 5), subsetMinorSq U I J.val * f I := by
  classical
  rw [← Finset.sum_subtype (univ.filter (fun I : Finset (Fin 5) => I.card = 2))
    (by simp) (fun I => f I * subsetMinorSq U I J.val), Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro I _
  by_cases h : I.card = 2
  · simp [h, mul_comm]
  · simp [h, subsetMinorSq, J.property]

/-- The order-five assignment dual with a finite collection of disjoint-pair
constraints. Each constraint has its own coupling. The resulting upper bound
proves the desired support inequality whenever it reaches a matching score. -/
theorem orderFive_spectral_support_le_disjoint_pair_dual
    {κ : Type*} [Fintype κ] (a b : Fin 5 → ℂ) (η : ℂ)
    (U : Matrix (Fin 5) (Fin 5) ℂ) (hU : IsUnitary U)
    (t : κ → OrderFiveDisjointPairCut) (r q : Pair₅ → ℝ)
    (hdual : ∀ I J, orderFivePairCost a b η I J + (∑ k, (t k).adjustment I J) ≤ r I + q J) :
    (η * determinantValue a b U).re ≤ orderFivePairOffset a b η + (∑ I, r I) + ∑ J, q J := by
  classical
  let m (I J : Pair₅) := subsetMinorSq U I.val J.val
  let S := ∑ J : Pair₅, ∑ I : Pair₅, orderFivePairCost a b η I J * m I J
  have hcolumn (V : Matrix (Fin 5) (Fin 5) ℂ) (hV : IsUnitary V) (J : Pair₅) :
      ∑ I : Pair₅, subsetMinorSq V I.val J.val = 1 := by
    simpa only [one_mul, mul_one] using
      (sum_pair_layer V J (fun _ => 1)).trans (by
        simpa only [mul_one] using sum_subsetMinorSq V hV J.val)
  have hcol (J : Pair₅) : ∑ I, m I J = 1 := hcolumn U hU J
  have hrow (I : Pair₅) : ∑ J, m I J = 1 := by
    have hUT : IsUnitary Uᴴ := by simpa [IsUnitary, and_comm] using hU
    have hm (J : Pair₅) : m I J = subsetMinorSq Uᴴ J.val I.val := by
      let e : Fin 2 ≃ I.val := Fintype.equivOfCardEq (by simp [I.property])
      let f : Fin 2 ≃ J.val := Fintype.equivOfCardEq (by simp [J.property])
      change subsetMinorSq U I.val J.val = _
      rw [subsetMinorSq_eq_normSq_det_submatrix U hU I.val J.val e f,
        subsetMinorSq_eq_normSq_det_submatrix Uᴴ hUT J.val I.val f e]
      change Complex.normSq (U.submatrix (Subtype.val ∘ e) (Subtype.val ∘ f)).det =
        Complex.normSq (U.submatrix (Subtype.val ∘ e) (Subtype.val ∘ f))ᴴ.det
      rw [Matrix.det_conjTranspose]
      exact (Complex.normSq_conj _).symm
    simpa only [hm] using (hcolumn Uᴴ hUT I : ∑ J : Pair₅, subsetMinorSq Uᴴ J.val I.val = 1)
  have hcut (k : κ) : 0 ≤ ∑ J : Pair₅, ∑ I : Pair₅, (t k).adjustment I J * m I J := by
    let v := t k
    have hcost (I L : Finset (Fin 5)) (hIL : Disjoint I L)
        (hI : I.card = v.first.val.card) (hL : L.card = v.second.val.card) :
        0 ≤ v.leftCost I + v.rightCost L :=
      v.nonneg ⟨I, hI.trans v.first.property⟩ ⟨L, hL.trans v.second.property⟩ hIL
    have h := disjointMinorReducedCost_nonneg U hU v.first.val v.second.val
      v.disjoint v.leftCost v.rightCost hcost
    rw [← sum_pair_layer U v.first v.leftCost, ← sum_pair_layer U v.second v.rightCost] at h
    change 0 ≤ ∑ J : Pair₅, ∑ I : Pair₅, v.adjustment I J * m I J
    simp only [OrderFiveDisjointPairCut.adjustment, add_mul, Finset.sum_add_distrib, ite_mul,
      zero_mul]
    rw [Finset.sum_comm (f := fun J I => if J = v.first then v.leftCost I.val * m I J else 0),
      Finset.sum_comm (f := fun J I => if J = v.second then v.rightCost I.val * m I J else 0)]
    simpa only [Finset.sum_ite_eq', Finset.mem_univ, if_true, m] using h
  have hd : S + ∑ k, ∑ J : Pair₅, ∑ I : Pair₅, (t k).adjustment I J * m I J ≤
      (∑ I, r I) + ∑ J, q J := by
    calc
      _ = ∑ J : Pair₅, ∑ I : Pair₅,
          (orderFivePairCost a b η I J + ∑ k, (t k).adjustment I J) * m I J := by
        simp only [S, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
        rw [Finset.sum_comm (f := fun k J => ∑ I : Pair₅, (t k).adjustment I J * m I J)]
        congr 1
        apply Finset.sum_congr rfl
        intro J _
        exact Finset.sum_comm
      _ ≤ ∑ J : Pair₅, ∑ I : Pair₅, (r I + q J) * m I J := by
        exact Finset.sum_le_sum fun J _ => Finset.sum_le_sum fun I _ =>
          mul_le_mul_of_nonneg_right (hdual I J) (subsetMinorSq_nonneg U I.val J.val)
      _ = _ := by
        simp only [add_mul, Finset.sum_add_distrib]
        rw [Finset.sum_comm (f := fun J I => r I * m I J)]
        simp only [← Finset.mul_sum, hrow, hcol, mul_one]
  rw [orderFive_determinant_support_eq_pair_cost a b η U hU]
  change orderFivePairOffset a b η + S ≤ orderFivePairOffset a b η + (∑ I, r I) + ∑ J, q J
  have hp := Finset.sum_nonneg (fun k (_ : k ∈ (univ : Finset κ)) => hcut k)
  linarith only [hd, hp]

/-! The worked order-five flow certificate uses column-to-row permutations.
The first spectral list below is the target list of the row-to-column
arithmetic certificate. The second list is its source list. -/

def orderFiveFlowFirst : Fin 5 → GaussianInt :=
  ![⟨-6, 4⟩, ⟨1, -3⟩, ⟨-1, 8⟩, ⟨8, -8⟩, ⟨5, 2⟩]

def orderFiveFlowSecond : Fin 5 → GaussianInt :=
  ![⟨3, 2⟩, ⟨3, 1⟩, ⟨5, -4⟩, ⟨1, 6⟩, ⟨-6, 7⟩]

def orderFiveFlowDirection : GaussianInt := ⟨34944, -130480⟩

private def flowRow (k : Fin 39) : Finset (Fin 5) :=
  ![{0}, {3}, {2}, {4}, {0,1}, {0,3}, {2,3}, {0,3}, {1,3}, {1,4},
    {0,1}, {0,2}, {1,2}, {1,3}, {3,4}, {0,1}, {0,2}, {0,4}, {2,4}, {0,1},
    {1,3}, {3,4}, {0,1}, {0,3}, {0,2}, {0,3}, {0,4}, {1,3}, {1,4}, {3,4},
    {0,3}, {1,2}, {1,4}, {2,3}, {0,1}, {0,4}, {2,3}, {2,4}, {3,4}] k

private def flowColumn (k : Fin 39) : Finset (Fin 5) :=
  ![{0}, {3}, {4}, {4}, {0,1}, {0,1}, {0,1}, {0,2}, {0,2}, {0,2},
    {0,3}, {0,3}, {0,3}, {0,3}, {0,3}, {0,4}, {0,4}, {0,4}, {0,4}, {1,2},
    {1,2}, {1,2}, {1,3}, {1,3}, {1,4}, {1,4}, {1,4}, {2,3}, {2,3}, {2,3},
    {2,4}, {2,4}, {2,4}, {2,4}, {3,4}, {3,4}, {3,4}, {3,4}, {3,4}] k

private def flowCoefficient (k : Fin 39) : ℤ :=
  112 * (![4695040, 5435806, 8747402, 4791716, 284340, 6470770, 1016376,
    1120420, 25460265, 2986752, 3434050, 668202, 82506, 1331237, 92466,
    2086306, 4759738, 8973960, 2157798, 237150, 30103240, 12240108,
    2416750, 2187460, 11909357, 5825120, 9287287, 16234611, 7355592,
    1899296, 11381432, 11682020, 21614574, 5137002, 39430192, 27438486,
    826690, 9587974, 574570] : Fin 39 → ℤ) k

private def flowLower : Finset (Finset (Fin 5)) :=
  {{0,3}, {1,3}, {1,4}, {2,3}, {3,4}}

private def flowUpperComplement : Finset (Finset (Fin 5)) :=
  {{0,1}, {0,2}, {0,3}, {0,4}, {1,2}, {1,4}, {2,3}, {2,4}}

private def flowLeftCost (I : Finset (Fin 5)) : ℤ :=
  if I ∈ flowLower then -(112 * 26309360) else 0

private def flowRightCost (L : Finset (Fin 5)) : ℤ :=
  if L ∈ flowUpperComplement then 112 * 26309360 else 0

private def flowScore (σ : Equiv.Perm (Fin 5)) : GaussianInt :=
  orderFiveFlowDirection * ∏ j, (orderFiveFlowFirst (σ j) + orderFiveFlowSecond j)

private theorem flowCoefficient_nonneg : ∀ k, 0 ≤ flowCoefficient k := by
  decide +kernel

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8000 in
private theorem flow_cut_nonneg :
    ∀ I L : Finset (Fin 5), Disjoint I L → I.card = 2 → L.card = 2 →
      0 ≤ flowLeftCost I + flowRightCost L := by
  decide +kernel

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16000 in
private theorem flow_identity :
    ∀ σ : Equiv.Perm (Fin 5),
    1228164224 - (flowScore σ).re =
      flowLeftCost (({3,4} : Finset (Fin 5)).map σ.toEmbedding) +
      flowRightCost (({0,1} : Finset (Fin 5)).map σ.toEmbedding) +
      ∑ k, if (flowColumn k).map σ.toEmbedding = flowRow k then flowCoefficient k else 0 := by
  decide +kernel

private theorem flowScore_cast (σ : Equiv.Perm (Fin 5)) :
    ((flowScore σ).re : ℝ) =
      (GaussianInt.toComplex orderFiveFlowDirection *
        matchingProduct (GaussianInt.toComplex ∘ orderFiveFlowFirst)
          (GaussianInt.toComplex ∘ orderFiveFlowSecond) σ).re := by
  rw [GaussianInt.to_real_re]
  simp only [flowScore, matchingProduct, map_mul, map_prod, map_add, Function.comp_apply]

/-- The exact certificate bounds one projection for every five-by-five
unitary mixer. It uses 39 nonnegative minor coefficients and one
disjoint-pair constraint. -/
theorem orderFiveFlowFixture_support (U : Matrix (Fin 5) (Fin 5) ℂ) (hU : IsUnitary U) :
    (GaussianInt.toComplex orderFiveFlowDirection *
      determinantValue (GaussianInt.toComplex ∘ orderFiveFlowFirst)
        (GaussianInt.toComplex ∘ orderFiveFlowSecond) U).re ≤ 1228164224 := by
  let J : Finset (Fin 5) := {3,4}
  let K : Finset (Fin 5) := {0,1}
  let r (σ : Equiv.Perm (Fin 5)) : ℝ :=
    (flowLeftCost (J.map σ.toEmbedding) : ℝ) + (flowRightCost (K.map σ.toEmbedding) : ℝ)
  have hcost (I L : Finset (Fin 5)) (hIL : Disjoint I L) (hI : I.card = J.card)
      (hL : L.card = K.card) : 0 ≤ (flowLeftCost I : ℝ) + (flowRightCost L : ℝ) := by
    have h := flow_cut_nonneg I L hIL (hI.trans (by decide)) (hL.trans (by decide))
    exact_mod_cast h
  have hr : 0 ≤ ∑ σ, realSignedWeight U σ * r σ :=
    signed_expectation_disjoint_image_potentials U hU J K (by decide)
      (fun I => (flowLeftCost I : ℝ)) (fun L => (flowRightCost L : ℝ)) hcost
  refine spectral_support_of_subsetImage_certificate _ _ U hU _ _ flowRow flowColumn
    (fun k => (flowCoefficient k : ℝ)) (fun k => ?_) r hr (fun σ => ?_)
  · dsimp only
    exact_mod_cast flowCoefficient_nonneg k
  · rw [← flowScore_cast]
    have hterm (k : Fin 39) :
        ((if (flowColumn k).map σ.toEmbedding = flowRow k then flowCoefficient k else 0 : ℤ) : ℝ) =
        (flowCoefficient k : ℝ) * subsetImageEvent (flowRow k) (flowColumn k) σ := by
      by_cases h : (flowColumn k).map σ.toEmbedding = flowRow k <;>
        simp [subsetImageEvent, h]
    have h := congrArg (fun x : ℤ => (x : ℝ)) (flow_identity σ)
    simpa only [Int.cast_sub, Int.cast_add, Int.cast_sum, Int.cast_ofNat,
      r, J, K, hterm] using h

private def flowContact : Equiv.Perm (Fin 5) :=
  ((Equiv.swap 0 3).trans (Equiv.swap 0 2)).trans (Equiv.swap 0 4)

/-- The upper bound in the fixture is attained by a matching. -/
theorem orderFiveFlowFixture_attains_bound :
    ∃ σ : Equiv.Perm (Fin 5),
      (GaussianInt.toComplex orderFiveFlowDirection *
        matchingProduct (GaussianInt.toComplex ∘ orderFiveFlowFirst)
          (GaussianInt.toComplex ∘ orderFiveFlowSecond) σ).re = 1228164224 := by
  refine ⟨flowContact, ?_⟩
  rw [← flowScore_cast]
  exact_mod_cast (show (flowScore flowContact).re = 1228164224 by decide +kernel)

/-- A certificate for every pair of order-five spectra and every support
direction. The cuts, dual potentials, and matching may depend on these
data. Each certificate works for all unitary mixers. -/
def OrderFiveDisjointPairDualTest : Prop :=
  ∀ (a b : Fin 5 → ℂ) (η : ℂ),
    ∃ (m : ℕ) (t : Fin m → OrderFiveDisjointPairCut) (r q : Pair₅ → ℝ)
      (σ : Equiv.Perm (Fin 5)),
      (∀ I J, orderFivePairCost a b η I J + (∑ k, (t k).adjustment I J) ≤ r I + q J) ∧
      orderFivePairOffset a b η + (∑ I, r I) + (∑ J, q J) ≤ (η * matchingProduct a b σ).re

/-- A disjoint-pair certificate for each spectral objective implies the
order-five determinant inclusion. -/
theorem conjecture_five_of_disjoint_pair_dual_test (h : OrderFiveDisjointPairDualTest) :
    Conjecture (Fin 5) := by
  intro a b U hU
  apply (holds_iff_directional a b U).2
  intro η
  obtain ⟨m, t, r, q, σ, hdual, hscore⟩ := h a b η
  exact ⟨σ, (orderFive_spectral_support_le_disjoint_pair_dual a b η U hU t r q hdual).trans
    hscore⟩

end

end MOC
