import MOC.FiniteMinorLaw

/-! An exact obstruction to the linear marked-star relaxation of Zheng's
T85 gap (preprint DOI: 10.13140/RG.2.2.36790.25923).
The evaluation uses the subset-minor identities of Merikoski and Virtanen
(DOI: 10.1016/0024-3795(89)90709-X). This does not give spectral data. -/

open Matrix BigOperators

namespace MOC
namespace ZhengStarObstruction

noncomputable section

abbrev P := Equiv.Perm (Fin 4)

def A : Finset (Fin 4) := {0,1}
def B : Finset (Fin 4) := {0,2}
def S : Finset (Fin 4) := {0,3}
def Ac : Finset (Fin 4) := {2,3}

def indicator (I J : Finset (Fin 4)) (p : P) : ℝ :=
  if J.map p.toEmbedding = I then 1 else 0

/-- The extremal residual objective, after relabeling the marked assignment
as the identity. The four constituents count the defect event, all crossing
assignments, the marked row, and the marked column, respectively. -/
def objective (p : P) : ℝ :=
  indicator S S p + (1 - indicator A B p - indicator Ac B p) -
    indicator B B p - indicator A A p

private theorem map_mem_iff (p : P) {I J : Finset (Fin 4)}
    (h : J.map p.toEmbedding = I) (i : Fin 4) : p i ∈ I ↔ i ∈ J := by
  rw [← h, Finset.mem_map_equiv, p.symm_apply_apply]

private theorem A_ne_Ac : A ≠ Ac := by
  intro h
  have hh : (0 : Fin 4) ∈ Ac := h ▸ (by simp [A] : (0 : Fin 4) ∈ A)
  simp [Ac] at hh

private theorem B_ne_A : B ≠ A := by
  intro h
  have hh : (2 : Fin 4) ∈ A := h ▸ (by simp [B] : (2 : Fin 4) ∈ B)
  simp [A] at hh

private theorem B_ne_Ac : B ≠ Ac := by
  intro h
  have hh : (0 : Fin 4) ∈ Ac := h ▸ (by simp [B] : (0 : Fin 4) ∈ B)
  simp [Ac] at hh

private theorem col_is_crossing (p : P) (h : A.map p.toEmbedding = A) :
    B.map p.toEmbedding ≠ A ∧ B.map p.toEmbedding ≠ Ac := by
  constructor
  · intro h'
    have hh := (map_mem_iff p h 2).mp ((map_mem_iff p h' 2).mpr (by simp [B]))
    simp [A] at hh
  · intro h'
    have ha := (map_mem_iff p h 0).mpr (by simp [A])
    have hb := (map_mem_iff p h' 0).mpr (by simp [B])
    have hAc : Ac = Aᶜ := by ext i; fin_cases i <;> decide
    rw [hAc, Finset.mem_compl] at hb
    exact hb ha

private theorem both_tags_fixed (p : P)
    (ha : A.map p.toEmbedding = A) (hb : B.map p.toEmbedding = B) : p = 1 := by
  apply Equiv.ext
  intro i
  change p i = i
  have h₁ := map_mem_iff p ha i
  have h₂ := map_mem_iff p hb i
  fin_cases i <;> (generalize hval : p _ = v at h₁ h₂ ⊢; fin_cases v <;> simp_all [A,B])

/-- The residual gap is nonnegative at every matching permutation. -/
theorem objective_nonneg (p : P) : 0 ≤ objective p := by
  unfold objective indicator
  by_cases hA : B.map p.toEmbedding = A
  · have hAc : B.map p.toEmbedding ≠ Ac := fun h => A_ne_Ac (hA.symm.trans h)
    have hB : B.map p.toEmbedding ≠ B := fun h => B_ne_A (h.symm.trans hA)
    have hAA : A.map p.toEmbedding ≠ A := fun h => (col_is_crossing p h).1 hA
    rw [if_pos hA, if_neg hAc, if_neg hB, if_neg hAA]
    split_ifs <;> norm_num
  by_cases hAc : B.map p.toEmbedding = Ac
  · have hB : B.map p.toEmbedding ≠ B := fun h => B_ne_Ac (h.symm.trans hAc)
    have hAA : A.map p.toEmbedding ≠ A := fun h => (col_is_crossing p h).2 hAc
    rw [if_neg hA, if_pos hAc, if_neg hB, if_neg hAA]
    split_ifs <;> norm_num
  rw [if_neg hA, if_neg hAc]
  by_cases hB : B.map p.toEmbedding = B
  · by_cases hAA : A.map p.toEmbedding = A
    · have he := both_tags_fixed p hAA hB
      have hSS : S.map p.toEmbedding = S := by
        rw [he]
        exact Finset.map_refl
      rw [if_pos hB, if_pos hAA, if_pos hSS]
      norm_num
    · rw [if_pos hB, if_neg hAA]
      split_ifs <;> norm_num
  · rw [if_neg hB]
    split_ifs <;> norm_num

def evaluation (U : Matrix (Fin 4) (Fin 4) ℂ) : ℝ :=
  ∑ p : P, realSignedWeight U p * objective p

private theorem indicator_eval (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U)
    (I J : Finset (Fin 4)) :
    ∑ p : P, realSignedWeight U p * indicator I J p = subsetMinorSq U I J := by
  have hs := congrArg Complex.re (sum_signedWeight_image_eq_subsetMinorSq U hU I J)
  simp only [Finset.sum_filter, Complex.re_sum, apply_ite, Complex.zero_re,
    Complex.ofReal_re, realSignedWeight] at hs
  rw [← hs]
  apply Finset.sum_congr rfl
  intro p _
  by_cases h : J.map p.toEmbedding = I <;> simp [indicator,h,realSignedWeight]

theorem evaluation_eq (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    evaluation U = subsetMinorSq U S S + (1 - subsetMinorSq U A B - subsetMinorSq U Ac B) -
      subsetMinorSq U B B - subsetMinorSq U A A := by
  simp only [evaluation, objective, mul_sub, mul_add, mul_one, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, indicator_eval U hU, sum_realSignedWeight U hU]

/-- A left-quaternion multiplier with parameters
`(c², cs, cs, -s²)`. -/
def family (c s : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  let w := (c : ℂ)^2
  let v := (c : ℂ)*s
  let z := (s : ℂ)^2
  !![w,-v,-v,z; v,w,z,v; v,-z,w,-v; -z,-v,v,w]

theorem family_unitary (c s : ℝ) (h : c^2 + s^2 = 1) : IsUnitary (family c s) := by
  have hc : (c : ℂ)^2 + (s : ℂ)^2 = 1 := by exact_mod_cast h
  have hnorm : (c : ℂ)^4 + 2*((c : ℂ)*s)^2 + (s : ℂ)^4 = 1 := by
    calc
      _ = ((c : ℂ)^2+(s : ℂ)^2)^2 := by ring
      _ = 1 := by rw [hc,one_pow]
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [family, Matrix.mul_apply, Fin.sum_univ_four, Matrix.conjTranspose_apply,
      Matrix.one_apply, Complex.conj_ofReal, map_pow, map_mul, map_neg] <;>
    first | (ring; done) | linear_combination hnorm

/-- The normalized marked-star gap is negative throughout an explicit open
interval of orthogonal mixers, with no spectral or numerical search. -/
theorem family_eval (c s : ℝ) (h : c^2 + s^2 = 1) :
    evaluation (family c s) = 2*s^4*(1-2*c^4) := by
  have hU := family_unitary c s h
  rw [evaluation_eq _ hU]
  simp only [S,A,B,Ac]
  repeat rw [subsetMinorSq_pair _ hU (by decide) (by decide)]
  simp [family, ← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_sub,
    ← Complex.ofReal_neg, Complex.normSq_ofReal]
  simp only [← Complex.ofReal_add, Complex.normSq_ofReal]
  linear_combination -(c^2+s^2+1)*(c^4+2*c^2*s^2-s^4+1) * h

theorem family_eval_neg (c s : ℝ) (h : c^2 + s^2 = 1) (hs : s ≠ 0)
    (hc : 1 < 2*c^4) : evaluation (family c s) < 0 := by
  rw [family_eval c s h]
  exact mul_neg_of_pos_of_neg (mul_pos (by norm_num) (by positivity))
    (sub_neg.mpr hc)

/-- The five displayed two-minors of this family already preclude a common
nonnegative coupling of subset images; other minor constraints are unnecessary. -/
theorem no_five_event_law (c s : ℝ) (h : c^2 + s^2 = 1) (hs : s ≠ 0)
    (hc : 1 < 2*c^4) (w : P → ℝ) (hw : ∀ p, 0 ≤ w p)
    (hmass : ∑ p, w p = 1)
    (hm : ∀ I J : Finset (Fin 4),
      (I,J) = (S,S) ∨ (I,J) = (A,B) ∨ (I,J) = (Ac,B) ∨
        (I,J) = (B,B) ∨ (I,J) = (A,A) →
      (∑ p, w p * indicator I J p) = subsetMinorSq (family c s) I J) : False := by
  have hnonneg : 0 ≤ ∑ p, w p * objective p :=
    Finset.sum_nonneg (fun p _ => mul_nonneg (hw p) (objective_nonneg p))
  have he : (∑ p, w p * objective p) = evaluation (family c s) := by
    rw [evaluation_eq _ (family_unitary c s h)]
    simp only [objective, mul_sub, mul_add, mul_one, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, hmass, hm S S (Or.inl rfl), hm A B (Or.inr (Or.inl rfl)),
      hm Ac B (Or.inr (Or.inr (Or.inl rfl))), hm B B (Or.inr (Or.inr (Or.inr (Or.inl rfl)))),
      hm A A (Or.inr (Or.inr (Or.inr (Or.inr rfl))))]
  rw [he] at hnonneg
  exact (not_lt_of_ge hnonneg) (family_eval_neg c s h hs hc)

end

end ZhengStarObstruction
