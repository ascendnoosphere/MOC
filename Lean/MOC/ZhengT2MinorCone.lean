import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Constructive allocation for the T2 support-contact cone in Zheng,
preprint DOI 10.13140/RG.2.2.36790.25923. This lemma uses no facet data. -/

namespace MOC.ZhengT2MinorCone

/-- Allocate three ordinary-marker coefficients subject to five upper bounds.
This is the explicit optimization used in the facet-free T2 decomposition. -/
theorem allocate (A B C E F T : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hE : 0 ≤ E) (hF : 0 ≤ F) (hT : 0 ≤ T)
    (hACE : T ≤ A+C+E) (hBC : T ≤ B+C)
    (hAF : T ≤ A+F) (hBF : T ≤ B+F) :
    ∃ a c d : ℝ, 0 ≤ a ∧ 0 ≤ c ∧ 0 ≤ d ∧ a+c+d = T ∧
      a ≤ A ∧ c ≤ C ∧ d ≤ E ∧ a+d ≤ B ∧ c+d ≤ F := by
  by_cases h : T ≤ A+C
  · let a := min (min A B) T
    have ha : 0 ≤ a := le_min (le_min hA hB) hT
    have haA : a ≤ A := (min_le_left _ _).trans (min_le_left _ _)
    have haB : a ≤ B := (min_le_left _ _).trans (min_le_right _ _)
    have haT : a ≤ T := min_le_right _ _
    have hcC : T-C ≤ a := le_min (le_min (by linarith) (by linarith)) (by linarith)
    have hcF : T-F ≤ a := le_min (le_min (by linarith) (by linarith)) (by linarith)
    refine ⟨a, T-a, 0, ha, by linarith, le_rfl, by ring, haA, by linarith, hE, ?_, ?_⟩
    · linarith
    · linarith
  · refine ⟨A, C, T-A-C, hA, hC, by linarith, by ring,
      le_rfl, le_rfl, by linarith, by linarith, by linarith⟩

/-- The residual coefficients giving the constructive marker representation of
the seven independent coordinates. Its hypotheses are exactly nonnegativity of
eleven specific gaps in the T2 table, not a complete facet classification. -/
theorem coefficients (A B C E F G H : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hE : 0 ≤ E)
    (hF : 0 ≤ F) (hG : 0 ≤ G) (hH : 0 ≤ H)
    (h16 : 0 ≤ B+C-H+G) (h18 : 0 ≤ A+C+E-(B+C-H))
    (h20 : 0 ≤ A+F-(B+C-H)) (h21 : 0 ≤ B+F-(B+C-H)) :
    ∃ a b c d e f g h i j k : ℝ,
      0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧ 0 ≤ e ∧ 0 ≤ f ∧
      0 ≤ g ∧ 0 ≤ h ∧ 0 ≤ i ∧ 0 ≤ j ∧ 0 ≤ k ∧ j=d ∧
      A=a+k ∧ B=a+i+j ∧ C=c+e ∧ E=h+j ∧ F=c+f+j ∧
      G=b+g ∧ H=b+e+i := by
  let R := B+C-H
  let T := max 0 R
  have hT : 0 ≤ T := le_max_left _ _
  have hTR : R ≤ T := le_max_right _ _
  have hT16 : T ≤ R+G := max_le h16 (by linarith)
  have hT18 : T ≤ A+C+E := max_le (by linarith) (by dsimp [R]; linarith)
  have hT19 : T ≤ B+C := max_le (by linarith) (by dsimp [R]; linarith)
  have hT20 : T ≤ A+F := max_le (by linarith) (by dsimp [R]; linarith)
  have hT21 : T ≤ B+F := max_le (by linarith) (by dsimp [R]; linarith)
  obtain ⟨a,c,d,ha,hc,hd,hsum,haA,hcC,hdE,hadB,hcdF⟩ :=
    allocate A B C E F T hA hB hC hE hF hT hT18 hT19 hT20 hT21
  refine ⟨a,T-R,c,d,C-c,F-c-d,G-(T-R),E-d,B-a-d,d,A-a,
    ha,by linarith,hc,hd,by linarith,by linarith,by linarith,by linarith,
    by linarith,hd,by linarith,rfl,by ring,by ring,by ring,by ring,by ring,
    by ring,?_⟩
  dsimp [R]
  linarith

end MOC.ZhengT2MinorCone
