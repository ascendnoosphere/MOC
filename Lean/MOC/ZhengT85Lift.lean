import MOC.FourMatchingPolarization
import Mathlib.Tactic.Linarith

/-! Projected coordinates for Zheng's T85 case (preprint DOI
10.13140/RG.2.2.36790.25923, Section 5 and Appendix A).
The proof uses the indicated bracket relations and linear elimination, not
an enumeration of feasible contact motifs. -/

namespace MOC

def zhengT85Lift (a1 a2 a3 a4 a5 a6 a7 β h : ℝ) : Fin 14 → ℝ :=
  ![-a4-a7, a2+a4+a5+β, -β, -a2, a7, a3+a6+a7+β, a1-a2-a3-a5-a6-β,
    -a3, a4, -a1+a2+a3, -a3-a7-β, -a2-a4-β, a4+a7+β, a1+β+h]

private def bipartite {R : Type*} [CommRing R] (z : Fin 8 → R) (i j k l : Fin 8) :=
  (z 0 - z i) * (z 1 - z j) * (z 2 - z k) * (z 3 - z l)

private theorem f0_brackets {R : Type*} [CommRing R] (z : Fin 8 → R) :
    bipartite z 4 5 6 7 = (let m := fourBracketLift z; 2 * m 0 + (m 1) + (m 2) + (m 3) + (m 4) + (m 5) + (m 6) + (m 7) + (m 8) + 2 * m 9 + (m 10) + (m 11) + (m 12) + (m 13)) := by
  simp [bipartite,fourBracketLift]
  ring

private theorem f5_brackets {R : Type*} [CommRing R] (z : Fin 8 → R) :
    bipartite z 4 7 6 5 = (let m := fourBracketLift z; (m 0) + (m 2) + (m 3) + (m 4) + (m 9) + (m 10) + (m 12) + (m 13)) := by
  simp [bipartite,fourBracketLift]
  ring

private theorem f7_brackets {R : Type*} [CommRing R] (z : Fin 8 → R) :
    bipartite z 5 4 7 6 = (let m := fourBracketLift z; (m 0) + (m 1) + (m 2) + (m 3) + (m 5) + (m 6) + (m 7) + 2 * m 9 + (m 10) + (m 11) + (m 12) + (m 13)) := by
  simp [bipartite,fourBracketLift]
  ring

private theorem f9_brackets {R : Type*} [CommRing R] (z : Fin 8 → R) :
    bipartite z 5 6 7 4 = (let m := fourBracketLift z; (m 2) + (m 3) + (m 7) + (m 9) + (m 13)) := by
  simp [bipartite,fourBracketLift]
  ring

private theorem f14_brackets {R : Type*} [CommRing R] (z : Fin 8 → R) :
    bipartite z 6 5 4 7 = (let m := fourBracketLift z; (m 0) + (m 2) + (m 7) + (m 8) + (m 9) + (m 11) + (m 12) + (m 13)) := by
  simp [bipartite,fourBracketLift]
  ring

private theorem f18_brackets {R : Type*} [CommRing R] (z : Fin 8 → R) :
    bipartite z 7 4 5 6 = (let m := fourBracketLift z; (m 9) + (m 10) + (m 11) + (m 12) + (m 13)) := by
  simp [bipartite,fourBracketLift]
  ring

private theorem f17_brackets {R : Type*} [CommRing R] (z : Fin 8 → R) :
    bipartite z 6 7 5 4 = (let m := fourBracketLift z; (m 2) + (m 13)) := by
  simp [bipartite,fourBracketLift]
  ring

private theorem f15_brackets {R : Type*} [CommRing R] (z : Fin 8 → R) :
    bipartite z 6 5 7 4 = (let m := fourBracketLift z; (m 2) + (m 7) + (m 9) + (m 13)) := by
  simp [bipartite,fourBracketLift]
  ring

private theorem f11_brackets {R : Type*} [CommRing R] (z : Fin 8 → R) :
    bipartite z 5 7 6 4 = (let m := fourBracketLift z; (m 2) + (m 3) + (m 9) + (m 13)) := by
  simp [bipartite,fourBracketLift]
  ring

private theorem f6_brackets {R : Type*} [CommRing R] (z : Fin 8 → R) :
    bipartite z 5 4 6 7 = (let m := fourBracketLift z; (m 0) + (m 1) + (m 2) + (m 3) + (m 5) + (m 6) + (m 7) + (m 8) + 2 * m 9 + (m 10) + (m 11) + (m 12) + (m 13)) := by
  simp [bipartite,fourBracketLift]
  ring

private theorem f4_brackets {R : Type*} [CommRing R] (z : Fin 8 → R) :
    bipartite z 4 7 5 6 = (let m := fourBracketLift z; (m 0) + (m 1) + (m 2) + (m 3) + (m 4) + (m 9) + (m 10) + (m 11) + (m 12) + (m 13)) := by
  simp [bipartite,fourBracketLift]
  ring

private theorem f12_brackets {R : Type*} [CommRing R] (z : Fin 8 → R) :
    bipartite z 6 4 5 7 = (let m := fourBracketLift z; (m 0) + (m 2) + (m 5) + (m 7) + (m 8) + (m 9) + (m 10) + (m 11) + (m 12) + (m 13)) := by
  simp [bipartite,fourBracketLift]
  ring

private theorem f1_brackets {R : Type*} [CommRing R] (z : Fin 8 → R) :
    bipartite z 4 5 7 6 = (let m := fourBracketLift z; (m 0) + (m 1) + (m 2) + (m 3) + (m 4) + (m 5) + (m 6) + (m 7) + 2 * m 9 + (m 10) + (m 11) + (m 12) + (m 13)) := by
  simp [bipartite,fourBracketLift]
  ring

private theorem f23_brackets {R : Type*} [CommRing R] (z : Fin 8 → R) :
    bipartite z 7 6 5 4 = (let m := fourBracketLift z; (m 13)) := by
  simp [bipartite,fourBracketLift]
set_option maxHeartbeats 1200000 in
/-- The six projected contacts determine the canonical real lift from the
seven radial gaps, the block-defect correction, and the projected pivot.
For upper support use the negative projection, so the final argument h
is the negative of the upper support height. -/
theorem zhengT85_projected_lift (z : Fin 8 → ℂ) (η : ℂ) :
    let p0 := bipartite z 4 5 6 7
    let p5 := bipartite z 4 7 6 5
    let p7 := bipartite z 5 4 7 6
    let p9 := bipartite z 5 6 7 4
    let p14 := bipartite z 6 5 4 7
    let p18 := bipartite z 7 4 5 6
    let p17 := bipartite z 6 7 5 4
    let p15 := bipartite z 6 5 7 4
    let p11 := bipartite z 5 7 6 4
    let p6 := bipartite z 5 4 6 7
    let p4 := bipartite z 4 7 5 6
    let p12 := bipartite z 6 4 5 7
    let p1 := bipartite z 4 5 7 6
    let p23 := bipartite z 7 6 5 4
    let m (k : Fin 14) := (η * fourBracketLift z k).re
    let H := (η * p0).re
    let a1 := (η * p17).re - H
    let a2 := (η * p15).re - H
    let a3 := (η * p11).re - H
    let a4 := (η * p6).re - H
    let a5 := (η * p4).re - H
    let a6 := (η * p12).re - H
    let a7 := (η * p1).re - H
    let β := (η * p23).re - (η * p17).re
    (η * p5).re = H → (η * p7).re = H → (η * p9).re = H →
      (η * p14).re = H → (η * p18).re = H →
      m = zhengT85Lift a1 a2 a3 a4 a5 a6 a7 β H := by
  intro p0 p5 p7 p9 p14 p18 p17 p15 p11 p6 p4 p12 p1 p23 m H a1 a2 a3 a4 a5 a6 a7 β h5 h7 h9 h14 h18
  have h0 : (η * p0).re = H := rfl
  have h17 : (η * p17).re = H + a1 := by dsimp [a1]; ring
  have h15 : (η * p15).re = H + a2 := by dsimp [a2]; ring
  have h11 : (η * p11).re = H + a3 := by dsimp [a3]; ring
  have h6 : (η * p6).re = H + a4 := by dsimp [a4]; ring
  have h4 : (η * p4).re = H + a5 := by dsimp [a5]; ring
  have h12 : (η * p12).re = H + a6 := by dsimp [a6]; ring
  have h1 : (η * p1).re = H + a7 := by dsimp [a7]; ring
  have h23 : (η * p23).re = H + a1 + β := by dsimp [a1, β]; ring
  have hmul (x : ℂ) : (η * (2 * x)).re = 2 * (η * x).re := by
    rw [mul_left_comm η 2 x]
    norm_num [Complex.mul_re]
  simp only [p0, f0_brackets, p5, f5_brackets, p7, f7_brackets, p9, f9_brackets, p14, f14_brackets, p18, f18_brackets, p17, f17_brackets, p15, f15_brackets, p11, f11_brackets, p6, f6_brackets, p4, f4_brackets, p12, f12_brackets, p1, f1_brackets, p23, f23_brackets,
    mul_add,Complex.add_re,hmul] at h0 h5 h7 h9 h14 h18 h17 h15 h11 h6 h4 h12 h1 h23
  funext i
  fin_cases i <;> simp [zhengT85Lift,m,-Complex.mul_re] <;>
    linarith only [h0, h5, h7, h9, h14, h18, h17, h15, h11, h6, h4, h12, h1, h23]

end MOC
