import MOC.QuaternionMixerParity
import Mathlib.Data.ZMod.Basic

/-! The quaternion basis sign cocycle on the binary coordinate group.
Write the basis label (a,b) for i^a j^b; its multiplication sign is
(-1)^(a*c + b*c + b*d). -/

namespace MOC.QuaternionIntrinsic

abbrev BinaryLabels := ZMod 2 × ZMod 2

private theorem zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  have h := x.val_lt
  rcases show x.val = 0 ∨ x.val = 1 by omega with hx | hx
  · exact Or.inl ((ZMod.val_eq_zero _).mp hx)
  · exact Or.inr ((ZMod.val_eq_one (by decide) _).mp hx)

private theorem charTwo (x : ZMod 2) : x+x=0 := by
  rw [← two_mul]
  have h : (2 : ZMod 2) = 0 := by decide
  simp [h]

theorem binaryLabels_exponentTwo (x : BinaryLabels) : x+x=0 := by
  exact Prod.ext (charTwo x.1) (charTwo x.2)

theorem binaryLabels_card : Fintype.card BinaryLabels = 4 := by
  simp [BinaryLabels, Fintype.card_prod, ZMod.card]

private noncomputable def bitSign (x : ZMod 2) : ℝ := if x=0 then 1 else -1

private theorem bitSign_add (x y : ZMod 2) : bitSign (x+y) = bitSign x * bitSign y := by
  by_cases hx : x=0
  · simp [bitSign, hx]
  by_cases hy : y=0
  · simp [bitSign, hy]
  have he : x=y := (zero_or_one x).resolve_left hx |>.trans ((zero_or_one y).resolve_left hy).symm
  rw [he, charTwo]
  simp [bitSign, hy]

private theorem bitSign_sq (x : ZMod 2) : bitSign x^2 = 1 := by
  unfold bitSign
  split_ifs <;> norm_num

/-- Bilinear sign in the quaternion basis (1,i,j,ij). -/
noncomputable def quaternionBinarySign (p j : BinaryLabels) : ℝ :=
  bitSign (p.1*j.1 + p.2*j.1 + p.2*j.2)

private theorem binaryQuadratic_ne_zero (p : BinaryLabels) (hp : p ≠ 0) :
    p.1*p.1+p.2*p.1+p.2*p.2 ≠ 0 := by
  intro h
  have hs (x : ZMod 2) : x*x=x := by
    rcases zero_or_one x with he | he <;> simp [he]
  rw [hs, hs, mul_comm p.2 p.1] at h
  have hfact : (p.1+1)*(p.2+1)=1 := by linear_combination h
  have h₁ : p.1 ≠ 1 := by
    intro he
    rw [he, charTwo, zero_mul] at hfact
    exact zero_ne_one hfact
  have h₂ : p.2 ≠ 1 := by
    intro he
    rw [he, charTwo, mul_zero] at hfact
    exact zero_ne_one hfact
  exact hp (Prod.ext ((zero_or_one p.1).resolve_right h₁) ((zero_or_one p.2).resolve_right h₂))

/-- The explicit binary quaternion cocycle satisfies the intrinsic sign
conditions. Only the bit character and anisotropic quadratic norm
are used, with no table of mixer entries or permutations. -/
theorem quaternionBinarySign_basisSigning : BasisSigning quaternionBinarySign := by
  apply basisSigning_of_bicharacter binaryLabels_card binaryLabels_exponentTwo
  · intro p j
    exact bitSign_sq _
  · intro p q j
    unfold quaternionBinarySign
    rw [show (p+q).1*j.1 + (p+q).2*j.1 + (p+q).2*j.2 =
      (p.1*j.1 + p.2*j.1 + p.2*j.2) + (q.1*j.1 + q.2*j.1 + q.2*j.2) by
        change (p.1+q.1)*j.1 + (p.2+q.2)*j.1 + (p.2+q.2)*j.2 = _
        ring, bitSign_add]
  · intro p i j
    unfold quaternionBinarySign
    rw [show p.1*(i+j).1 + p.2*(i+j).1 + p.2*(i+j).2 =
      (p.1*i.1 + p.2*i.1 + p.2*i.2) + (p.1*j.1 + p.2*j.1 + p.2*j.2) by
        change p.1*(i.1+j.1) + p.2*(i.1+j.1) + p.2*(i.2+j.2) = _
        ring, bitSign_add]
  · intro p hp
    simp [quaternionBinarySign, bitSign, binaryQuadratic_ne_zero p hp]

/-- Concrete binary quaternion table with near-balanced coefficients:
arbitrary complex spectra are allowed. -/
theorem holds_nearBalanced_quaternionBinary
    (a b : BinaryLabels → ℂ) (u : BinaryLabels) {x t : ℝ}
    (hx : 0 < x) (ht : 0 < t) (ht' : t ≤ 1) (hc : 0 ≤ t^3+3*t-2)
    (hU : IsUnitary (signedKleinMixerTable quaternionBinarySign
      (fun l => x * if l = u then t else 1)))
    (hd : (signedKleinMixerTable quaternionBinarySign (fun l => x * if l = u then t else 1)).det = 1) :
    Holds a b (signedKleinMixerTable quaternionBinarySign
      (fun l => x * if l = u then t else 1)) :=
  holds_nearBalanced_signedKleinMixerTable binaryLabels_card binaryLabels_exponentTwo
    a b quaternionBinarySign quaternionBinarySign_basisSigning u hx ht ht' hc hU hd

end MOC.QuaternionIntrinsic
