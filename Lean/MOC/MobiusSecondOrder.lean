import MOC.SpectralGap
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! The centered Möbius energy at a positive gap maximum has nonnegative
second variation in both real directions. Expanding it yields a bound
on the signed spectra's second and fourth moments. -/

open BigOperators Filter
open Matrix
open scoped ComplexConjugate Topology

namespace MOC

noncomputable section
private theorem realMapReal (t : ℝ) : algebraMap ℝ ℝ t = t := rfl
private theorem realMapComplex (t : ℝ) : algebraMap ℝ ℂ t = (t : ℂ) := rfl

/-- A quadratic expansion along a real line, with a continuous cubic remainder. -/
private def Quad {K : Type*} [Ring K] [Algebra ℝ K] [TopologicalSpace K]
    (f : ℝ → K) (a b c : K) : Prop :=
  ∃ R : ℝ → K, ContinuousAt R 0 ∧ ∀ᶠ t in 𝓝 (0 : ℝ),
    f t = a + algebraMap ℝ K t * b + algebraMap ℝ K t ^ 2 * c +
      algebraMap ℝ K t ^ 3 * R t

private theorem Quad.congr {K : Type*} [Ring K] [Algebra ℝ K] [TopologicalSpace K]
    {f g : ℝ → K} {a b c : K} (h : Quad f a b c) (he : f =ᶠ[𝓝 (0 : ℝ)] g) :
    Quad g a b c := by
  obtain ⟨r, hr, h⟩ := h
  exact ⟨r, hr, he.symm.trans h⟩

private theorem Quad.continuousAt {K : Type*} [Ring K] [Algebra ℝ K] [TopologicalSpace K]
    [IsTopologicalRing K] [ContinuousSMul ℝ K] {f : ℝ → K} {a b c : K}
    (h : Quad f a b c) : ContinuousAt f 0 := by
  obtain ⟨r, hr, he⟩ := h
  have hc := (continuous_algebraMap ℝ K).continuousAt (x := (0 : ℝ))
  exact ContinuousAt.congr
    (((continuousAt_const.add (hc.mul continuousAt_const)).add
      ((hc.pow 2).mul continuousAt_const)).add ((hc.pow 3).mul hr)) (he.mono fun _ h => h.symm)

private theorem Quad.const {K : Type*} [Ring K] [Algebra ℝ K] [TopologicalSpace K]
    (a : K) : Quad (fun _ => a) a 0 0 :=
  ⟨fun _ => 0, continuousAt_const, Eventually.of_forall fun _ => by simp⟩

private theorem Quad.at_zero {K : Type*} [Ring K] [Algebra ℝ K] [TopologicalSpace K]
    {f : ℝ → K} {a b c : K} (h : Quad f a b c) : f 0 = a := by
  obtain ⟨_, _, h⟩ := h
  simpa using h.self_of_nhds

section Quad
variable {K : Type*} [CommRing K] [Algebra ℝ K] [TopologicalSpace K]
  [IsTopologicalRing K] [ContinuousSMul ℝ K]
variable {f g : ℝ → K} {a₀ a₁ a₂ b₀ b₁ b₂ : K}

omit [ContinuousSMul ℝ K] in
private theorem Quad.add (h : Quad f a₀ a₁ a₂) (h' : Quad g b₀ b₁ b₂) :
    Quad (fun t => f t + g t) (a₀ + b₀) (a₁ + b₁) (a₂ + b₂) := by
  obtain ⟨r, hr, he⟩ := h
  obtain ⟨s, hs, hf⟩ := h'
  refine ⟨fun t => r t + s t, hr.add hs, ?_⟩
  filter_upwards [he, hf] with t ht hu
  rw [ht, hu]
  ring

omit [ContinuousSMul ℝ K] in
private theorem Quad.neg (h : Quad f a₀ a₁ a₂) :
    Quad (fun t => -f t) (-a₀) (-a₁) (-a₂) := by
  obtain ⟨r, hr, he⟩ := h
  refine ⟨fun t => -r t, hr.neg, ?_⟩
  filter_upwards [he] with t ht
  rw [ht]
  ring

omit [ContinuousSMul ℝ K] in
private theorem Quad.sub (h : Quad f a₀ a₁ a₂) (h' : Quad g b₀ b₁ b₂) :
    Quad (fun t => f t - g t) (a₀ - b₀) (a₁ - b₁) (a₂ - b₂) := by
  simpa only [sub_eq_add_neg] using h.add h'.neg

private theorem Quad.mul (h : Quad f a₀ a₁ a₂) (h' : Quad g b₀ b₁ b₂) :
    Quad (fun t => f t * g t) (a₀ * b₀) (a₁ * b₀ + a₀ * b₁)
      (a₂ * b₀ + a₁ * b₁ + a₀ * b₂) := by
  have hg := h'.continuousAt
  obtain ⟨r, hr, he⟩ := h
  obtain ⟨s, hs, hf⟩ := h'
  let z := algebraMap ℝ K
  let R (t : ℝ) := r t * g t + (a₀ + z t * a₁ + z t ^ 2 * a₂) * s t +
    a₁ * b₂ + a₂ * b₁ + z t * a₂ * b₂
  have hz : ContinuousAt z 0 := (continuous_algebraMap ℝ K).continuousAt
  refine ⟨R, ?_, ?_⟩
  · dsimp [R]
    fun_prop
  · filter_upwards [he, hf] with t ht hu
    dsimp only [R, z]
    rw [ht, hu]
    ring

omit [ContinuousSMul ℝ K] in
private theorem Quad.sum {ι : Type*} (s : Finset ι) (g : ι → ℝ → K) (a b c : ι → K)
    (h : ∀ i ∈ s, Quad (g i) (a i) (b i) (c i)) :
    Quad (fun t => ∑ i ∈ s, g i t) (∑ i ∈ s, a i) (∑ i ∈ s, b i) (∑ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Quad.const (0 : K)
  | @insert i s hi ih =>
    simp_rw [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self ..)).add
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

private theorem Quad.pow {f : ℝ → K} {q : K} (h : Quad f 1 0 q) (n : ℕ) :
    Quad (fun t => f t ^ n) 1 0 ((n : K) * q) := by
  induction n with
  | zero => simpa using Quad.const (1 : K)
  | succ m ih =>
    simpa only [pow_succ, mul_one, zero_mul, one_mul, zero_add, add_zero, Nat.cast_succ,
      add_mul] using ih.mul h

end Quad

private theorem Quad.second_nonneg {f : ℝ → ℝ} {a c : ℝ} (h : Quad f a 0 c)
    (hm : ∀ᶠ t in 𝓝 (0 : ℝ), a ≤ f t) : 0 ≤ c := by
  by_contra! hc
  obtain ⟨r, hr, h⟩ := h
  let G (t : ℝ) := c + t * r t
  have hG : ContinuousAt G 0 := continuousAt_const.add (continuousAt_id.mul hr)
  have hneg : ∀ᶠ t in 𝓝 (0 : ℝ), G t < 0 := by
    change ∀ᶠ t in 𝓝 (0 : ℝ), G t ∈ Set.Iio 0
    apply hG.eventually_mem
    apply Iio_mem_nhds
    simpa [G] using hc
  have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  obtain ⟨t, ⟨⟨⟨ht, hn⟩, hv⟩, hp⟩⟩ :=
    (((h.and hneg).and hm).filter_mono nhdsWithin_le_nhds).and hpos |>.exists
  have he : f t = a + t ^ 2 * G t := by
    simp only [realMapReal, mul_zero, add_zero] at ht
    rw [ht]
    dsimp [G]
    ring
  exact (not_lt_of_ge hv) (by rw [he]; exact add_lt_of_neg_right _ (mul_neg_of_pos_of_neg (sq_pos_of_pos hp) hn))


private theorem Quad.conj {f : ℝ → ℂ} {a b c : ℂ} (h : Quad f a b c) :
    Quad (fun t => conj (f t)) (conj a) (conj b) (conj c) := by
  obtain ⟨r, hr, he⟩ := h
  refine ⟨fun t => conj (r t), Complex.continuous_conj.continuousAt.comp hr, ?_⟩
  filter_upwards [he] with t ht
  rw [ht]
  simp only [map_add, map_mul, map_pow, realMapComplex, Complex.conj_ofReal]

private theorem Quad.re {f : ℝ → ℂ} {a b c : ℂ} (h : Quad f a b c) :
    Quad (fun t => (f t).re) a.re b.re c.re := by
  obtain ⟨r, hr, he⟩ := h
  refine ⟨fun t => (r t).re, Complex.continuous_re.continuousAt.comp hr, ?_⟩
  filter_upwards [he] with t ht
  rw [ht]
  simp only [realMapComplex, realMapReal,
    Complex.add_re, ← Complex.ofReal_pow, Complex.re_ofReal_mul]

private theorem Quad.normSq {f : ℝ → ℂ} {a b c : ℂ} (h : Quad f a b c) :
    Quad (fun t => Complex.normSq (f t)) (Complex.normSq a) (2 * (b * conj a).re)
      (Complex.normSq b + 2 * (c * conj a).re) := by
  have hpair (x y : ℂ) : (x * conj y).re = (y * conj x).re := by
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  convert (h.mul h.conj).re using 1
  · funext t; rw [Complex.mul_conj, Complex.ofReal_re]
  · rw [Complex.mul_conj, Complex.ofReal_re]
  · rw [Complex.add_re, hpair a b]
    ring
  · rw [Complex.add_re, Complex.add_re, Complex.mul_conj, Complex.ofReal_re, hpair a c]
    ring

private theorem quad_mobius_line (p x : ℂ) :
    Quad (fun t : ℝ => x / (1 - (t : ℂ) * p * x)) x (p * x ^ 2) (p ^ 2 * x ^ 3) := by
  let v := p * x
  let D (t : ℝ) := 1 - (t : ℂ) * v
  have hc : ContinuousAt D 0 := by dsimp [D]; fun_prop
  have hD : D 0 ≠ 0 := by simp [D]
  refine ⟨fun t => x * v ^ 3 / D t, continuousAt_const.div hc hD, ?_⟩
  filter_upwards [hc.eventually_ne hD] with t ht
  rw [realMapComplex]
  rw [mul_assoc (t : ℂ) p x]
  change x / D t = _
  field_simp [ht]
  dsimp only [D, v]
  ring

private theorem quad_one_sub_mul (p x : ℂ) :
    Quad (fun t : ℝ => 1 - (t : ℂ) * p * x) 1 (-(p * x)) 0 := by
  refine ⟨fun _ => 0, continuousAt_const, Eventually.of_forall fun _ => ?_⟩
  rw [realMapComplex]
  ring

private theorem Quad.prod_one {ι : Type*} (S : Finset ι) (f : ι → ℝ → ℂ) (d : ι → ℂ)
    (h : ∀ i ∈ S, Quad (f i) 1 (d i) 0) :
    Quad (fun t => ∏ i ∈ S, f i t) 1 (∑ i ∈ S, d i)
      (((∑ i ∈ S, d i) ^ 2 - ∑ i ∈ S, d i ^ 2) / 2) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using Quad.const (1 : ℂ)
  | @insert i s hi ih =>
    simp_rw [Finset.prod_insert hi, Finset.sum_insert hi]
    convert (h i (Finset.mem_insert_self ..)).mul
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj))) using 1 <;> ring


variable {J : Type*} [Fintype J]

private def mobiusPath (x : J → ℂ) (p : ℂ) (t : ℝ) (j : J) : ℂ :=
  x j / (1 - (t : ℂ) * p * x j)

private def centeredMobiusEnergy (n : ℕ) (x : J → ℂ) (p : ℂ) (t : ℝ) : ℝ :=
  (∑ j, Complex.normSq (mobiusPath x p t j)) -
    Complex.normSq (∑ j, mobiusPath x p t j) / (2 * (n : ℝ))

private def centeredMobiusDenominator (x : J → ℂ) (p : ℂ) (t : ℝ) : ℂ :=
  ∏ j, (1 - (t : ℂ) * p * x j)

private theorem quad_normSq_mobius_line (p x : ℂ) :
    Quad (fun t : ℝ => Complex.normSq (x / (1 - (t : ℂ) * p * x)))
      (Complex.normSq x) (2 * (p * ((Complex.normSq x : ℂ) * x)).re)
      (Complex.normSq p * Complex.normSq x ^ 2 +
        2 * (p ^ 2 * ((Complex.normSq x : ℂ) * x ^ 2)).re) := by
  have h₁ : (p * x ^ 2) * conj x = p * ((Complex.normSq x : ℂ) * x) := by
    rw [← Complex.mul_conj]
    ring
  have h₂ : (p ^ 2 * x ^ 3) * conj x = p ^ 2 * ((Complex.normSq x : ℂ) * x ^ 2) := by
    rw [← Complex.mul_conj]
    ring
  simpa only [h₁, h₂, map_mul, map_pow] using (quad_mobius_line p x).normSq

private theorem quad_centeredMobiusEnergy (n : ℕ) (x : J → ℂ)
    (h₁ : ∑ j, x j = 0)
    (hE : ∑ j, Complex.normSq (x j) = 1)
    (h₃ : ∑ j, (Complex.normSq (x j) : ℂ) * x j = 0)
    (p : ℂ) :
    Quad (centeredMobiusEnergy n x p) 1 0
      (Complex.normSq p *
        ((∑ j, Complex.normSq (x j) ^ 2) - Complex.normSq (∑ j, (x j) ^ 2) / (2 * (n : ℝ))) +
        2 * (p ^ 2 * ∑ j, (Complex.normSq (x j) : ℂ) * (x j) ^ 2).re) := by
  let m₂ : ℂ := ∑ j, x j ^ 2
  let h₂ : ℂ := ∑ j, (Complex.normSq (x j) : ℂ) * x j ^ 2
  let q : ℝ := ∑ j, Complex.normSq (x j) ^ 2
  have hsum :
      Quad (fun t => ∑ j, mobiusPath x p t j) 0 (p * m₂) (∑ j, p ^ 2 * (x j) ^ 3) := by
    have h := Quad.sum Finset.univ (fun j t => mobiusPath x p t j) x
      (fun j => p * (x j) ^ 2) (fun j => p ^ 2 * (x j) ^ 3)
      (fun j _ => quad_mobius_line p (x j))
    rwa [← Finset.mul_sum, h₁] at h
  have hcent : Quad (fun t => Complex.normSq (∑ j, mobiusPath x p t j)) 0 0
      (Complex.normSq p * Complex.normSq m₂) := by
    simpa using hsum.normSq
  have hcent' :
      Quad (fun t => Complex.normSq (∑ j, mobiusPath x p t j) / (2 * (n : ℝ))) 0 0
        (Complex.normSq p * Complex.normSq m₂ / (2 * (n : ℝ))) := by
    simpa only [div_eq_mul_inv, zero_mul, mul_zero, add_zero] using
      hcent.mul (Quad.const ((2 * (n : ℝ))⁻¹))
  have hmain := Quad.sum Finset.univ (fun j t => Complex.normSq (mobiusPath x p t j))
    (fun j => Complex.normSq (x j))
    (fun j => 2 * (p * ((Complex.normSq (x j) : ℂ) * x j)).re)
    (fun j => Complex.normSq p * Complex.normSq (x j) ^ 2 +
      2 * (p ^ 2 * ((Complex.normSq (x j) : ℂ) * (x j) ^ 2)).re)
    (fun j _ => quad_normSq_mobius_line p (x j))
  have hmain' : Quad (fun t => ∑ j, Complex.normSq (mobiusPath x p t j)) 1 0
      (Complex.normSq p * q + 2 * (p ^ 2 * h₂).re) := by
    simpa only [hE, Finset.sum_add_distrib, ← Finset.mul_sum, ← Complex.re_sum,
      h₃, mul_zero, Complex.zero_re, q, h₂] using hmain
  have he :
      Complex.normSq p * q + 2 * (p ^ 2 * h₂).re -
        Complex.normSq p * Complex.normSq m₂ / (2 * (n : ℝ)) =
        Complex.normSq p * (q - Complex.normSq m₂ / (2 * (n : ℝ))) + 2 * (p ^ 2 * h₂).re := by
    ring
  simpa only [sub_zero, he] using hmain'.sub hcent'

private theorem quad_centeredMobiusDenominator (x : J → ℂ) (h₁ : ∑ j, x j = 0) (p : ℂ) :
    Quad (fun t => Complex.normSq (centeredMobiusDenominator x p t)) 1 0
      (-(p ^ 2 * ∑ j, x j ^ 2).re) := by
  have hd := Quad.prod_one Finset.univ (fun (j : J) (t : ℝ) => 1 - (t : ℂ) * p * x j)
    (fun j => -(p * x j)) (fun j _ => quad_one_sub_mul p (x j))
  have hd₁ : ∑ j, -(p * x j) = 0 := by rw [Finset.sum_neg_distrib, ← Finset.mul_sum, h₁, mul_zero, neg_zero]
  have hd₂ : ∑ j, (-(p * x j)) ^ 2 = p ^ 2 * ∑ j, x j ^ 2 := by
    simp_rw [neg_sq, mul_pow, Finset.mul_sum]
  rw [hd₁, hd₂] at hd
  have he (z : ℂ) : 2 * (-(z : ℂ) / 2).re = -z.re := by
    rw [Complex.div_ofNat_re, Complex.neg_re]
    ring
  simpa only [centeredMobiusDenominator, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_sub,
    Complex.normSq_one, Complex.normSq_zero, map_one, mul_one, zero_mul, mul_zero,
    Complex.zero_re, zero_add, he] using hd.normSq

private theorem norm_le_of_unit_quadratic_re_nonneg (m : ℂ) (q : ℝ)
    (h : ∀ p : ℂ, Complex.normSq p = 1 → 0 ≤ q + (p ^ 2 * m).re) :
    ‖m‖ ≤ q := by
  by_cases hm : m = 0
  · simpa [hm] using h 1 (by simp)
  have hpos : 0 < ‖m‖ := norm_pos_iff.mpr hm
  have hposC : (‖m‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpos.ne'
  obtain ⟨p, hp⟩ := IsAlgClosed.exists_pow_nat_eq (-conj m / (‖m‖ : ℂ)) (n := 2) two_pos
  have hp' := congrArg Complex.normSq hp
  rw [map_pow, map_div₀, Complex.normSq_neg, Complex.normSq_conj,
    Complex.normSq_ofReal, Complex.normSq_eq_norm_sq m, ← sq, div_self (pow_ne_zero _ hpos.ne')] at hp'
  have hn : Complex.normSq p = 1 := (sq_eq_sq₀ (Complex.normSq_nonneg _) zero_le_one).mp
    (by rwa [one_pow])
  have hpM : p ^ 2 * m = -(‖m‖ : ℂ) := by
    rw [hp, div_mul_eq_mul_div, neg_mul, mul_comm (conj m) m, Complex.mul_conj,
      Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
    field_simp [hposC]
    ring
  have hreal := h p hn
  rw [hpM, Complex.neg_re, Complex.ofReal_re] at hreal
  linarith


private theorem centeredMobius_moment_test (n : ℕ) (hn : n ≠ 0) (x : J → ℂ)
    (h₁ : ∑ j, x j = 0)
    (hE : ∑ j, Complex.normSq (x j) = 1)
    (h₃ : ∑ j, (Complex.normSq (x j) : ℂ) * x j = 0)
    (hmin : ∀ p : ℂ, ∀ᶠ t in 𝓝 (0 : ℝ),
      1 ≤ centeredMobiusEnergy n x p t ^ n * Complex.normSq (centeredMobiusDenominator x p t)) :
    ‖(2 * (n : ℂ)) * (∑ j, (Complex.normSq (x j) : ℂ) * x j ^ 2) - ∑ j, x j ^ 2‖ ≤
      (n : ℝ) * (∑ j, Complex.normSq (x j) ^ 2) - Complex.normSq (∑ j, x j ^ 2) / 2 := by
  let m₂ : ℂ := ∑ j, x j ^ 2
  let h₂ : ℂ := ∑ j, (Complex.normSq (x j) : ℂ) * x j ^ 2
  let q : ℝ := ∑ j, Complex.normSq (x j) ^ 2
  change ‖(2 * (n : ℂ)) * h₂ - m₂‖ ≤ (n : ℝ) * q - Complex.normSq m₂ / 2
  apply norm_le_of_unit_quadratic_re_nonneg
  intro p hp
  have hq := ((quad_centeredMobiusEnergy n x h₁ hE h₃ p).pow n).mul
    (quad_centeredMobiusDenominator x h₁ p)
  have hq' : Quad (fun t => centeredMobiusEnergy n x p t ^ n *
      Complex.normSq (centeredMobiusDenominator x p t)) 1 0
        ((n : ℝ) * ((q - Complex.normSq m₂ / (2 * (n : ℝ))) +
          2 * (p ^ 2 * h₂).re) - (p ^ 2 * m₂).re) := by
    simpa only [q, m₂, h₂, hp, one_mul, mul_one, zero_mul, zero_add, add_zero,
      sub_eq_add_neg] using hq
  have htest := hq'.second_nonneg (hmin p)
  have hN : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hqcoeff :
      (n : ℝ) * ((q - Complex.normSq m₂ / (2 * (n : ℝ))) +
        2 * (p ^ 2 * h₂).re) - (p ^ 2 * m₂).re =
      (n : ℝ) * q - Complex.normSq m₂ / 2 +
        (p ^ 2 * ((2 * (n : ℂ)) * h₂ - m₂)).re := by
    rw [mul_sub, Complex.sub_re]
    have he : p ^ 2 * (2 * (n : ℂ) * h₂) = ((2 * (n : ℝ) : ℝ) : ℂ) * (p ^ 2 * h₂) := by
      push_cast
      ring
    rw [he, Complex.re_ofReal_mul]
    field_simp [hN]
    ring
  rwa [hqcoeff] at htest

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- At unit energy with the trace and cubic balances, the centered Möbius
minimum bounds the anisotropic fourth moment of the signed spectra. This
uses a local minimum, not any global assumption about the support envelope. -/
theorem spectral_mobius_moment_test (a b : ι → ℂ)
    (htrace : (∑ i, a i) = ∑ i, b i)
    (henergy : spectralEnergy a b = 1)
    (hcubic : (∑ i, (Complex.normSq (a i) : ℂ) * a i) =
      ∑ i, (Complex.normSq (b i) : ℂ) * b i)
    (hbound : ∀ t : ℂ, (∀ i, 1 - t * a i ≠ 0) → (∀ j, 1 + t * b j ≠ 0) →
      let E := centeredSpectralEnergy (mobiusSpectrum t a) (mobiusSpectrum (-t) b)
      0 < E → 1 ≤ E ^ Fintype.card ι * Complex.normSq (mobiusDenominator a b t)) :
    let x : ι ⊕ ι → ℂ := Sum.elim a (fun i => - b i)
    let n := Fintype.card ι
    ‖(2 * (n : ℂ)) * (∑ j, (Complex.normSq (x j) : ℂ) * x j ^ 2) - ∑ j, x j ^ 2‖ ≤
      (n : ℝ) * (∑ j, Complex.normSq (x j) ^ 2) - Complex.normSq (∑ j, x j ^ 2) / 2 := by
  intro x n
  have h₁ : ∑ j, x j = 0 := by
    simp only [x, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      Finset.sum_neg_distrib, ← sub_eq_add_neg, htrace, sub_self]
  have hE : ∑ j, Complex.normSq (x j) = 1 := by
    simpa only [x, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Complex.normSq_neg,
      spectralEnergy] using henergy
  have h₃ : ∑ j, (Complex.normSq (x j) : ℂ) * x j = 0 := by
    simp only [x, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Complex.normSq_neg,
      mul_neg, Finset.sum_neg_distrib, ← sub_eq_add_neg, hcubic, sub_self]
  refine centeredMobius_moment_test n Fintype.card_ne_zero x h₁ hE h₃ ?_
  intro p
  let E := centeredMobiusEnergy n x p
  have hEq (r : ℝ) :
      E r = centeredSpectralEnergy (mobiusSpectrum ((r : ℂ) * p) a)
        (mobiusSpectrum (-((r : ℂ) * p)) b) := by
    simp [E, centeredMobiusEnergy, centeredSpectralEnergy, spectralEnergy, mobiusPath,
      mobiusSpectrum, x, n, Fintype.sum_sum_type, mul_neg, neg_mul, neg_div,
      Finset.sum_neg_distrib, sub_eq_add_neg]
  have hDq (r : ℝ) :
      centeredMobiusDenominator x p r = mobiusDenominator a b ((r : ℂ) * p) := by
    simp [centeredMobiusDenominator, mobiusDenominator, x, Fintype.prod_sum_type, mul_neg,
      sub_eq_add_neg]
  have hEjet := quad_centeredMobiusEnergy n x h₁ hE h₃ p
  have hEpos : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < E t :=
    hEjet.continuousAt.eventually_mem (Ioi_mem_nhds (by rw [hEjet.at_zero]; exact zero_lt_one))
  have ha : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), ∀ i, 1 - (t : ℂ) * p * a i ≠ 0 :=
    Filter.eventually_all.mpr fun i =>
      (quad_one_sub_mul p (a i)).continuousAt.eventually_ne (by simp)
  have hb : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), ∀ i, 1 + (t : ℂ) * p * b i ≠ 0 :=
    Filter.eventually_all.mpr fun i => by
      simpa only [mul_neg, sub_neg_eq_add] using
        (quad_one_sub_mul p (-b i)).continuousAt.eventually_ne (by simp)
  filter_upwards [hEpos, ha, hb] with r hr har hbr
  change 1 ≤ E r ^ n * Complex.normSq (centeredMobiusDenominator x p r)
  rw [hEq, hDq]
  exact hbound ((r : ℂ) * p) har hbr (by rwa [← hEq])


/-- The moment test applies to the same contact-constrained maximizers
as in `exists_balanced_support_gap_maximizer_with_contacts`. It only
uses variations preserving the maximizing labels. -/
theorem spectral_mobius_moment_test_of_contact_gap_maximum [DecidableEq ι]
    (S : Finset (Equiv.Perm ι)) (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (η : ℂ) (hη : Complex.normSq η = 1) {g : ℝ} (hg : 0 < g)
    (hS : KeepsContacts S a b η) (henergy : spectralEnergy a b = 1)
    (htrace : (∑ i, a i) = ∑ i, b i)
    (hcubic : (∑ i, (Complex.normSq (a i) : ℂ) * a i) =
      ∑ i, (Complex.normSq (b i) : ℂ) * b i)
    (hgap : ∀ σ : Equiv.Perm ι,
      g ≤ (η * (determinantValue a b U - matchingProduct a b σ)).re)
    (hmax : ∀ (c d : ι → ℂ) (k : ℂ), spectralEnergy c d ≤ 1 → Complex.normSq k = 1 →
      KeepsContacts S c d k →
      ∃ σ : Equiv.Perm ι, (k * (determinantValue c d U - matchingProduct c d σ)).re ≤ g) :
    let x : ι ⊕ ι → ℂ := Sum.elim a (fun i => - b i)
    let n := Fintype.card ι
    ‖(2 * (n : ℂ)) * (∑ j, (Complex.normSq (x j) : ℂ) * x j ^ 2) - ∑ j, x j ^ 2‖ ≤
      (n : ℝ) * (∑ j, Complex.normSq (x j) ^ 2) - Complex.normSq (∑ j, x j ^ 2) / 2 := by
  apply spectral_mobius_moment_test a b htrace henergy hcubic
  intro t ha hb E he
  let c := mobiusSpectrum t a
  let d := mobiusSpectrum (-t) b
  let s : ℂ := -((∑ i, c i) - ∑ i, d i) / ((2 * (Fintype.card ι : ℝ) : ℝ) : ℂ)
  have hcenter : spectralEnergy (fun i => c i + s) (fun i => d i - s) = E :=
    spectralEnergy_centering c d
  have he' : 0 < spectralEnergy (fun i => c i + s) (fun i => d i - s) := by rwa [hcenter]
  have hbound :=
    spectralEnergy_shifted_mobius_bound_of_profile_scale_maximum a b U hU η hη hg hgap
      (fun c' d' k hE hk ⟨m, hm, hscale⟩ =>
        hmax c' d' k hE hk (KeepsContacts.of_profile_scale hS hm.le hscale))
      t s ha hb he'
  rwa [hcenter] at hbound

end

end MOC
