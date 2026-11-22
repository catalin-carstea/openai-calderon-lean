module

public import Proof.CalderonN.DoubleAngularTaylorEquation
public import Proof.CalderonN.SmoothFluxSumEstimates

import Mathlib.Tactic

/-! The same forcing computation supplies strong and weak Taylor
estimates for the nested angular response. -/

public section

noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 6500000
set_option maxSynthPendingDepth 27
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

@[expose] def SmoothCoefficientC1Bound (A : X dim → Mat dim) (q : ℝ) : Prop :=
  ∀ z ∈ ball (0 : X dim) 1, ‖A z‖ ≤ q ∧ ‖fderiv ℝ A z‖ ≤ q

@[expose] def SmoothDirichletDivergenceBudget (A : X dim → Mat dim) (N : SmoothData dim → ℝ)
    (C : ℝ) : Prop :=
  ∀ (n : ℕ) (a : Fin n → X dim → Mat dim), (∀ i, ContDiff ℝ ∞ (a i)) →
    ∀ (u : Fin n → SmoothData dim) (q : Fin n → ℝ), (∀ i, 0 ≤ q i) →
    (∀ i, SmoothCoefficientC1Bound (a i) (q i)) →
    ∀ v : SmoothData dim, EqOn v.1 0 (standardSphere dim) →
    EqOn (negativeBallDivergence A v.1) (fun z => -(∑ i,negativeBallDivergence (a i) (u i).1 z))
      (ball (0 : X dim) 1) →
    N v ≤ C*∑ i,q i*N (u i)

theorem norm_doubleAngular_bulkTaylor (i j k l : Fin dim)
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A) (b b₁ b₂ b₁₂ u q : SmoothData dim)
    (hb : EqOn (negativeBallDivergence A b.1) 0 (ball (0 : X dim) 1))
    (hb₁ : EqOn (negativeBallDivergence A b₁.1) 0 (ball (0 : X dim) 1))
    (hb₂ : EqOn (negativeBallDivergence A b₂.1) 0 (ball (0 : X dim) 1))
    (hb₁₂ : EqOn (negativeBallDivergence A b₁₂.1) 0 (ball (0 : X dim) 1))
    (hu : EqOn (negativeBallDivergence (fun _ => (1 : Mat dim)) u.1) 0 (ball (0 : X dim) 1))
    (ell₂ : X dim →L[ℝ] ℝ)
    (hq : EqOn (negativeBallDivergence (fun _ => (1 : Mat dim)) q.1)
      (-negativeBallDivergence (fun z => ell₂ z • (1 : Mat dim)) u.1) (ball (0 : X dim) 1))
    (N : SmoothData dim → ℝ) (hN : ∀ v, 0 ≤ N v)
    (hNSub : ∀ p t, N p ≤ N t+N ⟨p.1-t.1,p.2.sub t.2⟩)
    (r C G : ℝ) (hr : 0 ≤ r) (hr₁ : r ≤ 1) (hC : 0 ≤ C) (hG : 0 ≤ G) :
    let A₀ : X dim → Mat dim := fun _ => 1
    let A₁ := ballRotationCoefficient i j A
    let A₂ := ballRotationCoefficient k l A
    let A₁₂ := ballRotationCoefficient k l A₁
    let D := A-A₀
    let L := fun z => ell₂ z • (1 : Mat dim)
    let R := A₁₂-r • L
    let w₁ := angularBallCorrection i j b b₁
    let w₂ := angularBallCorrection k l b b₂
    let w₁₂ := angularBallCorrection i j b₂ b₁₂
    let w := angularBallCorrection k l w₁ w₁₂
    let e : SmoothData dim := ⟨w.1-r • q.1,w.2.sub (q.2.const_smul r)⟩
    let d : SmoothData dim := ⟨b.1-u.1,b.2.sub u.2⟩
    let J := C*G
    let B := J*(1+J)
    let E := J*(2*J+1+2*B)
    SmoothDirichletDivergenceBudget A N C →
    SmoothDirichletDivergenceBudget A₀ N C →
    EqOn b.1 u.1 (standardSphere dim) →
    EqOn w₁.1 0 (standardSphere dim) → EqOn w₂.1 0 (standardSphere dim) →
    EqOn w.1 0 (standardSphere dim) → EqOn q.1 0 (standardSphere dim) →
    SmoothCoefficientC1Bound D (G*r) → SmoothCoefficientC1Bound A₁ (G*r) →
    SmoothCoefficientC1Bound A₂ (G*r) → SmoothCoefficientC1Bound A₁₂ (G*r) →
    SmoothCoefficientC1Bound L G → SmoothCoefficientC1Bound R (G*r^2) →
    N d ≤ J*r*N u ∧ N w₁ ≤ B*r*N u ∧ N w₂ ≤ B*r*N u ∧
      N q ≤ J*N u ∧ N e ≤ E*r^2*N u := by
  dsimp only
  intro hInv hInv₀ hbu hw₁ hw₂ hw hqT hD hA₁ hA₂ hA₁₂ hL hR
  let A₀ : X dim → Mat dim := fun _ => 1
  let A₁ := ballRotationCoefficient i j A
  let A₂ := ballRotationCoefficient k l A
  let A₁₂ := ballRotationCoefficient k l A₁
  let D := A-A₀
  let L := fun z => ell₂ z • (1 : Mat dim)
  let R := A₁₂-r • L
  let w₁ := angularBallCorrection i j b b₁
  let w₂ := angularBallCorrection k l b b₂
  let w₁₂ := angularBallCorrection i j b₂ b₁₂
  let w := angularBallCorrection k l w₁ w₁₂
  let e : SmoothData dim := ⟨w.1-r • q.1,w.2.sub (q.2.const_smul r)⟩
  let d : SmoothData dim := ⟨b.1-u.1,b.2.sub u.2⟩
  let J := C*G
  let B := J*(1+J)
  let E := J*(2*J+1+2*B)
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  let forceOne (A' : X dim → Mat dim) (hA' : SmoothDirichletDivergenceBudget A' N C)
      (D' : X dim → Mat dim) (hD' : ContDiff ℝ ∞ D') (a : ℝ) (ha : 0 ≤ a)
      (hDa : SmoothCoefficientC1Bound D' a) (v f : SmoothData dim) (hv : EqOn v.1 0 (standardSphere dim))
      (hEq : EqOn (negativeBallDivergence A' v.1) (-negativeBallDivergence D' f.1) (ball (0 : X dim) 1)) :
      N v ≤ C*a*N f := by
    have hh := hA' 1 (fun _ => D') (fun _ => hD') (fun _ => f) (fun _ => a) (fun _ => ha)
      (fun _ => hDa) v hv (fun z hz => by simpa using hEq hz)
    exact hh.trans_eq (by rw [Fin.sum_univ_one,mul_assoc])
  have hdT : EqOn d.1 0 (standardSphere dim) := fun z hz => sub_eq_zero.mpr (hbu hz)
  have hd := forceOne A hInv D (hA.sub contDiff_const) (G*r) (by positivity) hD d u hdT
    (negativeBallDivergence_harmonic_lift_difference hA b u hb hu)
  have hbN : N b ≤ (1+J)*N u := by
    have hh : N b ≤ N u + J*r*N u := (hNSub b u).trans (add_le_add_right (hd.trans_eq (by dsimp [J]; ring)) _)
    exact hh.trans (by nlinarith only [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hr₁ hJ) (hN u)])
  have h1 := forceOne A hInv A₁ (contDiff_ballRotationCoefficient i j hA) (G*r) (by positivity)
    hA₁ w₁ b hw₁ (negativeBallDivergence_angularBallCorrection i j hA b b₁ hb hb₁)
  have h2 := forceOne A hInv A₂ (contDiff_ballRotationCoefficient k l hA) (G*r) (by positivity)
    hA₂ w₂ b hw₂ (negativeBallDivergence_angularBallCorrection k l hA b b₂ hb hb₂)
  have h1' : N w₁ ≤ B*r*N u :=
    (h1.trans (mul_le_mul_of_nonneg_left hbN (by positivity))).trans_eq (by dsimp [B,J]; ring)
  have h2' : N w₂ ≤ B*r*N u :=
    (h2.trans (mul_le_mul_of_nonneg_left hbN (by positivity))).trans_eq (by dsimp [B,J]; ring)
  have hqN : N q ≤ J*N u := forceOne A₀ hInv₀ L (ell₂.contDiff.smul contDiff_const) G hG hL q u hqT hq
  have hdN : N d ≤ J*r*N u := hd.trans_eq (by dsimp [J]; ring)
  refine ⟨hdN,h1',h2',hqN,?_⟩
  have heT : EqOn e.1 0 (standardSphere dim) := by
    intro z hz
    change w.1 z-r*q.1 z = 0
    rw [show w.1 z = 0 from hw hz,show q.1 z = 0 from hqT hz,mul_zero,sub_self]
  let F : Fin 5 → X dim → Mat dim := ![A₁₂,R,A₁,A₂,r • D]
  let U : Fin 5 → SmoothData dim := ![d,u,w₂,w₁,q]
  let Q : Fin 5 → ℝ := ![G*r,G*r^2,G*r,G*r,G*r^2]
  have hF (a : Fin 5) : ContDiff ℝ ∞ (F a) := by
    have ha₁ := contDiff_ballRotationCoefficient i j hA
    have hR' : ContDiff ℝ ∞ R :=
      (contDiff_ballRotationCoefficient k l ha₁).sub ((ell₂.contDiff.smul contDiff_const).const_smul r)
    fin_cases a <;> simp only [F,Matrix.cons_val] <;>
      first | exact contDiff_ballRotationCoefficient k l ha₁ | exact hR' | exact ha₁ |
        exact contDiff_ballRotationCoefficient k l hA | exact (hA.sub contDiff_const).const_smul r
  have hQr : 0 ≤ G*r := mul_nonneg hG hr
  have hQr₂ : 0 ≤ G*r^2 := mul_nonneg hG (sq_nonneg r)
  have hQ (a : Fin 5) : 0 ≤ Q a := by
    fin_cases a <;> first | exact hQr | exact hQr₂
  have hRD : SmoothCoefficientC1Bound (r • D) (G*r^2) := by
    intro z hz
    have h := hD z hz
    have he : fderiv ℝ (r • D) z = r • fderiv ℝ D z :=
      fderiv_const_smul ((hA.sub contDiff_const).differentiable (by simp) z) r
    rw [he]
    change ‖r • D z‖ ≤ G*r^2 ∧ ‖r • fderiv ℝ D z‖ ≤ G*r^2
    simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr]
    exact ⟨(mul_le_mul_of_nonneg_left h.1 hr).trans_eq (by ring),
      (mul_le_mul_of_nonneg_left h.2 hr).trans_eq (by ring)⟩
  have hfQ (a : Fin 5) : SmoothCoefficientC1Bound (F a) (Q a) := by
    fin_cases a <;> simp only [F,Q,Matrix.cons_val] <;> assumption
  have heq : EqOn (negativeBallDivergence A e.1)
      (fun z => -(∑ i,negativeBallDivergence (F i) (U i).1 z)) (ball (0 : X dim) 1) := by
    intro z hz
    change negativeBallDivergence A e.1 z = -(∑ i,negativeBallDivergence (F i) (U i).1 z)
    rw [Fin.sum_univ_five]
    simp only [F,U,Matrix.cons_val]
    have hh := negativeBallDivergence_doubleAngularTaylorRemainder i j k l hA b b₁ b₂ b₁₂ u q
      hb hb₁ hb₂ hb₁₂ ell₂ hq r hz
    change negativeBallDivergence A e.1 z =
      -negativeBallDivergence A₁₂ d.1 z-negativeBallDivergence R u.1 z-
        negativeBallDivergence A₁ w₂.1 z-negativeBallDivergence A₂ w₁.1 z-
        negativeBallDivergence (r • D) q.1 z at hh
    rw [hh]
    ring
  have he := hInv 5 F hF U Q hQ hfQ e heT heq
  rw [Fin.sum_univ_five] at he
  simp only [Q,U,Matrix.cons_val] at he
  refine he.trans ?_
  have hsum := add_le_add
    (add_le_add
      (add_le_add
        (add_le_add (mul_le_mul_of_nonneg_left hdN hQr) (le_refl (G*r^2*N u)))
        (mul_le_mul_of_nonneg_left h2' hQr))
      (mul_le_mul_of_nonneg_left h1' hQr))
    (mul_le_mul_of_nonneg_left hqN hQr₂)
  exact (mul_le_mul_of_nonneg_left hsum hC).trans_eq (by dsimp [E,J]; ring)

end CalderonN
