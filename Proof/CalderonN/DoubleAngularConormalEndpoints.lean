module

public import Proof.CalderonN.DoubleAngularConormalFlux

import Mathlib.Tactic

/-! Strong trace and weak Green bounds for the same nested conormal
commutator, after removing its scalar affine coefficient. -/

public section

noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 7300000
set_option maxSynthPendingDepth 28
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet OAI.AnisotropicCalderon.SmoothSphereRotation
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

private theorem norm_smoothBallSobolev_le_by_difference (s : ℕ) (u v : SmoothData dim) :
    ‖smoothBallSobolev s u‖ ≤ ‖smoothBallSobolev s v‖+
      ‖smoothBallSobolev s ⟨u.1-v.1,u.2.sub v.2⟩‖ := by
  let U : smoothBallDataSubmodule dim := ⟨u.1,u.2⟩
  let V : smoothBallDataSubmodule dim := ⟨v.1,v.2⟩
  let L := smoothBallSobolevLinear dim s
  change ‖L U‖ ≤ ‖L V‖+‖L (U-V)‖
  rw [map_sub]
  exact (le_trans (by rw [show L V+(L U-L V) = L U by abel]) (norm_add_le (L V) (L U-L V)))

theorem doubleAngularConormal_remainder_endpoints (hn : 3 ≤ dim)
    (C G : ℝ) (hC : 0 ≤ C) (hG : 0 ≤ G) :
    ∃ C_H C_L : ℝ, 0 ≤ C_H ∧ 0 ≤ C_L ∧
      ∀ (i j k l : Fin dim) {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
      (b b₁ b₂ b₁₂ u q : SmoothData dim) (ell₂ : X dim →L[ℝ] ℝ) (r : ℝ),
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
      0 ≤ r → r ≤ 1 →
      EqOn (negativeBallDivergence A b.1) 0 (ball (0 : X dim) 1) →
      EqOn (negativeBallDivergence A b₁.1) 0 (ball (0 : X dim) 1) →
      EqOn (negativeBallDivergence A b₂.1) 0 (ball (0 : X dim) 1) →
      EqOn (negativeBallDivergence A b₁₂.1) 0 (ball (0 : X dim) 1) →
      EqOn (negativeBallDivergence A₀ u.1) 0 (ball (0 : X dim) 1) →
      EqOn (negativeBallDivergence A₀ q.1) (-negativeBallDivergence L u.1) (ball (0 : X dim) 1) →
      EqOn b.1 u.1 (standardSphere dim) →
      EqOn w₁.1 0 (standardSphere dim) → EqOn w₂.1 0 (standardSphere dim) →
      EqOn w.1 0 (standardSphere dim) → EqOn q.1 0 (standardSphere dim) →
      SmoothCoefficientC1Bound A G → SmoothCoefficientC1Bound D (G*r) →
      SmoothCoefficientC1Bound A₁ (G*r) → SmoothCoefficientC1Bound A₂ (G*r) →
      SmoothCoefficientC1Bound A₁₂ (G*r) → SmoothCoefficientC1Bound L G →
      SmoothCoefficientC1Bound R (G*r^2) →
      SmoothDirichletDivergenceBudget A (fun v => ‖smoothBallSobolev 2 v‖) C →
      SmoothDirichletDivergenceBudget A₀ (fun v => ‖smoothBallSobolev 2 v‖) C →
      SmoothDirichletDivergenceBudget A (fun v => ‖smoothSobolev v‖) C →
      SmoothDirichletDivergenceBudget A₀ (fun v => ‖smoothSobolev v‖) C →
      ∃ Z : SmoothData dim,
        Z.1 = sphereRotationDerivative k l
          (sphereRotationDerivative i j (smoothBallConormal A b.1)-smoothBallConormal A b₁.1)-
          (sphereRotationDerivative i j (smoothBallConormal A b₂.1)-smoothBallConormal A b₁₂.1)-
          r • (smoothBallConormal L u.1+smoothBallConormal A₀ q.1) ∧
        ‖smoothBoundarySobolev hn (1/2:ℝ) (by norm_num) Z‖ ≤ C_H*r^2*‖smoothBallSobolev 2 u‖ ∧
        ∀ v : SmoothData dim,
          |∫ z : ↥(standardSphere dim), v.1 z*Z.1 z ∂(sphereProbability dim)| ≤
            C_L*r^2*‖smoothSobolev u‖*‖smoothSobolev v‖ := by
  obtain ⟨K_H,hK_H,hStrong⟩ := norm_smoothConormalSumData_half_le (ι:=Fin 6) hn
  let J := C*G
  let B := J*(1+J)
  let E := J*(2*J+1+2*B)
  let P := G*(E+2*J+1+2*B)
  have hP : 0 ≤ P := by dsimp [P,E,B,J]; positivity
  let K_L := (dim:ℝ)^2/unitSphereArea dim
  have hKL : 0 ≤ K_L := div_nonneg (sq_nonneg _) (unitSphereArea_pos (dim:=dim)).le
  refine ⟨K_H*P,K_L*P,by positivity,by positivity,?_⟩
  intro i j k l A hA b b₁ b₂ b₁₂ u q ell₂ r
  dsimp only
  intro hr hr₁ hb hb₁ hb₂ hb₁₂ hu hq hbu hw₁ hw₂ hw hqT hA_G hD hA₁ hA₂ hA₁₂ hL hR hIH hI₀H hIL hI₀L
  let A₀ : X dim → Mat dim := fun _ => 1
  let A₁ := ballRotationCoefficient i j A
  let A₂ := ballRotationCoefficient k l A
  let A₁₂ := ballRotationCoefficient k l A₁
  let L := fun z => ell₂ z • (1 : Mat dim)
  let D := A-A₀
  let R := A₁₂-r • L
  let w₁ := angularBallCorrection i j b b₁
  let w₂ := angularBallCorrection k l b b₂
  let w₁₂ := angularBallCorrection i j b₂ b₁₂
  let w := angularBallCorrection k l w₁ w₁₂
  let e : SmoothData dim := ⟨w.1-r • q.1,w.2.sub (q.2.const_smul r)⟩
  let d : SmoothData dim := ⟨b.1-u.1,b.2.sub u.2⟩
  let F : Fin 6 → X dim → Mat dim := ![A,A₁₂,R,A₁,A₂,r • D]
  let U : Fin 6 → SmoothData dim := ![e,d,u,w₂,w₁,q]
  let Q : Fin 6 → ℝ := ![G,G*r,G*r^2,G*r,G*r,G*r^2]
  have hQr : 0 ≤ G*r := mul_nonneg hG hr
  have hQr₂ : 0 ≤ G*r^2 := mul_nonneg hG (sq_nonneg r)
  have hQ (a : Fin 6) : 0 ≤ Q a := by
    fin_cases a <;> first | exact hG | exact hQr | exact hQr₂
  have hFD : ContDiff ℝ ∞ (r • D) := (hA.sub contDiff_const).const_smul r
  have hF (a : Fin 6) : ContDiff ℝ ∞ (F a) := by
    have ha₁ := contDiff_ballRotationCoefficient i j hA
    have ha₁₂ := contDiff_ballRotationCoefficient k l ha₁
    have hR' : ContDiff ℝ ∞ R := ha₁₂.sub ((ell₂.contDiff.smul contDiff_const).const_smul r)
    fin_cases a <;> simp only [F,Matrix.cons_val] <;>
      first | exact hA | exact ha₁₂ | exact hR' | exact ha₁ |
        exact contDiff_ballRotationCoefficient k l hA | exact hFD
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
  have hfQ (a : Fin 6) : SmoothCoefficientC1Bound (F a) (Q a) := by
    fin_cases a <;> simp only [F,Q,Matrix.cons_val] <;> assumption
  have hFlux : EqOn (coordinateFluxDivergence (∑ i,smoothBallFlux (F i) (U i).1)) 0 (ball (0 : X dim) 1) := by
    rw [Fin.sum_univ_six]
    simp only [F,U,Matrix.cons_val]
    have h := doubleAngularTaylor_conormal_sum_divergence i j k l hA b b₁ b₂ b₁₂ u q
      hb hb₁ hb₂ hb₁₂ ell₂ r hq
    convert h using 1
  let Z := smoothConormalSumData F hF U
  have hZ : Z.1 = sphereRotationDerivative k l
      (sphereRotationDerivative i j (smoothBallConormal A b.1)-smoothBallConormal A b₁.1)-
      (sphereRotationDerivative i j (smoothBallConormal A b₂.1)-smoothBallConormal A b₁₂.1)-
      r • (smoothBallConormal L u.1+smoothBallConormal A₀ q.1) := by
    rw [doubleAngularTaylor_conormal_sum i j k l hA b b₁ b₂ b₁₂ u q ell₂ r]
    funext z
    change (∑ i,smoothBallConormal (F i) (U i).1 z) = _
    rw [Fin.sum_univ_six]
    simp only [F,U,Matrix.cons_val,Pi.add_apply]
    ring
  have hSummed (N : SmoothData dim → ℝ) (hN : ∀ v, 0 ≤ N v)
      (hNSub : ∀ p t, N p ≤ N t+N ⟨p.1-t.1,p.2.sub t.2⟩)
      (hI : SmoothDirichletDivergenceBudget A N C) (hI₀ : SmoothDirichletDivergenceBudget A₀ N C) :
      ∑ i,Q i*N (U i) ≤ P*r^2*N u := by
    obtain ⟨hd,h₁,h₂,hq',he⟩ := norm_doubleAngular_bulkTaylor i j k l hA b b₁ b₂ b₁₂ u q hb hb₁ hb₂ hb₁₂
      hu ell₂ hq N hN hNSub r C G hr hr₁ hC hG hI hI₀ hbu hw₁ hw₂ hw hqT hD hA₁ hA₂ hA₁₂ hL hR
    rw [Fin.sum_univ_six]
    simp only [Q,U,Matrix.cons_val]
    have hSum := add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
      (mul_le_mul_of_nonneg_left he hG) (mul_le_mul_of_nonneg_left hd hQr)) (le_refl (G*r^2*N u)))
      (mul_le_mul_of_nonneg_left h₂ hQr)) (mul_le_mul_of_nonneg_left h₁ hQr)) (mul_le_mul_of_nonneg_left hq' hQr₂)
    exact hSum.trans_eq (by dsimp [P,E,B,J]; ring)
  have hHigh := hSummed (fun v => ‖smoothBallSobolev 2 v‖) (fun _ => norm_nonneg _)
    (norm_smoothBallSobolev_le_by_difference 2) hIH hI₀H
  have hLow := hSummed (fun v => ‖smoothSobolev v‖) (fun _ => norm_nonneg _)
    (norm_smoothBallSobolev_le_by_difference 1) hIL hI₀L
  refine ⟨Z,hZ,?_ ,fun v => ?_⟩
  · exact (hStrong F hF U Q hQ hfQ).trans
      ((mul_le_mul_of_nonneg_left hHigh hK_H).trans_eq (by ring))
  · have h := abs_conormal_sum_pair_le_weak_bulk F hF U v hFlux Q hQ (fun i z hz => (hfQ i z hz).1)
    exact h.trans ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hLow hKL) (norm_nonneg _)).trans_eq (by ring))

end CalderonN
