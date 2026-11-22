module

public import Proof.CalderonN.FiniteConormalTaylorSymmetry
public import Proof.CalderonN.SmoothStrongBallEstimates

import Proof.CalderonN.GreenSourceCutoff
import Mathlib.Tactic

/-! The smooth flat Dirichlet response and its first conormal variation
have the same Green pairings as the finite harmonic models. -/

public section

noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 3300000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE OAI.AnisotropicCalderon SphereHarmonic
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem exists_smooth_flat_response_and_variation
    (F : SmoothCoefficientMatrix dim 2)
    (hF : ∀ z ∈ closedBall (0 : X dim) 2, coefficientMatrixField 2 F z = 1)
    (ell : X dim →L[ℝ] ℝ) (f : SmoothData dim) :
    ∃ u q : SmoothData dim,
      EqOn u.1 f.1 (standardSphere dim) ∧
      EqOn (negativeBallDivergence (fun _ => (1 : Mat dim)) u.1) 0 (ball (0 : X dim) 1) ∧
      EqOn q.1 0 (standardSphere dim) ∧
      EqOn (negativeBallDivergence (fun _ => (1 : Mat dim)) q.1)
        (fun z => -negativeBallDivergence (fun w => ell w • (1 : Mat dim)) u.1 z) (ball (0 : X dim) 1) := by
  let A := coefficientMatrixField 2 F
  have hEq (z : X dim) (hz : z ∈ (fixedBallOpens dim : Set (X dim))) : A z = 1 :=
    hF z (closedBall_subset_closedBall (by norm_num : (1:ℝ) ≤ 2) (ball_subset_closedBall hz))
  have hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A 1 1 := by
    have h := uniformlyEllipticOn_const_one_one (n:=Fin dim) (fixedBallOpens dim : Set (X dim))
    refine ⟨h.1,h.2.1,fun z hz => ?_⟩
    rw [hEq z hz]
    exact h.2.2 hz
  have hAg {z : X dim} (hz : z ∈ ball (0 : X dim) 1) : A =ᶠ[𝓝 z] fun _ => (1 : Mat dim) := by
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw using hEq w hw
  obtain ⟨v,hv,hvT,hvH,_⟩ := exists_native_classicalBallPoisson 0 F hEll f
  let u : SmoothData dim := ⟨v,hv⟩
  let G : X dim → Mat dim := fun z => ell z • 1
  have hG : ContDiff ℝ ∞ G := ell.contDiff.smul contDiff_const
  let s : SmoothData dim := ⟨fun z => -negativeBallDivergence G u.1 z,
    (contDiff_negativeBallDivergence hG u.2).neg⟩
  obtain ⟨q,hqT,hqH,_⟩ := exists_native_classical_zeroDirichlet F hEll s
  refine ⟨u,q,hvT,fun z hz => ?_,hqT,fun z hz => ?_⟩
  · rw [← negativeBallDivergence_congr_germ (hAg hz) EventuallyEq.rfl]
    exact hvH hz
  · change negativeBallDivergence (fun _ => (1 : Mat dim)) q.1 z = s.1 z
    rw [← negativeBallDivergence_congr_germ (hAg hz) EventuallyEq.rfl]
    exact hqH hz

theorem integral_smoothFirstConormal_symm (ell : X dim →L[ℝ] ℝ)
    (f g u v q p : SmoothData dim)
    (huT : EqOn u.1 f.1 (standardSphere dim))
    (hvT : EqOn v.1 g.1 (standardSphere dim))
    (huH : EqOn (negativeBallDivergence (fun _ => (1 : Mat dim)) u.1) 0 (ball (0 : X dim) 1))
    (hvH : EqOn (negativeBallDivergence (fun _ => (1 : Mat dim)) v.1) 0 (ball (0 : X dim) 1))
    (hqT : EqOn q.1 0 (standardSphere dim)) (hpT : EqOn p.1 0 (standardSphere dim))
    (hqH : EqOn (negativeBallDivergence (fun _ => (1 : Mat dim)) q.1)
      (fun z => -negativeBallDivergence (fun w => ell w • (1 : Mat dim)) u.1 z) (ball (0 : X dim) 1))
    (hpH : EqOn (negativeBallDivergence (fun _ => (1 : Mat dim)) p.1)
      (fun z => -negativeBallDivergence (fun w => ell w • (1 : Mat dim)) v.1 z) (ball (0 : X dim) 1)) :
    (∫ z : ↥(standardSphere dim), (ell z*fderiv ℝ u.1 z z+fderiv ℝ q.1 z z)*g.1 z ∂(sphereProbability dim)) =
    ∫ z : ↥(standardSphere dim), f.1 z*(ell z*fderiv ℝ v.1 z z+fderiv ℝ p.1 z z) ∂(sphereProbability dim) := by
  let A : X dim → Mat dim := fun _ => 1
  let G : X dim → Mat dim := fun z => ell z • 1
  have hA : ContDiff ℝ ∞ A := contDiff_const
  have hG : ContDiff ℝ ∞ G := ell.contDiff.smul contDiff_const
  have hAS : ∀ z ∈ ball (0 : X dim) 1, (A z).IsSymm := fun _ _ => Matrix.isSymm_one
  have hGS (z : X dim) : (G z).IsSymm := Matrix.isSymm_one.smul _
  have coeff (U Q V : SmoothData dim) (hQT : EqOn Q.1 0 (standardSphere dim))
      (hQH : EqOn (negativeBallDivergence A Q.1) (fun z => -negativeBallDivergence G U.1 z)
        (ball (0 : X dim) 1))
      (hVH : EqOn (negativeBallDivergence A V.1) 0 (ball (0 : X dim) 1)) :
      unitSphereArea dim*(∫ z : ↥(standardSphere dim), V.1 z*
        (ell z*fderiv ℝ U.1 z z+fderiv ℝ Q.1 z z) ∂(sphereProbability dim)) =
        energyFormH1 G 0 0 (smoothSobolev U) (smoothSobolev V) := by
    have hDiv : EqOn (coordinateFluxDivergence (fun z => smoothBallFlux A Q.1 z+smoothBallFlux G U.1 z))
        0 (ball (0 : X dim) 1) := by
      intro z hz
      change coordinateFluxDivergence (smoothBallFlux A Q.1+smoothBallFlux G U.1) z = 0
      rw [coordinateFluxDivergence_add ((contDiff_smoothBallFlux hA Q).differentiable (by simp))
        ((contDiff_smoothBallFlux hG U).differentiable (by simp)),
        coordinateFluxDivergence_smoothBallFlux,coordinateFluxDivergence_smoothBallFlux]
      have hh : negativeBallDivergence A Q.1 z = -negativeBallDivergence G U.1 z := hQH hz
      rw [hh,neg_neg,add_neg_cancel]
    apply Eq.trans _ (integral_linearizedBallConormal hA hG hAS U Q V hQT hDiv hVH)
    congr 1
    apply integral_congr_ae
    filter_upwards with z
    rw [inner_add_right,show ⟪(z : X dim),smoothBallFlux A Q.1 z⟫_ℝ = fderiv ℝ Q.1 z z from by
      simpa only [one_smul,one_mul,A] using inner_smoothBallFlux_scalar (fun _ => 1) Q.1 z,
      show ⟪(z : X dim),smoothBallFlux G U.1 z⟫_ℝ = ell z*fderiv ℝ U.1 z z from
        inner_smoothBallFlux_scalar ell U.1 z,add_comm]
  have hE := energyFormH1_comm_of_isSymm_ae (c:=0) (Filter.Eventually.of_forall hGS)
    (smoothSobolev u) (smoothSobolev v)
  rw [← coeff u q v hqT hqH hvH,← coeff v p u hpT hpH huH] at hE
  have h := (mul_right_inj' (unitSphereArea_pos (dim:=dim)).ne').mp hE
  refine (integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)).trans
    (h.trans (integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)))
  · rw [hvT z.2,mul_comm]
  · change u.1 z*(ell z*fderiv ℝ v.1 z z+fderiv ℝ p.1 z z) =
      f.1 z*(ell z*fderiv ℝ v.1 z z+fderiv ℝ p.1 z z)
    rw [huT z.2]

end CalderonN
