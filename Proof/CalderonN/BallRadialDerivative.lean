module

public import Proof.CalderonN.BallPoissonOperator

import Mathlib.Tactic

/-! Fixed-ball radial derivative using the same coordinate derivatives
and Sobolev multipliers as the strong Dirichlet operator. -/

public section

noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal Gradient InnerProductSpace
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 24
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CalderonN

open BallDirichlet

variable {dim : ℕ} [NeZero dim]

private noncomputable def ballCoordinateCoefficient (i : Fin dim) : SmoothCoefficientJets dim 2 :=
  compactCoefficient 2 (fun z => (unitBallSmoothCutoff dim) z * z i)
    ((unitBallSmoothCutoff dim).contDiff.mul (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff)
    (unitBallSmoothCutoff dim).hasCompactSupport.mul_right

private theorem ballCoordinateCoefficient_value (i : Fin dim) {z : X dim}
    (hz : z ∈ fixedBallOpens dim) : coefficientValue 2 (ballCoordinateCoefficient i) z = z i := by
  unfold ballCoordinateCoefficient
  rw [coefficientValue_compactCoefficient,unitBallSmoothCutoff_one_of_mem hz,one_mul]

/-- The normalized outward radial derivative in the bulk before
restricting it to the sphere. -/
def ballRadialDerivativeL (dim : ℕ) [NeZero dim] :
    BallSobolev dim 2 →L[ℝ] BallSobolev dim 1 :=
  ∑ i : Fin dim, (coefficientMultiplier fixedSobolevCalculus 1 (ballCoordinateCoefficient i)).comp
    (unitBallCoordinateDerivativeL fixedSobolevCalculus 1 i)

/-- Ambient representative of the radial derivative for a smooth
fixed-ball function. -/
@[expose] def smoothBallRadialDerivative (u : SmoothData dim) : SmoothData dim :=
  ⟨fun z => fderiv ℝ u.1 z z, (u.2.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_id⟩

theorem ballRadialDerivativeL_smooth (u : SmoothData dim) :
    ballRadialDerivativeL dim (smoothBallSobolev 2 u) =
      smoothBallSobolev 1 (smoothBallRadialDerivative u) := by
  let μ := (volume : Measure (X dim)).restrict (fixedBallOpens dim)
  let U := smoothBallSobolev 2 u
  let D (i : Fin dim) := unitBallCoordinateDerivativeL fixedSobolevCalculus 1 i U
  let W (i : Fin dim) := coefficientMultiplier fixedSobolevCalculus 1 (ballCoordinateCoefficient i) (D i)
  have hD (i : Fin dim) :
      (TauCeti.Wkp.value 1 (D i) : X dim → ℝ) =ᵐ[μ] fun z => coordDeriv i u.1 z := by
    have hg := gradient_smoothSobolev_ae u
    have h := unitBallCoordinateDerivativeL_value_ae fixedSobolevCalculus 1 i U
    rw [show TauCeti.Wkp.firstOrder 1 U = smoothSobolev u from firstOrder_smoothBallSobolev 1 u] at h
    filter_upwards [h,hg] with z hz hz'
    rw [hz,hz',coordDeriv,← inner_gradient_left (𝕜 := ℝ)]
    simp only [axis,EuclideanSpace.inner_single_right,conj_trivial,one_mul]
  have hm : ∀ᵐ z ∂μ, z ∈ fixedBallOpens dim :=
    ae_restrict_mem (fixedBallOpens dim).isOpen.measurableSet
  have hW (i : Fin dim) :
      (TauCeti.Wkp.value 1 (W i) : X dim → ℝ) =ᵐ[μ] fun z => z i * coordDeriv i u.1 z := by
    have h := coefficientMultiplier_value_ae fixedSobolevCalculus 1 (ballCoordinateCoefficient i) (D i)
    filter_upwards [h,hD i,hm] with z hz hD' hzM
    rw [hz,hD',ballCoordinateCoefficient_value i hzM]
  have hPoint (z : X dim) : (∑ i : Fin dim, z i * coordDeriv i u.1 z) =
      (smoothBallRadialDerivative u).1 z := by
    change (∑ i : Fin dim, z i * fderiv ℝ u.1 z (axis i)) = fderiv ℝ u.1 z z
    rw [← congrArg (fderiv ℝ u.1 z) (vector_eq_sum_axis z)]
    simp only [map_sum,map_smul,smul_eq_mul]
  have hSum : ballRadialDerivativeL dim U = ∑ i : Fin dim, W i := by
    simp only [ballRadialDerivativeL,sum_apply,ContinuousLinearMap.comp_apply,W,D]
  rw [hSum]
  apply TauCeti.Wkp.ext 1
  rw [← TauCeti.Wkp.valueL_apply,map_sum]
  apply Lp.ext
  have hCo := Lp.coeFn_finsetSum Finset.univ (fun i => TauCeti.Wkp.valueL 1 (W i))
  have hEvery : ∀ᵐ z ∂μ, ∀ i : Fin dim, (TauCeti.Wkp.value 1 (W i)) z = z i * coordDeriv i u.1 z :=
    Filter.eventually_all.mpr hW
  filter_upwards [hCo,hEvery,value_smoothBallSobolev_ae 1 (smoothBallRadialDerivative u)]
    with z hz hEach hRad
  rw [hz,hRad]
  rw [Finset.sum_apply]
  refine (Finset.sum_congr rfl (fun i _ => ?_)).trans (hPoint z)
  exact hEach i

end CalderonN
