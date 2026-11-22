module

public import Proof.CalderonN.FixedBallWeakConormalFamilyJets
public import Proof.CalderonN.ActualGaussConormalCore

import Proof.CalderonN.SmoothStrongBallEstimates
import Proof.CalderonN.SmoothZeroTraceMembership
import Proof.CalderonN.PolynomialConormalFirstVariation
import Proof.CalderonN.BallRegularity.NativeSmoothBallSobolev
import Mathlib.Tactic

/-! Identify weak conormal Taylor forms with the genuine smooth
conormal remainder on the same finite harmonic data. -/

public section

noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Elementwise InnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
attribute [local instance] W1p0.instNormedAddCommGroup W1p0.instInnerProductSpace
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem fixedBallWeakPoisson_eq_smooth_on_finite {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
    (f : HarmonicFiniteCoefficients dim) (u : SmoothData dim)
    (hu : EqOn u.1 (harmonicFiniteSmooth f).1 (standardSphere dim))
    (hP : EqOn (negativeBallDivergence A u.1) 0 (ball (0:X dim) 1)) :
    weakEnergyPoissonOperatorL (fixedBallZeroInclusionL dim) (fixedBallSmoothEnergyL hA.continuous)
      (harmonicFirstOrderLift dim) (harmonicBoundaryFiniteL (1/2:ℝ) f) = smoothSobolev u := by
  rw [weakEnergyPoissonOperatorL_eq _ _ (isCoercive_fixedBallSmoothEnergy hA.continuous hEll)]
  obtain ⟨F,hF⟩ := exists_smoothCoefficientMatrix_eqOn hA
  have hFE : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) (coefficientMatrixField 2 F) lo hi := by
    refine ⟨hEll.1,hEll.2.1,?_⟩
    intro z hz
    rw [hF (ball_subset_ball (by norm_num : (1:ℝ) ≤ 5/4) hz)]
    exact hEll.2.2 hz
  let v := harmonicFiniteSmooth f
  let w : SmoothData dim := ⟨u.1-v.1,u.2.sub v.2⟩
  have hw : EqOn w.1 0 (standardSphere dim) := fun _ hz => sub_eq_zero.mpr (hu hz)
  have hm := smoothSobolev_mem_zero_of_eqOn_sphere F hFE w hw
  symm
  apply eq_weakDirichletPoissonL_of_equation
  · rw [harmonicFirstOrderLift_finite_smooth]
    refine ⟨⟨smoothSobolev w,hm⟩,?_⟩
    change smoothSobolev u-smoothSobolev v = smoothSobolev w
    exact ((smoothBallSobolevLinear dim 1).map_sub ⟨u.1,u.2⟩ ⟨v.1,v.2⟩).symm
  · intro w
    rw [fixedBallSmoothEnergyL_apply]
    exact energyFormH1_smooth_zeroDirichlet hA u hP w

theorem fixedBallWeakConormal_eq_flux_on_finite {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
    (f g : HarmonicFiniteCoefficients dim) (u : SmoothData dim)
    (hu : EqOn u.1 (harmonicFiniteSmooth f).1 (standardSphere dim))
    (hP : EqOn (negativeBallDivergence A u.1) 0 (ball (0:X dim) 1)) :
    fixedBallWeakConormalFamily (fixedBallSmoothEnergyL hA.continuous)
      (harmonicBoundaryFiniteL (1/2:ℝ) f) (harmonicBoundaryFiniteL (1/2:ℝ) g) =
      unitSphereArea dim*∫ z : ↥(standardSphere dim),(harmonicFiniteSmooth g).1 z*smoothBallConormal A u.1 z
        ∂(sphereProbability dim) := by
  unfold fixedBallWeakConormalFamily
  rw [ContinuousLinearMap.bilinearComp_apply,fixedBallWeakPoisson_eq_smooth_on_finite hA hEll f u hu hP,
    harmonicFirstOrderLift_finite_smooth,fixedBallSmoothEnergyL_apply]
  exact energyFormH1_smooth_eq_boundary_flux hA u (harmonicFiniteSmooth g) hP

end CalderonN
