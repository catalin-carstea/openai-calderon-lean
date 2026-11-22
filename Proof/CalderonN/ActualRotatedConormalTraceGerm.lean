module

public import Proof.CalderonN.ActualRelativeRotatedConormalTaylor
public import Proof.CalderonN.ActualFiniteRotatedConormalIdentity
public import Proof.CalderonN.FixedBallWeakConormalTraceAgreement

import Mathlib.Tactic

/-! The relative-radius weak rotational Taylor family represents the
same scaled conormal commutator throughout the physical radius germ. -/

public section

noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 4200000
set_option maxSynthPendingDepth 29
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE OAI.AnisotropicCalderon.SmoothSphereRotation
attribute [local instance] W1p0.instNormedAddCommGroup W1p0.instInnerProductSpace
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

private theorem fixedBallWeakConormalRotatedTaylor_apply
    (r : ℝ) (E₁ E₂ T₁ T₂ : FixedBallEnergyOperator dim)
    (f g : SphereSobolev dim (1/2:ℝ)) :
    let E : FixedBallEnergyOperator dim := fixedBallFlatEnergyL dim+r • E₁+r^2 • E₂
    let T : FixedBallEnergyOperator dim := r • T₁+r^2 • T₂
    let P := harmonicFirstOrderLift dim
    let U := weakEnergyPoissonOperatorL (fixedBallZeroInclusionL dim) E P
    fixedBallWeakConormalRotatedTaylor r E₁ E₂ T₁ T₂ f g =
      T (U f) (U g)-r*T₁ (P f) (P g) := by
  simp only [fixedBallWeakConormalRotatedTaylor,fixedBallWeakRotatedSubtract,
    fixedBallWeakRotatedCompose,fixedBallWeakRotatedSolution,sub_apply,smul_apply,smul_eq_mul,
    ContinuousLinearMap.bilinearComp_apply]

theorem ActualRelativeRotatedConormalGerm.eq_physical_rotation_finite
    {d : Data dim} {y : X dim} {N : ℕ} {B : ℝ}
    (H : ActualRelativeRotatedConormalGerm d y N B) (hr : d.radius y ≠ 0)
    {x : X dim} (hx : (x,d.radius x/d.radius y-1) ∈ H.energy.neighborhood)
    (D : ActualGaussFiberData d x)
    (hSym : ∀ z ∈ ball (0:X dim) 1,(D.coefficient z).IsSymm)
    (i j : I dim) (f g : HarmonicFiniteCoefficients dim) :
    let p := (x,d.radius x/d.radius y-1)
    fixedBallWeakConormalRotatedTaylor (d.radius y) (H.energy.first p) (H.energy.second p)
      (H.energy.rotFirst i j p) (H.energy.rotSecond i j p)
      (harmonicBoundaryFiniteL (1/2:ℝ) f) (harmonicBoundaryFiniteL (1/2:ℝ) g) =
      unitSphereArea dim * ∫ w : ↥(standardSphere dim),(harmonicFiniteSmooth g).1 w*
        ((smoothSphereTraceRotation i j*D.conormalRemainder-D.conormalRemainder*smoothSphereTraceRotation i j)
          (finiteHarmonicSmoothTraceL f)).1 w ∂(sphereProbability dim) := by
  dsimp only
  let r := d.radius y
  let s := d.radius x
  let p := (x,s/r-1)
  let A := D.coefficient
  let C (z : X dim) := actualFramedCoefficientField d (actualRelativeCoefficientInput r (p,z))
  let ell := (firstDensityCenterLinear d x).comp (ballRotationGeneratorL i j)
  let E : FixedBallEnergyOperator dim := fixedBallFlatEnergyL dim+r • H.energy.first p+r^2 • H.energy.second p
  let T₁ := H.energy.rotFirst i j p
  let T : FixedBallEnergyOperator dim := r • T₁+r^2 • H.energy.rotSecond i j p
  have hp : r*(1+p.2) = s := by
    have hr' : r ≠ 0 := hr
    dsimp only [p]
    rw [show 1+(s/r-1) = s/r by ring,div_eq_mul_inv,mul_left_comm,mul_inv_cancel₀ hr',mul_one]
  have hAC : EqOn A C (ball (0:X dim) 1) := by
    intro z hz
    change D.coefficient z = firstNormalVelocityCoefficient d x ((r*(1+p.2)) • frameVector d.frame x z)
    rw [hp]
    exact D.coefficientEq hz
  have hE : E = fixedBallSmoothEnergyL D.smoothCoefficient.continuous := by
    ext u v : 2
    rw [show E u v = _ from H.energy.energy_eq p hx u v]
    exact (fixedBallSmoothEnergyL_eq_weak_of_eqOn D.smoothCoefficient.continuous hAC u v).symm
  have hT (u v : FixedBallH1 dim) : T u v = energyFormH1 (ballRotationCoefficient i j A) 0 0 u v := by
    have hθ : Continuous (ballRotationCoefficient i j A) :=
      (contDiff_ballRotationCoefficient i j D.smoothCoefficient).continuous
    have hRot := ballRotationCoefficient_congrOn_open i j isOpen_ball hAC
    have h₁ := fixedBallSmoothEnergyL_eq_weak_of_eqOn hθ hRot u v
    have h₂ := fixedBallSmoothEnergyL_apply hθ u v
    exact (H.energy.rotEnergy_eq i j p hx u v).trans (h₁.symm.trans h₂)
  have hF (u v : FixedBallH1 dim) : r*T₁ u v =
      s*energyFormH1 (fun z => ell z • (1:Mat dim)) 0 0 u v := by
    let W (z : X dim) : Mat dim := ell z • 1
    have hW : Continuous W := ell.continuous.smul continuous_const
    have h₁ : T₁ = (1+p.2) • fixedBallSmoothEnergyL hW := by
      ext w z : 2
      change H.energy.rotFirst i j p w z = _
      rw [H.energy.rotFirst_eq i j p hx,← fixedBallSmoothEnergyL_smul hW,fixedBallSmoothEnergyL_apply]
      rfl
    rw [h₁]
    simp only [smul_apply,smul_eq_mul,mul_assoc,fixedBallSmoothEnergyL_apply]
    rw [← mul_assoc,hp]
  let L := harmonicBoundaryFiniteL (dim:=dim) (1/2:ℝ)
  let P := harmonicFirstOrderLift dim
  let U : SphereSobolev dim (1/2:ℝ) →L[ℝ] FixedBallH1 dim := weakEnergyPoissonOperatorL (fixedBallZeroInclusionL dim) E P
  have hU (f : HarmonicFiniteCoefficients dim) : U (L f) = smoothSobolev (D.solve (harmonicFiniteSmooth f)).actual := by
    dsimp only [U]
    rw [hE]
    exact fixedBallWeakPoisson_eq_smooth_on_finite D.smoothCoefficient D.ellipticCoefficient f
      (D.solve (harmonicFiniteSmooth f)).actual (D.solve (harmonicFiniteSmooth f)).actualTrace
      (D.solve (harmonicFiniteSmooth f)).actualEquation
  rw [fixedBallWeakConormalRotatedTaylor_apply]
  change T (U (L f)) (U (L g))-r*T₁ (P (L f)) (P (L g)) = _
  rw [hU,hU,hT,show P (L f) = smoothSobolev (harmonicFiniteSmooth f) from harmonicFirstOrderLift_finite_smooth f,
    show P (L g) = smoothSobolev (harmonicFiniteSmooth g) from harmonicFirstOrderLift_finite_smooth g,hF]
  exact (D.rotation_conormalRemainder_finite_energy hSym i j f g).symm

end CalderonN
