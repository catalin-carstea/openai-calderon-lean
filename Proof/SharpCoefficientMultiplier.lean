import Proof.Geometry
import Proof.Archive.CoefficientMultiplier
import Proof.TauCeti.Analysis.Sobolev.W1p.Multiplication

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
open scoped ContDiff ENNReal Gradient
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily

/-- The existing coefficient multiplier on H1 needs only the coefficient and
    its first derivative on the ball; its ambient second jet does not enter. -/
theorem norm_coefficientMultiplier_one_le (hcalc : FixedSobolevCalculus)
    (F : SmoothCoefficientJets 2) (q : ℝ) (hq : 0 ≤ q)
    (hValue : ∀ x ∈ (ballOpens : Set X),|coefficientValue 2 F x| ≤ q)
    (hDerivative : ∀ x ∈ (ballOpens : Set X),‖fderiv ℝ (coefficientValue 2 F) x‖ ≤ q) :
    ‖coefficientMultiplier hcalc 1 F‖ ≤ 2*q := by
  have hSmooth := contDiff_coefficientValue 2 F
  have hGrad (x : X) (hx : x ∈ (ballOpens : Set X)) : ‖gradient (coefficientValue 2 F) x‖ ≤ q := by
    simpa only [gradient,LinearIsometryEquiv.norm_map] using hDerivative x hx
  let T : BallH1 →L[ℝ] BallH1 := TauCeti.W1p.contDiffSMulL
    (mu:=(volume : Measure X)) (Omega:=ballOpens) (p:=2)
    (coefficientValue 2 F) hSmooth hq hValue hGrad
  have hEq : coefficientMultiplier hcalc 1 F = T := by
    apply ContinuousLinearMap.ext
    intro u
    apply TauCeti.W1p.ext_value
    apply Lp.ext
    have h1 : TauCeti.W1p.value (coefficientMultiplier hcalc 1 F u) =ᵐ[(volume : Measure X).restrict ballOpens]
        fun x => coefficientValue 2 F x*TauCeti.W1p.value u x := by
      simpa only [TauCeti.Wkp.value_one] using coefficientMultiplier_value_ae hcalc 1 F u
    have h2 : TauCeti.W1p.value (T u) =ᵐ[(volume : Measure X).restrict ballOpens]
        fun x => coefficientValue 2 F x*TauCeti.W1p.value u x := by
      change TauCeti.W1p.value
        (TauCeti.W1p.contDiffSMul (coefficientValue 2 F) hSmooth hq hValue hGrad u) =ᵐ[_] _
      have hh := TauCeti.W1p.value_contDiffSMul_ae (mu:=(volume : Measure X))
        (Omega:=ballOpens) (p:=2) (psi:=coefficientValue 2 F) hSmooth hq hValue hGrad u
      filter_upwards [hh] with x hx
      simpa only [smul_eq_mul] using hx
    exact h1.trans h2.symm
  rw [hEq]
  exact TauCeti.W1p.norm_contDiffSMulL_le hSmooth hq hValue hGrad

end ShrinkingSpheres
