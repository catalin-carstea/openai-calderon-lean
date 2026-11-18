import Proof.RadialDilationParameterJets
import Proof.LocalParameterAffineRemainderJets
import Proof.LocalFlowVariation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.ConnectionError

variable {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

def radialDilationFamily (F : P × ℝ → V) : (P × ℝ) × ℝ → V := F ∘ radialDilationInput

def radialAffineResidual (F : P × ℝ → V) (q : P × ℝ) : V :=
  F q-F (q.1,0)-q.2 • radialFirstDerivative F (q.1,0)

lemma radialDilationFamily_at_zero (F : P × ℝ → V) (q : P × ℝ) :
    radialDilationFamily F (q,0) = F (q.1,0) := by
  simp only [radialDilationFamily,Function.comp_apply,radialDilationInput,mul_zero]

theorem radialFirstDerivative_radialDilationFamily_zero (F : P × ℝ → V)
    (p : P) (tau : ℝ) (hF : ContDiffAt ℝ ∞ F (p,0)) :
    radialFirstDerivative (radialDilationFamily F) ((p,tau),0) =
      (1+tau) • radialFirstDerivative F (p,0) := by
  have hInput : radialDilationInput ((p,tau),(0:ℝ)) = (p,0) := by simp only [radialDilationInput,mul_zero]
  have hFInput : ContDiffAt ℝ ∞ F (radialDilationInput ((p,tau),(0:ℝ))) := by rwa [hInput]
  have hG : ContDiffAt ℝ ∞ (radialDilationFamily F) ((p,tau),0) :=
    hFInput.comp ((p,tau),0) contDiff_radialDilationInput.contDiffAt
  have hTime := hasDerivAt_time_slice (radialDilationFamily F) (p,tau) 0 (hG.differentiableAt (by simp))
  have hScaled : HasDerivAt (fun r : ℝ => (1+tau)*r) (1+tau) 0 := by
    simpa only [Function.id_def,mul_one] using (hasDerivAt_id 0).const_mul (1+tau)
  have hBase : HasDerivAt (fun r => F (p,r)) (radialFirstDerivative F (p,0)) ((1+tau)*0) := by
    simpa only [mul_zero,radialFirstDerivative] using hasDerivAt_time_slice F p 0 (hF.differentiableAt (by simp))
  have hComp := hBase.scomp 0 hScaled
  change HasDerivAt (fun r => radialDilationFamily F ((p,tau),r))
    ((1+tau) • radialFirstDerivative F (p,0)) 0 at hComp
  exact hTime.unique hComp

theorem radialAffineResidual_dilation_eq_germ (F : P × ℝ → V)
    {U : Set (P × ℝ)} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (p : P) (h0 : (p,0) ∈ U) (r : ℝ) :
    (fun q : P × ℝ => radialAffineResidual F (q.1,(1+q.2)*r)) =ᶠ[𝓝 (p,0)]
      (fun q => radialAffineResidual (radialDilationFamily F) (q,r)) := by
  have hNear : ∀ᶠ q : P × ℝ in 𝓝 (p,0),(q.1,0) ∈ U :=
    (continuous_fst.prodMk continuous_const).continuousAt.eventually (hU.mem_nhds h0)
  filter_upwards [hNear] with q hq
  have hFirst := radialFirstDerivative_radialDilationFamily_zero F q.1 q.2
    (hF.contDiffAt (hU.mem_nhds hq))
  simp only [radialAffineResidual,radialDilationFamily_at_zero,hFirst]
  change F (q.1,(1+q.2)*r)-F (q.1,0)-((1+q.2)*r) • radialFirstDerivative F (q.1,0) =
    F (q.1,(1+q.2)*r)-F (q.1,0)-r • ((1+q.2) • radialFirstDerivative F (q.1,0))
  rw [smul_smul,mul_comm r (1+q.2)]

end ShrinkingSpheres
