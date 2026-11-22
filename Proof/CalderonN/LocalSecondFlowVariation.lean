module

public import Proof.CalderonN.LocalFlowVariation

/- Adapted from the supplied SecondFlowVariation.lean. The second-variation
   calculation uses only smooth germs and the first variational equation germ,
   so it applies to the admitted normal map rather than a chosen global flow. -/
import Mathlib.Tactic

/-! Adapted from `LocalSecondFlowVariation` in the checked Proposition 5.3 release. -/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 15
open Filter
open scoped ContDiff Topology
namespace CalderonN
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

def firstParameterVariation (F : E × ℝ → G) (h : E) (p : E × ℝ) : G := fderiv ℝ F p (h,0)

def secondParameterVariation (F : E × ℝ → G) (h k : E) (p : E × ℝ) : G :=
  fderiv ℝ (firstParameterVariation F h) p (k,0)

lemma contDiffAt_firstParameterVariation (F : E × ℝ → G) (h : E) (p : E × ℝ)
    (hF : ContDiffAt ℝ ∞ F p) : ContDiffAt ℝ ∞ (firstParameterVariation F h) p :=
  (hF.fderiv_right (m:=∞) (by simp)).clm_apply contDiffAt_const

/-- Local second variation of an actual smooth ODE family, from its checked first
    variational equation in a neighborhood of the same initial datum. -/
theorem hasDerivAt_second_parameter_variation (F : E × ℝ → G) (V : G → G) (a h k : E) (t : ℝ)
    (hF : ContDiffAt ℝ ∞ F (a,t)) (hV : ContDiffAt ℝ ∞ V (F (a,t)))
    (hJTime : (fun x => fderiv ℝ (firstParameterVariation F h) (x,t) (0,1)) =ᶠ[𝓝 a]
      (fun x => fderiv ℝ V (F (x,t)) (firstParameterVariation F h (x,t)))) :
    HasDerivAt (fun s => secondParameterVariation F h k (a,s))
      (fderiv ℝ V (F (a,t)) (secondParameterVariation F h k (a,t))+
        fderiv ℝ (fderiv ℝ V) (F (a,t))
          (firstParameterVariation F k (a,t)) (firstParameterVariation F h (a,t))) t := by
  let J := firstParameterVariation F h
  have hJ : ContDiffAt ℝ ∞ J (a,t) := contDiffAt_firstParameterVariation F h (a,t) hF
  have hm := hasDerivAt_base_derivative_in_time_local J a k t hJ
  have hFs : DifferentiableAt ℝ (fun x => F (x,t)) a :=
    (hF.comp a (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  have hJs : DifferentiableAt ℝ (fun x => J (x,t)) a :=
    (hJ.comp a (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  have hD := ((hV.fderiv_right (m:=∞) (by simp)).differentiableAt (by simp)).hasFDerivAt.comp a hFs.hasFDerivAt
  have hp := hD.clm_apply hJs.hasFDerivAt
  simp only [Function.comp_def] at hp
  have hJTime' : (fun x => fderiv ℝ J (x,t) (0,1)) =ᶠ[𝓝 a]
      (fun x => fderiv ℝ V (F (x,t)) (J (x,t))) := hJTime
  have hValue : fderiv ℝ (fun x => fderiv ℝ J (x,t) (0,1)) a k =
      fderiv ℝ V (F (a,t)) (secondParameterVariation F h k (a,t))+
        fderiv ℝ (fderiv ℝ V) (F (a,t))
          (firstParameterVariation F k (a,t)) (J (a,t)) := by
    rw [hJTime'.fderiv_eq,hp.fderiv]
    simp only [_root_.add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
      fderiv_base_slice_of_contDiffAt F a k t hF,fderiv_base_slice_of_contDiffAt J a k t hJ]
    rfl
  exact hm.congr_deriv hValue

end CalderonN
