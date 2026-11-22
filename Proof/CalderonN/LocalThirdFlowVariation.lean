module

public import Proof.CalderonN.LocalSecondFlowVariation
import Mathlib.Tactic.Abel

import Mathlib.Tactic

/-! Adapted from `LocalThirdFlowVariation` in the checked Proposition 5.3 release. -/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 15
open Filter
open scoped ContDiff Topology
namespace CalderonN
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

def thirdParameterVariation (F : E × ℝ → G) (h k l : E) (p : E × ℝ) : G :=
  fderiv ℝ (secondParameterVariation F h k) p (l,0)

lemma contDiffAt_secondParameterVariation (F : E × ℝ → G) (h k : E) (p : E × ℝ)
    (hF : ContDiffAt ℝ ∞ F p) : ContDiffAt ℝ ∞ (secondParameterVariation F h k) p :=
  ((contDiffAt_firstParameterVariation F h p hF).fderiv_right (m:=∞) (by simp)).clm_apply contDiffAt_const

lemma contDiffAt_thirdParameterVariation (F : E × ℝ → G) (h k l : E) (p : E × ℝ)
    (hF : ContDiffAt ℝ ∞ F p) : ContDiffAt ℝ ∞ (thirdParameterVariation F h k l) p :=
  ((contDiffAt_secondParameterVariation F h k p hF).fderiv_right (m:=∞) (by simp)).clm_apply contDiffAt_const

/-- The third variational equation is local: the checked second equation is
    required only as a germ in the same initial parameter. -/
theorem hasDerivAt_third_parameter_variation (F : E × ℝ → G) (V : G → G)
    (a h k l : E) (t : ℝ) (hF : ContDiffAt ℝ ∞ F (a,t))
    (hV : ContDiffAt ℝ ∞ V (F (a,t)))
    (hSTime : (fun x => fderiv ℝ (secondParameterVariation F h k) (x,t) (0,1)) =ᶠ[𝓝 a]
      (fun x => fderiv ℝ V (F (x,t)) (secondParameterVariation F h k (x,t))+
        fderiv ℝ (fderiv ℝ V) (F (x,t))
          (firstParameterVariation F k (x,t)) (firstParameterVariation F h (x,t)))) :
    HasDerivAt (fun s => thirdParameterVariation F h k l (a,s))
      (fderiv ℝ V (F (a,t)) (thirdParameterVariation F h k l (a,t))+
        fderiv ℝ (fderiv ℝ V) (F (a,t))
          (firstParameterVariation F l (a,t)) (secondParameterVariation F h k (a,t))+
        fderiv ℝ (fderiv ℝ (fderiv ℝ V)) (F (a,t))
          (firstParameterVariation F l (a,t)) (firstParameterVariation F k (a,t))
            (firstParameterVariation F h (a,t))+
        fderiv ℝ (fderiv ℝ V) (F (a,t))
          (secondParameterVariation F k l (a,t)) (firstParameterVariation F h (a,t))+
        fderiv ℝ (fderiv ℝ V) (F (a,t))
          (firstParameterVariation F k (a,t)) (secondParameterVariation F h l (a,t))) t := by
  let Jh := firstParameterVariation F h
  let Jk := firstParameterVariation F k
  let S := secondParameterVariation F h k
  have hJh := contDiffAt_firstParameterVariation F h (a,t) hF
  have hJk := contDiffAt_firstParameterVariation F k (a,t) hF
  have hS := contDiffAt_secondParameterVariation F h k (a,t) hF
  have hm := hasDerivAt_base_derivative_in_time_local S a l t hS
  have hFs := (hF.comp a (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  have hJhs := (hJh.comp a (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  have hJks := (hJk.comp a (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  have hSs := (hS.comp a (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  have hD1 := ((hV.fderiv_right (m:=∞) (by simp)).differentiableAt (by simp)).hasFDerivAt.comp a hFs.hasFDerivAt
  have hD2 := (((hV.fderiv_right (m:=∞) (by simp)).fderiv_right (m:=∞) (by simp)).differentiableAt
    (by simp)).hasFDerivAt.comp a hFs.hasFDerivAt
  have hLeft := hD1.clm_apply hSs.hasFDerivAt
  have hRight := (hD2.clm_apply hJks.hasFDerivAt).clm_apply hJhs.hasFDerivAt
  simp only [Function.comp_def,id_eq] at hLeft hRight
  have hSum := hLeft.fun_add hRight
  have hValue : fderiv ℝ (fun x => fderiv ℝ S (x,t) (0,1)) a l =
      fderiv ℝ V (F (a,t)) (thirdParameterVariation F h k l (a,t))+
        fderiv ℝ (fderiv ℝ V) (F (a,t))
          (firstParameterVariation F l (a,t)) (secondParameterVariation F h k (a,t))+
        fderiv ℝ (fderiv ℝ (fderiv ℝ V)) (F (a,t))
          (firstParameterVariation F l (a,t)) (firstParameterVariation F k (a,t))
            (firstParameterVariation F h (a,t))+
        fderiv ℝ (fderiv ℝ V) (F (a,t))
          (secondParameterVariation F k l (a,t)) (firstParameterVariation F h (a,t))+
        fderiv ℝ (fderiv ℝ V) (F (a,t))
          (firstParameterVariation F k (a,t)) (secondParameterVariation F h l (a,t)) := by
    rw [hSTime.fderiv_eq,hSum.fderiv]
    simp only [_root_.add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
      fderiv_base_slice_of_contDiffAt F a l t hF,
      fderiv_base_slice_of_contDiffAt (firstParameterVariation F h) a l t hJh,
      fderiv_base_slice_of_contDiffAt (firstParameterVariation F k) a l t hJk,
      fderiv_base_slice_of_contDiffAt (secondParameterVariation F h k) a l t hS]
    simp only [thirdParameterVariation,secondParameterVariation,firstParameterVariation]
    abel
  exact hm.congr_deriv hValue

end CalderonN
