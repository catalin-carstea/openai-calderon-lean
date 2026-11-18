import Proof.LocalThirdFlowVariation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
open Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

def fourthParameterVariation (F : E × ℝ → G) (h k l m : E) (q : E × ℝ) : G :=
  fderiv ℝ (thirdParameterVariation F h k l) q (m,0)

lemma contDiffAt_fourthParameterVariation (F : E × ℝ → G) (h k l m : E) (q : E × ℝ)
    (hF : ContDiffAt ℝ ∞ F q) : ContDiffAt ℝ ∞ (fourthParameterVariation F h k l m) q :=
  ((contDiffAt_thirdParameterVariation F h k l q hF).fderiv_right (m:=∞) (by simp)).clm_apply contDiffAt_const

def thirdParameterVariationRhs (F : E × ℝ → G) (V : G → G) (h k l : E) (q : E × ℝ) : G :=
  let J := fun a => firstParameterVariation F a q
  let S := fun a b => secondParameterVariation F a b q
  let T := thirdParameterVariation F h k l q
  let A1 := fderiv ℝ V (F q)
  let A2 := fderiv ℝ (fderiv ℝ V) (F q)
  let A3 := fderiv ℝ (fderiv ℝ (fderiv ℝ V)) (F q)
  A1 T+A2 (J l) (S h k)+A3 (J l) (J k) (J h)+A2 (S k l) (J h)+A2 (J k) (S h l)

def fourthParameterVariationRhs (F : E × ℝ → G) (V : G → G) (h k l m : E) (q : E × ℝ) : G :=
  let J := fun a => firstParameterVariation F a q
  let S := fun a b => secondParameterVariation F a b q
  let T := fun a b c => thirdParameterVariation F a b c q
  let U := fourthParameterVariation F h k l m q
  let A1 := fderiv ℝ V (F q)
  let A2 := fderiv ℝ (fderiv ℝ V) (F q)
  let A3 := fderiv ℝ (fderiv ℝ (fderiv ℝ V)) (F q)
  let A4 := fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ V))) (F q)
  A1 U+A2 (J m) (T h k l)+
    A3 (J m) (J l) (S h k)+A2 (S l m) (S h k)+A2 (J l) (T h k m)+
    A4 (J m) (J l) (J k) (J h)+A3 (S l m) (J k) (J h)+
    A3 (J l) (S k m) (J h)+A3 (J l) (J k) (S h m)+
    A3 (J m) (S k l) (J h)+A2 (T k l m) (J h)+A2 (S k l) (S h m)+
    A3 (J m) (J k) (S h l)+A2 (S k m) (S h l)+A2 (J k) (T h l m)

/-- Differentiate the genuine third variational equation as a local germ.
    No global flow or global initial-parameter domain is required. -/
theorem hasDerivAt_fourth_parameter_variation (F : E × ℝ → G) (V : G → G)
    (a h k l m : E) (t : ℝ) (hF : ContDiffAt ℝ ∞ F (a,t))
    (hV : ContDiffAt ℝ ∞ V (F (a,t)))
    (hTTime : (fun x => fderiv ℝ (thirdParameterVariation F h k l) (x,t) (0,1)) =ᶠ[𝓝 a]
      fun x => thirdParameterVariationRhs F V h k l (x,t)) :
    HasDerivAt (fun s => fourthParameterVariation F h k l m (a,s))
      (fourthParameterVariationRhs F V h k l m (a,t)) t := by
  have hJh := contDiffAt_firstParameterVariation F h (a,t) hF
  have hJk := contDiffAt_firstParameterVariation F k (a,t) hF
  have hJl := contDiffAt_firstParameterVariation F l (a,t) hF
  have hShk := contDiffAt_secondParameterVariation F h k (a,t) hF
  have hSkl := contDiffAt_secondParameterVariation F k l (a,t) hF
  have hShl := contDiffAt_secondParameterVariation F h l (a,t) hF
  have hT := contDiffAt_thirdParameterVariation F h k l (a,t) hF
  have hm := hasDerivAt_base_derivative_in_time_local (thirdParameterVariation F h k l) a m t hT
  have hFs := (hF.comp a (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  have hJhs := (hJh.comp a (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  have hJks := (hJk.comp a (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  have hJls := (hJl.comp a (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  have hShks := (hShk.comp a (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  have hSkls := (hSkl.comp a (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  have hShls := (hShl.comp a (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  have hTs := (hT.comp a (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  have hD1 := ((hV.fderiv_right (m:=∞) (by simp)).differentiableAt (by simp)).hasFDerivAt.comp a hFs.hasFDerivAt
  have hD2 := (((hV.fderiv_right (m:=∞) (by simp)).fderiv_right (m:=∞) (by simp)).differentiableAt
    (by simp)).hasFDerivAt.comp a hFs.hasFDerivAt
  have hD3 := ((((hV.fderiv_right (m:=∞) (by simp)).fderiv_right (m:=∞) (by simp)).fderiv_right
    (m:=∞) (by simp)).differentiableAt (by simp)).hasFDerivAt.comp a hFs.hasFDerivAt
  have h1 := hD1.clm_apply hTs.hasFDerivAt
  have h2 := (hD2.clm_apply hJls.hasFDerivAt).clm_apply hShks.hasFDerivAt
  have h3 := ((hD3.clm_apply hJls.hasFDerivAt).clm_apply hJks.hasFDerivAt).clm_apply hJhs.hasFDerivAt
  have h4 := (hD2.clm_apply hSkls.hasFDerivAt).clm_apply hJhs.hasFDerivAt
  have h5 := (hD2.clm_apply hJks.hasFDerivAt).clm_apply hShls.hasFDerivAt
  simp only [Function.comp_def,id_eq] at h1 h2 h3 h4 h5
  have hSum := (((h1.fun_add h2).fun_add h3).fun_add h4).fun_add h5
  have hValue : fderiv ℝ (fun x => fderiv ℝ (thirdParameterVariation F h k l) (x,t) (0,1)) a m =
      fourthParameterVariationRhs F V h k l m (a,t) := by
    rw [hTTime.fderiv_eq]
    change fderiv ℝ (fun x =>
      fderiv ℝ V (F (x,t)) (thirdParameterVariation F h k l (x,t))+
      fderiv ℝ (fderiv ℝ V) (F (x,t)) (firstParameterVariation F l (x,t)) (secondParameterVariation F h k (x,t))+
      fderiv ℝ (fderiv ℝ (fderiv ℝ V)) (F (x,t)) (firstParameterVariation F l (x,t))
        (firstParameterVariation F k (x,t)) (firstParameterVariation F h (x,t))+
      fderiv ℝ (fderiv ℝ V) (F (x,t)) (secondParameterVariation F k l (x,t)) (firstParameterVariation F h (x,t))+
      fderiv ℝ (fderiv ℝ V) (F (x,t)) (firstParameterVariation F k (x,t)) (secondParameterVariation F h l (x,t))) a m = _
    rw [hSum.fderiv]
    simp only [fourthParameterVariationRhs,_root_.add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
      fderiv_base_slice_of_contDiffAt F a m t hF,
      fderiv_base_slice_of_contDiffAt (firstParameterVariation F h) a m t hJh,
      fderiv_base_slice_of_contDiffAt (firstParameterVariation F k) a m t hJk,
      fderiv_base_slice_of_contDiffAt (firstParameterVariation F l) a m t hJl,
      fderiv_base_slice_of_contDiffAt (secondParameterVariation F h k) a m t hShk,
      fderiv_base_slice_of_contDiffAt (secondParameterVariation F k l) a m t hSkl,
      fderiv_base_slice_of_contDiffAt (secondParameterVariation F h l) a m t hShl,
      fderiv_base_slice_of_contDiffAt (thirdParameterVariation F h k l) a m t hT]
    simp only [fourthParameterVariation,thirdParameterVariation,secondParameterVariation,firstParameterVariation]
    abel
  exact hm.congr_deriv hValue

end ShrinkingSpheres
