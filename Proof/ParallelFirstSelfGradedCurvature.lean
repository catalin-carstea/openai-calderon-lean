import Proof.FrameCovariantCurvatureComm
import Proof.GradedSphereSectionCovariantDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

lemma three_rotation_inclusion (s t : ℝ) (hst : t ≤ s) (p : I → ℝ) :
    (sphereSobolevInclusionL (s-1) (t-1) (by linarith)).comp (threeRotationL s p)=
      (threeRotationL t p).comp (sphereSobolevInclusionL s t hst) := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [threeRotationL,ContinuousLinearMap.comp_apply,_root_.add_apply,
    _root_.smul_apply,map_add,map_smul]
  have h01 := sphereSobolevRotationL_inclusion_apply s t hst 0 1 u
  have h02 := sphereSobolevRotationL_inclusion_apply s t hst 0 2 u
  have h12 := sphereSobolevRotationL_inclusion_apply s t hst 1 2 u
  rw [←h01,←h02,←h12]

/-- Curvature at every genuine source grade, including positive half.
The twice-lowered output is retained explicitly. -/
theorem three_rotation_half_source_commutator
    (C : X → X →L[ℝ] (I → ℝ)) (U : X → SphereSobolev (1/2:ℝ)) (y a b : X)
    (hC : DifferentiableAt ℝ C y) (hU : ContDiffAt ℝ ∞ U y) :
    gradedSectionCovariantDerivative (sphereSobolevInclusionL (-(1/2:ℝ)) (-(3/2:ℝ)) (by norm_num))
        (fun x v => threeRotationL (-(1/2:ℝ)) (C x v))
        (fun x => gradedSectionCovariantDerivative (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))
          (fun z v => threeRotationL (1/2:ℝ) (C z v)) U x b) y a-
      gradedSectionCovariantDerivative (sphereSobolevInclusionL (-(1/2:ℝ)) (-(3/2:ℝ)) (by norm_num))
        (fun x v => threeRotationL (-(1/2:ℝ)) (C x v))
        (fun x => gradedSectionCovariantDerivative (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))
          (fun z v => threeRotationL (1/2:ℝ) (C z v)) U x a) y b=
    -threeRotationL (-(1/2:ℝ)) (threeConnectionCurvature C y a b)
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) (U y)) := by
  have hCv (v : X) := hC.clm_apply (differentiableAt_const v)
  have hB (v : X) : DifferentiableAt ℝ (fun x => threeRotationL (1/2:ℝ) (C x v)) y := by
    simpa only [Function.comp_def,threeRotationMapL_apply] using
      (threeRotationMapL (1/2:ℝ)).differentiableAt.comp y (hCv v)
  have hD (v w : X) : fderiv ℝ (fun x => threeRotationL (1/2:ℝ) (C x v)) y w=
      threeRotationL (1/2:ℝ) (fderiv ℝ C y w v) := by
    rw [fderiv_threeRotationL (1/2:ℝ) _ y w (hCv v),fderiv_clm_apply_fixed C y w v hC]
  have hJ (p : I → ℝ) (u : SphereSobolev (1/2:ℝ)) :
      sphereSobolevInclusionL (-(1/2:ℝ)) (-(3/2:ℝ)) (by norm_num) (threeRotationL (1/2:ℝ) p u)=
        threeRotationL (-(1/2:ℝ)) p (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) u) := by
    have hh := DFunLike.congr_fun (three_rotation_inclusion (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) p) u
    simpa only [ContinuousLinearMap.comp_apply,sphereSobolevInclusionL,
      show (1/2:ℝ)-1= -(1/2:ℝ) by norm_num,
      show (-(1/2:ℝ))-1= -(3/2:ℝ) by norm_num] using hh
  have hLie : threeRotationL (-(1/2:ℝ)) (C y a) (threeRotationL (1/2:ℝ) (C y b) (U y))-
      threeRotationL (-(1/2:ℝ)) (C y b) (threeRotationL (1/2:ℝ) (C y a) (U y))=
        threeRotationL (-(1/2:ℝ)) (threeRotationBracket (C y a) (C y b))
          (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) (U y)) := by
    have h0 := DFunLike.congr_fun (threeRotationL_lie_commutator (1/2:ℝ) (C y a) (C y b)) (U y)
    have hR (p : I → ℝ) : threeRotationL ((1/2:ℝ)-1) p=threeRotationL (-(1/2:ℝ)) p := by congr 1 <;> norm_num
    have hI : sphereSobolevInclusionL (1/2:ℝ) ((1/2:ℝ)-1) (by norm_num)=
        sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) := by congr 1 <;> norm_num
    simpa only [ContinuousLinearMap.comp_apply,_root_.sub_apply,hR,hI] using h0
  have hJa : (sphereSobolevInclusionL (-(1/2:ℝ)) (-(3/2:ℝ)) (by norm_num)).comp
      (threeRotationL (1/2:ℝ) (C y a))=
        (threeRotationL (-(1/2:ℝ)) (C y a)).comp
          (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)) :=
    ContinuousLinearMap.ext (hJ (C y a))
  have hJb : (sphereSobolevInclusionL (-(1/2:ℝ)) (-(3/2:ℝ)) (by norm_num)).comp
      (threeRotationL (1/2:ℝ) (C y b))=
        (threeRotationL (-(1/2:ℝ)) (C y b)).comp
          (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)) :=
    ContinuousLinearMap.ext (hJ (C y b))
  have h := gradedSectionCovariantDerivative_commutator
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))
    (sphereSobolevInclusionL (-(1/2:ℝ)) (-(3/2:ℝ)) (by norm_num))
    (fun x v => threeRotationL (-(1/2:ℝ)) (C x v)) (fun x v => threeRotationL (1/2:ℝ) (C x v)) U y a b hU
    (hB a) (hB b) hJa hJb
  rw [h,hD b a,hD a b,map_sub,hJ,hJ]
  calc
    _ = -threeRotationL (-(1/2:ℝ)) (fderiv ℝ C y a b) (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) (U y))+
        threeRotationL (-(1/2:ℝ)) (fderiv ℝ C y b a) (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) (U y))+
        threeRotationL (-(1/2:ℝ)) (threeRotationBracket (C y a) (C y b))
          (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) (U y)) := by rw [←hLie];abel
    _ = _ := by
      simp only [threeConnectionCurvature,←threeRotationMapL_apply,map_sub,_root_.sub_apply]
      abel

lemma graded_sphere_covariant_eq_three (s : ℝ) (d : Data) (U : X → SphereSobolev s) (y a : X)
    (hA : ∀ i j,frameConnectionCoefficient d.γ d.frame y a i j= -frameConnectionCoefficient d.γ d.frame y a j i) :
    gradedSphereSectionCovariantDerivative s d U y a=
      gradedSectionCovariantDerivative (sphereSobolevInclusionL s (s-1) (by linarith))
        (fun x v => threeRotationL s (frameConnectionThreeLinear d.γ d.frame x v)) U y a := by
  have h := DFunLike.congr_fun (skew_sum_sobolev_rotation_eq_three s
    (frameConnectionCoefficient d.γ d.frame y a) hA) (U y)
  simpa only [gradedSphereSectionCovariantDerivative,gradedSectionCovariantDerivative,
    frameConnectionThreeLinear_apply,_root_.sum_apply,_root_.smul_apply] using congrArg
      (fun v => sphereSobolevInclusionL s (s-1) (by linarith) (fderiv ℝ U y a)-v) h

lemma graded_sphere_covariant_congr_germ (s : ℝ) (d : Data) {U V : X → SphereSobolev s}
    {y : X} (h : U=ᶠ[𝓝 y] V) (a : X) :
    gradedSphereSectionCovariantDerivative s d U y a=gradedSphereSectionCovariantDerivative s d V y a := by
  simp only [gradedSphereSectionCovariantDerivative,h.fderiv_eq,h.eq_of_nhds]

/-- The actual frame curvature identity extends to the half source grade
with genuine inclusions; arbitrary frame derivatives remain qualitative. -/
theorem half_source_sphere_covariant_commutator {Y : Set X} (hY : IsOpen Y)
    (d : Data) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (hFrame : ∀ x ∈ Y,∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j)=if i=j then 1 else 0)
    (U : X → SphereSobolev (1/2:ℝ)) (hU : ContDiffOn ℝ ∞ U Y)
    {y : X} (hy : y ∈ Y) (a b : X) :
    gradedSphereSectionCovariantDerivative ((1/2:ℝ)-1) d (fun x => gradedSphereSectionCovariantDerivative (1/2:ℝ) d U x b) y a-
      gradedSphereSectionCovariantDerivative ((1/2:ℝ)-1) d (fun x => gradedSphereSectionCovariantDerivative (1/2:ℝ) d U x a) y b=
    frameCurvatureSobolevL ((1/2:ℝ)-1) d.γ d.frame y a b
      (sphereSobolevInclusionL (1/2:ℝ) ((1/2:ℝ)-1) (by linarith) (U y)) := by
  let C := frameConnectionThreeLinear d.γ d.frame
  have hSkew (x : X) (hx : x ∈ Y) (v : X) := frameConnection_skew hY hg hK d.frame he hFrame hx v
  have hInner (v : X) : (fun x => gradedSphereSectionCovariantDerivative (1/2:ℝ) d U x v)=ᶠ[𝓝 y]
      (fun x => gradedSectionCovariantDerivative (sphereSobolevInclusionL (1/2:ℝ) ((1/2:ℝ)-1) (by linarith))
        (fun z w => threeRotationL (1/2:ℝ) (C z w)) U x v) := by
    filter_upwards [hY.mem_nhds hy] with x hx
    exact graded_sphere_covariant_eq_three (1/2:ℝ) d U x v (hSkew x hx v)
  rw [graded_sphere_covariant_congr_germ ((1/2:ℝ)-1) d (hInner b) a,
    graded_sphere_covariant_congr_germ ((1/2:ℝ)-1) d (hInner a) b,
    graded_sphere_covariant_eq_three _ _ _ y a (hSkew y hy a),
    graded_sphere_covariant_eq_three _ _ _ y b (hSkew y hy b)]
  have hCD := ((hg.contDiffOn_frameConnectionThreeLinear hY hK d.frame he).contDiffAt
    (hY.mem_nhds hy)).differentiableAt (by simp)
  have hh := three_rotation_half_source_commutator C U y a b hCD (hU.contDiffAt (hY.mem_nhds hy))
  change _= -threeRotationL ((1/2:ℝ)-1) (threeSkewCoordinates (frameCurvatureCoefficient d.γ d.frame y a b))
    (sphereSobolevInclusionL (1/2:ℝ) ((1/2:ℝ)-1) (by linarith) (U y))
  have hR (p : I → ℝ) : threeRotationL ((1/2:ℝ)-1) p=threeRotationL (-(1/2:ℝ)) p := by congr 1 <;> norm_num
  have hI01 : sphereSobolevInclusionL (1/2:ℝ) ((1/2:ℝ)-1) (by norm_num)=
      sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) := by congr 1 <;> norm_num
  have hI12 : sphereSobolevInclusionL ((1/2:ℝ)-1) (((1/2:ℝ)-1)-1) (by norm_num)=
      sphereSobolevInclusionL (-(1/2:ℝ)) (-(3/2:ℝ)) (by norm_num) := by congr 1 <;> norm_num
  rw [hI01,hI12]
  simp only [hR]
  rw [hh,hg.frameConnectionThreeLinear_curvature hY hK d.frame he hFrame hy a b]

end ShrinkingSpheres.ParallelEnergy
