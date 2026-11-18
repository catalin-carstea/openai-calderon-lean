import Proof.ModelCovariantSections
import Proof.CanonicalLoweringCovariantGraph
import Proof.CovariantRotationGraphOperations
import Proof.FrameCovectorDerivative
import Proof.FrameLogRadiusComponentBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

def modelAdjointDefectSobolevL (s : ℝ) (d : Data) (y : X) : SphereSobolev s →L[ℝ] SphereSobolev (s-1) :=
  ∑ i : I,modelLogRadiusCoefficient d i y • flatLoweringSobolevL s i

def modelAdjointDefectCoarseL (d : Data) (y : X) : SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  ∑ i : I,modelLogRadiusCoefficient d i y • flatOneLoweringL i

def modelAdjointDefectFirstCoarseL (d : Data) (a y : X) : SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  ∑ i : I,hessianBilinear d.γ (fun x => Real.log (d.radius x)) y a (d.frame y i) • flatOneLoweringL i

lemma modelAdjointDefectCoarseL_section (d : Data) (U : X → SphereSobolev 2) (y : X) :
    modelAdjointDefectCoarseL d y (sphereSobolevInclusionL 2 1 (by norm_num) (U y))=
      modelAdjointDefectSection d U y := by
  simp only [modelAdjointDefectCoarseL,modelAdjointDefectSection,_root_.sum_apply,_root_.smul_apply,flatOneLoweringL]

lemma modelAdjointDefectSobolevL_inclusion (s t : ℝ) (hst : t ≤ s) (d : Data) (y : X) :
    (modelAdjointDefectSobolevL t d y).comp (sphereSobolevInclusionL s t hst)=
      (sphereSobolevInclusionL (s-1) (t-1) (by linarith)).comp (modelAdjointDefectSobolevL s d y) := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [modelAdjointDefectSobolevL,ContinuousLinearMap.comp_apply,_root_.sum_apply,
    _root_.smul_apply,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun z => modelLogRadiusCoefficient d i y • z)
    (DFunLike.congr_fun (flatLoweringSobolevL_inclusion s t hst i) u)

lemma norm_modelAdjointDefectSobolevL_le (s : ℝ) (d : Data) (y : X)
    (hFrame : ∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j)=if i=j then 1 else 0) :
    ‖modelAdjointDefectSobolevL s d y‖ ≤
      (∑ i : I,‖flatLoweringSobolevL s i‖)*beta d.γ d.radius y := by
  calc
    _ ≤ ∑ i : I,‖modelLogRadiusCoefficient d i y • flatLoweringSobolevL s i‖ := norm_sum_le _ _
    _ ≤ ∑ i : I,beta d.γ d.radius y*‖flatLoweringSobolevL s i‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right
        (frame_logRadius_component_bound d.γ d.frame d.radius y hFrame i) (norm_nonneg _)
    _ = _ := by rw [←Finset.mul_sum];ring

lemma contDiffOn_modelAdjointDefectCoarseL {Y : Set X} (hY : IsOpen Y) (d : Data)
    (hlog : ContDiffOn ℝ ∞ (fun x => Real.log (d.radius x)) Y)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y) :
    ContDiffOn ℝ ∞ (modelAdjointDefectCoarseL d) Y :=
  ContDiffOn.sum (fun i _ => ((hlog.fderiv_of_isOpen hY (by simp)).clm_apply (he i)).smul contDiffOn_const)

lemma modelLogRadiusCoefficient_plus_connection_eq_hessian {Y : Set X} (hY : IsOpen Y)
    (d : Data) (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (hlog : ContDiffOn ℝ ∞ (fun x => Real.log (d.radius x)) Y) {y : X} (hy : y ∈ Y)
    (hFrame : ∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j)=if i=j then 1 else 0)
    (a : X) (hSkew : ∀ i j,frameConnectionCoefficient d.γ d.frame y a i j=
      -frameConnectionCoefficient d.γ d.frame y a j i) (j : I) :
    fderiv ℝ (modelLogRadiusCoefficient d j) y a+
      ∑ i : I,modelLogRadiusCoefficient d i y*frameConnectionCoefficient d.γ d.frame y a i j=
        hessianBilinear d.γ (fun x => Real.log (d.radius x)) y a (d.frame y j) := by
  have hDLog : DifferentiableAt ℝ (fderiv ℝ (fun x => Real.log (d.radius x))) y :=
    ((hlog.fderiv_of_isOpen (m:=∞) hY (by simp)).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)
  have hh := frame_covector_derivative_eq_hessian d.γ d.frame (fun x => Real.log (d.radius x)) y a j
    hDLog (((he j).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)) hFrame
  have hSum : (∑ i : I,modelLogRadiusCoefficient d i y*frameConnectionCoefficient d.γ d.frame y a i j)=
      -(∑ i : I,frameConnectionCoefficient d.γ d.frame y a j i*modelLogRadiusCoefficient d i y) := by
    rw [←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [hSkew i j]
    ring
  rw [hSum]
  exact hh

/-- Covariant differentiation of the actual model defect cancels every
frame derivative and gives precisely the log-radius Hessian coefficients. -/
theorem modelAdjointDefectCoarseL_covariant_graph {Y : Set X} (hY : IsOpen Y)
    (d : Data) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (hFrame : ∀ x ∈ Y,∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j)=if i=j then 1 else 0)
    (hlog : ContDiffOn ℝ ∞ (fun x => Real.log (d.radius x)) Y) {y : X} (hy : y ∈ Y) (a : X) :
    CoarseCovariantRotationGraph d y a (modelAdjointDefectCoarseL d) (modelAdjointDefectFirstCoarseL d a y) := by
  let f := modelLogRadiusCoefficient d
  let G := frameConnectionCoefficient d.γ d.frame y a
  have hSkew (i j : I) : G i j= -G j i := frameConnection_skew hY hg hK d.frame he hFrame hy a i j
  have hfi (i : I) : DifferentiableAt ℝ (f i) y :=
    (((hlog.fderiv_of_isOpen hY (by simp)).clm_apply (he i)).contDiffAt
      (hY.mem_nhds hy)).differentiableAt (by simp)
  have hCoeff (j : I) : fderiv ℝ (f j) y a+∑ i : I,f i y*G i j=
      hessianBilinear d.γ (fun x => Real.log (d.radius x)) y a (d.frame y j) :=
    modelLogRadiusCoefficient_plus_connection_eq_hessian hY d he hlog hy (hFrame y hy) a hSkew j
  let F := fun (i : I) x => f i x • flatOneLoweringL i
  let S := fun i => f i y • (∑ k : I,G i k • flatOneLoweringL k)+fderiv ℝ (f i) y a • flatOneLoweringL i
  have hi (i : I) : CoarseCovariantRotationGraph d y a (F i) (S i) :=
    (flatOneLoweringL_covariant_graph d y a hSkew i).smul (f i) (hfi i) (differentiableAt_const _)
  have hSum := CoarseCovariantRotationGraph.sum_three F S hi (fun i => (hfi i).smul_const _)
  have hS : (∑ i : I,S i)=modelAdjointDefectFirstCoarseL d a y := by
    calc
      _ = ∑ j : I,(fderiv ℝ (f j) y a+∑ i : I,f i y*G i j) • flatOneLoweringL j := by
        simp only [S,Fin.sum_univ_three,smul_add,smul_smul,add_smul]
        module
      _ = _ := by simp only [hCoeff,modelAdjointDefectFirstCoarseL]
  rw [hS] at hSum
  exact hSum

end ShrinkingSpheres
