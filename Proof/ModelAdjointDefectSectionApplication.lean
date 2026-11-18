import Proof.ModelAdjointDefectHigherCore
import Proof.CovariantTensorSectionApplication
import Proof.FlatLoweringSectionCalculus

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

lemma modelAdjointDefectSobolevL_two_coarse (d : Data) (y : X) (u : SphereSobolev 2) :
    sphereSobolevInclusionL 1 0 (by norm_num) (modelAdjointDefectSobolevL 2 d y u)=
      modelAdjointDefectCoarseL d y (sphereSobolevInclusionL 2 1 (by norm_num) u) := by
  simp only [modelAdjointDefectSobolevL,modelAdjointDefectCoarseL,_root_.sum_apply,
    _root_.smul_apply,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun z => modelLogRadiusCoefficient d i y • z) (flatLoweringSobolevL_two_coarse i u)

lemma modelAdjointDefectSobolevL_three_one (d : Data) (y : X) (u : SphereSobolev 3) :
    sphereSobolevInclusionL 2 1 (by norm_num) (modelAdjointDefectSobolevL 3 d y u)=
      modelAdjointDefectSobolevL 2 d y (sphereSobolevInclusionL 3 2 (by norm_num) u) := by
  have hI : sphereSobolevInclusionL ((3:ℝ)-1) ((2:ℝ)-1) (by norm_num)=
      sphereSobolevInclusionL 2 1 (by norm_num) := by congr 1 <;> norm_num
  have hh := modelAdjointDefectSobolevL_inclusion 3 2 (by norm_num) d y
  rw [hI] at hh
  exact (DFunLike.congr_fun hh u).symm

theorem oneSectionCovariantDerivative_modelAdjointDefect {Y : Set X} (hY : IsOpen Y)
    (d : Data) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (hFrame : ∀ x ∈ Y,∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j)=if i=j then 1 else 0)
    (hlog : ContDiffOn ℝ ∞ (fun x => Real.log (d.radius x)) Y)
    (U : X → SphereSobolev 2) {y : X} (hy : y ∈ Y) (hU : DifferentiableAt ℝ U y) (a : X) :
    oneSectionCovariantDerivative d (fun x => modelAdjointDefectSobolevL 2 d x (U x)) y a=
      modelAdjointDefectFirstCoarseL d a y (sphereSobolevInclusionL 2 1 (by norm_num) (U y))+
        modelAdjointDefectCoarseL d y (highSectionCovariantDerivative d U y a) := by
  have hG := modelAdjointDefectCoarseL_covariant_graph hY d hg hK he hFrame hlog hy a
  have hZ := ((contDiffOn_modelAdjointDefectCoarseL hY d hlog he).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)
  have hZ2 := ((contDiffOn_modelAdjointDefectSobolevL hY 2 d hlog he).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)
  exact hG.apply_oneSection hZ U hU (fun x => modelAdjointDefectSobolevL 2 d x (U x))
    (hZ2.clm_apply hU) (Filter.Eventually.of_forall (fun x => modelAdjointDefectSobolevL_two_coarse d x (U x)))

/-- The actual H3 source produces a genuine H2 model-defect section.
Its coarse derivative is identified with the SAME controlled coarse jet
and H2 source derivative through proved inclusion squares. -/
theorem highSectionCovariantDerivative_modelAdjointDefect_three_coarse {Y : Set X} (hY : IsOpen Y)
    (d : Data) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (hFrame : ∀ x ∈ Y,∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j)=if i=j then 1 else 0)
    (hlog : ContDiffOn ℝ ∞ (fun x => Real.log (d.radius x)) Y)
    (U : X → SphereSobolev 2) (V : X → SphereSobolev 3)
    (hCompat : ∀ x,sphereSobolevInclusionL 3 2 (by norm_num) (V x)=U x)
    {y : X} (hy : y ∈ Y) (hU : DifferentiableAt ℝ U y) (hV : DifferentiableAt ℝ V y) (a : X) :
    sphereSobolevInclusionL 1 0 (by norm_num)
      (highSectionCovariantDerivative d (fun x => modelAdjointDefectSobolevL 3 d x (V x)) y a)=
      modelAdjointDefectFirstCoarseL d a y (sphereSobolevInclusionL 2 1 (by norm_num) (U y))+
        modelAdjointDefectCoarseL d y (highSectionCovariantDerivative d U y a) := by
  have hZ3 := ((contDiffOn_modelAdjointDefectSobolevL hY 3 d hlog he).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)
  have hW : DifferentiableAt ℝ (fun x => modelAdjointDefectSobolevL 3 d x (V x)) y := hZ3.clm_apply hV
  rw [←oneSectionCovariantDerivative_high_inclusion d _ y a hW]
  have hOut : (fun x => sphereSobolevInclusionL 2 1 (by norm_num) (modelAdjointDefectSobolevL 3 d x (V x)))=
      (fun x => modelAdjointDefectSobolevL 2 d x (U x)) := by
    funext x
    rw [modelAdjointDefectSobolevL_three_one,hCompat x]
  rw [hOut]
  exact oneSectionCovariantDerivative_modelAdjointDefect hY d hg hK he hFrame hlog U hy hU a

end ShrinkingSpheres
