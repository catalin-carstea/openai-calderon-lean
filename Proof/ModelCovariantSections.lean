import Proof.CanonicalLoweringSectionOutput
import Proof.SupportedCovariantSections
import Proof.HighSectionCovariantDerivativeLinear

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic OperatorForms

def modelLogRadiusCoefficient (d : Data) (i : I) (y : X) : ℝ :=
  fderiv ℝ (fun x => Real.log (d.radius x)) y (d.frame y i)

def modelRaisingSection (d : Data) (U : X → SphereSobolev 2) (y : X) : SphereSobolev 0 :=
  ∑ i : I,flatOneRaisingL i (highSectionModelPlus d U y i)

def modelLoweringSection (d : Data) (U : X → SphereSobolev 2) (y : X) : SphereSobolev 0 :=
  ∑ i : I,flatLoweringSobolevL 1 i (highSectionModelMinus d U y i)

def modelAdjointDefectSection (d : Data) (U : X → SphereSobolev 2) (y : X) : SphereSobolev 0 :=
  ∑ i : I,modelLogRadiusCoefficient d i y •
    flatLoweringSobolevL 1 i (sphereSobolevInclusionL 2 1 (by norm_num) (U y))

lemma modelCovariantSections_zero_off (d : Data) (U : X → SphereSobolev 2)
    (S : Set X) (hS : IsClosed S) (h0 : ∀ x ∉ S,U x=0) (x : X) (hx : x ∉ S) :
    modelRaisingSection d U x=0 ∧ modelLoweringSection d U x=0 ∧ modelAdjointDefectSection d U x=0 := by
  have hD (i : I) := highSectionCovariantDerivative_zero_off d U S hS h0 (d.frame x i) x hx
  simp only [modelRaisingSection,modelLoweringSection,modelAdjointDefectSection,
    highSectionModelPlus,highSectionModelMinus,hD,h0 x hx,map_zero,smul_zero,
    zero_add,neg_zero,Finset.sum_const_zero,and_self]

/-- The actual model raising, lowering, and adjoint-defect sections all
preserve the same smooth supported core. Only qualitative geometry and
log-radius smoothness are used. -/
theorem contDiff_supported_modelCovariantSections {Y : Set X} (hY : IsOpen Y)
    (d : Data) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (hlog : ContDiffOn ℝ ∞ (fun x => Real.log (d.radius x)) Y)
    (U : X → SphereSobolev 2) (hU : ContDiff ℝ ∞ U)
    (S : Set X) (hS : IsClosed S) (hSY : S ⊆ Y) (h0 : ∀ x ∉ S,U x=0) :
    ContDiff ℝ ∞ (modelRaisingSection d U) ∧ ContDiff ℝ ∞ (modelLoweringSection d U) ∧
      ContDiff ℝ ∞ (modelAdjointDefectSection d U) := by
  have hfi (i : I) : ContDiffOn ℝ ∞ (modelLogRadiusCoefficient d i) Y :=
    (hlog.fderiv_of_isOpen hY (by simp)).clm_apply (he i)
  let HD := fun (i : I) x => highSectionCovariantDerivative d U x (d.frame x i)
  have hHLocal (i : I) : ContDiffOn ℝ ∞ (HD i) Y := by
    simpa only [HD,highSectionCovariantDerivativeLinear_apply] using
      (contDiffOn_highSectionCovariantDerivativeLinear hY d hg hK he U hU.contDiffOn).clm_apply (he i)
  have hHOff (i : I) (x : X) (hx : x ∉ S) : HD i x=0 :=
    highSectionCovariantDerivative_zero_off d U S hS h0 (d.frame x i) x hx
  have hH (i : I) : ContDiff ℝ ∞ (HD i) := contDiff_of_tsupport_subset hY _ (hHLocal i)
    ((tsupport_subset_of_zero_off _ S hS (hHOff i)).trans hSY)
  have hB : ContDiff ℝ ∞ (fun x => sphereSobolevShiftedDegreeL 2 (U x)) :=
    (sphereSobolevShiftedDegreeL 2).contDiff.comp hU
  have hB0 (x : X) (hx : x ∉ S) : sphereSobolevShiftedDegreeL 2 (U x)=0 := by rw [h0 x hx,map_zero]
  have hW (i : I) : ContDiff ℝ ∞ (fun x => modelLogRadiusCoefficient d i x • sphereSobolevShiftedDegreeL 2 (U x)) :=
    contDiff_supported_smul _ _ S hS hB hB0 (fun x hx => (hfi i).contDiffAt (hY.mem_nhds (hSY hx)))
  have hP (i : I) : ContDiff ℝ ∞ (fun x => highSectionModelPlus d U x i) := (hH i).add (hW i)
  have hM (i : I) : ContDiff ℝ ∞ (fun x => highSectionModelMinus d U x i) := (hH i).neg.add (hW i)
  have hL (i : I) : ContDiff ℝ ∞ (fun x => flatLoweringSobolevL 1 i
      (sphereSobolevInclusionL 2 1 (by norm_num) (U x))) :=
    (flatLoweringSobolevL 1 i).contDiff.comp ((sphereSobolevInclusionL 2 1 (by norm_num)).contDiff.comp hU)
  have hL0 (i : I) (x : X) (hx : x ∉ S) : flatLoweringSobolevL 1 i
      (sphereSobolevInclusionL 2 1 (by norm_num) (U x))=0 := by rw [h0 x hx,map_zero,map_zero]
  refine ⟨ContDiff.sum (fun i _ => (flatOneRaisingL i).contDiff.comp (hP i)),
    ContDiff.sum (fun i _ => (flatLoweringSobolevL 1 i).contDiff.comp (hM i)),?_⟩
  exact ContDiff.sum (fun i _ => contDiff_supported_smul _ _ S hS (hL i) (hL0 i)
    (fun x hx => (hfi i).contDiffAt (hY.mem_nhds (hSY hx))))

end ShrinkingSpheres
