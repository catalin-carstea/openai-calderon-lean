import Proof.GradedLoweringSectionCovariantDerivative
import Proof.ModelAdjointDefectFirstBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic OperatorForms

private lemma three_weighted_matrix_collect {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : I → E) (G : I → I → ℝ) (f df : I → ℝ) :
    (∑ i : I,(df i • V i+f i • ∑ k : I,G i k • V k))=
      ∑ j : I,(df j+∑ i : I,f i*G i j) • V j := by
  simp only [Fin.sum_univ_three,smul_add,smul_smul,add_smul]
  module

private lemma three_linear_packet_collect {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (J : E →L[ℝ] F)
    (v t : I → E) (w : I → F) (f df : I → ℝ) :
    (∑ i : I,(df i • J (v i)+f i • (w i+J (t i))))=
      (∑ i : I,f i • w i)+J (∑ i : I,(df i • v i+f i • t i)) := by
  simp only [map_sum,map_add,map_smul,smul_add,Fin.sum_univ_three]
  abel

def modelAdjointDefectFirstSobolevL (s : ℝ) (d : Data) (a y : X) :
    SphereSobolev s →L[ℝ] SphereSobolev (s-1) :=
  ∑ i : I,hessianBilinear d.γ (fun x => Real.log (d.radius x)) y a (d.frame y i) • flatLoweringSobolevL s i

lemma modelAdjointDefectFirstSobolevL_inclusion (s t : ℝ) (hst : t ≤ s) (d : Data) (a y : X) :
    (modelAdjointDefectFirstSobolevL t d a y).comp (sphereSobolevInclusionL s t hst)=
      (sphereSobolevInclusionL (s-1) (t-1) (by linarith)).comp (modelAdjointDefectFirstSobolevL s d a y) := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [modelAdjointDefectFirstSobolevL,ContinuousLinearMap.comp_apply,_root_.sum_apply,
    _root_.smul_apply,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun z => hessianBilinear d.γ (fun x => Real.log (d.radius x)) y a (d.frame y i) • z)
    (DFunLike.congr_fun (flatLoweringSobolevL_inclusion s t hst i) u)

lemma contDiffOn_modelAdjointDefectSobolevL {Y : Set X} (hY : IsOpen Y) (s : ℝ) (d : Data)
    (hlog : ContDiffOn ℝ ∞ (fun x => Real.log (d.radius x)) Y)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y) :
    ContDiffOn ℝ ∞ (modelAdjointDefectSobolevL s d) Y :=
  ContDiffOn.sum (fun i _ => ((hlog.fderiv_of_isOpen hY (by simp)).clm_apply (he i)).smul contDiffOn_const)

theorem contDiff_supported_modelAdjointDefectSobolevL_apply {Y : Set X} (hY : IsOpen Y)
    (s : ℝ) (d : Data) (hlog : ContDiffOn ℝ ∞ (fun x => Real.log (d.radius x)) Y)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (U : X → SphereSobolev s) (hU : ContDiff ℝ ∞ U)
    (S : Set X) (hS : IsClosed S) (hSY : S ⊆ Y) (h0 : ∀ x ∉ S,U x=0) :
    ContDiff ℝ ∞ (fun x => modelAdjointDefectSobolevL s d x (U x)) ∧
      ∀ x ∉ S,modelAdjointDefectSobolevL s d x (U x)=0 := by
  have hOp := contDiffOn_modelAdjointDefectSobolevL hY s d hlog he
  exact ⟨contDiff_supported_operator_apply U (modelAdjointDefectSobolevL s d) S hS hU h0
    (fun x hx => hOp.contDiffAt (hY.mem_nhds (hSY hx))),
    fun x hx => by rw [h0 x hx,map_zero]⟩

/-- Differentiating the actual model defect applied to a genuine high
section yields its SAME high first jet and source covariant derivative.
This supplies a real common core for the later mixed integrations. -/
theorem gradedSphereSectionCovariantDerivative_modelAdjointDefect {Y : Set X} (hY : IsOpen Y)
    (s : ℝ) (d : Data) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (hFrame : ∀ x ∈ Y,∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j)=if i=j then 1 else 0)
    (hlog : ContDiffOn ℝ ∞ (fun x => Real.log (d.radius x)) Y)
    (U : X → SphereSobolev s) {y : X} (hy : y ∈ Y) (hU : DifferentiableAt ℝ U y) (a : X) :
    gradedSphereSectionCovariantDerivative (s-1) d (fun x => modelAdjointDefectSobolevL s d x (U x)) y a=
      modelAdjointDefectSobolevL (s-1) d y (gradedSphereSectionCovariantDerivative s d U y a)+
      sphereSobolevInclusionL (s-1) ((s-1)-1) (by linarith)
        (modelAdjointDefectFirstSobolevL s d a y (U y)) := by
  let f := modelLogRadiusCoefficient d
  let G := frameConnectionCoefficient d.γ d.frame y a
  let V := fun i => flatLoweringSobolevL s i (U y)
  let J := sphereSobolevInclusionL (s-1) ((s-1)-1) (by linarith)
  have hSkew (p q : I) : G p q= -G q p := frameConnection_skew hY hg hK d.frame he hFrame hy a p q
  have hfi (i : I) : DifferentiableAt ℝ (f i) y :=
    (((hlog.fderiv_of_isOpen hY (by simp)).clm_apply (he i)).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)
  have hCoeff (j : I) : fderiv ℝ (f j) y a+∑ i : I,f i y*G i j=
      hessianBilinear d.γ (fun x => Real.log (d.radius x)) y a (d.frame y j) :=
    modelLogRadiusCoefficient_plus_connection_eq_hessian hY d he hlog hy (hFrame y hy) a hSkew j
  have hCollect : (∑ i : I,(fderiv ℝ (f i) y a • V i+f i y • ∑ k : I,G i k • V k))=
      modelAdjointDefectFirstSobolevL s d a y (U y) := by
    rw [three_weighted_matrix_collect V G (fun i => f i y) (fun i => fderiv ℝ (f i) y a)]
    simp only [hCoeff,modelAdjointDefectFirstSobolevL,_root_.sum_apply,_root_.smul_apply,V]
  let Ui := fun (i : I) x => f i x • flatLoweringSobolevL s i (U x)
  have hUi (i : I) : DifferentiableAt ℝ (Ui i) y := (hfi i).smul ((flatLoweringSobolevL s i).differentiableAt.comp y hU)
  have hOut : (fun x => modelAdjointDefectSobolevL s d x (U x))=(fun x => ∑ i : I,Ui i x) := by
    funext x
    simp only [modelAdjointDefectSobolevL,_root_.sum_apply,_root_.smul_apply,Ui,f]
  rw [hOut,gradedSphereSectionCovariantDerivative_sum_three (s-1) d Ui y a hUi]
  have hTerm (i : I) : gradedSphereSectionCovariantDerivative (s-1) d (Ui i) y a=
      fderiv ℝ (f i) y a • J (V i)+f i y •
        (flatLoweringSobolevL (s-1) i (gradedSphereSectionCovariantDerivative s d U y a)+
          J (∑ k : I,G i k • V k)) := by
    rw [gradedSphereSectionCovariantDerivative_smul (s-1) d (f i)
      (fun x => flatLoweringSobolevL s i (U x)) y a (hfi i)
      ((flatLoweringSobolevL s i).differentiableAt.comp y hU),
      gradedSphereSectionCovariantDerivative_flatLowering s d U y a hU hSkew i]
  simp only [hTerm]
  calc
    _ = (∑ i : I,f i y • flatLoweringSobolevL (s-1) i (gradedSphereSectionCovariantDerivative s d U y a))+
        J (∑ i : I,(fderiv ℝ (f i) y a • V i+f i y • ∑ k : I,G i k • V k)) :=
      three_linear_packet_collect J V (fun i => ∑ k : I,G i k • V k)
        (fun i => flatLoweringSobolevL (s-1) i (gradedSphereSectionCovariantDerivative s d U y a))
        (fun i => f i y) (fun i => fderiv ℝ (f i) y a)
    _ = _ := by rw [hCollect];simp only [modelAdjointDefectSobolevL,_root_.sum_apply,_root_.smul_apply,f,J]

end ShrinkingSpheres
