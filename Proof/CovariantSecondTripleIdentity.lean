import Proof.OneSectionCovariantInner
import Proof.FrameCovariantCurvatureComm
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
open OAI.AnisotropicCalderon.SphereHarmonic

lemma oneSectionCovariantDerivative_inner_fderiv (d : Data) (U V : X → SphereSobolev 1)
    (y a : X) (hU : DifferentiableAt ℝ U y) (hV : DifferentiableAt ℝ V y) :
    fderiv ℝ (fun x => ⟪sphereSobolevInclusionL 1 0 (by norm_num) (U x),
      sphereSobolevInclusionL 1 0 (by norm_num) (V x)⟫_ℝ) y a=
    ⟪sphereSobolevInclusionL 1 0 (by norm_num) (U y),oneSectionCovariantDerivative d V y a⟫_ℝ+
      ⟪oneSectionCovariantDerivative d U y a,sphereSobolevInclusionL 1 0 (by norm_num) (V y)⟫_ℝ := by
  let I10 := sphereSobolevInclusionL 1 0 (by norm_num)
  have hIU := I10.hasFDerivAt.comp y hU.hasFDerivAt
  have hIV := I10.hasFDerivAt.comp y hV.hasFDerivAt
  have hIUD : DifferentiableAt ℝ (fun x => I10 (U x)) y := hIU.differentiableAt
  have hIVD : DifferentiableAt ℝ (fun x => I10 (V x)) y := hIV.differentiableAt
  have hD := fderiv_inner_apply ℝ hIUD hIVD a
  have hUE : fderiv ℝ (fun x => I10 (U x)) y=I10.comp (fderiv ℝ U y) := hIU.fderiv
  have hVE : fderiv ℝ (fun x => I10 (V x)) y=I10.comp (fderiv ℝ V y) := hIV.fderiv
  rw [hUE,hVE] at hD
  rw [oneSectionCovariantDerivative_inner_sum]
  simpa only [I10,ContinuousLinearMap.comp_apply] using hD

lemma inner_covariant_second_triple_algebra {E A : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (V : A → E) (H R : A → A → E)
    (hR : ∀ v w,H v w-H w v=R v w) (a b c : A) :
    2*⟪H a b,V c⟫_ℝ=
      (⟪V b,H a c⟫_ℝ+⟪H a b,V c⟫_ℝ)+
      (⟪V a,H b c⟫_ℝ+⟪H b a,V c⟫_ℝ)-
      (⟪V a,H c b⟫_ℝ+⟪H c a,V b⟫_ℝ)+
      ⟪R a b,V c⟫_ℝ+⟪R c b,V a⟫_ℝ-⟪R a c,V b⟫_ℝ := by
  have hab := congrArg (fun t => ⟪t,V c⟫_ℝ) (hR a b)
  have hcb := congrArg (fun t => ⟪t,V a⟫_ℝ) (hR c b)
  have hac := congrArg (fun t => ⟪t,V b⟫_ℝ) (hR a c)
  simp only [inner_sub_left,real_inner_comm] at hab hcb hac ⊢
  linarith only [hab,hcb,hac]

/-- The third-base scalar cross form reduces to first derivatives of
gradient pairings and the actual curvature. No third section derivative
or derivative of curvature occurs in this identity. -/
theorem Elliptic.covariant_second_triple_identity {Y : Set X} (hY : IsOpen Y)
    (d : Data) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (hFrame : ∀ x ∈ Y,∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j)=if i=j then 1 else 0)
    (U : X → SphereSobolev 2) (hU : ContDiffOn ℝ ∞ U Y)
    {y : X} (hy : y ∈ Y) (a b c : X) :
    let H := fun v x => highSectionCovariantDerivative d U x v
    let I10 := sphereSobolevInclusionL 1 0 (by norm_num)
    let IU := sphereSobolevInclusionL 2 1 (by norm_num) (U y)
    2*⟪oneSectionCovariantDerivative d (H b) y a,I10 (H c y)⟫_ℝ=
      fderiv ℝ (fun x => ⟪I10 (H b x),I10 (H c x)⟫_ℝ) y a+
      fderiv ℝ (fun x => ⟪I10 (H a x),I10 (H c x)⟫_ℝ) y b-
      fderiv ℝ (fun x => ⟪I10 (H a x),I10 (H b x)⟫_ℝ) y c+
      ⟪frameCurvatureRotationL d.γ d.frame y a b IU,I10 (H c y)⟫_ℝ+
      ⟪frameCurvatureRotationL d.γ d.frame y c b IU,I10 (H a y)⟫_ℝ-
      ⟪frameCurvatureRotationL d.γ d.frame y a c IU,I10 (H b y)⟫_ℝ := by
  let H := fun v x => highSectionCovariantDerivative d U x v
  let I10 := sphereSobolevInclusionL 1 0 (by norm_num)
  have hHS (v : X) : ContDiffOn ℝ ∞ (H v) Y := by
    simpa only [H,highSectionCovariantDerivativeLinear_apply] using
      (contDiffOn_highSectionCovariantDerivativeLinear hY d hg hK he U hU).clm_apply
        (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : X => v) Y)
  have hHD (v : X) : DifferentiableAt ℝ (H v) y := ((hHS v).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)
  have hD (v w z : X) := oneSectionCovariantDerivative_inner_fderiv d (H v) (H w) y z (hHD v) (hHD w)
  change 2*⟪oneSectionCovariantDerivative d (H b) y a,I10 (H c y)⟫_ℝ=
    fderiv ℝ (fun x => ⟪I10 (H b x),I10 (H c x)⟫_ℝ) y a+
    fderiv ℝ (fun x => ⟪I10 (H a x),I10 (H c x)⟫_ℝ) y b-
    fderiv ℝ (fun x => ⟪I10 (H a x),I10 (H b x)⟫_ℝ) y c+
    ⟪frameCurvatureRotationL d.γ d.frame y a b
      (sphereSobolevInclusionL 2 1 (by norm_num) (U y)),I10 (H c y)⟫_ℝ+
    ⟪frameCurvatureRotationL d.γ d.frame y c b
      (sphereSobolevInclusionL 2 1 (by norm_num) (U y)),I10 (H a y)⟫_ℝ-
    ⟪frameCurvatureRotationL d.γ d.frame y a c
      (sphereSobolevInclusionL 2 1 (by norm_num) (U y)),I10 (H b y)⟫_ℝ
  rw [hD b c a,hD a c b,hD a b c]
  exact inner_covariant_second_triple_algebra (fun v => I10 (H v y))
    (fun v w => oneSectionCovariantDerivative d (H w) y v)
    (fun v w => frameCurvatureRotationL d.γ d.frame y v w
      (sphereSobolevInclusionL 2 1 (by norm_num) (U y)))
    (fun v w => hg.highSectionCovariantDerivative_commutator hY d hK he hFrame U hU hy v w) a b c

end ShrinkingSpheres
