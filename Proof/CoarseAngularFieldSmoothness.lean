import Proof.CoarseAngularFields
import Proof.NativeRelativeDegreeFamilySmooth
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped ContDiff BigOperators
namespace ShrinkingSpheres
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

structure CoarseAngularFields.SmoothAt (f : P → CoarseAngularFields) (p : P) : Prop where
  operator : ContDiffAt ℝ ∞ (fun x => (f x).operator) p
  adjoint : ContDiffAt ℝ ∞ (fun x => (f x).adjoint) p
  angular : ∀ ij,ContDiffAt ℝ ∞ (fun x => (f x).angular ij) p
  angularAdjoint : ∀ ij,ContDiffAt ℝ ∞ (fun x => (f x).angularAdjoint ij) p

structure ScalarRotationMultiplierData.SmoothAt (f : P → ScalarRotationMultiplierData) (p : P) : Prop where
  one : ContDiffAt ℝ ∞ (fun x => (f x).one) p
  coarse : ContDiffAt ℝ ∞ (fun x => (f x).coarse) p
  angularOne : ∀ ij,ContDiffAt ℝ ∞ (fun x => (f x).angularOne ij) p
  angularCoarse : ∀ ij,ContDiffAt ℝ ∞ (fun x => (f x).angularCoarse ij) p

namespace CoarseAngularFields.SmoothAt
lemma constant (Q : CoarseAngularFields) (p : P) : SmoothAt (fun _ : P => Q) p :=
  ⟨contDiffAt_const,contDiffAt_const,(fun _ => contDiffAt_const),(fun _ => contDiffAt_const)⟩
lemma add {f g : P → CoarseAngularFields} {p : P} (hf : SmoothAt f p) (hg : SmoothAt g p) :
    SmoothAt (fun x => (f x).add (g x)) p :=
  ⟨hf.operator.add hg.operator,hf.adjoint.add hg.adjoint,
    (fun ij => (hf.angular ij).add (hg.angular ij)),
    (fun ij => (hf.angularAdjoint ij).add (hg.angularAdjoint ij))⟩
lemma scalar {f : P → ℝ} {g : P → CoarseAngularFields} {p : P}
    (hf : ContDiffAt ℝ ∞ f p) (hg : SmoothAt g p) : SmoothAt (fun x => (g x).smul (f x)) p :=
  ⟨hf.smul hg.operator,hf.smul hg.adjoint,
    (fun ij => hf.smul (hg.angular ij)),(fun ij => hf.smul (hg.angularAdjoint ij))⟩
lemma const_smul {g : P → CoarseAngularFields} {p : P}
    (hg : SmoothAt g p) (c : ℝ) : SmoothAt (fun x => (g x).smul c) p := scalar contDiffAt_const hg
lemma mulRight {f : P → CoarseAngularFields} {g : P → ScalarRotationMultiplierData} {p : P}
    (hf : SmoothAt f p) (hg : ScalarRotationMultiplierData.SmoothAt g p) :
    SmoothAt (fun x => (f x).mulRight (g x)) p := by
  refine ⟨hf.operator.clm_comp hg.one,hg.coarse.clm_comp hf.adjoint,?_,?_⟩
  · intro ij
    change ContDiffAt ℝ ∞ (fun x => ((f x).angular ij).comp (g x).one+(f x).operator.comp ((g x).angularOne ij)) p
    exact ((hf.angular ij).clm_comp hg.one).add (hf.operator.clm_comp (hg.angularOne ij))
  · intro ij
    change ContDiffAt ℝ ∞ (fun x => (g x).coarse.comp ((f x).angularAdjoint ij)+
      ((g x).angularCoarse ij).comp (f x).adjoint) p
    exact (hg.coarse.clm_comp (hf.angularAdjoint ij)).add ((hg.angularCoarse ij).clm_comp hf.adjoint)
lemma sum {κ : Type*} [Fintype κ] (f : κ → P → CoarseAngularFields) (p : P)
    (hf : ∀ k,SmoothAt (f k) p) : SmoothAt (fun x => CoarseAngularFields.sum (fun k => f k x)) p :=
  ⟨ContDiffAt.sum (fun k _ => (hf k).operator),ContDiffAt.sum (fun k _ => (hf k).adjoint),
    (fun ij => ContDiffAt.sum (fun k _ => (hf k).angular ij)),
    (fun ij => ContDiffAt.sum (fun k _ => (hf k).angularAdjoint ij))⟩
lemma degreeData {f : P → CoarseAngularFields} {p : P} (hf : SmoothAt f p) :
    ContDiffAt ℝ ∞ (fun x => (f x).degreeData) p :=
  contDiffAt_coarseDegreeDataAssembly _ _ _ p hf.operator hf.angular hf.angularAdjoint
end CoarseAngularFields.SmoothAt

lemma ScalarRotationMultiplierData.SmoothAt.constant (Q : ScalarRotationMultiplierData) (p : P) :
    ScalarRotationMultiplierData.SmoothAt (fun _ : P => Q) p :=
  ⟨contDiffAt_const,contDiffAt_const,(fun _ => contDiffAt_const),(fun _ => contDiffAt_const)⟩

lemma closedCoefficient_scalar_rotation_smoothAt
    {Q : P → OAI.AnisotropicCalderon.DirichletFamily.ClosedCoefficientJets 3} {p : P}
    (hQ : ContDiffAt ℝ ∞ Q p) :
    ScalarRotationMultiplierData.SmoothAt (fun x => scalarRotationDataOfClosedCoefficient (Q x)) p :=
  ⟨closedOneBoundaryScalarMultiplierL.contDiff.contDiffAt.comp p hQ,
    closedThreeJetCoarseScalarMultiplierL.contDiff.contDiffAt.comp p hQ,
    (fun ij => (closedCoefficientAngularOneL ij.1 ij.2).contDiff.contDiffAt.comp p hQ),
    (fun ij => (closedCoefficientAngularCoarseL ij.1 ij.2).contDiff.contDiffAt.comp p hQ)⟩
end ShrinkingSpheres
