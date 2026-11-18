import Proof.CoarseAngularFieldJets
import Proof.CoarseAngularFieldSmoothness
import Proof.CoarseDegreeAssemblyJets
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open scoped ContDiff
namespace ShrinkingSpheres
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
namespace CoarseAngularFields.JetBound
lemma smoothAt {f : P → CoarseAngularFields} {p : P} {N : ℕ} {B : ℝ} (hf : JetBound f p N B) :
    CoarseAngularFields.SmoothAt f p :=
  ⟨hf.operator.smooth,hf.adjoint.smooth,(fun ij => (hf.angular ij).smooth),(fun ij => (hf.angularAdjoint ij).smooth)⟩
lemma degreeData {f : P → CoarseAngularFields} {p : P} {N : ℕ} {B : ℝ} (hf : JetBound f p N B) :
    SmoothFiniteJetBound (fun x => (f x).degreeData) p N B :=
  ⟨hf.operator.nonneg,hf.smoothAt.degreeData,fun n hn =>
    norm_iteratedFDeriv_coarseDegreeAssembly_le _ _ _ p hf.operator.smooth
      (fun ij => (hf.angular ij).smooth) (fun ij => (hf.angularAdjoint ij).smooth) n B hf.operator.nonneg
      (hf.operator.bound n hn) (fun ij => (hf.angular ij).bound n hn) (fun ij => (hf.angularAdjoint ij).bound n hn)⟩
end CoarseAngularFields.JetBound
end ShrinkingSpheres
