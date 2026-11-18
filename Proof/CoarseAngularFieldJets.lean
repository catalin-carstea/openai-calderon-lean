import Proof.CoarseAngularFields
import Proof.SmoothFiniteJetBounds
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped ContDiff BigOperators
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

structure CoarseAngularFields.JetBound (f : P → CoarseAngularFields) (p : P) (N : ℕ) (B : ℝ) : Prop where
  operator : SmoothFiniteJetBound (fun x => (f x).operator) p N B
  adjoint : SmoothFiniteJetBound (fun x => (f x).adjoint) p N B
  angular : ∀ ij,SmoothFiniteJetBound (fun x => (f x).angular ij) p N B
  angularAdjoint : ∀ ij,SmoothFiniteJetBound (fun x => (f x).angularAdjoint ij) p N B

structure ScalarRotationMultiplierData.JetBound (f : P → ScalarRotationMultiplierData) (p : P) (N : ℕ) (B : ℝ) : Prop where
  one : SmoothFiniteJetBound (fun x => (f x).one) p N B
  coarse : SmoothFiniteJetBound (fun x => (f x).coarse) p N B
  angularOne : ∀ ij,SmoothFiniteJetBound (fun x => (f x).angularOne ij) p N B
  angularCoarse : ∀ ij,SmoothFiniteJetBound (fun x => (f x).angularCoarse ij) p N B

namespace CoarseAngularFields.JetBound
lemma weaken {f : P → CoarseAngularFields} {p : P} {N : ℕ} {B C : ℝ}
    (hf : CoarseAngularFields.JetBound f p N B) (hBC : B ≤ C) :
    CoarseAngularFields.JetBound f p N C :=
  ⟨hf.operator.weaken hBC,hf.adjoint.weaken hBC,(fun ij => (hf.angular ij).weaken hBC),
    (fun ij => (hf.angularAdjoint ij).weaken hBC)⟩

lemma add {f g : P → CoarseAngularFields} {p : P} {N : ℕ} {B C : ℝ}
    (hf : CoarseAngularFields.JetBound f p N B) (hg : CoarseAngularFields.JetBound g p N C) :
    CoarseAngularFields.JetBound (fun x => (f x).add (g x)) p N (B+C) :=
  ⟨hf.operator.add hg.operator,hf.adjoint.add hg.adjoint,
    (fun ij => (hf.angular ij).add (hg.angular ij)),
    (fun ij => (hf.angularAdjoint ij).add (hg.angularAdjoint ij))⟩

lemma const_smul {f : P → CoarseAngularFields} {p : P} {N : ℕ} {B : ℝ}
    (hf : CoarseAngularFields.JetBound f p N B) (c : ℝ) :
    CoarseAngularFields.JetBound (fun x => (f x).smul c) p N (|c| * B) :=
  ⟨hf.operator.const_smul c,hf.adjoint.const_smul c,
    (fun ij => (hf.angular ij).const_smul c),
    (fun ij => (hf.angularAdjoint ij).const_smul c)⟩

lemma scalar {f : P → ℝ} {g : P → CoarseAngularFields} {p : P} {N : ℕ} {B C : ℝ}
    (hf : SmoothFiniteJetBound f p N B) (hg : CoarseAngularFields.JetBound g p N C) :
    CoarseAngularFields.JetBound (fun x => (g x).smul (f x)) p N (2^N*B*C) :=
  ⟨hf.scalar hg.operator,hf.scalar hg.adjoint,
    (fun ij => hf.scalar (hg.angular ij)),(fun ij => hf.scalar (hg.angularAdjoint ij))⟩

lemma mulRight {f : P → CoarseAngularFields} {g : P → ScalarRotationMultiplierData}
    {p : P} {N : ℕ} {B C : ℝ}
    (hf : CoarseAngularFields.JetBound f p N B) (hg : ScalarRotationMultiplierData.JetBound g p N C) :
    CoarseAngularFields.JetBound (fun x => (f x).mulRight (g x)) p N (2*(2^N*B*C)) := by
  have hBC : 0 ≤ 2^N*B*C := by have hB := hf.operator.nonneg;have hC := hg.one.nonneg;positivity
  have hSwap : 2^N*C*B = 2^N*B*C := by ring
  refine ⟨(hf.operator.comp hg.one).weaken (by linarith),?_,?_,?_⟩
  · have hh := hg.coarse.comp hf.adjoint
    rw [hSwap] at hh
    exact hh.weaken (by linarith)
  · intro ij
    have hh := (hf.angular ij).comp hg.one |>.add (hf.operator.comp (hg.angularOne ij))
    simpa only [two_mul,CoarseAngularFields.mulRight] using hh
  · intro ij
    have hh := hg.coarse.comp (hf.angularAdjoint ij) |>.add ((hg.angularCoarse ij).comp hf.adjoint)
    rw [hSwap] at hh
    simpa only [two_mul,CoarseAngularFields.mulRight] using hh

lemma sum {κ : Type*} [Fintype κ] (f : κ → P → CoarseAngularFields) (p : P) (N : ℕ) (B : κ → ℝ)
    (hf : ∀ k,CoarseAngularFields.JetBound (f k) p N (B k)) :
    CoarseAngularFields.JetBound (fun x => CoarseAngularFields.sum (fun k => f k x)) p N (∑ k,B k) :=
  ⟨SmoothFiniteJetBound.sum _ p N B (fun k => (hf k).operator),
    SmoothFiniteJetBound.sum _ p N B (fun k => (hf k).adjoint),
    (fun ij => SmoothFiniteJetBound.sum _ p N B (fun k => (hf k).angular ij)),
    (fun ij => SmoothFiniteJetBound.sum _ p N B (fun k => (hf k).angularAdjoint ij))⟩
end CoarseAngularFields.JetBound
end ShrinkingSpheres
