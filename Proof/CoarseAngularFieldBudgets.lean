import Proof.CoarseAngularFieldJets
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

lemma four_block_budget_bounds (a b : ℝ) (c d : I × I → ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : ∀ ij,0 ≤ c ij) (hd : ∀ ij,0 ≤ d ij) :
    a ≤ a+b+(∑ ij,c ij)+(∑ ij,d ij) ∧
    b ≤ a+b+(∑ ij,c ij)+(∑ ij,d ij) ∧
    (∀ ij,c ij ≤ a+b+(∑ ij,c ij)+(∑ ij,d ij)) ∧
    (∀ ij,d ij ≤ a+b+(∑ ij,c ij)+(∑ ij,d ij)) := by
  have hC := Finset.sum_nonneg (fun ij (_ : ij ∈ Finset.univ) => hc ij)
  have hD := Finset.sum_nonneg (fun ij (_ : ij ∈ Finset.univ) => hd ij)
  refine ⟨by linarith,by linarith,?_,?_⟩
  · intro ij
    have hh := Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) => hc k) (Finset.mem_univ ij)
    linarith
  · intro ij
    have hh := Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) => hd k) (Finset.mem_univ ij)
    linarith

def CoarseAngularFields.budget (Q : CoarseAngularFields) : ℝ :=
  ‖Q.operator‖+‖Q.adjoint‖+(∑ ij,‖Q.angular ij‖)+(∑ ij,‖Q.angularAdjoint ij‖)

lemma CoarseAngularFields.constant_jet_bound (Q : CoarseAngularFields) (p : P) (N : ℕ) :
    CoarseAngularFields.JetBound (fun _ : P => Q) p N Q.budget := by
  obtain ⟨h1,h2,h3,h4⟩ := four_block_budget_bounds ‖Q.operator‖ ‖Q.adjoint‖
    (fun ij => ‖Q.angular ij‖) (fun ij => ‖Q.angularAdjoint ij‖)
    (norm_nonneg _) (norm_nonneg _) (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  exact ⟨(SmoothFiniteJetBound.constant _ p N).weaken h1,(SmoothFiniteJetBound.constant _ p N).weaken h2,
    (fun ij => (SmoothFiniteJetBound.constant _ p N).weaken (h3 ij)),
    (fun ij => (SmoothFiniteJetBound.constant _ p N).weaken (h4 ij))⟩

def ScalarRotationMultiplierData.budget (Q : ScalarRotationMultiplierData) : ℝ :=
  ‖Q.one‖+‖Q.coarse‖+(∑ ij,‖Q.angularOne ij‖)+(∑ ij,‖Q.angularCoarse ij‖)

lemma ScalarRotationMultiplierData.constant_jet_bound (Q : ScalarRotationMultiplierData) (p : P) (N : ℕ) :
    ScalarRotationMultiplierData.JetBound (fun _ : P => Q) p N Q.budget := by
  obtain ⟨h1,h2,h3,h4⟩ := four_block_budget_bounds ‖Q.one‖ ‖Q.coarse‖
    (fun ij => ‖Q.angularOne ij‖) (fun ij => ‖Q.angularCoarse ij‖)
    (norm_nonneg _) (norm_nonneg _) (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  exact ⟨(SmoothFiniteJetBound.constant _ p N).weaken h1,(SmoothFiniteJetBound.constant _ p N).weaken h2,
    (fun ij => (SmoothFiniteJetBound.constant _ p N).weaken (h3 ij)),
    (fun ij => (SmoothFiniteJetBound.constant _ p N).weaken (h4 ij))⟩

lemma CoarseAngularFields.budget_nonneg (Q : CoarseAngularFields) : 0 ≤ Q.budget := by
  unfold budget
  positivity
lemma ScalarRotationMultiplierData.budget_nonneg (Q : ScalarRotationMultiplierData) : 0 ≤ Q.budget := by
  unfold budget
  positivity

namespace ScalarRotationMultiplierData.JetBound
lemma weaken {f : P → ScalarRotationMultiplierData} {p : P} {N : ℕ} {B C : ℝ}
    (hf : ScalarRotationMultiplierData.JetBound f p N B) (hBC : B ≤ C) :
    ScalarRotationMultiplierData.JetBound f p N C :=
  ⟨hf.one.weaken hBC,hf.coarse.weaken hBC,(fun ij => (hf.angularOne ij).weaken hBC),
    (fun ij => (hf.angularCoarse ij).weaken hBC)⟩
end ScalarRotationMultiplierData.JetBound
end ShrinkingSpheres
