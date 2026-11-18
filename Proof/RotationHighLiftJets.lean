import Proof.RotationHighLiftLinearMap
import Proof.FintypeFamilyHigherJetBound
import Proof.SmoothFiniteAdjointJets
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2200
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Fixed linear reconstruction preserves all jointly controlled jets of
one operator and its SAME low rotation commutator family. -/
lemma smoothFiniteJetBound_rotation_high_lift
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (F : P → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (G : I × I → P → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (p : P) (N : ℕ) (B : ℝ) (hf : SmoothFiniteJetBound F p N B)
    (hg : ∀ ij,SmoothFiniteJetBound (G ij) p N B) :
    SmoothFiniteJetBound (fun x => rotationHighLiftDataL (F x,fun ij => G ij x)) p N
      ((19+9*Real.sqrt 2)*B) := by
  have hGS : ContDiffAt ℝ ∞ (fun x => fun ij => G ij x) p :=
    contDiffAt_pi.mpr (fun ij => (hg ij).smooth)
  have hGJ (n : ℕ) (hn : n ≤ N) : ‖iteratedFDeriv ℝ n (fun x => fun ij => G ij x) p‖ ≤ B :=
    norm_iteratedFDeriv_fintype_family_le _ p hGS n B hf.nonneg (fun ij => (hg ij).bound n hn)
  have hPair : SmoothFiniteJetBound (fun x => (F x,fun ij => G ij x)) p N B :=
    ⟨hf.nonneg,hf.smooth.prodMk hGS,fun n hn => norm_iteratedFDeriv_product_family_le _ _ p
      hf.smooth hGS n B (hf.bound n hn) (hGJ n hn)⟩
  exact (hPair.clm rotationHighLiftDataL).weaken
    (mul_le_mul_of_nonneg_right norm_rotationHighLiftDataL_le hf.nonneg)
end ShrinkingSpheres
