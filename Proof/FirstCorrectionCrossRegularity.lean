import Proof.ActualFrameCorrectionGraded
import Proof.FirstCorrectionCrossRemainder
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

lemma Admissible.contDiffOn_firstFrameAdjointCorrectionSobolevL {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K) (i : I) :
    ContDiffOn ℝ ∞ (fun x => firstFrameAdjointCorrectionSobolevL d x i) Y := by
  exact hd.contDiffOn_firstFrameAdjointCorrectionAtL hY hΩ hK 1 i

lemma Admissible.contDiffOn_firstCorrectionCrossRemainderL {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K) (Q : OAI.AnisotropicCalderon.DirichletFamily.SmoothCoefficientJets 2) :
    ContDiffOn ℝ ∞ (fun x => firstCorrectionCrossRemainderL Q d x) Y := by
  apply ContDiffOn.sum
  intro i _
  have hA : ContDiffOn ℝ ∞ (fun _ : X => boundaryGradientAdjointL (coordinateBoundaryCoefficients Q i) sphereSobolevDegreeL) Y :=
    contDiffOn_const
  exact (hA.clm_comp (hd.contDiffOn_firstFrameAdjointCorrectionSobolevL hY hΩ hK i)).add
    ((hd.contDiffOn_firstFrameAdjointCorrectionL hY hΩ hK i).clm_comp hA)
end ShrinkingSpheres
