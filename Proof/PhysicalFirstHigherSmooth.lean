import Proof.PhysicalFirstDerivativeCoordinates
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
lemma PhysicalPrincipalData.firstDerivativeHigherL_smooth {Y Ω : Set X} {d : Data} {CF CT : ℝ}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} (P : PhysicalPrincipalData Y d CF CT)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K) (j : I) :
    ContDiffOn ℝ ∞ (fun y => P.firstDerivativeHigherL y j) Y := by
  have hSub : Y ⊆ Ω := fun x hx => hd.2.1.center_mem hx
  have hQ := fun i k => hd.contDiffOn_framePrincipalCoefficient hSub hK i k
  have hT := fun i => contDiffOn_scaledFrameLogRadius hY hd.2.2.2.2.1.1
    (fun x hx => (hd.2.2.2.2.1.2 x hx).1.ne')
    (fun k => (hd.1.2.2.2.2.2.2.1 k).mono hSub) i
  apply ContDiffOn.add
  · apply ContDiffOn.add
    · exact ContDiffOn.sum (fun i _ => (((hQ i j).add (hQ j i)).mul (hT i)).smul contDiffOn_const)
    · exact (ContDiffOn.sum (fun i _ => ((hQ i j).sub contDiffOn_const).smul contDiffOn_const)).const_smul (2:ℝ)
  · apply hd.2.2.2.2.1.1.smul
    exact ContDiffOn.sum (fun i _ => ((hQ i j).add (hQ j i)).smul
      (((hd.contDiffOn_firstFrameAdjointCorrectionAtL hY hΩ hK (1/2:ℝ) i).clm_comp contDiffOn_const).add
        (P.first.high_smooth i)))
end ShrinkingSpheres
