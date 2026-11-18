import Proof.FirstCorrectionCrossRegularity
import Proof.SobolevFamilyOutputBound
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set MeasureTheory
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

/-- The actual F/raising cross terms define a genuine output in the frozen
    physical Hilbert space with a uniform H1 bound independent of the profile
    floor. This supplies this entire contribution to J. -/
theorem Admissible.exists_firstCorrectionCrossOutput {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 2 ≤ m) {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) :
    ∃ P : SobolevFamilyOutput d E (fun x => firstCorrectionCrossRemainderL Q d x),
      ‖P.output‖^2 ≤ (576*K^2*|M ⟨1,by omega⟩|)^2*
        (∫ x in Y,metricDensity d.γ x*sobolevSq d.γ d.frame 1 x (fun w => φ (x,w))) := by
  have hKpos := zero_lt_one.trans_le hK
  have hSub : Y ⊆ Ω := fun x hx => hd.2.1.center_mem hx
  have hρ : ContinuousOn (metricDensity d.γ) Y := ((hd.1.1.contDiffOn_density hKpos).mono hSub).continuousOn
  have hFrame : ∀ x ∈ Y,∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j)=if i=j then 1 else 0 :=
    fun x hx => hd.1.2.2.2.2.2.2.2 x (hSub hx)
  obtain ⟨P⟩ := exists_sobolevFamilyOutput hY d hρ E (fun x => firstCorrectionCrossRemainderL Q d x)
    (hd.contDiffOn_firstCorrectionCrossRemainderL hY hΩ hKpos Q)
  refine ⟨P,SobolevFamilyOutput.norm_sq_le hY hρ hFrame P (by positivity) ?_⟩
  intro x hx
  exact hd.norm_firstCorrectionCrossRemainderL_le hΩ hm hK hf hε hε1 Q hQ hx
end ShrinkingSpheres
