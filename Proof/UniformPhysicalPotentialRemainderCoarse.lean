import Proof.PhysicalPotentialRemainderSmooth
import Proof.SobolevFamilyOutputBound
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3400000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2800
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Uniform coarse norm bound for the SAME complete physical complement.
All constants precede the radius, frame, physical witnesses and test. -/
theorem uniform_physical_potential_remainder_coarse {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ)
    (CF CT : ℝ) (hCT : 0 ≤ CT) :
    ∃ η CR : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CR ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ P : PhysicalPrincipalData Y d CF CT,
      ContDiffOn ℝ ∞ P.potentialRemainderCoarseL Y ∧
      ∀ y ∈ Y,‖P.potentialRemainderCoarseL y‖ ≤ CR*ε := by
  obtain ⟨η,CE,hη,hη1,hCE,hE⟩ :=
    uniform_physical_coarse_first_error_bound hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  let CR := potentialRemainderCoarseBudget K (M ⟨1,by omega⟩) (M ⟨2,by omega⟩) (Cj 2) CE CT
  refine ⟨η,CR,hη,hη1,abs_nonneg _,?_⟩
  intro floor hf ε hε hSmall d hd P
  have hParts := hE floor hf ε hε hSmall d hd CF CT P
  refine ⟨P.potentialRemainderCoarseL_smooth hY hΩ hd (zero_lt_one.trans_le hK),?_⟩
  intro y hy
  exact P.norm_potentialRemainderCoarseL_small hY hΩ (by omega) hCT hCE hd hK hf hε
    (hSmall.trans hη1) hy (fun i => hParts.2 i y hy)

/-- The genuine complementary output with its quantitative small H1 bound.
The witness used in the conclusion is the one to subtract in the residual. -/
theorem PhysicalPrincipalData.exists_potentialRemainderOutput {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} {K ρ c₀ floor ε CF CT CR : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (P : PhysicalPrincipalData Y d CF CT)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (hCR : 0 ≤ CR) (hε : 0 ≤ ε)
    (hNorm : ∀ y ∈ Y,‖P.potentialRemainderCoarseL y‖ ≤ CR*ε)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) :
    ∃ R : SobolevFamilyOutput d E P.potentialRemainderCoarseL,
      ‖R.output‖^2 ≤ (CR*ε)^2*
        (∫ y in Y,metricDensity d.γ y*sobolevSq d.γ d.frame 1 y (fun w => φ (y,w))) := by
  have hSub : Y ⊆ Ω := fun y hy => hd.2.1.center_mem hy
  have hρ := ((hd.1.1.contDiffOn_density hK).mono hSub).continuousOn
  have hFrame := fun y hy => hd.1.2.2.2.2.2.2.2 y (hSub hy)
  obtain ⟨R⟩ := exists_sobolevFamilyOutput hY d hρ E P.potentialRemainderCoarseL
    (P.potentialRemainderCoarseL_smooth hY hΩ hd hK)
  exact ⟨R,R.norm_sq_le hY hρ hFrame (mul_nonneg hCR hε) hNorm⟩
end ShrinkingSpheres
