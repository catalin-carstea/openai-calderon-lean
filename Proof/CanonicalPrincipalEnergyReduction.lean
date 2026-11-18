import Proof.FirstCorrectionCrossOutput
import Proof.PrincipalPhysicalReduction
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

def canonicalPrincipalPerturbation {Y : Set X} {d : Data} (T P J : Output Y d) : Output Y d :=
  P-(2:ℝ) • T-J

/-- The remaining squared-norm comparison for the actual principal residual
    after removing the explicit, uniformly H1-bounded F/raising cross terms.
    The selected result does not assume this proposition: its producer remains
    the internal open proof obligation. -/
def UniformCanonicalPrincipalEnergy (Y Ω : Set X) (K ρ c₀ : ℝ) {m : ℕ}
    (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) : Prop :=
  ∃ Q : SmoothCoefficientJets 2,∃ B η CE : ℝ,
    (∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ))) ∧
    0 < η ∧ 0 ≤ CE ∧
    ∀ floor,B ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ φ,Test Y d.γ d.frame φ →
      ∀ (E : HarmonicTestExpansion Y d.γ d.frame φ) (D : AngularModelData E d.radius) (O : AngularProductOutputs D)
        (PP : PhysicalOutputRealization Y d.γ d.frame (principalMovingTrace d.γ d.g₂ d.radius d.adjoint φ)),
      ∀ J : SobolevFamilyOutput d E (fun x => firstCorrectionCrossRemainderL Q d x),
      let P0 : Output Y d := PP.output
      let U := canonicalPrincipalPerturbation O.raisingOutput P0 J.output
      ∃ Ud : Output Y d,
        |(‖(2:ℝ) • O.raisingOutput+U‖^2-‖(2:ℝ) • O.loweringOutput+Ud‖^2)-
          4*(‖O.raisingOutput‖^2-‖O.loweringOutput‖^2)| ≤ CE*ε*(energyNorm Y d φ)^2

/-- The canonical physical product output supplies J and its complete uniform
    H1 bound. Only the stated actual residual energy comparison is left. -/
theorem uniformPrincipalPhysical_of_canonicalEnergy {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hEnergy : UniformCanonicalPrincipalEnergy Y Ω K ρ c₀ M Cj) :
    UniformPrincipalPhysicalDecomposition Y Ω K ρ c₀ M Cj := by
  obtain ⟨Q,B,η,CE,hQ,hη,hCE,hProduce⟩ := hEnergy
  let CJ := 576*K^2*|M ⟨1,by omega⟩|
  have hCJ : 0 ≤ CJ := by dsimp only [CJ];positivity
  refine ⟨max B 1,min η 1,CE,CJ,lt_min hη zero_lt_one,hCE,hCJ,?_⟩
  intro floor hFloor ε hε hSmall d hd φ hφ E D O PP
  have hf : 1 ≤ floor := (le_max_right B 1).trans hFloor
  have hB : B ≤ floor := (le_max_left B 1).trans hFloor
  have hSmallE : ε ≤ η := hSmall.trans (min_le_left η 1)
  have hSmall1 : ε ≤ 1 := hSmall.trans (min_le_right η 1)
  obtain ⟨J,hJ⟩ := hd.exists_firstCorrectionCrossOutput hY hΩ (by omega) hK hf hε hSmall1 Q hQ E
  obtain ⟨Ud,hBound⟩ := hProduce floor hB ε hε hSmallE d hd φ hφ E D O PP J
  let P0 : Output Y d := PP.output
  let U := canonicalPrincipalPerturbation O.raisingOutput P0 J.output
  let err := (‖(2:ℝ) • O.raisingOutput+U‖^2-‖(2:ℝ) • O.loweringOutput+Ud‖^2)-
    4*(‖O.raisingOutput‖^2-‖O.loweringOutput‖^2)
  refine ⟨U,Ud,J.output,err,?_,hBound,hJ,?_⟩
  · exact (sub_add_cancel
      (‖(2:ℝ) • O.raisingOutput+U‖^2-‖(2:ℝ) • O.loweringOutput+Ud‖^2)
      (4*(‖O.raisingOutput‖^2-‖O.loweringOutput‖^2))).symm.trans (add_comm _ _)
  · change P0=(2:ℝ) • O.raisingOutput+
      (P0-(2:ℝ) • O.raisingOutput-J.output)+J.output
    abel


theorem uniformEstimate_of_canonicalPrincipalEnergy {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    (hSub : Y ⊆ Ω) {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (hc₀ : 0 < c₀)
    (hEnergy : UniformCanonicalPrincipalEnergy Y Ω K ρ c₀ M Cj) :
    ∃ floor ε₀ C : ℝ,1 ≤ floor ∧ 0 < ε₀ ∧ 0 < C ∧ UniformEstimate Y Ω K ρ c₀ M Cj floor ε₀ C :=
  uniformEstimate_of_principalPhysicalDecomposition hY hΩ hSub hm K ρ c₀ M Cj hK hρ hc₀
    (uniformPrincipalPhysical_of_canonicalEnergy hY hΩ hm K ρ c₀ M Cj hK hEnergy)
end ShrinkingSpheres
