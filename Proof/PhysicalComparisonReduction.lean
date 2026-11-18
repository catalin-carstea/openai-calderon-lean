import Proof.AngularProductOutputs
import Proof.EnergyPositivity

noncomputable section
set_option autoImplicit false
open Set
namespace ShrinkingSpheres

namespace AngularProductOutputs
variable {Y : Set X} {d : Data} {φ : Field} {E : HarmonicTestExpansion Y d.γ d.frame φ}
  {D : AngularModelData E d.radius}

def raisingOutput (O : AngularProductOutputs D) : Output Y d := O.raising.output

def loweringOutput (O : AngularProductOutputs D) : Output Y d := O.lowering.output
end AngularProductOutputs

/-- The physical part still needed after the completed angular coercivity estimate.
    It compares the constructed model outputs to the actual moving trace. -/
def PhysicalComparison (Y : Set X) (d : Data) (φ : Field) (floor ε CE CJ : ℝ)
    (T Tf : Output Y d) : Prop :=
  ∃ U Ud J P : Output Y d,∃ err : ℝ,
    ‖(2:ℝ) • T+U‖^2-‖(2:ℝ) • Tf+Ud‖^2 = 4*(‖T‖^2-‖Tf‖^2)+err ∧
    |err| ≤ CE*ε*(energyNorm Y d φ)^2 ∧ ‖J‖ ≤ CJ/floor*energyNorm Y d φ ∧
    P = (2:ℝ) • T+U+J ∧ ‖P‖ = traceNorm Y d φ

/-- A uniform producer for the remaining physical estimates, stated at its actual caller.
    It has no angular coercivity premise to be supplied by an author. -/
def UniformPhysicalComparison (Y Ω : Set X) (K ρ c₀ : ℝ) {m : ℕ} (M : Fin (m+1) → ℝ)
    (Cj : Fin 9 → ℝ) : Prop :=
  ∃ B η CE CJ : ℝ,0 < η ∧ 0 ≤ CE ∧ 0 ≤ CJ ∧
    ∀ floor,B ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ φ,Test Y d.γ d.frame φ →
      ∀ (E : HarmonicTestExpansion Y d.γ d.frame φ) (D : AngularModelData E d.radius) (O : AngularProductOutputs D),
        PhysicalComparison Y d φ floor ε CE CJ O.raisingOutput O.loweringOutput

/-- The full frozen estimate follows from the physical comparison producer, with its
    model coercivity witnesses now supplied by the completed arbitrary-profile proof. -/
theorem uniformEstimate_of_physicalComparison {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    (hsub : Y ⊆ Ω) {m : ℕ} (hm : 2 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hc₀ : 0 < c₀) (hphysical : UniformPhysicalComparison Y Ω K ρ c₀ M Cj) :
    ∃ floor ε₀ C : ℝ,1 ≤ floor ∧ 0 < ε₀ ∧ 0 < C ∧ UniformEstimate Y Ω K ρ c₀ M Cj floor ε₀ C := by
  obtain ⟨B,η,CE,CJ,hη,hCE,hCJ,produce⟩ := hphysical
  apply uniformEstimate_of_analyticEstimates Y Ω K ρ c₀ M Cj
    (max B (backgroundCoercivityFloor hm K M c₀)) η (backgroundModeCoercivityConstant c₀) CE CJ
    hη (backgroundModeCoercivityConstant_pos c₀ hc₀) hCE hCJ
  intro floor hfloor ε hε hsmall d hd φ hφ
  have hfloorModel : backgroundCoercivityFloor hm K M c₀ ≤ floor := (le_max_right ..).trans hfloor
  obtain ⟨E,D,O,hmodel⟩ := hd.1.exists_coercive_product_outputs hY hΩ hsub (lt_of_lt_of_le zero_lt_one hK) hm
    hd.2.2.2.2.1 hc₀ hfloorModel hφ
  obtain ⟨U,Ud,J,P,err,hcomp,herr,hJ,hP,hnorm⟩ :=
    produce floor ((le_max_left ..).trans hfloor) ε hε hsmall d hd φ hφ E D O
  refine ⟨O.raisingOutput,O.loweringOutput,U,Ud,J,P,err,?_,hcomp,herr,hJ,hP,hnorm⟩
  rw [energyNorm_sq]
  exact hmodel

end ShrinkingSpheres
