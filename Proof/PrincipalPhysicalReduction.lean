import Proof.PhysicalDecompositionReduction
import Proof.MovingTraceDriftOutput
import Proof.PhysicalOutputAddition

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ENNReal Topology ContDiff
namespace ShrinkingSpheres

/-- The physical decomposition producer for the principal trace only. The
    second-metric drift is supplied separately by its proved energy remainder. -/
def UniformPrincipalPhysicalDecomposition (Y Ω : Set X) (K ρ c₀ : ℝ) {m : ℕ} (M : Fin (m+1) → ℝ)
    (Cj : Fin 9 → ℝ) : Prop :=
  ∃ B η CE CJ : ℝ,0 < η ∧ 0 ≤ CE ∧ 0 ≤ CJ ∧
    ∀ floor,B ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ φ,Test Y d.γ d.frame φ →
      ∀ (E : HarmonicTestExpansion Y d.γ d.frame φ) (D : AngularModelData E d.radius) (O : AngularProductOutputs D)
        (PP : PhysicalOutputRealization Y d.γ d.frame (principalMovingTrace d.γ d.g₂ d.radius d.adjoint φ)),
      PhysicalDecomposition Y d φ ε CE CJ O.raisingOutput O.loweringOutput PP.output

/-- The entire second-metric drift has already been proved absorbable from
    its zeroth-order size alone. Thus the remaining principal producer implies
    the full comparison for the unchanged frozen moving-trace operator. -/
theorem uniformPhysicalComparison_of_principal {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ)
    (hPrincipal : UniformPrincipalPhysicalDecomposition Y Ω K ρ c₀ M Cj) :
    UniformPhysicalComparison Y Ω K ρ c₀ M Cj := by
  have hDriftTheorem := uniform_movingTraceDrift_output_bound hY hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηD,CD,hηD,hCD,hDrift⟩ := hDriftTheorem
  obtain ⟨B,ηP,CE,CJ,hηP,hCE,hCJ,hProduce⟩ := hPrincipal
  refine ⟨max B 1,min ηP ηD,CE,CJ+CD,lt_min hηP hηD,hCE,add_nonneg hCJ hCD,?_⟩
  intro floor hFloor ε hε hSmall d hd φ hφ E D O
  have hf : 1 ≤ floor := (le_max_right ..).trans hFloor
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have h : Elliptic Y K d.γ := ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun y hy => hd.1.1.2 y (hSub hy)⟩
  have he : ∀ i,ContDiffOn ℝ ∞ (fun y => d.frame y i) Y := fun i => (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hFrame : ∀ y ∈ Y,∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j) = if i=j then 1 else 0 :=
    fun y hy => hd.1.2.2.2.2.2.2.2 y (hSub hy)
  have hOutputs := hd.exists_principal_drift_outputs hY hSub hKpos hφ
  obtain ⟨PP,⟨PD⟩⟩ := hOutputs
  have hHere := hProduce floor ((le_max_left ..).trans hFloor) ε hε (hSmall.trans (min_le_left _ _)) d hd φ hφ E D O PP
  obtain ⟨U,Ud,J,err,hcomp,herr,hJ,hP⟩ := hHere
  have hJNorm := remainder_norm_le_of_sobolev_one hY h hKpos he hFrame hd.2.2.2.2.1 hf hφ J hCJ hJ
  have hDNorm := hDrift floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd φ hφ PD
  let JD : Output Y d := PD.output
  let VP : Output Y d := PP.output
  have hJD : ‖JD‖ ≤ CD/floor*energyNorm Y d φ := hDNorm
  have hRemainder : ‖J+JD‖ ≤ (CJ+CD)/floor*energyNorm Y d φ :=
    (norm_add_le _ _).trans ((add_le_add hJNorm hJD).trans_eq (by ring))
  have hFull : VP+JD = (2:ℝ) • O.raisingOutput+U+(J+JD) :=
    (congrArg (fun V : Output Y d => V+JD) hP).trans (by abel)
  exact ⟨U,Ud,J+JD,VP+JD,err,hcomp,herr,hRemainder,hFull,
    fullTraceOutputOfPrincipalDrift_norm hY (h.contDiffOn_density hKpos).continuousOn PP PD⟩

theorem uniformEstimate_of_principalPhysicalDecomposition {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    (hSub : Y ⊆ Ω) {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (hc₀ : 0 < c₀)
    (hPrincipal : UniformPrincipalPhysicalDecomposition Y Ω K ρ c₀ M Cj) :
    ∃ floor ε₀ C : ℝ,1 ≤ floor ∧ 0 < ε₀ ∧ 0 < C ∧ UniformEstimate Y Ω K ρ c₀ M Cj floor ε₀ C :=
  uniformEstimate_of_physicalComparison hY hΩ hSub (by omega) K ρ c₀ M Cj hK hc₀
    (uniformPhysicalComparison_of_principal hY hΩ hSub hm K ρ c₀ M Cj hK hρ hPrincipal)

end ShrinkingSpheres
