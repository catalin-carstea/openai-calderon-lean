import Proof.UniformPhysicalPotentialRemainderCoarse
import Proof.NormSquareRemainderAddition
import Proof.CanonicalPrincipalLowerBound
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3400000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2800
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

/-- Conditional caller for the remaining energy argument after removing the
complete genuine order-one complement. Its omitted terms have a closed
uniform H1 output bound, and require no additional adjoint premise. -/
def UniformTruncatedPrincipalLowerBound (Y Ω : Set X) (K ρ c₀ : ℝ) {m : ℕ}
    (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (CF CT : ℝ) : Prop :=
  ∃ Q : SmoothCoefficientJets 2,∃ B η CE : ℝ,
    (∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ))) ∧
    0 < η ∧ 0 ≤ CE ∧
    ∀ floor,B ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ P : PhysicalPrincipalData Y d CF CT,
      ∀ φ,Test Y d.γ d.frame φ →
      ∀ (E : HarmonicTestExpansion Y d.γ d.frame φ) (D : AngularModelData E d.radius) (O : AngularProductOutputs D)
        (PP : PhysicalOutputRealization Y d.γ d.frame (principalMovingTrace d.γ d.g₂ d.radius d.adjoint φ)),
      ∀ J : SobolevFamilyOutput d E (fun x => firstCorrectionCrossRemainderL Q d x),
      ∀ R : SobolevFamilyOutput d E P.potentialRemainderCoarseL,
        let P0 : Output Y d := PP.output
        4*(‖O.raisingOutput‖^2-‖O.loweringOutput‖^2) ≤
          ‖P0-J.output-R.output‖^2+CE*ε*(energyNorm Y d φ)^2

theorem uniformPrincipalPhysical_of_truncatedLowerBound {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ)
    (hLower : ∀ CF CT : ℝ,0 ≤ CF → 0 ≤ CT → UniformTruncatedPrincipalLowerBound Y Ω K ρ c₀ M Cj CF CT) :
    UniformPrincipalPhysicalDecomposition Y Ω K ρ c₀ M Cj := by
  obtain ⟨ηP,CF,CT,hηP,hηP1,hCF,hCT,hPhysical⟩ :=
    uniform_physical_principal_data hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηR,CR,hηR,hηR1,hCR,hRem⟩ :=
    uniform_physical_potential_remainder_coarse hY hΩ hSub hm K ρ c₀ M Cj hK hρ CF CT hCT
  obtain ⟨Q,B,ηL,CE,hQ,hηL,hCE,hProduce⟩ := hLower CF CT hCF hCT
  let CJ := 576*K^2*|M ⟨1,by omega⟩|
  have hCJ : 0 ≤ CJ := by dsimp only [CJ];positivity
  refine ⟨max B 1,min ηP (min ηR ηL),CE,CJ+CR,
    lt_min hηP (lt_min hηR hηL),hCE,add_nonneg hCJ hCR,?_⟩
  intro floor hFloor ε hε hSmall d hd φ hφ E D O PP
  have hf : 1 ≤ floor := (le_max_right _ _).trans hFloor
  have hSmallP : ε ≤ ηP := hSmall.trans (min_le_left _ _)
  have hSmallR : ε ≤ ηR := hSmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hSmallL : ε ≤ ηL := hSmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hε1 : ε ≤ 1 := hSmallP.trans hηP1
  have hKpos := zero_lt_one.trans_le hK
  obtain ⟨P⟩ := hPhysical floor hf ε hε hSmallP d hd
  have hR := hRem floor hf ε hε hSmallR d hd P
  obtain ⟨J,hJ⟩ := hd.exists_firstCorrectionCrossOutput hY hΩ (by omega) hK hf hε hε1 Q hQ E
  obtain ⟨R,hRS⟩ := P.exists_potentialRemainderOutput hY hΩ hd hKpos hCR hε hR.2 E
  let I := ∫ y in Y,metricDensity d.γ y*sobolevSq d.γ d.frame 1 y (fun w => φ (y,w))
  have hI : 0 ≤ I := integral_nonneg (fun y => mul_nonneg (Real.sqrt_nonneg _) (sobolevSq_nonneg _ _ _ _ _))
  have hRbig : ‖R.output‖^2 ≤ CR^2*I := hRS.trans
    (mul_le_mul_of_nonneg_right
      ((sq_le_sq₀ (mul_nonneg hCR hε) hCR).mpr
        ((mul_le_mul_of_nonneg_left hε1 hCR).trans_eq (mul_one _))) hI)
  have hSum := norm_sq_add_le_of_sq_bounds J.output R.output hCJ hCR hI hJ hRbig
  let P0 : Output Y d := PP.output
  have hLowerHere := hProduce floor ((le_max_left _ _).trans hFloor) ε hε hSmallL d hd P φ hφ E D O PP J R
  obtain ⟨V,hV⟩ := norm_square_partner_of_lower_bound O.raisingOutput O.loweringOutput
    (P0-J.output-R.output) (show 0 ≤ CE*ε*(energyNorm Y d φ)^2 by positivity) hLowerHere
  let U := P0-J.output-R.output-(2:ℝ) • O.raisingOutput
  let Ud := V-(2:ℝ) • O.loweringOutput
  let err := (‖P0-J.output-R.output‖^2-‖V‖^2)-
    4*(‖O.raisingOutput‖^2-‖O.loweringOutput‖^2)
  have hU : (2:ℝ) • O.raisingOutput+U=P0-J.output-R.output := by dsimp only [U];abel
  have hUd : (2:ℝ) • O.loweringOutput+Ud=V := by dsimp only [Ud];abel
  refine ⟨U,Ud,J.output+R.output,err,?_,hV,hSum,?_⟩
  · rw [hU,hUd]
    dsimp only [err]
    ring
  · dsimp only [U]
    abel

theorem uniformEstimate_of_truncatedPrincipalLowerBound {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (hc₀ : 0 < c₀)
    (hLower : ∀ CF CT : ℝ,0 ≤ CF → 0 ≤ CT → UniformTruncatedPrincipalLowerBound Y Ω K ρ c₀ M Cj CF CT) :
    ∃ floor ε₀ C : ℝ,1 ≤ floor ∧ 0 < ε₀ ∧ 0 < C ∧ UniformEstimate Y Ω K ρ c₀ M Cj floor ε₀ C :=
  uniformEstimate_of_principalPhysicalDecomposition hY hΩ hSub (by omega) K ρ c₀ M Cj hK hρ hc₀
    (uniformPrincipalPhysical_of_truncatedLowerBound hY hΩ hSub hm K ρ c₀ M Cj hK hρ hLower)
end ShrinkingSpheres
