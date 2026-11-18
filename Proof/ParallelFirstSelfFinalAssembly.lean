import Proof.ParallelFirstSelfLeadingIntegral
import Proof.ParallelFirstSelfDefectCrossIntegral

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set MeasureTheory
namespace ShrinkingSpheres.ParallelEnergy

/-- Complete checked physical first-order self-comparison assembled from
the actual leading Hodge comparison and both complete adjoint defects. -/
theorem uniform_first_self_norm_comparison_closed {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (CF CT CB CS CG CK : ℝ)
    (hCB : 0 ≤ CB) (hCS : 0 ≤ CS) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK) :
    ∃ η C : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ C ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      ∀ P : PhysicalPrincipalData Y d CF CT,
      ∀ WF : PhysicalFirstCommutatorPacket P CB CS ε,
      ∀ W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK,
      ∀ φ : Field,∀ E : HarmonicTestExpansion Y d.γ d.frame φ,
      ∀ D : AngularModelData E d.radius,Test Y d.γ d.frame φ →
        IntegrableOn (firstSelfComplexDensity P WF W E) Y ∧
        |∫ y in Y,firstSelfComplexDensity P WF W E y| ≤ C*ε*energySq Y d.γ d.frame d.radius φ := by
  obtain ⟨ηL,CL,hηL,hηL1,hCL,hL⟩ := uniform_first_self_leading_integral_bound
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ CF CT CB CS CG CK hCB hCS hCG hCK
  obtain ⟨ηC,CC,hηC,hηC1,hCC,hC⟩ := uniform_first_self_defect_cross_integral_bound
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ CB CG CK hCB hCG hCK
  obtain ⟨ηD,CD,hηD,hηD1,hCD,hD⟩ := uniform_first_self_defect_square_integral_bound
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ CB CG CK hCB hCG hCK
  refine ⟨min ηL (min ηC ηD),CL+CC+CD,lt_min hηL (lt_min hηC hηD),
    (min_le_left _ _).trans hηL1,by positivity,?_⟩
  intro floor hf ε hε hSmall d hd P WF W φ E D hφ
  have hSmallL := hSmall.trans (min_le_left _ _)
  have hSmallC := hSmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hSmallD := hSmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hε1 := hSmallL.trans hηL1
  have hεsq : ε^2 ≤ ε := by nlinarith only [hε,hε1]
  have hEnergy := energySq_nonneg Y d.γ d.frame d.radius φ
  obtain ⟨hLI,hLN⟩ := hL floor hf ε hε hSmallL d hd P WF W φ E D hφ
  obtain ⟨hCI,hCN⟩ := hC floor hf ε hε hSmallC d hd CF CT CS P WF W φ E D hφ
  obtain ⟨hDI,hDN⟩ := hD floor hf ε hε hSmallD d hd CF CT CS P WF W φ E D hφ
  apply firstSelfComplexDensity_integral_bound_of_core_split P WF W E hLI hCI hDI CL CC CD hLN
  · exact hCN.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hεsq hCC) hEnergy)
  · exact hDN.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hεsq hCD) hEnergy)

end ShrinkingSpheres.ParallelEnergy
