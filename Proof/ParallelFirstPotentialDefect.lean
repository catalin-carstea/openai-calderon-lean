import Proof.ParallelFirstPotentialIntegrability
import Proof.ParallelFirstSelfDefectSquareIntegral
import Proof.ParallelNormAssemblyReservedAdjointWeakGraph

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.NativeHarmonicHalfCoarseDualPairing

lemma firstPotential_defect_point_bound {Y Ω : Set X} {m : ℕ}
    {K ρ c₀ floor ε CF CT CB CS CG CK CR : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (P : PhysicalPrincipalData Y d CF CT) (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hCG : 0 ≤ CG) (hCR : 0 ≤ CR)
    (U : X → SphereSobolev (5/2:ℝ)) {y : X} (hy : y ∈ Y)
    (R : SphereSobolev (1/2:ℝ))
    (hR : firstAdjointDefectCoreSection P WF W U y=sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) R)
    (hRN : ‖R‖ ≤ CR*ε*‖sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y)‖) :
    let CQ := (max (physicalPotentialGeneratorBudget CF) CG)^2*(49*potentialWordEntryBudget K)
    |firstPotentialDefectDensity P WF W U y| ≤
      (2*CR*CQ*ε^2)*metricDensity d.γ y*
        ‖sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y)‖^2 := by
  let u := sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y)
  let CQ := (max (physicalPotentialGeneratorBudget CF) CG)^2*(49*potentialWordEntryBudget K)
  have hCQ : 0 ≤ CQ := by dsimp only [CQ,potentialWordEntryBudget];positivity
  have hQN := actual_potential_adjoint_weak_norm_bound P hd hK hf hε hε1 hy hCG (W y hy) u
  have hQ : ‖sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
      (P.potentialQuadraticAdjointCoreSection W U y)‖ ≤ CQ*ε*‖u‖ := by
    rw [actual_potential_adjoint_section_weak_graph P W U hy]
    exact hQN
  have hPair : ⟪firstAdjointDefectCoreSection P WF W U y,P.potentialQuadraticAdjointCoreSection W U y⟫_ℝ=
      sphereSobolevDualPairing (1/2:ℝ) R (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
        (P.potentialQuadraticAdjointCoreSection W U y)) := by
    rw [sphereSobolevDualPairing_zero_inclusion,hR,real_inner_comm]
    norm_num
  have hN : |⟪firstAdjointDefectCoreSection P WF W U y,P.potentialQuadraticAdjointCoreSection W U y⟫_ℝ| ≤
      CR*CQ*ε^2*‖u‖^2 := by
    rw [hPair]
    calc
      _ ≤ ‖R‖*‖sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
          (P.potentialQuadraticAdjointCoreSection W U y)‖ := abs_sphereSobolevDualPairing_le _ _ _
      _ ≤ (CR*ε*‖u‖)*(CQ*ε*‖u‖) := mul_le_mul hRN hQ (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hμ : 0 ≤ metricDensity d.γ y := Real.sqrt_nonneg _
  unfold firstPotentialDefectDensity
  rw [abs_mul,abs_of_nonneg (mul_nonneg (by norm_num) hμ)]
  exact (mul_le_mul_of_nonneg_left hN (mul_nonneg (by norm_num) hμ)).trans_eq (by ring)

/-- The complete actual first-adjoint defect against the SAME quadratic
adjoint is bounded by epsilon squared times the original frozen energy. -/
theorem uniform_first_potential_defect_integral_bound
    {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 10 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (CF CB CG CK : ℝ)
    (hCB : 0 ≤ CB) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK) :
    ∃ η CD : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CD ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ CT CS : ℝ,
      ∀ P : PhysicalPrincipalData Y d CF CT,
      ∀ WF : PhysicalFirstCommutatorPacket P CB CS ε,
      ∀ W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK,
      ∀ φ : Field,∀ E : HarmonicTestExpansion Y d.γ d.frame φ,
      ∀ D : AngularModelData E d.radius,Test Y d.γ d.frame φ →
      IntegrableOn (firstPotentialDefectComplexDensity P WF W E) Y ∧
        |∫ y in Y,firstPotentialDefectComplexDensity P WF W E y| ≤
          CD*ε^2*energySq Y d.γ d.frame d.radius φ := by
  obtain ⟨η,CR,hη,hη1,hCR,hDefect⟩ := uniform_first_adjoint_defect_higher_bound
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ CB hCB
  let CQ := (max (physicalPotentialGeneratorBudget CF) CG)^2*(49*potentialWordEntryBudget K)
  let CD := 2*CR*CQ*(3*K^2+1)
  have hCQ : 0 ≤ CQ := by dsimp only [CQ,potentialWordEntryBudget];positivity
  refine ⟨η,CD,hη,hη1,by dsimp only [CD];positivity,?_⟩
  intro floor hf ε hε hSmall d hd CT CS P WF W φ E D hφ
  have hg : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have he (i : I) : ContDiffOn ℝ ∞ (fun x => d.frame x i) Y := (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hFrame : ∀ y ∈ Y,∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j)=if i=j then 1 else 0 :=
    fun y hy => hd.1.2.2.2.2.2.2.2 y (hSub hy)
  have hIntR := firstPotentialDefectDensity_integrable hY hΩ hSub hd (zero_lt_one.trans_le hK)
    P WF W hCG hCK (E.realHigherSobolevSection (5/2:ℝ) (by norm_num))
    (E.contDiff_realHigherSobolevSection _ _) E.supportSet E.compactSupportSet E.supportSubset
    (fun x hx => E.realHigherSobolevSection_zero _ _ (by norm_num) hx)
  have hIntI := firstPotentialDefectDensity_integrable hY hΩ hSub hd (zero_lt_one.trans_le hK)
    P WF W hCG hCK (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num))
    (E.contDiff_imagHigherSobolevSection _ _) E.supportSet E.compactSupportSet E.supportSubset
    (fun x hx => E.imagHigherSobolevSection_zero _ _ (by norm_num) hx)
  have hBound : ∀ᵐ y ∂volume.restrict Y,‖firstPotentialDefectComplexDensity P WF W E y‖ ≤
      (CD*ε^2)*physicalEnergyDensity d.γ d.frame d.radius φ y := by
    filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
    have hβ : 1 ≤ beta d.γ d.radius y := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
    have hPoint (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiffOn ℝ ∞ U Y) :
        |firstPotentialDefectDensity P WF W U y| ≤ (2*CR*CQ*ε^2)*metricDensity d.γ y*
          ‖sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y)‖^2 := by
      obtain ⟨R,hR,hRN⟩ := hDefect floor hf ε hε hSmall d hd CF CT CS CG CK P WF W U hU y hy
      exact firstPotential_defect_point_bound P WF W hd hK hf hε (hSmall.trans hη1) hCG hCR U hy R hR hRN
    have hR := hPoint (E.realHigherSobolevSection (5/2:ℝ) (by norm_num))
      (E.contDiff_realHigherSobolevSection _ _).contDiffOn
    have hI := hPoint (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num))
      (E.contDiff_imagHigherSobolevSection _ _).contDiffOn
    rw [E.realHigherSobolevSection_inclusion _ _ _ (by norm_num) (by norm_num)] at hR
    rw [E.imagHigherSobolevSection_inclusion _ _ _ (by norm_num) (by norm_num)] at hI
    have hMass := first_self_complex_mass_density_le hY hg hK he hFrame E D hφ hy hβ
    rw [Real.norm_eq_abs]
    unfold firstPotentialDefectComplexDensity
    calc
      _ ≤ |firstPotentialDefectDensity P WF W (E.realHigherSobolevSection (5/2:ℝ) (by norm_num)) y|+
          |firstPotentialDefectDensity P WF W (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)) y| := abs_add_le _ _
      _ ≤ _ := add_le_add hR hI
      _ = (2*CR*CQ*ε^2)*(metricDensity d.γ y*(‖E.realSobolevSection (3/2:ℝ) (by norm_num) y‖^2+
          ‖E.imagSobolevSection (3/2:ℝ) (by norm_num) y‖^2)) := by ring
      _ ≤ (2*CR*CQ*ε^2)*((3*K^2+1)*physicalEnergyDensity d.γ d.frame d.radius φ y) :=
        mul_le_mul_of_nonneg_left hMass (by positivity)
      _ = _ := by dsimp only [CD];ring
  have hDom := (hd.2.2.2.2.1.integrableOn_physicalEnergyDensity hY hg (zero_lt_one.trans_le hK)
    d.frame he hFrame hf hφ).const_mul (CD*ε^2)
  refine ⟨hIntR.add hIntI,?_⟩
  have hN := norm_integral_le_of_norm_le hDom hBound
  simpa only [Real.norm_eq_abs,integral_const_mul,←energySq_eq_integral_density] using hN

end ShrinkingSpheres.ParallelEnergy
