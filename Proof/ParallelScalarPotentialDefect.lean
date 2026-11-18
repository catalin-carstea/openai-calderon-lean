import Proof.ParallelScalarPotentialDefectPoint
import Proof.ParallelNormAssemblyReservedScalarDefectDefinition

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

/-- Complete ACTUAL scalar-transpose defect against the SAME quadratic
potential adjoint, with literal factor2 and both real/imaginary components.
Constants precede profiles/frames and arbitrary fixed P/WF/W before tests.
The stronger epsilon-squared bound uses the original frozen energy. -/
theorem uniform_scalar_potential_defect_integral_bound
    {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 10 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (_hρ : 0 < ρ) (CF CT : ℝ) :
    UniformScalarPotentialDefectEstimate Y Ω K ρ c₀ M Cj CF CT := by
  intro CB CS CG CK _hCB _hCS hCG hCK
  obtain ⟨CScalar,hCScalar,hScalar⟩ := uniform_scalar_fiveHalf_defect_square_point_bound
    hY hΩ hSub (by omega) K ρ c₀ M Cj hK
  let CQ := (max (physicalPotentialGeneratorBudget CF) CG)^2*(49*potentialWordEntryBudget K)
  let C := CScalar+CQ^2*(3*K^2+1)
  have hCQ : 0 ≤ CQ := by dsimp only [CQ,potentialWordEntryBudget];positivity
  have hC : 0 ≤ C := by dsimp only [C];positivity
  refine ⟨1,1,C,by norm_num,le_rfl,hC,?_⟩
  intro floor hf ε hε hε1 d hd P _WF W φ hφ E D
  let Ur := E.realHigherSobolevSection (5/2:ℝ) (by norm_num)
  let Ui := E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)
  have hUr := E.contDiff_realHigherSobolevSection (5/2:ℝ) (by norm_num)
  have hUi := E.contDiff_imagHigherSobolevSection (5/2:ℝ) (by norm_num)
  have hIR := scalar_potential_defect_inner_integrable hY hSub hd (zero_lt_one.trans_le hK) P W hCG hCK
    Ur hUr E.supportSet E.compactSupportSet E.supportSubset
    (fun x hx => E.realHigherSobolevSection_zero _ _ (by norm_num) hx)
  have hII := scalar_potential_defect_inner_integrable hY hSub hd (zero_lt_one.trans_le hK) P W hCG hCK
    Ui hUi E.supportSet E.compactSupportSet E.supportSubset
    (fun x hx => E.imagHigherSobolevSection_zero _ _ (by norm_num) hx)
  have hInt : IntegrableOn (scalarPotentialDefectComplexDensity P W E) Y := hIR.add hII
  have hPoint (y : X) (hy : y ∈ Y) : |scalarPotentialDefectComplexDensity P W E y| ≤
      C*ε^2*physicalEnergyDensity d.γ d.frame d.radius φ y := by
    have hr := abs_scalar_potential_defect_inner_le P W Ur hUr y
    have hi := abs_scalar_potential_defect_inner_le P W Ui hUi y
    have hs := hScalar floor hf ε hε hε1 d hd φ E D hφ y hy
    have hq := scalar_potential_adjoint_weak_square_point_bound hY hSub hd hK hf hε hε1 hCG P W E D hφ hy
    unfold scalarPotentialDefectComplexDensity
    calc
      _ ≤ |scalarPotentialDefectCoreDensity P W Ur y|+|scalarPotentialDefectCoreDensity P W Ui y| := abs_add_le _ _
      _ ≤ metricDensity d.γ y*(
          ‖scalarFiveHalfDefectSection d (metricDensity d.γ) (scalarPrincipalMatrix d.γ d.g₂ d.radius) Ur y‖^2+
          ‖sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (P.potentialQuadraticAdjointCoreSection W Ur y)‖^2)+
        metricDensity d.γ y*(
          ‖scalarFiveHalfDefectSection d (metricDensity d.γ) (scalarPrincipalMatrix d.γ d.g₂ d.radius) Ui y‖^2+
          ‖sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (P.potentialQuadraticAdjointCoreSection W Ui y)‖^2) := add_le_add hr hi
      _ = scalarFiveHalfDefectSquareDensity d E y+metricDensity d.γ y*(
          ‖sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (P.potentialQuadraticAdjointCoreSection W Ur y)‖^2+
          ‖sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (P.potentialQuadraticAdjointCoreSection W Ui y)‖^2) := by
        dsimp only [Ur,Ui,scalarFiveHalfDefectSquareDensity]
        ring
      _ ≤ CScalar*ε^2*physicalEnergyDensity d.γ d.frame d.radius φ y+
          (CQ^2*(3*K^2+1))*ε^2*physicalEnergyDensity d.γ d.frame d.radius φ y := add_le_add hs hq
      _ = _ := by dsimp only [C];ring
  have hg : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have he (i : I) : ContDiffOn ℝ ∞ (fun x => d.frame x i) Y := (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hFrame : ∀ x ∈ Y,∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j)=if i=j then 1 else 0 :=
    fun x hx => hd.1.2.2.2.2.2.2.2 x (hSub hx)
  have hDom := (hd.2.2.2.2.1.integrableOn_physicalEnergyDensity hY hg (zero_lt_one.trans_le hK)
    d.frame he hFrame hf hφ).const_mul (C*ε^2)
  have hBound : ∀ᵐ y ∂volume.restrict Y,‖scalarPotentialDefectComplexDensity P W E y‖ ≤
      (C*ε^2)*physicalEnergyDensity d.γ d.frame d.radius φ y := by
    filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
    rw [Real.norm_eq_abs]
    exact hPoint y hy
  refine ⟨hInt,?_⟩
  have hN := norm_integral_le_of_norm_le hDom hBound
  simpa only [Real.norm_eq_abs,integral_const_mul,←energySq_eq_integral_density] using hN

end ShrinkingSpheres.ParallelEnergy
