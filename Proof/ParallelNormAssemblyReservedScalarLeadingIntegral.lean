import Proof.ParallelNormAssemblyReservedScalarIdentity
import Proof.ParallelNormAssemblyReservedScalarGreenIntegral
import Proof.PhysicalPotentialWordMass
import Proof.PhysicalPotentialQuadraticSmooth

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The literal scalar/potential leading density has a uniform epsilon
squared frozen-energy bound, after its symmetric/skew cancellation.
Only actual FIRST potential and adjoint covariant jets are used. -/
theorem uniform_actual_scalar_potential_leading_integral_bound {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 10 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (CF CT : ℝ) :
    UniformScalarPotentialLeadingEstimate Y Ω K ρ c₀ M Cj CF CT := by
  classical
  obtain ⟨ηF,CJF,hηF,hηF1,hCJF,hForward⟩ := uniform_physical_quadratic_potential_first_covariant_jet
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ CF
  obtain ⟨ηA,CNA,CJA,hηA,hηA1,hCNA,hCJA,hAdjoint⟩ := uniform_physical_potential_adjoint_first_covariant_jet
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ CF
  obtain ⟨Q0,Q1,hQ0,hQ1,hWeights⟩ := uniform_scalar_potential_weight_bounds
    hY hSub (by omega) K ρ c₀ M Cj hK
  let CNF := (physicalPotentialGeneratorBudget CF)^2*(49*potentialWordEntryBudget K)
  have hCNF : 0 ≤ CNF := by dsimp only [CNF,potentialWordEntryBudget];positivity
  obtain ⟨C0,hC0,hIntegral⟩ := uniform_scalar_quadratic_green_integral_bound
    hY hSub K ρ c₀ M Cj hK Q0 Q1 (CNF+CNA) (CJF+CJA)
      hQ0 hQ1 (add_nonneg hCNF hCNA) (add_nonneg hCJF hCJA)
  intro CB CS CG CK hCB hCS hCG hCK
  refine ⟨1,min ηF ηA,2*C0,lt_min hηF hηA,(min_le_left _ _).trans hηF1,by positivity,?_⟩
  intro floor hf ε hε hSmall d hd P WF W φ hφ E D
  have heF := hSmall.trans (min_le_left ηF ηA)
  have heA := hSmall.trans (min_le_right ηF ηA)
  have hε1 := heF.trans hηF1
  obtain ⟨A⟩ := hAdjoint floor hf ε hε heA d hd CT P
  let V := fun x => P.potentialQuadraticHalfL x-A.weak x
  have hFS := P.potentialQuadraticHalfL_smooth hY hSub hd (zero_lt_one.trans_le hK)
  have hVS : ContDiffOn ℝ ∞ V Y := hFS.sub A.smooth
  let N : I → X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) := fun a x =>
    if hx : x ∈ Y then
      Classical.choose (hForward floor hf ε hε heF d hd CT CG CK P W a x hx)-
        Classical.choose (A.jet CG CK W a x hx) else 0
  have hFP (a : I) (x : X) (hx : x ∈ Y) := Classical.choose_spec
    (hForward floor hf ε hε heF d hd CT CG CK P W a x hx)
  have hAP (a : I) (x : X) (hx : x ∈ Y) := Classical.choose_spec (A.jet CG CK W a x hx)
  have hNGraph (a : I) (x : X) (hx : x ∈ Y) :
      quadraticOperatorCovariantDerivativeL d V x (axis a)=
      (sphereSobolevInclusionL (-(1/2:ℝ)) (-(3/2:ℝ)) (by norm_num)).comp
        ((N a x).comp (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num))) := by
    simpa only [V,N,dite_eq_left hx] using quadratic_covariant_sub_graph d _ _ x (axis a)
      (hFS.contDiffAt (hY.mem_nhds hx)) (A.smooth.contDiffAt (hY.mem_nhds hx)) _ _ (hFP a x hx).1 (hAP a x hx).1
  have hNN (x : X) (hx : x ∈ Y) (a : I) : ‖N a x‖ ≤ (CJF+CJA)*ε*beta d.γ d.radius x := by
    simp only [N,dite_eq_left hx]
    calc
      _ ≤ ‖Classical.choose (hForward floor hf ε hε heF d hd CT CG CK P W a x hx)‖+
          ‖Classical.choose (A.jet CG CK W a x hx)‖ := norm_sub_le _ _
      _ ≤ CJF*ε*beta d.γ d.radius x+CJA*ε*beta d.γ d.radius x := add_le_add (hFP a x hx).2 (hAP a x hx).2
      _ = _ := by ring
  have hVN (x : X) (hx : x ∈ Y) : ‖V x‖ ≤ (CNF+CNA)*ε := by
    calc
      _ ≤ ‖P.potentialQuadraticHalfL x‖+‖A.weak x‖ := norm_sub_le _ _
      _ ≤ CNF*ε+CNA*ε := add_le_add
        (P.norm_potentialQuadraticHalfL_weighted_small hd hK hf hε hε1 hx) (A.norm_bound x hx)
      _ = _ := by ring
  have hh := hIntegral floor hf ε hε d hd (scalarPotentialWeight d)
    (scalar_potential_weight_smooth hSub hd (zero_lt_one.trans_le hK))
    (fun x hx a b => scalar_potential_weight_symmetric hSub hd (zero_lt_one.trans_le hK) hx a b)
    V hVS (fun x hx u v => actual_potential_adjoint_difference_skew P A hx (W x hx) u v)
    N hNGraph (fun x hx a b => (hWeights floor hf ε hε hε1 d hd x hx a b).1)
    (fun x hx a b => (hWeights floor hf ε hε hε1 d hd x hx a b).2 a)
    hVN hNN φ E D hφ
  let Ur := E.realHigherSobolevSection (5/2:ℝ) (by norm_num)
  let Ui := E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)
  let H := fun (U : X → SphereSobolev (5/2:ℝ)) (b : I) x => fiveHalfSectionCovariantDerivativeL d U x (axis b)
  let F := fun y => scalarQuadraticSecondDensity d (scalarPotentialWeight d) V (H Ur) Ur y+
    scalarQuadraticSecondDensity d (scalarPotentialWeight d) V (H Ui) Ui y
  have hEq : scalarPotentialLeadingComplexDensity P WF W E D=ᵐ[volume.restrict Y] (fun y => 2*F y) := by
    filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
    have hr := component_scalar_potential_leading_weak_eq hY hSub hd (zero_lt_one.trans_le hK) P A WF W Ur
      (E.contDiff_realHigherSobolevSection _ _) D.realComponent.raisingOutput D.realComponent.loweringOutput hy
    have hi := component_scalar_potential_leading_weak_eq hY hSub hd (zero_lt_one.trans_le hK) P A WF W Ui
      (E.contDiff_imagHigherSobolevSection _ _) D.imagComponent.raisingOutput D.imagComponent.loweringOutput hy
    change (_+_)+(_+_)=2*(_+_)
    linarith only [hr,hi]
  refine ⟨(hh.1.const_mul 2).congr hEq.symm,?_⟩
  rw [integral_congr_ae hEq,integral_const_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  exact (mul_le_mul_of_nonneg_left hh.2 (by norm_num : (0:ℝ)≤2)).trans_eq (by ring)

end ShrinkingSpheres.ParallelEnergy
