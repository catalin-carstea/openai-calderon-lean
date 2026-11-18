import Proof.ParallelModelFirstDefectPoint
import Proof.ParallelFirstSelfCoreSplitIntegral

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

lemma modelFirstDefectDensity_integrableOn
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CB CS CG CK : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (P : PhysicalPrincipalData Y d CF CT) (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U)
    (S : Set X) (hS : IsCompact S) (hSY : S ⊆ Y) (h0U : ∀ x ∉ S,U x=0) :
    IntegrableOn (modelFirstDefectDensity P WF W U) Y := by
  let U2 := fiveHalfToTwoSection U
  have hU2 : ContDiff ℝ ∞ U2 := (sphereSobolevInclusionL (5/2:ℝ) 2 (by norm_num)).contDiff.comp hU
  have h02 (x : X) (hx : x ∉ S) : U2 x=0 := by simp only [U2,fiveHalfToTwoSection,h0U x hx,map_zero]
  have hg : Elliptic Y K d.γ := ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have he (i : I) : ContDiffOn ℝ ∞ (fun x => d.frame x i) Y := (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hlog : ContDiffOn ℝ ∞ (fun x => Real.log (d.radius x)) Y :=
    hd.2.2.2.2.1.1.log (fun x hx => (hd.2.2.2.2.1.2 x hx).1.ne')
  have hModels := contDiff_supported_modelCovariantSections hY d hg hK he hlog U2 hU2 S hS.isClosed hSY h02
  have hM0 (x : X) (hx : x ∉ S) := modelCovariantSections_zero_off d U2 S hS.isClosed h02 x hx
  have hAdjLp : MemLp (fun x => modelLoweringSection d U2 x-modelAdjointDefectSection d U2 x) 2 (volume.restrict Y) :=
    (hModels.2.1.sub hModels.2.2).continuous.memLp_of_hasCompactSupport
      (HasCompactSupport.intro hS (fun x hx => by rw [(hM0 x hx).2.1,(hM0 x hx).2.2,sub_self]))
  have hw := hd.contDiffOn_scalarPrincipalConnectionWeight hY hSub hK
  have hFull := P.firstFormalAdjointCore_memLp hY hΩ hSub hd hK WF W hCG hCK U hU S hS hSY h0U hw 2
  have hLead := firstAdjointLeadingCoreSection_memLp hY hSub hd hK WF U hU S hS hSY h0U 2
  have hDef : MemLp (firstAdjointDefectCoreSection P WF W U) 2 (volume.restrict Y) := hFull.sub hLead
  exact integrableOn_local_weighted_inner_of_memLp hY.measurableSet hS hSY _ _ hAdjLp hDef
    (fun x _ hx => by rw [(hM0 x hx).2.1,(hM0 x hx).2.2,sub_self]) _ (hg.contDiffOn_density hK).continuousOn

/-- Closed original-energy integral bound for the COMPLETE corrected
model / first-adjoint-defect subsector, with both actual components. -/
theorem uniform_model_first_defect_integral_bound {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ)
    (CB CG CK : ℝ) (hCB : 0 ≤ CB) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK) :
    ∃ η C : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ C ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ CF CT CS : ℝ,
      ∀ P : PhysicalPrincipalData Y d CF CT,∀ WF : PhysicalFirstCommutatorPacket P CB CS ε,
      ∀ W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK,
      ∀ φ : Field,∀ E : HarmonicTestExpansion Y d.γ d.frame φ,∀ D : AngularModelData E d.radius,
      Test Y d.γ d.frame φ →
      let f := fun y => modelFirstDefectDensity P WF W (E.realHigherSobolevSection (5/2:ℝ) (by norm_num)) y+
        modelFirstDefectDensity P WF W (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)) y
      IntegrableOn f Y ∧ |∫ y in Y,f y| ≤ C*ε*energySq Y d.γ d.frame d.radius φ := by
  let RB := Classical.choice (scalar_model_raising_budget_exists hY hΩ (by omega) K ρ c₀ M Cj hK)
  obtain ⟨η,C0,hη,hη1,hC0,hPoint⟩ := uniform_model_first_defect_component_point_bound hY hΩ hSub hm K ρ c₀ M Cj hK hρ CB hCB RB
  let CE := 3*(3*K^2+1)
  refine ⟨η,C0*CE,hη,hη1,by dsimp only [CE];positivity,?_⟩
  intro floor hf ε hε hSmall d hd CF CT CS P WF W φ E D hφ
  let Ur := E.realHigherSobolevSection (5/2:ℝ) (by norm_num)
  let Ui := E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)
  let En := fun (U : X → SphereSobolev (5/2:ℝ)) y => ∑ i : I,halfCovariantDirectionEnergy d
    (fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)) y (beta d.γ d.radius y) (axis i)
  have hr := modelFirstDefectDensity_integrableOn hY hΩ hSub hd (zero_lt_one.trans_le hK) P WF W hCG hCK Ur
    (E.contDiff_realHigherSobolevSection _ _) E.supportSet E.compactSupportSet E.supportSubset
    (fun x hx => E.realHigherSobolevSection_zero _ _ (by norm_num) hx)
  have hi := modelFirstDefectDensity_integrableOn hY hΩ hSub hd (zero_lt_one.trans_le hK) P WF W hCG hCK Ui
    (E.contDiff_imagHigherSobolevSection _ _) E.supportSet E.compactSupportSet E.supportSubset
    (fun x hx => E.imagHigherSobolevSection_zero _ _ (by norm_num) hx)
  have hg : Elliptic Y K d.γ := ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have he (i : I) : ContDiffOn ℝ ∞ (fun x => d.frame x i) Y := (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hFrame : ∀ x ∈ Y,∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j)=if i=j then 1 else 0 :=
    fun x hx => hd.1.2.2.2.2.2.2.2 x (hSub hx)
  have hUR : (fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (Ur x))=
      E.realSobolevSection (3/2:ℝ) (by norm_num) :=
    funext (E.realHigherSobolevSection_inclusion _ _ _ (by norm_num) (by norm_num))
  have hUI : (fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (Ui x))=
      E.imagSobolevSection (3/2:ℝ) (by norm_num) :=
    funext (E.imagHigherSobolevSection_inclusion _ _ _ (by norm_num) (by norm_num))
  have hDom := (hd.2.2.2.2.1.integrableOn_physicalEnergyDensity hY hg (zero_lt_one.trans_le hK)
    d.frame he hFrame hf hφ).const_mul ((C0*CE)*ε)
  have hBound : ∀ᵐ y ∂volume.restrict Y,‖modelFirstDefectDensity P WF W Ur y+modelFirstDefectDensity P WF W Ui y‖ ≤
      ((C0*CE)*ε)*physicalEnergyDensity d.γ d.frame d.radius φ y := by
    filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
    have hR := hPoint floor hf ε hε hSmall d hd CF CT CS CG CK P WF W Ur (E.contDiff_realHigherSobolevSection _ _) y hy
    have hI := hPoint floor hf ε hε hSmall d hd CF CT CS CG CK P WF W Ui (E.contDiff_imagHigherSobolevSection _ _) y hy
    have hAxis : metricDensity d.γ y*(En Ur y+En Ui y) ≤ CE*physicalEnergyDensity d.γ d.frame d.radius φ y := by
      simpa only [En,hUR,hUI,CE] using half_covariant_axis_energy_le D hY hg hK he hFrame hφ.1 hy
    rw [Real.norm_eq_abs]
    calc
      _ ≤ |modelFirstDefectDensity P WF W Ur y|+|modelFirstDefectDensity P WF W Ui y| := abs_add_le _ _
      _ ≤ C0*ε*metricDensity d.γ y*En Ur y+C0*ε*metricDensity d.γ y*En Ui y := add_le_add hR hI
      _ = (C0*ε)*(metricDensity d.γ y*(En Ur y+En Ui y)) := by ring
      _ ≤ (C0*ε)*(CE*physicalEnergyDensity d.γ d.frame d.radius φ y) := mul_le_mul_of_nonneg_left hAxis (mul_nonneg hC0 hε)
      _ = _ := by ring
  refine ⟨hr.add hi,?_⟩
  simpa only [Real.norm_eq_abs,integral_const_mul,←energySq_eq_integral_density] using norm_integral_le_of_norm_le hDom hBound

end ShrinkingSpheres.ParallelEnergy
