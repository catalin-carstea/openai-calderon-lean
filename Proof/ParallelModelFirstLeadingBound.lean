import Proof.ParallelModelFirstLeadingIntegral
import Proof.ParallelModelFirstLeadingRemainder

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Closed paired TWO-base model/complete-first integral estimate. Both
actual components, arbitrary fixed compatible witnesses and the original
energy are retained. Horizontal exchange is integrated before norms. -/
theorem uniform_model_first_leading_integral_bound {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ)
    (CB : ℝ) (hCB : 0 ≤ CB) :
    ∃ η C : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ C ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ CF CT CS CG CK : ℝ,
      ∀ P : PhysicalPrincipalData Y d CF CT,∀ WF : PhysicalFirstCommutatorPacket P CB CS ε,
      ∀ W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK,
      ∀ φ : Field,∀ E : HarmonicTestExpansion Y d.γ d.frame φ,∀ D : AngularModelData E d.radius,
      Test Y d.γ d.frame φ →
      let f := fun y => modelFirstLeadingDensity P WF (E.realHigherSobolevSection (5/2:ℝ) (by norm_num)) y+
        modelFirstLeadingDensity P WF (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)) y
      IntegrableOn f Y ∧ |∫ y in Y,f y| ≤ C*ε*energySq Y d.γ d.frame d.radius φ := by
  obtain ⟨ηP,CP,hηP,hηP1,hCP,hPoint⟩ := uniform_model_first_leading_remainder_component_point_bound hY hΩ hSub hm K ρ c₀ M Cj hK hρ CB hCB
  let FB := Classical.choice (first_self_leading_forward_budget hY hΩ hSub hm K ρ c₀ M Cj hK hρ)
  let CE := 3*(3*K^2+1)
  refine ⟨min ηP FB.eta,CP*CE,lt_min hηP FB.eta_pos,(min_le_left _ _).trans hηP1,by dsimp only [CE];positivity,?_⟩
  intro floor hf ε hε hSmall d hd CF CT CS CG CK P WF W φ E D hφ
  let Ur := E.realHigherSobolevSection (5/2:ℝ) (by norm_num)
  let Ui := E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)
  let En := fun (U : X → SphereSobolev (5/2:ℝ)) y => ∑ i : I,halfCovariantDirectionEnergy d
    (fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)) y (beta d.γ d.radius y) (axis i)
  let R := fun (U : X → SphereSobolev (5/2:ℝ)) y => modelFirstAngularCommutatorDensity P WF U y+
    modelFirstHodgeRemainder WF U y+modelFirstJetDensity P WF W U y
  have hP (b : I) (y : X) (hy : y ∈ Y) := P.firstCovariantCoordinateHigherL_balanced b y
    (FB.raw floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd CF CT P y hy b)
  have hr := model_first_leading_integral_reduction hY hΩ hSub hd (zero_lt_one.trans_le hK) P WF W Ur
    (E.contDiff_realHigherSobolevSection _ _) E.supportSet E.compactSupportSet E.supportSubset
    (fun x hx => E.realHigherSobolevSection_zero _ _ (by norm_num) hx) hP
  have hi := model_first_leading_integral_reduction hY hΩ hSub hd (zero_lt_one.trans_le hK) P WF W Ui
    (E.contDiff_imagHigherSobolevSection _ _) E.supportSet E.compactSupportSet E.supportSubset
    (fun x hx => E.imagHigherSobolevSection_zero _ _ (by norm_num) hx) hP
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
    d.frame he hFrame hf hφ).const_mul ((CP*CE)*ε)
  have hBound : ∀ᵐ y ∂volume.restrict Y,‖R Ur y+R Ui y‖ ≤ ((CP*CE)*ε)*physicalEnergyDensity d.γ d.frame d.radius φ y := by
    filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
    have hR := hPoint floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd CF CT CS CG CK P WF W Ur
      (E.contDiff_realHigherSobolevSection _ _) y hy
    have hI := hPoint floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd CF CT CS CG CK P WF W Ui
      (E.contDiff_imagHigherSobolevSection _ _) y hy
    have hAxis : metricDensity d.γ y*(En Ur y+En Ui y) ≤ CE*physicalEnergyDensity d.γ d.frame d.radius φ y := by
      simpa only [En,hUR,hUI,CE] using half_covariant_axis_energy_le D hY hg hK he hFrame hφ.1 hy
    rw [Real.norm_eq_abs]
    calc
      _ ≤ |R Ur y|+|R Ui y| := abs_add_le _ _
      _ ≤ CP*ε*metricDensity d.γ y*En Ur y+CP*ε*metricDensity d.γ y*En Ui y := add_le_add hR hI
      _ = (CP*ε)*(metricDensity d.γ y*(En Ur y+En Ui y)) := by ring
      _ ≤ (CP*ε)*(CE*physicalEnergyDensity d.γ d.frame d.radius φ y) := mul_le_mul_of_nonneg_left hAxis (mul_nonneg hCP hε)
      _ = _ := by ring
  have hRI : IntegrableOn (fun y => R Ur y+R Ui y) Y := hr.2.1.add hi.2.1
  have hEq : (∫ y in Y,modelFirstLeadingDensity P WF Ur y+modelFirstLeadingDensity P WF Ui y)=∫ y in Y,R Ur y+R Ui y := by
    rw [integral_add hr.1 hi.1,integral_add hr.2.1 hi.2.1,hr.2.2,hi.2.2]
  refine ⟨hr.1.add hi.1,?_⟩
  rw [hEq]
  simpa only [Real.norm_eq_abs,integral_const_mul,←energySq_eq_integral_density] using norm_integral_le_of_norm_le hDom hBound

end ShrinkingSpheres.ParallelEnergy
