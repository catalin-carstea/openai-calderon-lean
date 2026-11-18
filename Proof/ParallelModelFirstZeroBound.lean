import Proof.ParallelModelFirstZeroIntegral
import Proof.ParallelModelFirstZeroResidualPoint
import Proof.ParallelModelFirstZeroBudgets
import Proof.ParallelNormAssemblyReservedFirstWordMass

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

/-- Closed paired zero-model/complete-first integral estimate. Angular
commutators and the SAME actual adjoint Green remainder are combined before
the original physical energy estimate. -/
theorem uniform_model_first_zero_integral_bound {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ)
    (CB CG CK CF : ℝ) (hCB : 0 ≤ CB) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK) :
    ∃ η C : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ C ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ CT CS : ℝ,
      ∀ P : PhysicalPrincipalData Y d CF CT,∀ WF : PhysicalFirstCommutatorPacket P CB CS ε,
      ∀ W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK,
      ∀ φ : Field,∀ E : HarmonicTestExpansion Y d.γ d.frame φ,∀ D : AngularModelData E d.radius,
      Test Y d.γ d.frame φ →
      let f := fun y => modelFirstZeroDensity P WF (E.realHigherSobolevSection (5/2:ℝ) (by norm_num)) y+
        modelFirstZeroDensity P WF (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)) y
      IntegrableOn f Y ∧ |∫ y in Y,f y| ≤ C*ε*energySq Y d.γ d.frame d.radius φ := by
  let ZB := Classical.choice (model_first_zero_green_budget_exists hY hΩ hSub hm K ρ c₀ M Cj hK hρ CB hCB)
  let FB := Classical.choice (first_self_leading_forward_budget hY hΩ hSub hm K ρ c₀ M Cj hK hρ)
  let RB := Classical.choice (scalar_model_raising_budget_exists hY hΩ (by omega) K ρ c₀ M Cj hK)
  obtain ⟨BF,hBF,hForward⟩ := uniform_effective_first_bounded_remainder hY hΩ (by omega) K ρ c₀ M Cj hK (1/2:ℝ)
  obtain ⟨BA,hBA,hAdj⟩ := uniform_model_first_bounded_adjoint_three_half hY hΩ (by omega) K ρ c₀ M Cj hK
  obtain ⟨Q0,Q1,hQ0,hQ1,hWeight⟩ := uniform_model_first_zero_weight_jets hY hΩ hSub (by omega) K ρ c₀ M Cj hK
  let BD := principalModelDegreeCoordinateBudget K (M ⟨1,by omega⟩) (Cj 2)
  let BE := principalFirstErrorCoordinateTwoJetBudget K |M ⟨1,by omega⟩| |M ⟨2,by omega⟩| (Cj 2)
  let CW := |BD|+6+3*|BE|
  let CR := 54*Q0*(6*K*max (physicalPotentialGeneratorBudget CF) CG*CK*(3*K+1)*CW+2*RB.bound*(BF+BA))
  let CP := CR+ZB.C
  let CE := 3*(3*K^2+1)
  have hCW : 0 ≤ CW := by dsimp only [CW];positivity
  have hCR : 0 ≤ CR := by
    have hG : 0 ≤ max (physicalPotentialGeneratorBudget CF) CG := hCG.trans (le_max_right _ _)
    have := RB.nonneg
    dsimp only [CR]
    positivity
  have hCP : 0 ≤ CP := add_nonneg hCR ZB.C_nonneg
  refine ⟨min ZB.eta FB.eta,CP*CE,lt_min ZB.eta_pos FB.eta_pos,(min_le_left _ _).trans ZB.eta_le_one,by dsimp only [CE];positivity,?_⟩
  intro floor hf ε hε hSmall d hd CT CS P WF W φ E D hφ
  have hε1 := (hSmall.trans (min_le_left _ _)).trans ZB.eta_le_one
  obtain ⟨hJ,hGreenPoint⟩ := ZB.actual floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd CF CT CS P WF
  let Ur := E.realHigherSobolevSection (5/2:ℝ) (by norm_num)
  let Ui := E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)
  let En := fun (U : X → SphereSobolev (5/2:ℝ)) y => ∑ i : I,halfCovariantDirectionEnergy d
    (fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)) y (beta d.γ d.radius y) (axis i)
  let R := fun (U : X → SphereSobolev (5/2:ℝ)) y => modelFirstZeroResidualDensity P WF U y+
    modelFirstZeroPairedRemainder WF hJ U y
  have hP (b : I) (y : X) (hy : y ∈ Y) := P.firstCovariantCoordinateHigherL_balanced b y
    (FB.raw floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd CF CT P y hy b)
  have hr := model_first_zero_integral_reduction hY hΩ hSub hd (zero_lt_one.trans_le hK) P WF W hCG hCK hJ Ur
    (E.contDiff_realHigherSobolevSection _ _) E.supportSet E.compactSupportSet E.supportSubset
    (fun x hx => E.realHigherSobolevSection_zero _ _ (by norm_num) hx) hP
  have hi := model_first_zero_integral_reduction hY hΩ hSub hd (zero_lt_one.trans_le hK) P WF W hCG hCK hJ Ui
    (E.contDiff_imagHigherSobolevSection _ _) E.supportSet E.compactSupportSet E.supportSubset
    (fun x hx => E.imagHigherSobolevSection_zero _ _ (by norm_num) hx) hP
  have hPoint (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U) (y : X) (hy : y ∈ Y) :
      |R U y| ≤ CP*ε*metricDensity d.γ y*En U y := by
    have hMass (b : I) : (∑ a : PhysicalPotentialGeneratorIndex,|effectiveFirstWordCoefficient d b y a|) ≤ CW*ε/beta d.γ d.radius y := by
      have hNative := effective_first_normalized_word_mass_bound (CF:=CF) (CT:=CT) (by omega : 2 ≤ m) hY hd hK hf hε hε1 hy b
      have hCW' : BD+6+3*BE ≤ CW := by dsimp only [CW];linarith [le_abs_self BD,le_abs_self BE]
      exact hNative.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hCW' hε) (le_trans zero_le_one (hf.trans (hd.2.2.2.2.1.2 y hy).2.1)))
    have hRes := model_first_zero_residual_point_bound hY hd hK hf hε hCG hCK hCW RB.nonneg hBF hBA hQ0 P WF hy (W y hy) U
      (hU.differentiable (by simp) y) (fun b => hP b y hy)
      (fun c => (RB.actual floor ε d hd y hy 0 c).1)
      (fun b => (hForward floor hf ε hε hε1 d hd b).2 y hy)
      (fun b => (hAdj floor hf ε hε hε1 d hd b).2 y hy) hMass
      (fun k c => ((hWeight floor hf ε d hd k c).2 y hy 0).1)
    calc
      _ ≤ |modelFirstZeroResidualDensity P WF U y|+|modelFirstZeroPairedRemainder WF hJ U y| := abs_add_le _ _
      _ ≤ CR*ε*metricDensity d.γ y*En U y+ZB.C*ε*metricDensity d.γ y*En U y := add_le_add hRes (hGreenPoint U y hy)
      _ = _ := by dsimp only [CP];ring
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
    have hR := hPoint Ur (E.contDiff_realHigherSobolevSection _ _) y hy
    have hI := hPoint Ui (E.contDiff_imagHigherSobolevSection _ _) y hy
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
  have hEq : (∫ y in Y,modelFirstZeroDensity P WF Ur y+modelFirstZeroDensity P WF Ui y)=∫ y in Y,R Ur y+R Ui y := by
    rw [integral_add hr.1 hi.1,integral_add hr.2.1 hi.2.1,hr.2.2,hi.2.2]
  refine ⟨hr.1.add hi.1,?_⟩
  rw [hEq]
  simpa only [Real.norm_eq_abs,integral_const_mul,←energySq_eq_integral_density] using norm_integral_le_of_norm_le hDom hBound

end ShrinkingSpheres.ParallelEnergy
