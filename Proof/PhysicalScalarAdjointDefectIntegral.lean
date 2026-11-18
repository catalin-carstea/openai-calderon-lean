import Proof.PhysicalScalarAdjointDefectPoint
import Proof.SmoothEnergyRegularity
import Proof.LocalSupportedOperatorPairing

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic OperatorForms

lemma integrable_supported_weighted_norm_sq {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (mu : X → ℝ) (U : X → E) (S : Set X) (hS : IsCompact S)
    (hmu : ∀ x ∈ S,ContDiffAt ℝ ∞ mu x) (hU : ContDiff ℝ ∞ U)
    (h0 : ∀ x ∉ S,U x=0) : Integrable (fun x => mu x*‖U x‖^2) := by
  have ht := integrable_local_weighted_operator_pair (innerSL ℝ) mu U U
    (fun _ => ContinuousLinearMap.id ℝ E) S hS hmu hU hU h0 (fun _ _ => contDiffAt_const)
  change Integrable (fun x => mu x*⟪U x,U x⟫_ℝ) at ht
  simpa only [real_inner_self_eq_norm_sq] using ht

theorem uniform_physical_scalar_adjoint_defect_square_integral_bound {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 2 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ 1 → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ φ : Field,
      ∀ E : HarmonicTestExpansion Y d.γ d.frame φ,∀ D : AngularModelData E d.radius,
      Test Y d.γ d.frame φ →
      IntegrableOn (scalarAdjointDefectSquareDensity d E) Y ∧
        |∫ y in Y,scalarAdjointDefectSquareDensity d E y| ≤
          C*ε^2*energySq Y d.γ d.frame d.radius φ := by
  obtain ⟨C,hC,hPoint⟩ := uniform_physical_scalar_adjoint_defect_square_point_bound hY hΩ hSub hm K ρ c₀ M Cj hK
  refine ⟨C,hC,?_⟩
  intro floor hf ε hε hε1 d hd φ E D hφ
  let mu := metricDensity d.γ
  let A := scalarPrincipalMatrix d.γ d.g₂ d.radius
  let Ur := E.realSobolevSection 2 (by norm_num)
  let Ui := E.imagSobolevSection 2 (by norm_num)
  let Dr := scalarCovariantAdjointDefectSection d mu A Ur
  let Di := scalarCovariantAdjointDefectSection d mu A Ui
  have hKpos := zero_lt_one.trans_le hK
  have hg : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have hg2 : Elliptic Y K d.g₂ :=
    ⟨fun i j => (hd.1.2.2.1.1 i j).mono hSub,fun x hx => hd.1.2.2.1.2 x (hSub hx)⟩
  have he (i : I) : ContDiffOn ℝ ∞ (fun x => d.frame x i) Y := (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hFrame : ∀ x ∈ Y,∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j)=if i=j then 1 else 0 :=
    fun x hx => hd.1.2.2.2.2.2.2.2 x (hSub hx)
  have hmuS := hg.contDiffOn_density hKpos
  have haS (i j : I) : ContDiffOn ℝ ∞ (fun x => A x i j) Y := by
    simpa only [A,scalarPrincipalMatrix,Matrix.smul_apply,smul_eq_mul] using
      hd.2.2.2.2.1.1.mul (contDiffOn_principal_entry hg hg2 hKpos i j)
  have hmu0 : ∀ x ∈ Y,mu x ≠ 0 := fun x hx => (metricDensity_pos hg hKpos hx).ne'
  have hmu (x : X) (hx : x ∈ E.supportSet) : ContDiffAt ℝ ∞ mu x :=
    hmuS.contDiffAt (hY.mem_nhds (E.supportSubset hx))
  have h0R (x : X) (hx : x ∉ E.supportSet) : Ur x=0 := E.realSobolevSection_zero 2 (by norm_num) hx
  have h0I (x : X) (hx : x ∉ E.supportSet) : Ui x=0 := E.imagSobolevSection_zero 2 (by norm_num) hx
  have hDR := contDiff_supported_scalarCovariantAdjointDefectSection hY d hg hKpos he mu hmuS hmu0 A haS
    Ur (E.contDiff_realSobolevSection 2 (by norm_num)) E.supportSet E.compactSupportSet.isClosed E.supportSubset h0R
  have hDI := contDiff_supported_scalarCovariantAdjointDefectSection hY d hg hKpos he mu hmuS hmu0 A haS
    Ui (E.contDiff_imagSobolevSection 2 (by norm_num)) E.supportSet E.compactSupportSet.isClosed E.supportSubset h0I
  have hRInt := integrable_supported_weighted_norm_sq mu Dr E.supportSet E.compactSupportSet hmu hDR.1 hDR.2
  have hIInt := integrable_supported_weighted_norm_sq mu Di E.supportSet E.compactSupportSet hmu hDI.1 hDI.2
  have hInt : Integrable (scalarAdjointDefectSquareDensity d E) := by
    change Integrable (fun x => mu x*(‖Dr x‖^2+‖Di x‖^2))
    simp only [mul_add]
    exact hRInt.add hIInt
  have hBound : ∀ᵐ y ∂volume.restrict Y,‖scalarAdjointDefectSquareDensity d E y‖ ≤
      (C*ε^2)*physicalEnergyDensity d.γ d.frame d.radius φ y := by
    filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
    have hNonneg : 0 ≤ scalarAdjointDefectSquareDensity d E y := by
      unfold scalarAdjointDefectSquareDensity
      exact mul_nonneg (Real.sqrt_nonneg _) (add_nonneg (sq_nonneg _) (sq_nonneg _))
    rw [Real.norm_eq_abs,abs_of_nonneg hNonneg]
    exact hPoint floor hf ε hε hε1 d hd φ E D hφ y hy
  have hDom := (hd.2.2.2.2.1.integrableOn_physicalEnergyDensity hY hg hKpos d.frame he hFrame hf hφ).const_mul (C*ε^2)
  refine ⟨hInt.integrableOn,?_⟩
  have ht := norm_integral_le_of_norm_le hDom hBound
  simpa only [Real.norm_eq_abs,integral_const_mul,←energySq_eq_integral_density] using ht

end ShrinkingSpheres
