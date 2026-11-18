import Proof.ParallelNormAssemblyReservedScalarRemainderPoint
import Proof.ParallelScalarFirstCanonicalEnergy
import Proof.ParallelNormAssemblyReservedModel

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

/-- The symmetric scalar/skew-quadratic Green remainder has the original
uniform epsilon-squared physical-energy bound, using canonical H5/2
sources and only FIRST genuine quadratic coefficient jets. -/
theorem uniform_scalar_quadratic_green_integral_bound {Y Ω : Set X}
    (hY : IsOpen Y) (hSub : Y ⊆ Ω) {m : ℕ}
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K)
    (Q0 Q1 CN CJ : ℝ) (hQ0 : 0 ≤ Q0) (hQ1 : 0 ≤ Q1) (hCN : 0 ≤ CN) (hCJ : 0 ≤ CJ) :
    ∃ C0 : ℝ,0 ≤ C0 ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ∀ d,
    Admissible Y Ω K ρ c₀ M Cj floor ε d →
    ∀ q : I → I → X → ℝ,(∀ a b,ContDiffOn ℝ ∞ (q a b) Y) →
    (∀ y ∈ Y,∀ a b,q a b y=q b a y) →
    ∀ V : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),ContDiffOn ℝ ∞ V Y →
    (∀ y ∈ Y,∀ u v : SphereSobolev (3/2:ℝ),sphereSobolevDualPairing (1/2:ℝ)
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u) (V y v)=
      -sphereSobolevDualPairing (1/2:ℝ) (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) v) (V y u)) →
    ∀ N : I → X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
    (∀ a y,y ∈ Y → quadraticOperatorCovariantDerivativeL d V y (axis a)=
      (sphereSobolevInclusionL (-(1/2:ℝ)) (-(3/2:ℝ)) (by norm_num)).comp
        ((N a y).comp (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)))) →
    (∀ y ∈ Y,∀ a b,|q a b y| ≤ Q0*ε/(beta d.γ d.radius y)^2*metricDensity d.γ y) →
    (∀ y ∈ Y,∀ a b,|fderiv ℝ (q a b) y (axis a)| ≤ Q1*ε/beta d.γ d.radius y*metricDensity d.γ y) →
    (∀ y ∈ Y,‖V y‖ ≤ CN*ε) →
    (∀ y ∈ Y,∀ a,‖N a y‖ ≤ CJ*ε*beta d.γ d.radius y) →
    ∀ φ : Field,∀ E : HarmonicTestExpansion Y d.γ d.frame φ,∀ D : AngularModelData E d.radius,
    Test Y d.γ d.frame φ →
      let Ur := E.realHigherSobolevSection (5/2:ℝ) (by norm_num)
      let Ui := E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)
      let H := fun (U : X → SphereSobolev (5/2:ℝ)) (b : I) x => fiveHalfSectionCovariantDerivativeL d U x (axis b)
      let F := fun y => scalarQuadraticSecondDensity d q V (H Ur) Ur y+
        scalarQuadraticSecondDensity d q V (H Ui) Ui y
      IntegrableOn F Y ∧ |∫ y in Y,F y| ≤ C0*ε^2*energySq Y d.γ d.frame d.radius φ := by
  let CP := 18*(Q0*CJ+Q1*CN)
  let CE := 3*(3*K^2+1)
  have hCP : 0 ≤ CP := by dsimp only [CP];positivity
  have hCE : 0 ≤ CE := by dsimp only [CE];positivity
  refine ⟨CP*CE,mul_nonneg hCP hCE,?_⟩
  intro floor hf ε hε d hd q hq hSym V hV hSkew N hN hq0 hq1 hVN hNN φ E D hφ
  let Ur := E.realHigherSobolevSection (5/2:ℝ) (by norm_num)
  let Ui := E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)
  let H := fun (U : X → SphereSobolev (5/2:ℝ)) (b : I) x => fiveHalfSectionCovariantDerivativeL d U x (axis b)
  let F := fun U => scalarQuadraticSecondDensity d q V (H U) U
  let R := fun U => scalarQuadraticSecondRemainder q V N (H U) U
  let En := fun (U : X → SphereSobolev (5/2:ℝ)) y => ∑ i : I,halfCovariantDirectionEnergy d
    (fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)) y (beta d.γ d.radius y) (axis i)
  have hg : Elliptic Y K d.γ :=
    ⟨fun a b => (hd.1.1.1 a b).mono hSub,fun y hy => hd.1.1.2 y (hSub hy)⟩
  have he (i : I) : ContDiffOn ℝ ∞ (fun x => d.frame x i) Y := (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hFrame (y : X) (hy : y ∈ Y) := hd.1.2.2.2.2.2.2.2 y (hSub hy)
  have hPer (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U)
      (hU0 : ∀ x ∉ E.supportSet,U x=0) :
      IntegrableOn (F U) Y ∧ IntegrableOn (R U) Y ∧ (∫ y in Y,F U y)=∫ y in Y,R U y := by
    have hHS (b : I) := contDiff_supported_five_half_covariant_derivative hY d hg (zero_lt_one.trans_le hK)
      he U hU E.supportSet E.compactSupportSet.isClosed E.supportSubset hU0 (axis b)
    exact symmetric_scalar_quadratic_green_reduction hY d hg (zero_lt_one.trans_le hK) he q hq hSym V hV hSkew N hN
      U hU (H U) (fun b => (hHS b).1) (fun _ _ _ => rfl)
      E.supportSet E.compactSupportSet E.supportSubset hU0 (fun b => (hHS b).2)
  have hr := hPer Ur (E.contDiff_realHigherSobolevSection _ _)
    (fun x hx => E.realHigherSobolevSection_zero _ _ (by norm_num) hx)
  have hi := hPer Ui (E.contDiff_imagHigherSobolevSection _ _)
    (fun x hx => E.imagHigherSobolevSection_zero _ _ (by norm_num) hx)
  have hPoint (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U) (y : X) (hy : y ∈ Y) :
      |R U y| ≤ CP*ε^2*metricDensity d.γ y*En U y := by
    let U3 := fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)
    let β := beta d.γ d.radius y
    have hβ : 1 ≤ β := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
    have hDir (i : I) : 0 ≤ halfCovariantDirectionEnergy d U3 y β (axis i) := by
      dsimp only [halfCovariantDirectionEnergy];positivity
    have hEn : 0 ≤ En U y := Finset.sum_nonneg (fun i _ => hDir i)
    have hSingle (i : I) := Finset.single_le_sum (f:=fun i : I => halfCovariantDirectionEnergy d U3 y β (axis i))
      (fun i _ => hDir i) (Finset.mem_univ i)
    have hHB (b : I) : β⁻¹*‖sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (H U b y)‖^2 ≤ En U y := by
      rw [five_half_covariant_derivative_to_half d U y (axis b) (hU.differentiable (by simp) y)]
      exact (le_add_of_nonneg_right (by positivity : 0 ≤ β*‖U3 y‖^2)).trans (hSingle b)
    have hMass : β*‖U3 y‖^2 ≤ En U y :=
      (le_add_of_nonneg_left (by positivity : 0 ≤ β⁻¹*‖halfSectionCovariantDerivativeL d U3 y (axis 0)‖^2)).trans (hSingle 0)
    exact scalar_quadratic_second_remainder_bound q V N (H U) U y Q0 Q1 CN CJ ε β (metricDensity d.γ y) (En U y)
      hQ0 hQ1 hCN hCJ hε hβ (Real.sqrt_nonneg _) hEn (hq0 y hy) (hq1 y hy) (hVN y hy) (hNN y hy) hHB hMass
  have hUR : (fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (Ur x))=
      E.realSobolevSection (3/2:ℝ) (by norm_num) := funext (E.realHigherSobolevSection_inclusion _ _ _ (by norm_num) (by norm_num))
  have hUI : (fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (Ui x))=
      E.imagSobolevSection (3/2:ℝ) (by norm_num) := funext (E.imagHigherSobolevSection_inclusion _ _ _ (by norm_num) (by norm_num))
  have hBound : ∀ᵐ y ∂volume.restrict Y,‖R Ur y+R Ui y‖ ≤ (CP*CE*ε^2)*physicalEnergyDensity d.γ d.frame d.radius φ y := by
    filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
    have hAxis : metricDensity d.γ y*(En Ur y+En Ui y) ≤ CE*physicalEnergyDensity d.γ d.frame d.radius φ y := by
      simpa only [En,hUR,hUI,CE] using half_covariant_axis_energy_le D hY hg hK he hFrame hφ.1 hy
    rw [Real.norm_eq_abs]
    calc
      _ ≤ |R Ur y|+|R Ui y| := abs_add_le _ _
      _ ≤ CP*ε^2*metricDensity d.γ y*En Ur y+CP*ε^2*metricDensity d.γ y*En Ui y :=
        add_le_add (hPoint Ur (E.contDiff_realHigherSobolevSection _ _) y hy)
          (hPoint Ui (E.contDiff_imagHigherSobolevSection _ _) y hy)
      _ = (CP*ε^2)*(metricDensity d.γ y*(En Ur y+En Ui y)) := by ring
      _ ≤ (CP*ε^2)*(CE*physicalEnergyDensity d.γ d.frame d.radius φ y) :=
        mul_le_mul_of_nonneg_left hAxis (mul_nonneg hCP (sq_nonneg ε))
      _ = _ := by ring
  have hDom := (hd.2.2.2.2.1.integrableOn_physicalEnergyDensity hY hg (zero_lt_one.trans_le hK)
    d.frame he hFrame hf hφ).const_mul (CP*CE*ε^2)
  have hIntegral := norm_integral_le_of_norm_le hDom hBound
  have hIdentity : (∫ y in Y,F Ur y+F Ui y)=∫ y in Y,R Ur y+R Ui y := by
    rw [integral_add hr.1 hi.1,integral_add hr.2.1 hi.2.1,hr.2.2,hi.2.2]
  refine ⟨hr.1.add hi.1,?_⟩
  change |∫ y in Y,F Ur y+F Ui y| ≤ _
  rw [hIdentity]
  simpa only [Real.norm_eq_abs,integral_const_mul,←energySq_eq_integral_density,mul_assoc] using hIntegral

end ShrinkingSpheres.ParallelEnergy
