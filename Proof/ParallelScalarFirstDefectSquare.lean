import Proof.ParallelScalarFirstHighSections
import Proof.PhysicalScalarAdjointDefectPoint
import Proof.ParallelScalarFirstCanonicalEnergy

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.ActualScalarPrincipalAdjoint

def scalarFiveHalfDefectSquareDensity {Y : Set X} (d : Data) {φ : Field}
    (E : HarmonicTestExpansion Y d.γ d.frame φ) (y : X) : ℝ :=
  metricDensity d.γ y*(
    ‖scalarFiveHalfDefectSection d (metricDensity d.γ) (scalarPrincipalMatrix d.γ d.g₂ d.radius)
      (E.realHigherSobolevSection (5/2:ℝ) (by norm_num)) y‖^2+
    ‖scalarFiveHalfDefectSection d (metricDensity d.γ) (scalarPrincipalMatrix d.γ d.g₂ d.radius)
      (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)) y‖^2)

/-- The scalar adjoint defect has the genuine H1/2 norm needed to pair
against the weak H-1/2 first adjoint. Only the original scalar coefficient
weights and actual covariant half-direction energy are used. -/
theorem uniform_scalar_fiveHalf_defect_square_point_bound {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 2 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ 1 → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ φ : Field,
      ∀ E : HarmonicTestExpansion Y d.γ d.frame φ,∀ D : AngularModelData E d.radius,
      Test Y d.γ d.frame φ → ∀ y ∈ Y,
      scalarFiveHalfDefectSquareDensity d E y ≤
        C*ε^2*physicalEnergyDensity d.γ d.frame d.radius φ y := by
  let M1 := |M ⟨1,by omega⟩|
  let M2 := |M ⟨2,by omega⟩|
  let B := |principalAdjointFirstBudget K M1|
  let Z := |principalAdjointZeroBudget K M1 M2 (Cj 2)|
  let CP := 6*B^2+2*Z^2
  let CE := 3*(3*K^2+1)
  have hCP : 0 ≤ CP := by dsimp only [CP];positivity
  have hCE : 0 ≤ CE := by dsimp only [CE];positivity
  refine ⟨CP*CE,mul_nonneg hCP hCE,?_⟩
  intro floor hf ε hε hε1 d hd φ E D hφ y hy
  let β := beta d.γ d.radius y
  let μ := metricDensity d.γ y
  let A := scalarPrincipalMatrix d.γ d.g₂ d.radius
  let Ur := E.realHigherSobolevSection (5/2:ℝ) (by norm_num)
  let Ui := E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)
  let Rr := E.realSobolevSection (3/2:ℝ) (by norm_num)
  let Ri := E.imagSobolevSection (3/2:ℝ) (by norm_num)
  have hKpos := zero_lt_one.trans_le hK
  have hg : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have hg2 : Elliptic Y K d.g₂ :=
    ⟨fun i j => (hd.1.2.2.1.1 i j).mono hSub,fun x hx => hd.1.2.2.1.2 x (hSub hx)⟩
  have he (i : I) : ContDiffOn ℝ ∞ (fun x => d.frame x i) Y := (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hFrame : ∀ x ∈ Y,∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j)=if i=j then 1 else 0 :=
    fun x hx => hd.1.2.2.2.2.2.2.2 x (hSub hx)
  have hWeights := scalar_principal_adjoint_coefficient_weights hY hg hg2 hK d.frame hFrame
    hd.2.2.2.2.1 hf hε hε1 hd.2.2.2.2.2 hy M1 M2 (abs_nonneg _) (abs_nonneg _)
    (fun i j => (hd.1.reference_fderiv_bound (by omega) (hSub hy) i j).trans (le_abs_self _))
    (fun i j => (hd.1.reference_second_fderiv_bound hm (hSub hy) i j).trans (le_abs_self _))
  have hβ : 1 ≤ β := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  have hμ : 0 ≤ μ := Real.sqrt_nonneg _
  have hb (i : I) : |adjointFirstCoefficient axis (metricDensity d.γ) A y i| ≤ B*ε/β :=
    (hWeights.1 i).trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self _) hε) (zero_lt_one.trans_le hβ).le)
  have hc : |adjointZeroCoefficient axis (metricDensity d.γ) A y| ≤ Z*ε :=
    hWeights.2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hε)
  have hPer (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U) :
      ‖scalarFiveHalfDefectSection d (metricDensity d.γ) A U y‖^2 ≤
        CP*ε^2*(∑ i : I,halfCovariantDirectionEnergy d
          (fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)) y β (axis i)) := by
    let U3 := fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)
    let V := fun i => halfSectionCovariantDerivativeL d U3 y (axis i)
    have hRep : scalarFiveHalfDefectSection d (metricDensity d.γ) A U y=
        adjointZeroCoefficient axis (metricDensity d.γ) A y •
          sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (U3 y)+
        ∑ i : I,adjointFirstCoefficient axis (metricDensity d.γ) A y i • V i := by
      simp only [scalarFiveHalfDefectSection,V,U3,sphereSobolevInclusionL_trans_apply,
        fiveHalfCovariantDerivative_half_inclusion d U y _ (hU.differentiable (by simp) y)]
    have hRaw := scalar_first_zero_packet_norm_sq_bound
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
      (norm_sphereSobolevInclusionL_le _ _ _) (U3 y) V
      (fun i => adjointFirstCoefficient axis (metricDensity d.γ) A y i)
      (adjointZeroCoefficient axis (metricDensity d.γ) A y) B Z ε β
      (abs_nonneg _) (abs_nonneg _) hε hβ hb hc
    rw [hRep]
    apply hRaw.trans
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hCP (sq_nonneg ε))
    have hMass : 0 ≤ β*‖U3 y‖^2 := mul_nonneg (zero_le_one.trans hβ) (sq_nonneg _)
    simp only [halfCovariantDirectionEnergy,Fin.sum_univ_three,V]
    nlinarith only [hMass]
  have hUR : (fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (Ur x))=Rr :=
    funext (E.realHigherSobolevSection_inclusion _ _ _ (by norm_num) (by norm_num))
  have hUI : (fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (Ui x))=Ri :=
    funext (E.imagHigherSobolevSection_inclusion _ _ _ (by norm_num) (by norm_num))
  have hR := hPer Ur (E.contDiff_realHigherSobolevSection _ _)
  have hI := hPer Ui (E.contDiff_imagHigherSobolevSection _ _)
  rw [hUR] at hR
  rw [hUI] at hI
  have hEnergy : μ*((∑ i : I,halfCovariantDirectionEnergy d Rr y β (axis i))+
      ∑ i : I,halfCovariantDirectionEnergy d Ri y β (axis i)) ≤ CE*physicalEnergyDensity d.γ d.frame d.radius φ y := by
    exact half_covariant_axis_energy_le D hY hg hK he hFrame hφ.1 hy
  change μ*(_+_) ≤ _
  calc
    _ ≤ μ*(CP*ε^2*(∑ i : I,halfCovariantDirectionEnergy d Rr y β (axis i))+
        CP*ε^2*(∑ i : I,halfCovariantDirectionEnergy d Ri y β (axis i))) :=
      mul_le_mul_of_nonneg_left (add_le_add hR hI) hμ
    _ = (CP*ε^2)*(μ*((∑ i : I,halfCovariantDirectionEnergy d Rr y β (axis i))+
        ∑ i : I,halfCovariantDirectionEnergy d Ri y β (axis i))) := by ring
    _ ≤ (CP*ε^2)*(CE*physicalEnergyDensity d.γ d.frame d.radius φ y) :=
      mul_le_mul_of_nonneg_left hEnergy (mul_nonneg hCP (sq_nonneg ε))
    _ = _ := by ring

end ShrinkingSpheres.ParallelEnergy
