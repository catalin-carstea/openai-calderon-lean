import Proof.ScalarCovariantAdjointDefect
import Proof.CanonicalCoarseTripleEnergy
import Proof.PrincipalAdjointWeights

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.ActualScalarPrincipalAdjoint

def scalarAdjointDefectSquareDensity {Y : Set X} (d : Data) {φ : Field}
    (E : HarmonicTestExpansion Y d.γ d.frame φ) (y : X) : ℝ :=
  metricDensity d.γ y*(
    ‖scalarCovariantAdjointDefectSection d (metricDensity d.γ) (scalarPrincipalMatrix d.γ d.g₂ d.radius)
      (E.realSobolevSection 2 (by norm_num)) y‖^2+
    ‖scalarCovariantAdjointDefectSection d (metricDensity d.γ) (scalarPrincipalMatrix d.γ d.g₂ d.radius)
      (E.imagSobolevSection 2 (by norm_num)) y‖^2)

theorem uniform_physical_scalar_adjoint_defect_square_point_bound {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 2 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ 1 → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ φ : Field,
      ∀ E : HarmonicTestExpansion Y d.γ d.frame φ,∀ D : AngularModelData E d.radius,
      Test Y d.γ d.frame φ → ∀ y ∈ Y,
      scalarAdjointDefectSquareDensity d E y ≤
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
  let Ur := E.realSobolevSection 2 (by norm_num)
  let Ui := E.imagSobolevSection 2 (by norm_num)
  have hKpos := zero_lt_one.trans_le hK
  have hg : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have hg2 : Elliptic Y K d.g₂ :=
    ⟨fun i j => (hd.1.2.2.1.1 i j).mono hSub,fun x hx => hd.1.2.2.1.2 x (hSub hx)⟩
  have he (i : I) : ContDiffOn ℝ ∞ (fun x => d.frame x i) Y := (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hFrame : ∀ x ∈ Y,∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j)=if i=j then 1 else 0 :=
    fun x hx => hd.1.2.2.2.2.2.2.2 x (hSub hx)
  have hD (u v : I) : ‖fderiv ℝ (fun x => d.γ x u v) y‖ ≤ M1 :=
    (hd.1.reference_fderiv_bound (by omega) (hSub hy) u v).trans (le_abs_self _)
  have hD2 (u v : I) : ‖fderiv ℝ (fderiv ℝ (fun x => d.γ x u v)) y‖ ≤ M2 :=
    (hd.1.reference_second_fderiv_bound hm (hSub hy) u v).trans (le_abs_self _)
  have hWeights := scalar_principal_adjoint_coefficient_weights hY hg hg2 hK d.frame hFrame
    hd.2.2.2.2.1 hf hε hε1 hd.2.2.2.2.2 hy M1 M2 (abs_nonneg _) (abs_nonneg _) hD hD2
  have hβ : 1 ≤ β := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  have hμ : 0 ≤ μ := Real.sqrt_nonneg _
  have hb (i : I) : |adjointFirstCoefficient axis (metricDensity d.γ) A y i| ≤ B*ε/β :=
    (hWeights.1 i).trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self _) hε) (zero_lt_one.trans_le hβ).le)
  have hc : |adjointZeroCoefficient axis (metricDensity d.γ) A y| ≤ Z*ε :=
    hWeights.2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hε)
  have hPer (U : X → SphereSobolev 2) :
      ‖scalarCovariantAdjointDefectSection d (metricDensity d.γ) A U y‖^2 ≤
      CP*ε^2*coarseCovariantTripleEnergy d U y β (axis 0) (axis 1) (axis 2) := by
    have hh := scalar_first_zero_packet_norm_sq_bound
      (sphereSobolevInclusionL 1 0 (by norm_num)) (norm_sphereSobolevInclusionL_le 1 0 (by norm_num))
      (sphereSobolevInclusionL 2 1 (by norm_num) (U y))
      (fun i => sphereSobolevInclusionL 1 0 (by norm_num) (highSectionCovariantDerivative d U y (axis i)))
      (fun i => adjointFirstCoefficient axis (metricDensity d.γ) A y i)
      (adjointZeroCoefficient axis (metricDensity d.γ) A y) B Z ε β
      (abs_nonneg _) (abs_nonneg _) hε hβ hb hc
    simpa only [scalarCovariantAdjointDefectSection,coarseCovariantTripleEnergy,Fin.sum_univ_three,CP]
      using hh
  have hR := hPer Ur
  have hI := hPer Ui
  have hEnergy := D.coarse_covariant_triple_energy_le hY hg hK he hFrame hφ.1 hy 0 1 2
  change μ*(_+_) ≤ _
  calc
    _ ≤ μ*(CP*ε^2*coarseCovariantTripleEnergy d Ur y β (axis 0) (axis 1) (axis 2)+
        CP*ε^2*coarseCovariantTripleEnergy d Ui y β (axis 0) (axis 1) (axis 2)) :=
      mul_le_mul_of_nonneg_left (add_le_add hR hI) hμ
    _ = (CP*ε^2)*(μ*(coarseCovariantTripleEnergy d Ur y β (axis 0) (axis 1) (axis 2)+
        coarseCovariantTripleEnergy d Ui y β (axis 0) (axis 1) (axis 2))) := by ring
    _ ≤ (CP*ε^2)*(CE*physicalEnergyDensity d.γ d.frame d.radius φ y) :=
      mul_le_mul_of_nonneg_left hEnergy (mul_nonneg hCP (sq_nonneg ε))
    _ = _ := by ring

end ShrinkingSpheres
