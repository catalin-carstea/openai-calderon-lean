import Proof.CanonicalScalarModelDefectSecondPoint
import Proof.ScalarPrincipalSharpTwoJets
import Proof.PrincipalDensityProductJets
import Proof.ConstantBoundaryCoefficients

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

def scalarPrincipalDensityWeight (g g₂ : MetricField) (r : X → ℝ) (i j : I) (x : X) : ℝ :=
  metricDensity g x*scalarPrincipalMatrix g g₂ r x i j

def scalarModelDefectSecondRemainderDensity {Y : Set X} (d : Data) {φ : Field}
    (E : HarmonicTestExpansion Y d.γ d.frame φ) (q : X → ℝ) (a b : I) (y : X) : ℝ :=
  scalarModelDefectSecondRemainder d q (E.realSobolevSection 2 (by norm_num)) (axis a) (axis b) y+
    scalarModelDefectSecondRemainder d q (E.imagSobolevSection 2 (by norm_num)) (axis a) (axis b) y

theorem uniform_physical_scalar_model_defect_second_remainder_point_bound {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 2 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ 1 → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ φ : Field,
      ∀ E : HarmonicTestExpansion Y d.γ d.frame φ,∀ D : AngularModelData E d.radius,
      Test Y d.γ d.frame φ → ∀ i j a b : I,∀ y ∈ Y,
      |scalarModelDefectSecondRemainderDensity d E (scalarPrincipalDensityWeight d.γ d.g₂ d.radius i j) a b y| ≤
        C*ε*physicalEnergyDensity d.γ d.frame d.radius φ y := by
  let M1 := |M ⟨1,by omega⟩|
  let M2 := |M ⟨2,by omega⟩|
  let A := principalZeroBudget K
  let A1 := principalDensityProductFirstBudget K M1
  let CP := scalarModelDefectSecondBudget K (Cj 2) A A1
  let CE := 2*(3*K^2+1)
  have hK0 := zero_le_one.trans hK
  have hA : 0 ≤ A := by dsimp only [A,principalZeroBudget];positivity
  have hA1 : 0 ≤ A1 := by
    dsimp only [A1,principalDensityProductFirstBudget,densityFirstBudget,principalZeroBudget,principalFirstBudget]
    positivity
  have hCP : 0 ≤ CP := scalarModelDefectSecondBudget_nonneg K (Cj 2) A A1 hK0 hA hA1
  have hCE : 0 ≤ CE := by dsimp only [CE];positivity
  obtain ⟨Q,hQ⟩ := exists_unit_boundary_coefficient
  refine ⟨CP*CE,mul_nonneg hCP hCE,?_⟩
  intro floor hf ε hε hε1 d hd φ E D hφ i j a b y hy
  let q := scalarPrincipalDensityWeight d.γ d.g₂ d.radius i j
  let β := beta d.γ d.radius y
  let μ := metricDensity d.γ y
  let Ur := E.realSobolevSection 2 (by norm_num)
  let Ui := E.imagSobolevSection 2 (by norm_num)
  let Hr := E.realSobolevSection (3/2:ℝ) (by norm_num)
  let Hi := E.imagSobolevSection (3/2:ℝ) (by norm_num)
  let Er := fun k => halfCovariantDirectionEnergy d Hr y β (axis k)
  let Ei := fun k => halfCovariantDirectionEnergy d Hi y β (axis k)
  have hKpos := zero_lt_one.trans_le hK
  have hg : Elliptic Y K d.γ :=
    ⟨fun u v => (hd.1.1.1 u v).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have hg2 : Elliptic Y K d.g₂ :=
    ⟨fun u v => (hd.1.2.2.1.1 u v).mono hSub,fun x hx => hd.1.2.2.1.2 x (hSub hx)⟩
  have he (k : I) : ContDiffOn ℝ ∞ (fun x => d.frame x k) Y := (hd.1.2.2.2.2.2.2.1 k).mono hSub
  have hFrame : ∀ x ∈ Y,∀ u v,metricPair d.γ x (d.frame x u) (d.frame x v)=if u=v then 1 else 0 :=
    fun x hx => hd.1.2.2.2.2.2.2.2 x (hSub hx)
  have hD (u v : I) : ‖fderiv ℝ (fun x => d.γ x u v) y‖ ≤ M1 :=
    (hd.1.reference_fderiv_bound (by omega) (hSub hy) u v).trans (le_abs_self _)
  have hD2 (u v : I) : ‖fderiv ℝ (fderiv ℝ (fun x => d.γ x u v)) y‖ ≤ M2 :=
    (hd.1.reference_second_fderiv_bound hm (hSub hy) u v).trans (le_abs_self _)
  have hμ : 0 ≤ μ := Real.sqrt_nonneg _
  have hScalar : |scalarPrincipalMatrix d.γ d.g₂ d.radius y i j| ≤ A*ε/β^2 :=
    (scalar_principal_sharp_two_jet_weights hY hg hg2 hK d.frame hFrame hd.2.2.2.2.1 hf hε hε1
      hd.2.2.2.2.2 hy M1 M2 (abs_nonneg _) (abs_nonneg _) hD hD2 i j a b).1
  have hq : |q y| ≤ μ*A*ε/β^2 := by
    change |μ*scalarPrincipalMatrix d.γ d.g₂ d.radius y i j| ≤ _
    rw [abs_mul,abs_of_nonneg hμ]
    exact (mul_le_mul_of_nonneg_left hScalar hμ).trans_eq (by ring)
  have hdq : |fderiv ℝ q y (axis a)| ≤ μ*A1*ε/β :=
    (scalar_principal_density_product_two_jets hY hg hg2 hK d.frame hFrame hd.2.2.2.2.1 hf hε hε1
      hd.2.2.2.2.2 hy M1 M2 (abs_nonneg _) (abs_nonneg _) hD hD2 i j a a).1
  have hR := canonical_scalar_model_defect_second_remainder_bound hY d hg hK hd.2.2.2.2.1 hf Q hQ
    (fun p => (E.representative p).re) (Complex.reCLM.contDiff.comp E.representativeSmooth) q
    μ A A1 ε hμ hA hA1 hε hy (hFrame y hy) a b hq hdq
  have hI := canonical_scalar_model_defect_second_remainder_bound hY d hg hK hd.2.2.2.2.1 hf Q hQ
    (fun p => (E.representative p).im) (Complex.imCLM.contDiff.comp E.representativeSmooth) q
    μ A A1 ε hμ hA hA1 hε hy (hFrame y hy) a b hq hdq
  have hEa : μ*(Er a+Ei a) ≤ (3*K^2+1)*physicalEnergyDensity d.γ d.frame d.radius φ y :=
    D.half_covariant_direction_energy_le hY hg hK he hFrame hφ.1 hy a
  have hEb : μ*(Er b+Ei b) ≤ (3*K^2+1)*physicalEnergyDensity d.γ d.frame d.radius φ y :=
    D.half_covariant_direction_energy_le hY hg hK he hFrame hφ.1 hy b
  have hEnergy : μ*((Er a+Er b)+(Ei a+Ei b)) ≤ CE*physicalEnergyDensity d.γ d.frame d.radius φ y := by
    dsimp only [CE]
    linarith only [hEa,hEb]
  change |scalarModelDefectSecondRemainder d q Ur (axis a) (axis b) y+
    scalarModelDefectSecondRemainder d q Ui (axis a) (axis b) y| ≤ _
  calc
    _ ≤ CP*μ*ε*(Er a+Er b)+CP*μ*ε*(Ei a+Ei b) := (abs_add_le _ _).trans (add_le_add hR hI)
    _ = (CP*ε)*(μ*((Er a+Er b)+(Ei a+Ei b))) := by ring
    _ ≤ (CP*ε)*(CE*physicalEnergyDensity d.γ d.frame d.radius φ y) :=
      mul_le_mul_of_nonneg_left hEnergy (mul_nonneg hCP hε)
    _ = _ := by ring

end ShrinkingSpheres
