import Proof.ParallelScalarFirstMassWeights
import Proof.ParallelScalarFirstMassPoint
import Proof.ParallelScalarFirstCanonicalEnergy
import Proof.ParallelScalarFirstHighSections

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Every actual scalar-second/mass contraction has the original uniform
energy bound once its SAME smooth coefficient has the genuine strong jet.
The coefficient, high graph and constants all precede the test section. -/
theorem uniform_scalar_first_mass_contraction_bound {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 2 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K)
    (Q : ℝ) (hQ : 0 ≤ Q) :
    ∃ C0 : ℝ,0 ≤ C0 ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ 1 → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      ∀ C : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
      ∀ Ch : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
      ContDiffOn ℝ ∞ C Y →
      (∀ y ∈ Y,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (Ch y)=
        (C y).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) →
      (∀ y ∈ Y,‖C y‖ ≤ Q*ε) →
      (∀ y ∈ Y,∀ i : I,∃ L : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
        halfOperatorCovariantDerivativeL d C Ch y (axis i)=
          L.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) ∧
        ‖L‖ ≤ Q*ε*beta d.γ d.radius y) →
      ∀ t : Fin 2,∀ a b k : I,∀ φ : Field,∀ E : HarmonicTestExpansion Y d.γ d.frame φ,
      ∀ D : AngularModelData E d.radius,Test Y d.γ d.frame φ →
        let q := scalarFirstMassWeight d t a b k
        let Ur := E.realHigherSobolevSection (5/2:ℝ) (by norm_num)
        let Ui := E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)
        let U3 := fun U x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)
        let T := fun y => halfCovariantSecondMassDensity d q C (U3 Ur)
          (fiveHalfCovariantDerivative d Ur (axis b)) (axis a) y+
          halfCovariantSecondMassDensity d q C (U3 Ui)
          (fiveHalfCovariantDerivative d Ui (axis b)) (axis a) y
        IntegrableOn T Y ∧ |∫ y in Y,T y| ≤ C0*ε^2*energySq Y d.γ d.frame d.radius φ := by
  obtain ⟨A,hA,hWeight⟩ := uniform_scalar_first_mass_weight_jets hY hΩ hSub hm K ρ c₀ M Cj hK
  let CE := 3*(3*K^2+1)
  let CQ := 6*A*Q
  have hCQ : 0 ≤ CQ := by dsimp only [CQ];positivity
  refine ⟨CQ*CE,by dsimp only [CE];positivity,?_⟩
  intro floor hf ε hε hε1 d hd C Ch hC hCh hCN hCD t a b k φ E D hφ
  let q := scalarFirstMassWeight d t a b k
  let U3 := fun (U : X → SphereSobolev (5/2:ℝ)) x =>
    sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)
  let H := fun U => fiveHalfCovariantDerivative d U
  let Ur := E.realHigherSobolevSection (5/2:ℝ) (by norm_num)
  let Ui := E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)
  let T := fun U => halfCovariantSecondMassDensity d q C (U3 U) (H U (axis b)) (axis a)
  let Rem := fun U => halfCovariantSecondMassRemainder d q C Ch (U3 U) (H U (axis b)) (axis a)
  let En := fun (U : X → SphereSobolev (5/2:ℝ)) (y : X) =>
    ∑ i : I,halfCovariantDirectionEnergy d (U3 U) y (beta d.γ d.radius y) (axis i)
  have hg : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have he (i : I) : ContDiffOn ℝ ∞ (fun x => d.frame x i) Y := (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hFrame : ∀ x ∈ Y,∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j)=if i=j then 1 else 0 :=
    fun x hx => hd.1.2.2.2.2.2.2.2 x (hSub hx)
  have hW := hWeight floor hf ε hε hε1 d hd t a b k
  have hPer (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U)
      (hU0 : ∀ x ∉ E.supportSet,U x=0) :
      IntegrableOn (T U) Y ∧ IntegrableOn (Rem U) Y ∧ (∫ y in Y,T U y)=∫ y in Y,Rem U y := by
    have hUS : ContDiff ℝ ∞ (U3 U) :=
      (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)).contDiff.comp hU
    have hU30 (x : X) (hx : x ∉ E.supportSet) : U3 U x=0 := by dsimp only [U3];rw [hU0 x hx,map_zero]
    have hHS := contDiff_supported_gradedSphereSectionCovariantDerivative hY (5/2:ℝ) d hg
      (zero_lt_one.trans_le hK) he U hU E.supportSet E.compactSupportSet.isClosed E.supportSubset hU0 (axis b)
    exact half_covariant_second_mass_reduction hY d hg (zero_lt_one.trans_le hK) he q hW.1 C Ch hC hCh
      (U3 U) (H U (axis b)) hUS hHS.1 E.supportSet E.compactSupportSet E.supportSubset hU30 hHS.2 (axis a)
  have hr := hPer Ur (E.contDiff_realHigherSobolevSection _ _)
    (fun x hx => E.realHigherSobolevSection_zero _ _ (by norm_num) hx)
  have hi := hPer Ui (E.contDiff_imagHigherSobolevSection _ _)
    (fun x hx => E.imagHigherSobolevSection_zero _ _ (by norm_num) hx)
  have hPoint (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U) (y : X) (hy : y ∈ Y) :
      |Rem U y| ≤ CQ*ε^2*metricDensity d.γ y*En U y := by
    let β := beta d.γ d.radius y
    have hβ : 1 ≤ β := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
    have hDir0 (i : I) : 0 ≤ halfCovariantDirectionEnergy d (U3 U) y β (axis i) := by
      dsimp only [halfCovariantDirectionEnergy]
      positivity
    have hSingle (i : I) := Finset.single_le_sum (f:=fun i : I => halfCovariantDirectionEnergy d (U3 U) y β (axis i))
      (fun i _ => hDir0 i) (Finset.mem_univ i)
    have hGrad (i : I) : β⁻¹*‖halfSectionCovariantDerivativeL d (U3 U) y (axis i)‖^2 ≤ En U y :=
      (le_add_of_nonneg_right (by positivity : 0 ≤ β*‖U3 U y‖^2)).trans (hSingle i)
    have hV : β⁻¹*‖sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (H U (axis b) y)‖^2 ≤ En U y := by
      rw [fiveHalfCovariantDerivative_half_inclusion d U y (axis b) (hU.differentiable (by simp) y)]
      exact hGrad b
    have hMass : β*‖U3 U y‖^2 ≤ En U y :=
      (le_add_of_nonneg_left (by positivity : 0 ≤ β⁻¹*‖halfSectionCovariantDerivativeL d (U3 U) y (axis 0)‖^2)).trans (hSingle 0)
    obtain ⟨L,hL,hLN⟩ := hCD y hy a
    have hDC : ‖halfOperatorCovariantDerivativeL d C Ch y (axis a) (H U (axis b) y)‖ ≤
        Q*ε*β*‖sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (H U (axis b) y)‖ := by
      rw [hL,ContinuousLinearMap.comp_apply]
      exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_right hLN (norm_nonneg _))
    exact halfCovariantSecondMassRemainder_bound d q C Ch (U3 U) (H U (axis b)) y (axis a)
      A Q ε β _ (En U y) hA hQ hε hβ (Real.sqrt_nonneg _) ((hW.2 y hy a).1)
      ((hW.2 y hy a).2) (hCN y hy) hDC (hGrad a) hV hMass
  have hUR : U3 Ur=E.realSobolevSection (3/2:ℝ) (by norm_num) :=
    funext (E.realHigherSobolevSection_inclusion _ _ _ (by norm_num) (by norm_num))
  have hUI : U3 Ui=E.imagSobolevSection (3/2:ℝ) (by norm_num) :=
    funext (E.imagHigherSobolevSection_inclusion _ _ _ (by norm_num) (by norm_num))
  have hBound : ∀ᵐ y ∂volume.restrict Y,‖Rem Ur y+Rem Ui y‖ ≤
      (CQ*CE*ε^2)*physicalEnergyDensity d.γ d.frame d.radius φ y := by
    filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
    rw [Real.norm_eq_abs]
    have hR := hPoint Ur (E.contDiff_realHigherSobolevSection _ _) y hy
    have hI := hPoint Ui (E.contDiff_imagHigherSobolevSection _ _) y hy
    have hEnergy := half_covariant_axis_energy_le D hY hg hK he hFrame hφ.1 hy
    have hAxis : metricDensity d.γ y*(En Ur y+En Ui y) ≤ CE*physicalEnergyDensity d.γ d.frame d.radius φ y := by
      simpa only [En,hUR,hUI,CE] using hEnergy
    calc
      _ ≤ |Rem Ur y|+|Rem Ui y| := abs_add_le _ _
      _ ≤ CQ*ε^2*metricDensity d.γ y*En Ur y+CQ*ε^2*metricDensity d.γ y*En Ui y := add_le_add hR hI
      _ = (CQ*ε^2)*(metricDensity d.γ y*(En Ur y+En Ui y)) := by ring
      _ ≤ (CQ*ε^2)*(CE*physicalEnergyDensity d.γ d.frame d.radius φ y) :=
        mul_le_mul_of_nonneg_left hAxis (mul_nonneg hCQ (sq_nonneg ε))
      _ = _ := by ring
  have hDom := (hd.2.2.2.2.1.integrableOn_physicalEnergyDensity hY hg (zero_lt_one.trans_le hK)
    d.frame he hFrame hf hφ).const_mul (CQ*CE*ε^2)
  have hIntegral := norm_integral_le_of_norm_le hDom hBound
  have hIdentity : (∫ y in Y,T Ur y+T Ui y)=(∫ y in Y,Rem Ur y+Rem Ui y) := by
    rw [integral_add hr.1 hi.1,integral_add hr.2.1 hi.2.1,hr.2.2,hi.2.2]
  refine ⟨hr.1.add hi.1,?_⟩
  rw [hIdentity]
  simpa only [Real.norm_eq_abs,integral_const_mul,←energySq_eq_integral_density] using hIntegral

end ShrinkingSpheres.ParallelEnergy
