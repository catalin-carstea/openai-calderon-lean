import Proof.ParallelScalarModelNormAlgebra
import Proof.ParallelScalarModelCoordinateWeak
import Proof.ParallelScalarModelHalfIdentity
import Proof.ParallelScalarModelBudgets
import Proof.ParallelScalarFirstCanonicalEnergy
import Proof.PhysicalScalarAdjointDefectPoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.ActualScalarPrincipalAdjoint

/-- The complete model-adjoint/scalar-transpose-defect pair has the
original linear epsilon energy bound. Inverse-beta gains are kept
until the mass/gradient products have been estimated. -/
theorem uniform_scalar_model_defect_pair_point_bound {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 2 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K)
    (RB : ScalarModelRaisingBudget Y Ω m K ρ c₀ M Cj) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ 1 → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ φ : Field,
      ∀ E : HarmonicTestExpansion Y d.γ d.frame φ,∀ D : AngularModelData E d.radius,
      Test Y d.γ d.frame φ → ∀ y ∈ Y,
      |scalarModelDefectPairDensity d (E.realHigherSobolevSection (5/2:ℝ) (by norm_num)) y+
        scalarModelDefectPairDensity d (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)) y| ≤
        C*ε*physicalEnergyDensity d.γ d.frame d.radius φ y := by
  let M1 := |M ⟨1,by omega⟩|
  let M2 := |M ⟨2,by omega⟩|
  let B := |principalAdjointFirstBudget K M1|
  let Z := |principalAdjointZeroBudget K M1 M2 (Cj 2)|
  let Q := 3*K*RB.bound
  let R := 27*K^2*RB.bound
  let CP := 3*B*Q+4*Z*Q+4*B*R+Z*R
  let CE := 3*(3*K^2+1)
  have hB : 0 ≤ B := abs_nonneg _
  have hZ : 0 ≤ Z := abs_nonneg _
  have hQ : 0 ≤ Q := by dsimp only [Q];exact mul_nonneg (mul_nonneg (by norm_num) (zero_le_one.trans hK)) RB.nonneg
  have hR : 0 ≤ R := by dsimp only [R];exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg K)) RB.nonneg
  have hCP : 0 ≤ CP := by dsimp only [CP];positivity
  refine ⟨CP*CE,by dsimp only [CE];positivity,?_⟩
  intro floor hf ε hε hε1 d hd φ E D hφ y hy
  let β := beta d.γ d.radius y
  let μ := metricDensity d.γ y
  let A := scalarPrincipalMatrix d.γ d.g₂ d.radius
  let Ur := E.realHigherSobolevSection (5/2:ℝ) (by norm_num)
  let Ui := E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)
  let En := fun (U : X → SphereSobolev (5/2:ℝ)) => ∑ i : I,halfCovariantDirectionEnergy d
    (fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)) y β (axis i)
  have hKp := zero_lt_one.trans_le hK
  have hβ : 1 ≤ β := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  have hβp : 0 < β := zero_lt_one.trans_le hβ
  have hμ : 0 ≤ μ := Real.sqrt_nonneg _
  have hg : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have hg2 : Elliptic Y K d.g₂ :=
    ⟨fun i j => (hd.1.2.2.1.1 i j).mono hSub,fun x hx => hd.1.2.2.1.2 x (hSub hx)⟩
  have he (i : I) : ContDiffOn ℝ ∞ (fun x => d.frame x i) Y := (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hFrame : ∀ x ∈ Y,∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j)=if i=j then 1 else 0 :=
    fun x hx => hd.1.2.2.2.2.2.2.2 x (hSub hx)
  have hWeights := scalar_principal_adjoint_coefficient_weights hY hg hg2 hK d.frame hFrame
    hd.2.2.2.2.1 hf hε hε1 hd.2.2.2.2.2 hy |M ⟨1,by omega⟩| |M ⟨2,by omega⟩| (abs_nonneg _) (abs_nonneg _)
    (fun i j => (hd.1.reference_fderiv_bound (by omega) (hSub hy) i j).trans (le_abs_self _))
    (fun i j => (hd.1.reference_second_fderiv_bound hm (hSub hy) i j).trans (le_abs_self _))
  have hb (i : I) : |adjointFirstCoefficient axis (metricDensity d.γ) A y i| ≤ B*ε/β :=
    (hWeights.1 i).trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hε) hβp.le)
  have hc : |adjointZeroCoefficient axis (metricDensity d.γ) A y| ≤ Z*ε :=
    hWeights.2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hε)
  have hPer (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U) :
      |scalarModelDefectPairDensity d U y| ≤ CP*ε*μ*En U := by
    let J := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
    let U3 := fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)
    let V := fun i : I => J (fiveHalfCovariantDerivative d U (axis i) y)
    let s := ∑ i : I,‖V i‖
    have hV (i : I) : V i=halfSectionCovariantDerivativeL d U3 y (axis i) :=
      fiveHalfCovariantDerivative_half_inclusion d U y (axis i) (hU.differentiable (by simp) y)
    have hJF : scalarFiveHalfDefectSection d (metricDensity d.γ) A U y=
        adjointZeroCoefficient axis (metricDensity d.γ) A y • J (U3 y)+
          ∑ i : I,adjointFirstCoefficient axis (metricDensity d.γ) A y i • V i := by
      simp only [scalarFiveHalfDefectSection,J,U3,V,sphereSobolevInclusionL_trans_apply]
    have hFN : ‖scalarFiveHalfDefectSection d (metricDensity d.γ) A U y‖ ≤ B*ε/β*s+Z*ε*‖U3 y‖ := by
      rw [hJF]
      exact scalar_model_defect_sum_norm_bound J (norm_sphereSobolevInclusionL_le _ _ _) (U3 y) V
        (fun i => adjointFirstCoefficient axis (metricDensity d.γ) A y i)
        (adjointZeroCoefficient axis (metricDensity d.γ) A y) B Z ε β hB hZ hε hβp hb hc
    have hJU : ‖J (U3 y)‖ ≤ ‖U3 y‖ := (J.le_opNorm _).trans
      ((mul_le_mul_of_nonneg_right (norm_sphereSobolevInclusionL_le _ _ _) (norm_nonneg _)).trans_eq (one_mul _))
    have hDU : ‖degreeHigherL (U3 y)‖ ≤ 2*‖U3 y‖ := (degreeHigherL.le_opNorm _).trans
      (mul_le_mul_of_nonneg_right norm_degreeHigherL_le_two (norm_nonneg _))
    have hShift : ‖degreeHigherL (U3 y)-J (U3 y)‖ ≤ 3*‖U3 y‖ :=
      (norm_sub_le _ _).trans ((add_le_add hDU hJU).trans_eq (by ring))
    have hM := scalar_model_adjoint_sum_norm_bound (fun k c => (d.γ y)⁻¹ k c)
      (fun k => coordDeriv k (fun x => Real.log (d.radius x)) y) (fun c => framedRaisingHalfL d y (axis c)) V
      (degreeHigherL (U3 y)-J (U3 y)) K RB.bound β ‖U3 y‖ (zero_le_one.trans hK) RB.nonneg hβp.le (norm_nonneg _)
      (fun k c => hd.1.1.inverse_entry_bound hKp (hSub hy) k c)
      (fun k => hg.coord_logRadius_bound hK d.frame d.radius hy (hFrame y hy) k)
      (fun c => (RB.actual floor ε d hd y hy 0 c).1) hShift
    have hMN : ‖scalarModelAdjointWeakSection d U y‖ ≤ Q*s+R*β*‖U3 y‖ := by
      rw [scalarModelAdjointWeakSection_coordinate d U y (hFrame y hy)]
      simpa only [U3,J,sphereSobolevInclusionL_trans_apply,Q,R,s,V] using hM
    have hGrad : β⁻¹*(∑ i : I,‖V i‖^2) ≤ En U := by
      simp only [hV,En,halfCovariantDirectionEnergy,Fin.sum_univ_three]
      nlinarith only [mul_nonneg hβp.le (sq_nonneg ‖U3 y‖)]
    have hS : s^2 ≤ 3*(∑ i : I,‖V i‖^2) := by
      simp only [s,Fin.sum_univ_three]
      nlinarith only [sq_nonneg (‖V 0‖-‖V 1‖),sq_nonneg (‖V 0‖-‖V 2‖),sq_nonneg (‖V 1‖-‖V 2‖)]
    have hGradS : β⁻¹*s^2 ≤ 3*En U := by
      have hh := mul_le_mul_of_nonneg_left hS (inv_nonneg.mpr hβp.le)
      nlinarith only [hh,hGrad]
    have hMass : β*‖U3 y‖^2 ≤ En U := by
      have hDir (i : I) : 0 ≤ halfCovariantDirectionEnergy d U3 y β (axis i) := by
        dsimp only [halfCovariantDirectionEnergy];positivity
      have hh := Finset.single_le_sum (f:=fun i : I => halfCovariantDirectionEnergy d U3 y β (axis i))
        (fun i _ => hDir i) (Finset.mem_univ 0)
      exact (le_add_of_nonneg_left (by positivity : 0 ≤ β⁻¹*‖halfSectionCovariantDerivativeL d U3 y (axis 0)‖^2)).trans hh
    have hPair := scalar_model_defect_pair_bound (scalarFiveHalfDefectSection d (metricDensity d.γ) A U y)
      (scalarModelAdjointWeakSection d U y) s ‖U3 y‖ B Z Q R ε β (En U)
      (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (norm_nonneg _) hB hZ hQ hR hε hβp hFN hMN hGradS hMass
    change |μ*_| ≤ _
    rw [abs_mul,abs_of_nonneg hμ]
    exact (mul_le_mul_of_nonneg_left hPair hμ).trans_eq (by dsimp only [CP];ring)
  have hUR : (fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (Ur x))=
      E.realSobolevSection (3/2:ℝ) (by norm_num) :=
    funext (E.realHigherSobolevSection_inclusion _ _ _ (by norm_num) (by norm_num))
  have hUI : (fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (Ui x))=
      E.imagSobolevSection (3/2:ℝ) (by norm_num) :=
    funext (E.imagHigherSobolevSection_inclusion _ _ _ (by norm_num) (by norm_num))
  have hAxis : μ*(En Ur+En Ui) ≤ CE*physicalEnergyDensity d.γ d.frame d.radius φ y := by
    simpa only [En,hUR,hUI,CE] using half_covariant_axis_energy_le D hY hg hK he hFrame hφ.1 hy
  calc
    _ ≤ |scalarModelDefectPairDensity d Ur y|+|scalarModelDefectPairDensity d Ui y| := abs_add_le _ _
    _ ≤ CP*ε*μ*En Ur+CP*ε*μ*En Ui := add_le_add
      (hPer Ur (E.contDiff_realHigherSobolevSection _ _)) (hPer Ui (E.contDiff_imagHigherSobolevSection _ _))
    _ = (CP*ε)*(μ*(En Ur+En Ui)) := by ring
    _ ≤ (CP*ε)*(CE*physicalEnergyDensity d.γ d.frame d.radius φ y) :=
      mul_le_mul_of_nonneg_left hAxis (mul_nonneg hCP hε)
    _ = _ := by ring

end ShrinkingSpheres.ParallelEnergy
