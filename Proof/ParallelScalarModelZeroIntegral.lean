import Proof.ParallelScalarModelZeroGreen
import Proof.ParallelScalarModelZeroPoint
import Proof.ParallelScalarFirstCanonicalEnergy
import Proof.UniformActualHalfCovariantFirstForm

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.DirichletFamily

def scalarModelDegreePairDensity (d : Data) (q : I → I → X → ℝ) (c : I)
    (U : X → SphereSobolev (5/2:ℝ)) : X → ℝ :=
  pairedHalfMassDensity d q (fun x => (framedRaisingHalfL d x (axis c)).adjoint)
    (fun x => framedRaisingHalfL d x (axis c))
    (scalarModelDegreeSection U) (scalarModelShiftedDegreeSection U)
    (fun b : I => fiveHalfCovariantDerivative d U (axis b))

/-- A complete symmetric scalar-weighted degree pair, including real
and imaginary sections, has an original-energy linear-epsilon bound. -/
theorem uniform_scalar_model_degree_pair_integral_bound {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ}
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K)
    (RB : ScalarModelRaisingBudget Y Ω m K ρ c₀ M Cj)
    (Z0 Z1 : ℝ) (hZ0 : 0 ≤ Z0) (hZ1 : 0 ≤ Z1) :
    ∃ C0 : ℝ,0 ≤ C0 ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      ∀ A : I → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
      (∀ j : I,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (A j)=
        (flatHalfRaisingL j).adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) →
      ∀ q : I → I → X → ℝ,(∀ a b,ContDiffOn ℝ ∞ (q a b) Y) →
      (∀ y ∈ Y,∀ a b,q a b y=q b a y) →
      (∀ a b,∀ y ∈ Y,∀ i : I,
        |q a b y| ≤ Z0*ε/beta d.γ d.radius y*metricDensity d.γ y ∧
        |fderiv ℝ (q a b) y (axis i)| ≤ Z1*ε*metricDensity d.γ y) →
      ∀ c : I,∀ φ : Field,∀ E : HarmonicTestExpansion Y d.γ d.frame φ,
      ∀ D : AngularModelData E d.radius,Test Y d.γ d.frame φ →
        let T := fun y => scalarModelDegreePairDensity d q c (E.realHigherSobolevSection (5/2:ℝ) (by norm_num)) y+
          scalarModelDegreePairDensity d q c (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)) y
        IntegrableOn T Y ∧ |∫ y in Y,T y| ≤ C0*ε*energySq Y d.γ d.frame d.radius φ := by
  let CP := 108*RB.bound*(Z0+Z1)
  let CE := 3*(3*K^2+1)
  have hCP : 0 ≤ CP := by dsimp only [CP];exact mul_nonneg (mul_nonneg (by norm_num) RB.nonneg) (add_nonneg hZ0 hZ1)
  refine ⟨CP*CE,by dsimp only [CE];positivity,?_⟩
  intro floor hf ε hε d hd A hA q hq hSym hWeights c φ E D hφ
  let Ur := E.realHigherSobolevSection (5/2:ℝ) (by norm_num)
  let Ui := E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)
  let C0 := fun x => (framedRaisingHalfL d x (axis c)).adjoint
  let C1 := fun x => framedRaisingHalfL d x (axis c)
  let Ch0 := scalarModelRaisingAdjointHigher A d c
  let Ch1 := fun x => framedRaisingHigherL d x (axis c)
  let T := fun U => scalarModelDegreePairDensity d q c U
  let Rem := fun U => pairedHalfMassRemainder d q C0 C1 Ch0 Ch1 (scalarModelDegreeSection U)
    (scalarModelShiftedDegreeSection U) (fun b : I => fiveHalfCovariantDerivative d U (axis b))
  let En := fun (U : X → SphereSobolev (5/2:ℝ)) (y : X) => ∑ b : I,halfCovariantDirectionEnergy d
    (fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)) y (beta d.γ d.radius y) (axis b)
  have hg : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have he (i : I) : ContDiffOn ℝ ∞ (fun x => d.frame x i) Y := (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hFrame : ∀ x ∈ Y,∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j)=if i=j then 1 else 0 :=
    fun x hx => hd.1.2.2.2.2.2.2.2 x (hSub hx)
  obtain ⟨Q,hQ⟩ := exists_unit_boundary_coefficient
  have hPer (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U) (hU0 : ∀ x ∉ E.supportSet,U x=0) :=
    scalar_model_degree_pair_reduction hY hd hg (zero_lt_one.trans_le hK) he Q hQ A hA q hq hSym c
      U hU E.supportSet E.compactSupportSet E.supportSubset hU0
  have hr := hPer Ur (E.contDiff_realHigherSobolevSection _ _)
    (fun x hx => E.realHigherSobolevSection_zero _ _ (by norm_num) hx)
  have hi := hPer Ui (E.contDiff_imagHigherSobolevSection _ _)
    (fun x hx => E.imagHigherSobolevSection_zero _ _ (by norm_num) hx)
  change IntegrableOn (T Ur) Y ∧ IntegrableOn (Rem Ur) Y ∧
    (∫ y in Y,T Ur y)=∫ y in Y,Rem Ur y at hr
  change IntegrableOn (T Ui) Y ∧ IntegrableOn (Rem Ui) Y ∧
    (∫ y in Y,T Ui y)=∫ y in Y,Rem Ui y at hi
  have hPoint (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U) (y : X) (hy : y ∈ Y) :
      |Rem U y| ≤ CP*ε*metricDensity d.γ y*En U y :=
    scalar_model_degree_remainder_bound hY hΩ hd (zero_lt_one.trans_le hK) hf hε RB A hA q Z0 Z1 hZ0 hZ1 hy c
      (fun a b => (hWeights a b y hy 0).1) (fun a b => (hWeights a b y hy a).2)
      U (hU.differentiable (by simp) y)
  have hUR : (fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (Ur x))=
      E.realSobolevSection (3/2:ℝ) (by norm_num) :=
    funext (E.realHigherSobolevSection_inclusion _ _ _ (by norm_num) (by norm_num))
  have hUI : (fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (Ui x))=
      E.imagSobolevSection (3/2:ℝ) (by norm_num) :=
    funext (E.imagHigherSobolevSection_inclusion _ _ _ (by norm_num) (by norm_num))
  have hBound : ∀ᵐ y ∂volume.restrict Y,‖Rem Ur y+Rem Ui y‖ ≤ (CP*CE*ε)*physicalEnergyDensity d.γ d.frame d.radius φ y := by
    filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
    rw [Real.norm_eq_abs]
    have hR := hPoint Ur (E.contDiff_realHigherSobolevSection _ _) y hy
    have hI := hPoint Ui (E.contDiff_imagHigherSobolevSection _ _) y hy
    have hEnergy := half_covariant_axis_energy_le D hY hg hK he hFrame hφ.1 hy
    have hAxis : metricDensity d.γ y*(En Ur y+En Ui y) ≤ CE*physicalEnergyDensity d.γ d.frame d.radius φ y := by
      simpa only [En,hUR,hUI,CE] using hEnergy
    calc
      _ ≤ |Rem Ur y|+|Rem Ui y| := abs_add_le _ _
      _ ≤ CP*ε*metricDensity d.γ y*En Ur y+CP*ε*metricDensity d.γ y*En Ui y := add_le_add hR hI
      _ = (CP*ε)*(metricDensity d.γ y*(En Ur y+En Ui y)) := by ring
      _ ≤ (CP*ε)*(CE*physicalEnergyDensity d.γ d.frame d.radius φ y) :=
        mul_le_mul_of_nonneg_left hAxis (mul_nonneg hCP hε)
      _ = _ := by ring
  have hDom := (hd.2.2.2.2.1.integrableOn_physicalEnergyDensity hY hg (zero_lt_one.trans_le hK)
    d.frame he hFrame hf hφ).const_mul (CP*CE*ε)
  have hIntegral := norm_integral_le_of_norm_le hDom hBound
  have hIdentity : (∫ y in Y,T Ur y+T Ui y)=(∫ y in Y,Rem Ur y+Rem Ui y) := by
    rw [integral_add hr.1 hi.1,integral_add hr.2.1 hi.2.1,hr.2.2,hi.2.2]
  refine ⟨hr.1.add hi.1,?_⟩
  rw [hIdentity]
  simpa only [Real.norm_eq_abs,integral_const_mul,←energySq_eq_integral_density] using hIntegral

end ShrinkingSpheres.ParallelEnergy
