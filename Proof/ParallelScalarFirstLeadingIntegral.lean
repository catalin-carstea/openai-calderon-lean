import Proof.ParallelScalarFirstSymmetricJets
import Proof.ParallelScalarFirstRemainderPoint
import Proof.ParallelScalarFirstCanonicalEnergy
import Proof.UniformActualHalfCovariantFirstForm

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

/-- One actual contracted leading symmetric scalar/first term, including
real and imaginary components, has the original uniform energy bound.
The factor two on its integral is exactly that in the paired expansion. -/
theorem uniform_scalar_first_symmetric_third_integral_bound {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C0 : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ C0 ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ CF CT CB CS : ℝ,
      ∀ P : PhysicalPrincipalData Y d CF CT,∀ WF : PhysicalFirstCommutatorPacket P CB CS ε,
      ∀ a b k : I,∀ φ : Field,∀ E : HarmonicTestExpansion Y d.γ d.frame φ,
      ∀ D : AngularModelData E d.radius,Test Y d.γ d.frame φ →
        let w := fun x => scalarPrincipalMatrix d.γ d.g₂ d.radius x a b
        let C := scalarFirstSymmetricCoefficient P w k
        let Ur := E.realHigherSobolevSection (5/2:ℝ) (by norm_num)
        let Ui := E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)
        let T := fun y => halfCovariantThirdDensity d (metricDensity d.γ) C
          (fiveHalfCovariantDerivative d Ur) (axis a) (axis b) (axis k) y+
          halfCovariantThirdDensity d (metricDensity d.γ) C
          (fiveHalfCovariantDerivative d Ui) (axis a) (axis b) (axis k) y
        IntegrableOn T Y ∧ |2*(∫ y in Y,T y)| ≤ C0*ε^2*energySq Y d.γ d.frame d.radius φ := by
  obtain ⟨ηJ,Q,hηJ,hηJ1,hQ,hJets⟩ := uniform_scalar_first_symmetric_half_jets hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηB,hηB,hηB1,hBalanced⟩ := uniform_full_first_derivative_balanced_endpoints hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  let MD := 27*K*|M ⟨1,by omega⟩|
  let CR := 3*Real.sqrt 2*curvatureBudget K |M 0| |M ⟨1,by omega⟩| |M ⟨2,by omega⟩|
  let CE := 3*(3*K^2+1)
  let CQ := 6*Q*(MD+CR+1)
  have hMD : 0 ≤ MD := by dsimp only [MD];positivity
  have hCR : 0 ≤ CR := by
    dsimp only [CR]
    exact mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
      (curvatureBudget_nonneg K _ _ _ (zero_le_one.trans hK) (abs_nonneg _) (abs_nonneg _) (abs_nonneg _))
  have hCQ : 0 ≤ CQ := by dsimp only [CQ];positivity
  refine ⟨min ηJ ηB,CQ*CE,lt_min hηJ hηB,(min_le_left _ _).trans hηJ1,by dsimp only [CE];positivity,?_⟩
  intro floor hf ε hε hSmall d hd CF CT CB CS P WF a b k φ E D hφ
  let w := fun x => scalarPrincipalMatrix d.γ d.g₂ d.radius x a b
  let C := scalarFirstSymmetricCoefficient P w k
  let Ch := scalarFirstSymmetricHigher WF w k
  let Ur := E.realHigherSobolevSection (5/2:ℝ) (by norm_num)
  let Ui := E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)
  let H := fun U => fiveHalfCovariantDerivative d U
  let R := fun (U : X → SphereSobolev (5/2:ℝ)) v z y => frameCurvatureSobolevL (3/2:ℝ) d.γ d.frame y v z
    (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y))
  let T := fun U => halfCovariantThirdDensity d (metricDensity d.γ) C (H U) (axis a) (axis b) (axis k)
  let Rem := fun U => halfCovariantThirdRemainder d (metricDensity d.γ) C Ch (H U) (R U) (axis a) (axis b) (axis k)
  let En := fun (U : X → SphereSobolev (5/2:ℝ)) (y : X) => ∑ i : I,halfCovariantDirectionEnergy d
    (fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)) y (beta d.γ d.radius y) (axis i)
  have hg : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have he (i : I) : ContDiffOn ℝ ∞ (fun x => d.frame x i) Y := (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hFrame : ∀ x ∈ Y,∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j)=if i=j then 1 else 0 :=
    fun x hx => hd.1.2.2.2.2.2.2.2 x (hSub hx)
  have hForward (y : X) (hy : y ∈ Y) (i : I) := P.firstCovariantCoordinateHigherL_balanced i y
    (P.firstDerivativeCoordinate_balanced y (hBalanced floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd CF CT P y hy) i)
  have hWS := hd.contDiffOn_scalarPrincipalMatrix_entry hSub (zero_lt_one.trans_le hK) a b
  have hPer (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U) (hU0 : ∀ x ∉ E.supportSet,U x=0) :=
    physical_scalar_first_symmetric_third_reduction hY hΩ hSub hd (zero_lt_one.trans_le hK) P WF hForward w hWS k
      U hU E.supportSet E.compactSupportSet E.supportSubset hU0 (axis a) (axis b) (axis k)
  have hr := hPer Ur (E.contDiff_realHigherSobolevSection _ _)
    (fun x hx => E.realHigherSobolevSection_zero _ _ (by norm_num) hx)
  have hi := hPer Ui (E.contDiff_imagHigherSobolevSection _ _)
    (fun x hx => E.imagHigherSobolevSection_zero _ _ (by norm_num) hx)
  have hPoint (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U) (y : X) (hy : y ∈ Y) :
      |Rem U y| ≤ CQ*ε^2*metricDensity d.γ y*En U y := by
    let U3 := fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)
    let β := beta d.γ d.radius y
    have hβ : 1 ≤ β := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
    have hData := hJets floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd CF CT P CB CS WF a b k y hy
    have hDC (i j : I) : ‖halfOperatorCovariantDerivativeL d C Ch y (axis i) (H U (axis j) y)‖ ≤
        Q*ε^2/β*‖sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (H U (axis j) y)‖ := by
      obtain ⟨L,hL,hLN⟩ := hData.2 i
      have hh := DFunLike.congr_fun hL (H U (axis j) y)
      simp only [ContinuousLinearMap.comp_apply] at hh
      rw [hh]
      exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_right hLN (norm_nonneg _))
    have hRNorm (i j : I) : ‖R U (axis i) (axis j) y‖ ≤ CR*‖U3 y‖ := by
      have hh := hd.1.norm_frameCurvatureSobolevL_le (3/2:ℝ) hΩ hK (by omega) (hSub hy) (axis i) (axis j)
      simp only [norm_axis,mul_one] at hh
      exact ((frameCurvatureSobolevL (3/2:ℝ) d.γ d.frame y (axis i) (axis j)).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right hh (norm_nonneg _))
    have hDir0 (i : I) : 0 ≤ halfCovariantDirectionEnergy d U3 y β (axis i) := by
      dsimp only [halfCovariantDirectionEnergy]
      positivity
    have hSingle (i : I) := Finset.single_le_sum (f:=fun i : I => halfCovariantDirectionEnergy d U3 y β (axis i))
      (fun i _ => hDir0 i) (Finset.mem_univ i)
    have hV (i : I) : β⁻¹*‖sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (H U (axis i) y)‖^2 ≤ En U y := by
      rw [fiveHalfCovariantDerivative_half_inclusion d U y (axis i) (hU.differentiable (by simp) y)]
      exact (le_add_of_nonneg_right (by positivity : 0 ≤ β*‖U3 y‖^2)).trans (hSingle i)
    have hMass : β*‖U3 y‖^2 ≤ En U y :=
      (le_add_of_nonneg_left (by positivity : 0 ≤ β⁻¹*‖halfSectionCovariantDerivativeL d U3 y (axis 0)‖^2)).trans (hSingle 0)
    exact halfCovariantThirdRemainder_bound d (metricDensity d.γ) C Ch (H U) (R U) y a b k (U3 y)
      Q MD CR ε β (En U y) hQ hMD hCR (Real.sqrt_nonneg _) hβ hData.1 hDC
      (fun i => hd.relative_density_axis_bound hΩ (by omega) (zero_lt_one.trans_le hK) hy i) hRNorm hV hMass
  have hUR : (fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (Ur x))=
      E.realSobolevSection (3/2:ℝ) (by norm_num) :=
    funext (E.realHigherSobolevSection_inclusion _ _ _ (by norm_num) (by norm_num))
  have hUI : (fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (Ui x))=
      E.imagSobolevSection (3/2:ℝ) (by norm_num) :=
    funext (E.imagHigherSobolevSection_inclusion _ _ _ (by norm_num) (by norm_num))
  have hBound : ∀ᵐ y ∂volume.restrict Y,‖Rem Ur y+Rem Ui y‖ ≤ (CQ*CE*ε^2)*physicalEnergyDensity d.γ d.frame d.radius φ y := by
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
  have hIdentity : 2*(∫ y in Y,T Ur y+T Ui y)=(∫ y in Y,Rem Ur y+Rem Ui y) := by
    rw [integral_add hr.1 hi.1,integral_add hr.2.1 hi.2.1]
    linarith only [hr.2.2,hi.2.2]
  refine ⟨hr.1.add hi.1,?_⟩
  rw [hIdentity]
  simpa only [Real.norm_eq_abs,integral_const_mul,←energySq_eq_integral_density] using hIntegral

end ShrinkingSpheres.ParallelEnergy
