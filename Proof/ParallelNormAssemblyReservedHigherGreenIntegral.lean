import Proof.ParallelNormAssemblyReservedHigherGreenPoint
import Proof.HalfCovariantEnergyControl
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

/-- Quantitative paired Green estimate with the original physical energy.
All coefficient families precede tests; the lift is a genuine graph only,
with no assumed smoothness and no second HIGH jet premise. -/
theorem uniform_quadratic_higher_pair_integral_bound {Y Ω : Set X}
    (hY : IsOpen Y) (hSub : Y ⊆ Ω) {m : ℕ}
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K)
    (Q Q1 CH CN CQ CD : ℝ) (hQ : 0 ≤ Q) (hQ1 : 0 ≤ Q1)
    (hCH : 0 ≤ CH) (hCN : 0 ≤ CN) (hCQ : 0 ≤ CQ) (hCD : 0 ≤ CD) :
    ∃ C0 : ℝ,0 ≤ C0 ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ∀ d,
    Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ i : I,
    ∀ q : X → ℝ,ContDiffOn ℝ ∞ q Y →
    ∀ H : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),ContDiffOn ℝ ∞ H Y →
    ∀ C : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),ContDiffOn ℝ ∞ C Y →
    ∀ N : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
    ∀ DQ : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
    (∀ y ∈ Y,higherOperatorCovariantDerivativeL d H y (axis i)=
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
        ((N y).comp (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)))) →
    (∀ y ∈ Y,quadraticOperatorCovariantDerivativeL d C y (axis i)=
      (sphereSobolevInclusionL (-(1/2:ℝ)) (-(3/2:ℝ)) (by norm_num)).comp
        ((DQ y).comp (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)))) →
    (∀ y ∈ Y,|q y| ≤ Q*metricDensity d.γ y ∧
      |fderiv ℝ q y (axis i)| ≤ Q1*metricDensity d.γ y ∧
      ‖H y‖ ≤ CH ∧ ‖N y‖ ≤ CN*beta d.γ d.radius y ∧
      ‖C y‖ ≤ CQ*ε ∧ ‖DQ y‖ ≤ CD*ε*beta d.γ d.radius y) →
    ∀ L : X → SphereSobolev (5/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ),
    (∀ y ∈ Y,∀ u : SphereSobolev (5/2:ℝ),
      sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (L y u)=
        H y (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u)) →
    ∀ φ : Field,∀ E : HarmonicTestExpansion Y d.γ d.frame φ,∀ D : AngularModelData E d.radius,
    Test Y d.γ d.frame φ →
      let Ur := E.realHigherSobolevSection (5/2:ℝ) (by norm_num)
      let Ui := E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)
      let F := fun y => quadraticHigherPairDensity d q H C Ur (axis i) y+
        quadraticHigherPairDensity d q H C Ui (axis i) y
      IntegrableOn F Y ∧ |∫ y in Y,F y| ≤ C0*ε*energySq Y d.γ d.frame d.radius φ := by
  let CR := Q*(CN*CQ+CH*CD)+Q1*CH*CQ
  let CE := 3*K^2+1
  have hCR : 0 ≤ CR := by dsimp only [CR];positivity
  have hCE : 0 ≤ CE := by dsimp only [CE];positivity
  refine ⟨CR*CE,mul_nonneg hCR hCE,?_⟩
  intro floor hf ε hε d hd i q hq H hH C hC N DQ hN hDQ hBounds L hL φ E D hφ
  let Ur := E.realHigherSobolevSection (5/2:ℝ) (by norm_num)
  let Ui := E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)
  let F := fun U => quadraticHigherPairDensity d q H C U (axis i)
  let R := fun U => quadraticHigherPairRemainder q H N C DQ U (axis i)
  have hg : Elliptic Y K d.γ :=
    ⟨fun a b => (hd.1.1.1 a b).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have he (a : I) : ContDiffOn ℝ ∞ (fun x => d.frame x a) Y := (hd.1.2.2.2.2.2.2.1 a).mono hSub
  have hFrame : ∀ x ∈ Y,∀ a b,metricPair d.γ x (d.frame x a) (d.frame x b)=if a=b then 1 else 0 :=
    fun x hx => hd.1.2.2.2.2.2.2.2 x (hSub hx)
  have hPer (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U)
      (hU0 : ∀ x ∉ E.supportSet,U x=0) :
      IntegrableOn (F U) Y ∧ IntegrableOn (R U) Y ∧ (∫ y in Y,F U y)=∫ y in Y,R U y :=
    quadratic_higher_paired_mass_reduction hY d (axis i) hg (zero_lt_one.trans_le hK) he
      q hq H hH C hC N DQ hN hDQ U hU (fun x => L x (U x))
      (fun x hx => hL x hx (U x)) E.supportSet E.compactSupportSet E.supportSubset hU0
  have hr := hPer Ur (E.contDiff_realHigherSobolevSection _ _)
    (fun x hx => E.realHigherSobolevSection_zero _ _ (by norm_num) hx)
  have hi := hPer Ui (E.contDiff_imagHigherSobolevSection _ _)
    (fun x hx => E.imagHigherSobolevSection_zero _ _ (by norm_num) hx)
  have hPoint (U : X → SphereSobolev (5/2:ℝ)) (y : X) (hy : y ∈ Y) :
      |R U y| ≤ CR*ε*beta d.γ d.radius y*metricDensity d.γ y*
        ‖sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y)‖^2 := by
    have hh := hBounds y hy
    exact quadratic_higher_pair_remainder_bound q H N C DQ U (axis i) y Q Q1 CH CN CQ CD
      ε (beta d.γ d.radius y) (metricDensity d.γ y) hQ hQ1 hCH hCN hCQ hCD hε
      (hf.trans (hd.2.2.2.2.1.2 y hy).2.1) (Real.sqrt_nonneg _)
      hh.1 hh.2.1 hh.2.2.1 hh.2.2.2.1 hh.2.2.2.2.1 hh.2.2.2.2.2
  have hUR (y : X) : sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (Ur y)=
      E.realSobolevSection (3/2:ℝ) (by norm_num) y :=
    E.realHigherSobolevSection_inclusion _ _ _ (by norm_num) (by norm_num) y
  have hUI (y : X) : sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (Ui y)=
      E.imagSobolevSection (3/2:ℝ) (by norm_num) y :=
    E.imagHigherSobolevSection_inclusion _ _ _ (by norm_num) (by norm_num) y
  have hBound : ∀ᵐ y ∂volume.restrict Y,‖R Ur y+R Ui y‖ ≤
      (CR*CE*ε)*physicalEnergyDensity d.γ d.frame d.radius φ y := by
    filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
    let β := beta d.γ d.radius y
    let μ := metricDensity d.γ y
    let ur := E.realSobolevSection (3/2:ℝ) (by norm_num) y
    let ui := E.imagSobolevSection (3/2:ℝ) (by norm_num) y
    have hMass : μ*(β*‖ur‖^2+β*‖ui‖^2) ≤ CE*physicalEnergyDensity d.γ d.frame d.radius φ y := by
      have hEnergy := D.half_covariant_direction_energy_le hY hg hK he hFrame hφ.1 hy i
      have hGrow : μ*(β*‖ur‖^2+β*‖ui‖^2) ≤ metricDensity d.γ y*(
          halfCovariantDirectionEnergy d (E.realSobolevSection (3/2:ℝ) (by norm_num)) y β (axis i)+
          halfCovariantDirectionEnergy d (E.imagSobolevSection (3/2:ℝ) (by norm_num)) y β (axis i)) := by
        apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
        dsimp only [halfCovariantDirectionEnergy,ur,ui]
        have hb : 0 ≤ β⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
        nlinarith only [mul_nonneg hb (sq_nonneg ‖halfSectionCovariantDerivativeL d
          (E.realSobolevSection (3/2:ℝ) (by norm_num)) y (axis i)‖),
          mul_nonneg hb (sq_nonneg ‖halfSectionCovariantDerivativeL d
          (E.imagSobolevSection (3/2:ℝ) (by norm_num)) y (axis i)‖)]
      exact hGrow.trans hEnergy
    rw [Real.norm_eq_abs]
    calc
      _ ≤ |R Ur y|+|R Ui y| := abs_add_le _ _
      _ ≤ CR*ε*β*μ*‖sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (Ur y)‖^2+
          CR*ε*β*μ*‖sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (Ui y)‖^2 :=
        add_le_add (hPoint Ur y hy) (hPoint Ui y hy)
      _ = (CR*ε)*(μ*(β*‖ur‖^2+β*‖ui‖^2)) := by rw [hUR,hUI];ring
      _ ≤ (CR*ε)*(CE*physicalEnergyDensity d.γ d.frame d.radius φ y) :=
        mul_le_mul_of_nonneg_left hMass (mul_nonneg hCR hε)
      _ = _ := by ring
  have hDom := (hd.2.2.2.2.1.integrableOn_physicalEnergyDensity hY hg (zero_lt_one.trans_le hK)
    d.frame he hFrame hf hφ).const_mul (CR*CE*ε)
  have hInt := norm_integral_le_of_norm_le hDom hBound
  have hIdentity : (∫ y in Y,F Ur y+F Ui y)=∫ y in Y,R Ur y+R Ui y := by
    rw [integral_add hr.1 hi.1,integral_add hr.2.1 hi.2.1,hr.2.2,hi.2.2]
  refine ⟨hr.1.add hi.1,?_⟩
  change |∫ y in Y,F Ur y+F Ui y| ≤ _
  rw [hIdentity]
  simpa only [Real.norm_eq_abs,integral_const_mul,←energySq_eq_integral_density,mul_assoc] using hInt

end ShrinkingSpheres.ParallelEnergy
