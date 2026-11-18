import Proof.ScalarCovariantAdjointDefect
import Proof.ScalarCovariantThirdCrossReduction
import Proof.ScalarCovariantSecondZeroReduction

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

lemma scalar_second_first_zero_square_algebra {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (mu c : ℝ) (a : I → I → ℝ) (b : I → ℝ) (u : E) (V : I → E) (H : I → I → E) :
    let S := ∑ i : I,∑ j : I,a i j • H i j
    let D := c • u+∑ i : I,b i • V i
    mu*(‖S‖^2-‖S+D‖^2)=
      -2*(∑ i : I,∑ j : I,∑ l : I,mu*a i j*b l*⟪H i j,V l⟫_ℝ)-
        2*(∑ i : I,∑ j : I,mu*a i j*c*⟪u,H i j⟫_ℝ)-mu*‖D‖^2 := by
  dsimp only
  rw [norm_add_sq_real]
  simp only [sum_inner,inner_sum,inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right,
    Fin.sum_univ_three]
  simp only [real_inner_comm u]
  ring

/-- The exact scalar self norm-square difference uses the SAME supplied
adjoint coefficients and genuine H2/H1/H0 covariant sections. -/
theorem scalar_covariant_self_square_identity {Y : Set X} (hY : IsOpen Y)
    (d : Data) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (mu : X → ℝ) (hmu : ContDiffOn ℝ ∞ mu Y)
    (a : MetricField) (ha : ∀ i j,ContDiffOn ℝ ∞ (fun x => a x i j) Y)
    (hSym : ∀ x ∈ Y,(a x).IsHermitian) (U : X → SphereSobolev 2) (hU : ContDiffOn ℝ ∞ U Y)
    {y : X} (hy : y ∈ Y) (hmu0 : mu y ≠ 0) :
    mu y*(‖scalarCovariantSecondSection d a U y‖^2-
      ‖scalarCovariantSecondTransposeSection d mu a U y‖^2)=
      -2*(∑ i : I,∑ j : I,∑ l : I,
        scalarCovariantThirdCrossDensity d (fun x => mu x*a x i j*adjointFirstCoefficient axis mu a x l)
          U (axis i) (axis j) (axis l) y)-
      2*(∑ i : I,∑ j : I,
        scalarCovariantSecondZeroDensity d (fun x => mu x*a x i j*adjointZeroCoefficient axis mu a x)
          U (axis i) (axis j) y)-mu y*‖scalarCovariantAdjointDefectSection d mu a U y‖^2 := by
  rw [scalarCovariantSecondTransposeSection_eq_add_defect hY d hg hK he mu hmu a ha hSym U hU hy hmu0]
  exact scalar_second_first_zero_square_algebra (mu y) (adjointZeroCoefficient axis mu a y)
    (fun i j => a y i j) (fun l => adjointFirstCoefficient axis mu a y l)
    (sphereSobolevInclusionL 1 0 (by norm_num) (sphereSobolevInclusionL 2 1 (by norm_num) (U y)))
    (fun l => sphereSobolevInclusionL 1 0 (by norm_num) (highSectionCovariantDerivative d U y (axis l)))
    (fun i j => oneSectionCovariantDerivative d (fun x => highSectionCovariantDerivative d U x (axis j)) y (axis i))

end ShrinkingSpheres
