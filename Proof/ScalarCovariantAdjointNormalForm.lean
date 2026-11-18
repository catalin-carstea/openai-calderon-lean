import Proof.CovariantScalarSectionProduct
import Proof.Archive.ScalarAdjointCoefficients

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.PrincipalCommutator
open OAI.AnisotropicCalderon.ScalarBaseAdjoint
open OAI.AnisotropicCalderon.ActualScalarPrincipalAdjoint

def scalarCovariantSecondSection (d : Data) (a : X → Mat) (U : X → SphereSobolev 2) (y : X) :
    SphereSobolev 0 :=
  ∑ i : I,∑ j : I,a y i j • oneSectionCovariantDerivative d
    (fun x => highSectionCovariantDerivative d U x (axis j)) y (axis i)

/-- The formal double covariant transpose. Its genuine integrated
adjunction is a separate downstream Green identity. -/
def scalarCovariantSecondTransposeSection (d : Data) (mu : X → ℝ) (a : X → Mat)
    (U : X → SphereSobolev 2) (y : X) : SphereSobolev 0 :=
  (mu y)⁻¹ • ∑ i : I,∑ j : I,oneSectionCovariantDerivative d
    (fun x => highSectionCovariantDerivative d (fun z => (mu z*a z i j) • U z) x (axis i)) y (axis j)

/-- Symmetry of the scalar second coefficient cancels every second base
term in the formal transpose defect. The scalar coefficients are exactly
the supplied density-adjoint coefficients; connection terms are retained. -/
theorem scalarCovariantSecondTransposeSection_sub {Y : Set X} (hY : IsOpen Y)
    (d : Data) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (mu : X → ℝ) (hmu : ContDiffOn ℝ ∞ mu Y)
    (a : X → Mat) (ha : ∀ i j,ContDiffOn ℝ ∞ (fun x => a x i j) Y)
    (hSym : ∀ x ∈ Y,(a x).IsHermitian)
    (U : X → SphereSobolev 2) (hU : ContDiffOn ℝ ∞ U Y)
    {y : X} (hy : y ∈ Y) (hmu0 : mu y ≠ 0) :
    scalarCovariantSecondTransposeSection d mu a U y-scalarCovariantSecondSection d a U y=
      adjointZeroCoefficient axis mu a y • sphereSobolevInclusionL 1 0 (by norm_num)
        (sphereSobolevInclusionL 2 1 (by norm_num) (U y))+
      ∑ i : I,adjointFirstCoefficient axis mu a y i • sphereSobolevInclusionL 1 0 (by norm_num)
        (highSectionCovariantDerivative d U y (axis i)) := by
  let F := fun i j x => mu x*a x i j
  let Iu := sphereSobolevInclusionL 1 0 (by norm_num)
    (sphereSobolevInclusionL 2 1 (by norm_num) (U y))
  let V := fun i => sphereSobolevInclusionL 1 0 (by norm_num)
    (highSectionCovariantDerivative d U y (axis i))
  let H := fun i j => oneSectionCovariantDerivative d
    (fun x => highSectionCovariantDerivative d U x (axis j)) y (axis i)
  have hNear : ∀ᶠ x in nhds y,(a x).IsHermitian := by
    filter_upwards [hY.mem_nhds hy] with x hx
    exact hSym x hx
  have hDsym (v : X) (i j : I) : fderiv ℝ (F i j) y v=fderiv ℝ (F j i) y v :=
    weighted_coefficient_directional_symmetry v mu a y hNear i j
  have hCross : (∑ i : I,∑ j : I,fderiv ℝ (F i j) y (axis i) • V j)=
      ∑ i : I,∑ j : I,fderiv ℝ (F i j) y (axis j) • V i := by
    calc
      _ = ∑ i : I,∑ j : I,fderiv ℝ (F j i) y (axis j) • V i := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [hDsym (axis j) j i]
  have hPrincipal : (mu y)⁻¹ • (∑ i : I,∑ j : I,F i j y • H j i)=
      scalarCovariantSecondSection d a U y := by
    have hCancel (i j : I) : (mu y)⁻¹*F i j y=a y i j := by
      dsimp only [F]
      rw [←mul_assoc,inv_mul_cancel₀ hmu0,one_mul]
    simp only [Finset.smul_sum,smul_smul,hCancel]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have hS : a y j i=a y i j := by simpa only [star_trivial] using (hSym y hy).apply i j
    rw [hS]
  have hExp : scalarCovariantSecondTransposeSection d mu a U y=
      (mu y)⁻¹ • ∑ i : I,∑ j : I,
        (fderiv ℝ (fun x => fderiv ℝ (F i j) x (axis i)) y (axis j) • Iu+
          fderiv ℝ (F i j) y (axis i) • V j+fderiv ℝ (F i j) y (axis j) • V i+
          F i j y • H j i) := by
    unfold scalarCovariantSecondTransposeSection
    apply congrArg (fun z : SphereSobolev 0 => (mu y)⁻¹ • z)
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact secondSectionCovariantDerivative_smul hY d hg hK he (F i j)
      (hmu.mul (ha i j)) U hU hy (axis j) (axis i)
  have hGroup : scalarCovariantSecondTransposeSection d mu a U y=
      (mu y)⁻¹ • (∑ i : I,∑ j : I,
        fderiv ℝ (fun x => fderiv ℝ (F i j) x (axis i)) y (axis j) • Iu)+
      (mu y)⁻¹ • (∑ i : I,∑ j : I,fderiv ℝ (F i j) y (axis i) • V j)+
      (mu y)⁻¹ • (∑ i : I,∑ j : I,fderiv ℝ (F i j) y (axis j) • V i)+
      (mu y)⁻¹ • (∑ i : I,∑ j : I,F i j y • H j i) := by
    rw [hExp]
    simp only [Finset.sum_add_distrib,smul_add]
  rw [hGroup,hCross,hPrincipal]
  change _=adjointZeroCoefficient axis mu a y • Iu+
    ∑ i : I,adjointFirstCoefficient axis mu a y i • V i
  unfold adjointZeroCoefficient adjointFirstCoefficient directionalFDeriv
  simp only [
    Finset.sum_smul,Finset.smul_sum,smul_smul,Fin.sum_univ_three,F]
  module

end ShrinkingSpheres
