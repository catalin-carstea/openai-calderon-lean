import Proof.HighSectionHessianCoordinateContraction
import Proof.PhysicalFirstCoordinateCoarse
import Proof.PhysicalTruncatedResidual

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Exact fixed-coordinate covariant normal form of the SAME actual
truncated residual. The genuine Hessian retains the base connection;
the actual first coefficient uses its checked coarse inclusion graph. -/
theorem PhysicalPrincipalData.truncatedResidualValue_coordinate_covariant_normal_form
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (P : PhysicalPrincipalData Y d CF CT) (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d)
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hK : 0 < K)
    (U : X → SphereSobolev 2) (hU : ContDiffOn ℝ ∞ U Y) {y : X} (hy : y ∈ Y) :
    P.truncatedResidualValue U y=
      sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
        (∑ a : I,∑ b : I,scalarPrincipalMatrix d.γ d.g₂ d.radius y a b •
          highSectionCovariantHessianLinear d U y (axis a) (axis b))+
      sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
        (∑ b : I,P.firstDerivativeCoordinateCoarseL b y (highSectionCovariantDerivative d U y (axis b)))+
      P.potentialQuadraticHalfL y (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) (U y)) := by
  have hSub : Y ⊆ Ω := fun x hx => hd.2.1.center_mem hx
  have hg : Elliptic Y K d.γ :=
    ⟨fun a b => (hd.1.1.1 a b).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have he (j : I) : ContDiffOn ℝ ∞ (fun x => d.frame x j) Y :=
    (hd.1.2.2.2.2.2.2.1 j).mono hSub
  have hFrame := hd.1.2.2.2.2.2.2.2 y (hSub hy)
  have hL := ((contDiffOn_highSectionCovariantDerivativeLinear hY d hg hK he U hU).contDiffAt
    (hY.mem_nhds hy)).differentiableAt (by simp)
  have hE (j : I) := ((he j).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)
  have hSecond := principal_highSectionCovariantHessian_coordinate d U y hFrame hL hE
  let V := (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)).comp
    (highSectionCovariantDerivativeLinear d U y)
  have hCoordinate : (∑ j : I,P.firstDerivativeHalfL y j
      (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)
        (highSectionCovariantDerivative d U y (d.frame y j))))=
      ∑ b : I,P.firstDerivativeCoordinateHalfL y b
        (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) (highSectionCovariantDerivative d U y (axis b))) := by
    simpa only [V,ContinuousLinearMap.comp_apply,highSectionCovariantDerivativeLinear_apply] using
      P.first_derivative_coordinate_contraction y V
  have hFirst : (∑ j : I,P.firstDerivativeHalfL y j
      (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)
        (highSectionCovariantDerivative d U y (d.frame y j))))=
      sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
        (∑ b : I,P.firstDerivativeCoordinateCoarseL b y (highSectionCovariantDerivative d U y (axis b))) := by
    rw [hCoordinate,map_sum]
    apply Finset.sum_congr rfl
    intro b _
    have hh := DFunLike.congr_fun (P.firstDerivativeCoordinate_coarse_low_compatible hd hY hy b)
      (highSectionCovariantDerivative d U y (axis b))
    exact hh.symm
  rw [P.truncatedResidualValue_balanced_normal_form U hy hFrame,hSecond,hFirst]

end ShrinkingSpheres
