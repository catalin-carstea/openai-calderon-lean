import Proof.PhysicalTruncatedCoordinateNormalForm
import Proof.ScalarPrincipalConnectionDrift

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Effective first coefficient when the base-connection part of the
scalar Hessian is included, while angular covariant derivatives are kept. -/
def PhysicalPrincipalData.firstCovariantCoordinateCoarseL
    {Y : Set X} {d : Data} {CF CT : ℝ} (P : PhysicalPrincipalData Y d CF CT) (k : I) (y : X) :
    SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  P.firstDerivativeCoordinateCoarseL k y-
    scalarPrincipalConnectionWeight d k y • sphereSobolevInclusionL 1 0 (by norm_num)

/-- Exact SAME actual residual in ordered fixed-base covariant derivatives.
All frame derivatives have canceled; the scalar base-connection drift is
included explicitly in its effective first coefficient. -/
theorem PhysicalPrincipalData.truncatedResidualValue_covariant_derivative_normal_form
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (P : PhysicalPrincipalData Y d CF CT) (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d)
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hK : 0 < K)
    (U : X → SphereSobolev 2) (hU : ContDiffOn ℝ ∞ U Y) {y : X} (hy : y ∈ Y) :
    P.truncatedResidualValue U y=
      sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
        ((∑ a : I,∑ b : I,scalarPrincipalMatrix d.γ d.g₂ d.radius y a b •
          oneSectionCovariantDerivative d (fun x => highSectionCovariantDerivative d U x (axis b)) y (axis a))+
          ∑ k : I,P.firstCovariantCoordinateCoarseL k y (highSectionCovariantDerivative d U y (axis k)))+
      P.potentialQuadraticHalfL y (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) (U y)) := by
  have hSub : Y ⊆ Ω := fun x hx => hd.2.1.center_mem hx
  have hg : Elliptic Y K d.γ :=
    ⟨fun a b => (hd.1.1.1 a b).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have he (j : I) : ContDiffOn ℝ ∞ (fun x => d.frame x j) Y :=
    (hd.1.2.2.2.2.2.2.1 j).mono hSub
  have hL := ((contDiffOn_highSectionCovariantDerivativeLinear hY d hg hK he U hU).contDiffAt
    (hY.mem_nhds hy)).differentiableAt (by simp)
  have hFirst : (∑ k : I,P.firstCovariantCoordinateCoarseL k y (highSectionCovariantDerivative d U y (axis k)))=
      (∑ k : I,P.firstDerivativeCoordinateCoarseL k y (highSectionCovariantDerivative d U y (axis k)))-
      ∑ k : I,scalarPrincipalConnectionWeight d k y • sphereSobolevInclusionL 1 0 (by norm_num)
        (highSectionCovariantDerivative d U y (axis k)) := by
    simp only [PhysicalPrincipalData.firstCovariantCoordinateCoarseL,_root_.sub_apply,_root_.smul_apply,
      Finset.sum_sub_distrib]
  rw [P.truncatedResidualValue_coordinate_covariant_normal_form hd hY hΩ hK U hU hy,
    scalar_principal_covariant_hessian_trace_split d U y hL,hFirst]
  simp only [map_add,map_sub]
  abel

end ShrinkingSpheres
