import Proof.ActualFrameErrorLift
import Proof.FramePrincipalBounds
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
namespace ActualFrameErrorEndpointPair
variable {Y : Set X} {d : Data}
  {A : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0}
  {G : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0} {CE : ℝ}

def radiusPrincipalProductL (P : ActualFrameErrorEndpointPair Y d A G CE) (x : X) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  d.radius x • P.productL (fun x i j => frameTensorMatrix d.γ d.frame x (principal d.γ d.g₂ x) i j) x

lemma norm_radiusPrincipalProductL_small {Ω : Set X} {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (P : ActualFrameErrorEndpointPair Y d A G CE) (hCE : 0 ≤ CE)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {x : X} (hx : x ∈ Y) :
    ‖P.radiusPrincipalProductL x‖ ≤ 81*(K+1)*K^2*CE^2*ε := by
  have hr : 0 < d.radius x := (hd.2.2.2.2.1.2 x hx).1
  have hrε : d.radius x ≤ ε := (radius_bounds (d.radius x) (beta d.γ d.radius x) floor ε hr.le hf
    (hd.2.2.2.2.1.2 x hx).2.1 (hd.2.2.2.2.2 x hx).2).2.2
  have hr1 : d.radius x ≤ 1 := hrε.trans hε1
  have hSq : (d.radius x)^2 ≤ d.radius x := by
    simpa only [pow_two,mul_one] using mul_le_mul_of_nonneg_left hr1 hr.le
  have hCube : (d.radius x)^3 ≤ ε := by
    calc
      _ = d.radius x*(d.radius x)^2 := by ring
      _ ≤ d.radius x*d.radius x := mul_le_mul_of_nonneg_left hSq hr.le
      _ = (d.radius x)^2 := by ring
      _ ≤ d.radius x := hSq
      _ ≤ ε := hrε
  let B := 9*(K+1)*K^2
  have hB : 0 ≤ B := by dsimp only [B];positivity
  have hQ (i j : I) : |frameTensorMatrix d.γ d.frame x (principal d.γ d.g₂ x) i j| ≤ B :=
    (hd.framePrincipalCoefficient_bounds hK hf hε hε1 hx i j).2.1
  have hNorm := P.norm_productL_le (fun x i j => frameTensorMatrix d.γ d.frame x (principal d.γ d.g₂ x) i j)
    hB hCE hx hr.le hQ
  rw [radiusPrincipalProductL,norm_smul,Real.norm_eq_abs,abs_of_pos hr]
  calc
    _ ≤ d.radius x*(9*B*CE^2*(d.radius x)^2) := mul_le_mul_of_nonneg_left hNorm hr.le
    _ = (9*B*CE^2)*(d.radius x)^3 := by ring
    _ ≤ (9*B*CE^2)*ε := mul_le_mul_of_nonneg_left hCube (by positivity)
    _ = _ := by dsimp only [B];ring
end ActualFrameErrorEndpointPair
namespace SecondTraceSectionOutput
variable {Y : Set X} {d : Data}
  {A : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0}
  {G : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0}
  {S : I → I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0}
  {φ : Field} {L : ℂ →L[ℝ] ℝ} {F : X × X → ℝ} {hF : ContDiff ℝ ∞ F}

/-- The actual radius-weighted E/E term is exactly the small balanced map,
    on the SAME physical adjoint output and actual first-error witnesses. -/
lemma radius_error_product_actual (P : SecondTraceSectionOutput Y d A G S φ L F hF)
    {CE : ℝ} (E : ActualFrameErrorEndpointPair Y d A G CE) {y : X} (hy : y ∈ Y) :
    sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
      (d.radius y • ∑ i : I,∑ j : I,frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j •
        actualFrameFirstAdjointErrorFamily d A G i y (P.errorLift y j))=
      E.radiusPrincipalProductL y (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num)
        (ambientSobolevSection 2 (by norm_num) F hF y)) := by
  have hh := P.error_product_actual E (fun x i j => frameTensorMatrix d.γ d.frame x (principal d.γ d.g₂ x) i j) hy
  simpa only [ActualFrameErrorEndpointPair.radiusPrincipalProductL,_root_.smul_apply,map_smul] using
    congrArg (fun z : SphereSobolev (-(1/2:ℝ)) => d.radius y • z) hh
end SecondTraceSectionOutput

end ShrinkingSpheres
