module

public import Proof.CalderonN.ActualSupportedConormalRemainder
public import Proof.CalderonN.ActualSupportedAffineRegular

import Proof.CalderonN.InverseAffineRemainderFactorization
import Mathlib.Tactic

/-! The angular factor entering the lower-order commutator needs only
the first normal-response difference, with the full quadratic remainder
remaining in the single scaled conormal generator. -/

public section

noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {d : Data dim} {x : X dim}

theorem ActualGaussFiberData.normalResponse_eq_flat_add_firstDifference (D : ActualGaussFiberData d x)
    (hr : d.radius x ≠ 0) :
    let r := d.radius x
    let B := D.flatDegree
    let L := ActualGaussFiberData.affineDensityMul d x
    let H := smoothSphereTraceMul D.reciprocal
    let H₁ := r⁻¹ • (H-1)
    let R := (r^2)⁻¹ • D.conormalRemainder
    let T := D.affineCorrection+B*L
    let N₁ := B*H₁+(T+r • R)*H
    D.normalResponse = B+r • N₁ := by
  dsimp only
  let r := d.radius x
  let B := D.flatDegree
  let L := ActualGaussFiberData.affineDensityMul d x
  let H := smoothSphereTraceMul D.reciprocal
  let H₁ := r⁻¹ • (H-1)
  let R := (r^2)⁻¹ • D.conormalRemainder
  let T := D.affineCorrection+B*L
  let N₁ := B*H₁+(T+r • R)*H
  let Q := (LinearMap.snd ℝ _ _).comp ((LinearMap.snd ℝ _ _).comp
    (smoothSphereTaylorResponses D.smoothCoefficient D.ellipticCoefficient D.solve))
  let C := smoothSphereTraceMul D.weight * ((LinearMap.fst ℝ _ _).comp
    (smoothSphereTaylorResponses D.smoothCoefficient D.ellipticCoefficient D.solve))
  have hT : T = L*B+Q := by
    change Q-(B*L-L*B)+B*L = L*B+Q
    abel
  have hC : C = B+r • T+r^2 • R := by
    change C = B+r • T+r^2 • ((r^2)⁻¹ • (C-B-r • (L*B+Q)))
    rw [hT,smul_smul,mul_inv_cancel₀ (pow_ne_zero _ hr),one_smul]
    abel
  have hH : H = 1+r • H₁ := by
    change H = 1+r • (r⁻¹ • (H-1))
    rw [smul_smul,mul_inv_cancel₀ hr,one_smul]
    abel
  change C*H = B+r • (B*H₁+(T+r • R)*H)
  have hC' : C = B+r • (T+r • R) := by
    rw [hC,smul_add r T,smul_smul r r R,← pow_two r,add_assoc]
  have hBH : B*H = B+r • (B*H₁) := by
    calc
      B*H = B*(1+r • H₁) := congrArg (fun X => B*X) hH
      _ = _ := by rw [mul_add,mul_one,mul_smul_comm]
  rw [hC',add_mul,smul_mul_assoc,hBH,smul_add r (B*H₁),add_assoc]

theorem ActualGaussFiberData.affine_add_radius_velocityRemainder_eq (D : ActualGaussFiberData d x)
    (hr : d.radius x ≠ 0) (i : I dim) :
    let r := d.radius x
    let B := D.flatDegree
    let L := ActualGaussFiberData.affineDensityMul d x
    let H := smoothSphereTraceMul D.reciprocal
    let H₁ := r⁻¹ • (H-1)
    let R := (r^2)⁻¹ • D.conormalRemainder
    let T := D.affineCorrection+B*L
    let N₁ := B*H₁+(T+r • R)*H
    let M := ActualGaussFiberData.translationMultiplier d x i+fderiv ℝ d.radius x (axis i) • 1
    let U := D.centerCorrection i
    D.affineCorrection*M+r • D.velocityRemainder i =
      N₁*M+r • (D.normalResponse*smoothSphereTraceMul (smoothVelocityNormal U)-
        smoothSphereVelocityTangent U) := by
  dsimp only
  let r := d.radius x
  have hr' : r ≠ 0 := hr
  let B := D.flatDegree
  let L := ActualGaussFiberData.affineDensityMul d x
  let H := smoothSphereTraceMul D.reciprocal
  let H₁ := r⁻¹ • (H-1)
  let R := (r^2)⁻¹ • D.conormalRemainder
  let T := D.affineCorrection+B*L
  let N₁ := B*H₁+(T+r • R)*H
  let M := ActualGaussFiberData.translationMultiplier d x i+fderiv ℝ d.radius x (axis i) • 1
  let U := D.centerCorrection i
  let P := smoothSphereTraceMul (smoothVelocityNormal U)
  let G := smoothSphereVelocityTangent U
  have hN : D.normalResponse = B+r • N₁ := D.normalResponse_eq_flat_add_firstDifference hr
  have hR : r • D.responseRemainder = N₁-D.affineCorrection := by
    change r • ((r^2)⁻¹ • (D.normalResponse-B-r • D.affineCorrection)) = _
    have hSub : B+r • N₁-B-r • D.affineCorrection = r • (N₁-D.affineCorrection) := by
      calc
        _ = r • N₁-r • D.affineCorrection := by abel
        _ = _ := (smul_sub r N₁ D.affineCorrection).symm
    rw [hN,hSub,smul_smul,smul_smul,show r*(r^2)⁻¹*r = 1 from by field_simp [hr'],one_smul]
  change D.affineCorrection*M+r • (D.responseRemainder*M+D.normalResponse*P-G) =
    N₁*M+r • (D.normalResponse*P-G)
  rw [show D.responseRemainder*M+D.normalResponse*P-G =
      D.responseRemainder*M+(D.normalResponse*P-G) by abel,smul_add,← smul_mul_assoc,hR,sub_mul N₁ D.affineCorrection M]
  abel

end CalderonN
