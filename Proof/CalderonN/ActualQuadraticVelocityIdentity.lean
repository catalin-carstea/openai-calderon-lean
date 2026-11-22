module

public import Proof.CalderonN.ActualLowerOrderVelocity
public import Proof.CalderonN.ActualRadialQuadraticMultiplierBounds

import Mathlib.Tactic

/-! The factored quadratic velocity remainder uses the actual reciprocal
Taylor multiplier and the actual scaled conormal remainder. -/

public section

noncomputable section
open scoped ContDiff
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {d : Data dim} {x : X dim}

theorem ActualGaussFiberData.responseRemainder_eq_firstDifference
    (D : ActualGaussFiberData d x) (hr : d.radius x ≠ 0) :
    let r := d.radius x
    let B := D.flatDegree
    let L := ActualGaussFiberData.affineDensityMul d x
    let H := smoothSphereTraceMul D.reciprocal
    let H₁ := r⁻¹ • (H-1)
    let H₂ := (r^2)⁻¹ • (H-1+r • L)
    let T := D.affineCorrection+B*L
    D.responseRemainder = B*H₂+T*H₁+((r^2)⁻¹ • D.conormalRemainder)*H := by
  dsimp only
  let r := d.radius x
  let B := D.flatDegree
  let L := ActualGaussFiberData.affineDensityMul d x
  let H := smoothSphereTraceMul D.reciprocal
  let H₁ := r⁻¹ • (H-1)
  let H₂ := (r^2)⁻¹ • (H-1+r • L)
  let T := D.affineCorrection+B*L
  let R := (r^2)⁻¹ • D.conormalRemainder
  change D.responseRemainder = B*H₂+T*H₁+R*H
  have h := D.responseRemainder_eq_conormal hr
  change D.responseRemainder =
    B*H₂+(_+_)*(-L+r • H₂)+R*H at h
  have hT : T = L*B+(LinearMap.snd ℝ _ _).comp ((LinearMap.snd ℝ _ _).comp
      (smoothSphereTaylorResponses D.smoothCoefficient D.ellipticCoefficient D.solve)) := by
    dsimp [T,ActualGaussFiberData.affineCorrection]
    abel
  have hH₁ : -L+r • H₂ = H₁ := by
    change -L+r • ((r^2)⁻¹ • (H-1+r • L)) = r⁻¹ • (H-1)
    rw [smul_smul,show r*(r^2)⁻¹ = r⁻¹ by field_simp [hr]]
    rw [smul_add,smul_smul,inv_mul_cancel₀ hr,one_smul]
    abel
  rw [h,hT,hH₁]

end CalderonN
