module

public import Proof.CalderonN.SmoothTraceVelocityAffine
public import Proof.CalderonN.FlatTraceRaisingAction

import Mathlib.Tactic

/-! The affine normal form of the frozen adjoint uses the actual conormal
response, its reciprocal weight and the actual scaled velocity. -/

public section

noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 4300000
set_option maxSynthPendingDepth 24
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem admitted_scaledMovingAdjoint_affine_normalForm
    (hn : 2 ≤ dim) {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ}
    {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data dim}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    {y : X dim} (hy : y ∈ Y) (hrρ : 2*d.radius y < ρ)
    (i : I dim) {v : Field dim} (hv : smoothNear v (bundle Y d.γ))
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    (hAa : EqOn A (fun z => firstNormalVelocityCoefficient d y
      (d.radius y • frameVector d.frame y z)) (ball (0 : X dim) 1))
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
    (S : ∀ f : SmoothData dim, ConormalTaylorSolutions A (firstDensityCenterLinear d y) f)
    (W WI : SmoothData dim)
    (hW : EqOn W.1 (firstNormalRadialWeight d y (d.radius y)) (standardSphere dim))
    (hWI : EqOn WI.1 (fun z => (W.1 z)⁻¹) (standardSphere dim))
    (V : SmoothBallVelocity dim)
    (hV : EqOn V.1 (fun z => scaledNormalTraceVelocity d.γ d.expMap d.frame y (d.radius y)
      (fderiv ℝ d.radius y (axis i)) z (axis i)) (standardSphere dim))
    (fR fI : SmoothData dim)
    (hfR : EqOn fR.1 (fun z => (v (y,frameVector d.frame y z)).re) (standardSphere dim))
    (hfI : EqOn fI.1 (fun z => (v (y,frameVector d.frame y z)).im) (standardSphere dim)) :
    let r := d.radius y
    let b := fderiv ℝ d.radius y (axis i)
    let a := frameCoordinatesL d.γ y (d.frame y) (axis i)
    let X := smoothSphereTaylorResponses hA hEll S
    let N := smoothSphereTraceMul W * ((LinearMap.fst ℝ _ _).comp X) * smoothSphereTraceMul WI
    let Y := (LinearMap.snd ℝ _ _).comp X
    let B := (LinearMap.fst ℝ _ _).comp Y
    let Q := (LinearMap.snd ℝ _ _).comp Y
    let L := smoothSphereTraceMul ⟨firstDensityCenterLinear d y,(firstDensityCenterLinear d y).contDiff⟩
    let R := (r^2)⁻¹ • (smoothSphereTraceMul W * ((LinearMap.fst ℝ _ _).comp X)-B-r • (L*B+Q))
    let H₂ := (r^2)⁻¹ • (smoothSphereTraceMul WI-1+r • L)
    let U : SmoothBallVelocity dim :=
      ⟨fun z => (r^2)⁻¹ • (V.1 z-a-b • z),
        ((V.2.sub contDiff_const).sub (contDiff_id.const_smul b)).const_smul _⟩
    let F := Q-(B*L-L*B)
    let G := B*H₂+(L*B+Q)*(-L+r • H₂)+R*smoothSphereTraceMul WI
    let M_a := smoothSphereTraceMul (smoothVelocityNormal (smoothConstantVelocity a))
    let T := smoothSphereGaussAdjoint B (smoothConstantVelocity a)
    let E := G*(M_a+b • 1)+N*smoothSphereTraceMul (smoothVelocityNormal U)-smoothSphereVelocityTangent U
    let C := T+b • B+r • (F*M_a+b • F)+r^2 • E
    ∀ z : ↥(standardSphere dim),
      (r : ℂ)*adjointField d.adjoint i v (y,frameVector d.frame y z) =
        ⟨(C (smoothSphereTrace fR)).1 z,(C (smoothSphereTrace fI)).1 z⟩ := by
  dsimp only
  let r := d.radius y
  let b := fderiv ℝ d.radius y (axis i)
  let a := frameCoordinatesL d.γ y (d.frame y) (axis i)
  let P := smoothSphereTaylorResponses hA hEll S
  let S₀ := smoothSphereTraceMul W * ((LinearMap.fst ℝ _ _).comp P)
  let H := smoothSphereTraceMul WI
  let Y₀ := (LinearMap.snd ℝ _ _).comp P
  let B := (LinearMap.fst ℝ _ _).comp Y₀
  let Q := (LinearMap.snd ℝ _ _).comp Y₀
  let L := smoothSphereTraceMul ⟨firstDensityCenterLinear d y,(firstDensityCenterLinear d y).contDiff⟩
  let R := (r^2)⁻¹ • (S₀-B-r • (L*B+Q))
  let H₂ := (r^2)⁻¹ • (H-1+r • L)
  let U : SmoothBallVelocity dim :=
    ⟨fun z => (r^2)⁻¹ • (V.1 z-a-b • z),
      ((V.2.sub contDiff_const).sub (contDiff_id.const_smul b)).const_smul _⟩
  have hr : 0 < r := (hd.2.2.2.2.1.2 y hy).1
  have hr₂ : r^2 ≠ 0 := pow_ne_zero 2 hr.ne'
  have hS : B+r • (L*B+Q)+r^2 • R = S₀ := by
    change B+r • (L*B+Q)+r^2 • ((r^2)⁻¹ • (S₀-B-r • (L*B+Q))) = _
    rw [smul_smul,mul_inv_cancel₀ hr₂,one_smul]
    abel
  have hH : 1-r • L+r^2 • H₂ = H := by
    change 1-r • L+r^2 • ((r^2)⁻¹ • (H-1+r • L)) = _
    rw [smul_smul,mul_inv_cancel₀ hr₂,one_smul]
    abel
  have hAff : smoothAffineVelocity a b (r^2) U = V := by
    apply Subtype.ext
    funext z
    change a+b • z+r^2 • ((r^2)⁻¹ • (V.1 z-a-b • z)) = V.1 z
    rw [smul_smul,mul_inv_cancel₀ hr₂,one_smul]
    abel
  have h := smoothSphereGaussAdjoint_affineTaylor B L Q R H₂ r b a U
  dsimp only at h
  rw [hS,hH,hAff] at h
  intro z
  rw [admitted_smoothSphereGaussAdjoint_eq hn hY hΩ hd hK hy hrρ i hv hA hAa hEll S W WI hW hWI V hV
    fR fI hfR hfI z]
  have hGauss : smoothSphereGaussAdjoint (S₀*H) V = _ := h
  change Complex.mk ((smoothSphereGaussAdjoint (S₀*H) V (smoothSphereTrace fR)).1 z)
    ((smoothSphereGaussAdjoint (S₀*H) V (smoothSphereTrace fI)).1 z) = _
  rw [hGauss]

end CalderonN
