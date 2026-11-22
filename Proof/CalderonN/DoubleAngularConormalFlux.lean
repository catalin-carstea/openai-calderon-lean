module

public import Proof.CalderonN.ConormalFluxSumBounds

import Mathlib.Tactic

/-! The double angular Taylor remainder is the sum of six actual
conormal fluxes. Their combined divergence vanishes in the ball. -/

public section

noncomputable section
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 4800000
set_option maxSynthPendingDepth 25
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet OAI.AnisotropicCalderon.SmoothSphereRotation
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem smoothBallConormal_sub_coefficient (A B : X dim → Mat dim) (u : X dim → ℝ) :
    smoothBallConormal (A-B) u = smoothBallConormal A u-smoothBallConormal B u := by
  funext z
  have hF : smoothBallFlux (A-B) u z = smoothBallFlux A u z-smoothBallFlux B u z := by
    ext i
    simp only [smoothBallFlux_apply,Pi.sub_apply,Matrix.sub_apply,sub_mul,Finset.sum_sub_distrib,PiLp.sub_apply]
  rw [smoothBallConormal,hF,inner_sub_right]
  rfl

theorem smoothBallConormal_smul_coefficient (A : X dim → Mat dim) (u : X dim → ℝ) (r : ℝ) :
    smoothBallConormal (r • A) u = r • smoothBallConormal A u := by
  funext z
  have hF : smoothBallFlux (r • A) u z = r • smoothBallFlux A u z := by
    ext i
    simp only [smoothBallFlux_apply,Pi.smul_apply,Matrix.smul_apply,smul_eq_mul,PiLp.smul_apply,
      Finset.mul_sum,mul_assoc]
  rw [smoothBallConormal,hF,real_inner_smul_right]
  rfl

theorem smoothBallConormal_smul_solution (A : X dim → Mat dim) (u : SmoothData dim) (r : ℝ) :
    smoothBallConormal A (r • u.1) = r • smoothBallConormal A u.1 := by
  funext z
  have hF : smoothBallFlux A (r • u.1) z = r • smoothBallFlux A u.1 z := by
    have hD : fderiv ℝ (r • u.1) z = r • fderiv ℝ u.1 z :=
      fderiv_const_smul (u.2.differentiable (by simp) z) r
    ext i
    simp only [smoothBallFlux_apply,coordDeriv,hD,smul_apply,smul_eq_mul,PiLp.smul_apply,Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [smoothBallConormal,hF,real_inner_smul_right]
  rfl

theorem doubleAngularTaylor_conormal_sum (i j k l : Fin dim)
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A) (b b₁ b₂ b₁₂ u q : SmoothData dim)
    (ell₂ : X dim →L[ℝ] ℝ) (r : ℝ) :
    let A₁ := ballRotationCoefficient i j A
    let A₂ := ballRotationCoefficient k l A
    let A₁₂ := ballRotationCoefficient k l A₁
    let L (z : X dim) := ell₂ z • (1 : Mat dim)
    let A₀ : X dim → Mat dim := fun _ => 1
    let R := A₁₂-r • L
    let D := A-A₀
    let w₁ := angularBallCorrection i j b b₁
    let w₂ := angularBallCorrection k l b b₂
    let w₁₂ := angularBallCorrection i j b₂ b₁₂
    let w := angularBallCorrection k l w₁ w₁₂
    let e : SmoothData dim := ⟨w.1-r • q.1,w.2.sub (q.2.const_smul r)⟩
    let d : SmoothData dim := ⟨b.1-u.1,b.2.sub u.2⟩
    sphereRotationDerivative k l
      (sphereRotationDerivative i j (smoothBallConormal A b.1)-smoothBallConormal A b₁.1)-
      (sphereRotationDerivative i j (smoothBallConormal A b₂.1)-smoothBallConormal A b₁₂.1)-
      r • (smoothBallConormal L u.1+smoothBallConormal A₀ q.1) =
      smoothBallConormal A e.1+smoothBallConormal A₁₂ d.1+smoothBallConormal R u.1+
        smoothBallConormal A₁ w₂.1+smoothBallConormal A₂ w₁.1+smoothBallConormal (r • D) q.1 := by
  dsimp only
  rw [conormal_doubleAngularBallCorrection i j k l hA b b₁ b₂ b₁₂]
  let A₁ := ballRotationCoefficient i j A
  let A₂ := ballRotationCoefficient k l A
  let A₁₂ := ballRotationCoefficient k l A₁
  let L (z : X dim) := ell₂ z • (1 : Mat dim)
  let A₀ : X dim → Mat dim := fun _ => 1
  let w₁ := angularBallCorrection i j b b₁
  let w₂ := angularBallCorrection k l b b₂
  let w₁₂ := angularBallCorrection i j b₂ b₁₂
  let w := angularBallCorrection k l w₁ w₁₂
  let q' : SmoothData dim := ⟨r • q.1,q.2.const_smul r⟩
  change smoothBallConormal A w.1 + smoothBallConormal A₂ w₁.1+
      smoothBallConormal A₁ w₂.1+smoothBallConormal A₁₂ b.1-
      r • (smoothBallConormal L u.1+smoothBallConormal A₀ q.1) =
    smoothBallConormal A (w.1-q'.1)+smoothBallConormal A₁₂ (b.1-u.1)+
      smoothBallConormal (A₁₂-r • L) u.1+smoothBallConormal A₁ w₂.1+
      smoothBallConormal A₂ w₁.1+smoothBallConormal (r • (A-A₀)) q.1
  rw [smoothBallConormal_sub_solution A w q',smoothBallConormal_sub_solution A₁₂ b u,
    smoothBallConormal_sub_coefficient A₁₂ (r • L),smoothBallConormal_smul_coefficient L u.1 r,
    smoothBallConormal_smul_coefficient (A-A₀) q.1 r,smoothBallConormal_sub_coefficient A A₀]
  change _ = smoothBallConormal A w.1-smoothBallConormal A (r • q.1)+_+_+_+_+_
  rw [smoothBallConormal_smul_solution A q r,smul_add,smul_sub]
  abel

theorem doubleAngularTaylor_conormal_sum_divergence (i j k l : Fin dim)
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A) (b b₁ b₂ b₁₂ u q : SmoothData dim)
    (hb : EqOn (negativeBallDivergence A b.1) 0 (ball (0 : X dim) 1))
    (hb₁ : EqOn (negativeBallDivergence A b₁.1) 0 (ball (0 : X dim) 1))
    (hb₂ : EqOn (negativeBallDivergence A b₂.1) 0 (ball (0 : X dim) 1))
    (hb₁₂ : EqOn (negativeBallDivergence A b₁₂.1) 0 (ball (0 : X dim) 1))
    (ell₂ : X dim →L[ℝ] ℝ) (r : ℝ)
    (hq : EqOn (negativeBallDivergence (fun _ => (1 : Mat dim)) q.1)
      (-negativeBallDivergence (fun z => ell₂ z • (1 : Mat dim)) u.1) (ball (0 : X dim) 1)) :
    let A₁ := ballRotationCoefficient i j A
    let A₂ := ballRotationCoefficient k l A
    let A₁₂ := ballRotationCoefficient k l A₁
    let L (z : X dim) := ell₂ z • (1 : Mat dim)
    let A₀ : X dim → Mat dim := fun _ => 1
    let R := A₁₂-r • L
    let D := A-A₀
    let w₁ := angularBallCorrection i j b b₁
    let w₂ := angularBallCorrection k l b b₂
    let w₁₂ := angularBallCorrection i j b₂ b₁₂
    let w := angularBallCorrection k l w₁ w₁₂
    let e : SmoothData dim := ⟨w.1-r • q.1,w.2.sub (q.2.const_smul r)⟩
    let d : SmoothData dim := ⟨b.1-u.1,b.2.sub u.2⟩
    EqOn (coordinateFluxDivergence
      (smoothBallFlux A e.1+smoothBallFlux A₁₂ d.1+smoothBallFlux R u.1+
        smoothBallFlux A₁ w₂.1+smoothBallFlux A₂ w₁.1+smoothBallFlux (r • D) q.1))
      0 (ball (0 : X dim) 1) := by
  dsimp only
  let A₁ := ballRotationCoefficient i j A
  let A₂ := ballRotationCoefficient k l A
  let A₁₂ := ballRotationCoefficient k l A₁
  let L (z : X dim) := ell₂ z • (1 : Mat dim)
  let A₀ : X dim → Mat dim := fun _ => 1
  let R := A₁₂-r • L
  let D := A-A₀
  let w₁ := angularBallCorrection i j b b₁
  let w₂ := angularBallCorrection k l b b₂
  let w₁₂ := angularBallCorrection i j b₂ b₁₂
  let w := angularBallCorrection k l w₁ w₁₂
  let e : SmoothData dim := ⟨w.1-r • q.1,w.2.sub (q.2.const_smul r)⟩
  let d : SmoothData dim := ⟨b.1-u.1,b.2.sub u.2⟩
  let F₀ := smoothBallFlux A e.1
  let F₁ := smoothBallFlux A₁₂ d.1
  let F₂ := smoothBallFlux R u.1
  let F₃ := smoothBallFlux A₁ w₂.1
  let F₄ := smoothBallFlux A₂ w₁.1
  let F₅ := smoothBallFlux (r • D) q.1
  let hA₁ := contDiff_ballRotationCoefficient i j hA
  let hA₂ := contDiff_ballRotationCoefficient k l hA
  let hA₁₂ := contDiff_ballRotationCoefficient k l hA₁
  have hR : ContDiff ℝ ∞ R := hA₁₂.sub ((ell₂.contDiff.smul contDiff_const).const_smul r)
  have hD : ContDiff ℝ ∞ (r • D) := (hA.sub contDiff_const).const_smul r
  have hF₀ : Differentiable ℝ F₀ := (contDiff_smoothBallFlux hA e).differentiable (by simp)
  have hF₁ : Differentiable ℝ F₁ := (contDiff_smoothBallFlux hA₁₂ d).differentiable (by simp)
  have hF₂ : Differentiable ℝ F₂ := (contDiff_smoothBallFlux hR u).differentiable (by simp)
  have hF₃ : Differentiable ℝ F₃ := (contDiff_smoothBallFlux hA₁ w₂).differentiable (by simp)
  have hF₄ : Differentiable ℝ F₄ := (contDiff_smoothBallFlux hA₂ w₁).differentiable (by simp)
  have hF₅ : Differentiable ℝ F₅ := (contDiff_smoothBallFlux hD q).differentiable (by simp)
  intro z hz
  change coordinateFluxDivergence (F₀+F₁+F₂+F₃+F₄+F₅) z = 0
  rw [coordinateFluxDivergence_add ((((hF₀.add hF₁).add hF₂).add hF₃).add hF₄) hF₅,
    coordinateFluxDivergence_add (((hF₀.add hF₁).add hF₂).add hF₃) hF₄,
    coordinateFluxDivergence_add ((hF₀.add hF₁).add hF₂) hF₃,
    coordinateFluxDivergence_add (hF₀.add hF₁) hF₂,coordinateFluxDivergence_add hF₀ hF₁]
  dsimp only [F₀,F₁,F₂,F₃,F₄,F₅]
  simp only [coordinateFluxDivergence_smoothBallFlux]
  have hEq := negativeBallDivergence_doubleAngularTaylorRemainder i j k l hA b b₁ b₂ b₁₂ u q
    hb hb₁ hb₂ hb₁₂ ell₂ hq r hz
  change negativeBallDivergence A e.1 z =
    -negativeBallDivergence A₁₂ d.1 z-negativeBallDivergence R u.1 z-
      negativeBallDivergence A₁ w₂.1 z-negativeBallDivergence A₂ w₁.1 z-
      negativeBallDivergence (r • D) q.1 z at hEq
  linarith only [hEq]

end CalderonN
