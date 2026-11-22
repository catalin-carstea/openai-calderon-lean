module

public import Proof.CalderonN.BallRotationCalculus
public import Proof.CalderonN.FixedBallSmoothFlux

import Proof.CalderonN.LinearMetric
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

/-! Differentiating the physical flux along an angular generator, with the
matrix commutator for the pulled-back divergence coefficient. -/

public section

noncomputable section
open Set Matrix
open scoped ContDiff Gradient InnerProductSpace Matrix.Norms.Elementwise
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 23
set_option backward.isDefEq.respectTransparency false

namespace CalderonN

open OAI.AnisotropicCalderon.SmoothSphereRotation BallDirichlet

variable {dim : ℕ} [NeZero dim]

def divergenceMatrixOperatorL (dim : ℕ) : Mat dim →L[ℝ] X dim →L[ℝ] X dim :=
  (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin dim)).toAlgEquiv.toLinearEquiv.toLinearMap.toContinuousLinearMap

theorem divergenceMatrixOperatorL_apply_coord (A : Mat dim) (x : X dim) (i : Fin dim) :
    divergenceMatrixOperatorL dim A x i = ∑ j, A i j * x j := by
  unfold divergenceMatrixOperatorL
  exact congrFun (Matrix.ofLp_toEuclideanCLM A x) i

theorem divergenceMatrixOperatorL_mul (A B : Mat dim) :
    divergenceMatrixOperatorL dim (A*B) = (divergenceMatrixOperatorL dim A).comp
      (divergenceMatrixOperatorL dim B) := by
  unfold divergenceMatrixOperatorL
  exact map_mul (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin dim)) A B

theorem divergenceMatrixOperatorL_coordinateMatrix (J : X dim →L[ℝ] X dim) :
    divergenceMatrixOperatorL dim (coordinateMatrix J) = J := by
  apply ContinuousLinearMap.ext
  intro x
  ext i
  rw [divergenceMatrixOperatorL_apply_coord]
  exact congrFun (coordinateMatrix_mulVec J x) i

theorem smoothBallFlux_eq_gradient (a : X dim → Mat dim) (u : X dim → ℝ) (z : X dim) :
    smoothBallFlux a u z = divergenceMatrixOperatorL dim (a z) (gradient u z) := by
  ext i
  rw [smoothBallFlux_apply,divergenceMatrixOperatorL_apply_coord]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  rw [coordDeriv,← inner_gradient_left (𝕜 := ℝ)]
  simp only [axis,EuclideanSpace.inner_single_right,conj_trivial,one_mul]

/-- Linearized change of the pulled-back coefficient under a solid
rotation. The two matrix products account for the rotating coframe. -/
@[expose] def ballRotationCoefficient (i j : Fin dim) (a : X dim → Mat dim) (z : X dim) : Mat dim :=
  let J := ballRotationGeneratorL i j
  fderiv ℝ a z (J z)+a z*coordinateMatrix J-coordinateMatrix J*a z

theorem contDiff_ballRotationCoefficient (i j : Fin dim) {a : X dim → Mat dim}
    (ha : ContDiff ℝ ∞ a) : ContDiff ℝ ∞ (ballRotationCoefficient i j a) := by
  let B := coordinateMatrix (ballRotationGeneratorL i j)
  have hRight : ContDiff ℝ ∞ (fun z => a z * B) := by
    apply contDiff_pi.mpr
    intro k
    apply contDiff_pi.mpr
    intro l
    simpa only [Matrix.mul_apply] using ContDiff.sum fun m _ =>
      (contDiff_pi.mp (contDiff_pi.mp ha k) m).mul (contDiff_const (c := B m l))
  have hLeft : ContDiff ℝ ∞ (fun z => B * a z) := by
    apply contDiff_pi.mpr
    intro k
    apply contDiff_pi.mpr
    intro l
    simpa only [Matrix.mul_apply] using ContDiff.sum fun m _ =>
      (contDiff_const (c := B k m)).mul (contDiff_pi.mp (contDiff_pi.mp ha m) l)
  exact (((ha.fderiv_right (m := ∞) (by simp)).clm_apply
    (ballRotationGeneratorL i j).contDiff).add hRight).sub hLeft

private theorem inner_fderiv_gradient (u : SmoothData dim) (x v w : X dim) :
    ⟪fderiv ℝ (gradient u.1) x v,w⟫_ℝ = fderiv ℝ (fderiv ℝ u.1) x v w := by
  let L := (InnerProductSpace.toDual ℝ (X dim)).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have h := (L.hasFDerivAt.comp x
    ((u.2.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x).hasFDerivAt).fderiv
  change fderiv ℝ (gradient u.1) x = _ at h
  rw [h,ContinuousLinearMap.comp_apply]
  change ⟪(InnerProductSpace.toDual ℝ (X dim)).symm (fderiv ℝ (fderiv ℝ u.1) x v),w⟫_ℝ = _
  rw [← InnerProductSpace.toDual_apply_apply,LinearIsometryEquiv.apply_symm_apply]

theorem fderiv_gradient_along_rotation (i j : Fin dim) (u : SmoothData dim) (z : X dim) :
    fderiv ℝ (gradient u.1) z (ballRotationGeneratorL i j z) =
      gradient (sphereRotationDerivative i j u.1) z+ballRotationGeneratorL i j (gradient u.1 z) := by
  let J := ballRotationGeneratorL i j
  change fderiv ℝ (gradient u.1) z (J z) = gradient (sphereRotationDerivative i j u.1) z+J (gradient u.1 z)
  apply ext_inner_right ℝ
  intro v
  have hSym := (u.2.contDiffAt (x := z)).isSymmSndFDerivAt (by simp) (J z) v
  rw [inner_add_left,inner_fderiv_gradient,inner_gradient_left,
    show sphereRotationDerivative i j u.1 = (fun w => fderiv ℝ u.1 w (J w)) by
      funext w; rw [sphereRotationDerivative,ballRotationGeneratorL_apply],
    fderiv_linearDirectional_apply J u.2,← neg_eq_iff_eq_neg.mpr (inner_ballRotationGeneratorL_skew i j (gradient u.1 z) v),
    inner_gradient_left,hSym]
  ring

theorem fderiv_gradient_along_radial (u : SmoothData dim) (z : X dim) :
    fderiv ℝ (gradient u.1) z z =
      gradient (fun x => fderiv ℝ u.1 x x) z-gradient u.1 z := by
  apply ext_inner_right ℝ
  intro v
  have hSym := (u.2.contDiffAt (x := z)).isSymmSndFDerivAt (by simp) z v
  rw [inner_sub_left,inner_fderiv_gradient,inner_gradient_left,inner_gradient_left]
  have h := fderiv_linearDirectional_apply (ContinuousLinearMap.id ℝ (X dim)) u.2 z v
  simp only [ContinuousLinearMap.id_apply] at h
  rw [h,hSym]
  ring

/-- The rotated flux derivative is the sum of the flux of the rotated
solution and the flux of the matrix coefficient variation. -/
theorem linearDirectional_smoothBallFlux_sub_rotation (i j : Fin dim)
    {a : X dim → Mat dim} (ha : ContDiff ℝ ∞ a) (u : SmoothData dim) (z : X dim) :
    let J := ballRotationGeneratorL i j
    fderiv ℝ (smoothBallFlux a u.1) z (J z)-J (smoothBallFlux a u.1 z) =
      smoothBallFlux a (sphereRotationDerivative i j u.1) z+smoothBallFlux (ballRotationCoefficient i j a) u.1 z := by
  let J := ballRotationGeneratorL i j
  let L := divergenceMatrixOperatorL dim
  let A := L ∘ a
  have hA : ContDiff ℝ ∞ A := L.contDiff.comp ha
  have hu : ContDiff ℝ ∞ (gradient u.1) := u.2.gradient_right (by simp)
  have hf : smoothBallFlux a u.1 = fun z => A z (gradient u.1 z) :=
    funext (smoothBallFlux_eq_gradient a u.1)
  change fderiv ℝ (smoothBallFlux a u.1) z (J z)-J (smoothBallFlux a u.1 z) = _
  rw [hf]
  have h := congrArg (fun P : X dim →L[ℝ] X dim => P (J z))
    ((((hA.differentiable (by simp) z).hasFDerivAt).clm_apply
      (hu.differentiable (by simp) z).hasFDerivAt).fderiv)
  simp only [_root_.add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply] at h
  rw [h,fderiv_gradient_along_rotation i j u]
  rw [smoothBallFlux_eq_gradient,smoothBallFlux_eq_gradient]
  have h' := (L.hasFDerivAt.comp z (ha.differentiable (by simp) z).hasFDerivAt).fderiv
  change fderiv ℝ A z = _ at h'
  rw [h']
  have hP : L (ballRotationCoefficient i j a z) =
      L (fderiv ℝ a z (J z))+(A z).comp J-J.comp (A z) := by
    unfold ballRotationCoefficient
    simp only [L,map_sub,map_add,divergenceMatrixOperatorL_mul,divergenceMatrixOperatorL_coordinateMatrix]
    rfl
  change _ = L (a z) (gradient (sphereRotationDerivative i j u.1) z)+L (ballRotationCoefficient i j a z) (gradient u.1 z)
  rw [hP]
  simp only [ContinuousLinearMap.comp_apply,_root_.add_apply,_root_.sub_apply,map_add,A,Function.comp_apply,J]
  abel

private def coordinateTraceL (dim : ℕ) : (X dim →L[ℝ] X dim) →L[ℝ] ℝ :=
  ∑ k : Fin dim, (EuclideanSpace.proj (𝕜 := ℝ) k).comp
    (ContinuousLinearMap.apply ℝ (X dim) (axis k))

private theorem coordinateTraceL_eq_trace (L : X dim →L[ℝ] X dim) :
    coordinateTraceL dim L = Matrix.trace (coordinateMatrix L) := by
  unfold coordinateTraceL Matrix.trace
  simp only [_root_.sum_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.apply_apply,
    PiLp.proj_apply,Matrix.diag_apply,coordinateMatrix_apply]

private theorem coordinateTraceL_comp_comm (L M : X dim →L[ℝ] X dim) :
    coordinateTraceL dim (L.comp M) = coordinateTraceL dim (M.comp L) := by
  rw [coordinateTraceL_eq_trace,coordinateTraceL_eq_trace,coordinateMatrix_comp,coordinateMatrix_comp,Matrix.trace_mul_comm]

private theorem coordinateFluxDivergence_eq_coordinateTrace {F : X dim → X dim}
    (hF : Differentiable ℝ F) :
    coordinateFluxDivergence F = coordinateTraceL dim ∘ fderiv ℝ F := by
  funext z
  unfold coordinateFluxDivergence coordinateTraceL
  rw [Function.comp_apply]
  simp only [_root_.sum_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.apply_apply,PiLp.proj_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun L : X dim →L[ℝ] ℝ => L (axis i))
    (((EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp z (hF z).hasFDerivAt).fderiv)

theorem coordinateFluxDivergence_add {F G : X dim → X dim}
    (hF : Differentiable ℝ F) (hG : Differentiable ℝ G) (z : X dim) :
    coordinateFluxDivergence (F+G) z =
      coordinateFluxDivergence F z+coordinateFluxDivergence G z := by
  rw [coordinateFluxDivergence_eq_coordinateTrace (hF.add hG),
    coordinateFluxDivergence_eq_coordinateTrace hF,coordinateFluxDivergence_eq_coordinateTrace hG]
  simp only [Function.comp_apply,fderiv_add (hF z) (hG z),map_add]

/-- Differentiating a flux under a linear change of coordinates commutes
with divergence after differentiating the vector frame. -/
theorem coordinateFluxDivergence_linearDirectional_sub (J : X dim →L[ℝ] X dim)
    {F : X dim → X dim} (hF : ContDiff ℝ ∞ F) (z : X dim) :
    coordinateFluxDivergence (fun x => fderiv ℝ F x (J x)-J (F x)) z =
      fderiv ℝ (coordinateFluxDivergence F) z (J z) := by
  let G (x : X dim) := fderiv ℝ F x (J x)-J (F x)
  have hDiff : ContDiff ℝ ∞ G :=
    ((hF.fderiv_right (m := ∞) (by simp)).clm_apply J.contDiff).sub (J.contDiff.comp hF)
  change coordinateFluxDivergence G z = _
  rw [coordinateFluxDivergence_eq_coordinateTrace (hDiff.differentiable (by simp)),
    coordinateFluxDivergence_eq_coordinateTrace (hF.differentiable (by simp))]
  have hG : fderiv ℝ G z =
      fderiv ℝ (fderiv ℝ F) z (J z)+(fderiv ℝ F z).comp J-J.comp (fderiv ℝ F z) := by
    apply ContinuousLinearMap.ext
    intro v
    have hC := (J.hasFDerivAt.comp z (hF.differentiable (by simp) z).hasFDerivAt).fderiv
    have hU : DifferentiableAt ℝ (fun x => fderiv ℝ F x (J x)) z :=
      ((hF.fderiv_right (m := ∞) (by simp)).clm_apply J.contDiff).differentiable (by simp) z
    have hV : DifferentiableAt ℝ (fun x => J (F x)) z := (J.contDiff.comp hF).differentiable (by simp) z
    unfold G
    rw [fderiv_fun_sub hU hV,_root_.sub_apply,fderiv_linearDirectional_apply J hF]
    change _ - fderiv ℝ (J ∘ F) z v = _
    rw [hC]
    simp only [_root_.sub_apply,_root_.add_apply,ContinuousLinearMap.comp_apply]
    rw [(hF.contDiffAt (x := z)).isSymmSndFDerivAt (by simp) v (J z)]
  rw [Function.comp_apply,hG]
  have hf := ((coordinateTraceL dim).hasFDerivAt.comp z
    ((hF.fderiv_right (m := ∞) (by simp)).differentiable (by simp) z).hasFDerivAt).fderiv
  rw [hf,ContinuousLinearMap.comp_apply,map_sub,map_add,coordinateTraceL_comp_comm (fderiv ℝ F z) J]
  abel

theorem coordinateFluxDivergence_rotation_sub (i j : Fin dim) {F : X dim → X dim}
    (hF : ContDiff ℝ ∞ F) (z : X dim) :
    let J := ballRotationGeneratorL i j
    coordinateFluxDivergence (fun x => fderiv ℝ F x (J x)-J (F x)) z =
      sphereRotationDerivative i j (coordinateFluxDivergence F) z := by
  dsimp only
  rw [sphereRotationDerivative,← ballRotationGeneratorL_apply]
  exact coordinateFluxDivergence_linearDirectional_sub (ballRotationGeneratorL i j) hF z

/-- The angular derivative of the divergence equation separates into the
rotated solution and the rotated coefficient. -/
theorem sphereRotationDerivative_negativeBallDivergence (i j : Fin dim)
    {a : X dim → Mat dim} (ha : ContDiff ℝ ∞ a) (u : SmoothData dim) (z : X dim) :
    sphereRotationDerivative i j (negativeBallDivergence a u.1) z =
      negativeBallDivergence a (sphereRotationDerivative i j u.1) z+
      negativeBallDivergence (ballRotationCoefficient i j a) u.1 z := by
  let J := ballRotationGeneratorL i j
  let F := smoothBallFlux a u.1
  let v : SmoothData dim := ⟨sphereRotationDerivative i j u.1,
    contDiff_sphereRotationDerivative i j u.1 u.2⟩
  let G := smoothBallFlux a v.1
  let H := smoothBallFlux (ballRotationCoefficient i j a) u.1
  have hF := contDiff_smoothBallFlux ha u
  have hG := contDiff_smoothBallFlux ha v
  have hH := contDiff_smoothBallFlux (contDiff_ballRotationCoefficient i j ha) u
  have hRH : (fun x => fderiv ℝ F x (J x)-J (F x)) = G+H :=
    funext fun x => linearDirectional_smoothBallFlux_sub_rotation i j ha u x
  have hL : negativeBallDivergence a u.1 = fun x => -coordinateFluxDivergence F x := by
    funext x
    rw [coordinateFluxDivergence_smoothBallFlux,neg_neg]
  rw [hL,sphereRotationDerivative,fderiv_fun_neg]
  simp only [_root_.neg_apply]
  rw [← sphereRotationDerivative,← coordinateFluxDivergence_rotation_sub i j hF z,hRH,
    coordinateFluxDivergence_add (hG.differentiable (by simp)) (hH.differentiable (by simp))]
  change -(coordinateFluxDivergence (smoothBallFlux a v.1) z+
    coordinateFluxDivergence (smoothBallFlux (ballRotationCoefficient i j a) u.1) z) = _
  simp only [coordinateFluxDivergence_smoothBallFlux,neg_add,neg_neg,v]


end CalderonN
