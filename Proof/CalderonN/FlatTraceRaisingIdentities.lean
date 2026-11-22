module

public import Proof.CalderonN.FlatTraceRaisingAdjoint
public import Proof.CalderonN.SmoothTraceDegreeSpectral

import Proof.CalderonN.SmoothAngularCasimir
import Mathlib.Tactic

/-! The exact degree shift and Euclidean double-raising cancellation
hold on smooth traces, as well as on the harmonic blocks. -/

public section

noncomputable section
open Set MvPolynomial
open scoped ContDiff Matrix.Norms.Elementwise Classical
set_option autoImplicit false
set_option maxHeartbeats 4800000
set_option maxSynthPendingDepth 25
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE OAI.AnisotropicCalderon SphereHarmonic AngularPolynomial
  GreenRadialTrace SmoothSphereRotation
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem smoothHarmonicSingle_polynomial (hn : 3 ≤ dim) (k : ℕ) (p : harmonicHomogeneous dim k) :
    smoothHarmonicSingle k (harmonicPolynomialSphereMap k p) =
      smoothSphereTrace (smoothPolynomialData p) := by
  apply smoothSphereTraceL2_injective hn
  rw [smoothSphereTraceL2_harmonicSingle,smoothSphereTraceL2_apply]
  exact (smoothSphereLift_polynomialEvaluation (p : MvPolynomial (Fin dim) ℝ)).symm

variable (hn : 3 ≤ dim) {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
  {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
  {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim, ConormalTaylorSolutions A ell f)

include hn

theorem smoothTraceRaising_harmonicSingle (k : ℕ) (i : Fin dim) (v : harmonicSphereSubspace dim k) :
    smoothTraceRaising (smoothTraceFlatDegree hA hEll S) i (smoothHarmonicSingle k v) =
      smoothHarmonicSingle (k+1) (harmonicDerivativeAdjoint (sphereFischerInner dim) k i v) := by
  obtain ⟨p,rfl⟩ := harmonicPolynomialSphereMap_surjective k v
  rw [smoothHarmonicSingle_polynomial hn,harmonicDerivativeAdjoint_apply_image]
  have h := smoothSphereGaussAdjoint_flat_axis_homogeneous hn hA hEll S k i p p.property
  change smoothTraceRaising (smoothTraceFlatDegree hA hEll S) i
    (smoothSphereTrace (smoothPolynomialData p)) =
      smoothSphereTrace (smoothPolynomialData (sphereDerivativeAdjoint k i p)) at h
  have hv : harmonicPolynomialDerivativeAdjointMap k i p =
      harmonicPolynomialSphereMap (k+1) ⟨sphereDerivativeAdjoint k i p,
        sphereDerivativeAdjoint_harmonicHomogeneous k i p p.property⟩ := rfl
  rw [hv,smoothHarmonicSingle_polynomial hn]
  exact h

theorem smoothTraceLowering_harmonicSingle_succ (k : ℕ) (i : Fin dim) (v : harmonicSphereSubspace dim (k+1)) :
    smoothTraceLowering (smoothTraceFlatDegree hA hEll S) i (smoothHarmonicSingle (k+1) v) =
      smoothHarmonicSingle k (harmonicDerivative (sphereFischerInner dim) k i v) := by
  obtain ⟨p,rfl⟩ := harmonicPolynomialSphereMap_surjective (k+1) v
  rw [smoothHarmonicSingle_polynomial hn,harmonicDerivative_apply_image,
    smoothTraceLowering_polynomial hA hEll S _ _ _ p.property]
  have hv : harmonicPolynomialDerivativeMap k i p =
      harmonicPolynomialSphereMap k ⟨pderiv i (p : MvPolynomial (Fin dim) ℝ),
        pderiv_harmonicHomogeneous_succ k i p p.property⟩ := rfl
  rw [hv,smoothHarmonicSingle_polynomial hn]

theorem smoothTraceLowering_harmonicSingle_zero (i : Fin dim) (v : harmonicSphereSubspace dim 0) :
    smoothTraceLowering (smoothTraceFlatDegree hA hEll S) i (smoothHarmonicSingle 0 v) = 0 := by
  obtain ⟨p,rfl⟩ := harmonicPolynomialSphereMap_surjective 0 v
  rw [smoothHarmonicSingle_polynomial hn,smoothTraceLowering_polynomial hA hEll S _ _ _ p.property,
    eq_C_of_mem_harmonicHomogeneous_zero p.property,pderiv_C]
  apply Subtype.ext
  funext z
  simp [smoothSphereTrace_apply,smoothPolynomialData,polynomialEvaluation]

theorem smoothTraceDegree_comm_raising (i : Fin dim) :
    let B := smoothTraceFlatDegree hA hEll S
    let R := smoothTraceRaising B i
    B*R-R*B = R := by
  dsimp only
  let B := smoothTraceFlatDegree hA hEll S
  let R := smoothTraceRaising B i
  let L := smoothTraceLowering B i
  have hB := smoothTraceFlatDegree_symmetric hn hA hEll S
  have hR : SmoothTraceAdjoint hn R L := smoothTraceRaising_adjoint hn B hB i
  have hComm : SmoothTraceAdjoint hn (B*R-R*B) (L*B-B*L) := (hB.mul hR).sub (hR.mul hB)
  apply SmoothTraceAdjoint.eq_of_finite hComm hR
  have hEq : (B*R-R*B).comp finiteHarmonicSmoothTraceL = R.comp finiteHarmonicSmoothTraceL := by
    ext k v : 2
    change B (R (smoothHarmonicSingle k v))-R (B (smoothHarmonicSingle k v)) = R (smoothHarmonicSingle k v)
    simp only [B,R,smoothTraceDegree_harmonicSingle (smoothTraceFlatDegree_finite hA hEll S),
      smoothTraceRaising_harmonicSingle hn hA hEll S,map_smul,← sub_smul]
    norm_num
  exact fun f => congrArg (fun T : HarmonicFiniteCoefficients dim →ₗ[ℝ] SmoothSphereTrace dim => T f) hEq

theorem sum_smoothTraceRaising_twice :
    let B := smoothTraceFlatDegree hA hEll S
    ∑ i : Fin dim, smoothTraceRaising B i*smoothTraceRaising B i = 0 := by
  dsimp only
  let B := smoothTraceFlatDegree hA hEll S
  let R := smoothTraceRaising B
  let L := smoothTraceLowering B
  have hB := smoothTraceFlatDegree_symmetric hn hA hEll S
  have hR i : SmoothTraceAdjoint hn (R i) (L i) := smoothTraceRaising_adjoint hn B hB i
  have hRR : SmoothTraceAdjoint hn (∑ i,R i*R i) (∑ i,L i*L i) :=
    SmoothTraceAdjoint.sum _ _ _ (fun i _ => (hR i).mul (hR i))
  have hZero : SmoothTraceAdjoint hn (0 : Module.End ℝ _) 0 := by
    intro x y
    simp only [LinearMap.zero_apply,map_zero,inner_zero_left,inner_zero_right]
  apply SmoothTraceAdjoint.eq_of_finite hRR hZero
  have hEq : (∑ i,R i*R i).comp finiteHarmonicSmoothTraceL = (0 : Module.End ℝ _).comp finiteHarmonicSmoothTraceL := by
    ext k v : 2
    simp only [LinearMap.comp_apply,LinearMap.sum_apply,Module.End.mul_apply,LinearMap.zero_apply]
    change (∑ i,R i (R i (smoothHarmonicSingle k v))) = 0
    simp only [R,B,smoothTraceRaising_harmonicSingle hn hA hEll S,← map_sum,
      sum_double_harmonicDerivativeAdjoint_eq_zero,map_zero]
  exact fun f => congrArg (fun T : HarmonicFiniteCoefficients dim →ₗ[ℝ] SmoothSphereTrace dim => T f) hEq

end CalderonN
