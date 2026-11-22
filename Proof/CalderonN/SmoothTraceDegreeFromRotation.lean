module

public import Proof.CalderonN.SmoothTraceFlatDegree
public import Proof.CalderonN.FiniteDoubleConormalTrace

import Proof.CalderonN.FiniteSmoothDegreeForm
import Mathlib.Tactic

/-! The same physical Sylvester bound applies to a trace operator and
to its first angular commutator once their rotation bounds are known. -/

public section

noncomputable section
open Set
open scoped ContDiff InnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 5400000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet OAI.AnisotropicCalderon SphereHarmonic SmoothSphereRotation
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem norm_smoothSphereTraceL2_eq_sobolev_zero (hn : 3 ≤ dim) (u : SmoothSphereTrace dim) :
    ‖smoothSphereTraceL2 hn u‖ = ‖smoothSphereTraceSobolev hn 0 (by norm_num) u‖ := by
  rw [← smoothSphereTrace_representative u,smoothSphereTraceL2_apply,smoothSphereTraceSobolev_apply]
  exact (norm_smoothBoundarySobolev_zero_eq hn _).symm

theorem norm_smoothTrace_degreeComm_of_rotation (hn : 3 ≤ dim)
    (B T : Module.End ℝ (SmoothSphereTrace dim))
    (hSymT : SmoothTraceAdjoint hn T T) (hSymB : SmoothTraceAdjoint hn B B)
    (hB : ∀ f, B (finiteHarmonicSmoothTraceL f) = finiteHarmonicSmoothTraceL (finiteHarmonicDegreeL f))
    (C : ℝ) (hC : 0 ≤ C)
    (hRot : ∀ (i j : Fin dim) f,‖smoothSphereTraceSobolev hn 0 (by norm_num)
      (smoothTraceAngularComm i j T (finiteHarmonicSmoothTraceL f))‖ ≤ C*‖harmonicBoundaryFiniteL 1 f‖)
    (u : SmoothSphereTrace dim) :
    ‖smoothSphereTraceSobolev hn (-(1/2):ℝ) (by norm_num) ((B*T-T*B) u)‖ ≤
      ((dim:ℝ)^4*(C+C))*‖smoothSphereTraceSobolev hn (1/2:ℝ) (by norm_num) u‖ := by
  let X := finiteHarmonicSmoothTraceL (dim:=dim)
  let L := smoothSphereTraceL2 (dim:=dim) hn
  let T₀ := L.comp (T.comp X)
  let τ (f : HarmonicFiniteCoefficients dim) := smoothSphereTraceRepresentative (T (X f))
  let P (ij : Fin dim × Fin dim) := L.comp ((smoothTraceAngularComm ij.1 ij.2 T).comp X)
  let J := (dim:ℝ)^4*(C+C)
  have hτ (f : HarmonicFiniteCoefficients dim) : T₀ f = smoothSphereLift (τ f).1 (τ f).2 := by
    change L (T (X f)) = _
    rw [← smoothSphereTrace_representative (T (X f))]
    exact smoothSphereTraceL2_apply hn (τ f)
  have hX (f : HarmonicFiniteCoefficients dim) : L (X f) = finiteHarmonicSphereL hn f := by
    dsimp only [L,X]
    rw [finiteHarmonicSmoothTraceL_apply,smoothSphereTraceL2_apply,finiteHarmonicSphereL_apply]
  have hT' (f g : HarmonicFiniteCoefficients dim) :
      ⟪T₀ f,finiteHarmonicSphereL hn g⟫_ℝ = ⟪finiteHarmonicSphereL hn f,T₀ g⟫_ℝ := by
    rw [← hX,← hX]
    exact hSymT (X f) (X g)
  have hP (ij : Fin dim × Fin dim) (f : HarmonicFiniteCoefficients dim) :
      P ij f = smoothSphereLift (sphereRotationDerivative ij.1 ij.2 (τ f).1)
        (contDiff_sphereRotationDerivative ij.1 ij.2 _ (τ f).2)-T₀ (finiteHarmonicRotationL ij.1 ij.2 f) := by
    change L (smoothSphereTraceRotation ij.1 ij.2 (T (X f))-
      T (smoothSphereTraceRotation ij.1 ij.2 (X f))) = _
    rw [map_sub,finiteHarmonicSmoothTraceL_rotation]
    congr 1
    rw [← smoothSphereTrace_representative (T (X f)),smoothSphereTraceRotation_apply]
    exact smoothSphereTraceL2_apply hn _
  have hPN (ij : Fin dim × Fin dim) (f : HarmonicFiniteCoefficients dim) :
      ‖P ij f‖ ≤ C*‖harmonicBoundaryFiniteL 1 f‖ := by
    change ‖L (smoothTraceAngularComm ij.1 ij.2 T (X f))‖ ≤ _
    rw [norm_smoothSphereTraceL2_eq_sobolev_zero]
    exact hRot ij.1 ij.2 f
  have hFin := abs_finite_smooth_degree_pair_le hn T₀ τ hτ hT' P hP C hC hPN
  let S := B*T-T*B
  have hS : SmoothTraceAdjoint hn S (-S) := by
    intro x y
    change ⟪L (B (T x)-T (B x)),L y⟫_ℝ = ⟪L x,L (-(B (T y)-T (B y)))⟫_ℝ
    simp only [map_sub,map_neg,inner_sub_left,inner_neg_right,inner_sub_right]
    have hB' : ∀ x y, ⟪L (B x),L y⟫_ℝ = ⟪L x,L (B y)⟫_ℝ := hSymB
    have hT'' : ∀ x y, ⟪L (T x),L y⟫_ℝ = ⟪L x,L (T y)⟫_ℝ := hSymT
    rw [hB' (T x) y,hT'' x (B y),hT'' (B x) y,hB' x (T y)]
    ring
  have hPair (f g : HarmonicFiniteCoefficients dim) :
      |⟪L (S (X f)),L (X g)⟫_ℝ| ≤ J*‖harmonicBoundaryFiniteL (1/2:ℝ) f‖*
        ‖harmonicBoundaryFiniteL (1/2:ℝ) g‖ := by
    change |⟪L (B (T (X f))-T (B (X f))),L (X g)⟫_ℝ| ≤ _
    have hB' : ∀ x y, ⟪L (B x),L y⟫_ℝ = ⟪L x,L (B y)⟫_ℝ := hSymB
    rw [map_sub,inner_sub_left,hB' (T (X f)) (X g)]
    have hBd (u : HarmonicFiniteCoefficients dim) : B (X u) = X (finiteHarmonicDegreeL u) := hB u
    rw [hBd f,hBd g,hX,hX]
    exact hFin f g
  have hN (f : HarmonicFiniteCoefficients dim) :
      ‖smoothSphereTraceSobolev hn (-(1/2):ℝ) (by norm_num) (S (X f))‖ ≤
        J*‖harmonicBoundaryFiniteL (1/2:ℝ) f‖ := by
    let p := smoothSphereTraceRepresentative (S (X f))
    rw [← smoothSphereTrace_representative (S (X f)),smoothSphereTraceSobolev_apply]
    apply norm_smoothBoundarySobolev_le_of_finite_tests hn (1/2:ℝ) (by norm_num) (by norm_num)
    · dsimp [J]; positivity
    · intro g
      have h := hPair f g
      rw [← smoothSphereTrace_representative (S (X f)),hX,finiteHarmonicSphereL_apply] at h
      change |⟪smoothSphereTraceL2 hn (smoothSphereTrace p),
        smoothSphereLift (harmonicFiniteSmooth g).1 (harmonicFiniteSmooth g).2⟫_ℝ| ≤ _ at h
      rw [smoothSphereTraceL2_apply,smoothSphereLift_inner] at h
      exact h
  exact norm_smoothTraceOperator_le_of_finite hn (1/2:ℝ) (-(1/2):ℝ) (by norm_num) (by norm_num) (by norm_num)
    S (-S) hS J (by dsimp [J]; positivity) hN u

end CalderonN
