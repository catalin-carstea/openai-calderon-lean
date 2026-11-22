module

public import Proof.CalderonN.ActualTraceSections
public import Proof.CalderonN.ModelOutputLimits
public import Proof.CalderonN.SmoothTraceRaisingProjection

import Mathlib.Tactic

/-! Identification of the existing harmonic graph outputs with the
actual raising and lowering operations on the common smooth domain. -/

public section

noncomputable section
open Set
open scoped ContDiff InnerProductSpace Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE OAI.AnisotropicCalderon SphereHarmonic SmoothSphereFields
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]
variable {Y : Set (X dim)} {g : MetricField dim} {e : Frame dim} {φ : Field dim}
  {E : HarmonicTestExpansion Y g e φ} {r : X dim → ℝ} {L : ℂ →L[ℝ] ℝ}

namespace AngularComponentData

@[expose] def horizontalTraceComponent (Q : AngularComponentData E r L) (i : I dim) :
    SmoothSupportedTraceSection Y :=
  smoothSupportedTraceOfAmbient (Q.horizontalRepresentative i) (Q.horizontalSmooth i)
    E.compactSupportSet E.supportSubset (Q.horizontalZero i)

theorem horizontalTraceComponent_apply (Q : AngularComponentData E r L) (i : I dim)
    {x : X dim} (hx : x ∈ Y) (z : UnitSphere dim) :
    (Q.horizontalTraceComponent i).1 (x,z) = L (horizontal g φ x (frameVector e x z) (e x i)) :=
  Q.horizontalEq i x hx z

theorem horizontalTraceComponent_L2 (Q : AngularComponentData E r L) (i : I dim) (x : X dim) :
    smoothSupportedTraceL2 Q.dimensionBound (Q.horizontalTraceComponent i) x =
      ambientSphereL2 (Q.horizontalRepresentative i) (Q.horizontalSmooth i) x :=
  smoothSupportedTraceL2_eq_ambient Q.dimensionBound _ _ (fun _ _ => rfl) x

variable {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
  {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
  {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim, ConormalTaylorSolutions A ell f)

@[expose] def modelFiberInput (Q : AngularComponentData E r L) (i : I dim)
    (sign : ℝ) (x : X dim) : SmoothSphereTrace dim :=
  sign • smoothSupportedTraceFiberL x (Q.horizontalTraceComponent i) +
    Q.coefficient i x • smoothTraceFlatDegree hA hEll S (smoothSupportedTraceFiberL x (E.traceComponent L))

theorem harmonicProjection_modelFiberInput (Q : AngularComponentData E r L)
    (i : I dim) (sign : ℝ) (x : X dim) (k : ℕ) :
    harmonicProjection k (smoothSphereTraceL2 Q.dimensionBound (Q.modelFiberInput hA hEll S i sign x)) =
      weightedAngularComponent (Q.horizontalRepresentative i) (fun p => L (E.representative p))
        (Q.horizontalSmooth i) (L.contDiff.comp E.representativeSmooth) (Q.coefficient i) sign x k := by
  simp only [modelFiberInput,map_add,map_smul]
  rw [smoothTraceDegree_projection (smoothTraceFlatDegree_symmetric Q.dimensionBound hA hEll S)
    (smoothTraceFlatDegree_finite hA hEll S),smul_smul]
  change sign • harmonicProjection k (smoothSupportedTraceL2 Q.dimensionBound (Q.horizontalTraceComponent i) x) +
    (Q.coefficient i x*(k:ℝ)) • harmonicProjection k (smoothSupportedTraceL2 Q.dimensionBound (E.traceComponent L) x) = _
  rw [horizontalTraceComponent_L2,HarmonicTestExpansion.traceComponent_L2]
  rfl

private theorem sphereL2_ext_of_projection {u v : SphereL2 dim}
    (h : ∀ k, harmonicProjection k u = harmonicProjection k v) : u = v := by
  apply sphereHarmonicDecomposition.injective
  apply lp.ext
  funext k
  simpa only [sphereHarmonicDecomposition_apply] using h k

theorem raisingOutput_eq_smoothTrace (Q : AngularComponentData E r L) (x : X dim) :
    Q.raisingOutput x = smoothSphereTraceL2 Q.dimensionBound
      (∑ i, smoothTraceRaising (smoothTraceFlatDegree hA hEll S) i (Q.modelFiberInput hA hEll S i 1 x)) := by
  apply sphereL2_ext_of_projection
  intro k
  cases k with
  | zero =>
    rw [raisingOutput,harmonicProjection_angularRaisingSum_zero,map_sum,map_sum]
    simp only [harmonicProjection_smoothTraceRaising_zero,Finset.sum_const_zero]
  | succ k =>
    rw [raisingOutput,harmonicProjection_angularRaisingSum_succ,map_sum,map_sum]
    simp only [harmonicProjection_smoothTraceRaising_succ,harmonicProjection_modelFiberInput]

theorem loweringOutput_eq_smoothTrace (Q : AngularComponentData E r L) (x : X dim) :
    Q.loweringOutput x = smoothSphereTraceL2 Q.dimensionBound
      (∑ i, smoothTraceLowering (smoothTraceFlatDegree hA hEll S) i (Q.modelFiberInput hA hEll S i (-1) x)) := by
  apply sphereL2_ext_of_projection
  intro k
  rw [loweringOutput,harmonicProjection_angularLoweringSum,map_sum,map_sum]
  simp only [harmonicProjection_smoothTraceLowering,harmonicProjection_modelFiberInput]

end AngularComponentData

end CalderonN
