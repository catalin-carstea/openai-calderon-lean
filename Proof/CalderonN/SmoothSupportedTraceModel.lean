module

public import Proof.CalderonN.SmoothSupportedFlatDegree
public import Proof.CalderonN.SmoothSupportedTraceFiberCalculus
public import Proof.CalderonN.SmoothSupportedTraceBaseAdjoint
public import Proof.CalderonN.TraceModelFiberIdentification

import Mathlib.Tactic

/-! Real raising and lowering operators on compactly supported smooth
sections. Their graph values and weighted square norms are the existing
harmonic model values. -/

public section

noncomputable section
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE OAI.AnisotropicCalderon SphereHarmonic GreenRadialTrace
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]
variable {Y : Set (X dim)}
variable {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
  {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
  {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim, ConormalTaylorSolutions A ell f)

theorem smoothSupportedTraceFiberRegular_raising (hY : IsOpen Y) (i : I dim) :
    SmoothSupportedTraceFiberRegular Y (fun _ => smoothTraceRaising (smoothTraceFlatDegree hA hEll S) i) := by
  simp only [smoothTraceRaising_eq_coordinate_rotation]
  exact ((smoothSupportedTraceFiberRegular_flatDegree hA hEll S Y).mul hY
    (smoothSupportedTraceFiberRegular_constMultiplier (smoothCoordinateData i))).sub
    (SmoothSupportedTraceFiberRegular.sum Finset.univ _ (fun j _ =>
      (smoothSupportedTraceFiberRegular_rotation j i).mul hY
        (smoothSupportedTraceFiberRegular_constMultiplier (smoothCoordinateData j))))

theorem smoothSupportedTraceFiberRegular_lowering (hY : IsOpen Y) (i : I dim) :
    SmoothSupportedTraceFiberRegular Y (fun _ => smoothTraceLowering (smoothTraceFlatDegree hA hEll S) i) := by
  simp only [smoothTraceLowering]
  exact ((smoothSupportedTraceFiberRegular_constMultiplier (smoothCoordinateData i)).mul hY
    (smoothSupportedTraceFiberRegular_flatDegree hA hEll S Y)).add
    (SmoothSupportedTraceFiberRegular.sum Finset.univ _ (fun j _ =>
      (smoothSupportedTraceFiberRegular_constMultiplier (smoothCoordinateData j)).mul hY
        (smoothSupportedTraceFiberRegular_rotation j i)))

variable (hY : IsOpen Y)

abbrev supportedFlatDegree :=
  smoothSupportedTraceFiberAction hY _ (smoothSupportedTraceFiberRegular_flatDegree hA hEll S Y)

abbrev supportedRaising (i : I dim) :=
  smoothSupportedTraceFiberAction hY _ (smoothSupportedTraceFiberRegular_raising hA hEll S hY i)

abbrev supportedLowering (i : I dim) :=
  smoothSupportedTraceFiberAction hY _ (smoothSupportedTraceFiberRegular_lowering hA hEll S hY i)

variable (D : I dim → Module.End ℝ (SmoothSupportedTraceSection Y))
  (b : I dim → X dim → ℝ) (hb : ∀ i, ContDiffOn ℝ ∞ (b i) Y)

@[expose] def supportedRaisingModel : Module.End ℝ (SmoothSupportedTraceSection Y) :=
  ∑ i, supportedRaising hA hEll S hY i *
    (D i + smoothSupportedTraceBaseMul hY (b i) (hb i) * supportedFlatDegree hA hEll S hY)

@[expose] def supportedLoweringModel : Module.End ℝ (SmoothSupportedTraceSection Y) :=
  ∑ i, supportedLowering hA hEll S hY i *
    (-D i + smoothSupportedTraceBaseMul hY (b i) (hb i) * supportedFlatDegree hA hEll S hY)

variable {g : MetricField dim} {e : Frame dim} {φ : Field dim}
  {E : HarmonicTestExpansion Y g e φ} {r : X dim → ℝ} {L : ℂ →L[ℝ] ℝ}
  (Q : AngularComponentData E r L)

variable (hH : ∀ i,D i (E.traceComponent L) = Q.horizontalTraceComponent i)
  (hB : ∀ i x, b i x • smoothTraceFlatDegree hA hEll S (smoothSupportedTraceFiberL x (E.traceComponent L)) =
    Q.coefficient i x • smoothTraceFlatDegree hA hEll S (smoothSupportedTraceFiberL x (E.traceComponent L)))

include hH hB in
theorem supportedRaisingModel_L2 (x : X dim) :
    smoothSupportedTraceL2 Q.dimensionBound (supportedRaisingModel hA hEll S hY D b hb (E.traceComponent L)) x =
      Q.raisingOutput x := by
  rw [Q.raisingOutput_eq_smoothTrace hA hEll S]
  unfold smoothSupportedTraceL2
  congr 1
  simp only [supportedRaisingModel,LinearMap.sum_apply,map_sum,Module.End.mul_apply,
    smoothSupportedTraceFiberAction_fiber,LinearMap.add_apply,map_add,smoothSupportedTraceBaseMul_fiber,
    hH,hB,AngularComponentData.modelFiberInput,one_smul]

include hH hB in
theorem supportedLoweringModel_L2 (x : X dim) :
    smoothSupportedTraceL2 Q.dimensionBound (supportedLoweringModel hA hEll S hY D b hb (E.traceComponent L)) x =
      Q.loweringOutput x := by
  rw [Q.loweringOutput_eq_smoothTrace hA hEll S]
  unfold smoothSupportedTraceL2
  congr 1
  have hNeg (v : SmoothSphereTrace dim) : (-1:ℝ) • v = -v := neg_one_smul ℝ v
  simp only [supportedLoweringModel,LinearMap.sum_apply,map_sum,Module.End.mul_apply,
    smoothSupportedTraceFiberAction_fiber,LinearMap.add_apply,map_add,smoothSupportedTraceBaseMul_fiber,
    hH,hB,AngularComponentData.modelFiberInput,hNeg,LinearMap.neg_apply,map_neg]

end CalderonN
