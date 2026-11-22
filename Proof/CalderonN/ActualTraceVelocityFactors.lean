module

public import Proof.CalderonN.PairedTraceFiberFamilyBounds
public import Proof.CalderonN.ActualQuadraticVelocityIdentity
public import Proof.CalderonN.ActualSupportedLowerOrderVelocity

import Proof.CalderonN.ActualLowerOrderVelocity
import Proof.CalderonN.ActualSupportedAffineRegular
import Mathlib.Tactic

/-! The velocity remainder in the principal perturbation is the
small radius times an order-one angular family. Its normalized
formula uses the second reciprocal remainder. -/

public section

noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 5200000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)}

structure ActualTraceVelocityFactors (hn : 3 ≤ dim) (Y : Set (X dim)) where
  degree : PairedTraceFiberFamily hn Y
  rotations : I dim → I dim → PairedTraceFiberFamily hn Y
  radius : PairedTraceFiberFamily hn Y
  half : PairedTraceFiberFamily hn Y
  densityLinear : PairedTraceFiberFamily hn Y
  reciprocal : PairedTraceFiberFamily hn Y
  reciprocalLinear : PairedTraceFiberFamily hn Y
  reciprocalQuadratic : PairedTraceFiberFamily hn Y
  conormalQuadratic : PairedTraceFiberFamily hn Y
  translation : I dim → PairedTraceFiberFamily hn Y
  centerNormal : I dim → PairedTraceFiberFamily hn Y
  centerAngular : I dim → I dim → I dim → PairedTraceFiberFamily hn Y

namespace ActualTraceVelocityFactors

variable {hn : 3 ≤ dim}

@[expose] def firstConormal (hY : IsOpen Y) (F : ActualTraceVelocityFactors hn Y) :
    PairedTraceFiberFamily hn Y :=
  F.half.mul hY (((F.densityLinear.mul hY F.degree).add (F.degree.mul hY F.densityLinear)).sub F.densityLinear)

@[expose] def affine (hY : IsOpen Y) (F : ActualTraceVelocityFactors hn Y) (i : I dim) :
    PairedTraceFiberFamily hn Y :=
  ((F.firstConormal hY).sub (F.degree.mul hY F.densityLinear)).mul hY (F.translation i)

@[expose] def normalResponse (hY : IsOpen Y) (F : ActualTraceVelocityFactors hn Y) :
    PairedTraceFiberFamily hn Y :=
  F.degree.add (F.radius.mul hY ((F.degree.mul hY F.reciprocalLinear).add
    (((F.firstConormal hY).add (F.radius.mul hY F.conormalQuadratic)).mul hY F.reciprocal)))

@[expose] def responseRemainder (hY : IsOpen Y) (F : ActualTraceVelocityFactors hn Y) :
    PairedTraceFiberFamily hn Y :=
  ((F.degree.mul hY F.reciprocalQuadratic).add ((F.firstConormal hY).mul hY F.reciprocalLinear)).add
    (F.conormalQuadratic.mul hY F.reciprocal)

@[expose] def velocityRemainder (hY : IsOpen Y) (F : ActualTraceVelocityFactors hn Y) (i : I dim) :
    PairedTraceFiberFamily hn Y :=
  (((F.responseRemainder hY).mul hY (F.translation i)).add
    ((F.normalResponse hY).mul hY (F.centerNormal i))).sub
      (PairedTraceFiberFamily.finiteSum Finset.univ (fun a =>
        PairedTraceFiberFamily.finiteSum Finset.univ (fun b => (F.rotations a b).mul hY (F.centerAngular i a b))))

@[expose] def lowerVelocity (hY : IsOpen Y) (F : ActualTraceVelocityFactors hn Y) (i : I dim) :
    PairedTraceFiberFamily hn Y :=
  (F.affine hY i).add (F.radius.mul hY (F.velocityRemainder hY i))

structure Matches (F : ActualTraceVelocityFactors hn Y) {d : Data dim} {x : X dim}
    (D : ActualGaussFiberData d x) : Prop where
  degree : F.degree.forward.1 x = D.flatDegree
  rotations : ∀ i j,(F.rotations i j).forward.1 x = smoothSphereTraceRotation i j
  radius : F.radius.forward.1 x = d.radius x • 1
  half : F.half.forward.1 x = (1/2:ℝ) • 1
  densityLinear : F.densityLinear.forward.1 x = ActualGaussFiberData.affineDensityMul d x
  reciprocal : F.reciprocal.forward.1 x = smoothSphereTraceMul D.reciprocal
  reciprocalLinear : F.reciprocalLinear.forward.1 x =
    (d.radius x)⁻¹ • (smoothSphereTraceMul D.reciprocal-1)
  reciprocalQuadratic : F.reciprocalQuadratic.forward.1 x =
    ((d.radius x)^2)⁻¹ • (smoothSphereTraceMul D.reciprocal-1+d.radius x • ActualGaussFiberData.affineDensityMul d x)
  conormalQuadratic : F.conormalQuadratic.forward.1 x = ((d.radius x)^2)⁻¹ • D.conormalRemainder
  translation : ∀ i,(F.translation i).forward.1 x =
    ActualGaussFiberData.translationMultiplier d x i+fderiv ℝ d.radius x (axis i) • 1
  centerNormal : ∀ i,(F.centerNormal i).forward.1 x = smoothSphereTraceMul (smoothVelocityNormal (D.centerCorrection i))
  centerAngular : ∀ i a b,(F.centerAngular i a b).forward.1 x =
    smoothSphereTraceMul (smoothVelocityAngular (D.centerCorrection i) a b)

section Matches
variable {d : Data dim} {x : X dim} {D : ActualGaussFiberData d x} {F : ActualTraceVelocityFactors hn Y}
variable (hY : IsOpen Y) (h : F.Matches D)
include h

theorem Matches.firstConormal_eq :
    (F.firstConormal hY).forward.1 x = D.affineCorrection+D.flatDegree*ActualGaussFiberData.affineDensityMul d x := by
  have ha := D.affineCorrection_eq hn D.smoothCoefficient D.ellipticCoefficient D.solve
  dsimp only at ha
  simp only [firstConormal,PairedTraceFiberFamily.mul,PairedTraceFiberFamily.add,PairedTraceFiberFamily.sub,
    RegularTraceFiberFamily.mul,RegularTraceFiberFamily.add,RegularTraceFiberFamily.sub,
    h.half,h.degree,h.densityLinear,smul_mul_assoc,one_mul,ha]
  module

theorem Matches.affine_eq (i : I dim) :
    (F.affine hY i).forward.1 x =
      D.affineCorrection*(ActualGaussFiberData.translationMultiplier d x i+fderiv ℝ d.radius x (axis i) • 1) := by
  simp only [affine,PairedTraceFiberFamily.mul,PairedTraceFiberFamily.sub,
    RegularTraceFiberFamily.mul,RegularTraceFiberFamily.sub,h.firstConormal_eq hY,h.translation,
    h.degree,h.densityLinear]
  noncomm_ring

theorem Matches.normalResponse_eq (hr : d.radius x ≠ 0) :
    (F.normalResponse hY).forward.1 x = D.normalResponse := by
  simp only [normalResponse,PairedTraceFiberFamily.mul,PairedTraceFiberFamily.add,
    RegularTraceFiberFamily.mul,RegularTraceFiberFamily.add,h.firstConormal_eq hY,h.radius,h.degree,
    h.reciprocal,h.reciprocalLinear,h.conormalQuadratic,smul_mul_assoc,one_mul]
  exact (D.normalResponse_eq_flat_add_firstDifference hr).symm

theorem Matches.responseRemainder_eq (hr : d.radius x ≠ 0) :
    (F.responseRemainder hY).forward.1 x = D.responseRemainder := by
  simp only [responseRemainder,PairedTraceFiberFamily.mul,PairedTraceFiberFamily.add,
    RegularTraceFiberFamily.mul,RegularTraceFiberFamily.add,h.firstConormal_eq hY,h.degree,
    h.reciprocal,h.reciprocalLinear,h.reciprocalQuadratic,h.conormalQuadratic]
  exact (D.responseRemainder_eq_firstDifference hr).symm

theorem Matches.velocityRemainder_eq (hr : d.radius x ≠ 0) (i : I dim) :
    (F.velocityRemainder hY i).forward.1 x = D.velocityRemainder i := by
  simp only [velocityRemainder,PairedTraceFiberFamily.mul,PairedTraceFiberFamily.add,PairedTraceFiberFamily.sub,
    PairedTraceFiberFamily.finiteSum,RegularTraceFiberFamily.finiteSum,
    RegularTraceFiberFamily.mul,RegularTraceFiberFamily.add,RegularTraceFiberFamily.sub,
    h.responseRemainder_eq hY hr,h.normalResponse_eq hY hr,h.translation,h.centerNormal,h.rotations,h.centerAngular]
  rfl

theorem Matches.lowerVelocity_eq (hr : d.radius x ≠ 0) (i : I dim) :
    (F.lowerVelocity hY i).forward.1 x =
      D.affineCorrection*(ActualGaussFiberData.translationMultiplier d x i+fderiv ℝ d.radius x (axis i) • 1)+
        d.radius x • D.velocityRemainder i := by
  simp only [lowerVelocity,PairedTraceFiberFamily.mul,PairedTraceFiberFamily.add,RegularTraceFiberFamily.mul,
    RegularTraceFiberFamily.add,h.affine_eq hY,h.radius,h.velocityRemainder_eq hY hr,smul_mul_assoc,one_mul]

end Matches

end ActualTraceVelocityFactors

end CalderonN
