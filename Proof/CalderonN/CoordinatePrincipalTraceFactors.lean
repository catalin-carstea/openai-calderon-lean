module

public import Proof.CalderonN.CoordinateTraceModelFactors
public import Proof.CalderonN.ActualTraceVelocityFactors
public import Proof.CalderonN.MovingTracePerturbationBaseNormal

import Mathlib.Tactic

/-! Radius cancellations in the principal perturbation. The
coefficient formulas use the normalized angular velocity directly,
without differentiating inverse powers of the radius. -/

public section

noncomputable section
open Set
set_option autoImplicit false
set_option maxHeartbeats 4600000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)} {hn : 3 ≤ dim}

structure CoordinatePrincipalTraceFactors (hn : 3 ≤ dim) (Y : Set (X dim)) where
  principal : I dim → I dim → PairedTraceFiberFamily hn Y
  principalDerivative : I dim → I dim → I dim → PairedTraceFiberFamily hn Y
  smallDifference : I dim → I dim → PairedTraceFiberFamily hn Y
  density : I dim → PairedTraceFiberFamily hn Y
  radius : PairedTraceFiberFamily hn Y
  model : CoordinateTraceModelFactors hn Y
  velocity : ActualTraceVelocityFactors hn Y

namespace CoordinatePrincipalTraceFactors

@[expose] def firstNormalEntry (hY : IsOpen Y) (F : CoordinatePrincipalTraceFactors hn Y)
    (i j k : I dim) : PairedTraceFiberFamily hn Y :=
  ((F.principal i j).mul hY ((F.model.potential hY k).add (F.velocity.lowerVelocity hY k))).add
    (((F.radius.mul hY (F.smallDifference i j)).mul hY (F.model.leading hY k)))

@[expose] def firstNormal (hY : IsOpen Y) (F : CoordinatePrincipalTraceFactors hn Y) (i : I dim) :
    PairedTraceFiberFamily hn Y :=
  (PairedTraceFiberFamily.finiteSum Finset.univ (fun j => F.firstNormalEntry hY i j j)).add
    (PairedTraceFiberFamily.finiteSum Finset.univ (fun j => F.firstNormalEntry hY j i j))

@[expose] def densityAdjustment (hY : IsOpen Y) (F : CoordinatePrincipalTraceFactors hn Y) (i : I dim) :
    PairedTraceFiberFamily hn Y :=
  PairedTraceFiberFamily.finiteSum Finset.univ (fun j =>
    (F.principalDerivative j j i).add ((F.density j).mul hY (F.principal j i)))

@[expose] def first (hY : IsOpen Y) (F : CoordinatePrincipalTraceFactors hn Y) (i : I dim) :
    PairedTraceFiberFamily hn Y :=
  (F.firstNormal hY i).sub (F.densityAdjustment hY i)

@[expose] def zeroNormalizedEntry (hY : IsOpen Y) (F : CoordinatePrincipalTraceFactors hn Y)
    (i j : I dim) : PairedTraceFiberFamily hn Y :=
  let R := F.model.leading hY
  let K := F.model.potential hY
  let G := F.velocity.velocityRemainder hY
  let W := F.velocity.lowerVelocity hY
  let dK := F.model.potentialDerivative hY
  let H := F.smallDifference i j
  (((H.mul hY (R i)).mul hY (R j)).add
    ((F.radius.mul hY H).mul hY (((R i).mul hY (K j)).add ((R j).mul hY (K i))))).add
    ((F.principal i j).mul hY
      ((((((((R i).mul hY (G j)).add ((G i).mul hY (R j))).add ((K i).mul hY (K j))).add
        ((W j).mul hY (K i))).add ((W i).mul hY (K j))).add ((W i).mul hY (W j))).add (dK i j)))

@[expose] def zero (hY : IsOpen Y) (F : CoordinatePrincipalTraceFactors hn Y) : PairedTraceFiberFamily hn Y :=
  PairedTraceFiberFamily.finiteSum Finset.univ (fun i =>
    PairedTraceFiberFamily.finiteSum Finset.univ (fun j => F.zeroNormalizedEntry hY i j))

@[expose] def divergence (hY : IsOpen Y) (F : CoordinatePrincipalTraceFactors hn Y) :
    CoordinateTraceDivergence hn Y :=
  ⟨fun i => (F.density i).forward,fun i j => (F.principal i j).neg,F.first hY,F.zero hY⟩

end CoordinatePrincipalTraceFactors

end CalderonN
