module

public import Proof.CalderonN.TraceCoordinateRadialCancellation
public import Proof.CalderonN.SupportedHorizontalRotationCovariance

import Proof.CalderonN.SmoothTraceRotationCovariance
import Mathlib.Tactic

/-! The horizontal part of the leading-velocity commutator is
a fiber operator made of raising factors and smooth coframe entries. -/

public section

noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxSynthPendingDepth 26
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)}
variable (hY : IsOpen Y) {K : ℝ} {g : MetricField dim} {e : Frame dim}
  (hg : Elliptic Y K g) (hK : 0 < K)
  (he : ∀ a,ContDiffOn ℝ ∞ (fun x => e x a) Y)
  (hframe : ∀ x ∈ Y,∀ i j,metricPair g x (e x i) (e x j) = if i=j then 1 else 0)

include hframe in
theorem supportedCoordinateHorizontal_comm_coordinateRaising (hn : 3 ≤ dim)
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
    {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim,ConormalTaylorSolutions A ell f) (i j : I dim) :
    let H := supportedCoordinateHorizontal hY hg hK he i
    let R := supportedCoordinateRaising hY hg he hA hEll S j
    let L := supportedRaising hA hEll S hY
    let c (a : I dim) := traceFrameCoordinate g e a j
    let hc (a : I dim) := contDiffOn_traceFrameCoordinate hg he a j
    H*R-R*H =
      (∑ a : I dim,
        ((smoothSupportedTraceBaseMul hY (coordDeriv i (c a))
          (((hc a).fderiv_of_isOpen (m:=∞) hY (by simp)).clm_apply contDiffOn_const))*L a+
        (smoothSupportedTraceBaseMul hY (c a) (hc a))*
          (∑ b : I dim,smoothSupportedTraceBaseMul hY
            (fun x => frameConnectionCoefficient g e x (axis i) a b)
            (hg.contDiffOn_frameConnection hY hK e he _ contDiffOn_const a b)*L b))) := by
  dsimp only
  let H := supportedCoordinateHorizontal hY hg hK he i
  let L := supportedRaising hA hEll S hY
  let c (a : I dim) := traceFrameCoordinate g e a j
  let hc (a : I dim) := contDiffOn_traceFrameCoordinate hg he a j
  let C (a : I dim) := smoothSupportedTraceBaseMul hY (c a) (hc a)
  let D (a : I dim) := smoothSupportedTraceBaseMul hY (coordDeriv i (c a))
    (((hc a).fderiv_of_isOpen (m:=∞) hY (by simp)).clm_apply contDiffOn_const)
  let Γ (a b : I dim) := smoothSupportedTraceBaseMul hY
    (fun x => frameConnectionCoefficient g e x (axis i) a b)
    (hg.contDiffOn_frameConnection hY hK e he _ contDiffOn_const a b)
  have hC (a : I dim) : H*C a-C a*H = D a :=
    supportedCoordinateHorizontal_comm_scalar hY hg hK he (c a) (hc a) i
  have hH (a : I dim) : H*L a-L a*H = ∑ b : I dim,Γ a b*L b :=
    supportedHorizontal_comm_rotating_family hY hg hK he hframe _ contDiffOn_const _
      (smoothSupportedTraceFiberRegular_raising hA hEll S hY)
      (supportedRaising_comm_base hn hA hEll S hY)
      (smoothTraceRaising_rotation_comm hn hA hEll S) a
  change H*(∑ a : I dim,C a*L a)-(∑ a : I dim,C a*L a)*H =
    ∑ a : I dim,(D a*L a+C a*(∑ b : I dim,Γ a b*L b))
  rw [Finset.mul_sum,Finset.sum_mul,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [← hC a,← hH a]
  noncomm_ring

end CalderonN
