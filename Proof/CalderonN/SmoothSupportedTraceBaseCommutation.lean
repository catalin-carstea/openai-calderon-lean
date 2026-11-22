module

public import Proof.CalderonN.SmoothSupportedTraceHorizontal
public import Proof.CalderonN.SmoothTraceRotationGraph

import Mathlib.Tactic

/-! Coordinate differentiation commutes with the constant harmonic
operators acting on the common smooth domain. Spectral testing uses
each bounded harmonic projection individually. -/

public section

noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 2300000
set_option maxSynthPendingDepth 23
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE OAI.AnisotropicCalderon SphereHarmonic
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)}

theorem smoothSupportedTraceSection_ext_by_fibers {u v : SmoothSupportedTraceSection Y}
    (h : ∀ x ∈ Y, smoothSupportedTraceFiberL x u = smoothSupportedTraceFiberL x v) : u = v := by
  apply Subtype.ext
  funext ⟨x,z⟩
  by_cases hx : x ∈ Y
  · exact congrArg (fun w : SmoothSphereTrace dim => w.1 z) (h x hx)
  · exact (congrArg (fun w : SmoothSphereTrace dim => w.1 z) (smoothSupportedTraceFiberL_zero_off u hx)).trans
      (congrArg (fun w : SmoothSphereTrace dim => w.1 z) (smoothSupportedTraceFiberL_zero_off v hx)).symm

theorem smoothSupportedTraceL2_injective (hn : 3 ≤ dim) :
    Function.Injective (smoothSupportedTraceL2 (Y:=Y) hn) := by
  intro u v h
  apply smoothSupportedTraceSection_ext_by_fibers
  intro x _
  apply smoothSphereTraceL2_injective hn
  exact congrFun h x

theorem harmonicProjection_smoothSphereTraceRotation (hn : 3 ≤ dim)
    (i j : I dim) (u : SmoothSphereTrace dim) (k : ℕ) :
    harmonicProjection k (smoothSphereTraceL2 hn (smoothSphereTraceRotation i j u)) =
      harmonicSphereRotation k i j (harmonicProjection k (smoothSphereTraceL2 hn u)) := by
  have h := smoothSphereTraceSobolev_rotate_coordinate hn 0 (by norm_num) i j u k
  simpa only [smoothSphereTraceSobolev_coordinate,besselWeight,Real.rpow_zero,one_smul] using h

theorem supportedConstantFiber_comm_base
    (hn : 3 ≤ dim) (hY : IsOpen Y) (T : Module.End ℝ (SmoothSphereTrace dim))
    (hT : SmoothSupportedTraceFiberRegular Y (fun _ => T))
    (P : ∀ k, SphereL2 dim →L[ℝ] harmonicSphereSubspace dim k)
    (hP : ∀ k u, harmonicProjection k (smoothSphereTraceL2 hn (T u)) =
      P k (smoothSphereTraceL2 hn u))
    (a : X dim) :
    let S := smoothSupportedTraceFiberAction hY (fun _ => T) hT
    smoothSupportedTraceBaseDiff a * S = S * smoothSupportedTraceBaseDiff a := by
  dsimp only
  let S := smoothSupportedTraceFiberAction hY (fun _ => T) hT
  let D := smoothSupportedTraceBaseDiff (Y:=Y) a
  change D*S = S*D
  ext u : 1
  apply smoothSupportedTraceL2_injective hn
  funext x
  apply sphereHarmonicDecomposition.injective
  apply lp.ext
  funext k
  rw [sphereHarmonicDecomposition_apply,sphereHarmonicDecomposition_apply]
  have hComm (v : SmoothSupportedTraceSection Y) (y : X dim) :
      harmonicProjection k (smoothSupportedTraceL2 hn (S v) y) =
        P k (smoothSupportedTraceL2 hn v y) := by
    rw [smoothSupportedTraceL2,smoothSupportedTraceFiberAction_fiber,hP,smoothSupportedTraceL2]
  have hF := congrArg (fun G : X dim → harmonicSphereSubspace dim k => fderiv ℝ G x a)
    (funext (hComm u))
  have hSu := (contDiff_smoothSupportedTraceL2 hn (S u)).differentiable (by simp) x
  have hu := (contDiff_smoothSupportedTraceL2 hn u).differentiable (by simp) x
  change (fderiv ℝ (harmonicProjection k ∘ smoothSupportedTraceL2 hn (S u)) x) a =
    (fderiv ℝ (P k ∘ smoothSupportedTraceL2 hn u) x) a at hF
  rw [((harmonicProjection k).hasFDerivAt.comp x hSu.hasFDerivAt).fderiv,
    ((P k).hasFDerivAt.comp x hu.hasFDerivAt).fderiv,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply,
    fderiv_smoothSupportedTraceL2,fderiv_smoothSupportedTraceL2] at hF
  change harmonicProjection k (smoothSupportedTraceL2 hn (D (S u)) x) =
    harmonicProjection k (smoothSupportedTraceL2 hn (S (D u)) x)
  rw [hComm]
  exact hF

theorem supportedRotation_comm_base (hn : 3 ≤ dim) (hY : IsOpen Y) (i j : I dim) (a : X dim) :
    smoothSupportedTraceBaseDiff a * supportedRotation hY i j =
      supportedRotation hY i j * smoothSupportedTraceBaseDiff a := by
  apply supportedConstantFiber_comm_base hn hY _ _ (fun k => (harmonicSphereRotation k i j).comp (harmonicProjection k))
  exact fun k u => harmonicProjection_smoothSphereTraceRotation hn i j u k

variable (hn : 3 ≤ dim) {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
  {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
  {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim, ConormalTaylorSolutions A ell f)
  (hY : IsOpen Y)

include hn in
theorem supportedLowering_comm_base (i : I dim) (a : X dim) :
    smoothSupportedTraceBaseDiff a * supportedLowering hA hEll S hY i =
      supportedLowering hA hEll S hY i * smoothSupportedTraceBaseDiff a := by
  apply supportedConstantFiber_comm_base hn hY _ _
    (fun k => (harmonicDerivative (sphereFischerInner dim) k i).comp (harmonicProjection (k+1)))
  exact fun k u => harmonicProjection_smoothTraceLowering hn hA hEll S i k u

include hn in
theorem supportedRaising_comm_base (i : I dim) (a : X dim) :
    smoothSupportedTraceBaseDiff a * supportedRaising hA hEll S hY i =
      supportedRaising hA hEll S hY i * smoothSupportedTraceBaseDiff a := by
  apply supportedConstantFiber_comm_base hn hY _ _
    (fun k => match k with
      | 0 => 0
      | k+1 => (harmonicDerivativeAdjoint (sphereFischerInner dim) k i).comp (harmonicProjection k))
  intro k u
  cases k with
  | zero => exact harmonicProjection_smoothTraceRaising_zero hn hA hEll S i u
  | succ k => exact harmonicProjection_smoothTraceRaising_succ hn hA hEll S i k u

include hn in
theorem supportedFlatDegree_comm_base (a : X dim) :
    smoothSupportedTraceBaseDiff a * supportedFlatDegree hA hEll S hY =
      supportedFlatDegree hA hEll S hY * smoothSupportedTraceBaseDiff a := by
  apply supportedConstantFiber_comm_base hn hY _ _ (fun k => (k:ℝ) • harmonicProjection k)
  exact fun k u => smoothTraceDegree_projection (smoothTraceFlatDegree_symmetric hn hA hEll S)
    (smoothTraceFlatDegree_finite hA hEll S) u k

end CalderonN
