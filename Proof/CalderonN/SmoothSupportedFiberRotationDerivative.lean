module

public import Proof.CalderonN.SmoothSupportedFiberMatrixDerivative

import Proof.CalderonN.SmoothTraceLinearAdjunction
import Mathlib.Tactic

/-! Base differentiation commutes with the commutator of a smooth
fiber family with a fixed sphere rotation. -/

public section

noncomputable section
open Set Filter
open scoped ContDiff InnerProductSpace Topology
set_option autoImplicit false
set_option maxHeartbeats 3700000
set_option maxSynthPendingDepth 26
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet OAI.AnisotropicCalderon SphereHarmonic
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)}

@[expose] def supportedFiberRotationComm (F : X dim → Module.End ℝ (SmoothSphereTrace dim))
    (i j : I dim) (y : X dim) : Module.End ℝ (SmoothSphereTrace dim) :=
  smoothSphereTraceRotation i j*F y-F y*smoothSphereTraceRotation i j

theorem supportedFiberRotationComm_regular (hY : IsOpen Y)
    (F : X dim → Module.End ℝ (SmoothSphereTrace dim)) (hF : SmoothSupportedTraceFiberRegular Y F)
    (i j : I dim) : SmoothSupportedTraceFiberRegular Y (supportedFiberRotationComm F i j) := by
  let hR := smoothSupportedTraceFiberRegular_rotation (Y:=Y) i j
  exact (hR.mul hY hF).sub (hF.mul hY hR)

theorem supportedFiberRotationComm_derivative (hn : 3 ≤ dim) (hY : IsOpen Y)
    (F : X dim → Module.End ℝ (SmoothSphereTrace dim)) (hF : SmoothSupportedTraceFiberRegular Y F)
    (i j : I dim) (a : X dim) {x : X dim} (hx : x ∈ Y) :
    smoothSupportedTraceFiberDerivative hY (supportedFiberRotationComm F i j)
        (supportedFiberRotationComm_regular hY F hF i j) a x =
      supportedFiberRotationComm (smoothSupportedTraceFiberDerivative hY F hF a) i j x := by
  let L := smoothSphereTraceL2 hn
  let R := smoothSphereTraceRotation i j
  let G := supportedFiberRotationComm F i j
  let G' := smoothSupportedTraceFiberDerivative hY G (supportedFiberRotationComm_regular hY F hF i j) a x
  let F' := smoothSupportedTraceFiberDerivative hY F hF a
  have hR := smoothTraceRotation_skew hn i j
  have hComm (D : Module.End ℝ (SmoothSphereTrace dim)) (u v : SmoothSphereTrace dim) :
      ⟪L ((R*D-D*R) u),L v⟫_ℝ = -⟪L (D u),L (R v)⟫_ℝ-⟪L (D (R u)),L v⟫_ℝ := by
    simp only [LinearMap.sub_apply,Module.End.mul_apply,map_sub,inner_sub_left]
    rw [hR (D u) v,LinearMap.neg_apply,map_neg,inner_neg_right]
  have hPair (u v : SmoothSphereTrace dim) :
      ⟪L (G' u),L v⟫_ℝ = ⟪L ((R*F' x-F' x*R) u),L v⟫_ℝ := by
    rw [← fderiv_smoothTrace_fiber_matrix_element hn hY hx G (supportedFiberRotationComm_regular hY F hF i j),
      hComm (F' x) u v]
    let p (y : X dim) := ⟪L (F y u),L (R v)⟫_ℝ
    let q (y : X dim) := ⟪L (F y (R u)),L v⟫_ℝ
    have hp := (contDiffAt_smoothTrace_fiber_matrix_element hn hY hx F hF u (R v)).differentiableAt (by simp)
    have hq := (contDiffAt_smoothTrace_fiber_matrix_element hn hY hx F hF (R u) v).differentiableAt (by simp)
    rw [show (fun y => ⟪L (G y u),L v⟫_ℝ) = -p-q from funext (fun y => hComm (F y) u v)]
    rw [fderiv_sub hp.neg hq,fderiv_neg]
    simp only [sub_apply,neg_apply,fderiv_smoothTrace_fiber_matrix_element hn hY hx F hF a]
    rfl
  ext u : 1
  apply smoothSphereTraceL2_injective hn
  let w := G' u-(R*F' x-F' x*R) u
  have h0 : ⟪L w,L w⟫_ℝ = 0 := by
    calc
      ⟪L w,L w⟫_ℝ = ⟪L (G' u),L w⟫_ℝ-⟪L ((R*F' x-F' x*R) u),L w⟫_ℝ := by
        have hL : L w = L (G' u)-L ((R*F' x-F' x*R) u) := map_sub _ _ _
        exact (congrArg (fun z : SphereL2 dim => ⟪z,L w⟫_ℝ) hL).trans (inner_sub_left _ _ _)
      _ = 0 := sub_eq_zero.mpr (hPair u w)
  have hW : L w = 0 := inner_self_eq_zero.mp h0
  exact sub_eq_zero.mp ((map_sub L _ _).symm.trans hW)

end CalderonN
