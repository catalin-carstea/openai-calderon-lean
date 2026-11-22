module

public import Proof.CalderonN.SmoothSupportedTraceFiberAction
public import Proof.CalderonN.SmoothSphereTrace
import Proof.CalderonN.SmoothSphereRotation

import Mathlib.Tactic

/-! Regular scalar multipliers and rotations on supported traces, and
closure of regular fiber families under the operations used by the model. -/

public section

noncomputable section
open Set
open scoped ContDiff
set_option autoImplicit false
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet OAI.AnisotropicCalderon SmoothSphereRotation
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)}

namespace SmoothSupportedTraceFiberRegular
variable {S T : X dim → Module.End ℝ (SmoothSphereTrace dim)}

theorem add (hS : SmoothSupportedTraceFiberRegular Y S)
    (hT : SmoothSupportedTraceFiberRegular Y T) :
    SmoothSupportedTraceFiberRegular Y (fun x => S x+T x) := by
  intro u
  obtain ⟨U,F,hU,hYU,hF,hSA⟩ := hS u
  obtain ⟨V,G,hV,hYV,hG,hTA⟩ := hT u
  exact ⟨U ∩ V,F+G,hU.inter hV,subset_inter hYU hYV,
    (hF.mono inter_subset_left).add (hG.mono inter_subset_right),fun x hx z => by
      change F (x,z)+G (x,z) = _
      rw [hSA x hx z,hTA x hx z]
      rfl⟩

theorem neg (hS : SmoothSupportedTraceFiberRegular Y S) :
    SmoothSupportedTraceFiberRegular Y (fun x => -S x) := by
  intro u
  obtain ⟨U,F,hU,hYU,hF,hA⟩ := hS u
  exact ⟨U,-F,hU,hYU,hF.neg,fun x hx z => by
    change -F (x,z) = _
    rw [hA x hx z]
    rfl⟩

theorem sub (hS : SmoothSupportedTraceFiberRegular Y S)
    (hT : SmoothSupportedTraceFiberRegular Y T) :
    SmoothSupportedTraceFiberRegular Y (fun x => S x-T x) := by
  rw [show (fun x => S x-T x) = (fun x => S x + -T x) from funext (fun x => sub_eq_add_neg (S x) (T x))]
  exact hS.add hT.neg

theorem mul (hY : IsOpen Y) (hS : SmoothSupportedTraceFiberRegular Y S)
    (hT : SmoothSupportedTraceFiberRegular Y T) :
    SmoothSupportedTraceFiberRegular Y (fun x => S x*T x) := by
  intro u
  obtain ⟨U,F,hU,hYU,hF,hA⟩ := hS (smoothSupportedTraceFiberAction hY T hT u)
  refine ⟨U,F,hU,hYU,hF,fun x hx z => ?_⟩
  rw [hA x hx z,smoothSupportedTraceFiberAction_fiber]
  rfl

theorem sum {ι : Type*} (t : Finset ι)
    (S : ι → X dim → Module.End ℝ (SmoothSphereTrace dim))
    (hS : ∀ i ∈ t, SmoothSupportedTraceFiberRegular Y (S i)) :
    SmoothSupportedTraceFiberRegular Y (fun x => ∑ i ∈ t,S i x) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    intro u
    exact ⟨univ,0,isOpen_univ,subset_univ _,contDiffOn_const,fun _ _ _ => rfl⟩
  | @insert i t hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hS i (Finset.mem_insert_self _ _)).add (ih (fun j hj => hS j (Finset.mem_insert_of_mem hj)))

end SmoothSupportedTraceFiberRegular

theorem smoothSupportedTraceFiberRegular_constMultiplier (f : SmoothData dim) :
    SmoothSupportedTraceFiberRegular Y (fun _ => smoothSphereTraceMul f) := by
  intro u
  obtain ⟨G,hG,hu⟩ := smoothSupportedTraceSection_repr u
  refine ⟨univ,fun p => f.1 p.2*G p,isOpen_univ,subset_univ _,
    ((f.2.comp contDiff_snd).mul hG).contDiffOn,?_⟩
  intro x hx z
  rw [smoothSphereTraceMul_apply,smoothSupportedTraceFiberL_apply,hu x z]

theorem smoothSupportedTraceFiberRegular_rotation (i j : Fin dim) :
    SmoothSupportedTraceFiberRegular Y (fun _ => smoothSphereTraceRotation i j) := by
  intro u
  obtain ⟨G,hG,hu⟩ := smoothSupportedTraceSection_repr u
  let V (p : X dim × X dim) := ((0 : X dim),rotationVector i j p.2)
  have hV : ContDiff ℝ ∞ V :=
    contDiff_const.prodMk ((contDiff_rotationVector i j).comp contDiff_snd)
  refine ⟨univ,fun p => fderiv ℝ G p (V p),isOpen_univ,subset_univ _,
    ((hG.fderiv_right (m:=∞) (by simp)).clm_apply hV).contDiffOn,?_⟩
  intro x hx z
  let f : SmoothData dim := ⟨fun w => G (x,w),hG.comp (contDiff_const.prodMk contDiff_id)⟩
  have hF : smoothSupportedTraceFiberL x u = smoothSphereTrace f := Subtype.ext (funext (hu x))
  rw [hF,smoothSphereTraceRotation_apply,smoothSphereTrace_apply]
  change fderiv ℝ G (x,(z:X dim)) (0,rotationVector i j z) =
    fderiv ℝ (G ∘ Prod.mk x) (z:X dim) (rotationVector i j z)
  rw [((hG.differentiable (by simp) (x,(z:X dim))).hasFDerivAt.comp (z:X dim)
    (hasFDerivAt_prodMk_right x (z:X dim))).fderiv]
  rfl

end CalderonN
