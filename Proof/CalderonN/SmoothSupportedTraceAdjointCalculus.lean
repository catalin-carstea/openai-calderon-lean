module

public import Proof.CalderonN.SmoothSupportedTraceScalarCalculus
public import Proof.CalderonN.MovingTraceNormIdentity

import Mathlib.Tactic

/-! Bilinear adjunction on the common smooth section space. -/

public section

noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

section PairedAdjoint
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

@[expose] def PairedAdjoint (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (S T : Module.End ℝ V) : Prop :=
  ∀ u v, B (S u) v = B u (T v)

namespace PairedAdjoint
variable {B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {S S' T T' : Module.End ℝ V}

theorem add (hS : PairedAdjoint B S S') (hT : PairedAdjoint B T T') :
    PairedAdjoint B (S+T) (S'+T') := by
  intro u v
  simp only [LinearMap.add_apply,map_add,hS u v,hT u v]

theorem sub (hS : PairedAdjoint B S S') (hT : PairedAdjoint B T T') :
    PairedAdjoint B (S-T) (S'-T') := by
  intro u v
  simp only [LinearMap.sub_apply,map_sub,hS u v,hT u v]

theorem neg (hS : PairedAdjoint B S S') : PairedAdjoint B (-S) (-S') := by
  intro u v
  simp only [LinearMap.neg_apply,map_neg,hS u v]

theorem mul (hS : PairedAdjoint B S S') (hT : PairedAdjoint B T T') :
    PairedAdjoint B (S*T) (T'*S') := by
  intro u v
  simp only [Module.End.mul_apply]
  exact (hS (T u) v).trans (hT u (S' v))

theorem sum {ι : Type*} (s : Finset ι) (S T : ι → Module.End ℝ V)
    (h : ∀ i ∈ s, PairedAdjoint B (S i) (T i)) :
    PairedAdjoint B (∑ i ∈ s,S i) (∑ i ∈ s,T i) := by
  intro u v
  simp only [LinearMap.sum_apply,map_sum]
  exact Finset.sum_congr rfl (fun i hi => h i hi u v)

end PairedAdjoint
end PairedAdjoint

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)}
variable (hn : 3 ≤ dim) (hY : IsOpen Y) (μ : X dim → ℝ) (hμ : ContDiffOn ℝ ∞ μ Y)

theorem pairedAdjoint_supportedFiber
    (S T : X dim → Module.End ℝ (SmoothSphereTrace dim))
    (hS : SmoothSupportedTraceFiberRegular Y S) (hT : SmoothSupportedTraceFiberRegular Y T)
    (h : ∀ x ∈ Y, SmoothTraceAdjoint hn (S x) (T x)) :
    PairedAdjoint (smoothSupportedTracePairingL hn hY μ hμ)
      (smoothSupportedTraceFiberAction hY S hS) (smoothSupportedTraceFiberAction hY T hT) := by
  intro u v
  exact smoothSupportedTraceFiberAction_adjoint hn hY μ S T hS hT h u v

theorem pairedAdjoint_supportedBaseMul (a : X dim → ℝ) (ha : ContDiffOn ℝ ∞ a Y) :
    PairedAdjoint (smoothSupportedTracePairingL hn hY μ hμ)
      (smoothSupportedTraceBaseMul hY a ha) (smoothSupportedTraceBaseMul hY a ha) := by
  intro u v
  change smoothSupportedTracePairing hn μ (smoothSupportedTraceBaseMul hY a ha u) v =
    smoothSupportedTracePairing hn μ u (smoothSupportedTraceBaseMul hY a ha v)
  rw [smoothSupportedTracePairing_symm hn μ _ v,smoothSupportedTrace_basePairing_mul_right hn hY μ a ha,
    smoothSupportedTrace_basePairing_mul_right hn hY μ a ha,smoothSupportedTracePairing_symm hn _]

theorem pairedAdjoint_supportedRotation (i j : I dim) :
    PairedAdjoint (smoothSupportedTracePairingL hn hY μ hμ) (supportedRotation hY i j) (-supportedRotation hY i j) := by
  let T := smoothSphereTraceRotation (dim:=dim) i j
  let hT := smoothSupportedTraceFiberRegular_rotation (Y:=Y) i j
  have hEq : smoothSupportedTraceFiberAction hY (fun _ => -T) hT.neg = -supportedRotation hY i j := by
    ext u : 1
    apply smoothSupportedTraceSection_ext_by_fibers
    intro x hx
    simp only [LinearMap.neg_apply,map_neg,smoothSupportedTraceFiberAction_fiber,T]
  rw [← hEq]
  exact pairedAdjoint_supportedFiber hn hY μ hμ _ _ hT hT.neg (fun _ _ => smoothTraceRotation_skew hn i j)

variable {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
  {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
  {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim, ConormalTaylorSolutions A ell f)

theorem pairedAdjoint_supportedFlatDegree :
    PairedAdjoint (smoothSupportedTracePairingL hn hY μ hμ)
      (supportedFlatDegree hA hEll S hY) (supportedFlatDegree hA hEll S hY) :=
  pairedAdjoint_supportedFiber hn hY μ hμ _ _ _ _ (fun _ _ => smoothTraceFlatDegree_symmetric hn hA hEll S)

theorem pairedAdjoint_supportedRaising (i : I dim) :
    PairedAdjoint (smoothSupportedTracePairingL hn hY μ hμ)
      (supportedRaising hA hEll S hY i) (supportedLowering hA hEll S hY i) :=
  pairedAdjoint_supportedFiber hn hY μ hμ _ _ _ _ (fun _ _ =>
    smoothTraceRaising_adjoint hn _ (smoothTraceFlatDegree_symmetric hn hA hEll S) i)

end CalderonN
