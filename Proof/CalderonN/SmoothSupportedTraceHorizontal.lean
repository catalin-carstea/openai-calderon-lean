module

public import Proof.CalderonN.SmoothSupportedTraceModel
public import Proof.CalderonN.FramePullback

import Proof.CalderonN.MetricSmooth
import Proof.CalderonN.ChartBilinear
import Proof.CalderonN.HorizontalProjection
import Mathlib.Tactic

/-! Ordinary coordinates for the physical horizontal derivative on
the common smooth trace domain. -/

public section

noncomputable section
open Set
open scoped ContDiff
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet OAI.AnisotropicCalderon SphereHarmonic SmoothSphereRotation
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]
variable {Y : Set (X dim)} {g : MetricField dim} {e : Frame dim}
variable (hY : IsOpen Y) {K : ℝ} (hg : Elliptic Y K g) (hK : 0 < K)
  (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)

abbrev supportedRotation (i j : I dim) :=
  smoothSupportedTraceFiberAction hY _ (smoothSupportedTraceFiberRegular_rotation i j)

@[expose] def supportedHorizontal (a : X dim → X dim) (ha : ContDiffOn ℝ ∞ a Y) :
    Module.End ℝ (SmoothSupportedTraceSection Y) :=
  (∑ i : I dim,smoothSupportedTraceBaseMul hY (fun x => a x i) (contDiffOn_vector_component a ha i) *
    smoothSupportedTraceBaseDiff (axis i)) +
  ∑ i : I dim, ∑ j : I dim, smoothSupportedTraceBaseMul hY
    (fun x => (-(1/2:ℝ))*frameConnectionCoefficient g e x (a x) i j)
    ((contDiffOn_const (c:=(-(1/2:ℝ)))).mul (hg.contDiffOn_frameConnection hY hK e he a ha i j)) * supportedRotation hY i j

theorem supportedRotation_apply_of_repr (u : SmoothSupportedTraceSection Y)
    {G : X dim × X dim → ℝ} (hG : ContDiff ℝ ∞ G) (hu : ∀ x z, u.1 (x,z) = G (x,z))
    (i j : I dim) (x : X dim) (z : UnitSphere dim) :
    (supportedRotation hY i j u).1 (x,z) = fderiv ℝ G (x,z) (0,rotationVector i j z) := by
  rw [← smoothSupportedTraceFiberL_apply x, smoothSupportedTraceFiberAction_fiber]
  let f : SmoothData dim := ⟨fun w => G (x,w),hG.comp (contDiff_const.prodMk contDiff_id)⟩
  have hF : smoothSupportedTraceFiberL x u = smoothSphereTrace f := Subtype.ext (funext (hu x))
  rw [hF,smoothSphereTraceRotation_apply,smoothSphereTrace_apply]
  change fderiv ℝ (G ∘ Prod.mk x) (z:X dim) (rotationVector i j z) =
    fderiv ℝ G (x,(z:X dim)) (0,rotationVector i j z)
  rw [((hG.differentiable (by simp) (x,(z:X dim))).hasFDerivAt.comp (z:X dim)
    (hasFDerivAt_prodMk_right x (z:X dim))).fderiv]
  rfl

theorem supportedTraceBaseMul_apply (b : X dim → ℝ) (hb : ContDiffOn ℝ ∞ b Y)
    (u : SmoothSupportedTraceSection Y) (x : X dim) (z : UnitSphere dim) :
    (smoothSupportedTraceBaseMul hY b hb u).1 (x,z) = b x * u.1 (x,z) := by
  rw [← smoothSupportedTraceFiberL_apply x,smoothSupportedTraceBaseMul_fiber]
  rfl

theorem supportedHorizontal_apply_of_repr
    (hframe : ∀ x ∈ Y,∀ i j,metricPair g x (e x i) (e x j) = if i=j then 1 else 0)
    (a : X dim → X dim) (ha : ContDiffOn ℝ ∞ a Y)
    (u : SmoothSupportedTraceSection Y)
    {G : X dim × X dim → ℝ} (hG : ContDiff ℝ ∞ G) (hu : ∀ x z,u.1 (x,z) = G (x,z))
    {x : X dim} (hx : x ∈ Y) (z : UnitSphere dim) :
    (supportedHorizontal hY hg hK he a ha u).1 (x,z) =
      fderiv ℝ G (x,z) (a x,frameAngularVector (frameConnectionCoefficient g e x (a x)) z) := by
  simp only [supportedHorizontal,LinearMap.add_apply,Submodule.coe_add,Pi.add_apply,
    LinearMap.sum_apply,Submodule.coe_sum,Finset.sum_apply,Module.End.mul_apply,
    supportedTraceBaseMul_apply,smoothSupportedTraceBaseDiff_apply,standardTraceBaseDiff_of_repr _ hG hu,
    supportedRotation_apply_of_repr hY u hG hu]
  rw [frameAngularVector_eq_rotation _ (frameConnection_skew hY hg hK e he hframe hx (a x))]
  let F := fderiv ℝ G (x,(z:X dim))
  let α (i j : I dim) := (-(1/2:ℝ))*frameConnectionCoefficient g e x (a x) i j
  have hAxis : (∑ i : I dim,a x i • axis i) = a x := by
    simpa only [chartCoordBasis,OrthonormalBasis.coe_toBasis_repr_apply,
      EuclideanSpace.basisFun_repr,OrthonormalBasis.coe_toBasis,EuclideanSpace.basisFun_apply,axis] using
      (chartCoordBasis dim).sum_repr (a x)
  have hBase : ∑ i : I dim,a x i • (axis i, (0:X dim)) = (a x,0) := by
    simpa only [map_sum,map_smul,ContinuousLinearMap.inl_apply] using
      congrArg (ContinuousLinearMap.inl ℝ (X dim) (X dim)) hAxis
  have hAng :
      (∑ i : I dim, ∑ j : I dim, α i j • ((0:X dim), rotationVector i j (z:X dim))) =
        (0,∑ i : I dim, ∑ j : I dim, α i j • rotationVector i j (z:X dim)) := by
    let w := ∑ i : I dim, ∑ j : I dim, α i j • rotationVector i j (z:X dim)
    have h : (0,w) = (ContinuousLinearMap.inr ℝ (X dim) (X dim)) w := rfl
    exact (by simpa only [w,map_sum,map_smul,ContinuousLinearMap.inr_apply] using h.symm)
  change (∑ i : I dim,a x i * F (axis i,0)) +
    (∑ i : I dim,∑ j : I dim,α i j * F (0,rotationVector i j z)) = _
  simp_rw [← smul_eq_mul,← map_smul,← map_sum]
  rw [hBase,hAng,← map_add]
  simp only [F,α,Prod.mk_add_mk,add_zero,zero_add,smul_eq_mul]

theorem supportedHorizontal_traceComponent
    (hframe : ∀ x ∈ Y,∀ i j,metricPair g x (e x i) (e x j) = if i=j then 1 else 0)
    {φ : Field dim} (hφ : smoothNear φ (bundle Y g)) {E : HarmonicTestExpansion Y g e φ}
    {r : X dim → ℝ} {L : ℂ →L[ℝ] ℝ} (Q : AngularComponentData E r L) (i : I dim) :
    supportedHorizontal hY hg hK he (fun x => e x i) (he i) (E.traceComponent L) =
      Q.horizontalTraceComponent i := by
  apply Subtype.ext
  funext ⟨x,z⟩
  by_cases hx : x ∈ Y
  · let F : X dim × X dim → ℂ := fun q => φ (q.1,frameVector e q.1 q.2)
    let G : X dim × X dim → ℝ := fun q => L (E.representative q)
    have hG : ContDiff ℝ ∞ G := L.contDiff.comp E.representativeSmooth
    have hφ' : DifferentiableAt ℝ φ (x,frameVector e x z) :=
      by
        obtain ⟨U,hU,hBU,hS⟩ := hφ
        exact (hS.contDiffAt (hU.mem_nhds (hBU
          ⟨hx,frameVector_mem_sphere g e x (hframe x hx) z⟩))).differentiableAt (by simp)
    have he' : ∀ j,DifferentiableAt ℝ (fun x => e x j) x :=
      fun j => ((he j).contDiffAt (hY.mem_nhds hx)).differentiableAt (by simp)
    have hF := differentiableAt_frame_pullback e φ x (z:X dim) he' hφ'
    have hA := frameConnection_skew hY hg hK e he hframe hx (e x i)
    have hEq : ∀ y ∈ Y,∀ w : UnitSphere dim,(L ∘ F) (y,w) = G (y,w) :=
      fun y hy w => (congrArg L (E.representativeEq y hy w)).symm
    have hDer := fderiv_covariant_eq_of_eqOn_spheres hY hx z (L ∘ F) G
      ((L.differentiableAt).comp _ hF) (hG.differentiable (by simp) _) hEq _ hA (e x i)
    rw [supportedHorizontal_apply_of_repr hY hg hK he hframe _ _ _ hG (fun _ _ => rfl) hx,
      ← hDer,Q.horizontalTraceComponent_apply i hx,
      horizontal_eq_frame_pullback g e φ x (z:X dim) (e x i) he' (hframe x hx) hφ',
      fderiv_comp _ L.differentiableAt hF,L.fderiv]
    rfl
  · have hZero (u : SmoothSupportedTraceSection Y) : u.1 (x,z) = 0 := by
      obtain ⟨C,_,hCY,hC⟩ := smoothSupportedTraceSection_compact u
      exact hC x (fun h => hx (hCY h)) z
    rw [hZero,hZero]

end CalderonN
