module

public import Proof.CalderonPatch.NativeNormalChart
public import Proof.CalderonN.MetricConnection

import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Topology.VectorBundle.Riemannian

@[expose] public section

noncomputable section
open Bundle ContinuousLinearMap Filter Set
open scoped ContDiff Manifold Topology

namespace CalderonPatch


open CalderonN (I X MetricField metricBilinear metricBilinear_apply metricPair)

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]

local notation "J" => 𝓡∂ n
local notation "K" => 𝓘(ℝ, X n)
local notation "T" => TangentSpace J
local notation "B" => (X n →L[ℝ] X n →L[ℝ] ℝ)
local notation "JB" => (ModelWithCorners.prod J 𝓘(ℝ, B))

/-- A coordinate matrix field pulled back to the native tangent
bundle by the derivative of a smooth coordinate map. -/
def nativeCoordinateBilinear (γ : MetricField n) (q : M → X n) (x : M) :
    T x →L[ℝ] T x →L[ℝ] ℝ := by
  let D : X n →L[ℝ] X n := mfderiv J K q x
  exact (metricBilinear γ (q x)).bilinearComp D D

theorem nativeCoordinateBilinear_apply (γ : MetricField n) (q : M → X n) (x : M) (v w : T x) :
    nativeCoordinateBilinear γ q x v w =
      metricPair γ (q x) (mfderiv J K q x v) (mfderiv J K q x w) := by
  let D : X n →L[ℝ] X n := mfderiv J K q x
  change (metricBilinear γ (q x)).bilinearComp D D v w = metricPair γ (q x) (D v) (D w)
  exact metricBilinear_apply γ (q x) (D v) (D w)

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 2400000 in
/-- Smooth coordinate metric coefficients give a smooth section of
the native bilinear-form bundle through the boundary. -/
theorem contMDiffOn_nativeCoordinateBilinear {U : Set M} {V : Set (X n)}
    (hU : IsOpen U) {γ : MetricField n} (hγ : CalderonN.SmoothMetric V γ)
    {q : M → X n} (hq : ContMDiffOn J K ∞ q U) (hMap : MapsTo q U V) :
    ContMDiffOn J JB ∞ (fun x => TotalSpace.mk' B x (nativeCoordinateBilinear γ q x)) U := by
  intro x hx
  apply ContMDiffAt.contMDiffWithinAt
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  let D (y : M) : X n →L[ℝ] X n :=
    inTangentCoordinates J K id q (mfderiv J K q) x y
  have hqAt := hq.contMDiffAt (hU.mem_nhds hx)
  have hD : ContMDiffAt J 𝓘(ℝ, X n →L[ℝ] X n) ∞ D x := hqAt.mfderiv_const (by simp)
  have hG : ContMDiffAt J 𝓘(ℝ, B) ∞ (fun y => metricBilinear γ (q y)) x := by
    apply ContMDiffOn.contMDiffAt _ (hU.mem_nhds hx)
    intro y hy
    simp only [metricBilinear]
    exact contMDiffWithinAt_finsetSum fun i _ => contMDiffWithinAt_finsetSum fun j _ =>
      (((hγ.1 i j).contMDiffOn.comp hq hMap) y hy).smul contMDiffWithinAt_const
  let flip : B →L[ℝ] B := (ContinuousLinearMap.flipₗᵢ ℝ (X n) (X n) ℝ).toContinuousLinearMap
  have h1 : ContMDiffAt J 𝓘(ℝ, B) ∞ (fun y => (metricBilinear γ (q y)).comp (D y)) x :=
    hG.clm_comp hD
  have hFlip' : ContDiff ℝ ∞ (flip : B → B) := ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := B) (F := B) (n := ∞) flip
  have hFlip : ContMDiff 𝓘(ℝ, B) 𝓘(ℝ, B) ∞ (flip : B → B) := hFlip'.contMDiff
  have h2 : ContMDiffAt J 𝓘(ℝ, B) ∞ (fun y => ((metricBilinear γ (q y)).comp (D y)).flip) x :=
    hFlip.contMDiffAt.comp x h1
  have h3 := h2.clm_comp hD
  have hLocal : ContMDiffAt J 𝓘(ℝ, B) ∞ (fun y => (metricBilinear γ (q y)).bilinearComp (D y) (D y)) x :=
    hFlip.contMDiffAt.comp x h3
  apply hLocal.congr_of_eventuallyEq
  have hTr := (trivializationAt (X n) T x).open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt' x)
  filter_upwards [hTr] with y hy
  change inCoordinates (X n) T (X n →L[ℝ] ℝ) (fun a => T a →L[ℝ] ℝ) x y x y
    (nativeCoordinateBilinear γ q y) = _
  ext v w
  have hTriv : y ∈ (trivializationAt ℝ (Bundle.Trivial M ℝ) x).baseSet := by simp
  rw [inCoordinates_apply_eq₂ hy hy hTriv]
  simp only [Trivial.fiberBundle_trivializationAt', Trivial.linearMapAt_trivialization, LinearMap.id_coe, id_eq,
    nativeCoordinateBilinear, bilinearComp_apply]
  let E : X n →L[ℝ] X n := mfderiv J K q y
  let S : X n →L[ℝ] X n := (trivializationAt (X n) T x).symmL ℝ y
  have hDeq : D y = E.comp S := by
    unfold D inTangentCoordinates ContinuousLinearMap.inCoordinates
    rw [TangentBundle.continuousLinearMapAt_model_space]
    rfl
  have hS (u : X n) : S u = (trivializationAt (X n) T x).symm y u := by
    exact Trivialization.symmL_apply _ hy u
  change metricBilinear γ (q y) (E ((trivializationAt (X n) T x).symm y v))
      (E ((trivializationAt (X n) T x).symm y w)) =
    metricBilinear γ (q y) (D y v) (D y w)
  rw [hDeq, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hS v, hS w]

end CalderonPatch
