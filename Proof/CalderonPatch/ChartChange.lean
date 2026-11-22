module

public import Proof.CalderonPatch.CoordinateMetric
public import Proof.CalderonN.MetricPullback

import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Proof.CalderonN.GreenWeak
import Proof.CalderonN.LinearMetric
import Proof.CalderonN.MetricPair

@[expose] public section

noncomputable section
open Filter Matrix Metric Set
open scoped ContDiff Manifold Topology

namespace CalderonPatch

open CalderonN (I X axis chartVolume coordDeriv coordinateJacobian coordinateJacobian_det_ne_zero
  coordinateMatrix coordinateMatrix_mulVec laplace laplace_congrOn laplace_pullbackMetric
  metricPair metricPair_eq_dotProduct pullbackMetric)

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]

local notation "J" => 𝓡∂ n
local notation "K" => 𝓘(ℝ, X n)

omit [NeZero n] in
private theorem normed_mfderiv_eq_fderiv (F : X n → X n) (x : X n) :
    mfderiv K K F x = fderiv ℝ F x := by
  rw [mfderiv_eq_fderiv]
  ext v
  rfl

theorem pullbackMetric_apply (γ : CalderonN.MetricField n) (F : X n → X n)
    (x : X n) (i j : I n) :
    pullbackMetric γ F x i j =
      metricPair γ (F x) (fderiv ℝ F x (axis i)) (fderiv ℝ F x (axis j)) := by
  let A := fderiv ℝ F x
  let B := coordinateMatrix A
  change (Bᵀ * γ (F x) * B) i j = _
  rw [metricPair_eq_dotProduct, ← coordinateMatrix_mulVec A (axis i),
    ← coordinateMatrix_mulVec A (axis j)]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec,
    CalderonN.axis, PiLp.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- The transition of two smooth native charts pulls back the coordinate
metric by precisely the matrix formula of Theorem 3.1's development. -/
theorem coordinateMetric_change (g : SmoothMetric n M)
    (a b : OpenPartialHomeomorph M (X n)) (ha : a.MDifferentiable J K) (hb : b.MDifferentiable J K) :
    EqOn (coordinateMetric g b) (pullbackMetric (coordinateMetric g a) (a ∘ b.symm))
      (b.symm.trans a).source := by
  let T := b.symm.trans a
  let F : X n → X n := a ∘ b.symm
  intro x hx
  have hxb : x ∈ b.target := hx.1
  have hxa : b.symm x ∈ a.source := hx.2
  have hFx : F x ∈ a.target := a.map_source hxa
  have hbase : a.symm (F x) = b.symm x := a.left_inv hxa
  have hEq : ((a.symm : X n → M) ∘ F) =ᶠ[𝓝 x] b.symm :=
    Filter.mem_of_superset (T.open_source.mem_nhds hx) (fun y hy => a.left_inv hy.2)
  have hDF : MDifferentiableAt K K F x :=
    (ha.mdifferentiableAt hxa).comp x (hb.mdifferentiableAt_symm hxb)
  let Da : X n →L[ℝ] X n := mfderiv K J a.symm (F x)
  have hD : (mfderiv K J b.symm x : X n →L[ℝ] X n) = Da.comp (fderiv ℝ F x) := by
    have hcomp := hEq.mfderiv_eq.symm.trans (mfderiv_comp x (ha.mdifferentiableAt_symm hFx) hDF)
    exact hcomp.trans (congrArg (fun L : X n →L[ℝ] X n => Da.comp L) (normed_mfderiv_eq_fderiv F x))
  ext i j
  change coordinateMetric g b x i j = pullbackMetric (coordinateMetric g a) F x i j
  rw [pullbackMetric_apply, realizesCoordinateMetric g a (F x) hFx]
  change g.inner (b.symm x) ((mfderiv K J b.symm x) (axis i)) ((mfderiv K J b.symm x) (axis j)) = _
  rw [hD]
  exact congrArg (fun p : M => g.inner p
    ((mfderiv K J a.symm (F x)) (fderiv ℝ F x (axis i)))
    ((mfderiv K J a.symm (F x)) (fderiv ℝ F x (axis j)))) hbase.symm

/-- A smooth function on an open Euclidean set admits a global smooth
representative of its germ, by multiplication with a supported bump. -/
private theorem exists_smooth_germ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set (X n)} (hU : IsOpen U) {f : X n → E} (hf : ContDiffOn ℝ ∞ f U)
    {x : X n} (hx : x ∈ U) :
    ∃ f' : X n → E, ContDiff ℝ ∞ f' ∧ f' =ᶠ[𝓝 x] f := by
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  let ρ : ContDiffBump x := ⟨r / 4, r / 2, by positivity, by linarith⟩
  have hρ : tsupport (ρ : X n → ℝ) ⊆ U := by
    rw [ρ.tsupport_eq]
    exact (closedBall_subset_ball (by dsimp [ρ]; linarith)).trans hrU
  refine ⟨fun y => ρ y • f y, contDiff_iff_contDiffAt.mpr ?_, ?_⟩
  · intro y
    by_cases hy : y ∈ U
    · exact (ρ.contDiff.contDiffAt).smul (hf.contDiffAt (hU.mem_nhds hy))
    · apply (contDiffAt_const (c := (0 : E))).congr_of_eventuallyEq
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds
        (show y ∉ tsupport (ρ : X n → ℝ) from fun hz => hy (hρ hz))]
        with z hz
      rw [image_eq_zero_of_notMem_tsupport hz, zero_smul]
  · filter_upwards [ρ.eventuallyEq_one] with y hy
    change ρ y = 1 at hy
    rw [hy, one_smul]

/-- The chart definition of the Laplace–Beltrami operator is independent
of the smooth interior coordinates. -/
theorem laplace_coordinateMetric_change (g : SmoothMetric n M)
    (a b : OpenPartialHomeomorph M (X n))
    (ha : ContMDiffOn J K ∞ a a.source) (has : ContMDiffOn K J ∞ a.symm a.target)
    (hb : ContMDiffOn J K ∞ b b.source) (hbs : ContMDiffOn K J ∞ b.symm b.target)
    {U : Set M} (hU : IsOpen U) (haU : a.source ⊆ U)
    {u : M → ℝ} (hu : ContMDiffOn J 𝓘(ℝ, ℝ) ∞ u U)
    {p : M} (hpa : p ∈ a.source) (hpb : p ∈ b.source) :
    laplace (coordinateMetric g b) (u ∘ b.symm) (b p) =
      laplace (coordinateMetric g a) (u ∘ a.symm) (a p) := by
  let T := b.symm.trans a
  let F : X n → X n := a ∘ b.symm
  let x := b p
  have hx : x ∈ T.source := by
    refine ⟨b.map_source hpb, ?_⟩
    change b.symm (b p) ∈ a.source
    rwa [b.left_inv hpb]
  have hFx : F x = a p := congrArg a (b.left_inv hpb)
  have hFD : ContDiffOn ℝ ∞ F T.source :=
    (ha.comp (hbs.mono (fun _ hy => hy.1)) (fun _ hy => hy.2)).contDiffOn
  have hTD : T.MDifferentiable K K := by
    refine ⟨hFD.contMDiffOn.mdifferentiableOn (by simp), ?_⟩
    exact (hb.comp (has.mono (fun _ hy => hy.1)) (fun _ hy => hy.2)).mdifferentiableOn (by simp)
  have hBij : Function.Bijective (fderiv ℝ F x) :=
    normed_mfderiv_eq_fderiv F x ▸ hTD.mfderiv_bijective hx
  obtain ⟨F', hF', hEq⟩ := exists_smooth_germ T.open_source hFD hx
  obtain ⟨V, hVsub, hV, hxV⟩ := _root_.mem_nhds_iff.mp
    (inter_mem (T.open_source.mem_nhds hx) hEq)
  have hGT : EqOn (coordinateMetric g b) (pullbackMetric (coordinateMetric g a) F') V := by
    intro y hy
    have hchange : coordinateMetric g b y = pullbackMetric (coordinateMetric g a) F y :=
      coordinateMetric_change g a b
      ⟨ha.mdifferentiableOn (by simp), has.mdifferentiableOn (by simp)⟩
      ⟨hb.mdifferentiableOn (by simp), hbs.mdifferentiableOn (by simp)⟩ (hVsub hy).1
    have hGerm : F' =ᶠ[𝓝 y] F :=
      Filter.mem_of_superset (hV.mem_nhds hy) (fun z hz => (hVsub hz).2)
    have hd : fderiv ℝ F' y = fderiv ℝ F y := hGerm.fderiv_eq
    exact hchange.trans (by simp only [pullbackMetric, coordinateJacobian, hd,
      (show F' y = F y from (hVsub hy).2)])
  have huT : EqOn (u ∘ b.symm) ((u ∘ a.symm) ∘ F') V := by
    intro y hy
    change u (b.symm y) = u (a.symm (F' y))
    rw [show F' y = F y from (hVsub hy).2]
    exact congrArg u (a.left_inv (hVsub hy).1.2).symm
  rw [laplace_congrOn hV hGT huT hxV]
  have hx' : F' x = a p := hEq.eq_of_nhds.trans hFx
  have hJa : (coordinateJacobian F' x).det ≠ 0 := by
    have hd : fderiv ℝ F' x = fderiv ℝ F x := hEq.fderiv_eq
    exact coordinateJacobian_det_ne_zero (hd.symm ▸ hBij)
  rw [laplace_pullbackMetric a.open_target (coordinateMetric_smooth g a ha has) hF'
    (hu.comp has (fun _ hy => haU (a.map_target hy))).contDiffOn
    (hx'.symm ▸ a.map_source hpa) hJa, hx']

end CalderonPatch
