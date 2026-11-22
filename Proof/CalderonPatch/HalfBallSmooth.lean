module

public import Proof.CalderonPatch.HalfBallJetBounds

import Proof.CalderonN.SobolevInteriorRepresentative
import Proof.CalderonN.TaylorJetCalculus
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.ExtendFrom
import Mathlib.Tactic

public section

noncomputable section
open Set Filter Metric
open scoped ContDiff Topology

namespace CalderonPatch

open CalderonN (X I axis)

private theorem exists_tendsto_nhdsWithin_of_uniformContinuousOn
    {E F : Type*} [MetricSpace E] [MetricSpace F] [CompleteSpace F]
    {S : Set E} {f : E → F} (hf : UniformContinuousOn f S) {x : E} (hx : x ∈ closure S) :
    ∃ y, Tendsto f (𝓝[S] x) (𝓝 y) := by
  have : NeBot (𝓝[S] x) := mem_closure_iff_nhdsWithin_neBot.mp hx
  apply cauchy_map_iff_exists_tendsto.mp
  refine Metric.cauchy_iff.2 ⟨inferInstance,fun ε hε => ?_⟩
  obtain ⟨δ,hδ,hD⟩ := Metric.uniformContinuousOn_iff.1 hf ε hε
  let N := ball x (δ / 2) ∩ S
  have hN : N ∈ 𝓝[S] x := by
    simpa only [N,inter_comm] using inter_mem_nhdsWithin S
      (ball_mem_nhds x (by positivity : 0 < δ / 2))
  refine ⟨f '' N,mem_map.2 (mem_of_superset hN (fun y hy => mem_image_of_mem f hy)),?_⟩
  rintro _ ⟨u,hu,rfl⟩ _ ⟨v,hv,rfl⟩
  apply hD u hu.2 v hv.2
  have hu' := mem_ball.1 hu.1
  have hv' := mem_ball.1 hv.1
  exact (dist_triangle_right u v x).trans_lt (by linarith)

variable {n : ℕ} [NeZero n]
local notation "E" => X n

/-- An open half-ball is convex. -/
theorem convex_positiveHalfBall (p : E) (R : ℝ) :
    Convex ℝ (ball p R ∩ positiveHalfSpace n) := by
  apply (convex_ball ..).inter
  exact convex_halfSpace_gt (EuclideanSpace.proj (𝕜 := ℝ) (0 : I n)).isLinear 0

/-- The relative half-ball with its flat face lies in the closure
of the corresponding open half-ball. -/
theorem halfBall_inward_subset_closure (p : E) (R : ℝ) :
    ball p R ∩ inwardHalfSpace n ⊆ closure (ball p R ∩ positiveHalfSpace n) := by
  intro x hx
  apply Metric.mem_closure_iff.2
  intro ε hε
  have hx' := mem_ball.1 hx.1
  let v : E := axis 0
  have hv0 : v 0 = 1 := by simp [v,axis]
  have hv : ‖v‖ = 1 := by simp [v,axis]
  let t := min (ε / 2) ((R - dist x p) / 2)
  have ht : 0 < t := lt_min (by positivity) (by linarith)
  let y := x + t • v
  have hdist : dist y x = t := by rw [dist_eq_norm]; simp [y,norm_smul,Real.norm_of_nonneg ht.le,hv]
  have hy : y ∈ ball p R := by
    apply mem_ball.2
    have hh := (dist_triangle y x p)
    rw [hdist] at hh
    have ht' : t ≤ (R - dist x p) / 2 := min_le_right _ _
    linarith
  have hypos : y ∈ positiveHalfSpace n := by
    apply mem_positiveHalfSpace.2
    have h := mem_inwardHalfSpace.mp hx.2
    simpa [y,hv0] using add_pos_of_nonneg_of_pos h ht
  refine ⟨y,⟨hy,hypos⟩,?_⟩
  rw [dist_comm,hdist]
  exact (min_le_left _ _).trans_lt (by linarith)

/-- Square-integrable jets of every order on a half-ball have
a single smooth representative up to the flat face of a smaller
half-ball. The extension is determined by continuity from the interior. -/
theorem exists_contDiffOn_halfBall_closure_of_bulk_jets
    {p : E} {R : ℝ} (hR : 0 < R) {f : E → ℝ}
    (hf : ContDiffOn ℝ ∞ f (ball p R ∩ positiveHalfSpace n))
    (hLp : ∀ k, MeasureTheory.MemLp (iteratedFDeriv ℝ k f) 2
      (MeasureTheory.volume.restrict (ball p R ∩ positiveHalfSpace n))) :
    ∃ F : E → ℝ, ContDiffOn ℝ ∞ F (closure (ball p (R/4) ∩ positiveHalfSpace n)) ∧
      EqOn F f (ball p (R/4) ∩ positiveHalfSpace n) := by
  let S := ball p (R / 4) ∩ positiveHalfSpace n
  have hS : IsOpen S := isOpen_ball.inter isOpen_positiveHalfSpace
  have hSc : Convex ℝ S := convex_positiveHalfBall p (R / 4)
  have hSub : S ⊆ ball p R ∩ positiveHalfSpace n :=
    inter_subset_inter_left _ (ball_subset_ball (by linarith))
  have hsmooth (k : ℕ) : ContDiffOn ℝ ∞ (iteratedFDeriv ℝ k f) S :=
    CalderonN.contDiffOn_iteratedFDeriv_top (hf.mono hSub) hS k
  let G (k : ℕ) := extendFrom S (iteratedFDeriv ℝ k f)
  have hLip (k : ℕ) : ∃ B : NNReal, LipschitzOnWith B (iteratedFDeriv ℝ k f) S := by
    obtain ⟨B,hB,hh⟩ := exists_iteratedFDeriv_bound_on_halfBall hR hf hLp (k+1)
    refine ⟨⟨B,hB⟩,Convex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ) (fun x hx => ?_) (fun x hx => ?_) hSc⟩
    · exact ((hsmooth k x hx).contDiffAt (hS.mem_nhds hx)).differentiableAt (by simp)
    · apply NNReal.coe_le_coe.mp
      change ‖fderiv ℝ (iteratedFDeriv ℝ k f) x‖ ≤ B
      rw [norm_fderiv_iteratedFDeriv]
      exact hh x hx
  have hG (k : ℕ) : ContinuousOn (G k) (closure S) := by
    obtain ⟨B,hB⟩ := hLip k
    exact continuousOn_extendFrom Subset.rfl (fun x hx =>
      exists_tendsto_nhdsWithin_of_uniformContinuousOn hB.uniformContinuousOn hx)
  have he (k : ℕ) : EqOn (G k) (iteratedFDeriv ℝ k f) S :=
    extendFrom_extends (hsmooth k).continuousOn
  let F := fun x => (G 0 x).curry0
  let J : E → FormalMultilinearSeries ℝ E ℝ := fun x k => G k x
  have hSeries : HasFTaylorSeriesUpToOn (⊤ : ℕ∞) F J (closure S) := by
    refine ⟨fun x _ => rfl,fun k _ x hx => ?_,fun k _ => hG k⟩
    have hdiff : DifferentiableOn ℝ (G k) S :=
      ((hsmooth k).differentiableOn (by simp)).congr (he k)
    have hDeriv (z : E) (hz : z ∈ S) : fderiv ℝ (G k) z = (G (k+1) z).curryLeft := by
      have hg : G k =ᶠ[𝓝 z] iteratedFDeriv ℝ k f :=
        Filter.mem_of_superset (hS.mem_nhds hz) (he k)
      rw [hg.fderiv_eq,fderiv_iteratedFDeriv,Function.comp_apply,he (k+1) hz]
      rfl
    have hCont (z : E) (hz : z ∈ closure S) : ContinuousWithinAt (G k) S z :=
      ((hG k) z hz).mono subset_closure
    have hCur : ContinuousOn (fun z => (G (k+1) z).curryLeft) (closure S) :=
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k+1) => E) ℝ).continuous.comp_continuousOn
        (hG (k+1))
    have hLim : Tendsto (fun z => fderiv ℝ (G k) z) (𝓝[S] x)
        (𝓝 ((G (k+1) x).curryLeft)) :=
      ((hCur x hx).mono subset_closure).tendsto.congr'
        (eventually_mem_nhdsWithin.mono fun z hz => (hDeriv z hz).symm)
    exact hasFDerivWithinAt_closure_of_tendsto_fderiv hdiff hSc hS hCont hLim
  refine ⟨F,hSeries.contDiffOn,fun x hx => ?_⟩
  change (G 0 x).curry0 = f x
  rw [he 0 hx]
  simp [ContinuousMultilinearMap.curry0]

end CalderonPatch
