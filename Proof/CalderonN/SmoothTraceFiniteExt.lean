module

public import Proof.CalderonN.SmoothTraceSobolevCompletion

import Proof.CalderonN.SmoothZonalSobolev
import Proof.CalderonN.FiniteHarmonicPackets
import Mathlib.Tactic

/-! Pointwise equality of smooth angular operators from finite harmonic
tests and genuine adjoints. -/

public section

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ContDiff InnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 3400000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet OAI.AnisotropicCalderon SphereHarmonic
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem smoothSphereTraceL2_injective (hn : 3 ≤ dim) :
    Function.Injective (smoothSphereTraceL2 (dim:=dim) hn) := by
  intro u v hv
  let U := smoothSphereTraceRepresentative u
  let V := smoothSphereTraceRepresentative v
  have hU : smoothSphereTrace U = u := smoothSphereTrace_representative u
  have hV : smoothSphereTrace V = v := smoothSphereTrace_representative v
  rw [← hU,← hV,smoothSphereTraceL2_apply,smoothSphereTraceL2_apply] at hv
  have hAE := (smoothSphereLift_ae U.1 U.2).symm.trans
    ((EventuallyEq.of_eq (congrArg (fun x : SphereL2 dim => (x : UnitSphere dim → ℝ)) hv)).trans
      (smoothSphereLift_ae V.1 V.2))
  let : (unitSphereProbability dim).IsOpenPosMeasure := by
    let σ := (volume : Measure (X dim)).toSphere
    have h0 : σ univ ≠ 0 := by rw [ne_eq,Measure.measure_univ_eq_zero]; exact Measure.toSphere_ne_zero _
    change (((σ univ)⁻¹) • σ).IsOpenPosMeasure
    exact Measure.isOpenPosMeasure_smul σ (by simp [measure_ne_top σ univ])
  have h := Measure.eq_of_ae_eq (μ := unitSphereProbability dim) hAE
    (U.2.continuous.comp continuous_subtype_val) (V.2.continuous.comp continuous_subtype_val)
  rw [← hU,← hV]
  apply (smoothSphereTrace_eq_iff U V).mpr
  exact fun z hz => congrFun h (⟨z,hz⟩ : UnitSphere dim)

theorem denseRange_smoothSphereTraceL2_finite (hn : 3 ≤ dim) :
    DenseRange (fun f => smoothSphereTraceL2 (dim:=dim) hn (finiteHarmonicSmoothTraceL f)) := by
  have h (f : HarmonicFiniteCoefficients dim) :
      smoothSphereTraceL2 hn (finiteHarmonicSmoothTraceL f) =
        (sphereSobolevZeroEquiv (dim:=dim)).symm (harmonicBoundaryFiniteL 0 f) := by
    rw [finiteHarmonicSmoothTraceL_apply,smoothSphereTraceL2_apply,← finiteHarmonicSphereL_apply,
      finiteHarmonicSphereL_eq_sobolev]
    exact hn
  simp_rw [h]
  exact (sphereSobolevZeroEquiv (dim:=dim)).symm.surjective.denseRange.comp
    (denseRange_harmonicBoundaryFiniteL 0) (sphereSobolevZeroEquiv (dim:=dim)).symm.continuous

namespace SmoothTraceAdjoint
variable {hn : 3 ≤ dim} {S S' T T' : Module.End ℝ (SmoothSphereTrace dim)}

theorem symm (hS : SmoothTraceAdjoint hn S S') : SmoothTraceAdjoint hn S' S := by
  intro u v
  rw [real_inner_comm,← hS v u,real_inner_comm]

theorem mul (hS : SmoothTraceAdjoint hn S S') (hT : SmoothTraceAdjoint hn T T') :
    SmoothTraceAdjoint hn (S*T) (T'*S') := by
  intro u v
  change ⟪smoothSphereTraceL2 hn (S (T u)),smoothSphereTraceL2 hn v⟫_ℝ =
    ⟪smoothSphereTraceL2 hn u,smoothSphereTraceL2 hn (T' (S' v))⟫_ℝ
  rw [hS,hT]

theorem add (hS : SmoothTraceAdjoint hn S S') (hT : SmoothTraceAdjoint hn T T') :
    SmoothTraceAdjoint hn (S+T) (S'+T') := by
  intro u v
  simp only [LinearMap.add_apply,map_add,inner_add_left,inner_add_right,hS u v,hT u v]

theorem sub (hS : SmoothTraceAdjoint hn S S') (hT : SmoothTraceAdjoint hn T T') :
    SmoothTraceAdjoint hn (S-T) (S'-T') := by
  intro u v
  simp only [LinearMap.sub_apply,map_sub,inner_sub_left,inner_sub_right,hS u v,hT u v]

theorem const_smul (hS : SmoothTraceAdjoint hn S S') (c : ℝ) :
    SmoothTraceAdjoint hn (c • S) (c • S') := by
  intro u v
  simp only [LinearMap.smul_apply,map_smul,real_inner_smul_left,real_inner_smul_right,hS u v]

theorem neg (hS : SmoothTraceAdjoint hn S S') : SmoothTraceAdjoint hn (-S) (-S') := by
  intro u v
  simp only [LinearMap.neg_apply,map_neg,inner_neg_left,inner_neg_right,hS u v]

theorem sum {ι : Type*} (s : Finset ι) (F G : ι → Module.End ℝ (SmoothSphereTrace dim))
    (hAdj : ∀ i ∈ s, SmoothTraceAdjoint hn (F i) (G i)) :
    SmoothTraceAdjoint hn (∑ i ∈ s,F i) (∑ i ∈ s,G i) := by
  intro u v
  simp only [LinearMap.sum_apply,map_sum,sum_inner,inner_sum]
  exact Finset.sum_congr rfl fun i hi => hAdj i hi u v

theorem eq_of_finite (hS : SmoothTraceAdjoint hn S S') (hT : SmoothTraceAdjoint hn T T')
    (hFin : ∀ f, S (finiteHarmonicSmoothTraceL f) = T (finiteHarmonicSmoothTraceL f)) :
    S = T := by
  have hAdjPair (u : SmoothSphereTrace dim) (f : HarmonicFiniteCoefficients dim) :
      ⟪smoothSphereTraceL2 hn (finiteHarmonicSmoothTraceL f),smoothSphereTraceL2 hn (S' u)⟫_ℝ =
      ⟪smoothSphereTraceL2 hn (finiteHarmonicSmoothTraceL f),smoothSphereTraceL2 hn (T' u)⟫_ℝ := by
    rw [← hS,← hT,hFin]
  have hAdjEq (u : SmoothSphereTrace dim) : S' u = T' u := by
    apply smoothSphereTraceL2_injective hn
    apply ext_inner_left ℝ
    intro v
    exact (denseRange_smoothSphereTraceL2_finite hn).induction_on
      (p := fun v => ⟪v,smoothSphereTraceL2 hn (S' u)⟫_ℝ = ⟪v,smoothSphereTraceL2 hn (T' u)⟫_ℝ)
      v (isClosed_eq (continuous_id.inner continuous_const) (continuous_id.inner continuous_const)) (hAdjPair u)
  ext u : 1
  apply smoothSphereTraceL2_injective hn
  apply ext_inner_right ℝ
  intro v
  refine (denseRange_smoothSphereTraceL2_finite hn).induction_on
    (p := fun v => ⟪smoothSphereTraceL2 hn (S u),v⟫_ℝ = ⟪smoothSphereTraceL2 hn (T u),v⟫_ℝ)
    v (isClosed_eq (continuous_const.inner continuous_id) (continuous_const.inner continuous_id)) ?_
  intro f
  rw [hS,hT,hAdjEq]

end SmoothTraceAdjoint

end CalderonN
