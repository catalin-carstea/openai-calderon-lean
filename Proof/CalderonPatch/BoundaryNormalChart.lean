module

public import Proof.CalderonPatch.BoundaryNormalField
public import Proof.CalderonN.GeodesicEndpoint

import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

@[expose] public section

noncomputable section
open Filter Metric Set
open scoped ContDiff Topology

namespace CalderonPatch

open CalderonN (I X MetricField axis GeodesicPhase GeodesicFlowOn geodesicEndpoint)

variable {n : ℕ}

/-- The normal coordinate splits into its foot point on the flat seam
and its height. -/
def boundaryFoot (i : I n) : X n →L[ℝ] X n :=
  ContinuousLinearMap.id ℝ (X n) - (EuclideanSpace.proj (𝕜 := ℝ) i).smulRight (axis i)

theorem boundaryFoot_apply (i : I n) (x : X n) : boundaryFoot i x = x - x i • axis i := rfl

theorem boundaryFoot_on_face (i : I n) {x : X n} (hx : x i = 0) : boundaryFoot i x = x := by
  rw [boundaryFoot_apply, hx, zero_smul, sub_zero]

private theorem endpointPair_fderiv_at_rest {g : MetricField n} {p q : X n} {r : ℝ}
    {F : GeodesicPhase n → ℝ → GeodesicPhase n}
    (hF : GeodesicFlowOn (fun _ => g) ({(0 : ℝ)} ×ˢ closedBall p 1) r F) (hr : 0 < r) (hq : q ∈ ball p 1) :
    fderiv ℝ (fun z : X n × X n => geodesicEndpoint F ((0, z.1), z.2)) (q, 0) =
      ContinuousLinearMap.fst ℝ (X n) (X n) + ContinuousLinearMap.snd ℝ (X n) (X n) := by
  let E (q : X n × X n) := geodesicEndpoint F ((0, q.1), q.2)
  have hE : ContDiff ℝ ∞ E := hF.contDiff_endpoint.comp
    ((contDiff_const.prodMk contDiff_fst).prodMk contDiff_snd)
  let D := fderiv ℝ E (q, 0)
  have hD : HasFDerivAt E D (q, 0) := (hE.differentiable (by simp) (q, 0)).hasFDerivAt
  have hc : (fun x : X n => E (x, 0)) =ᶠ[𝓝 q] id := by
    filter_upwards [isOpen_ball.mem_nhds hq] with x hx
    exact hF.endpoint_rest ⟨mem_singleton _, ball_subset_closedBall hx⟩
  have hA : D.comp (ContinuousLinearMap.inl ℝ (X n) (X n)) = ContinuousLinearMap.id ℝ (X n) := by
    have hIn : HasFDerivAt (fun x : X n => (x, (0 : X n)))
        (ContinuousLinearMap.inl ℝ (X n) (X n)) q :=
      (hasFDerivAt_id q).prodMk (hasFDerivAt_const (0 : X n) q)
    have hD' : HasFDerivAt E D (q, (0 : X n)) := hD
    have h := hD'.comp q hIn
    have he := (h.congr_of_eventuallyEq hc.symm).unique (hasFDerivAt_id q)
    exact he
  have hB : D.comp (ContinuousLinearMap.inr ℝ (X n) (X n)) = ContinuousLinearMap.id ℝ (X n) := by
    have h := hD.comp (0 : X n) ((hasFDerivAt_const q (0 : X n)).prodMk (hasFDerivAt_id (0 : X n)))
    have he : fderiv ℝ (fun v => E (q, v)) 0 = ContinuousLinearMap.id ℝ (X n) :=
      hF.endpoint_fderiv_at_rest (p := (0, q)) hr ⟨mem_singleton _, ball_subset_closedBall hq⟩
    exact h.fderiv.symm.trans he
  apply ContinuousLinearMap.ext
  rintro ⟨x, v⟩
  have h₁ := DFunLike.congr_fun hA x
  have h₂ := DFunLike.congr_fun hB v
  change D (x, 0) = x at h₁
  change D (0, v) = v at h₂
  change D (x, v) = x + v
  rw [show ((x, v) : X n × X n) = (x, 0) + (0, v) by simp, map_add, h₁, h₂]

/-- The smooth signed normal endpoint map of the actual geodesic flow. -/
def boundaryNormalEndpoint (g : MetricField n) (i : I n)
    (F : GeodesicPhase n → ℝ → GeodesicPhase n) (x : X n) : X n :=
  geodesicEndpoint F ((0, boundaryFoot i x), x i • positiveCoordinateNormal g i (boundaryFoot i x))

theorem boundaryNormalEndpoint_smooth {g : MetricField n} {p : X n} {r : ℝ}
    {F : GeodesicPhase n → ℝ → GeodesicPhase n}
    (hF : GeodesicFlowOn (fun _ => g) ({(0 : ℝ)} ×ˢ closedBall p 1) r F)
    (hg : CalderonN.SmoothMetric univ g) (i : I n) : ContDiff ℝ ∞ (boundaryNormalEndpoint g i F) := by
  let P := boundaryFoot i
  have hν := contDiffOn_univ.mp (contDiffOn_positiveCoordinateNormal hg i)
  exact hF.contDiff_endpoint.comp ((contDiff_const.prodMk P.contDiff).prodMk
    ((EuclideanSpace.proj i).contDiff.smul (hν.comp P.contDiff)))

theorem boundaryNormalEndpoint_hasFDerivAt {g : MetricField n} {p q : X n} {r : ℝ}
    {F : GeodesicPhase n → ℝ → GeodesicPhase n}
    (hF : GeodesicFlowOn (fun _ => g) ({(0 : ℝ)} ×ˢ closedBall p 1) r F) (hr : 0 < r)
    (hg : CalderonN.SmoothMetric univ g) {i : I n} (hp : q i = 0) (hq : q ∈ ball p 1) :
    HasFDerivAt (boundaryNormalEndpoint g i F)
      (boundaryFoot i + (EuclideanSpace.proj (𝕜 := ℝ) i).smulRight (positiveCoordinateNormal g i q)) q := by
  let p := q
  let P := boundaryFoot i
  let L : X n →L[ℝ] ℝ := EuclideanSpace.proj i
  let ν := positiveCoordinateNormal g i
  let E (q : X n × X n) := geodesicEndpoint F ((0, q.1), q.2)
  have hpP : P p = p := boundaryFoot_on_face i hp
  have hν : ContDiff ℝ ∞ ν := contDiffOn_univ.mp (contDiffOn_positiveCoordinateNormal hg i)
  have hE : ContDiff ℝ ∞ E := hF.contDiff_endpoint.comp
    ((contDiff_const.prodMk contDiff_fst).prodMk contDiff_snd)
  have hDE : HasFDerivAt E (ContinuousLinearMap.fst ℝ (X n) (X n) + ContinuousLinearMap.snd ℝ (X n) (X n)) (p, 0) :=
    (endpointPair_fderiv_at_rest hF hr hq) ▸ (hE.differentiable (by simp) (p, 0)).hasFDerivAt
  have hV : HasFDerivAt (fun x => L x • ν (P x)) (L.smulRight (ν p)) p := by
    have h := L.hasFDerivAt.smul ((hν.comp P.contDiff).differentiable (by simp) p).hasFDerivAt
    change HasFDerivAt (fun x : X n => L x • ν (P x))
      (L p • fderiv ℝ (ν ∘ P) p + L.smulRight (ν (P p))) p at h
    have hD' : L p • fderiv ℝ (ν ∘ P) p + L.smulRight (ν (P p)) = L.smulRight (ν p) := by
      apply ContinuousLinearMap.ext
      intro y
      simp [show L p = (0 : ℝ) from hp, hpP]
    rwa [hD'] at h
  have hDE' : HasFDerivAt E (ContinuousLinearMap.fst ℝ (X n) (X n) + ContinuousLinearMap.snd ℝ (X n) (X n))
      (P p, L p • ν (P p)) := by simpa only [show L p = 0 from hp, hpP, zero_smul] using hDE
  have h := hDE'.comp p (P.hasFDerivAt.prodMk hV)
  have heq : (ContinuousLinearMap.fst ℝ (X n) (X n) + ContinuousLinearMap.snd ℝ (X n) (X n)).comp
      (P.prod (L.smulRight (ν p))) = P + L.smulRight (ν p) := by ext x; rfl
  rw [heq] at h
  exact h

/-- A smooth metric in Euclidean coordinates gives a smooth local
boundary normal chart. The chart is the signed endpoint of the actual
geodesic flow and fixes its parametrizing seam. -/
theorem exists_boundaryNormalChart {g : MetricField n} (hg : CalderonN.SmoothMetric univ g)
    {p : X n} {i : I n} (hp : p i = 0) :
    ∃ (r : ℝ) (F : GeodesicPhase n → ℝ → GeodesicPhase n) (e : OpenPartialHomeomorph (X n) (X n)),
      0 < r ∧ GeodesicFlowOn (fun _ => g) ({(0 : ℝ)} ×ˢ closedBall p 1) r F ∧
      p ∈ e.source ∧ (e : X n → X n) = boundaryNormalEndpoint g i F ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      EqOn e id (e.source ∩ {x | x i = 0}) := by
  let K := ({(0 : ℝ)} : Set ℝ) ×ˢ closedBall p 1
  have hK : IsCompact K := isCompact_singleton.prod (isCompact_closedBall _ _)
  have hγ (i j : I n) : ContDiff ℝ ∞ (fun q : ℝ × X n => g q.2 i j) :=
    (contDiffOn_univ.mp (hg.1 i j)).comp contDiff_snd
  obtain ⟨r, F, hr, hF⟩ := CalderonN.exists_geodesicFlowOn
    (CalderonN.contDiff_geodesicSpray hγ (fun _ x => hg.2 x (mem_univ x))) hK
  let f := boundaryNormalEndpoint g i F
  let A := boundaryFoot i + (EuclideanSpace.proj (𝕜 := ℝ) i).smulRight (positiveCoordinateNormal g i p)
  have hf := boundaryNormalEndpoint_smooth hF hg i
  have hfD := boundaryNormalEndpoint_hasFDerivAt hF hr hg hp (mem_ball_self (by norm_num : (0 : ℝ) < 1))
  have hAcoord (x : X n) : A x i = x i * positiveCoordinateNormal g i p i := by
    change ((boundaryFoot i x) + x i • positiveCoordinateNormal g i p) i = _
    rw [boundaryFoot_apply]
    simp [axis]
  have hAi : Function.Injective A := (injective_iff_map_eq_zero A).mpr (fun x hx => by
    have hi₀ : x i = 0 := by
      have h := congrArg (fun z : X n => z i) hx
      change A x i = 0 at h
      rw [hAcoord] at h
      exact (mul_eq_zero.mp h).resolve_right (positiveCoordinateNormal_transverse g (hg.2 p (mem_univ p)) i).ne'
    change boundaryFoot i x + x i • positiveCoordinateNormal g i p = 0 at hx
    simpa only [hi₀, boundaryFoot_on_face i hi₀, zero_smul, add_zero] using hx)
  have hAs : Function.Surjective A := LinearMap.injective_iff_surjective.mp hAi
  let B := ContinuousLinearEquiv.ofBijective A (LinearMap.ker_eq_bot.mpr hAi) (LinearMap.range_eq_top.mpr hAs)
  have hfD' : HasFDerivAt f (B : X n →L[ℝ] X n) p := hfD
  let e₀ := hf.contDiffAt.toOpenPartialHomeomorph f hfD' (by simp)
  have hp₀ := hf.contDiffAt.mem_toOpenPartialHomeomorph_source hfD' (by simp)
  let V := (boundaryFoot i) ⁻¹' ball p 1 ∩ (fderiv ℝ f) ⁻¹' {A | ContinuousLinearMap.IsInvertible A}
  have hV : IsOpen V := ((isOpen_ball.preimage (boundaryFoot i).continuous)).inter
    (ContinuousLinearMap.isOpen_setOfPred_isInvertible.preimage (hf.continuous_fderiv (by simp)))
  have hpV : p ∈ V := ⟨by change boundaryFoot i p ∈ ball p 1; rw [boundaryFoot_on_face i hp]; simp,
    by change (fderiv ℝ f p).IsInvertible; rw [hfD'.fderiv]; exact ⟨B, rfl⟩⟩
  let e := e₀.restr V
  have heS : e.source = e₀.source ∩ V := e₀.restr_source' V hV
  refine ⟨r, F, e, hr, hF, heS.symm ▸ ⟨hp₀, hpV⟩, rfl, hf.contDiffOn, ?_, ?_⟩
  · intro y hy
    have hx : e.symm y ∈ e₀.source ∩ V := heS ▸ e.map_target hy
    obtain ⟨A, hA⟩ := hx.2.2
    have hF := (hf.differentiable (by simp) (e.symm y)).hasFDerivAt
    exact (e.contDiffAt_symm hy (hA ▸ hF) hf.contDiffAt).contDiffWithinAt
  · intro x hx
    have hxV : x ∈ V := (show x ∈ e₀.source ∩ V from heS ▸ hx.1).2
    have hxp : boundaryFoot i x = x := boundaryFoot_on_face i hx.2
    have hxb : boundaryFoot i x ∈ ball p 1 := hxV.1
    rw [hxp] at hxb
    change geodesicEndpoint F ((0, boundaryFoot i x), x i • positiveCoordinateNormal g i (boundaryFoot i x)) = x
    rw [hxp, show x i = 0 from hx.2, zero_smul]
    exact hF.endpoint_rest ⟨mem_singleton _, ball_subset_closedBall hxb⟩

end CalderonPatch
