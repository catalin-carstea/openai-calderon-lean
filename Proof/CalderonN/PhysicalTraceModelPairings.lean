module

public import Proof.CalderonN.SmoothSupportedTraceHorizontal

import Mathlib.Tactic

/-! The global pairings of the genuine geometric model agree with the
squared raising and lowering graph norms in the coercivity estimate. -/

public section

noncomputable section
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 23
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE OAI.AnisotropicCalderon SphereHarmonic
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]
variable {Y : Set (X dim)} {g : MetricField dim} {e : Frame dim}
variable (hY : IsOpen Y) {K : ℝ} (hg : Elliptic Y K g) (hK : 0 < K)
  (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
variable {r : X dim → ℝ} (hlog : ContDiffOn ℝ ∞ (fun x => Real.log (r x)) Y)

@[expose] def traceModelLogGradient (e : Frame dim) (r : X dim → ℝ) (i : I dim) (x : X dim) : ℝ :=
  fderiv ℝ (fun y => Real.log (r y)) x (e x i)

include hY he hlog in
theorem contDiffOn_traceModelLogGradient (i : I dim) :
    ContDiffOn ℝ ∞ (traceModelLogGradient e r i) Y :=
  (hlog.fderiv_of_isOpen (m:=∞) hY (by simp)).clm_apply (he i)

variable {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
  {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
  {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim, ConormalTaylorSolutions A ell f)

abbrev physicalRaisingModel :=
  supportedRaisingModel hA hEll S hY (fun i => supportedHorizontal hY hg hK he _ (he i))
    (traceModelLogGradient e r) (contDiffOn_traceModelLogGradient hY he hlog)

abbrev physicalLoweringModel :=
  supportedLoweringModel hA hEll S hY (fun i => supportedHorizontal hY hg hK he _ (he i))
    (traceModelLogGradient e r) (contDiffOn_traceModelLogGradient hY he hlog)

variable (hframe : ∀ x ∈ Y, ∀ i j, metricPair g x (e x i) (e x j) = if i=j then 1 else 0)
  {φ : Field dim} (hφ : smoothNear φ (bundle Y g))
  {E : HarmonicTestExpansion Y g e φ} {L : ℂ →L[ℝ] ℝ} (Q : AngularComponentData E r L)

private theorem traceModelLogGradient_smul_flatDegree (i : I dim) (x : X dim) :
    let v := smoothTraceFlatDegree hA hEll S (smoothSupportedTraceFiberL x (E.traceComponent L))
    traceModelLogGradient e r i x • v = Q.coefficient i x • v := by
  dsimp only
  by_cases hx : x ∈ E.supportSet
  · rw [Q.coefficientEq i x hx]
    rfl
  · have hZero : smoothSupportedTraceFiberL x (E.traceComponent L) = 0 := by
      apply Subtype.ext
      funext z
      change L (E.representative (x,z)) = 0
      rw [E.representativeZero x hx z,map_zero]
    rw [hZero,map_zero,smul_zero,smul_zero]

include hframe hφ in
theorem physicalRaisingModel_L2 (x : X dim) :
    smoothSupportedTraceL2 Q.dimensionBound
      (physicalRaisingModel hY hg hK he hlog hA hEll S (E.traceComponent L)) x = Q.raisingOutput x :=
  supportedRaisingModel_L2 hA hEll S hY _ _ _ Q
    (supportedHorizontal_traceComponent hY hg hK he hframe hφ Q)
    (traceModelLogGradient_smul_flatDegree hA hEll S Q) x

include hframe hφ in
theorem physicalLoweringModel_L2 (x : X dim) :
    smoothSupportedTraceL2 Q.dimensionBound
      (physicalLoweringModel hY hg hK he hlog hA hEll S (E.traceComponent L)) x = Q.loweringOutput x :=
  supportedLoweringModel_L2 hA hEll S hY _ _ _ Q
    (supportedHorizontal_traceComponent hY hg hK he hframe hφ Q)
    (traceModelLogGradient_smul_flatDegree hA hEll S Q) x

include hframe hφ in
theorem physicalRaisingModel_pairing (D : AngularModelData E r) :
    let T := physicalRaisingModel hY hg hK he hlog hA hEll S
    let u := T (E.traceComponent Complex.reCLM)
    let v := T (E.traceComponent Complex.imCLM)
    D.raisingSquare =
      smoothSupportedTracePairing D.dimensionBound (metricDensity g) u u+
        smoothSupportedTracePairing D.dimensionBound (metricDensity g) v v := by
  dsimp only
  rw [smoothSupportedTracePairing_self_eq_setIntegral,smoothSupportedTracePairing_self_eq_setIntegral]
  simp_rw [physicalRaisingModel_L2 hY hg hK he hlog hA hEll S hframe hφ D.realComponent,
    physicalRaisingModel_L2 hY hg hK he hlog hA hEll S hframe hφ D.imagComponent]
  rfl

include hframe hφ in
theorem physicalLoweringModel_pairing (D : AngularModelData E r) :
    let T := physicalLoweringModel hY hg hK he hlog hA hEll S
    let u := T (E.traceComponent Complex.reCLM)
    let v := T (E.traceComponent Complex.imCLM)
    D.loweringSquare =
      smoothSupportedTracePairing D.dimensionBound (metricDensity g) u u+
        smoothSupportedTracePairing D.dimensionBound (metricDensity g) v v := by
  dsimp only
  rw [smoothSupportedTracePairing_self_eq_setIntegral,smoothSupportedTracePairing_self_eq_setIntegral]
  simp_rw [physicalLoweringModel_L2 hY hg hK he hlog hA hEll S hframe hφ D.realComponent,
    physicalLoweringModel_L2 hY hg hK he hlog hA hEll S hframe hφ D.imagComponent]
  rfl

end CalderonN
