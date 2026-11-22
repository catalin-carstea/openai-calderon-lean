module

public import Proof.CalderonN.PhysicalTraceModelPairings
public import Proof.CalderonN.SmoothSupportedHorizontalAdjoint
public import Proof.CalderonN.SupportedHorizontalRotationCovariance

import Proof.CalderonN.MetricSmooth
import Mathlib.Tactic

/-! Exact adjoint correction for the physical raising model. The
divergence of the moving frame cancels its horizontal connection term. -/

public section

noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Elementwise InnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option maxSynthPendingDepth 24
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE OAI.AnisotropicCalderon SphereHarmonic
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)}

private theorem smoothTraceDegree_comm_lowering (hn : 3 ≤ dim)
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
    {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim, ConormalTaylorSolutions A ell f) (i : I dim) :
    let B := smoothTraceFlatDegree hA hEll S
    let L := smoothTraceLowering B i
    B*L-L*B = -L := by
  dsimp only
  let B := smoothTraceFlatDegree hA hEll S
  let L := smoothTraceLowering B i
  have hB := smoothTraceDegree_projection (smoothTraceFlatDegree_symmetric hn hA hEll S)
    (smoothTraceFlatDegree_finite hA hEll S)
  have hL := harmonicProjection_smoothTraceLowering hn hA hEll S i
  ext u : 1
  apply smoothSphereTraceL2_injective hn
  apply sphereHarmonicDecomposition.injective
  apply lp.ext
  funext k
  rw [sphereHarmonicDecomposition_apply,sphereHarmonicDecomposition_apply]
  change harmonicProjection k (smoothSphereTraceL2 hn (B (L u)-L (B u))) =
    harmonicProjection k (smoothSphereTraceL2 hn (-L u))
  simp only [B,L,map_sub,map_neg,hB,hL,map_smul,Nat.cast_succ]
  rw [← sub_smul,show (k:ℝ)-((k:ℝ)+1) = -1 by ring,neg_one_smul]

theorem supportedFlatDegree_comm_lowering (hn : 3 ≤ dim) (hY : IsOpen Y)
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
    {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim, ConormalTaylorSolutions A ell f) (i : I dim) :
    let B := supportedFlatDegree hA hEll S hY
    let L := supportedLowering hA hEll S hY i
    B*L-L*B = -L := by
  dsimp only
  ext u : 1
  apply smoothSupportedTraceSection_ext_by_fibers
  intro x hx
  simp only [LinearMap.sub_apply,LinearMap.neg_apply,map_sub,map_neg,Module.End.mul_apply,
    smoothSupportedTraceFiberAction_fiber]
  have h := congrArg (fun T : Module.End ℝ (SmoothSphereTrace dim) => T (smoothSupportedTraceFiberL x u))
    (smoothTraceDegree_comm_lowering hn hA hEll S i)
  simpa only [LinearMap.sub_apply,LinearMap.neg_apply,Module.End.mul_apply] using h

variable {g : MetricField dim} {e : Frame dim} {K : ℝ}
  (hY : IsOpen Y) (hg : Elliptic Y K g) (hK : 0 < K)
  (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
  (hframe : ∀ x ∈ Y,∀ i j,metricPair g x (e x i) (e x j) = if i=j then 1 else 0)

include hY hg hK he hframe in
theorem traceDensityDivergence_frame_eq {x : X dim} (hx : x ∈ Y) (i : I dim) :
    traceDensityDivergence (metricDensity g) (fun q => e q i) x =
      -(∑ j : I dim,frameConnectionCoefficient g e x (e x j) j i) := by
  have hD := weightedDivergence_metric_frame hY hg hK e hx (hframe x hx) (fun q => e q i)
    (((he i).contDiffAt (hY.mem_nhds hx)).differentiableAt (by simp))
  have hp : 0 < metricDensity g x := Real.sqrt_pos.2 (hg.posDef hK hx).det_pos
  rw [traceDensityDivergence,hD]
  have hEq : (∑ j : I dim, metricPair g x
      (fderiv ℝ (fun q => e q i) x (e x j)+connection g x (e x j) (e x i)) (e x j)) =
      -(∑ j : I dim,frameConnectionCoefficient g e x (e x j) j i) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => frameConnection_skew hY hg hK e he hframe hx (e x j) i j
  rw [hEq]
  exact mul_div_cancel_left₀ _ hp.ne'

variable (hn : 3 ≤ dim)
  {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
  {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
  {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim, ConormalTaylorSolutions A ell f)

include hn hframe in
theorem supportedFrame_lowering_divergence_cancellation :
    let H (i : I dim) := supportedHorizontal hY hg hK he (fun q => e q i) (he i)
    let L (i : I dim) := supportedLowering hA hEll S hY i
    let μ := metricDensity g
    let hμ := hg.contDiffOn_density hK
    let hp (q : X dim) (hq : q ∈ Y) : 0 < μ q := Real.sqrt_pos.2 (hg.posDef hK hq).det_pos
    let M (i : I dim) := smoothSupportedTraceBaseMul hY (traceDensityDivergence μ (fun q => e q i))
      (contDiffOn_traceDensityDivergence hY μ hμ hp _ (he i))
    (∑ i : I dim, ((H i*L i-L i*H i)+M i*L i)) = 0 := by
  dsimp only
  let H (i : I dim) := supportedHorizontal hY hg hK he (fun q => e q i) (he i)
  let L (i : I dim) := supportedLowering hA hEll S hY i
  let μ := metricDensity g
  let δ (i : I dim) := traceDensityDivergence μ (fun q => e q i)
  let Γ (i j : I dim) (q : X dim) := frameConnectionCoefficient g e q (e q i) i j
  have hΓ (i j : I dim) := hg.contDiffOn_frameConnection hY hK e he _ (he i) i j
  have hδ (i : I dim) : ContDiffOn ℝ ∞ (δ i) Y :=
    contDiffOn_traceDensityDivergence hY μ (hg.contDiffOn_density hK)
      (fun x hx => Real.sqrt_pos.2 (hg.posDef hK hx).det_pos) _ (he i)
  have hH (i : I dim) : H i*L i-L i*H i =
      ∑ j : I dim, smoothSupportedTraceBaseMul hY (Γ i j) (hΓ i j)*L j :=
    supportedHorizontal_comm_rotating_family hY hg hK he hframe _ (he i) _
      (smoothSupportedTraceFiberRegular_lowering hA hEll S hY) (supportedLowering_comm_base hn hA hEll S hY)
      (smoothTraceLowering_rotation_comm hn hA hEll S) i
  change (∑ i : I dim,((H i*L i-L i*H i)+smoothSupportedTraceBaseMul hY (δ i) (hδ i)*L i)) = 0
  simp only [hH,Finset.sum_add_distrib]
  rw [Finset.sum_comm (f:=fun i j : I dim => smoothSupportedTraceBaseMul hY (Γ i j) (hΓ i j)*L j),
    ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro i _
  rw [← Finset.sum_mul,← smoothSupportedTraceBaseMul_sum hY Finset.univ (fun j => Γ j i) (fun j => hΓ j i),
    ← add_mul]
  have hEq : EqOn (δ i) (fun x => -(∑ j : I dim,Γ j i x)) Y :=
    fun x hx => traceDensityDivergence_frame_eq hY hg hK he hframe hx i
  have hSum : ContDiffOn ℝ ∞ (fun x => ∑ j : I dim,Γ j i x) Y :=
    ContDiffOn.sum (fun j _ => hΓ j i)
  rw [smoothSupportedTraceBaseMul_congr hY (hδ i) hSum.neg hEq,
    smoothSupportedTraceBaseMul_neg hY _ hSum,add_neg_cancel,zero_mul]


variable {r : X dim → ℝ} (hlog : ContDiffOn ℝ ∞ (fun x => Real.log (r x)) Y)

/-- The correction in the adjoint of the degree-raising model is the
logarithmic radius gradient paired with angular lowering. -/
@[expose] def physicalTraceModelCorrection : Module.End ℝ (SmoothSupportedTraceSection Y) :=
  ∑ i : I dim,smoothSupportedTraceBaseMul hY (traceModelLogGradient e r i)
    (contDiffOn_traceModelLogGradient hY he hlog i)*supportedLowering hA hEll S hY i

include hframe in
theorem pairedAdjoint_physicalRaisingModel :
    PairedAdjoint (smoothSupportedTracePairingL hn hY (metricDensity g) (hg.contDiffOn_density hK))
      (physicalRaisingModel hY hg hK he hlog hA hEll S)
      (physicalLoweringModel hY hg hK he hlog hA hEll S-
        physicalTraceModelCorrection hY he hA hEll S hlog) := by
  let μ := metricDensity g
  have hμ := hg.contDiffOn_density hK
  have hp (x : X dim) (hx : x ∈ Y) : 0 < μ x := Real.sqrt_pos.2 (hg.posDef hK hx).det_pos
  let Pair := smoothSupportedTracePairingL hn hY μ hμ
  let H (i : I dim) := supportedHorizontal hY hg hK he (fun q => e q i) (he i)
  let L (i : I dim) := supportedLowering hA hEll S hY i
  let R (i : I dim) := supportedRaising hA hEll S hY i
  let B := supportedFlatDegree hA hEll S hY
  let b (i : I dim) := traceModelLogGradient e r i
  let hb (i : I dim) := contDiffOn_traceModelLogGradient hY he hlog i
  let F (i : I dim) := smoothSupportedTraceBaseMul hY (b i) (hb i)
  let M (i : I dim) := smoothSupportedTraceBaseMul hY (traceDensityDivergence μ (fun q => e q i))
    (contDiffOn_traceDensityDivergence hY μ hμ hp _ (he i))
  have hB : PairedAdjoint Pair B B := pairedAdjoint_supportedFlatDegree hn hY μ hμ hA hEll S
  have hH (i : I dim) : PairedAdjoint Pair (H i) (-H i-M i) :=
    pairedAdjoint_supportedHorizontal hY hn μ hμ hp hg hK he _ (he i)
  have hR (i : I dim) : PairedAdjoint Pair (R i) (L i) :=
    pairedAdjoint_supportedRaising hn hY μ hμ hA hEll S i
  have hF (i : I dim) : PairedAdjoint Pair (F i) (F i) := pairedAdjoint_supportedBaseMul hn hY μ hμ _ _
  let Td (i : I dim) := (-H i-M i+B*F i)*L i
  have hAdj : PairedAdjoint Pair (∑ i : I dim,R i*(H i+F i*B)) (∑ i,Td i) :=
    PairedAdjoint.sum Finset.univ _ _ (fun i _ => (hR i).mul ((hH i).add ((hF i).mul hB)))
  have hDiff (i : I dim) : Td i =
      L i*(-H i+F i*B)-F i*L i-((H i*L i-L i*H i)+M i*L i) := by
    have hComB : F i*B = B*F i := smoothSupportedTraceBaseMul_comm_fiber hY _ _ _ _
    have hComL : F i*L i = L i*F i := smoothSupportedTraceBaseMul_comm_fiber hY _ _ _ _
    have hDeg : B*L i-L i*B = -L i := supportedFlatDegree_comm_lowering hn hY hA hEll S i
    have hDeg' : B*L i = L i*B-L i := by
      rw [eq_sub_iff_add_eq]
      have hr := (sub_eq_iff_eq_add.mp hDeg)
      rw [hr]
      abel
    dsimp only [Td]
    rw [← hComB,add_mul,mul_assoc (F i) B (L i),hDeg',mul_sub,← mul_assoc (F i) (L i) B,hComL]
    noncomm_ring
  have hCancel : (∑ i : I dim,((H i*L i-L i*H i)+M i*L i)) = 0 :=
    supportedFrame_lowering_divergence_cancellation hY hg hK he hframe hn hA hEll S
  simp only [hDiff,Finset.sum_sub_distrib,hCancel,sub_zero] at hAdj
  exact hAdj

end CalderonN
