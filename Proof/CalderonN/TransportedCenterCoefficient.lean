module

public import Proof.CalderonN.AffineNormalizedCenterJets
public import Proof.CalderonN.LocalCenterParallelFrame

import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

/-! The genuine parallel-frame coefficient and the affine extension have
identical first center derivatives at each fixed normal coordinate. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3700000
set_option maxSynthPendingDepth 33
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

abbrev CenterChartInput (dim : ℕ) := (X dim × FrameOperator dim) × (ℝ × X dim)

@[expose] def centerChartPullbackData (d : Data dim) (p : CenterChartInput dim) :
    PullbackCoefficientData dim :=
  let v := p.1.2 p.2.2
  (d.g₁ (d.expMap (p.1.1,v)),
    (normalVerticalJacobian d.expMap p.1.1 v).comp p.1.2)

@[expose] def centerChartCoefficient (d : Data dim) (p : CenterChartInput dim) : Mat dim :=
  p.2.1 • pullbackDivergenceMatrix (centerChartPullbackData d p)

theorem contDiffAt_centerChartCoefficient (d : Data dim) (p : CenterChartInput dim)
    (hE : ContDiffAt ℝ ∞ d.expMap (p.1.1,p.1.2 p.2.2))
    (hg : ContDiffAt ℝ ∞ d.g₁ (d.expMap (p.1.1,p.1.2 p.2.2)))
    (hPos : (pullbackMetricMatrix (centerChartPullbackData d p)).PosDef) :
    ContDiffAt ℝ ∞ (centerChartCoefficient d) p := by
  let A (q : CenterChartInput dim) := (q.1.1,q.1.2 q.2.2)
  have hA : ContDiff ℝ ∞ A := contDiff_fst.fst.prodMk (contDiff_fst.snd.clm_apply contDiff_snd.snd)
  have hX : ContDiffAt ℝ ∞ (d.expMap ∘ A) p := hE.comp p hA.contDiffAt
  have hG : ContDiffAt ℝ ∞ (d.g₁ ∘ d.expMap ∘ A) p := hg.comp p hX
  let J := (ContinuousLinearMap.compL ℝ (X dim) (X dim × X dim) (X dim)).flip
    (ContinuousLinearMap.inr ℝ (X dim) (X dim))
  have hJ : ContDiffAt ℝ ∞ (J ∘ fderiv ℝ d.expMap ∘ A) p :=
    J.contDiff.contDiffAt.comp p ((hE.fderiv_right (m:=∞) (by simp)).comp p hA.contDiffAt)
  have hF : ContDiffAt ℝ ∞ (fun q : CenterChartInput dim => q.1.2) p := contDiffAt_fst.snd
  have hT := hJ.clm_comp hF
  have hData : ContDiffAt ℝ ∞ (centerChartPullbackData d) p := hG.prodMk hT
  exact (contDiffAt_snd.fst : ContDiffAt ℝ ∞ (fun q : CenterChartInput dim => q.2.1) p).smul
    ((contDiffAt_pullbackDivergenceMatrix_of_posDef _ hPos).comp p hData)

@[expose] def transportedCenterCoefficient (d : Data dim) (y a : X dim)
    (F : ℝ → FrameOperator dim) (p : CenterParameters dim) : Mat dim :=
  let q := y+p.1 • a
  centerChartCoefficient d ((q,F p.1),(centerInverseDensity d q,p.2))

theorem transportedCenterCoefficient_eq_rescaled (d : Data dim) (y a z : X dim)
    (F : ℝ → I dim → X dim) (t s : ℝ) (i j : I dim) :
    transportedCenterCoefficient d y a (fun t => frameVectorLinear (fun _ => F t) (y+t • a))
      (t,s • z) i j =
    normalizedFirstNormalCoeff {d with frame := fun _ => F t} (y+t • a) s z i j := by
  let dt : Data dim := {d with frame := fun _ => F t}
  have hh := firstNormalVelocityCoefficient_rescaled dt (y+t • a) z s i j
  simpa only [transportedCenterCoefficient,centerChartCoefficient,centerChartPullbackData,
    firstNormalVelocityCoefficient,centerInverseDensity,dt,map_smul,frameVectorLinear_apply] using hh

lemma frameVectorLinear_eq_sum (e : Frame dim) (y : X dim) :
    frameVectorLinear e y = ∑ i : I dim,
      ContinuousLinearMap.smulRightL ℝ (X dim) (X dim) (EuclideanSpace.proj i) (e y i) := by
  ext v
  rw [frameVectorLinear_apply,frameVector,ContinuousLinearMap.sum_apply]
  rfl

theorem contDiff_frameVectorLinear_curve (F : ℝ → I dim → X dim) (q : ℝ → X dim)
    (hF : ∀ i, ContDiff ℝ ∞ (fun t => F t i)) :
    ContDiff ℝ ∞ (fun t => frameVectorLinear (fun _ => F t) (q t)) := by
  simp only [frameVectorLinear_eq_sum]
  apply ContDiff.sum
  intro i _
  exact (ContinuousLinearMap.smulRightL ℝ (X dim) (X dim) (EuclideanSpace.proj i)).contDiff.comp (hF i)

theorem hasDerivAt_parallelFrameOperator (d : Data dim) (y a : X dim) (F : ℝ → I dim → X dim)
    (hF₀ : F 0 = d.frame y)
    (hF : ∀ i, HasDerivAt (fun t => F t i) (-connection d.γ y a (F 0 i)) 0) :
    HasDerivAt (fun t => frameVectorLinear (fun _ => F t) (y+t • a)) (parallelFrameFirstJet d y a) 0 := by
  simp only [frameVectorLinear_eq_sum]
  have hSum := HasDerivAt.fun_sum (u:=Finset.univ) fun i _ =>
    (ContinuousLinearMap.smulRightL ℝ (X dim) (X dim) (EuclideanSpace.proj i)).hasFDerivAt.comp_hasDerivAt
      0 (hF i)
  refine hSum.congr_deriv ?_
  simp only [hF₀]
  ext1 v
  change (∑ i : I dim, (ContinuousLinearMap.smulRightL ℝ (X dim) (X dim)
    (EuclideanSpace.proj i)) (-connection d.γ y a (d.frame y i))) v = _
  rw [ContinuousLinearMap.sum_apply]
  simp only [parallelFrameFirstJet,ContinuousLinearMap.neg_apply,ContinuousLinearMap.comp_apply,
    frameVectorLinear_apply,← connectionBilinear_apply,frameVector,map_sum,map_smul,smul_neg,Finset.sum_neg_distrib]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  change v i • (-connectionBilinear d.γ y a (d.frame y i)) = -(v i • connectionBilinear d.γ y a (d.frame y i))
  exact smul_neg _ _

/-- The physical center derivative only depends on the first jet of the frame
    and normalization. A genuine parallel frame can therefore be used locally
    even though its higher center derivatives are absent from the estimates. -/
theorem hasDerivAt_transportedCenterCoefficient (d : Data dim) (y a v : X dim)
    (F : ℝ → FrameOperator dim)
    (hF₀ : F 0 = frameVectorLinear d.frame y)
    (hF : HasDerivAt F (parallelFrameFirstJet d y a) 0)
    (hb : DifferentiableAt ℝ (centerInverseDensity d) y)
    (hChart : ContDiffAt ℝ ∞ (centerChartCoefficient d)
      ((y,frameVectorLinear d.frame y),(centerInverseDensity d y,v)))
    (hAff : ContDiffAt ℝ ∞ (actualCenterCoefficientFamilyJet d y a) (0,v)) :
    HasDerivAt (fun t => transportedCenterCoefficient d y a F (t,v))
      (actualCenterNormalCoefficientDerivative d y a v) 0 := by
  let U := frameVectorLinear d.frame y
  let P := parallelFrameFirstJet d y a
  let b := centerInverseDensity d
  let A (t : ℝ) := y+t • a
  have hA : HasDerivAt A a 0 := by
    have hh : HasDerivAt (fun t : ℝ => t • a) a 0 := by
      simpa only [id_eq,one_smul] using (hasDerivAt_id (0:ℝ)).smul_const a
    exact hh.const_add y
  have hA₀ : A 0 = y := by simp [A]
  have hB : HasDerivAt (b ∘ A) (fderiv ℝ b y a) 0 :=
    (show HasFDerivAt b (fderiv ℝ b y) (A 0) by rw [hA₀]; exact hb.hasFDerivAt).comp_hasDerivAt 0 hA
  have hPath := (hA.prodMk hF).prodMk (hB.prodMk (hasDerivAt_const (0:ℝ) v))
  have hPath₀ : ((A 0,F 0),((b ∘ A) 0,v)) = ((y,U),(b y,v)) := by simp [hA₀,hF₀,U]
  have hChart' : HasFDerivAt (centerChartCoefficient d)
      (fderiv ℝ (centerChartCoefficient d) ((y,U),(b y,v))) ((A 0,F 0),((b ∘ A) 0,v)) := by
    rw [hPath₀]
    exact (hChart.differentiableAt (by simp)).hasFDerivAt
  have hMain := hChart'.comp_hasDerivAt 0 hPath
  have hFrameAff : HasDerivAt (fun t : ℝ => U+t • P) P 0 := by
    have hh : HasDerivAt (fun t : ℝ => t • P) P 0 := by
      simpa only [id_eq,one_smul] using (hasDerivAt_id (0:ℝ)).smul_const P
    exact hh.const_add U
  have hAffB : HasDerivAt (fun t : ℝ => b y+t*fderiv ℝ b y a) (fderiv ℝ b y a) 0 := by
    have hh := (hasDerivAt_id (0:ℝ)).mul_const (fderiv ℝ b y a)
    simpa only [id_eq,one_mul] using hh.const_add (b y)
  have hAffPath := (hA.prodMk hFrameAff).prodMk (hAffB.prodMk (hasDerivAt_const (0:ℝ) v))
  have hAffPath₀ : ((A 0,U+(0:ℝ) • P),(b y+0*fderiv ℝ b y a,v)) = ((y,U),(b y,v)) := by simp [hA₀]
  have hAffChart : HasFDerivAt (centerChartCoefficient d)
      (fderiv ℝ (centerChartCoefficient d) ((y,U),(b y,v)))
      ((A 0,U+(0:ℝ) • P),(b y+0*fderiv ℝ b y a,v)) := by
    rw [hAffPath₀]
    exact (hChart.differentiableAt (by simp)).hasFDerivAt
  have hAffCalc : HasDerivAt (fun t => actualCenterCoefficientFamilyJet d y a (t,v))
      (fderiv ℝ (centerChartCoefficient d) ((y,U),(b y,v)) ((a,P),(fderiv ℝ b y a,0))) 0 := by
    have hh := hAffChart.comp_hasDerivAt 0 hAffPath
    exact hh.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => by
      change actualCenterCoefficientFamilyJet d y a (t,v) = _
      simp only [actualCenterCoefficientFamilyJet,affineNormalCoefficient,affineNormalPullbackData,
        affineNormalInput,affineCenterFrame,centerChartCoefficient,centerChartPullbackData,
        Function.comp_apply,A,b,U,P])
  have hSame := hAffCalc.unique
    (hasDerivAt_centerDerivativeSlice (actualCenterCoefficientFamilyJet d y a) v 0
      (hAff.differentiableAt (by simp)))
  exact hMain.congr_deriv hSame

/-- The affine covariance correction for the first scalar density variation. -/
@[expose] def centerDensityCovariantLinear (d : Data dim) (y a : X dim) : X dim →L[ℝ] ℝ :=
  let f := firstMetricDensityFactor d.γ d.g₁
  let U := frameVectorLinear d.frame y
  let P := parallelFrameFirstJet d y a
  let b := centerInverseDensity d
  (b y) • ((fderiv ℝ (fderiv ℝ f) y a).comp U+(fderiv ℝ f y).comp P) +
    (fderiv ℝ b y a) • (fderiv ℝ f y).comp U

theorem hasDerivAt_transportedFirstDensity (d : Data dim) (y a : X dim)
    (F : ℝ → FrameOperator dim)
    (hF₀ : F 0 = frameVectorLinear d.frame y)
    (hF : HasDerivAt F (parallelFrameFirstJet d y a) 0)
    (hb : DifferentiableAt ℝ (centerInverseDensity d) y)
    (hf : DifferentiableAt ℝ (fderiv ℝ (firstMetricDensityFactor d.γ d.g₁)) y) :
    HasDerivAt (fun t =>
      (centerInverseDensity d (y+t • a)) •
        (fderiv ℝ (firstMetricDensityFactor d.γ d.g₁) (y+t • a)).comp (F t))
      (centerDensityCovariantLinear d y a) 0 := by
  let A (t : ℝ) := y+t • a
  let b := centerInverseDensity d
  let f := firstMetricDensityFactor d.γ d.g₁
  have hA : HasDerivAt A a 0 := by
    have hh : HasDerivAt (fun t : ℝ => t • a) a 0 := by
      simpa only [id_eq,one_smul] using (hasDerivAt_id (0:ℝ)).smul_const a
    exact hh.const_add y
  have hA₀ : A 0 = y := by simp [A]
  have hB : HasDerivAt (b ∘ A) (fderiv ℝ b y a) 0 :=
    (show HasFDerivAt b (fderiv ℝ b y) (A 0) by rw [hA₀]; exact hb.hasFDerivAt).comp_hasDerivAt 0 hA
  have hDf : HasDerivAt ((fderiv ℝ f) ∘ A) (fderiv ℝ (fderiv ℝ f) y a) 0 :=
    (show HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) y) (A 0) by
      rw [hA₀]; exact hf.hasFDerivAt).comp_hasDerivAt 0 hA
  have h := hB.smul (hDf.clm_comp hF)
  change HasDerivAt (fun t => b (A t) • (fderiv ℝ f (A t)).comp (F t))
    (b (A 0) • ((fderiv ℝ (fderiv ℝ f) y a).comp (F 0) +
      (fderiv ℝ f (A 0)).comp (parallelFrameFirstJet d y a)) +
        (fderiv ℝ b y a) • (fderiv ℝ f (A 0)).comp (F 0)) 0 at h
  simpa only [hA₀,hF₀,centerDensityCovariantLinear,b,f,A] using h

end CalderonN
