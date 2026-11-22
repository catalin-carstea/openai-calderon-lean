module

public import Proof.CalderonN.TransportedCenterCoefficient

import Proof.CalderonN.NormalMapDerivativeTaylor
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic

/-! The exact constant and linear spatial coefficients of a moving-center
derivative come from the actual signed-radius coefficient in the parallel frame. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4900000
set_option maxSynthPendingDepth 35
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

theorem Admissible.contDiffAt_centerChartCoefficient
    {Y Ω : Set (X dim)} (hΩ : IsOpen Ω) {K ρ c₀ floor ε : ℝ} {m : ℕ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data dim}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    {y : X dim} (hy : y ∈ Y) (w : X dim)
    (hw : frameVectorLinear d.frame y w ∈ disk d.γ y (max ρ (d.radius y))) :
    ContDiffAt ℝ ∞ (centerChartCoefficient d)
      ((y,frameVectorLinear d.frame y),(centerInverseDensity d y,w)) := by
  let U := frameVectorLinear d.frame y
  let v := U w
  let J := normalVerticalJacobian d.expMap y v
  let p : CenterChartInput dim := ((y,U),(centerInverseDensity d y,w))
  let x := d.expMap (y,v)
  obtain ⟨S,hS,hTube,hES⟩ := hd.2.1.1
  have hE : ContDiffAt ℝ ∞ d.expMap (y,v) := hES.contDiffAt (hS.mem_nhds (hTube ⟨hy,hw⟩))
  have hx : x ∈ Ω := ((hd.2.1.2 y hy).2.2 v hw).1
  have hg : ContDiffAt ℝ ∞ d.g₁ x :=
    contDiffAt_pi.mpr fun i => contDiffAt_pi.mpr fun j =>
      (hd.1.2.1.1 i j).contDiffAt (hΩ.mem_nhds hx)
  have hJ : Function.Injective J := by
    have hh := ((hd.2.1.2 y hy).2.2 v hw).2.1
    rw [(hd.2.1.hasFDerivAt_velocity_slice hy v hw).fderiv] at hh
    exact hh.1
  have hyΩ := hd.2.1.center_mem hy
  have hFrame := hd.1.2.2.2.2.2.2.2 y hyΩ
  have hU : Function.Injective U := by
    intro a b hab
    have h := (hd.1.1.frameVector_norm_sq_bounds hK hyΩ d.frame hFrame (a-b)).1
    rw [← frameVectorLinear_apply,show frameVectorLinear d.frame y = U from rfl,
      map_sub,hab,sub_self,norm_zero,zero_pow (by decide : (2 : ℕ) ≠ 0),mul_zero] at h
    exact sub_eq_zero.mp (norm_le_zero_iff.mp (by nlinarith only [h]))
  exact CalderonN.contDiffAt_centerChartCoefficient d p hE hg
    (pullbackMetricMatrix_posDef (q:=centerChartPullbackData d p) (hd.1.2.1.posDef hK hx)
      (hJ.comp hU))

theorem contDiffAt_actualCenterCoefficientFamilyJet
    (d : Data dim) (y a w : X dim)
    (h : ContDiffAt ℝ ∞ (centerChartCoefficient d)
      ((y,frameVectorLinear d.frame y),(centerInverseDensity d y,w))) :
    ContDiffAt ℝ ∞ (actualCenterCoefficientFamilyJet d y a) (0,w) := by
  let U := frameVectorLinear d.frame y
  let P := parallelFrameFirstJet d y a
  let b := centerInverseDensity d y
  let b' := fderiv ℝ (centerInverseDensity d) y a
  let F (p : CenterParameters dim) := ((y+p.1 • a,affineCenterFrame U P p),(b+p.1*b',p.2))
  have hF : ContDiff ℝ ∞ F :=
    (contDiff_const.add (contDiff_fst.smul contDiff_const) |>.prodMk
      (contDiff_affineCenterFrame U P)).prodMk
      ((contDiff_const.add (contDiff_fst.mul contDiff_const)).prodMk contDiff_snd)
  have hp : F (0,w) = ((y,U),(b,w)) := by simp [F,affineCenterFrame]
  exact (show ContDiffAt ℝ ∞ (centerChartCoefficient d) (F (0,w)) by rwa [hp]).comp (0,w) hF.contDiffAt

private theorem hasDerivAt_deriv_other_order {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : CenterParameters dim → E) (h : ContDiffAt ℝ ∞ T (0,0)) (w : X dim) :
    HasDerivAt (fun t => fderiv ℝ T (t,0) (0,w))
      (fderiv ℝ (centerDerivativeSlice T) 0 w) 0 := by
  let V := ContinuousLinearMap.inr ℝ ℝ (X dim)
  let A (p : CenterParameters dim) := fderiv ℝ T p (1,0)
  let B (p : CenterParameters dim) := fderiv ℝ T p (0,w)
  have hD := (h.fderiv_right (m:=∞) (by simp)).differentiableAt (by simp)
  have hA := (ContinuousLinearMap.apply ℝ E ((1:ℝ),(0:X dim))).hasFDerivAt.comp (0,0) hD.hasFDerivAt
  have hA' : HasFDerivAt A _ (V (0 : X dim)) := hA
  have hB := (ContinuousLinearMap.apply ℝ E ((0:ℝ),w)).hasFDerivAt.comp (0,0) hD.hasFDerivAt
  have hP : HasDerivAt (fun t : ℝ => (t,(0:X dim))) (1,0) 0 :=
    (hasDerivAt_id (0:ℝ)).prodMk (hasDerivAt_const (0:ℝ) (0:X dim))
  have hL := hB.comp_hasDerivAt 0 hP
  refine hL.congr_deriv ?_
  change fderiv ℝ (fderiv ℝ T) (0,0) (1,0) (0,w) = fderiv ℝ (A ∘ V) 0 w
  rw [(hA'.comp 0 V.hasFDerivAt).fderiv]
  exact (h.isSymmSndFDerivAt (by simp)).eq (1,0) (0,w)

theorem actualCenterNormalCoefficientDerivative_center_jet (hn : 2 ≤ dim)
    {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) {K ρ c₀ floor ε : ℝ} {m : ℕ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data dim}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K) (hρ : 0 < ρ)
    {y : X dim} (hy : y ∈ Y) (a : X dim) :
    actualCenterNormalCoefficientDerivative d y a 0 = 0 ∧
      fderiv ℝ (actualCenterNormalCoefficientDerivative d y a) 0 =
        (centerDensityCovariantLinear d y a).smulRight (1 : Mat dim) := by
  have hyΩ := hd.2.1.center_mem hy
  have hFrame := hd.1.2.2.2.2.2.2.2 y hyΩ
  obtain ⟨F,hF,hF₀,hFnear⟩ := hd.1.1.exists_local_center_parallelFrame hΩ hK y a hyΩ
    (d.frame y) hFrame
  let q (t : ℝ) := y+t • a
  let U (t : ℝ) := frameVectorLinear (fun _ => F t) (q t)
  let T := transportedCenterCoefficient d y a U
  let L (t : ℝ) := (centerInverseDensity d (q t)) •
    (fderiv ℝ (firstMetricDensityFactor d.γ d.g₁) (q t)).comp (U t)
  have hq : ContDiff ℝ ∞ q := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hq₀ : q 0 = y := by simp [q]
  have hU : ContDiff ℝ ∞ U := contDiff_frameVectorLinear_curve F q hF
  have hU₀ : U 0 = frameVectorLinear d.frame y := by simp [U,hF₀,frameVectorLinear_eq_sum]
  have hUD : HasDerivAt U (parallelFrameFirstJet d y a) 0 :=
    hasDerivAt_parallelFrameOperator d y a F hF₀
      (fun i => by simpa only [zero_smul,add_zero] using hFnear.self_of_nhds.2.1 i)
  have hb : ContDiffAt ℝ ∞ (centerInverseDensity d) y :=
    (hd.1.contDiffOn_centerInverseDensity hK).contDiffAt (hΩ.mem_nhds hyΩ)
  have hf : ContDiffAt ℝ ∞ (firstMetricDensityFactor d.γ d.g₁) y :=
    (hd.1.firstMetricDensityFactor_smooth hK).contDiffAt (hΩ.mem_nhds hyΩ)
  have hLD : HasDerivAt L (centerDensityCovariantLinear d y a) 0 :=
    hasDerivAt_transportedFirstDensity d y a U hU₀ hUD (hb.differentiableAt (by simp))
      ((hf.fderiv_right (m:=∞) (by simp)).differentiableAt (by simp))
  have hyN : ∀ᶠ t in 𝓝 (0:ℝ), q t ∈ Y :=
    hq.continuous.continuousAt.eventually (hY.mem_nhds (hq₀ ▸ hy))
  have hwN : ∀ᶠ w in 𝓝 (0 : X dim),
      frameVectorLinear d.frame y w ∈ disk d.γ y (max ρ (d.radius y)) := by
    have ho : (0 : X dim) ∈ interior (disk d.γ y (max ρ (d.radius y))) := by
      apply mem_interior_disk_of_metricPair_lt
      have he : metricPair d.γ y 0 0 = 0 := by simp [metricPair]
      rw [he]
      exact sq_pos_of_pos (hρ.trans_le (le_max_left _ _))
    exact (frameVectorLinear d.frame y).continuous.continuousAt.eventually
      (isOpen_interior.mem_nhds (by simpa only [map_zero] using ho)) |>.mono
        (fun _ h => interior_subset h)
  have hChart₀ := hd.contDiffAt_centerChartCoefficient hΩ hK hy (0 : X dim) hwN.self_of_nhds
  have hT : ContDiffAt ℝ ∞ T (0,0) := by
    let R (p : CenterParameters dim) := ((q p.1,U p.1),(centerInverseDensity d (q p.1),p.2))
    have hQ : ContDiffAt ℝ ∞ (fun p : CenterParameters dim => q p.1) (0,0) :=
      hq.contDiffAt.comp _ contDiffAt_fst
    have hB := (show ContDiffAt ℝ ∞ (centerInverseDensity d) (q 0) by rwa [hq₀]).comp (0,0) hQ
    have hR : ContDiffAt ℝ ∞ R (0,0) :=
      (hQ.prodMk (hU.contDiffAt.comp _ contDiffAt_fst)).prodMk (hB.prodMk contDiffAt_snd)
    have h₀ : R (0,0) = ((y,frameVectorLinear d.frame y),(centerInverseDensity d y,0)) := by simp [R,hq₀,hU₀]
    exact (show ContDiffAt ℝ ∞ (centerChartCoefficient d) (R (0,0)) by rwa [h₀]).comp (0,0) hR
  have hTN : ∀ᶠ p : CenterParameters dim in 𝓝 ((0 : ℝ),(0 : X dim)), DifferentiableAt ℝ T p :=
    ((hT.of_le (show (1:ℕ∞ω) ≤ ∞ by simp)).eventually (by simp)).mono
      (fun _ hp => hp.differentiableAt (by simp))
  have hDerivativeEq : (centerDerivativeSlice T) =ᶠ[𝓝 (0 : X dim)] actualCenterNormalCoefficientDerivative d y a := by
    have hc : Continuous (fun w : X dim => ((0:ℝ),w)) := continuous_const.prodMk continuous_id
    have hTnear : ∀ᶠ w : X dim in 𝓝 (0 : X dim), DifferentiableAt ℝ T (0,w) :=
      hc.continuousAt.eventually hTN
    filter_upwards [hwN,hTnear] with w hw hTw
    have hCh := hd.contDiffAt_centerChartCoefficient hΩ hK hy w hw
    exact (hasDerivAt_centerDerivativeSlice T w 0 hTw).unique
      (hasDerivAt_transportedCenterCoefficient d y a w U hU₀ hUD (hb.differentiableAt (by simp))
        hCh (contDiffAt_actualCenterCoefficientFamilyJet d y a w hCh))
  have hTZero : (fun t => T (t,0)) =ᶠ[𝓝 (0:ℝ)] fun _ => (1 : Mat dim) := by
    filter_upwards [hFnear,hyN] with t ht hyt
    ext i j
    have he := transportedCenterCoefficient_eq_rescaled d y a 0 F t 0 i j
    rw [zero_smul] at he
    exact he.trans (normalizedFirstNormalCoeff_center_of_frame (d := {d with frame := fun _ => F t})
      hn hd.1 hd.2.1 hK hyt ht.2.2 0 i j)
  have hValue : centerDerivativeSlice T 0 = 0 :=
    (hasDerivAt_centerDerivativeSlice T 0 0 (hT.differentiableAt (by simp))).unique
      ((hasDerivAt_const (0:ℝ) (1 : Mat dim)).congr_of_eventuallyEq hTZero)
  refine ⟨hDerivativeEq.eq_of_nhds.symm.trans hValue,?_⟩
  rw [← hDerivativeEq.fderiv_eq]
  ext1 w
  have hc : Continuous (fun t : ℝ => (t,(0:X dim))) := continuous_id.prodMk continuous_const
  have hTdiff : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), DifferentiableAt ℝ T (t,0) :=
    hc.continuousAt.eventually hTN
  have hLnear : (fun t => fderiv ℝ T (t,0) (0,w)) =ᶠ[𝓝 (0:ℝ)] fun t => L t w • (1 : Mat dim) := by
    filter_upwards [hTdiff,hFnear,hyN] with t ht hFt hyt
    ext i j
    have hCurve (u : ℝ) : HasDerivAt (fun s : ℝ => (t,s • w)) (0,w) u := by
      have hs : HasDerivAt (fun s : ℝ => s • w) w u := by
        simpa only [id_eq,one_smul] using (hasDerivAt_id u).smul_const w
      exact (hasDerivAt_const u t).prodMk hs
    have hTR : HasFDerivAt T (fderiv ℝ T (t,0)) (t,(0:ℝ) • w) := by
      simpa only [zero_smul] using ht.hasFDerivAt
    have hTR' := (matrixEntryL i j).hasFDerivAt.comp_hasDerivAt 0 (hTR.comp_hasDerivAt 0 (hCurve 0))
    have hExact := normalizedFirstNormalCoeff_first_of_frame (d := {d with frame := fun _ => F t})
      hn hΩ hd.1 hd.2.1 hK hyt hFt.2.2 w i j
    have hEx : HasDerivAt (fun s : ℝ => T (t,s • w) i j)
          (L t w*(1 : Mat dim) i j) 0 :=
      hExact.congr_of_eventuallyEq (Filter.Eventually.of_forall
        (fun s => transportedCenterCoefficient_eq_rescaled d y a w F t s i j))
    have hEntry : HasDerivAt (fun s : ℝ => T (t,s • w) i j)
        ((fderiv ℝ T (t,0) (0,w)) i j) 0 := hTR'
    have hSame := hEntry.unique hEx
    simpa only [L,q,firstDensityCenterLinear,centerInverseDensity,U,Matrix.smul_apply,smul_eq_mul]
      using hSame
  have hCom := hasDerivAt_deriv_other_order T hT w
  have hR := ((ContinuousLinearMap.apply ℝ ℝ w).hasFDerivAt.comp_hasDerivAt 0 hLD).smul_const
    (1 : Mat dim)
  exact hCom.unique (hR.congr_of_eventuallyEq hLnear)

end CalderonN
