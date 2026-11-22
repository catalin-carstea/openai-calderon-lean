module

public import Proof.CalderonN.NormalPhase

import Proof.CalderonN.GeodesicFirstVariation
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set Metric Filter
open scoped Topology ContDiff

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

/-- The physical velocity of the radial geodesic at its outer endpoint. -/
@[expose] def terminalVelocity (E : (X dim) × (X dim) → (X dim)) (y v : (X dim)) : (X dim) :=
  deriv (fun t : ℝ => E (y,t • v)) 1

theorem exists_smooth_curve_germ {D : Set ℝ} (hD : IsOpen D) (h₀ : (0 : ℝ) ∈ D)
    {u : ℝ → (X dim)} (hu : ContDiffOn ℝ ∞ u D) :
    ∃ v : ℝ → (X dim), ContDiff ℝ ∞ v ∧ v =ᶠ[𝓝 (0 : ℝ)] u := by
  obtain ⟨δ,hδ,hδD⟩ := Metric.isOpen_iff.mp hD 0 h₀
  let χ : ContDiffBump (0 : ℝ) := ⟨δ/4,δ/2,by positivity,by linarith⟩
  let v (t : ℝ) := χ t • u t
  have hχD : tsupport (χ : ℝ → ℝ) ⊆ D := by
    rw [χ.tsupport_eq]
    exact (closedBall_subset_ball (by change δ/2 < δ; linarith)).trans hδD
  refine ⟨v,contDiff_iff_contDiffAt.mpr (fun x => ?_),?_⟩
  · by_cases hx : x ∈ D
    · exact χ.contDiff.contDiffAt.smul (hu.contDiffAt (hD.mem_nhds hx))
    · have hzero : (χ : ℝ → ℝ) =ᶠ[𝓝 x] fun _ => 0 :=
        notMem_tsupport_iff_eventuallyEq.mp (fun h => hx (hχD h))
      have he : v =ᶠ[𝓝 x] fun _ => (0 : (X dim)) :=
        hzero.mono (fun z hz => by change χ z = 0 at hz; simp [v,hz])
      exact contDiffAt_const.congr_of_eventuallyEq he
  · filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (show 0 < χ.rIn by exact χ.rIn_pos))] with t ht
    simp [v,χ.one_of_mem_closedBall (ball_subset_closedBall ht)]

/-- The two exact covectors of the moving normal phase, with the
same exponential and inverse velocity throughout. -/
theorem fderiv_normalPhase_eq_endpoint_terms
    {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {γ : (MetricField dim)} (hγ : SmoothMetric Ω γ) {R : ℝ}
    {E V : (X dim) × (X dim) → (X dim)} (hE : ContDiff ℝ ∞ E)
    (hN : NormalCoordinates Y Ω γ E (fun _ => R))
    {r : (X dim) → ℝ} (hr : ContDiffOn ℝ ∞ r Y)
    (hYΩ : Y ⊆ Ω)
    (hD : IsOpen (normalPairDomain Y γ R E))
    (hV : ContDiffOn ℝ ∞ V (normalPairDomain Y γ R E))
    (hinv : ∀ p ∈ normalPairDomain Y γ R E,
      (p.2,V p) ∈ normalVelocityDomain Y γ R ∧ E (p.2,V p) = p.1)
    {p : (X dim) × (X dim)} (hp : p ∈ normalPairDomain Y γ R E) (w : (X dim) × (X dim)) :
    fderiv ℝ (normalPhase γ V r) p w =
      metricPair γ p.1 (terminalVelocity E p.2 (V p)) w.1 -
        metricPair γ p.2 (V p) w.2 - r p.2 * fderiv ℝ r p.2 w.2 := by
  let D := normalPairDomain Y γ R E
  let P (s : ℝ) := p+s • w
  let S := P ⁻¹' D
  have hP : ContDiff ℝ ∞ P := contDiff_const.add
    ((contDiff_id : ContDiff ℝ ∞ (id : ℝ → ℝ)).smul contDiff_const)
  have hP₀ : P 0 = p := by simp [P]
  have hs₀ : (0 : ℝ) ∈ S := by change P 0 ∈ D; rwa [hP₀]
  have hS : IsOpen S := hD.preimage hP.continuous
  have hVP : ContDiffOn ℝ ∞ (fun s => V (P s)) S :=
    hV.comp hP.contDiffOn (fun _ h => h)
  obtain ⟨v,hv,hvEq⟩ := exists_smooth_curve_germ hS hs₀ hVP
  let q (a : ℝ × ℝ) := E ((P a.1).2,a.2 • v a.1)
  have hq : ContDiff ℝ ∞ q := hE.comp
    (((hP.comp contDiff_fst).snd).prodMk (contDiff_snd.smul (hv.comp contDiff_fst)))
  have hFam : ∀ᶠ s in 𝓝 (0 : ℝ),
      (P s).2 ∈ Y ∧ v s ∈ disk γ (P s).2 R ∧ q (s,1) = (P s).1 := by
    filter_upwards [hS.mem_nhds hs₀,hvEq] with s hs he
    obtain ⟨h,hh⟩ := hinv (P s) hs
    exact ⟨h.1,he.symm ▸ h.2.le,by simp [q,he,hh]⟩
  have hcurve (s t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
      (hs : (P s).2 ∈ Y) (hvs : v s ∈ disk γ (P s).2 R) :
      q (s,t) ∈ Ω := by
    have hmetric : 0 ≤ metricPair γ (P s).2 (v s) (v s) :=
      metricPair_nonneg_of_posDef (hγ.2 _ (hYΩ hs)) _
    have hu : t • v s ∈ disk γ (P s).2 R := by
      change metricPair γ (P s).2 (t • v s) (t • v s) ≤ R^2
      rw [metricPair_smul_same]
      exact (mul_le_of_le_one_left hmetric (pow_le_one₀ ht.1 ht.2)).trans hvs
    exact ((hN.2 _ hs).2.2 _ hu).1
  have htvel (s t : ℝ) : timeVelocity q (s,t) = deriv (fun z : ℝ => q (s,z)) t :=
    (hasDerivAt_geodesicTime (hq.differentiable (by simp) (s,t))).deriv.symm
  have htacc (s t : ℝ) : timeVelocity (timeVelocity q) (s,t) =
      deriv (deriv (fun z : ℝ => q (s,z))) t := by
    rw [← show (fun z : ℝ => timeVelocity q (s,z)) = deriv (fun z : ℝ => q (s,z)) from funext (htvel s)]
    exact (hasDerivAt_geodesicTime ((contDiff_timeVelocity hq).differentiable (by simp) (s,t))).deriv.symm
  have hgeo : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) 1,
      q (s,t) ∈ Ω ∧ timeVelocity (timeVelocity q) (s,t) =
        -connection γ (q (s,t)) (timeVelocity q (s,t)) (timeVelocity q (s,t)) := by
    filter_upwards [hFam] with s hs t ht
    refine ⟨hcurve s t ht hs.1 hs.2.1,?_⟩
    rw [htacc,htvel]
    exact ((hN.2 _ hs.1).2.2 _ hs.2.1).2.2.2.2 t ht
  have hInit : ∀ᶠ s in 𝓝 (0 : ℝ), q (s,0) = (P s).2 ∧ timeVelocity q (s,0) = V (P s) := by
    filter_upwards [hFam,hvEq] with s hs he
    have h := ((hN.2 _ hs.1).2.2 _ hs.2.1).2.2
    exact ⟨h.1,(htvel s 0).trans (h.2.1.trans he)⟩
  have hv₀ : v 0 = V p := by
    have h := hvEq.eq_of_nhds
    change v 0 = V (P 0) at h
    simpa only [hP₀] using h
  have hq₀ : q (0,0) = p.2 := (hInit.self_of_nhds.1).trans (congrArg Prod.snd hP₀)
  have hq₁ : q (0,1) = p.1 := hFam.self_of_nhds.2.2.trans (congrArg Prod.fst hP₀)
  have hvInit : timeVelocity q (0,0) = V p :=
    (hInit.self_of_nhds.2).trans (congrArg V hP₀)
  have hvEnd : timeVelocity q (0,1) = terminalVelocity E p.2 (V p) := by
    rw [htvel]
    have he : (fun z : ℝ => q (0,z)) = fun z => E (p.2,z • V p) := by
      funext z
      simp only [q,hP₀,hv₀]
    rw [he,terminalVelocity]
  have hPDeriv : HasDerivAt P w 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add p
    simpa only [P,id_eq,one_smul] using h
  have hleft : pathVariation q (0,0) = w.2 := by
    apply HasDerivAt.unique (hasDerivAt_variation_slice (hq.differentiable (by simp) (0,0)))
    exact ((ContinuousLinearMap.snd ℝ (X dim) (X dim)).hasFDerivAt.comp_hasDerivAt 0 hPDeriv).congr_of_eventuallyEq
      (hInit.mono (fun s hs => hs.1))
  have hright : pathVariation q (0,1) = w.1 := by
    apply HasDerivAt.unique (hasDerivAt_variation_slice (hq.differentiable (by simp) (0,1)))
    exact ((ContinuousLinearMap.fst ℝ (X dim) (X dim)).hasFDerivAt.comp_hasDerivAt 0 hPDeriv).congr_of_eventuallyEq
      (hFam.mono (fun s hs => hs.2.2))
  have hFirst := geodesic_firstVariation hΩ hγ hq hgeo
  rw [hq₀,hq₁,hvInit,hvEnd,hleft,hright] at hFirst
  have hEnergy : HasDerivAt
      (fun s => metricPair γ (P s).2 (V (P s)) (V (P s))/2) _ 0 :=
    hFirst.congr_of_eventuallyEq (hInit.mono (fun s hs => by dsimp only; rw [hs.1,hs.2]))
  have hpY : p.2 ∈ Y := (hinv p hp).1.1
  have hrD : HasFDerivAt r (fderiv ℝ r p.2) ((P 0).2) := by
    rw [hP₀]
    exact ((hr.contDiffAt (hY.mem_nhds hpY)).differentiableAt (by simp)).hasFDerivAt
  have hrLine : HasDerivAt (fun s => r (P s).2) (fderiv ℝ r p.2 w.2) 0 :=
    hrD.comp_hasDerivAt 0 ((ContinuousLinearMap.snd ℝ (X dim) (X dim)).hasFDerivAt.comp_hasDerivAt 0 hPDeriv)
  have hHalf : HasDerivAt (fun s => (r (P s).2)^2/2) (r p.2*fderiv ℝ r p.2 w.2) 0 := by
    have h := (hrLine.fun_mul hrLine).div_const (2 : ℝ)
    convert h using 1
    · funext s
      ring
    · rw [hP₀]
      ring
  have hPH := hEnergy.fun_sub hHalf
  have hF : HasDerivAt (fun s => normalPhase γ V r (P s))
      (metricPair γ p.1 (terminalVelocity E p.2 (V p)) w.1 -
        metricPair γ p.2 (V p) w.2 - r p.2 * fderiv ℝ r p.2 w.2) 0 := by
    convert hPH using 1
    funext s
    unfold normalPhase
    ring
  have hDiff : HasFDerivAt (normalPhase γ V r) (fderiv ℝ (normalPhase γ V r) p) (P 0) := by
    rw [hP₀]
    have hγY : SmoothMetric Y γ := ⟨fun i j => (hγ.1 i j).mono hYΩ,fun y hy => hγ.2 y (hYΩ hy)⟩
    have hsm := contDiffOn_normalPhase hγY (fun z hz => (hinv z hz).1.1) hV hr
    exact ((hsm.contDiffAt (hD.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
  exact (hDiff.comp_hasDerivAt 0 hPDeriv).unique hF

end CalderonN
