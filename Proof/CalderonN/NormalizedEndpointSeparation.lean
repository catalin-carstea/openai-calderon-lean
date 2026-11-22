module

public import Proof.CalderonN.NormalEndpointJets
public import Proof.CalderonN.ScaledGreenDatumJets

import Proof.CalderonN.CompactBounds
import Proof.CalderonN.MetricPair
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

public section

set_option maxHeartbeats 2000000

noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff Interval

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

/-- The chart displacement of a framed normal endpoint is bounded
below by a fixed multiple of its radius, including along families that
approach radius zero. -/
theorem exists_uniform_normalBallChartMap_separation_linear
    {A : Set ℝ} (hA : IsCompact A) {K Y Ω : Set (X dim)} (hK : IsCompact K) (hKY : K ⊆ Y)
    {γ : ℝ → (MetricField dim)} {E : ℝ → (X dim) × (X dim) → (X dim)} {e : ℝ → (Frame dim)}
    (hE : ContDiff ℝ ∞ (fun q : ℝ × ((X dim) × (X dim)) => E q.1 q.2))
    (he : ∀ i, ContDiff ℝ ∞ (fun q : ℝ × (X dim) => e q.1 q.2 i))
    {ρ : ℝ} (hρ : 0 < ρ)
    (hNormal : ∀ lam ∈ A, NormalCoordinates Y Ω (γ lam) (E lam) (fun _ => ρ))
    (hFrame : ∀ lam ∈ A, ∀ y ∈ K, ∀ i j, metricPair (γ lam) y (e lam y i) (e lam y j) =
      if i=j then 1 else 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ lam ∈ A, ∀ y ∈ K, ∀ r ∈ Icc 0 ρ, ∀ w ∈ (standardSphere dim),
      c*r ≤ ‖normalBallChartMap (E lam) (e lam) y r w-y‖ := by
  let P := ℝ × ((X dim) × (ℝ × (X dim)))
  let F (q : P) := frameVector (e q.1) q.2.1 q.2.2.2
  let G (z : ℝ × ((X dim) × (X dim))) := E z.1 z.2
  let J (q : P) (t : ℝ) := fderiv ℝ G (q.1,(q.2.1,(t*q.2.2.1) • F q)) (0,(0,F q))
  let D (q : P) := ∫ t in Icc (0 : ℝ) 1, J q t
  have hF : ContDiff ℝ ∞ F := contDiff_family_frameVector
    (fun i => (he i).comp (contDiff_fst.prodMk contDiff_snd.fst)) contDiff_snd.snd.snd
  have hG : ContDiff ℝ ∞ G := hE
  have hJ : ContDiff ℝ ∞ (fun q : P × ℝ => J q.1 q.2) := by
    let B (q : P × ℝ) := (q.1.1,(q.1.2.1,(q.2*q.1.2.2.1) • F q.1))
    have hB : ContDiff ℝ ∞ B := contDiff_fst.fst.prodMk (contDiff_fst.snd.fst.prodMk
      ((contDiff_snd.mul contDiff_fst.snd.snd.fst).smul (hF.comp contDiff_fst)))
    exact ((hG.fderiv_right (m := ∞) (by simp)).comp hB).clm_apply
      (contDiff_const.prodMk (contDiff_const.prodMk (hF.comp contDiff_fst)))
  have hD : Continuous D := continuous_parametric_integral_of_continuous (μ := volume)
    hJ.continuous isCompact_Icc
  have hD₀ (lam : ℝ) (hl : lam ∈ A) (y : (X dim)) (hy : y ∈ K) (w : (X dim)) :
      D (lam,(y,(0,w))) = frameVector (e lam) y w := by
    let z := frameVector (e lam) y w
    have hz := (hNormal lam hl).vertical_zero (hKY hy) (e lam) (hFrame lam hl y hy) z
    have hVert (v : (X dim) × (X dim)) :
        fderiv ℝ (E lam) (y,0) v = fderiv ℝ G (lam,(y,0)) (0,v) := by
      have h := (hG.differentiable (by simp) (lam,(y,0))).hasFDerivAt.comp (y,(0 : X dim))
        (hasFDerivAt_prodMk_right (𝕜 := ℝ) lam (y,(0 : X dim)))
      rw [show fderiv ℝ (E lam) (y,0) = _ from h.fderiv]
      rfl
    have hVal : fderiv ℝ G (lam,(y,0)) (0,(0,z)) = z := (hVert (0,z)).symm.trans hz
    have hJ0 : (fun t => J (lam,(y,(0,w))) t) = fun _ => z := by
      funext t
      simpa only [J,F,mul_zero,zero_smul] using hVal
    change (∫ t in Icc (0 : ℝ) 1, J (lam,(y,(0,w))) t) = z
    rw [show (∫ t in Icc (0 : ℝ) 1, J (lam,(y,(0,w))) t) =
      ∫ t in Icc (0 : ℝ) 1, z from congrArg (fun f : ℝ → (X dim) => ∫ t in Icc (0 : ℝ) 1, f t) hJ0]
    simp
  have hDscale (lam : ℝ) (hl : lam ∈ A) (y : (X dim)) (hy : y ∈ K) (r : ℝ) (w : (X dim)) :
      r • D (lam,(y,(r,w))) = normalBallChartMap (E lam) (e lam) y r w-y := by
    let z := frameVector (e lam) y w
    let Q (t : ℝ) := (lam,(y,(t*r) • z))
    let f (t : ℝ) := G (Q t)
    have hQ (t : ℝ) : HasDerivAt Q (0,(0,r • z)) t := by
      have ht : HasDerivAt (fun s : ℝ => (s*r) • z) (r • z) t := by
        simpa only [id_eq,one_mul] using ((hasDerivAt_id t).mul_const r).smul_const z
      exact (hasDerivAt_const t lam).prodMk ((hasDerivAt_const t y).prodMk ht)
    have hf (t : ℝ) : HasDerivAt f (r • J (lam,(y,(r,w))) t) t := by
      have h := ((hG.differentiable (by simp) (Q t)).hasFDerivAt.comp_hasDerivAt t (hQ t))
      have hEq : ((0:ℝ),((0:(X dim)),r • z)) = r • ((0:ℝ),((0:(X dim)),z)) := by simp
      rw [hEq,map_smul] at h
      exact h
    have hSlice : Continuous (fun t => J (lam,(y,(r,w))) t) :=
      hJ.continuous.comp ((continuous_const : Continuous (fun _ : ℝ => ((lam,(y,(r,w))) : P))).prodMk continuous_id)
    have hf' : Continuous (fun t => r • J (lam,(y,(r,w))) t) :=
      (continuous_const : Continuous (fun _ : ℝ => r)).smul hSlice
    have hFTC := intervalIntegral.integral_deriv_eq_sub' f (funext fun t => (hf t).deriv)
      (fun t _ => (hf t).differentiableAt) hf'.continuousOn
      (a := 0) (b := 1)
    rw [intervalIntegral.integral_of_le zero_le_one,← integral_Icc_eq_integral_Ioc,integral_smul] at hFTC
    change r • D (lam,(y,(r,w))) = f 1-f 0 at hFTC
    rw [hFTC]
    simp only [f,Q,G,one_mul,zero_mul,zero_smul,normalBallChartMap,z]
    rw [(hNormal lam hl).exp_zero (hKY hy)]
  let S := A ×ˢ (K ×ˢ (Icc 0 ρ ×ˢ (standardSphere dim)))
  have hS : IsCompact S := hA.prod (hK.prod (isCompact_Icc.prod (isCompact_sphere (0 : (X dim)) 1)))
  have hPos (q : P) (hq : q ∈ S) : 0 < ‖D q‖ := by
    rcases q with ⟨lam,y,r,w⟩
    obtain ⟨hl,hy,hr,hw⟩ := hq
    have hFr := hFrame lam hl y hy
    have hSw : frameVector (e lam) y w ∈ sphereAt (γ lam) y :=
      frameVector_mem_sphere (γ lam) (e lam) y hFr ⟨w,hw⟩
    have hw₀ : frameVector (e lam) y w ≠ 0 := by
      intro hz
      rw [hz] at hSw
      simp [sphereAt,metricPair] at hSw
    change 0 ≤ r ∧ r ≤ ρ at hr
    rcases hr.1.eq_or_lt with hz | hpos
    · subst r
      rw [hD₀ lam hl y hy]
      exact norm_pos_iff.mpr hw₀
    · apply norm_pos_iff.mpr
      intro hDzero
      have h := hDscale lam hl y hy r w
      rw [show D (lam,(y,(r,w))) = 0 from hDzero,smul_zero] at h
      have hVal : E lam (y,r • frameVector (e lam) y w) = y :=
        sub_eq_zero.mp h.symm
      have hLoc := (hNormal lam hl).2 y (hKY hy)
      have hDisk : r • frameVector (e lam) y w ∈ disk (γ lam) y ρ := by
        change metricPair (γ lam) y (r • frameVector (e lam) y w) (r • frameVector (e lam) y w) ≤ ρ^2
        rw [metricPair_smul_same,show metricPair (γ lam) y (frameVector (e lam) y w)
          (frameVector (e lam) y w) = 1 from hSw,mul_one]
        exact pow_le_pow_left₀ hpos.le hr.2 2
      have hDisk₀ : (0 : (X dim)) ∈ disk (γ lam) y ρ := by simp [disk,metricPair,sq_nonneg]
      have hV₀ := hLoc.2.1 hDisk hDisk₀
        (hVal.trans ((hNormal lam hl).exp_zero (hKY hy)).symm)
      exact (smul_ne_zero hpos.ne' hw₀) hV₀
  obtain ⟨c,hc,hbound⟩ := Carleman.exists_pos_lower_of_compact hS hD.norm.continuousOn hPos
  refine ⟨c,hc,fun lam hl y hy r hr w hw => ?_⟩
  rw [← hDscale lam hl y hy r w, norm_smul,Real.norm_eq_abs,abs_of_nonneg hr.1]
  exact (mul_comm c r).trans_le (mul_le_mul_of_nonneg_left (hbound _ ⟨hl,hy,hr,hw⟩) hr.1)

end CalderonN
