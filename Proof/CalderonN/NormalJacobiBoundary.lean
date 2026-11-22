module

public import Proof.CalderonN.NormalPhaseHessian
public import Proof.CalderonN.GeodesicFirstVariation

import Proof.CalderonN.MetricPair
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

/-- The covariant derivative in time of the variation field along the
actual normal geodesic. -/
@[expose] def variationCovariantTime (g : (MetricField dim)) (q : ℝ × ℝ → (X dim)) (s t : ℝ) : (X dim) :=
  timeVelocity (pathVariation q) (s,t) +
    connection g (q (s,t)) (timeVelocity q (s,t)) (pathVariation q (s,t))

set_option maxHeartbeats 1100000 in
/-- The squared-distance part of the normal phase Hessian is the exact
boundary form of one smooth variation of the radial geodesic. This variation
has the prescribed endpoint variations and obeys the same geodesic IVP. -/
theorem exists_normalPhase_jacobi_boundary
    {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {γ : (MetricField dim)} (hγ : SmoothMetric Ω γ) {R : ℝ}
    {E V : (X dim) × (X dim) → (X dim)} (hE : ContDiff ℝ ∞ E)
    (hN : NormalCoordinates Y Ω γ E (fun _ => R))
    {r : (X dim) → ℝ} (hr : ContDiffOn ℝ ∞ r Y) (hYΩ : Y ⊆ Ω)
    (hD : IsOpen (normalPairDomain Y γ R E))
    (hV : ContDiffOn ℝ ∞ V (normalPairDomain Y γ R E))
    (hinv : ∀ p ∈ normalPairDomain Y γ R E,
      (p.2,V p) ∈ normalVelocityDomain Y γ R ∧ E (p.2,V p) = p.1)
    {p : (X dim) × (X dim)} (hp : p ∈ normalPairDomain Y γ R E) (u : (X dim) × (X dim)) :
    ∃ q : ℝ × ℝ → (X dim), ContDiff ℝ ∞ q ∧
      (∀ t : ℝ, q (0,t) = E (p.2,t • V p)) ∧
      q (0,0) = p.2 ∧ q (0,1) = p.1 ∧ timeVelocity q (0,0) = V p ∧
      pathVariation q (0,0) = u.2 ∧ pathVariation q (0,1) = u.1 ∧
      (∀ᶠ s in 𝓝 (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) 1,
        q (s,t) ∈ Ω ∧ timeVelocity (timeVelocity q) (s,t) =
          -connection γ (q (s,t)) (timeVelocity q (s,t)) (timeVelocity q (s,t))) ∧
      ∀ w : (X dim) × (X dim), productMetricHessian γ γ (normalPhase γ V r) p u w =
        metricPair γ p.1 (variationCovariantTime γ q 0 1) w.1 -
        metricPair γ p.2 (variationCovariantTime γ q 0 0) w.2 -
        fderiv ℝ r p.2 u.2 * fderiv ℝ r p.2 w.2 -
        r p.2 * (fderiv ℝ (fderiv ℝ r) p.2 u.2 w.2 -
          fderiv ℝ r p.2 (connection γ p.2 u.2 w.2)) := by
  let P (s : ℝ) := p+s • u
  let U := P ⁻¹' normalPairDomain Y γ R E
  have hP : ContDiff ℝ ∞ P := contDiff_const.add
    ((contDiff_id : ContDiff ℝ ∞ (id : ℝ → ℝ)).smul contDiff_const)
  have hp₀ : P 0 = p := by simp [P]
  have hU₀ : (0 : ℝ) ∈ U := by
    change P 0 ∈ normalPairDomain Y γ R E
    rwa [hp₀]
  have hU : IsOpen U := hD.preimage hP.continuous
  have hVP : ContDiffOn ℝ ∞ (fun s => V (P s)) U := hV.comp hP.contDiffOn (fun _ h => h)
  obtain ⟨v,hv,hvEq⟩ := exists_smooth_curve_germ hU hU₀ hVP
  let q (a : ℝ × ℝ) := E ((P a.1).2,a.2 • v a.1)
  have hq : ContDiff ℝ ∞ q := hE.comp
    (((hP.comp contDiff_fst).snd).prodMk (contDiff_snd.smul (hv.comp contDiff_fst)))
  let B (a : (X dim) × (X dim)) := terminalVelocity E a.2 (V a)
  have hB : ContDiffOn ℝ ∞ B (normalPairDomain Y γ R E) :=
    (contDiff_terminalVelocity hE).comp_contDiffOn (contDiff_snd.contDiffOn.prodMk hV)
  have htvel (s t : ℝ) : timeVelocity q (s,t) = deriv (fun z : ℝ => q (s,z)) t :=
    (hasDerivAt_geodesicTime (hq.differentiable (by simp) (s,t))).deriv.symm
  have htacc (s t : ℝ) : timeVelocity (timeVelocity q) (s,t) =
      deriv (deriv (fun z : ℝ => q (s,z))) t := by
    rw [← show (fun z : ℝ => timeVelocity q (s,z)) = deriv (fun z : ℝ => q (s,z)) from funext (htvel s)]
    exact (hasDerivAt_geodesicTime ((contDiff_timeVelocity hq).differentiable (by simp) (s,t))).deriv.symm
  have hfamily : ∀ᶠ s in 𝓝 (0 : ℝ),
      q (s,0) = (P s).2 ∧ q (s,1) = (P s).1 ∧ timeVelocity q (s,0) = V (P s) ∧
        timeVelocity q (s,1) = B (P s) ∧
        ∀ t ∈ Icc (0 : ℝ) 1, q (s,t) ∈ Ω ∧ timeVelocity (timeVelocity q) (s,t) =
          -connection γ (q (s,t)) (timeVelocity q (s,t)) (timeVelocity q (s,t)) := by
    filter_upwards [hU.mem_nhds hU₀,hvEq] with s hs he
    obtain ⟨⟨hy,hv'⟩,hEnd⟩ := hinv (P s) hs
    have hvR : v s ∈ disk γ (P s).2 R := he.symm ▸ hv'.le
    have hN' := (hN.2 (P s).2 hy).2.2 (v s) hvR
    refine ⟨hN'.2.2.1,?_,(htvel s 0).trans (hN'.2.2.2.1.trans he),?_,fun t ht => ?_⟩
    · simpa only [q,one_smul,he] using hEnd
    · rw [htvel,show (fun t : ℝ => q (s,t)) = fun t => E ((P s).2,t • V (P s))
        from funext (fun t => by simp only [q,he])]
      rfl
    · have hpos := metricPair_nonneg_of_posDef (hγ.2 _ (hYΩ hy)) (v s)
      have hvT : t • v s ∈ disk γ (P s).2 R := by
        change metricPair γ (P s).2 (t • v s) (t • v s) ≤ R^2
        rw [metricPair_smul_same]
        exact (mul_le_of_le_one_left hpos (pow_le_one₀ ht.1 ht.2)).trans hvR
      refine ⟨((hN.2 (P s).2 hy).2.2 _ hvT).1,?_⟩
      rw [htacc,htvel]
      exact hN'.2.2.2.2 t ht
  have hP' : HasDerivAt P u 0 := by
    simpa only [P,id_eq,one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add p
  have hqD := hq.differentiable (by simp)
  have hqL : q (0,0) = p.2 := hfamily.self_of_nhds.1.trans (congrArg Prod.snd hp₀)
  have hqR : q (0,1) = p.1 := hfamily.self_of_nhds.2.1.trans (congrArg Prod.fst hp₀)
  have hPL : HasDerivAt (fun s => (P s).2) u.2 0 := hP'.snd
  have hPR : HasDerivAt (fun s => (P s).1) u.1 0 := hP'.fst
  have hJL : pathVariation q (0,0) = u.2 :=
    (hasDerivAt_variation_slice (hqD (0,0))).unique
      (hPL.congr_of_eventuallyEq (hfamily.mono fun _ h => h.1))
  have hJR : pathVariation q (0,1) = u.1 :=
    (hasDerivAt_variation_slice (hqD (0,1))).unique
      (hPR.congr_of_eventuallyEq (hfamily.mono fun _ h => h.2.1))
  have hTL : timeVelocity q (0,0) = V p :=
    hfamily.self_of_nhds.2.2.1.trans (congrArg V hp₀)
  have hTR : timeVelocity q (0,1) = B p :=
    hfamily.self_of_nhds.2.2.2.1.trans (congrArg B hp₀)
  have hf (W : (X dim) × (X dim) → (X dim)) (hW : DifferentiableAt ℝ W p) :
      HasDerivAt (fun s => W (P s)) (fderiv ℝ W p u) 0 := by
    have hd : HasFDerivAt W (fderiv ℝ W p) (P 0) := hp₀.symm ▸ hW.hasFDerivAt
    exact hd.comp_hasDerivAt 0 hP'
  have hV' := (hV.contDiffAt (hD.mem_nhds hp)).differentiableAt (by simp)
  have hB' := (hB.contDiffAt (hD.mem_nhds hp)).differentiableAt (by simp)
  have htD := (contDiff_timeVelocity hq).differentiable (by simp)
  have hdL : pathVariation (timeVelocity q) (0,0) = fderiv ℝ V p u :=
    (hasDerivAt_variation_slice (htD (0,0))).unique
      ((hf V hV').congr_of_eventuallyEq (hfamily.mono fun _ h => h.2.2.1))
  have hdR : pathVariation (timeVelocity q) (0,1) = fderiv ℝ B p u :=
    (hasDerivAt_variation_slice (htD (0,1))).unique
      ((hf B hB').congr_of_eventuallyEq (hfamily.mono fun _ h => h.2.2.2.1))
  have hgeo := hfamily.mono fun _ h => h.2.2.2.2
  have hleft : variationCovariantTime γ q 0 0 = fderiv ℝ V p u + connection γ p.2 u.2 (V p) := by
    rw [variationCovariantTime,← mixed_slice_deriv_eq hq,hdL,hqL,hTL,hJL,
      connection_comm hΩ hγ (hYΩ (hinv p hp).1.1)]
  have hright : variationCovariantTime γ q 0 1 = fderiv ℝ B p u + connection γ p.1 u.1 (B p) := by
    rw [variationCovariantTime,← mixed_slice_deriv_eq hq,hdR,hqR,hTR,hJR,
      connection_comm hΩ hγ (hqR ▸ (hgeo.self_of_nhds 1 ⟨zero_le_one,le_rfl⟩).1)]
  refine ⟨q,hq,fun t => ?_,hqL,hqR,hTL,hJL,hJR,hgeo,fun w => ?_⟩
  · simp only [q,hp₀,show v 0 = V p from hvEq.eq_of_nhds.trans (congrArg V hp₀)]
  · rw [hleft,hright]
    exact productMetricHessian_normalPhase hY hΩ hγ hE hN hr hYΩ hD hV hinv hp u w

end CalderonN
