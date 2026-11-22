module

public import Proof.CalderonN.NormalPhaseVariation
public import Proof.CalderonN.ProductMetricHessian

import Proof.CalderonN.MetricCompatibility
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

theorem terminalVelocity_eq_fderiv {E : (X dim) × (X dim) → (X dim)} (hE : ContDiff ℝ ∞ E) (y v : (X dim)) :
    terminalVelocity E y v = fderiv ℝ E (y,v) (0,v) := by
  have hv : HasDerivAt (fun t : ℝ => t • v) v 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).smul_const v
  have hp : HasDerivAt (fun t : ℝ => (y,t • v)) (0,v) 1 :=
    (hasDerivAt_const (1 : ℝ) y).prodMk hv
  have hD : HasFDerivAt E (fderiv ℝ E (y,v)) (y,(1:ℝ) • v) := by
    simpa only [one_smul] using (hE.differentiable (by simp) (y,v)).hasFDerivAt
  exact (hD.comp_hasDerivAt 1 hp).deriv

theorem contDiff_terminalVelocity {E : (X dim) × (X dim) → (X dim)} (hE : ContDiff ℝ ∞ E) :
    ContDiff ℝ ∞ (fun q : (X dim) × (X dim) => terminalVelocity E q.1 q.2) := by
  simp_rw [terminalVelocity_eq_fderiv hE]
  exact (hE.fderiv_right (m := ∞) (by simp)).clm_apply (contDiff_const.prodMk contDiff_snd)

private theorem hasDerivAt_affineLine {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (p v : F) : HasDerivAt (fun t : ℝ => p + t • v) v 0 := by
  simpa only [id_eq,one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add p

private theorem along_affineLine_deriv {F E : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : F → E} {p v : F} (h : DifferentiableAt ℝ u p) :
    HasDerivAt (fun t : ℝ => u (p + t • v)) (fderiv ℝ u p v) 0 := by
  have hp : HasFDerivAt u (fderiv ℝ u p) (p + (0 : ℝ) • v) := by simpa using h.hasFDerivAt
  exact hp.comp_hasDerivAt 0 (hasDerivAt_affineLine p v)

set_option maxHeartbeats 620000 in
/-- Differentiating the two endpoint covectors gives the product Hessian.
The endpoint derivatives of velocity are covariant, and the radius term
uses the same connection at the center. -/
theorem productMetricHessian_eq_endpointVelocity_derivatives
    {Ω : Set (X dim)} (hΩ : IsOpen Ω) {γ : (MetricField dim)} (hγ : SmoothMetric Ω γ)
    {p : (X dim) × (X dim)} (hp₁ : p.1 ∈ Ω) (hp₂ : p.2 ∈ Ω)
    {ρ : (X dim) × (X dim) → ℝ} {B₁ B₂ : (X dim) × (X dim) → (X dim)} {r : (X dim) → ℝ}
    (hρ : ContDiffAt ℝ 2 ρ p)
    (hB₁ : DifferentiableAt ℝ B₁ p) (hB₂ : DifferentiableAt ℝ B₂ p)
    (hr : ContDiffAt ℝ 2 r p.2)
    (hfirst : ∀ᶠ q in 𝓝 p, ∀ w : (X dim) × (X dim), fderiv ℝ ρ q w =
      metricPair γ q.1 (B₁ q) w.1 - metricPair γ q.2 (B₂ q) w.2 -
        r q.2 * fderiv ℝ r q.2 w.2)
    (u w : (X dim) × (X dim)) :
    productMetricHessian γ γ ρ p u w =
      metricPair γ p.1 (fderiv ℝ B₁ p u + connection γ p.1 u.1 (B₁ p)) w.1 -
      metricPair γ p.2 (fderiv ℝ B₂ p u + connection γ p.2 u.2 (B₂ p)) w.2 -
      fderiv ℝ r p.2 u.2 * fderiv ℝ r p.2 w.2 -
      r p.2 * (fderiv ℝ (fderiv ℝ r) p.2 u.2 w.2 -
        fderiv ℝ r p.2 (connection γ p.2 u.2 w.2)) := by
  let P (t : ℝ) := p+t • u
  have hP : HasDerivAt P u 0 := hasDerivAt_affineLine p u
  have hP₁ : HasDerivAt (fun t => (P t).1) u.1 0 := hP.fst
  have hP₂ : HasDerivAt (fun t => (P t).2) u.2 0 := hP.snd
  have hp₀ : P 0 = p := by simp [P]
  have hderiv₁ := hasDerivAt_metricPair hΩ hγ (by rwa [hp₀]) hP₁
    (along_affineLine_deriv (v := u) hB₁) (hasDerivAt_const 0 w.1)
  have hderiv₂ := hasDerivAt_metricPair hΩ hγ (by rwa [hp₀]) hP₂
    (along_affineLine_deriv (v := u) hB₂) (hasDerivAt_const 0 w.2)
  have hr' : DifferentiableAt ℝ (fderiv ℝ r) p.2 := (hr.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)
  have hrD : HasDerivAt (fun t => r (P t).2) (fderiv ℝ r p.2 u.2) 0 :=
    (along_affineLine_deriv (v := u.2) (hr.differentiableAt (by norm_num)))
  have hrDD : HasDerivAt (fun t => fderiv ℝ r (P t).2 w.2)
      (fderiv ℝ (fderiv ℝ r) p.2 u.2 w.2) 0 :=
    (ContinuousLinearMap.apply ℝ ℝ w.2).hasFDerivAt.comp_hasDerivAt 0
      (along_affineLine_deriv (v := u.2) hr')
  have hrho' : DifferentiableAt ℝ (fderiv ℝ ρ) p :=
    (hρ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hF : HasDerivAt (fun t => fderiv ℝ ρ (P t) w)
      (fderiv ℝ (fderiv ℝ ρ) p u w) 0 :=
    (ContinuousLinearMap.apply ℝ ℝ w).hasFDerivAt.comp_hasDerivAt 0
      (along_affineLine_deriv (v := u) hrho')
  have hE : (fun t => fderiv ℝ ρ (P t) w) =ᶠ[𝓝 (0 : ℝ)]
      fun t => metricPair γ (P t).1 (B₁ (P t)) w.1 -
        metricPair γ (P t).2 (B₂ (P t)) w.2 - r (P t).2 * fderiv ℝ r (P t).2 w.2 := by
    have ht : Tendsto P (𝓝 0) (𝓝 p) := by
      simpa only [hp₀] using hP.continuousAt.tendsto
    exact (ht.eventually hfirst).mono fun t h => h w
  have hD := hF.unique (((hderiv₁.sub hderiv₂).sub (hrD.mul hrDD)).congr_of_eventuallyEq hE)
  simp only [hp₀,zero_smul,zero_add,add_zero] at hD
  rw [productMetricHessian,hD,
    hfirst.self_of_nhds (connection γ p.1 u.1 w.1,connection γ p.2 u.2 w.2)]
  dsimp only
  ring

/-- The literal normal phase has the endpoint Hessian formula on the
normal tube produced by the same exponential and inverse velocity. -/
theorem productMetricHessian_normalPhase
    {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) {γ : (MetricField dim)}
    (hγ : SmoothMetric Ω γ) {R : ℝ} {E V : (X dim) × (X dim) → (X dim)} (hE : ContDiff ℝ ∞ E)
    (hN : NormalCoordinates Y Ω γ E (fun _ => R))
    {r : (X dim) → ℝ} (hr : ContDiffOn ℝ ∞ r Y) (hYΩ : Y ⊆ Ω)
    (hD : IsOpen (normalPairDomain Y γ R E))
    (hV : ContDiffOn ℝ ∞ V (normalPairDomain Y γ R E))
    (hinv : ∀ q ∈ normalPairDomain Y γ R E,
      (q.2,V q) ∈ normalVelocityDomain Y γ R ∧ E (q.2,V q) = q.1)
    {p : (X dim) × (X dim)} (hp : p ∈ normalPairDomain Y γ R E) (u w : (X dim) × (X dim)) :
    let B (q : (X dim) × (X dim)) := terminalVelocity E q.2 (V q)
    productMetricHessian γ γ (normalPhase γ V r) p u w =
      metricPair γ p.1 (fderiv ℝ B p u + connection γ p.1 u.1 (B p)) w.1 -
      metricPair γ p.2 (fderiv ℝ V p u + connection γ p.2 u.2 (V p)) w.2 -
      fderiv ℝ r p.2 u.2 * fderiv ℝ r p.2 w.2 -
      r p.2 * (fderiv ℝ (fderiv ℝ r) p.2 u.2 w.2 -
        fderiv ℝ r p.2 (connection γ p.2 u.2 w.2)) := by
  dsimp only
  have hMap : MapsTo Prod.snd (normalPairDomain Y γ R E) Y :=
    fun q hq => (hinv q hq).1.1
  have hpY := hMap hp
  have he := hinv p hp
  have hp₁ : p.1 ∈ Ω := he.2 ▸ ((hN.2 p.2 hpY).2.2 _ he.1.2.le).1
  have hγY : SmoothMetric Y γ := ⟨fun i j => (hγ.1 i j).mono hYΩ,fun y hy => hγ.2 y (hYΩ hy)⟩
  have hx := hD.mem_nhds hp
  have hρ := (contDiffOn_normalPhase hγY hMap hV hr).contDiffAt hx
  have hB := (contDiff_terminalVelocity hE).comp_contDiffOn (contDiff_snd.contDiffOn.prodMk hV)
  apply productMetricHessian_eq_endpointVelocity_derivatives hΩ hγ hp₁ (hYΩ hpY)
    (hρ.of_le (by simp)) ((hB.contDiffAt hx).differentiableAt (by simp))
    ((hV.contDiffAt hx).differentiableAt (by simp))
    ((hr.contDiffAt (hY.mem_nhds hpY)).of_le (by simp)) _ u w
  filter_upwards [hx] with q hq w
  exact fderiv_normalPhase_eq_endpoint_terms hY hΩ hγ hE hN hr hYΩ hD hV hinv hq w

end CalderonN
