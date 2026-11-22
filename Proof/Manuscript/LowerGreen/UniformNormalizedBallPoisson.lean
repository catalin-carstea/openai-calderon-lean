module

public import Proof.Manuscript.LowerGreen.NormalizedPoissonRoom
public import Proof.Manuscript.LowerGreen.NormalizedPoissonCoefficients
public import Proof.Manuscript.LowerGreen.BallPoissonDensity
public import Proof.Manuscript.LowerGreen.FramedFiniteJetBounds

import Mathlib.Tactic

public section

noncomputable section

open Set Filter MeasureTheory Metric CalderonN CalderonN.BallDirichlet
open scoped ContDiff Topology Matrix.Norms.Elementwise

namespace CalderonPaper.LowerGreen

variable {n : ℕ} [NeZero n] [Nontrivial (Fin n)]

theorem norm_normalGreenBase_fderiv_le (lam : ℝ) {r : X n → ℝ} (hr : ContDiff ℝ ∞ r)
    (y : X n) {D : ℝ} (hD : 0 ≤ D) (hd : ‖fderiv ℝ r y‖ ≤ D) :
    ‖fderiv ℝ (fun z : X n => (lam,(z,r z))) y‖ ≤ max 1 D := by
  have h := (hasFDerivAt_const (𝕜 := ℝ) lam y).prodMk
    ((hasFDerivAt_id y).prodMk (hr.differentiable (by simp) y).hasFDerivAt)
  change ‖fderiv ℝ (fun z : X n => (lam,(id z,r z))) y‖ ≤ max 1 D
  rw [h.fderiv]
  apply ContinuousLinearMap.opNorm_le_bound _ ((zero_le_one : (0:ℝ) ≤ 1).trans (le_max_left _ _))
  intro v
  change ‖((0:ℝ),(v,fderiv ℝ r y v))‖ ≤ _
  rw [Prod.norm_def,Real.norm_eq_abs,abs_zero,Prod.norm_def]
  refine max_le (mul_nonneg (zero_le_one.trans (le_max_left _ _)) (norm_nonneg _)) (max_le ?_ ?_)
  · exact (one_mul ‖v‖).symm.trans_le (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  · exact ((fderiv ℝ r y).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (hd.trans (le_max_right _ _)) (norm_nonneg _))

set_option maxHeartbeats 2100000 in
/-- Uniform angular and unscaled base jets of the center Poisson density
for the common normalized ball, through the limiting radius zero. -/
theorem exists_uniform_normalizedBallPoisson_jets
    {γ g : ℝ → MetricField n} {E : ℝ → X n × X n → X n} {e : ℝ → Frame n}
    (hg : ∀ i j, ContDiff ℝ ∞ (fun p : ℝ × X n => g p.1 p.2 i j))
    (hgPos : ∀ lam y, (g lam y).PosDef)
    (hE : ContDiff ℝ ∞ (fun q : ℝ × (X n × X n) => E q.1 q.2))
    (he : ∀ i, ContDiff ℝ ∞ (fun q : ℝ × X n => e q.1 q.2 i))
    {S : Set ℝ} {K Y' Ω : Set (X n)}
    (hS : IsCompact S) (hK : IsCompact K) (hKY' : K ⊆ Y')
    {ρ D : ℝ} (hρ : 0 < ρ) (hD : 0 ≤ D)
    (hNormal : ∀ lam ∈ S, NormalCoordinates Y' Ω (γ lam) (E lam) (fun _ => ρ))
    (hFrame : ∀ lam ∈ S, ∀ y ∈ K, ∀ i j,
      metricPair (γ lam) y (e lam y i) (e lam y j) = if i=j then 1 else 0) :
    let J : Set (NormalGreenParameter n) := S ×ˢ (K ×ˢ Icc (0:ℝ) (ρ/2))
    ∃ (F : SupportedBallFamily (NormalGreenParameter n) n) (W : Set (X n))
      (C : ℕ → ℝ) (ψ : ℕ → NormalGreenParameter n × X n → ℝ),
      J ⊆ F.V ∧ IsOpen W ∧ closedBall (0 : X n) 1 ⊆ W ∧
      (∀ p ∈ F.V, SmoothMetric W (fun z => normalGreenMetric g E e (p,z)) ∧
        ∀ z ∈ W, ∀ i j, F.a (p,z) i j = divergenceCoeff (fun z => normalGreenMetric g E e (p,z)) z i j) ∧
      (∀ k, ContDiffOn ℝ (k+1 : ℕ) (ψ k) (F.V ×ˢ ({0}ᶜ : Set (X n))) ∧
        ∀ p z, z ≠ 0 → ψ k (p,z) = ψ k (p,sphereNormalize z)) ∧
      (∀ k p, p ∈ F.V → ∀ u : SmoothData n,
        EqOn (negativeBallDivergence (fun z => F.a (p,z)) u.1) 0 (ball (0 : X n) 1) →
        ∫ w : ↥(standardSphere n), ψ k (p,w) * u.1 w ∂(sphereProbability n) = u.1 0) ∧
      ∀ k lam, lam ∈ S → ∀ r : X n → ℝ, ContDiff ℝ ∞ r →
        ∀ y ∈ K, r y ∈ Icc (0:ℝ) (ρ/2) → ‖fderiv ℝ r y‖ ≤ D → ∀ w : ↥(standardSphere n),
          ‖iteratedFDeriv ℝ k (fun z => ψ k ((lam,(y,r y)),z)) (w : X n)‖ ≤ C k ∧
          ‖iteratedFDeriv ℝ k (fun z => fderiv ℝ (fun x => ψ k ((lam,(x,r x)),z)) y) (w : X n)‖ ≤ C k := by
  let J : Set (NormalGreenParameter n) := S ×ˢ (K ×ˢ Icc (0:ℝ) (ρ/2))
  have hJ : IsCompact J := hS.prod (hK.prod isCompact_Icc)
  obtain ⟨U,hU,hJU,hm,hPos⟩ := exists_open_normalGreenMetric_room hg hgPos hE he
    hKY' hρ hNormal hFrame
  obtain ⟨F,W,hJV,hW,hBW,hFv,hA⟩ := exists_supportedBallFamily_of_metric hJ hU hJU hm hPos
  choose ψ hψ hRad hRep using (fun k : ℕ => F.exists_radialBallPoissonDensity (k+1))
  let B := J ×ˢ standardSphere n
  have hB : IsCompact B := hJ.prod (isCompact_sphere (0 : X n) 1)
  have hBV : B ⊆ F.V ×ˢ ({0}ᶜ : Set (X n)) := by
    intro q hq
    refine ⟨hJV hq.1,?_⟩
    have hn := mem_sphere_zero_iff_norm.mp hq.2
    show q.2 ≠ 0
    intro hz
    simp [hz] at hn
  have hO : IsOpen (F.V ×ˢ ({0}ᶜ : Set (X n))) := F.openV.prod isClosed_singleton.isOpen_compl
  have hJets k := exists_uniform_baseComposed_mixed_jets (X := X n) hO hB hBV (hψ k)
    (show 0 ≤ max 1 D from zero_le_one.trans (le_max_left _ _))
  choose C hC hBound using hJets
  refine ⟨F,W,C,ψ,hJV,hW,hBW,?_,fun k => ⟨hψ k,hRad k⟩,hRep,?_⟩
  · intro p hp
    refine ⟨⟨fun i j => (hm i j).comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun z hz => hFv ⟨hp,hz⟩),fun z hz => hPos _ (hFv ⟨hp,hz⟩)⟩,hA p hp⟩
  · intro k lam hlam r hr y hy hR hd w
    exact hBound k (fun z => (lam,(z,r z))) (contDiff_const.prodMk (contDiff_id.prodMk hr))
      y w ⟨⟨hlam,hy,hR⟩,w.property⟩ (norm_normalGreenBase_fderiv_le lam hr y hD hd)

end CalderonPaper.LowerGreen

end
