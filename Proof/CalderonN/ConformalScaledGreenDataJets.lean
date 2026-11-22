module

public import Proof.CalderonN.MovingSphere.GreenContinuation
public import Proof.CalderonN.ScaledGreenDatumJets

import Proof.CalderonN.NormalizedEndpointSeparation
import Proof.CalderonN.RescaledGreenSeeds
import Proof.CalderonN.CylinderCutoff
public import Proof.CalderonN.SphereCoercivity
import Proof.CalderonN.SmoothMetricFrame
import Proof.CalderonN.FixedTube.Initialization
import Mathlib.Tactic

public section

set_option maxHeartbeats 4000000

noncomputable section
open Set Filter Metric
open scoped ContDiff Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim] {normal : I dim}

open FixedTube MovingSphere

/-- Uniform finite jets of the actual radius-normalized boundary values.
The base parameter is rescaled by the local radius and the angular
variable remains in unit-sphere coordinates. -/
@[expose] def UniformCylinderScaledGreenDataJets (normal : I dim)
    (g₁ g₂ : (MetricField dim)) (W Y' : Set (X dim)) (G₁ G₂ : (X dim) × (X dim) → ℝ) (E : ℝ → (X dim) × (X dim) → (X dim))
    (p : ℕ) (ρ R ε tb : ℝ) (n : ℕ) : Prop :=
  let Y := interior (coordinateCylinder normal)
  let γ := conformalReference (depthScale normal 4) g₁
  let e (lam : ℝ) (y : (X dim)) := smoothMetricFrame (γ lam y)
  let r := shrinkingRadius R p (conformalDepth normal 4)
  let χ := cylinderCutoff (normal := normal) 4 tb
  ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam →
    ∀ δ ∈ Ioc (0 : ℝ) 1, Small Y (γ lam) (dilatedMetric g₂ lam) (r δ) ε →
    ∃ (O : Set ((X dim) × (X dim))) (G : (X dim) × (X dim) → ℝ),
      IsOpen O ∧ ProductSolutionOn (dilatedMetric g₁ lam) (dilatedMetric g₂ lam) O G ∧
      (∀ y ∈ Y, ∀ w : ↥(standardSphere dim),
        normalGreenPoint E e (lam,(y,r δ y)) w ∈ O) ∧
      EqOn G (dilatedInitialGreen W G₁ G₂ lam) (lowerNormalSeed normal (normalPairDomain Y' (γ lam) ρ (E lam))) ∧
      ∀ y ∈ Y, y ∈ tsupport (fderiv ℝ χ) → ∀ w : ↥(standardSphere dim),
        let a : (NormalGreenParameter dim) := (lam,(y,r δ y))
        ∃ f : (NormalGreenParameter dim) × (X dim) → ℝ, ContDiff ℝ ∞ f ∧
          f =ᶠ[𝓝 (0,(w:(X dim)))] (fun q => scaledNormalGreenDatum E e G (a+r δ y • q.1,q.2)) ∧
          ∀ k ≤ n, ‖iteratedFDeriv ℝ k f (0,(w:(X dim)))‖ ≤ C

theorem uniformCylinderScaledGreenDataJets (hn : 3 ≤ dim)
    {Ω W : Set (X dim)} (hΩ : IsOpen Ω) (hW : IsOpen W) (hside : ContainsAlignedSide normal Ω W)
    {g₁ g₂ : (MetricField dim)} (hg₁ : SmoothMetric univ g₁) (hg₂ : SmoothMetric univ g₂)
    (hg₁₀ : g₁ 0 = 1) (hg₂₀ : g₂ 0 = 1)
    {G₁ G₂ : (X dim) × (X dim) → ℝ} (hG₁ : GreenGerm Ω g₁ G₁) (hG₂ : GreenGerm Ω g₂ G₂)
    (hmetric : EqOn g₁ g₂ W) (hgreen : EqOn G₁ G₂ (OffDiagonal W))
    {Z : Set (X dim)} (hZ : IsCompact Z) (hCZ : (coordinateCylinder normal) ⊆ interior Z)
    (hZB : Z ⊆ ball (0 : (X dim)) 3)
    {E : ℝ → (X dim) × (X dim) → (X dim)} (hE : ContDiff ℝ ∞ (fun q : ℝ × ((X dim) × (X dim)) => E q.1 q.2))
    {ρ R ε tb : ℝ} (hρ : 0 < ρ) (hR : 0 < R) (hε : 0 ≤ ε) (htb : 0 < tb)
    {p : ℕ} (hp : 0 < p)
    (hDepth : ∀ y, conformalDepth normal 4 y ≤ 3*tb → parabolicHeight normal y < 1/4)
    (hNormal : ∀ lam ∈ Icc (-1 : ℝ) 1, NormalCoordinates Z (ball (0 : (X dim)) 3)
      (conformalReference (depthScale normal 4) g₁ lam) (E lam) (fun _ => ρ))
    (hRadius : ∀ a ∈ Ioc (0 : ℝ) 1, ∀ y ∈ (coordinateCylinder normal),
      shrinkingRadius R p (conformalDepth normal 4) a y ≤ ρ/2)
    (hTests : ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam →
      let γ := conformalReference (depthScale normal 4) g₁ lam
      let N := normalPairDomain (interior Z) γ ρ (E lam)
      IsOpen N ∧ N ⊆ ball (0 : (X dim)) 3 ×ˢ interior Z ∧
      ∃ V : (X dim) × (X dim) → (X dim), ContDiffOn ℝ ∞ V N ∧
        (∀ z ∈ normalVelocityDomain (interior Z) γ ρ, V (E lam z,z.1) = z.2) ∧
        (∀ q ∈ N, (q.2,V q) ∈ normalVelocityDomain (interior Z) γ ρ ∧ E lam (q.2,V q) = q.1) ∧
        ∀ a ∈ Ioc (0 : ℝ) 1,
          let r := shrinkingRadius R p (conformalDepth normal 4) a
          ∀ q ∈ N, normalPhase γ V r q = 0 → smallJet γ (dilatedMetric g₂ lam) q.2 ≤ ε*r q.2 →
            ProductStrictHessianAt (dilatedMetric g₁ lam) (dilatedMetric g₂ lam) (normalPhase γ V r) q)
    (n : ℕ) : UniformCylinderScaledGreenDataJets normal g₁ g₂ W (interior Z) G₁ G₂ E p ρ R ε tb n := by
  let γ := conformalReference (depthScale normal 4) g₁
  let r := shrinkingRadius R p (conformalDepth normal 4)
  let A := Icc (-1 : ℝ) 1
  let e (lam : ℝ) (y : (X dim)) := smoothMetricFrame (γ lam y)
  have hγ (i j : (I dim)) : ContDiff ℝ ∞ (fun q : ℝ × (X dim) => γ q.1 q.2 i j) := by
    apply contDiffOn_univ.mp
    simpa only [mem_univ,ofPred_true] using
      contDiffOn_conformalReference_family_entry hg₁ (contDiff_depthScale (normal := normal) 4) i j
  have hPos (lam : ℝ) (y : (X dim)) : (γ lam y).PosDef :=
    (hg₁.2 _ (mem_univ _)).smul (depthScale_pos (normal := normal) 4 y)
  have he (i : (I dim)) : ContDiff ℝ ∞ (fun q : ℝ × (X dim) => e q.1 q.2 i) :=
    contDiffOn_univ.mp (contDiffOn_smoothMetricFrame (fun j k => (hγ j k).contDiffOn)
      (fun q _ => hPos q.1 q.2) i)
  obtain ⟨c,hc,hLinear⟩ := exists_uniform_normalBallChartMap_separation_linear
    (A := A) (K := (coordinateCylinder normal)) isCompact_Icc (isCompact_coordinateCylinder (normal := normal))
    (hCZ.trans interior_subset) hE he hρ hNormal
    (fun lam _ y _ i j => smoothMetricFrame_orthonormal (hPos lam y) i j)
  obtain ⟨d,M,hd,hM,hKernel⟩ := exists_conformalCylinder_greenContinuation_with_high_seed
    hn hΩ hW hside hg₁ hg₂ hg₁₀ hg₂₀ hG₁ hG₂ hmetric hgreen hZ hCZ hZB hE
    hρ hR hε htb hp hDepth hNormal hRadius
    (frames := e) (fun lam _ y i j => smoothMetricFrame_orthonormal (hPos lam y) i j)
    (fun lam _ i => ((he i).comp (contDiff_const.prodMk contDiff_id)).contDiffOn) hTests
  have h₀ : (0 : (X dim)) ∈ Ω := by
    obtain ⟨V,s,hV,h₀,hVΩ,_⟩ := hside
    exact hVΩ h₀
  obtain ⟨η,L,hη,hL,hSeed⟩ := exists_rescaledGreenSeed_jet_bounds
    hn hΩ h₀ hg₁ hg₂ hG₁ hc hd (half_pos hρ) hM n
  let K : Set (NormalGreenParameter dim) := A ×ˢ ((coordinateCylinder normal) ×ˢ Icc 0 (ρ/2))
  obtain ⟨C,hC,hJets⟩ := exists_scaledNormalGreenDatum_jet_bound hE he
    (isCompact_Icc.prod ((isCompact_coordinateCylinder (normal := normal)).prod isCompact_Icc) : IsCompact K) hη.ne' n
  have hA : A ∈ 𝓝 (0 : ℝ) := Icc_mem_nhds (by norm_num) (by norm_num)
  refine ⟨C*L,mul_nonneg hC hL,?_⟩
  filter_upwards [hKernel,hSeed,hA] with lam hKernel hSeed hlam hpos δ hδ hSmall
  obtain ⟨O₀,F,hO₀,hOut,hF,hMb,hExt⟩ := hKernel hpos
  obtain ⟨O,G,hO,hOS,hG,hLow,hHi,hLo⟩ := hExt δ hδ hSmall
  have hSph (y : (X dim)) (hy : y ∈ interior (coordinateCylinder normal)) (w : ↥(standardSphere dim)) :
      normalGreenPoint E e (lam,(y,r δ y)) w ∈ O := by
    apply hOS
    right
    exact ⟨((y,w),δ),⟨⟨interior_subset hy,mem_univ _⟩,le_rfl,hδ.2⟩,rfl⟩
  refine ⟨O,G,hO,hG,hSph,hLow,?_⟩
  intro y hy hχ w
  let a : (NormalGreenParameter dim) := (lam,(y,r δ y))
  let x := (normalGreenPoint E e a w).1
  let v := r δ y
  have hyK : y ∈ (coordinateCylinder normal) := interior_subset hy
  have hv : v ∈ Ioc 0 (ρ/2) :=
    ⟨mul_pos hR (pow_pos (softplus_pos hδ.1 _) _),hRadius δ hδ y hyK⟩
  have hA₀ : a ∈ K := ⟨hlam,hyK,hv.1.le,hv.2⟩
  have hRoom : ‖x‖ ≤ 3 ∧ ‖y‖ ≤ 3 ∧
      ((c*v ≤ dist x y ∧ G =ᶠ[𝓝 (x,y)] dilatedGreen G₁ lam) ∨
        (d ≤ dist x y ∧ ∃ (O' : Set ((X dim) × (X dim))) (F' : (X dim) × (X dim) → ℝ),
          IsOpen O' ∧ fixedSeparationSet 4 (d/2) ⊆ O' ∧
          ProductSolutionOn (dilatedMetric g₁ lam) (dilatedMetric g₂ lam) O' F' ∧
          (∀ q ∈ fixedSeparationSet 4 (d/2), |F' q| ≤ M) ∧ G =ᶠ[𝓝 (x,y)] F')) := by
    rcases cylinderCutoff_differential_tsupport (normal := normal) htb hχ with hlo | hhi
    · obtain ⟨hx,hy,hEq⟩ := hLo y hyK hlo w
      have hSep : c*v ≤ dist x y := by
        rw [dist_eq_norm]
        exact hLinear lam hlam y hyK v ⟨hv.1.le,hv.2.trans (half_le_self hρ.le)⟩ w w.property
      exact ⟨hx,hy,Or.inl ⟨hSep,hEq⟩⟩
    · obtain ⟨⟨hx,hy,hSep⟩,hEq⟩ := hHi y hyK hhi w
      exact ⟨hx,hy,Or.inr ⟨by rw [dist_eq_norm]; exact hSep,O₀,F,hO₀,hOut,hF,hMb,hEq⟩⟩
  obtain ⟨H,hH,hEq,hJ⟩ := hSeed hpos x y hRoom.1 hRoom.2.1 v hv G hRoom.2.2
  exact hJets a hA₀ w w.property G H hH hEq L hL hJ

end CalderonN
