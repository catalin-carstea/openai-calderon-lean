module

public import Proof.CalderonN.GlobalChartReduction
public import Proof.CalderonN.SphereCoercivity
public import Proof.CalderonN.WeightedMomentAgreement
public import Proof.CalderonN.UniformTransferMoment
public import Proof.CalderonN.CylinderSeed

import Mathlib.Tactic

public section

noncomputable section
open Set Metric Filter
open scoped ContDiff Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim] {normal : I dim}

/-- The prepared sphere family on the fixed conformal cylinder. -/
@[expose] def ConformalCylinderSphereSetup (normal : I dim) (g₁ g₂ : (MetricField dim)) (E : ℝ → (X dim) × (X dim) → (X dim))
    (p : ℕ) (R ε K ρ c₀ floor : ℝ) {m : ℕ} (Mv : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) : Prop :=
  ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam → ∀ δ ∈ Ioc (0 : ℝ) 1, ∀ A : TraceAdjoint dim,
    let d := conformalSphereData normal g₁ g₂ E p R lam δ A
    let Y := interior (coordinateCylinder normal)
    (∀ y ∈ Y, 0 < d.radius y ∧ d.radius y < ρ ∧ d.radius y * (beta d.γ d.radius y)^2 ≤ ε) ∧
    Background (ball (0 : (X dim)) 3) K Mv d.γ d.g₁ d.g₂ d.frame ∧
    NormalCoordinates Y (ball (0 : (X dim)) 3) d.γ d.expMap (fun _ => ρ) ∧
    Profile Y d.γ d.frame d.radius floor c₀ Cj

/-- The analytical transfer estimate needed on those same spheres.
Its constants must be uniform in the two continuation parameters. -/
@[expose] def ConformalCylinderTransfer (normal : I dim) (g₁ g₂ : (MetricField dim)) (E : ℝ → (X dim) × (X dim) → (X dim))
    (p : ℕ) (R ε tb : ℝ) {n : ℕ} (u₁ u₂ : Fin n → (X dim) → ℝ) : Prop :=
  ∃ Ctay volFloor B : ℝ, 0 ≤ Ctay ∧ 0 < volFloor ∧ 0 ≤ B ∧
    ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam → ∀ δ ∈ Ioc (0 : ℝ) 1,
      Small (interior (coordinateCylinder normal)) (conformalReference (depthScale normal 4) g₁ lam)
        (dilatedMetric g₂ lam) (shrinkingRadius R p (conformalDepth normal 4) δ) ε →
      ∃ (A : TraceAdjoint dim) (ψ : (Field dim)),
        let d := conformalSphereData normal g₁ g₂ E p R lam δ A
        let v₁ (a : Fin n) := renormalizedHarmonic (u₁ a 0) (fderiv ℝ (u₁ a) 0) (u₁ a) lam
        let v₂ (a : Fin n) := renormalizedHarmonic (u₁ a 0) (fderiv ℝ (u₁ a) 0) (u₂ a) lam
        Dirichlet (interior (coordinateCylinder normal)) d.γ d.g₁ d.expMap d.radius ∧
        IsMovingTraceAdjoint (interior (coordinateCylinder normal)) d.γ d.g₁ d.frame d.expMap d.radius d.adjoint ∧
        SphereTransferBounds (interior (coordinateCylinder normal)) d ψ (cylinderCutoff (normal := normal) 4 tb)
          v₁ v₂ Ctay volFloor B

/-- With the actual uniform transfer estimate on the fixed conformal
cylinder, the original chart metrics agree near the origin. The same
cutoff, normal family, radii and renormalized pairs enter both estimates. -/
theorem exists_ball_metric_eq_of_conformalCylinder_transfer (hn : 3 ≤ dim)
    {Ω W : Set (X dim)} (hΩ : IsOpen Ω) (hW : IsOpen W) (hside : ContainsAlignedSide normal Ω W)
    {g₁ g₂ : (MetricField dim)} (hg₁ : SmoothMetric Ω g₁) (hg₂ : SmoothMetric Ω g₂)
    (hchart₁ : HarmonicCoordinates Ω g₁) (hchart₂ : HarmonicCoordinates Ω g₂)
    (hmatch : EqOn g₁ g₂ W)
    {n : ℕ} {u₁ u₂ : Fin n → (X dim) → ℝ}
    (hu₁ : ∀ a, Harmonic Ω g₁ (u₁ a)) (hu₂ : ∀ a, Harmonic Ω g₂ (u₂ a))
    (hspan : HessianSpanning g₁ u₁)
    {tb : ℝ} (htb : 0 < tb)
    (hm : ∀ y, conformalDepth normal 4 y ≤ 3*tb → parabolicHeight normal y < 1/4)
    {p : ℕ} (hp : 21 + dim ≤ p) {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    {K ρ c₀ C floor ε₀ : ℝ} {m : ℕ} {Mv : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hε₀ : ε ≤ ε₀) (hC : 0 ≤ C) (hK : 0 < K) (hfloor : 1 ≤ floor)
    (hEst : UniformEstimate (interior (coordinateCylinder normal)) (ball (0 : (X dim)) 3) K ρ c₀ Mv Cj floor ε₀ C)
    {E : ℝ → (X dim) × (X dim) → (X dim)}
    (hSetup : ConformalCylinderSphereSetup normal g₁ g₂ E p R ε K ρ c₀ floor Mv Cj)
    (htransfer : ConformalCylinderTransfer normal g₁ g₂ E p R ε tb u₁ u₂) :
    ∃ r > 0, ball (0 : (X dim)) r ⊆ Ω ∧ EqOn g₁ g₂ (ball 0 r) := by
  unfold ConformalCylinderSphereSetup at hSetup
  let Y := interior (coordinateCylinder normal)
  let O := ball (0 : (X dim)) 3
  let v₁ (lam : ℝ) (a : Fin n) := renormalizedHarmonic (u₁ a 0) (fderiv ℝ (u₁ a) 0) (u₁ a) lam
  let v₂ (lam : ℝ) (a : Fin n) := renormalizedHarmonic (u₁ a 0) (fderiv ℝ (u₁ a) 0) (u₂ a) lam
  have hYO : Y ⊆ O := interior_subset.trans ((coordinateCylinder_subset_closedBall (normal := normal)).trans
    (closedBall_subset_ball (by norm_num)))
  have hsideOrig := hside.containsSmoothSide
  obtain ⟨V,s,hV,h₀V,hVΩ,hs,hs₀,hD,hsideW⟩ := hside
  have h₀ := hVΩ h₀V
  have hsD : DifferentiableAt ℝ s 0 :=
    (hs.contDiffAt (hV.mem_nhds h₀V)).differentiableAt (by simp)
  have hnear : ∀ᶠ lam in 𝓝 (0 : ℝ), ∀ y ∈ closedBall (0 : (X dim)) 3, lam • y ∈ Ω := by
    apply (isCompact_closedBall (0 : (X dim)) 3).eventually_forall_of_forall_eventually
    intro y _
    have hsmul : ContinuousAt (fun q : ℝ × (X dim) => q.1 • q.2) (0,y) :=
      (continuous_fst.smul continuous_snd).continuousAt
    exact hsmul.preimage_mem_nhds (by simpa only [zero_smul] using hΩ.mem_nhds h₀)
  have hU : ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam → ∀ a,
      ContinuousOn (v₁ lam a) O ∧ ContinuousOn (v₂ lam a) Y := hnear.mono fun lam hLam _ a => by
    have hOLam : O ⊆ {z : (X dim) | lam • z ∈ Ω} := fun z hz => hLam z (ball_subset_closedBall hz)
    exact ⟨((contDiffOn_renormalizedHarmonic (hu₁ a).1 _ _ lam).mono hOLam).continuousOn,
      ((contDiffOn_renormalizedHarmonic (hu₂ a).1 _ _ lam).mono (hYO.trans hOLam)).continuousOn⟩
  have hsetup : ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam → ∀ δ ∈ Ioc (0 : ℝ) 1, ∀ A : TraceAdjoint dim,
      let d := conformalSphereData normal g₁ g₂ E p R lam δ A
      (∀ y ∈ Y, d.radius y ≤ ρ) ∧ Background O K Mv d.γ d.g₁ d.g₂ d.frame ∧
      NormalCoordinates Y O d.γ d.expMap (fun _ => ρ) ∧ Profile Y d.γ d.frame d.radius floor c₀ Cj :=
    hSetup.mono fun _ h hpos δ hδ A =>
      let H := h hpos δ hδ A
      ⟨fun y hy => (H.1 y hy).2.1.le,H.2⟩
  have hβ : ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam → ∀ δ ∈ Ioc (0 : ℝ) 1, ∀ y ∈ Y,
      shrinkingRadius R p (conformalDepth normal 4) δ y *
        (beta (conformalReference (depthScale normal 4) g₁ lam) (shrinkingRadius R p (conformalDepth normal 4) δ) y)^2 ≤ ε :=
    hSetup.mono fun _ h hpos δ hδ y hy => ((h hpos δ hδ (fun _ _ _ _ => 0)).1 y hy).2.2
  have hmoment := exists_uniform_weighted_moment_of_sphereTransfer hn isOpen_interior hYO hε.le hε₀
    hC hK hfloor hEst hsetup (contDiff_cylinderCutoff (normal := normal) 4 tb) (hasCompactSupport_cylinderCutoff htb hm)
    (cylinderCutoff_tsupport_subset_interior htb hm) v₁ v₂ hU htransfer
  obtain ⟨l,hl⟩ := exists_cylinderDepth_lipschitz (normal := normal) 4
  obtain ⟨s₀,hBufRad,hbuf⟩ := exists_cylinderCore_cutoff_buffer htb hm
  have hoff := (eventually_cylinderSeed_dichotomy hV h₀V hsD hs₀ hsideW hD htb hm).mono fun _ h hpos =>
    (h hpos).1
  exact exists_ball_metric_eq_of_uniform_weighted_moment hn hΩ hW hsideOrig
    (isCompact_cylinderCore (normal := normal) 4 tb) (isCompact_coordinateCylinder (normal := normal))
    (cylinderCore_subset_interior htb hm) interior_subset
    (origin_mem_interior_cylinderCore (by norm_num) htb) hg₁ hg₂ hchart₁ hchart₂ hmatch
    hu₁ hu₂ hspan (contDiff_depthScale (normal := normal) 4) (depthScale_pos (normal := normal) 4) hl
    (conformalDepth_at_origin_neg (normal := normal) (by norm_num)) htb hBufRad hbuf hoff hR hε hp hβ hmoment

end CalderonN
