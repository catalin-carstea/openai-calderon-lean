module

public import Proof.CalderonN.ConformalScaledGreenDataJets
public import Proof.CalderonN.ConformalCylinderAgreement

import Proof.CalderonN.MovingSphere.UniformStrict
import Proof.CalderonN.CylinderCutoff
import Mathlib.Tactic

public section

noncomputable section
open Set Metric Filter
open scoped ContDiff Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim] {normal : I dim}

/-- The uniform moving-sphere analysis uses the same dilations, cutoff,
normal-coordinate tubes, continued Green kernels, and harmonic pairs
as the final chart calculation. -/
@[expose] def UniformTransferFromScaledData (normal : I dim) : Prop :=
  ∀ {U W Z : Set (X dim)} (hU : IsOpen U) (hside : ContainsAlignedSide normal U W)
    {q₁ q₂ : MetricField dim} (hq₁ : SmoothMetric univ q₁) (hq₂ : SmoothMetric univ q₂)
    (hq₁₀ : q₁ 0 = 1) (hq₂₀ : q₂ 0 = 1)
    (hcoords₁ : HarmonicCoordinates U q₁) (hcoords₂ : HarmonicCoordinates U q₂)
    {G₁ G₂ : X dim × X dim → ℝ} (hG₁ : GreenGerm U q₁ G₁) (hG₂ : GreenGerm U q₂ G₂)
    (hm : EqOn q₁ q₂ W) (hG : EqOn G₁ G₂ (OffDiagonal W))
    {m : ℕ} {v₁ v₂ : Fin m → X dim → ℝ}
    (hv₁ : ∀ a, Harmonic U q₁ (v₁ a)) (hv₂ : ∀ a, Harmonic U q₂ (v₂ a))
    (hpair : ∀ a, EqOn (v₁ a) (v₂ a) W)
    {E : ℝ → X dim × X dim → X dim}
    (hE : ContDiff ℝ ∞ (fun q : ℝ × (X dim × X dim) => E q.1 q.2))
    {p : ℕ} (hp : 21 + dim ≤ p) {ρ R ε tb K c₀ floor : ℝ}
    (hρ : 0 < ρ) (hR : 0 < R) (hε : 0 < ε) (htb : 0 < tb) (hK : 0 < K)
    (hdepth : ∀ y, conformalDepth normal 4 y ≤ 3*tb → parabolicHeight normal y < 1/4)
    (hZ : IsCompact Z) (hCZ : coordinateCylinder normal ⊆ interior Z)
    (hZO : Z ⊆ ball (0 : X dim) 3)
    (hNormal : ∀ lam ∈ Icc (-1 : ℝ) 1, NormalCoordinates Z (ball (0 : X dim) 3)
      (conformalReference (depthScale normal 4) q₁ lam) (E lam) (fun _ => ρ))
    (hRadius : ∀ δ ∈ Ioc (0 : ℝ) 1, ∀ y ∈ Z, shrinkingRadius R p (conformalDepth normal 4) δ y ≤ ρ/2)
    {k : ℕ} {M : Fin (k+1) → ℝ} {Cj : Fin 9 → ℝ},
    ConformalCylinderSphereSetup normal q₁ q₂ E p R ε K ρ c₀ floor M Cj →
    UniformCylinderScaledGreenDataJets normal q₁ q₂ W (interior Z) G₁ G₂ E p ρ R ε tb (2*dim+8) →
    ConformalCylinderTransfer normal q₁ q₂ E p R ε tb v₁ v₂

set_option maxHeartbeats 2500000 in
/-- The top-level harmonic chart argument, conditional only on the
uniform transfer producer and Proposition 5.3. -/
theorem globalNormalizedLocalMetricExtension_of_scaled_transfer (hn : 3 ≤ dim)
    (hCoercivity : Coercivity dim) (hProduce : UniformTransferFromScaledData normal) :
    GlobalNormalizedLocalMetricExtension normal := by
  intro U W' hU hW' hW'U hside' q₁ q₂ hq₁ hq₂ hq₁₀ hq₂₀ hcoord₁ hcoord₂ H₁ H₂ hH₁ hH₂ hmatch
    hGreen n' v₁ v₂ hv₁ hv₂ hpair hHess
  obtain ⟨tb,htb,hdepth⟩ := exists_cylinderDepth_margin (normal := normal) (L := 4) (by norm_num)
  let Y := interior (coordinateCylinder normal)
  let O := ball (0 : (X dim)) 3
  let D := closedBall (0 : (X dim)) 3
  let Z := closedBall (0 : (X dim)) (5/2)
  have hYc : IsCompact (closure Y) :=
    (isCompact_coordinateCylinder (normal := normal)).of_isClosed_subset isClosed_closure
      (closure_minimal interior_subset (isClosed_coordinateCylinder (normal := normal)))
  have hCZ : (coordinateCylinder normal) ⊆ interior Z := (coordinateCylinder_subset_closedBall (normal := normal)).trans
    ((closedBall_subset_ball (by norm_num)).trans
      (isOpen_ball.subset_interior_iff.mpr ball_subset_closedBall))
  have hYZ : closure Y ⊆ Z :=
    (closure_minimal interior_subset (isClosed_coordinateCylinder (normal := normal))).trans (hCZ.trans interior_subset)
  have hZO : Z ⊆ O := closedBall_subset_ball (by norm_num)
  have hZ' : closure (interior Z) ⊆ O :=
    (closure_minimal interior_subset isClosed_closedBall).trans hZO
  have hZ'c : IsCompact (closure (interior Z)) :=
    (isCompact_closedBall (0 : (X dim)) (5/2)).of_isClosed_subset isClosed_closure
      (closure_minimal interior_subset isClosed_closedBall)
  obtain ⟨pmin,εmax,Rmax,hεmax,hRmax,hTests⟩ :=
    MovingSphere.exists_uniform_strict_conformal_spheres (normal := normal) (Y := interior Z) (Ω := O) (D := D)
      isOpen_interior isOpen_ball hZ'c hZ' (isCompact_closedBall (0 : (X dim)) 3)
      ball_subset_closedBall hq₁ hq₂ hq₁₀
  obtain ⟨p,R,ε,C,ρ,c₀,K,floor,ε₀,m,M,Cj,E,hp,hpmin,hR,hRR,hε,hεε,hC,hρ,hK,hfloor,
      hε₀,hEst,hE,hNormal,hRadius,hData⟩ :=
    exists_uniform_conformalSphereData_on_centers (normal := normal) hCoercivity pmin εmax Rmax hεmax hRmax
      isOpen_interior (isOpen_ball : IsOpen O) hYc hYZ (isCompact_closedBall (0 : (X dim)) (5/2)) hZO
      (isCompact_closedBall (0 : (X dim)) 3) ball_subset_closedBall hq₁ hq₂ hq₁₀
  have hSetup : ConformalCylinderSphereSetup normal q₁ q₂ E p R ε K ρ c₀ floor M Cj := hData
  have hA : Icc (-1 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := Icc_mem_nhds (by norm_num) (by norm_num)
  have hStrict := ((hTests p hpmin ε ⟨hε,hεε⟩ R ⟨hR,hRR⟩).and hA).mono fun lam h hlam =>
    h.1 hlam (hE.comp (contDiff_const.prodMk contDiff_id))
      ((hNormal lam h.2).mono_centers (interior_subset : interior Z ⊆ Z))
  have hScaledData := uniformCylinderScaledGreenDataJets hn hU hW' hside'
    hq₁ hq₂ hq₁₀ hq₂₀ hH₁ hH₂ hmatch hGreen (isCompact_closedBall (0 : (X dim)) (5/2)) hCZ hZO hE
    hρ hR hε.le htb (show 0 < p by omega) hdepth hNormal
    (fun a ha y hy => hRadius a ha y (interior_subset (hCZ hy))) hStrict (2*dim+8)
  have hTransfer := hProduce hU hside' hq₁ hq₂ hq₁₀ hq₂₀ hcoord₁ hcoord₂ hH₁ hH₂ hmatch hGreen
    hv₁ hv₂ hpair hE hp hρ hR hε htb hK hdepth (isCompact_closedBall _ _) hCZ hZO hNormal hRadius
    hSetup hScaledData
  exact exists_ball_metric_eq_of_conformalCylinder_transfer hn hU hW' hside'
    ⟨fun i j => (hq₁.1 i j).mono (subset_univ U),fun x _ => hq₁.2 x (mem_univ x)⟩
    ⟨fun i j => (hq₂.1 i j).mono (subset_univ U),fun x _ => hq₂.2 x (mem_univ x)⟩
    hcoord₁ hcoord₂ hmatch hv₁ hv₂ hHess htb hdepth hp hR hε hε₀ hC.le hK hfloor hEst hSetup hTransfer

end CalderonN
