module

public import Proof.Manuscript.MovingTrace.PhysicalAdjointExpansion
public import Proof.Manuscript.MovingTrace.MovingSymbolProfileBounds
public import Proof.CalderonN.SphereCoercivity
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

noncomputable section
set_option maxHeartbeats 4800000
set_option backward.isDefEq.respectTransparency false

open CalderonN Set Metric
open scoped ContDiff

namespace CalderonPaper

variable {dim : ℕ}

/-- The moving-radius parameter type in the frozen statement. -/
abbrev MovingTraceRadii (Y : Set (X dim)) (γ g₂ : ℝ → MetricField dim) (e : ℝ → Frame dim)
    (ρ floor c₀ ε : ℝ) (Cj : Fin 9 → ℝ) :=
  Σ lam : ↥(Icc (0:ℝ) 1),
    {r : X dim → ℝ // AdmittedTraceRadius Y (γ lam) (g₂ lam) (e lam) ρ floor c₀ ε Cj r}

variable [NeZero dim]

abbrev movingTraceRadiusBeta {Y : Set (X dim)} {γ g₂ : ℝ → MetricField dim} {e : ℝ → Frame dim}
    {ρ floor c₀ ε : ℝ} {Cj : Fin 9 → ℝ}
    (t : MovingTraceRadii Y γ g₂ e ρ floor c₀ ε Cj) : X dim → ℝ := beta (γ t.1) t.2.val

abbrev movingTraceRadiusGeometry {Y : Set (X dim)} {γ g₂ : ℝ → MetricField dim} {e : ℝ → Frame dim}
    {ρ floor c₀ ε : ℝ} {Cj : Fin 9 → ℝ} (i : I dim)
    (t : MovingTraceRadii Y γ g₂ e ρ floor c₀ ε Cj) : X dim → MovingSymbolGeometry dim :=
  movingSymbolGeometryInput t.1 t.2.val i

theorem exists_admittedTraceRadius_geometry_envelope
    {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    (hComp : IsCompact (closure Y)) (hSub : closure Y ⊆ Ω)
    {γ g₁ g₂ : ℝ → MetricField dim}
    (hΓ : ∀ i j, ContDiff ℝ ∞ (fun q : ℝ × X dim => γ q.1 q.2 i j))
    (hG₁ : ∀ i j, ContDiff ℝ ∞ (fun q : ℝ × X dim => g₁ q.1 q.2 i j))
    {e : ℝ → Frame dim} {K : ℝ} (hK : 0 < K) {m : ℕ} {M : Fin (m+1) → ℝ}
    (hbg : ∀ lam ∈ Icc (0 : ℝ) 1, Background Ω K M (γ lam) (g₁ lam) (g₂ lam) (e lam))
    {ρ floor c₀ ε : ℝ} (hρ : 0 < ρ) (hFloor : 1 ≤ floor) (hε : 0 ≤ ε) (Cj : Fin 9 → ℝ) :
    let R := MovingTraceRadii Y γ g₂ e ρ floor c₀ ε Cj
    ∃ B ≥ (1:ℝ), ∃ D ≥ (1:ℝ),
      (∀ t : R, ∀ y ∈ Y, 1 ≤ movingTraceRadiusBeta t y) ∧
      ∀ i : I dim, (∀ t : R, ContDiff ℝ ∞ (movingTraceRadiusGeometry i t)) ∧
        (∀ t : R, MapsTo (movingTraceRadiusGeometry i t) Y (movingSymbolGeometryCompact Y ρ B)) ∧
        ∀ (t : R) y, y ∈ Y → ∀ j ≤ 6,
          ‖iteratedFDeriv ℝ j (movingTraceRadiusGeometry i t) y‖ ≤ D*(movingTraceRadiusBeta t y)^j := by
  let R := MovingTraceRadii Y γ g₂ e ρ floor c₀ ε Cj
  obtain ⟨B,hB,hBudgets⟩ := uniform_admittedRadius_profile_jets (c₀ := c₀)
    hY hΩ hComp hSub hΓ hG₁ hK hbg hρ hFloor hε Cj
  have hβ (t : R) (y : X dim) (hy : y ∈ Y) : 1 ≤ movingTraceRadiusBeta t y :=
    hFloor.trans (t.2.property.2.1.2 y hy).2.1
  obtain ⟨D,hD,hGeom⟩ := exists_movingSymbolGeometryInput_envelope hComp ρ
    (fun t : R => t.1.val) (fun t : R => t.2.val) movingTraceRadiusBeta
    (fun t => t.1.property) (fun t => t.2.property.1)
    (fun t y hy => ⟨(t.2.property.2.1.2 y hy).1.le,(t.2.property.2.2.2 y hy).le⟩)
    hβ hB (fun t y hy => hBudgets t.1 t.1.property t.2 t.2.property y hy)
  exact ⟨B,hB,D,hD,hβ,hGeom⟩

variable {n : ℕ} [Nontrivial (Fin (n+1))]
local notation "d" => n+1
local notation "Z" => X (n+1)
local notation "P" => MovingSymbolGeometry (n+1)
local notation "S" => standardSphere (n+1)

/-- A physical radius and its companion radius-zero point both lie in
one signed model tube. The exact pointwise conclusion then follows from
one Taylor identity for that same operator. -/
theorem actualMovingTraceAdjoint_admitted_expansion
    {Y Ω : Set Z} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {γ g₁ g₂ : ℝ → MetricField d}
    (hγ : ∀ lam ∈ Icc (0:ℝ) 1, SmoothMetric univ (γ lam))
    (hg₁ : ∀ lam ∈ Icc (0:ℝ) 1, SmoothMetric univ (g₁ lam))
    {e : ℝ → Frame d} (he : ∀ j, ContDiff ℝ ∞ (fun q : ℝ × Z => e q.1 q.2 j))
    {E : ℝ → Z × Z → Z} (hE : ContDiff ℝ ∞ (fun q : ℝ × (Z × Z) => E q.1 q.2))
    {K : ℝ} (hK : 0 < K) {m : ℕ} {M : Fin (m+1) → ℝ}
    (hbg : ∀ lam ∈ Icc (0:ℝ) 1, Background Ω K M (γ lam) (g₁ lam) (g₂ lam) (e lam))
    {ρ : ℝ} (hρ : 0 < ρ)
    (hN : ∀ lam ∈ Icc (0:ℝ) 1, NormalCoordinates (closure Y) Ω (γ lam) (E lam) (fun _ => ρ))
    {B δ : ℝ} (hδ : 0 < δ) {U : Set P} (hJU : signedGeometryCompact Y ρ B δ ⊆ U)
    {G : BallPoissonTube P d} (A : I d → SmoothRadialVelocity G) (hAU : ∀ i, (A i).U = U)
    (hG : G.g = radializedNormalFamily (fun p => symmetrizedNormalMetric g₁ E e (p.1.1,p.2)))
    (hW : ∀ i q, (A i).weight q = sphereGaussWeight (fun z => G.g (q.1,z)) 1 q.2)
    (hV : ∀ i (q : P × Z), q.1.1.1 ∈ Icc 0 1 → q.1.1.2.1 ∈ closure Y →
      (A i).velocity q = physicalSignedVelocity γ E e i q)
    {floor c₀ ε : ℝ} {Cj : Fin 9 → ℝ}
    (hMaps : ∀ i, ∀ t : MovingTraceRadii Y γ g₂ e ρ floor c₀ ε Cj,
      MapsTo (movingTraceRadiusGeometry i t) Y (movingSymbolGeometryCompact Y ρ B)) :
    ∀ t : MovingTraceRadii Y γ g₂ e ρ floor c₀ ε Cj,
      let lam := t.1.val
      let r := t.2.val
      ∀ i, ∀ y ∈ Y, ∀ φ : Z → ℂ, smoothNear φ S → ∀ w : ↥S,
        let p := movingTraceRadiusGeometry i t y
        let L := movingSymbolSignedRadiusEquiv d
        let a := (movingBallToFrame (γ lam) (e lam) (y,axis i)).2
        let fᵢ := coordDeriv i (fun z => Real.log (r z)) y
        actualMovingTraceAdjoint (γ lam) (g₁ lam) (E lam) (e lam) r i y
          (fun z => φ (movingBallToFrame (γ lam) (e lam) (y,z)).2) (frameVector (e lam) y w) =
          ((r y)⁻¹ : ℂ) * flatAngularVelocityAdjoint (fun _ => a) φ w +
          (fᵢ : ℂ) * flatAngularVelocityAdjoint id φ w +
          (r y : ℂ) * radiusTaylorSphereOperator L (A i).operator p φ w +
          radiusFirstSphereOperator L (A i).operator p φ w := by
  intro t
  dsimp only
  intro i y hy φ hφ w
  let lam := t.1.val
  let r := t.2.val
  have hlam : lam ∈ Icc (0:ℝ) 1 := t.1.property
  have hy' : y ∈ closure Y := subset_closure hy
  have hpJ := hMaps i t hy
  change ((lam,(y,r y)),coordDeriv i r y) ∈ movingSymbolGeometryCompact Y ρ B at hpJ
  have hp₀J : ((lam,(y,0)),coordDeriv i r y) ∈ movingSymbolGeometryCompact Y ρ B :=
    ⟨⟨hlam,hy',⟨le_rfl,hρ.le⟩⟩,hpJ.2⟩
  have hJU' : movingSymbolGeometryCompact Y ρ B ⊆ (A i).U := by
    rw [hAU i]
    exact (movingSymbolGeometryCompact_subset_signed hδ.le).trans hJU
  exact actualMovingTraceAdjoint_radius_expansion hY hΩ lam (hbg lam hlam) hK
    (hγ lam hlam) (hg₁ lam hlam) (hE.comp (contDiff_const.prodMk contDiff_id))
    (fun j => (he j).comp (contDiff_const.prodMk contDiff_id)) ((hN lam hlam).mono_centers subset_closure)
    t.2.property.1 (fun z hz => ⟨(t.2.property.2.1.2 z hz).1,t.2.property.2.2.2 z hz⟩)
    i hy (A i) hG (fun p z => hW i (p,z))
    (fun s z => hV i (((lam,y,s),coordDeriv i r y),z) hlam hy')
    (hJU' hpJ) (hJU' hp₀J) hφ w.property

end CalderonPaper
