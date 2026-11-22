module

public import Proof.Manuscript.MovingTrace.NormalBallPoissonTube
public import Proof.Manuscript.MovingTrace.RadialVelocityOperator
public import Proof.Manuscript.PhysicalVelocityTube
public import Proof.Manuscript.RadializedPhysicalMetric
public import Proof.Manuscript.MovingSymbolGeometryProfile
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

noncomputable section
set_option maxHeartbeats 5300000
set_option backward.isDefEq.respectTransparency false

open CalderonN Set Metric
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Elementwise

namespace CalderonPaper

variable {n : ℕ} [Nontrivial (Fin (n+1))]
local notation "Z" => X (n+1)
local notation "S" => standardSphere (n+1)
local notation "P" => MovingSymbolGeometry (n+1)

def physicalSignedVelocity (γ : ℝ → MetricField (n+1))
    (E : ℝ → Z × Z → Z) (e : ℝ → Frame (n+1)) (i : I (n+1)) (q : P × Z) : Z :=
  scaledNormalTraceVelocity (γ q.1.1.1) (E q.1.1.1) (e q.1.1.1)
    q.1.1.2.1 q.1.1.2.2 q.1.2 q.2 (axis i)

def fixedGeometryCompact (Y : Set Z) (B : ℝ) : Set (MovingSymbolFixedGeometry (n+1)) :=
  (Icc (0:ℝ) 1 ×ˢ closure Y) ×ˢ Icc (-B) B

def signedGeometryCompact (Y : Set Z) (ρ B δ : ℝ) : Set P :=
  movingSymbolSignedRadiusEquiv (n+1) '' (fixedGeometryCompact Y B ×ˢ Icc (-δ) ρ)

theorem signedGeometryCompact_isCompact {Y : Set Z} (hY : IsCompact (closure Y))
    (ρ B δ : ℝ) : IsCompact (signedGeometryCompact Y ρ B δ) :=
  (((isCompact_Icc.prod hY).prod isCompact_Icc).prod isCompact_Icc).image
    (movingSymbolSignedRadiusEquiv (n+1)).continuous

theorem movingSymbolGeometryCompact_subset_signed {Y : Set Z} {ρ B δ : ℝ} (hδ : 0 ≤ δ) :
    movingSymbolGeometryCompact Y ρ B ⊆ signedGeometryCompact Y ρ B δ := by
  rintro ⟨⟨lam,y,r⟩,b⟩ ⟨⟨hlam,hy,hr⟩,hb⟩
  change ((lam,(y,r)),b) ∈ signedGeometryCompact Y ρ B δ
  exact ⟨(((lam,y),b),r),⟨⟨⟨hlam,hy⟩,hb⟩,⟨(neg_nonpos.mpr hδ).trans hr.1,hr.2⟩⟩,rfl⟩

theorem exists_signedGeometryCompact_subset {Y : Set Z} (hY : IsCompact (closure Y))
    {ρ B : ℝ} (hρ : 0 < ρ) {U : Set P} (hU : IsOpen U)
    (hJU : movingSymbolGeometryCompact Y ρ B ⊆ U) :
    ∃ δ > 0, signedGeometryCompact Y ρ B δ ⊆ U := by
  let L := movingSymbolSignedRadiusEquiv (n+1)
  let V := L ⁻¹' U
  have hV : IsOpen V := hU.preimage L.continuous
  have hK : IsCompact (fixedGeometryCompact Y B) := (isCompact_Icc.prod hY).prod isCompact_Icc
  have hKV : fixedGeometryCompact Y B ×ˢ Icc (0:ℝ) ρ ⊆ V :=
    fun q hq => hJU ⟨⟨hq.1.1.1,hq.1.1.2,hq.2⟩,hq.1.2⟩
  obtain ⟨Y',D,hY',hD,hKY',hRD,hY'D⟩ := generalized_tube_lemma hK isCompact_Icc hV hKV
  have h0 : (0:ℝ) ∈ D := hRD ⟨le_rfl,hρ.le⟩
  obtain ⟨r,hr,hBD⟩ := Metric.mem_nhds_iff.mp (hD.mem_nhds h0)
  refine ⟨r/2,half_pos hr,?_⟩
  rintro _ ⟨⟨p,s⟩,⟨hp,hs⟩,rfl⟩
  apply hY'D
  refine ⟨hKY' hp,?_⟩
  change s ∈ D
  by_cases hS : 0 ≤ s
  · exact hRD ⟨hS,hs.2⟩
  · apply hBD
    rw [mem_ball_zero_iff,Real.norm_eq_abs,abs_of_neg (lt_of_not_ge hS)]
    linarith [hs.1]

/-- One open signed geometry tube for the metric and every velocity.
The weight is the literal outward radial conormal factor on every unit
sphere in the auxiliary open neighborhood. -/
theorem exists_actual_radialVelocity_model
    {Y Ω : Set Z} (hY : IsCompact (closure Y)) {ρ : ℝ} (hρ : 0 < ρ)
    {γ g : ℝ → MetricField (n+1)}
    (hγ : ∀ lam ∈ Icc (0:ℝ) 1, SmoothMetric univ (γ lam))
    (hg : ∀ lam ∈ Icc (0:ℝ) 1, SmoothMetric univ (g lam))
    (hΓ : ∀ i j, ContDiff ℝ ∞ (fun q : ℝ × Z => γ q.1 q.2 i j))
    (hG : ∀ i j, ContDiff ℝ ∞ (fun q : ℝ × Z => g q.1 q.2 i j))
    {E : ℝ → Z × Z → Z} (hE : ContDiff ℝ ∞ (fun q : ℝ × (Z × Z) => E q.1 q.2))
    (hN : ∀ lam ∈ Icc (0:ℝ) 1, NormalCoordinates (closure Y) Ω (γ lam) (E lam) (fun _ => ρ))
    {e : ℝ → Frame (n+1)} (he : ∀ i, ContDiff ℝ ∞ (fun q : ℝ × Z => e q.1 q.2 i))
    (hFrame : ∀ lam ∈ Icc (0:ℝ) 1, ∀ y ∈ closure Y, ∀ i j,
      metricPair (γ lam) y (e lam y i) (e lam y j) = if i=j then 1 else 0)
    (B : ℝ) :
    ∃ (G : BallPoissonTube P (n+1)) (A : I (n+1) → SmoothRadialVelocity G)
      (U : Set P) (δ : ℝ),
      IsOpen U ∧ 0 < δ ∧ signedGeometryCompact Y ρ B δ ⊆ U ∧
      G.g = radializedNormalFamily (fun q => symmetrizedNormalMetric g E e (q.1.1,q.2)) ∧
      (∀ v : ↥S, ∃ C : SignedPoissonCollar G, C.pole = v) ∧
      (∀ i, (A i).U = U) ∧
      (∀ i q, (A i).weight q = sphereGaussWeight (fun z => G.g (q.1,z)) 1 q.2) ∧
      ∀ i (q : P × Z), q.1.1.1 ∈ Icc 0 1 → q.1.1.2.1 ∈ closure Y →
        (A i).velocity q = physicalSignedVelocity γ E e i q := by
  let J := movingSymbolGeometryCompact Y ρ B
  have hJ : IsCompact J := isCompact_movingSymbolGeometryCompact hY ρ B
  obtain ⟨G,hJG,hM,hCollar⟩ := exists_normalMetric_slope_ballPoissonTube
    hY hρ hg hG hE hN he hFrame B
  obtain ⟨γ₀,U₀,S₀,hγ₀,hγP,hU₀,hS₀,hJU₀,hCS₀,hVel,hEqVel⟩ :=
    exists_global_spd_normalVelocity_tube hY hρ hγ hΓ hE hN he hFrame B
  have hSp : IsCompact (standardSphere (n+1)) := isCompact_sphere _ _
  have hJU : J ×ˢ standardSphere (n+1) ⊆ G.U :=
    fun q hq => G.contains ⟨hJG hq.1,sphere_subset_closedBall hq.2⟩
  obtain ⟨U₁,S₁,hU₁,hS₁,hJU₁,hSS₁,hU₁S₁⟩ := generalized_tube_lemma hJ hSp G.openU hJU
  let U := (G.V ∩ U₀) ∩ U₁
  let W := (S₀ ∩ S₁) ∩ ({0}ᶜ : Set Z)
  have hU : IsOpen U := (G.openV.inter hU₀).inter hU₁
  have hW : IsOpen W := (hS₀.inter hS₁).inter isOpen_compl_singleton
  have hWG : U ×ˢ W ⊆ G.U := fun q hq => hU₁S₁ ⟨hq.1.2,hq.2.1.2⟩
  have hUW : U ×ˢ W ⊆ U₀ ×ˢ S₀ := fun q hq => ⟨hq.1.1.2,hq.2.1.1⟩
  have hJW : J ⊆ U := fun q hq => ⟨⟨hJG hq,hJU₀ hq⟩,hJU₁ hq⟩
  have hS : standardSphere (n+1) ⊆ W := by
    intro z hz
    exact ⟨⟨hCS₀ (sphere_subset_closedBall hz),hSS₁ hz⟩,
      norm_ne_zero_iff.mp ((mem_sphere_zero_iff_norm.mp hz).trans_ne one_ne_zero)⟩
  let K (q : P × Z) := sphereGaussWeight (fun z => G.g (q.1,z)) 1 q.2
  have hC : ContDiffOn ℝ ∞ (fun q : P × Z => ballConormalVector (fun z => G.g (q.1,z)) q.2) G.U :=
    contDiffOn_product_ballConormalVector G.smoothG G.posG
  have hK : ContDiffOn ℝ ∞ K (U ×ˢ W) :=
    (contDiffOn_snd.inner ℝ (hC.mono hWG)).div_const 1
  have hRad (p : P) (hp : p ∈ U) : EqOn (ballConormalVector (fun z => G.g (p,z)))
      (fun z => (1 * K (p,z)) • z) S := by
    intro z hz
    change ballConormalVector (fun x => G.g (p,x)) z = (1 * K (p,z)) • z
    unfold K
    rw [hM]
    exact ballConormalVector_radializedMetric_on_sphere
      (fun x => symmetrizedNormalMetric g E e (p.1,x)) (c := 1) one_ne_zero hz
      (by simpa only [hM,radializedNormalFamily] using G.posG (p,z) (hWG ⟨hp,hS hz⟩))
  let A (i : I (n+1)) : SmoothRadialVelocity G :=
    ⟨U,hU,inter_subset_left.trans inter_subset_left,W,hW,hS,hWG,fun h => h.2 rfl,
      physicalSignedVelocity γ₀ E e i,K,(hVel i).mono hUW,hK,
      fun q hq => (sphereGaussWeight_pos one_pos (G.posG q (hWG hq)) hq.2.2).ne',
      1,one_ne_zero,hRad⟩
  obtain ⟨δ,hδ,hδU⟩ := exists_signedGeometryCompact_subset hY hρ hU hJW
  refine ⟨G,A,U,δ,hU,hδ,hδU,hM,hCollar,fun _ => rfl,fun _ _ => rfl,?_⟩
  exact fun i q hlam hy => hEqVel i q hlam hy

end CalderonPaper
