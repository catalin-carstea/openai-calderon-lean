module

public import Proof.CalderonN.UniformMovingGreenDensity

import Proof.Manuscript.BallConormalMixed
import Proof.Manuscript.FramedJetComposition
import Mathlib.Tactic

public section

noncomputable section

open Set Filter Metric CalderonN
open scoped ContDiff Topology

namespace CalderonPaper

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

set_option maxHeartbeats 6000000 in
/-- Finite mixed jets of the literal Green density in its orthonormal
frame. A positive radius floor turns the parameter weight into a
uniform constant on the region under consideration. -/
theorem exists_uniform_framed_movingGreen_mixed_jets
    (m : ℕ)
    {γ g : ℝ → MetricField dim}
    {E : ℝ → (X dim) × (X dim) → X dim} {e : ℝ → Frame dim}
    (hγ : ∀ i j, ContDiff ℝ ∞ (fun p : ℝ × X dim => γ p.1 p.2 i j))
    (hγPos : ∀ lam y, (γ lam y).PosDef)
    (hg : ∀ i j, ContDiff ℝ ∞ (fun p : ℝ × X dim => g p.1 p.2 i j))
    (hgPos : ∀ lam y, (g lam y).PosDef)
    (hE : ContDiff ℝ ∞ (fun q : ℝ × ((X dim) × X dim) => E q.1 q.2))
    (he : ∀ i, ContDiff ℝ ∞ (fun q : ℝ × X dim => e q.1 q.2 i))
    {S : Set ℝ} {K Y Y' Ω : Set (X dim)} (hS : IsCompact S) (hK : IsCompact K)
    (hY : IsOpen Y) (hYK : Y ⊆ K) (hKY' : K ⊆ Y')
    {ρ b D M : ℝ} (hρ : 0 < ρ) (hb : 0 < b) (hD : 0 ≤ D) (hM : 0 ≤ M)
    (hNormal : ∀ lam ∈ S, NormalCoordinates Y' Ω (γ lam) (E lam) (fun _ => ρ))
    (hFrame : ∀ lam ∈ S, ∀ y ∈ K, ∀ i j,
      metricPair (γ lam) y (e lam y i) (e lam y j) = if i=j then 1 else 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lam ∈ S, ∀ r : X dim → ℝ, ContDiff ℝ ∞ r →
      (∀ y ∈ Y, r y ∈ Ioc 0 (ρ/2)) →
      ∀ {O : Set ((X dim) × X dim)}, IsOpen O → ∀ G : (X dim) × X dim → ℝ, ContDiffOn ℝ ∞ G O →
      (∀ y ∈ Y, ∀ w : ↥(standardSphere dim), normalGreenPoint E e (lam,(y,r y)) w ∈ O) →
      ∀ y ∈ Y, b ≤ r y → ‖fderiv ℝ r y‖ ≤ D →
      ScaledSphereDatumJets (m+dim+4) (scaledNormalGreenDatum E e G) (lam,(y,r y)) (r y) M →
      ∀ w : ↥(standardSphere dim), ∃ H : X dim × X dim → ℝ, ContDiff ℝ ∞ H ∧
        H =ᶠ[𝓝 (y,(w : X dim))]
          (fun q => movingGreenFluxDensity (γ lam) (g lam) (E lam) (e lam) r G
            (q.1,frameVector (e lam) q.1 q.2)) ∧
        ∀ k ≤ m, ‖iteratedFDeriv ℝ k (fun z => H (y,z)) (w : X dim)‖ ≤ C ∧
          ‖iteratedFDeriv ℝ k (fun z => fderiv ℝ (fun x => H (x,z)) y) (w : X dim)‖ ≤ C := by
  let R := ρ/2
  let J : Set (NormalGreenParameter dim) := S ×ˢ (K ×ˢ Icc 0 R)
  have hJ : IsCompact J := hS.prod (hK.prod isCompact_Icc)
  let U' := signedNormalNondegenerate E e
  let Cb := closedBall (0 : X dim) 1
  have hU' : IsOpen U' := signedNormalNondegenerate_isOpen hE he
  let I₀ (q : (NormalGreenParameter dim) × X dim) : (SignedNormalParameter dim) × X dim :=
    ((q.1.1,(q.1.2.1,(q.1.2.2,0))),q.2)
  have hI₀ : ContDiff ℝ ∞ I₀ :=
    (contDiff_fst.fst.prodMk (contDiff_fst.snd.fst.prodMk
      (contDiff_fst.snd.snd.prodMk contDiff_const))).prodMk contDiff_snd
  let U := I₀ ⁻¹' U'
  have hU : IsOpen U := hU'.preimage hI₀.continuous
  have hJU : J ×ˢ Cb ⊆ U := by
    rintro ⟨⟨lam,y,s⟩,w⟩ ⟨⟨hl,hy,hs⟩,hw⟩
    change ((lam,(y,(s,(0 : (I dim) → ℝ)))),w) ∈ U'
    exact signedNormalNondegenerate_of_nonneg_radius 0 (hE.comp (contDiff_const.prodMk contDiff_id))
      (hNormal lam hl) (hKY' hy) (hFrame lam hl y hy) ⟨hs.1,hs.2.trans_lt (half_lt_self hρ)⟩
      ⟨mem_singleton _,hw⟩
  have hg₀ (i j : I dim) : ContDiffOn ℝ ∞ (fun q => normalGreenMetric g E e q i j) U := by
    change ContDiffOn ℝ ∞ (fun q => signedNormalMetric g E e (I₀ q) i j) U
    exact ((contDiff_signedNormalMetric_entry hg hE he i j).comp hI₀).contDiffOn
  have hg₀' (q : (NormalGreenParameter dim) × X dim) (hq : q ∈ U) :
      (normalGreenMetric g E e q).PosDef := by
    change (signedNormalMetric g E e (I₀ q)).PosDef
    exact signedNormalMetric_posDef (g := g) (E := E) (e := e) (q := I₀ q) hgPos hq
  obtain ⟨A,hA,hCon⟩ := exists_uniform_ballConormalDifference_mixed_jets m R (half_pos hρ).le hU hJ hJU hg₀ hg₀'
  let C := |unitSphereArea dim| * (A*M) * (1+(1+D)/b)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C,hC,?_⟩
  intro lam hlam r hr hRad O hO G hG hSphere y hy hFloor hSlope hJet w
  let Γ := γ lam
  let g' := g lam
  let E' := E lam
  let e' := e lam
  have hΓ : SmoothMetric univ Γ :=
    ⟨fun i j => ((hγ i j).comp (contDiff_const.prodMk contDiff_id)).contDiffOn,fun _ _ => hγPos _ _⟩
  have hg' : SmoothMetric univ g' :=
    ⟨fun i j => ((hg i j).comp (contDiff_const.prodMk contDiff_id)).contDiffOn,fun _ _ => hgPos _ _⟩
  have hE' : ContDiff ℝ ∞ E' := hE.comp (contDiff_const.prodMk contDiff_id)
  have he' (i : I dim) : ContDiff ℝ ∞ (fun y => e' y i) :=
    (he i).comp (contDiff_const.prodMk contDiff_id)
  have hFrame' (p : X dim) (hp : p ∈ Y) := hFrame lam hlam p (hYK hp)
  obtain ⟨U₀,hU₀,hYB,_,hgm,hgmPos,_⟩ := exists_smooth_movingBallFamilies hΓ hg' hE'
    ((hNormal lam hlam).mono_centers (hYK.trans hKY')) he' hFrame' hr
    (fun p hp => ⟨(hRad p hp).1,(hRad p hp).2.trans_lt (half_lt_self hρ)⟩)
  let Z (q : X dim × X dim) := (normalBallChartMap E' e' q.1 (r q.1) q.2,q.1)
  let T₀ := Z ⁻¹' O
  have hZ : ContDiff ℝ ∞ Z := (contDiff_movingNormalEndpoint hE' he' hr).prodMk contDiff_fst
  have hT₀ : IsOpen T₀ := hO.preimage hZ.continuous
  have hYT : Y ×ˢ standardSphere dim ⊆ T₀ :=
    fun q hq => hSphere q.1 hq.1 ⟨q.2,hq.2⟩
  have hDat : ContDiffOn ℝ ∞ (framedMovingGreenKernel E' e' r G) T₀ :=
    hG.comp hZ.contDiffOn (fun _ h => h)
  let ψ := movingGreenFluxDensity Γ g' E' e' r G
  let u := ballConormalDifference (normalGreenMetric g E e) (scaledNormalGreenDatum E e G)
  let a (z : X dim) : NormalGreenParameter dim := (lam,(z,r z))
  have ha : ContDiff ℝ ∞ a := contDiff_const.prodMk (contDiff_id.prodMk hr)
  let L := normalGreenAngularLift Γ e' lam r
  let F := movingBallToFrame Γ e'
  have hCompare (p z : X dim) (hp : p ∈ Y) (hz : z ≠ 0) :
      ψ (p,frameVector e' p z) = unitSphereArea dim * u (a p,z) := by
    let q := (p,frameVector e' p z)
    let slice (v : X dim) := (p,v)
    have hI : ContDiff ℝ ∞ slice := contDiff_const.prodMk contDiff_id
    have hChart : closedBall (0 : X dim) 1 ⊆ slice ⁻¹' U₀ := fun _ hv => hYB ⟨hp,hv⟩
    have hd' : smoothNear (fun v => framedMovingGreenKernel E' e' r G (p,v)) (standardSphere dim) :=
      ⟨slice ⁻¹' T₀,hT₀.preimage hI.continuous,fun _ hv => hYT ⟨hp,hv⟩,
        hDat.comp hI.contDiffOn (fun _ h => h)⟩
    have hL : L q = (a p,z) := normalGreenAngularLift_frame (hFrame' p hp)
    have hF : (F q).2 = z := congrArg Prod.snd hL
    have hEq := movingGreenFluxDensity_eq_ballConormalDifference lam r G q
      (hU₀.preimage hI.continuous) hChart (smoothMetric_movingBall_slice hgm hgmPos p) hd' (hF.symm ▸ hz)
    exact hEq.trans (congrArg (fun q => unitSphereArea dim * u q) hL)
  have haJ : a y ∈ J := ⟨hlam,hYK hy,(hRad y hy).1.le,(hRad y hy).2⟩
  have hrPos := (hRad y hy).1
  have hrAbs : |r y| ≤ R := (abs_of_pos hrPos).symm ▸ (hRad y hy).2
  obtain ⟨⟨V,hV,haV,huV⟩,hJetU⟩ := hCon _ (a y) haJ (r y) M hrPos.ne' hrAbs hM hJet
  let N : Set (X dim) := ({0}ᶜ : Set (X dim))
  have hN : IsOpen N := isClosed_singleton.isOpen_compl
  have hwN : (w : X dim) ∈ N := by
    change (w : X dim) ≠ 0
    intro hz
    have hn := mem_sphere_zero_iff_norm.mp w.property
    simp [hz] at hn
  let w₀ : NormalGreenParameter dim × X dim := (a y,w)
  obtain ⟨B,hB,_,W,hW,hwW,_,hEq⟩ := exists_contDiff_extension_near_compact (hV.prod hN)
    (isCompact_singleton (x := w₀)) (singleton_subset_iff.mpr ⟨haV,hwN⟩) huV
  have hwW' : w₀ ∈ W := hwW (mem_singleton _)
  have hfEq : B =ᶠ[𝓝 w₀] u := hEq.eventuallyEq_of_mem (hW.mem_nhds hwW')
  let lift (q : X dim × X dim) := (a q.1,q.2)
  have hLift : ContDiff ℝ ∞ lift := (ha.comp contDiff_fst).prodMk contDiff_snd
  let H (q : X dim × X dim) := unitSphereArea dim * B (lift q)
  have hH : ContDiff ℝ ∞ H := contDiff_const.mul (hB.comp hLift)
  have hHΨ : H =ᶠ[𝓝 (y,(w : X dim))] fun q => ψ (q.1,frameVector e' q.1 q.2) := by
    have ht : Tendsto lift (𝓝 (y,(w : X dim))) (𝓝 w₀) :=
      hLift.continuous.continuousAt
    filter_upwards [hfEq.comp_tendsto ht,continuous_fst.continuousAt.preimage_mem_nhds (hY.mem_nhds hy),
      continuous_snd.continuousAt.preimage_mem_nhds (hN.mem_nhds hwN)] with q hq hqY hqN
    change unitSphereArea dim * B (lift q) = _
    change B (lift q) = u (lift q) at hq
    rw [hq]
    exact (hCompare q.1 q.2 hqY hqN).symm
  refine ⟨H,hH,hHΨ,?_⟩
  intro k hk
  have hBAng : (fun z => B (a y,z)) =ᶠ[𝓝 (w : X dim)] fun z => u (a y,z) :=
    hfEq.comp_tendsto ((continuous_const.prodMk continuous_id).continuousAt)
  have hBJets : (fun p => iteratedFDeriv ℝ k (fun z => B (p,z)) w) =ᶠ[𝓝 (a y)]
      (fun p => iteratedFDeriv ℝ k (fun z => u (p,z)) w) := by
    filter_upwards [(continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds
      (hW.mem_nhds hwW')] with p hp
    have hpW : (p,(w:X dim)) ∈ W := hp
    have hEw : (fun z => B (p,z)) =ᶠ[𝓝 (w:X dim)] fun z => u (p,z) :=
      (hEq.eventuallyEq_of_mem (hW.mem_nhds hpW)).comp_tendsto
        ((continuous_const.prodMk continuous_id).continuousAt)
    exact (hEw.iteratedFDeriv ℝ k).eq_of_nhds
  have hBaseD : ‖fderiv ℝ a y‖ ≤ 1+D := by
    have hF := (hasFDerivAt_const (c := lam) y).prodMk
      ((hasFDerivAt_id y).prodMk (hr.differentiable (by simp) y).hasFDerivAt)
    rw [show fderiv ℝ a y = _ from hF.fderiv]
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    change ‖((0 : ℝ),(v,fderiv ℝ r y v))‖ ≤ (1+D)*‖v‖
    rw [Prod.norm_def,Prod.norm_def,norm_zero]
    have hZ : 0 ≤ (1+D)*‖v‖ := by positivity
    have hV : ‖v‖ ≤ (1+D)*‖v‖ := by nlinarith [mul_nonneg hD (norm_nonneg v)]
    have hS : ‖fderiv ℝ r y v‖ ≤ (1+D)*‖v‖ :=
      ((fderiv ℝ r y).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (hSlope.trans (by linarith)) (norm_nonneg v))
    exact max_le hZ (max_le hV hS)
  have hMix (v : NormalGreenParameter dim) :
      ‖fderiv ℝ (fun p => iteratedFDeriv ℝ k (fun z => B (p,z)) w) (a y) v‖ ≤ (A*M/b)*‖v‖ := by
    rw [hBJets.fderiv_eq]
    let L₁ := fderiv ℝ (fun p => iteratedFDeriv ℝ k (fun z => u (p,z)) w) (a y)
    have h := (hJetU w w.property).2 k hk ((r y)⁻¹ • v)
    have hmul : r y • ((r y)⁻¹ • v) = v := smul_inv_smul₀ hrPos.ne' v
    change ‖L₁ (r y • ((r y)⁻¹ • v))‖ ≤ A*M*‖(r y)⁻¹ • v‖ at h
    rw [hmul,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hrPos.le)] at h
    calc
      _ ≤ A*M*((r y)⁻¹ * ‖v‖) := h
      _ ≤ A*M*(b⁻¹ * ‖v‖) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (inv_anti₀ hb hFloor) (norm_nonneg v)) (mul_nonneg hA hM)
      _ = A*M/b*‖v‖ := by ring
  have hBAS : ContDiff ℝ ∞ (fun z => B (a y,z)) := hB.comp (contDiff_const.prodMk contDiff_id)
  constructor
  · change ‖iteratedFDeriv ℝ k (fun z => (unitSphereArea dim) • B (a y,z)) w‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply' (hBAS.contDiffAt.of_le (by simp)),norm_smul,Real.norm_eq_abs,
      (hBAng.iteratedFDeriv ℝ k).eq_of_nhds]
    refine (mul_le_mul_of_nonneg_left ((hJetU w w.property).1 k hk) (abs_nonneg _)).trans ?_
    dsimp only [C]
    apply le_mul_of_one_le_right (by positivity)
    linarith [show 0 ≤ (1+D)/b by positivity]
  · have hL : ContDiff ℝ ∞ (fun q : X dim × X dim => B (a q.1,q.2)) := hB.comp hLift
    change ‖iteratedFDeriv ℝ k (fun z => fderiv ℝ (fun x => unitSphereArea dim * B (a x,z)) y) w‖ ≤ C
    rw [norm_iteratedFDeriv_fderiv_first_slice_const_mul _ hL y w k]
    refine (mul_le_mul_of_nonneg_left
      (norm_fderiv_angularJet_comp_base_le ha hB y w k (by positivity) hBaseD (by positivity) hMix)
      (abs_nonneg _)).trans ?_
    dsimp only [C]
    have hpos : 0 ≤ |unitSphereArea dim| * (A*M) := by positivity
    calc
      _ = |unitSphereArea dim| * (A*M) * ((1+D)/b) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hpos

end CalderonPaper
