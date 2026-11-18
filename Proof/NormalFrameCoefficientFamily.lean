import Proof.NormalFrameCoefficientModel
import Proof.ParallelCoefficientPairFamily

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres

/-- A genuine open coefficient domain with center, radius and frame allowed
    to vary independently. Smoothness comes from the admitted actual normal
    map and metric; orthonormality away from the chosen point is unnecessary. -/
theorem Background.exists_normalFrame_coefficient_domain {Y Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {g g₁ g₂ : MetricField} {e : Frame}
    (h : Background Ω K M g g₁ g₂ e) (hK : 0 < K)
    {E : X × X → X} {R : X → ℝ} (hN : NormalCoordinates Y Ω g E R)
    {y : X} (hy : y ∈ Y) (s : ℝ) (L : X →L[ℝ] X) (z : X)
    (hv : s • L z ∈ disk g y (R y))
    (hPos : 0 < (normalFrameMetric g₁ E ((y,(s,L)),z)).det) :
    ∃ S : Set (NormalFrameParameter × X),IsOpen S ∧ ((y,(s,L)),z) ∈ S ∧
      ContDiffOn ℝ ∞ (normalFrameNormalizedCoefficient g g₁ E) S := by
  obtain ⟨U,hU,hTube,hReg⟩ := hN.1
  let W := U ∩ E ⁻¹' Ω
  have hW : IsOpen W := hReg.continuousOn.isOpen_inter_preimage hU hΩ
  have hTensor (p : X × X) (hp : p ∈ W) : ContDiffAt ℝ ∞ (normalJointMetricTensor g₁ E) p :=
    contDiffAt_normalJointMetricTensor g₁ E p (hReg.contDiffAt (hU.mem_nhds hp.1))
      (fun i j => (h.2.1.1 i j).contDiffAt (hΩ.mem_nhds hp.2))
  let D := normalFrameInput ⁻¹' W ∩ (fun q : NormalFrameParameter × X => q.1.1) ⁻¹' Ω
  have hD : IsOpen D := (hW.preimage contDiff_normalFrameInput.continuous).inter
    (hΩ.preimage (continuous_fst.comp continuous_fst))
  have hMetric : ContDiffOn ℝ ∞ (normalFrameMetric g₁ E) D := by
    intro q hq
    exact (contDiffAt_normalFrameMetric g₁ E q (hTensor _ hq.1)).contDiffWithinAt
  have hDet := contDiffOn_matrixFamily_det (normalFrameMetric g₁ E)
    (fun i j => contDiffOn_pi.mp (contDiffOn_pi.mp hMetric i) j)
  let S := D ∩ (fun q => (normalFrameMetric g₁ E q).det) ⁻¹' Ioi (0:ℝ)
  have hS : IsOpen S := hDet.continuousOn.isOpen_inter_preimage hD isOpen_Ioi
  have hx : E (y,s • L z) ∈ Ω := by
    simpa only [one_smul] using hN.path_image hy (s • L z) hv (show (1:ℝ) ∈ Icc (0:ℝ) 1 from ⟨zero_le_one,le_rfl⟩)
  have hHere : ((y,(s,L)),z) ∈ S := ⟨⟨⟨hTube ⟨hy,hv⟩,hx⟩,hN.center_mem hy⟩,hPos⟩
  refine ⟨S,hS,hHere,?_⟩
  intro q hq
  exact (contDiffAt_normalFrameNormalizedCoefficient g g₁ E q (hTensor _ hq.1.1)
    ((h.firstMetricDensityFactor_smooth hK).contDiffAt (hΩ.mem_nhds hq.1.2)) hq.2).contDiffWithinAt

/-- One genuine compact coefficient family around the actual center/radius/
    frame parameter represents all three sorts of local variations. -/
theorem uniform_normalFrame_coefficient_family {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 2 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η : ℝ,0 < η ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∃ A : NormalFrameParameter × X → Mat,∃ hA : ContDiff ℝ ∞ A,
      ∃ S : Set X,∃ hS : IsCompact S,∃ hz : ∀ p z,z ∉ S → A (p,z) = 0,
      ∃ V : Set NormalFrameParameter,IsOpen V ∧ (y,(d.radius y,frameVectorLinear d.frame y)) ∈ V ∧
        (∀ p ∈ V,p.1 ∈ Y) ∧ ∀ p ∈ V,∀ z ∈ Metric.closedBall (0:X) 2,
          A =ᶠ[𝓝 (p,z)] normalFrameNormalizedCoefficient d.γ d.g₁ d.expMap := by
  obtain ⟨ηG,hηG,hGeometry⟩ := uniform_normal_control_on_disk (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ 2 (by norm_num)
  obtain ⟨ηE,hηE,hElliptic⟩ := uniform_enlarged_framed_normal_elliptic (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ 2 (by norm_num)
  refine ⟨min ηG ηE,lt_min hηG hηE,?_⟩
  intro floor hf ε hε hSmall d hd y hy
  let r := d.radius y
  let L := frameVectorLinear d.frame y
  let p0 : NormalFrameParameter := (y,(r,L))
  let B := normalFrameNormalizedCoefficient d.γ d.g₁ d.expMap
  let YP : Set NormalFrameParameter := Prod.fst ⁻¹' Y
  have hYP : IsOpen YP := hY.preimage continuous_fst
  have hp0 : p0 ∈ YP := hy
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hFrame := hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy)
  have hEll := hElliptic floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd y hy d.g₁ (by simp)
  have hLocal (z : X) (hz : z ∈ Metric.closedBall (0:X) 2) :
      ∃ W : Set (NormalFrameParameter × X),IsOpen W ∧ (p0,z) ∈ W ∧ ContDiffOn ℝ ∞ B W := by
    have hw := frameVector_mem_disk d.γ d.frame y z 2 hFrame hz
    have hPack := hGeometry floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy (L z) hw
    have hPos : 0 < (normalFrameMetric d.g₁ d.expMap (p0,z)).det := by
      rw [normalFrameMetric_framed]
      exact (hEll.posDef (by positivity) hz).det_pos
    exact hd.1.exists_normalFrame_coefficient_domain hΩ hKpos hd.2.1 hy r L z
      (mem_of_mem_of_subset hPack.1.1 interior_subset) hPos
  choose W hW hHere hBW using hLocal
  let U := ⋃ z,⋃ hz : z ∈ Metric.closedBall (0:X) 2,W z hz
  have hU : IsOpen U := isOpen_iUnion (fun z => isOpen_iUnion (fun hz => hW z hz))
  have hBU : ContDiffOn ℝ ∞ B U := by
    intro p hp
    simp only [U,mem_iUnion] at hp
    obtain ⟨z,hz,hp⟩ := hp
    exact ((hBW z hz).contDiffAt ((hW z hz).mem_nhds hp)).contDiffWithinAt
  have hSub : {p0} ×ˢ Metric.closedBall (0:X) 2 ⊆ U := by
    rintro ⟨p,z⟩ ⟨hp,hz⟩
    have hpp : p = p0 := hp
    subst p
    exact mem_iUnion_of_mem z (mem_iUnion_of_mem hz (hHere z hz))
  obtain ⟨A,hA,S,hS,hz,V,hV,hpV,hVY,hRep⟩ :=
    exists_local_commonSupport_matrix_family_on_open hYP B 2 U hU hBU hp0 hSub
  exact ⟨A,hA,S,hS,hz,V,hV,hpV,hVY,hRep⟩

end ShrinkingSpheres
