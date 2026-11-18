import Proof.NormalFrameRelativeNormalization
import Proof.NormalFrameSignedRadiusControl
import Proof.OrthogonalCoefficientEllipticity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres

def normalFrameRelativeGeometricInput (g : MetricField) (r : ℝ)
    (q : NormalFrameRelativeParameter × X) : X × X :=
  normalFrameInput (normalFrameRelativeInput r (normalFrameRelativeNormalization g q.1,q.2))

lemma normalFrameNormalizedCoefficient_isSymm (g g₁ : MetricField) (E : X × X → X)
    (q : NormalFrameParameter × X) (hs : (g₁ (E (normalFrameInput q))).IsSymm) :
    (normalFrameNormalizedCoefficient g g₁ E q).IsSymm := by
  have hM : (normalFrameMetric g₁ E q).IsSymm := by
    ext i j
    exact metricPair_symm g₁ (E (normalFrameInput q))
      (normalVerticalJacobian E q.1.1 (q.1.2.1 • q.1.2.2 q.2) (q.1.2.2 (axis j)))
      (normalVerticalJacobian E q.1.1 (q.1.2.1 • q.1.2.2 q.2) (q.1.2.2 (axis i))) hs
  change ((firstMetricDensityFactor g g₁ q.1.1)⁻¹ •
    (Real.sqrt (normalFrameMetric g₁ E q).det • (normalFrameMetric g₁ E q)⁻¹)).IsSymm
  exact (hM.inv.smul _).smul _

/-- Actual admitted geometry supplies a genuine common parameter
    neighborhood on which all the normal coefficients are symmetric. The
    compact tube argument uses only the fixed spatial ball. -/
theorem uniform_relative_normal_coefficient_symmetric_neighborhood {Y Ω : Set X}
    (hΩ : IsOpen Ω) {m : ℕ} (hm : 2 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η : ℝ,0 < η ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∃ V : Set NormalFrameRelativeParameter,IsOpen V ∧ ((y,frameVectorLinear d.frame y),0) ∈ V ∧
        V ⊆ normalFrameRelativePositiveDomain Ω ∧ ∀ p ∈ V,∀ z ∈ Metric.closedBall (0:X) 2,
          (normalFrameRelativeCoefficient d.γ d.g₁ d.expMap (d.radius y) (p,z)).IsSymm := by
  obtain ⟨η,hη,hη1,hGeo⟩ := uniform_normalFrame_signed_radius_control (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ 2 (by norm_num)
  refine ⟨η,hη,?_⟩
  intro floor hf ε hε hSmall d hd y hy
  let p0 : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let G := normalFrameRelativeGeometricInput d.γ (d.radius y)
  let D := normalFrameRelativePositiveDomain Ω
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hCenter := hd.2.1.center_mem hy
  have he (i j : I) : metricPair d.γ y ((frameVectorLinear d.frame y) (axis i))
      ((frameVectorLinear d.frame y) (axis j)) = if i=j then 1 else 0 := by
    simpa only [frameVectorLinear_apply,frameVector_axis] using hd.1.2.2.2.2.2.2.2 y hCenter i j
  have hp0 : p0 ∈ D := normalFramePositiveDomain_mem_of_orthonormal d.γ
    (normalFrameRelativeZeroL p0) hCenter he
  obtain ⟨U,hU,hTube,hReg⟩ := hd.2.1.1
  let W := U ∩ d.expMap ⁻¹' Ω
  have hW : IsOpen W := hReg.continuousOn.isOpen_inter_preimage hU hΩ
  have hN := hd.1.1.contDiffOn_normalFrameRelativeNormalization hΩ hKpos
  have hG : ContDiffOn ℝ ∞ G (D ×ˢ (univ:Set X)) := by
    intro q hq
    have hNorm := hN.contDiffAt ((isOpen_normalFrameRelativePositiveDomain hΩ).mem_nhds hq.1)
    have hInput := (contDiff_normalFrameRelativeInput (d.radius y)).contDiffAt.comp q
      ((hNorm.comp q contDiffAt_fst).prodMk contDiffAt_snd)
    exact (contDiff_normalFrameInput.contDiffAt.comp q hInput).contDiffWithinAt
  let O := (D ×ˢ (univ:Set X)) ∩ G ⁻¹' W
  have hO : IsOpen O := hG.continuousOn.isOpen_inter_preimage
    ((isOpen_normalFrameRelativePositiveDomain hΩ).prod isOpen_univ) hW
  have hSub : ({p0}:Set NormalFrameRelativeParameter) ×ˢ Metric.closedBall (0:X) 2 ⊆ O := by
    rintro ⟨p,z⟩ ⟨hp,hz⟩
    have hpEq : p = p0 := mem_singleton_iff.mp hp
    subst p
    have hzN : ‖z‖ ≤ 2 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hz
    have hPoint := hGeo floor hf ε hε hSmall d hd y hy (frameVectorLinear d.frame y) he
      (d.radius y) (by rw [abs_of_pos (hd.2.2.2.2.1.2 y hy).1]) z hzN
    have hG0 : G (p0,z) = (y,d.radius y • frameVectorLinear d.frame y z) := by
      change normalFrameInput (normalFrameRelativeInput (d.radius y)
        (normalFrameRelativeNormalization d.γ p0,z)) = _
      rw [normalFrameRelativeNormalization_eq_self d.γ p0 he]
      simp only [normalFrameRelativeInput,normalFrameInput,p0,add_zero,one_mul]
    refine ⟨⟨hp0,mem_univ z⟩,?_⟩
    change G (p0,z) ∈ W
    rw [hG0]
    exact ⟨hTube ⟨hy,hPoint.1.1.le⟩,hPoint.2.1⟩
  obtain ⟨V,B,hV,hB,hpV,hZB,hVB⟩ := generalized_tube_lemma isCompact_singleton
    (isCompact_closedBall (0:X) 2) hO hSub
  refine ⟨V ∩ D,hV.inter (isOpen_normalFrameRelativePositiveDomain hΩ),⟨hpV (mem_singleton p0),hp0⟩,
    inter_subset_right,?_⟩
  intro p hp z hz
  have hMem : (p,z) ∈ O := @hVB (p,z) ⟨hp.1,hZB hz⟩
  have hEnd : d.expMap (G (p,z)) ∈ Ω := hMem.2.2
  rw [normalFrameRelativeCoefficient_eq_raw_normalized]
  change d.expMap (normalFrameInput (normalFrameRelativeInput (d.radius y)
    (normalFrameRelativeNormalization d.γ p,z))) ∈ Ω at hEnd
  have hs : (d.g₁ (d.expMap (normalFrameInput (normalFrameRelativeInput (d.radius y)
      (normalFrameRelativeNormalization d.γ p,z))))).IsSymm := (hd.1.2.1.2 _ hEnd).1
  exact normalFrameNormalizedCoefficient_isSymm d.γ d.g₁ d.expMap _ hs

end ShrinkingSpheres
