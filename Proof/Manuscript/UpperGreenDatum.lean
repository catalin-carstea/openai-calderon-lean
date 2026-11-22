module

public import Proof.CalderonN.ScaledGreenDatumJets
public import Proof.CalderonN.ScaledSphereDatumExtension
public import Proof.CalderonN.FixedTube.Initialization

import Proof.CalderonN.RescaledGreenSeeds
import Proof.CalderonN.RescaledProductJets
import Proof.CalderonN.NormalEndpointJets
import Proof.CalderonN.CompactBounds
import Mathlib.Tactic

public section

noncomputable section
open Set Filter Metric CalderonN FixedTube
open scoped ContDiff Topology

namespace CalderonPaper

variable {dim : ℕ} [NeZero dim]

set_option maxHeartbeats 2400000 in
/-- The upper branch of the released rescaled seed estimate uses only
the bounded continuation kernel in its fixed-separation neighborhood. -/
theorem exists_upper_rescaledGreenSeed_jet_bounds
    {g₁ g₂ : MetricField dim} (hg₁ : SmoothMetric univ g₁) (hg₂ : SmoothMetric univ g₂)
    {d R M : ℝ} (hd : 0 < d) (hR : 0 < R) (hM : 0 ≤ M) (m : ℕ) :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ lam ∈ Icc (-1 : ℝ) 1,
      ∀ x y : X dim, ‖x‖ ≤ 3 → ‖y‖ ≤ 3 → d ≤ dist x y → ∀ r ∈ Ioc 0 R,
      ∀ {O : Set (X dim × X dim)}, IsOpen O → fixedSeparationSet 4 (d/2) ⊆ O →
      ∀ F G : X dim × X dim → ℝ,
        ProductSolutionOn (dilatedMetric g₁ lam) (dilatedMetric g₂ lam) O F →
        (∀ q ∈ fixedSeparationSet 4 (d/2), |F q| ≤ M) → G =ᶠ[𝓝 (x,y)] F →
      ∃ H : X dim × X dim → ℝ, ContDiff ℝ ∞ H ∧
        H =ᶠ[𝓝 0] (fun q => r^(dim-2) * G (separateAffineChart x y (η*r) q)) ∧
        ∀ k ≤ m, ‖iteratedFDeriv ℝ k H 0‖ ≤ C := by
  let η := min (1/(2*R)) (d/(8*R))
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have hηR : η*R ≤ 1/2 := by
    have he : (1/(2*R))*R = 1/2 := by field_simp
    exact (mul_le_mul_of_nonneg_right (min_le_left _ _) hR.le).trans_eq he
  have hηd : 4*(η*R) ≤ d/2 := by
    have h := mul_le_mul_of_nonneg_right (min_le_right (1/(2*R)) (d/(8*R))) hR.le
    have he : (d/(8*R))*R = d/8 := by field_simp
    rw [he] at h
    linarith
  obtain ⟨U,hU,hUpperJet⟩ := exists_uniform_rescaled_product_jets hg₁ hg₂ 3 (1/2) m
  refine ⟨η,U*(R^(dim-2)*M),hη,by positivity,?_⟩
  intro lam hlam x y hx hy hSep r hr O hO hOut F G hF hMb hEq
  let s := η*r
  have hs : 0 ≤ s := mul_nonneg hη.le hr.1.le
  have hSR : s ≤ η*R := mul_le_mul_of_nonneg_left hr.2 hη.le
  have hS : s ≤ 1/2 := hSR.trans hηR
  let W := ball (0 : X dim) 2 ×ˢ ball (0 : X dim) 2
  let f := separateAffineChart x y s
  have hf : Continuous f := (contDiff_separateAffineChart _ _ _).continuous
  have hf₀ : f 0 = (x,y) := by simp [f,separateAffineChart,affineChartMap]
  have hRoom (q : X dim × X dim) (hq : q ∈ W) : f q ∈ fixedSeparationSet 4 (d/2) := by
    obtain ⟨h₁,h₂,h₃⟩ := separateAffineChart_room_bounds hx hy hs hS hq
    have hSM := (mul_le_mul_of_nonneg_left hSR (by norm_num : (0:ℝ) ≤ 4)).trans hηd
    exact ⟨h₁,h₂,by rw [← dist_eq_norm]; linarith⟩
  have hMap : MapsTo f W O := fun q hq => hOut (hRoom q hq)
  have hBound (q : X dim × X dim) (hq : q ∈ W) : |r^(dim-2) * F (f q)| ≤ R^(dim-2)*M := by
    rw [abs_mul,abs_of_nonneg (pow_nonneg hr.1.le _)]
    exact mul_le_mul (pow_le_pow_left₀ hr.1.le hr.2 _) (hMb _ (hRoom q hq))
      (abs_nonneg _) (pow_nonneg hR.le _)
  have heq : (fun q => r^(dim-2) * F (f q)) =ᶠ[𝓝 0] fun q => r^(dim-2) * G (f q) := by
    have ht : Tendsto f (𝓝 0) (𝓝 (x,y)) := hf₀ ▸ hf.continuousAt.tendsto
    exact (hEq.comp_tendsto ht).symm.mono (fun q h => congrArg (r^(dim-2) * ·) h)
  obtain ⟨H,hH,hE,hJ⟩ := hUpperJet lam hlam x (mem_closedBall_zero_iff.mpr hx)
    y (mem_closedBall_zero_iff.mpr hy) s ⟨hs,hS⟩ (r^(dim-2)) hO hMap hF (R^(dim-2)*M) (by positivity) hBound
  exact ⟨H,hH,hE.trans heq,hJ⟩


/-- Uniform angular and radius-scaled parameter jets of the actual
normalized datum whenever the full sphere has the upper seed germ. -/
theorem exists_upper_fixedSeparation_datumJets
    {g₁ g₂ : MetricField dim} (hg₁ : SmoothMetric univ g₁) (hg₂ : SmoothMetric univ g₂)
    {E : ℝ → X dim × X dim → X dim} {e : ℝ → Frame dim}
    (hE : ContDiff ℝ ∞ (fun q : ℝ × (X dim × X dim) => E q.1 q.2))
    (he : ∀ i, ContDiff ℝ ∞ (fun q : ℝ × X dim => e q.1 q.2 i))
    {S : Set ℝ} {K : Set (X dim)} (hS : IsCompact S) (hK : IsCompact K)
    (hS₁ : S ⊆ Icc (-1 : ℝ) 1) {d R M : ℝ} (hd : 0 < d) (hR : 0 < R) (hM : 0 ≤ M)
    (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lam ∈ S, ∀ y ∈ K, ∀ r ∈ Ioc 0 R,
      ∀ {O : Set (X dim × X dim)}, IsOpen O → fixedSeparationSet 4 (d/2) ⊆ O →
      ∀ F G : X dim × X dim → ℝ,
        ProductSolutionOn (dilatedMetric g₁ lam) (dilatedMetric g₂ lam) O F →
        (∀ q ∈ fixedSeparationSet 4 (d/2), |F q| ≤ M) →
        (∀ w ∈ standardSphere dim,
          let q := normalGreenPoint E e (lam,(y,r)) w
          q ∈ fixedSeparationSet 3 d ∧ G =ᶠ[𝓝 q] F) →
      ScaledSphereDatumJets m (scaledNormalGreenDatum E e G) (lam,(y,r)) r C := by
  let J : Set (NormalGreenParameter dim) := S ×ˢ (K ×ˢ Icc 0 R)
  have hJ : IsCompact J := hS.prod (hK.prod isCompact_Icc)
  obtain ⟨η,L,hη,hL,hSeed⟩ := exists_upper_rescaledGreenSeed_jet_bounds hg₁ hg₂ hd hR hM m
  obtain ⟨C,hC,hDatum⟩ := exists_scaledNormalGreenDatum_jet_bound hE he hJ hη.ne' m
  refine ⟨C*L,mul_nonneg hC hL,?_⟩
  intro lam hlam y hy r hr O hO hOut F G hF hBound hG w hw
  let q := normalGreenPoint E e (lam,(y,r)) w
  obtain ⟨⟨hx,hy',hsep⟩,hEq⟩ := hG w hw
  have hSep : d ≤ dist q.1 q.2 := by simpa only [dist_eq_norm] using hsep
  obtain ⟨H,hH,hHG,hHjet⟩ := hSeed lam (hS₁ hlam) q.1 q.2 hx hy' hSep r hr hO hOut F G hF hBound hEq
  exact hDatum (lam,(y,r)) ⟨hlam,hy,hr.1.le,hr.2⟩ w hw G H hH hHG L hL hHjet

/-- Fixed positive endpoint separation prevents the radius from
approaching zero uniformly in the compact reference normal chart. -/
theorem exists_upper_fixedSeparation_radius_floor
    {γ : ℝ → MetricField dim} {E : ℝ → X dim × X dim → X dim} {e : ℝ → Frame dim}
    (hE : ContDiff ℝ ∞ (fun q : ℝ × (X dim × X dim) => E q.1 q.2))
    (he : ∀ i, ContDiff ℝ ∞ (fun q : ℝ × X dim => e q.1 q.2 i))
    {S : Set ℝ} {K Y' Ω : Set (X dim)} (hS : IsCompact S) (hK : IsCompact K) (hKY' : K ⊆ Y')
    {ρ d : ℝ} (hd : 0 < d)
    (hNormal : ∀ lam ∈ S, NormalCoordinates Y' Ω (γ lam) (E lam) (fun _ => ρ)) :
    ∃ b > 0, ∀ lam ∈ S, ∀ y ∈ K, ∀ r ∈ Icc 0 (ρ/2), ∀ w ∈ standardSphere dim,
      d ≤ dist (normalGreenPoint E e (lam,(y,r)) w).1 y → b ≤ r := by
  let T := NormalGreenParameter dim × X dim
  let J : Set T := (S ×ˢ (K ×ˢ Icc 0 (ρ/2))) ×ˢ standardSphere dim
  have hJ : IsCompact J := (hS.prod (hK.prod isCompact_Icc)).prod (isCompact_sphere _ _)
  let Δ (q : T) := dist (normalGreenPoint E e q.1 q.2).1 q.1.2.1
  have he' (i : I dim) : ContDiff ℝ ∞ (fun q : T => e q.1.1 q.1.2.1 i) :=
    (he i).comp (contDiff_fst.fst.prodMk contDiff_fst.snd.fst)
  have hVec : ContDiff ℝ ∞ (fun q : T => frameVector (e q.1.1) q.1.2.1 q.2) :=
    contDiff_family_frameVector he' contDiff_snd
  have hPoint : ContDiff ℝ ∞ (fun q : T => (normalGreenPoint E e q.1 q.2).1) :=
    hE.comp (contDiff_fst.fst.prodMk (contDiff_fst.snd.fst.prodMk (contDiff_fst.snd.snd.smul hVec)))
  have hΔ : Continuous Δ := hPoint.continuous.dist continuous_fst.snd.fst
  let A := J ∩ Δ ⁻¹' Ici d
  have hA : IsCompact A := hJ.inter_right (isClosed_Ici.preimage hΔ)
  have hPos (q : T) (hq : q ∈ A) : 0 < q.1.2.2 := by
    have hr := hq.1.1.2.2.1
    rcases eq_or_lt_of_le hr with hz | hz
    · have hEx := (hNormal q.1.1 hq.1.1.1).exp_zero (hKY' hq.1.1.2.1)
      have h0 : Δ q = 0 := by
        simp only [Δ,normalGreenPoint,normalBallChartMap,← hz,zero_smul,hEx,dist_self]
      have hSep : d ≤ Δ q := hq.2
      rw [h0] at hSep
      exact (not_le_of_gt hd hSep).elim
    · exact hz
  obtain ⟨b,hb,h⟩ := Carleman.exists_pos_lower_of_compact hA
    (continuous_fst.snd.snd.continuousOn) hPos
  refine ⟨b,hb,fun lam hlam y hy r hr w hw hsep => ?_⟩
  exact h ((lam,(y,r)),w) ⟨⟨⟨hlam,hy,hr⟩,hw⟩,hsep⟩

end CalderonPaper
