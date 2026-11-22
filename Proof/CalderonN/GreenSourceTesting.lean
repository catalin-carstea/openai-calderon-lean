module

public import Proof.CalderonN.GreenSourceCutoff
public import Proof.CalderonN.FixedBallMetricEllipticity
public import Proof.CalderonN.SourceSobolev

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

public section

/- Green source testing on separated balls, adapted from GreenSourceTesting
   and its fixed-ball solver in the 3D Theorem 3.1 release. -/
noncomputable section
open Set Filter MeasureTheory Metric
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise

namespace CalderonN
open Elliptic
variable {n : ℕ}

private theorem memLp_two_restrict_ball_of_continuous {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [SecondCountableTopology V] {f : X n → V} (hf : Continuous f) :
    MemLp f 2 ((volume : Measure (X n)).restrict (ball 0 1)) := by
  let μ := (volume : Measure (X n)).restrict (ball 0 1)
  have hfinite : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    simpa [μ] using
      (measure_ball_lt_top (μ := (volume : Measure (X n))) (x := (0 : X n)) (r := (1 : ℝ)))
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0 : X n) 1).bddAbove_image hf.norm.continuousOn
  apply MemLp.of_bound hf.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem (isOpen_ball.measurableSet : MeasurableSet (ball (0 : X n) 1))] with x hx
  exact hC ⟨x, ball_subset_closedBall hx, rfl⟩

private theorem integral_norm_le_volume_sqrt_eLpNorm_two
    {F : Type*} [NormedAddCommGroup F] {μ : Measure (X n)} [IsFiniteMeasure μ]
    {f : (X n) → F} (hf : MemLp f 2 μ) :
    (∫ z, ‖f z‖ ∂μ) ≤ Real.sqrt (μ.real univ) * (eLpNorm f 2 μ).toReal := by
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) (by norm_num)
    hf.aestronglyMeasurable
  have hExp : 1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal = (1:ℝ)/2 := by norm_num
  rw [hExp] at h
  have hfin : eLpNorm f 2 μ * μ univ ^ ((1:ℝ)/2) ≠ ⊤ :=
    ENNReal.mul_ne_top hf.ne (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top _ _))
  have h' := ENNReal.toReal_mono hfin h
  rw [eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable,← integral_norm_eq_lintegral_enorm
    hf.aestronglyMeasurable,ENNReal.toReal_mul,← ENNReal.toReal_rpow,← Real.sqrt_eq_rpow,mul_comm] at h'
  exact h'

private theorem greenSlice_contDiffOn {Ω : Set (X n)} {g : (MetricField n)} {G : (X n) × (X n) → ℝ}
    (hG : GreenGerm Ω g G) {y : (X n)} (hy : y ∈ Ω) :
    ContDiffOn ℝ ∞ (fun x => G (x,y)) (Ω \ {y}) :=
  hG.1.comp (contDiff_id.prodMk contDiff_const).contDiffOn (fun _ hx => ⟨hx.1,hy,hx.2⟩)

private theorem integrableOn_Green_mul_compactSupport
    {Ω B : Set (X n)} {g : (MetricField n)} {G : (X n) × (X n) → ℝ} (hG : GreenGerm Ω g G) {y : (X n)} (hy : y ∈ Ω)
    {f : (X n) → ℝ} (hf : Continuous f) (hfK : HasCompactSupport f) (hSupp : tsupport f ⊆ Ω) :
    IntegrableOn (fun x => G (x,y) * f x) B := by
  let K := tsupport f
  obtain ⟨M,hM⟩ := hfK.bddAbove_image hf.norm.continuousOn
  have hInt : IntegrableOn (fun x => G (x,y)) K :=
    (hG.2.2 y hy).1.integrableOn_compact_subset hSupp hfK
  have hI : IntegrableOn (fun x => G (x,y)*f x) K :=
    hInt.mul_bdd hf.aestronglyMeasurable ((ae_restrict_iff' (isClosed_tsupport f).measurableSet).mpr
      (Eventually.of_forall fun x hx => hM (mem_image_of_mem _ hx)))
  exact (hI.integrable_of_forall_notMem_eq_zero (fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport hx,mul_zero])).integrableOn

set_option maxHeartbeats 2000000 in
private theorem exists_uniform_Green_cutoff_error
    {Ω : Set (X n)} {g : (MetricField n)} {G : (X n) × (X n) → ℝ} (hG : GreenGerm Ω g G)
    (hCover : closedBall (0:(X n)) 1 ⊆ Ω) {a : (X n) → (Mat n)} (ha : ContDiff ℝ ∞ a)
    {χ : (X n) → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχK : HasCompactSupport χ)
    (hχB : tsupport χ ⊆ ball (0:(X n)) 1)
    (hOne : ∀ x ∈ closedBall (0:(X n)) (1/2), χ =ᶠ[𝓝 x] fun _ => 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ closedBall (0:(X n)) (1/4), ∀ b : (X n) → ℝ, ContDiff ℝ ∞ b →
      let B := ball (0:(X n)) 1
      let μ := (volume : Measure (X n)).restrict B
      IntegrableOn (fun x => G (x,y)*greenSourceCutoffError a χ b x) B ∧
      |∫ x in B, G (x,y)*greenSourceCutoffError a χ b x| ≤
        C * ((eLpNorm b 2 μ).toReal + (eLpNorm (fderiv ℝ b) 2 μ).toReal) := by
  let B := ball (0:(X n)) 1
  let μ := (volume : Measure (X n)).restrict B
  let L := closedBall (0:(X n)) (1/4)
  let K := tsupport χ \ ball (0:(X n)) (1/2)
  have hKclose : IsClosed K := (isClosed_tsupport _).inter isOpen_ball.isClosed_compl
  have hK : IsCompact K := hχK.of_isClosed_subset hKclose sdiff_subset
  have hKB : K ⊆ B := sdiff_subset.trans hχB
  have hL₁ : L ⊆ ball (0:(X n)) (1/2) := closedBall_subset_ball (by norm_num)
  have hLO : L ⊆ Ω := (closedBall_subset_closedBall (by norm_num)).trans hCover
  have hKO : K ⊆ Ω := hKB.trans (ball_subset_closedBall.trans hCover)
  have hOff : K ×ˢ L ⊆ OffDiagonal Ω := by
    intro z hz
    exact ⟨hKO hz.1,hLO hz.2,fun he => hz.1.2 (he ▸ hL₁ hz.2)⟩
  obtain ⟨M,hM⟩ := (hK.prod (isCompact_closedBall _ _)).bddAbove_image (hG.1.continuousOn.mono hOff).abs
  obtain ⟨D,hD,hBound⟩ := exists_cutoffError_pointwise_bound hK ha hχ
  let J := max M 0 * D
  have hJ : 0 ≤ J := mul_nonneg (le_max_right _ _) hD
  have hμ : IsFiniteMeasure μ := ⟨by
    simpa only [μ,Measure.restrict_apply_univ,B] using
      measure_ball_lt_top (μ := volume) (x := (0:(X n))) (r := (1:ℝ))⟩
  refine ⟨J * Real.sqrt (μ.real univ),by positivity,?_⟩
  intro y hy b hb
  let F (x : (X n)) := G (x,y)*greenSourceCutoffError a χ b x
  have hFC : ContinuousOn F K :=
    ((greenSlice_contDiffOn hG (hLO hy)).continuousOn.mono
      (fun x hx => ⟨hKO hx,fun hz => hx.2 (by simpa only [mem_singleton_iff.mp hz] using hL₁ hy)⟩)).mul
      (contDiff_greenSourceCutoffError ha hχ hb).continuous.continuousOn
  have hFzero (x : (X n)) (hx : x ∉ K) : F x = 0 := by
    have hEq : greenSourceCutoffError a χ b x = 0 := by
      by_cases hx' : x ∈ tsupport χ
      · have hi : x ∈ ball (0:(X n)) (1/2) := by
          by_contra ho
          exact hx ⟨hx',ho⟩
        exact greenSourceCutoffError_eq_zero (hOne x (ball_subset_closedBall hi))
      · apply greenSourceCutoffError_eq_zero (t := 0)
        exact Filter.mem_of_superset ((isClosed_tsupport χ).isOpen_compl.mem_nhds hx')
          (fun _ hz => image_eq_zero_of_notMem_tsupport hz)
    simp only [F,hEq,mul_zero]
  have hFi : IntegrableOn F B :=
    ((hFC.integrableOn_compact hK).integrable_of_forall_notMem_eq_zero hFzero).integrableOn
  have hPoint (x : (X n)) : ‖F x‖ ≤ J*(‖b x‖ + ‖fderiv ℝ b x‖) := by
    by_cases hx : x ∈ K
    · change ‖G (x,y)*greenSourceCutoffError a χ b x‖ ≤ _
      rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs]
      refine (mul_le_mul ((hM (mem_image_of_mem _ (show (x,y) ∈ K ×ˢ L from ⟨hx,hy⟩))).trans
        (le_max_left _ _)) (hBound b x hx) (abs_nonneg _) (le_max_right _ _)).trans_eq ?_
      change max M 0 * (D*(|b x|+‖fderiv ℝ b x‖)) = J*(|b x|+‖fderiv ℝ b x‖)
      exact (mul_assoc _ _ _).symm
    · rw [hFzero x hx,norm_zero]
      positivity
  have hb₂ := memLp_two_restrict_ball_of_continuous hb.continuous
  have hb'₂ := memLp_two_restrict_ball_of_continuous (hb.continuous_fderiv (by simp))
  have hi₁ : Integrable (fun x => ‖b x‖) μ := (hb₂.integrable (by norm_num)).norm
  have hi₂ : Integrable (fun x => ‖fderiv ℝ b x‖) μ := (hb'₂.integrable (by norm_num)).norm
  refine ⟨hFi,?_⟩
  change |∫ x, F x ∂μ| ≤ _
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le ((hi₁.add hi₂).const_mul J)
    (Eventually.of_forall hPoint)).trans ?_
  rw [integral_const_mul]
  change J*(∫ x, ‖b x‖+‖fderiv ℝ b x‖ ∂μ) ≤ _
  rw [integral_add hi₁ hi₂]
  calc
    _ ≤ J*(Real.sqrt (μ.real univ)*(eLpNorm b 2 μ).toReal+
        Real.sqrt (μ.real univ)*(eLpNorm (fderiv ℝ b) 2 μ).toReal) :=
      mul_le_mul_of_nonneg_left (add_le_add (integral_norm_le_volume_sqrt_eLpNorm_two hb₂)
        (integral_norm_le_volume_sqrt_eLpNorm_two hb'₂)) hJ
    _ = _ := by ring


/-- The fixed-ball source estimate using a homogeneously harmonic ball at the
    evaluation point and a source supported on a separated ball. -/
@[expose] def SeparatedClassicalSourceEstimate (n : ℕ) : Prop :=
  ∀ (a : X n → Mat n), ContDiff ℝ ∞ a → HasCompactSupport a →
      (∀ i j x, a x i j = a x j i) →
      ∀ {lo hi : ℝ}, TauCeti.PDE.UniformlyEllipticOn (fixedBallOpens n : Set (X n)) a lo hi →
      ∃ N : ℝ, 0 < N ∧
        ∀ y ∈ closedBall (0 : X n) (1/4), ∀ x : X n, ∀ r ∈ Ioc (0 : ℝ) (1/4),
          closedBall x r ⊆ closedBall (0 : X n) (1/2) → 2 * r ≤ dist x y →
          ∀ f : X n → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → Function.support f ⊆ ball x r →
            let B := ball (0 : X n) 1
            let μ := (volume : Measure (X n)).restrict B
            let F := (eLpNorm f 2 μ).toReal
            ∃ b : X n → ℝ, ContDiff ℝ ∞ b ∧ EqOn (negativeBallDivergence a b) f (ball 0 (3/4)) ∧
              |b y| ≤ N * r ^ (2 - (n : ℝ)/2) * F ∧
              (eLpNorm (fderiv ℝ b) 2 μ).toReal ≤ N * r * F ∧
              (eLpNorm b 2 μ).toReal ≤ N * r * F

set_option maxHeartbeats 2300000 in
theorem exists_Green_separated_test_bound_of_classical_source [NeZero n] (hn : 3 ≤ n)
    {Ω : Set (X n)} (hΩ : IsOpen Ω) {g : MetricField n} (hg : SmoothMetric univ g)
    {G : X n × X n → ℝ} (hG : GreenGerm Ω g G)
    (hCover : closedBall (0 : X n) 1 ⊆ Ω)
    (hClassical : SeparatedClassicalSourceEstimate n) :
    ∃ N : ℝ, 0 < N ∧
      ∀ y ∈ closedBall (0 : X n) (1/4), ∀ x : X n, ∀ r ∈ Ioc (0 : ℝ) (1/4),
        closedBall x r ⊆ closedBall (0 : X n) (1/2) → 2 * r ≤ dist x y →
        ∀ f : X n → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → Function.support f ⊆ ball x r →
          |∫ z in ball (0 : X n) 1, G (z,y) * f z| ≤
            N * r ^ (2 - (n : ℝ)/2) * (eLpNorm f 2 (volume.restrict (ball (0 : X n) 1))).toReal := by
  let B := ball (0:(X n)) 1
  let μ := (volume : Measure (X n)).restrict B
  let B' := closedBall (0:(X n)) (1/2)
  have hB' : B' ⊆ B := closedBall_subset_ball (by norm_num)
  have hBΩ : B ⊆ Ω := ball_subset_closedBall.trans hCover
  obtain ⟨η,hη,hηK,_,hηOne⟩ := exists_plateau_cutoff isOpen_univ (isCompact_closedBall (0:(X n)) 1)
    (subset_univ _)
  let a (z : (X n)) : (Mat n) := fun i j => η z * divergenceCoeff g z i j
  have ha : ContDiff ℝ ∞ a := by
    change ContDiff ℝ ∞ (fun z : (X n) => fun i j : (I n) => η z * divergenceCoeff g z i j)
    exact contDiff_pi.mpr (fun i => contDiff_pi.mpr (fun j =>
      hη.mul (contDiffOn_univ.mp (contDiffOn_divergenceCoeff hg i j))))
  have haK : HasCompactSupport a := hηK.mono (fun x hx => by
    intro hz
    apply hx
    ext i j
    simp [a,show η x = 0 from hz])
  have hs (i j : (I n)) (x : (X n)) : a x i j = a x j i := by
    simp only [a,divergenceCoeff_symm hg (mem_univ _) i j]
  have haG (x : (X n)) (hx : x ∈ closedBall (0:(X n)) 1) :
      a x = (fun i j => divergenceCoeff g x i j : (Mat n)) := by
    ext i j
    simp [a,(hηOne x hx).eq_of_nhds]
  obtain ⟨lo,hi,hEll⟩ := exists_uniformEllipticOn_fixedBall a ha.continuous
    (fun x hx => by rw [haG x hx]; exact divergenceMatrix_posDef g x (hg.2 x (mem_univ _)))
  obtain ⟨N,hN,hSolve⟩ := hClassical a ha haK hs hEll
  obtain ⟨χ,hχ,hχK,hχInner,hOne⟩ := exists_plateau_cutoff
    (isOpen_ball : IsOpen (ball (0 : X n) (3/4))) (isCompact_closedBall _ _)
    (closedBall_subset_ball (by norm_num : (1 : ℝ)/2 < 3/4))
  have hχB : tsupport χ ⊆ B := hχInner.trans (ball_subset_ball (by norm_num))
  obtain ⟨M,hM,hError⟩ := exists_uniform_Green_cutoff_error hG hCover ha hχ hχK hχB hOne
  refine ⟨N+2*M*N,by positivity,?_⟩
  intro y hy x r hr hSub hSep f hf hfK hFA
  have hAB : ball x r ⊆ B' := ball_subset_closedBall.trans hSub
  have hYB' : y ∈ B' := closedBall_subset_closedBall (by norm_num) hy
  obtain ⟨b,hb,hbEq,hby,hbD,hbV⟩ := hSolve y hy x r hr hSub hSep f hf hfK hFA
  obtain ⟨hI,hErr⟩ := hError y hy b hb
  have hYΩ := hBΩ (hB' hYB')
  have hfΩ : tsupport f ⊆ Ω :=
    (closure_minimal (hFA.trans hAB) isClosed_closedBall).trans (hB'.trans hBΩ)
  have hF : IntegrableOn (fun x => G (x,y)*f x) B :=
    integrableOn_Green_mul_compactSupport hG hYΩ hf.continuous hfK hfΩ
  have hId := green_cutoff_source_identity hΩ ⟨fun i j => (hg.1 i j).mono (subset_univ Ω),
    fun x _ => hg.2 x (mem_univ _)⟩ hG hYΩ isOpen_ball hBΩ ha hs
      (fun x hx => haG x (ball_subset_closedBall hx)) hχ hχK hχB (hOne y hYB').eq_of_nhds
      (fun x hx => (hOne x (hAB (hFA hx))).eq_of_nhds) hb (hbEq.mono hχInner) hF hI
  rw [hId]
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hr' : r ≤ r ^ (2 - (n : ℝ)/2) := by
    conv_lhs => rw [← Real.rpow_one r]
    exact Real.rpow_le_rpow_of_exponent_ge hr.1 (hr.2.trans (by norm_num)) (by linarith)
  calc
    _ ≤ |b y| + |∫ x in B, G (x,y)*greenSourceCutoffError a χ b x| := abs_sub _ _
    _ ≤ N*r ^ (2 - (n : ℝ)/2)*(eLpNorm f 2 μ).toReal +
        M*(N*r*(eLpNorm f 2 μ).toReal+N*r*(eLpNorm f 2 μ).toReal) :=
      add_le_add hby (hErr.trans (mul_le_mul_of_nonneg_left (add_le_add hbV hbD) hM))
    _ ≤ _ := by
      have hNorm : 0 ≤ (eLpNorm f 2 μ).toReal := ENNReal.toReal_nonneg
      rw [show (N+2*M*N)*r ^ (2 - (n : ℝ)/2)*(eLpNorm f 2 μ).toReal =
        N*r ^ (2 - (n : ℝ)/2)*(eLpNorm f 2 μ).toReal + 2*M*N*r ^ (2 - (n : ℝ)/2)*(eLpNorm f 2 μ).toReal by ring]
      refine add_le_add le_rfl ?_
      calc
        _ = (2*M*N)*r*(eLpNorm f 2 μ).toReal := by ring
        _ ≤ _ := by gcongr

end CalderonN
