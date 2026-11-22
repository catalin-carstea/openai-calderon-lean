module

public import Proof.CalderonN.FixedTube.CoarsePatchGeometry

public import Proof.CalderonN.FixedTube.DilatedGeometry
public import Proof.CalderonN.FixedTube.BoundedPlaneReference
import Proof.CalderonN.ChartUniqueContinuation
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set Metric Filter
open scoped Topology ContDiff

namespace CalderonN.FixedTube

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {normal : I dim}

private theorem norm_bounds_mem_closure_planeAnnulus {x : (X dim)}
    (hx : x ∈ closure (planeAnnulus (dim := dim))) : (1/2 : ℝ) ≤ ‖x‖ ∧ ‖x‖ ≤ 2 := by
  have hClosed : IsClosed {x : (X dim) | (1/2 : ℝ) ≤ ‖x‖ ∧ ‖x‖ ≤ 2} :=
    (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)
  refine closure_minimal ?_ hClosed hx
  intro z hz
  change 1/2 < ‖z-0‖ ∧ ‖z-0‖ < 2 at hz
  rw [sub_zero] at hz
  exact ⟨hz.1.le,hz.2.le⟩

set_option maxHeartbeats 3800000 in
/-- The normalizations of all bounded planar anchors and positive
separation scales enter the same parameter neighborhood. The patch
extends the actual lower cross and agrees on both of its lower slices. -/
theorem exists_uniform_coarsePatch_with_bound
    {g₁ g₂ : (MetricField dim)} (hg₁ : SmoothMetric univ g₁) (hg₂ : SmoothMetric univ g₂)
    (h₁ : g₁ 0 = 1) (h₂ : g₂ 0 = 1) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ planeDepth/100 ∧
    ∀ B s₀ s₁ : ℝ, 0 < s₀ → s₀ ≤ s₁ →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ lam in 𝓝 (0 : ℝ), ∀ c ∈ closedBall (0 : (X dim)) B, c normal = 0 → ∀ s ∈ Icc s₀ s₁,
      ∀ η < δ*s₀, ∀ F : (X dim) × (X dim) → ℝ,
        ProductSolutionOn (dilatedMetric g₁ lam) (dilatedMetric g₂ lam) (lowerCross normal (B+2*s₁+1) η) F →
        ∃ G, ProductSolutionOn (dilatedMetric g₁ lam) (dilatedMetric g₂ lam) (coarsePatch normal c s δ) G ∧
          EqOn G F ((coarsePatch normal c s δ) ∩ {q | min (q.1 normal) (q.2 normal) < -η}) ∧
          ∀ M : ℝ, 0 ≤ M →
            (∀ q ∈ lowerCross normal (B+2*s₁+1) η, (3/8 : ℝ)*s₀ ≤ ‖q.1-q.2‖ → |F q| ≤ M) →
            ∀ q ∈ retainedPatch c s (δ/2), |G q| ≤ C*M := by
  let a (g : (MetricField dim)) := affineChartMetric g
  let e (g : (MetricField dim)) (hg : SmoothMetric univ g) := smoothMetric_affineChartMetric hg
  obtain ⟨δ,C₁,C₂,γ₁,γ₂,hδ,hδcap,hC₁,hC₂,hγ₂,hγ₂',hγ,hS₁,hO₁,hI⟩ :=
    (exists_planeReference_interpolation (normal := normal)) ((0 : (X dim)),0) (a g₁) (a g₂)
      (e g₁ hg₁) (e g₂ hg₂) (contDiff_affineChartMetric_divergenceCoeff hg₁)
      (contDiff_affineChartMetric_divergenceCoeff hg₂)
      (affineChartMetric_zero h₁) (affineChartMetric_zero h₂)
  obtain ⟨D,hD,hQuant⟩ := (exists_uniform_bounded_planeReference (normal := normal)) ((0 : (X dim)),0)
    (e g₁ hg₁) (e g₂ hg₂) (contDiff_affineChartMetric_divergenceCoeff hg₁)
    (contDiff_affineChartMetric_divergenceCoeff hg₂) hδ hδcap hC₁.le hC₂.le hγ₂ hγ₂'.le
    (by linarith) hO₁ hI
  refine ⟨δ,hδ,hδcap,?_⟩
  intro B s₀ s₁ hs₀ hss
  let a₀ := (3/8 : ℝ)*s₀
  have ha₀ : 0 < a₀ := by dsimp only [a₀]; positivity
  refine ⟨D,hD,?_⟩
  let K : Set ((X dim) × ℝ) := closedBall (0 : (X dim)) B ×ˢ Icc s₀ s₁
  have hK : IsCompact K := (isCompact_closedBall _ _).prod isCompact_Icc
  let φ (p : ℝ × ((X dim) × ℝ)) : (X dim) × ℝ := (p.1 • p.2.1,p.1*p.2.2)
  have hcφ : Continuous φ :=
    (continuous_fst.smul continuous_snd.fst).prodMk (continuous_fst.mul continuous_snd.snd)
  have hφ (z : (X dim) × ℝ) : φ (0,z) = (0,0) := by simp [φ]
  have hUniform := hK.eventually_forall_of_forall_eventually
    (x₀ := (0 : ℝ))
    (P := fun lam z =>
      HarmonicInterpolation (isOpen_ball : IsOpen (planeBall normal (3*planeDepth)))
        (smoothMetric_restrict (e g₁ hg₁ (φ (lam,z))) (subset_univ _)) hS₁ hO₁ C₁ γ₁ ∧
      HarmonicInterpolation (isOpen_openAnnulus 0 (1/2) 2)
        (smoothMetric_restrict (e g₂ hg₂ (φ (lam,z))) (subset_univ _))
        (subset_closure.trans (closure_planeAnnulusObservation_subset (normal := normal))) (planeAnnulusOutput_subset (dim := dim)) C₂ γ₂)
    (fun z _ => by
      have ht : Tendsto φ (𝓝 ((0 : ℝ),z)) (𝓝 ((0 : (X dim)),0)) := by
        rw [← hφ z]
        exact hcφ.continuousAt
      exact ht.eventually hI)
  have hPull {P : (X dim) × ℝ → Prop} (hP : ∀ᶠ z in 𝓝 ((0 : (X dim)),0), P z) :
      ∀ᶠ lam in 𝓝 (0 : ℝ), ∀ z ∈ K, P (φ (lam,z)) :=
    hK.eventually_forall_of_forall_eventually (fun z _ => by
      have ht : Tendsto φ (𝓝 ((0 : ℝ),z)) (𝓝 ((0 : (X dim)),0)) := by
        rw [← hφ z]
        exact hcφ.continuousAt
      exact ht.eventually hP)
  filter_upwards [hUniform,hPull hQuant] with lam hnear hQuant c hc hc₂ s hs η hη F hF
  have hspos : 0 < s := hs₀.trans_le hs.1
  obtain ⟨hI₁,hI₂⟩ := hnear (c,s) ⟨hc,hs⟩
  let A := affineChartProduct c s
  let Ai := affineChartProduct (-(s⁻¹ • c)) s⁻¹
  let L : Set (X dim) := {x | affineChartMap c s x normal < -η}
  let V := A ⁻¹' lowerCross normal (B+2*s₁+1) η
  let G₁ := dilatedMetric g₁ lam
  let G₂ := dilatedMetric g₂ lam
  have hG₁ := smoothMetric_dilatedMetric hg₁ lam
  have hG₂ := smoothMetric_dilatedMetric hg₂ lam
  have hEq₁ : affineChartMetric G₁ (c,s) = affineChartMetric g₁ (φ (lam,(c,s))) :=
    affineChartMetric_dilatedMetric g₁ lam c s
  have hEq₂ : affineChartMetric G₂ (c,s) = affineChartMetric g₂ (φ (lam,(c,s))) :=
    affineChartMetric_dilatedMetric g₂ lam c s
  have hFref := hF.affineChart_pullback ((isOpen_lowerCross (normal := normal)) _ _) hG₁ hG₂ c s
  rw [hEq₁,hEq₂] at hFref
  have hcB : ‖c‖ ≤ B := by simpa only [mem_closedBall,dist_zero_right] using hc
  have hbounded (x : (X dim)) (hx : ‖x‖ ≤ 2) :
      affineChartMap c s x ∈ ball (0 : (X dim)) (B+2*s₁+1) := by
    rw [mem_ball,dist_zero_right]
    have hh := norm_affineChartMap_le c hspos.le x
    have hm := mul_le_mul hs.2 hx (norm_nonneg _) (hspos.le.trans hs.2)
    linarith
  have hLo₁ : closure (planeBall normal (planeDepth-δ)) ⊆ L := by
    intro x hx
    change affineChartMap c s x normal < -η
    rw [(affineChartMap_height (normal := normal)) hc₂]
    have hh := (height_le_of_mem_closure_planeBall (normal := normal)) hx
    have hxδ : x normal ≤ -δ := by linarith
    have h1 := mul_le_mul_of_nonneg_left hxδ hspos.le
    have h2 := mul_le_mul_of_nonneg_left hs.1 hδ.le
    nlinarith only [h1,h2,hη]
  have hLo₂ : closure (planeAnnulusObservation normal) ⊆ L := by
    intro x hx
    change affineChartMap c s x normal < -η
    rw [(affineChartMap_height (normal := normal)) hc₂]
    have hxδ : x normal ≤ -δ := by
      have hh := (height_le_of_mem_closure_planeAnnulusObservation (normal := normal)) hx
      norm_num [planeDepth] at hδcap
      linarith
    have h1 := mul_le_mul_of_nonneg_left hxδ hspos.le
    have h2 := mul_le_mul_of_nonneg_left hs.1 hδ.le
    nlinarith only [h1,h2,hη]
  have hV (x y : (X dim)) (hx : x ∈ closure (planeBall normal (3*planeDepth)))
      (hy : y ∈ closure (planeAnnulus (dim := dim))) (hL : y ∈ L ∨ x ∈ L) : (x,y) ∈ V := by
    have hxmin := (norm_le_of_mem_closure_planeBall (normal := normal)) hx
    have hxy : x ≠ y := by
      intro he
      rw [he] at hxmin
      have hylo := (norm_bounds_mem_closure_planeAnnulus hy).1
      norm_num [planeDepth] at hxmin
      linarith
    refine ⟨⟨hbounded x (by norm_num [planeDepth] at hxmin; linarith),
      hbounded y (norm_bounds_mem_closure_planeAnnulus hy).2,?_⟩,hL⟩
    intro he
    exact hxy ((affineChartMap_inverse c hspos.ne' x).symm.trans
      ((congrArg (affineChartMap (-(s⁻¹ • c)) s⁻¹) he).trans (affineChartMap_inverse c hspos.ne' y)))
  have hD₂Obs : closure (planeAnnulusObservation normal) ⊆ closure (planeAnnulus (dim := dim)) :=
    (closure_planeAnnulusObservation_subset (normal := normal)).trans subset_closure
  have hD₁Obs : closure (planeBall normal (planeDepth-δ)) ⊆ closure (planeBall normal (3*planeDepth)) :=
    ((closure_planeBall_obs_subset (normal := normal)) hδ).trans subset_closure
  have hD₁Out : planeBall normal (planeDepth+δ) ⊆ closure (planeBall normal (3*planeDepth)) :=
    hO₁.trans subset_closure
  have hD₂Out : (planeAnnulusOutput (dim := dim)) ⊆ closure (planeAnnulus (dim := dim)) := (planeAnnulusOutput_subset (dim := dim)).trans subset_closure
  obtain ⟨G,hG,hEqLeft,hEqRight⟩ := (exists_referencePlane_productSolution (normal := normal))
    (e g₁ hg₁ (φ (lam,(c,s)))) (e g₂ hg₂ (φ (lam,(c,s)))) hδ hδcap hC₁.le hC₂.le hγ₂ hγ₂'.le
    (by linarith) hO₁ hI₁ hI₂ hFref
    (fun q hq => hV q.1 q.2 hq.1 (hD₂Obs hq.2) (Or.inl (hLo₂ hq.2)))
    (fun q hq => hV q.1 q.2 (hD₁Obs hq.1) hq.2 (Or.inr (hLo₁ hq.1)))
    (fun q hq => hV q.1 q.2 (hD₁Out hq.1) (hD₂Out hq.2.1) (Or.inl hq.2.2))
    (fun q hq => hV q.1 q.2 (hD₁Out hq.1.1) (hD₂Out hq.2) (Or.inr hq.1.2))
  have hGRef := hG
  rw [← hEq₁,← hEq₂] at hG
  have hOut : IsOpen (planeBall normal (planeDepth+δ) ×ˢ (planeAnnulusOutput (dim := dim))) :=
    isOpen_ball.prod (isOpen_openAnnulus 0 (4/5) (6/5))
  have hSol := ProductSolutionOn.affineChart_pushforward hOut hG₁ hG₂ hspos.ne' hG
  rw [(affineChartProduct_image_planeOutput (normal := normal)) c hspos δ] at hSol
  refine ⟨G ∘ Ai,hSol,?_,?_⟩
  · intro q hq
    have hImage := hq.1
    rw [← (affineChartProduct_image_planeOutput (normal := normal)) c hspos δ] at hImage
    obtain ⟨z,hz,rfl⟩ := hImage
    change G (Ai (A z)) = F (A z)
    rw [show Ai (A z) = z from affineChartProduct_inverse c hspos.ne' z]
    have hlo : min ((A z).1 normal) ((A z).2 normal) < -η := hq.2
    rcases min_lt_iff.mp hlo with hx | hy
    · exact hEqRight (show z ∈ (planeBall normal (planeDepth+δ) ∩ L) ×ˢ (planeAnnulusOutput (dim := dim)) from
        ⟨⟨hz.1,hx⟩,hz.2⟩)
    · exact hEqLeft (show z ∈ planeBall normal (planeDepth+δ) ×ˢ ((planeAnnulusOutput (dim := dim)) ∩ L) from
        ⟨hz.1,⟨hz.2,hy⟩⟩)
  · intro M hM hBound
    have hNorm (x y : (X dim)) (hX : x ∈ closure (planeBall normal (3*planeDepth)))
        (hY : y ∈ closure (planeAnnulus (dim := dim))) : a₀ ≤ ‖(A (x,y)).1-(A (x,y)).2‖ := by
      have hx := (norm_le_of_mem_closure_planeBall (normal := normal)) hX
      have hy := (norm_bounds_mem_closure_planeAnnulus hY).1
      have hdist : (3/8 : ℝ) ≤ ‖x-y‖ := by
        have h := norm_sub_le x (x-y)
        rw [sub_sub_cancel] at h
        norm_num [planeDepth] at hx
        linarith
      change a₀ ≤ ‖affineChartMap c s x-affineChartMap c s y‖
      rw [← dist_eq_norm,dist_affineChartMap c hspos.le,dist_eq_norm]
      calc
        a₀ ≤ s*(3/8) := by
          dsimp only [a₀]
          rw [mul_comm (3/8 : ℝ)]
          exact mul_le_mul_of_nonneg_right hs.1 (by norm_num)
        _ ≤ _ := mul_le_mul_of_nonneg_left hdist hspos.le
    have hBuf₁ : closure (planeBall normal (3*planeDepth)) ×ˢ closure (planeAnnulusObservation normal) ⊆ V :=
      fun q hq => hV q.1 q.2 hq.1 (hD₂Obs hq.2) (Or.inl (hLo₂ hq.2))
    have hBuf₂ : closure (planeBall normal (planeDepth-δ)) ×ˢ closure (planeAnnulus (dim := dim)) ⊆ V :=
      fun q hq => hV q.1 q.2 (hD₁Obs hq.1) hq.2 (Or.inr (hLo₁ hq.1))
    have hPt (x y : (X dim)) (hx : x ∈ closure (planeBall normal (3*planeDepth)))
        (hy : y ∈ closure (planeAnnulus (dim := dim))) (hxy : (x,y) ∈ V) :
        |(F ∘ A) (x,y)| ≤ M := hBound _ hxy (hNorm x y hx hy)
    obtain ⟨G',hG',hLeft',hG'bound⟩ := hQuant (c,s) ⟨hc,hs⟩ (F ∘ A) M hM
      (hFref.mono ((Set.prod_mono subset_closure subset_closure).trans hBuf₁))
      (hFref.mono ((Set.prod_mono subset_closure subset_closure).trans hBuf₂))
      (fun z hz => by
        rcases hz with hz | hz
        · exact hPt z.1 z.2 (subset_closure hz.1) (hD₂Obs (subset_closure hz.2))
            (hBuf₁ ⟨subset_closure hz.1,subset_closure hz.2⟩)
        · exact hPt z.1 z.2 (hD₁Obs (subset_closure hz.1)) (subset_closure hz.2)
            (hBuf₂ ⟨subset_closure hz.1,subset_closure hz.2⟩))
    have hOb : 0 < planeDepth+δ := by dsimp [planeDepth]; positivity
    have hAgree := product_eqOn_of_rectangle
      (A := planeBall normal (planeDepth+δ)) (B := (planeAnnulusOutput (dim := dim)))
      (A₀ := planeBall normal (planeDepth+δ)) (B₀ := (planeAnnulusObservation normal))
      isOpen_ball (isConnected_ball hOb) (isOpen_openAnnulus _ _ _)
      (isConnected_openAnnulus 0 (4/5) (6/5) (by norm_num) (by norm_num))
      isOpen_ball isOpen_ball (nonempty_ball.mpr hOb) (nonempty_ball.mpr (by norm_num))
      Subset.rfl (planeAnnulusObservation_subset_output (normal := normal))
      (smoothMetric_restrict (e g₁ hg₁ (φ (lam,(c,s)))) (subset_univ _))
      (smoothMetric_restrict (e g₂ hg₂ (φ (lam,(c,s)))) (subset_univ _))
      hG' hGRef
      (fun z hz => (hLeft' hz).trans ((hEqLeft
        ⟨hz.1,(planeAnnulusObservation_subset_output (normal := normal)) hz.2,hLo₂ (subset_closure hz.2)⟩)).symm)
    intro q hq
    have hp := (retainedPatch_subset_coarsePatch (normal := normal)) c hspos (half_lt_self hδ).le hq
    rw [← (affineChartProduct_image_planeOutput (normal := normal)) c hspos δ] at hp
    obtain ⟨z,hz,rfl⟩ := hp
    have hDist (x : (X dim)) : dist (affineChartMap c s x) c = s*‖x‖ := by
      have hzero : affineChartMap c s 0 = c := by simp [affineChartMap]
      calc
        dist (affineChartMap c s x) c = dist (affineChartMap c s x) (affineChartMap c s 0) :=
          congrArg (dist (affineChartMap c s x)) hzero.symm
        _ = s*‖x‖ := by rw [dist_affineChartMap c hspos.le,dist_zero_right]
    have hx : ‖z.1‖ < δ/2 := by
      have hb := mem_ball.mp hq.1
      change dist (affineChartMap c s z.1) c < (δ/2)*s at hb
      rw [hDist,mul_comm (δ/2)] at hb
      exact (mul_lt_mul_iff_right₀ hspos).mp hb
    have hy : z.2 ∈ closedAnnulus (0 : (X dim)) (9/10) (11/10) := by
      have hb : 9*s/10 < dist (affineChartMap c s z.2) c ∧
        dist (affineChartMap c s z.2) c < 11*s/10 := hq.2
      rw [hDist,show 9*s/10 = s*(9/10) by ring,show 11*s/10 = s*(11/10) by ring] at hb
      rw [mem_closedAnnulus,sub_zero]
      exact ⟨((mul_lt_mul_iff_right₀ hspos).mp hb.1).le,((mul_lt_mul_iff_right₀ hspos).mp hb.2).le⟩
    change |G (Ai (A z))| ≤ _
    rw [show Ai (A z) = z from affineChartProduct_inverse c hspos.ne' z,← hAgree hz]
    exact (hG'bound z ⟨mem_closedBall_zero_iff.mpr hx.le,hy⟩)

set_option maxHeartbeats 1000000 in
/-- The normalizations of all bounded planar anchors and positive
separation scales enter the same parameter neighborhood. The patch
extends the actual lower cross and agrees on both of its lower slices. -/
theorem exists_uniform_coarsePatch
    {g₁ g₂ : (MetricField dim)} (hg₁ : SmoothMetric univ g₁) (hg₂ : SmoothMetric univ g₂)
    (h₁ : g₁ 0 = 1) (h₂ : g₂ 0 = 1) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ planeDepth/100 ∧
    ∀ B s₀ s₁ : ℝ, 0 < s₀ → s₀ ≤ s₁ →
      ∀ᶠ lam in 𝓝 (0 : ℝ), ∀ c ∈ closedBall (0 : (X dim)) B, c normal = 0 → ∀ s ∈ Icc s₀ s₁,
      ∀ η < δ*s₀, ∀ F : (X dim) × (X dim) → ℝ,
        ProductSolutionOn (dilatedMetric g₁ lam) (dilatedMetric g₂ lam) (lowerCross normal (B+2*s₁+1) η) F →
        ∃ G, ProductSolutionOn (dilatedMetric g₁ lam) (dilatedMetric g₂ lam) (coarsePatch normal c s δ) G ∧
          EqOn G F ((coarsePatch normal c s δ) ∩ {q | min (q.1 normal) (q.2 normal) < -η}) := by
  obtain ⟨δ,hδ,hδcap,h⟩ := (exists_uniform_coarsePatch_with_bound (normal := normal)) hg₁ hg₂ h₁ h₂
  refine ⟨δ,hδ,hδcap,fun B s₀ s₁ h₀ h₁ => ?_⟩
  obtain ⟨_,_,h⟩ := h B s₀ s₁ h₀ h₁
  exact h.mono fun lam h c hc hc' s hs η hη F hf => by
    obtain ⟨G,hG,hEq,_⟩ := h c hc hc' s hs η hη F hf
    exact ⟨G,hG,hEq⟩

end CalderonN.FixedTube
