module

public import Proof.CalderonN.ProfileBounds
public import Proof.CalderonN.Coercivity
public import Proof.CalderonN.SmoothMetricFrame
public import Proof.CalderonN.DilationHarmonic

import Proof.CalderonN.BackgroundBounds
import Proof.CalderonN.FixedTube.DilatedGeometry
import Proof.CalderonN.NormalCoordinates
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic

public section

noncomputable section
open Set Filter
open scoped ContDiff Topology BigOperators

namespace CalderonN

variable {dim : ℕ} [NeZero dim]
variable {normal : I dim}

theorem NormalCoordinates.mono_centers {Y Y' Ω : Set (X dim)} {g : (MetricField dim)}
    {E : (X dim) × (X dim) → (X dim)} {r : (X dim) → ℝ} (h : NormalCoordinates Y Ω g E r) (hsub : Y' ⊆ Y) :
    NormalCoordinates Y' Ω g E r := by
  obtain ⟨⟨V, hV, hVsub, hsm⟩, hloc⟩ := h
  exact ⟨⟨V, hV, fun _ hq => hVsub ⟨hsub hq.1, hq.2⟩, hsm⟩, fun y hy => hloc y (hsub hy)⟩

private theorem Profile.weaken {Y Y' : Set (X dim)} {γ : (MetricField dim)} {e : (Frame dim)} {r : (X dim) → ℝ}
    {floor floor' c₀ : ℝ} {Cj : Fin 9 → ℝ} (h : Profile Y γ e r floor c₀ Cj)
    (hsub : Y' ⊆ Y) (hf : floor' ≤ floor) : Profile Y' γ e r floor' c₀ Cj := by
  refine ⟨h.1.mono hsub, fun y hy => ?_⟩
  obtain ⟨hr, hβ, hh, hj⟩ := h.2 y (hsub hy)
  exact ⟨hr, hf.trans hβ, hh, hj⟩

private theorem eventually_frame_bound {D : Set (X dim)} (hD : IsCompact D) {γ : ℝ → (MetricField dim)}
    (hγ : ∀ i j, ContDiff ℝ ∞ (fun q : ℝ × (X dim) => γ q.1 q.2 i j))
    (hpos : ∀ lam y, (γ lam y).PosDef) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam →
      ∀ y ∈ D, ∀ i j, |smoothMetricFrame (γ lam y) i j| ≤ A := by
  let S := Icc (-1 : ℝ) 1
  let T := S ×ˢ D
  have hT : IsCompact T := isCompact_Icc.prod hD
  have he (i j : (I dim)) : Continuous (fun q : ℝ × (X dim) => smoothMetricFrame (γ q.1 q.2) i j) := by
    have hFrame := contDiffOn_smoothMetricFrame (U := univ)
      (fun a b => (hγ a b).contDiffOn) (fun (q : ℝ × (X dim)) _ => hpos q.1 q.2) i
    exact (EuclideanSpace.proj j : (X dim) →L[ℝ] ℝ).continuous.comp
      (contDiffOn_univ.mp hFrame).continuous
  choose A hA using fun (i j : (I dim)) => hT.exists_bound_of_continuousOn (he i j).continuousOn
  let B : ℝ := ∑ i : (I dim), ∑ j : (I dim), max 0 (A i j)
  have hb : 0 ≤ B := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => le_max_left _ _
  have hle (i j : (I dim)) : A i j ≤ B :=
    (le_max_right _ _).trans ((Finset.single_le_sum (f := fun k => max 0 (A i k))
      (fun k _ => le_max_left 0 (A i k)) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun k : (I dim) => ∑ l : (I dim), max 0 (A k l))
        (fun _ _ => Finset.sum_nonneg fun _ _ => le_max_left _ _) (Finset.mem_univ i)))
  refine ⟨B, hb, ?_⟩
  have hnear : S ∈ 𝓝 (0 : ℝ) := Icc_mem_nhds (by norm_num) (by norm_num)
  filter_upwards [hnear] with lam hlam _ y hy i j
  exact (hA i j (lam,y) ⟨hlam,hy⟩).trans (hle i j)

/-- The actual sphere data after the fixed conformal normalization and dilation. -/
@[expose] def conformalSphereData (normal : I dim) (g₁ g₂ : (MetricField dim)) (E : ℝ → (X dim) × (X dim) → (X dim))
    (p : ℕ) (R lam δ : ℝ) (A : (TraceAdjoint dim)) : (Data dim) :=
  let γ := conformalReference (depthScale normal 4) g₁ lam
  ⟨γ, dilatedMetric g₁ lam, dilatedMetric g₂ lam, fun y => smoothMetricFrame (γ y),
    shrinkingRadius R p (conformalDepth normal 4) δ, E lam, A⟩

set_option maxHeartbeats 2200000 in
/-- Choose the coercivity parameters with a common normal tube on a larger
compact center set. The radius cap has room for a top collar. -/
theorem exists_uniform_conformalSphereData_on_centers
    (coercivity : (Coercivity dim)) (pmin : ℕ)
    (εmax : ℕ → ℝ) (Rmax : ℕ → ℝ → ℝ)
    (hεmax : ∀ p ≥ pmin, 0 < εmax p)
    (hRmax : ∀ p ≥ pmin, ∀ ε ∈ Ioc (0 : ℝ) (εmax p), 0 < Rmax p ε)
    {Y Ω D Z : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    (hYc : IsCompact (closure Y)) (hYZ : closure Y ⊆ Z)
    (hZ : IsCompact Z) (hZΩ : Z ⊆ Ω)
    (hD : IsCompact D) (hΩD : Ω ⊆ D)
    {g₁ g₂ : (MetricField dim)} (hg₁ : SmoothMetric univ g₁) (hg₂ : SmoothMetric univ g₂)
    (hunit : g₁ 0 = 1) :
    ∃ (p : ℕ) (R ε C ρ c₀ K floor ε₀ : ℝ) (m : ℕ)
      (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (E : ℝ → (X dim) × (X dim) → (X dim)),
      21 + dim ≤ p ∧ pmin ≤ p ∧ 0 < R ∧ R ≤ Rmax p ε ∧ 0 < ε ∧ ε ≤ εmax p ∧
      0 < C ∧ 0 < ρ ∧ 0 < K ∧ 1 ≤ floor ∧ ε ≤ ε₀ ∧
      UniformEstimate Y Ω K ρ c₀ M Cj floor ε₀ C ∧
      ContDiff ℝ ∞ (fun q : ℝ × ((X dim) × (X dim)) => E q.1 q.2) ∧
      (∀ lam ∈ Icc (-1 : ℝ) 1,
        NormalCoordinates Z Ω (conformalReference (depthScale normal 4) g₁ lam) (E lam) (fun _ => ρ)) ∧
      (∀ δ ∈ Ioc (0 : ℝ) 1, ∀ y ∈ Z, shrinkingRadius R p (conformalDepth normal 4) δ y ≤ ρ/2) ∧
      ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam → ∀ δ ∈ Ioc (0 : ℝ) 1, ∀ A : (TraceAdjoint dim),
        let d := conformalSphereData normal g₁ g₂ E p R lam δ A
        (∀ y ∈ Y, 0 < d.radius y ∧ d.radius y < ρ ∧ d.radius y * (beta d.γ d.radius y)^2 ≤ ε) ∧
        Background Ω K M d.γ d.g₁ d.g₂ d.frame ∧
        NormalCoordinates Y Ω d.γ d.expMap (fun _ => ρ) ∧
        Profile Y d.γ d.frame d.radius floor c₀ Cj := by
  let S := Icc (-1 : ℝ) 1
  let γ := conformalReference (depthScale normal 4) g₁
  let q₁ := dilatedMetric g₁
  let q₂ := dilatedMetric g₂
  have hγ (i j : (I dim)) : ContDiff ℝ ∞ (fun q : ℝ × (X dim) => γ q.1 q.2 i j) := by
    apply contDiffOn_univ.mp
    simpa only [mem_univ, ofPred_true] using
      contDiffOn_conformalReference_family_entry hg₁ (contDiff_depthScale (normal := normal) 4) i j
  have h₁ (i j : (I dim)) : ContDiff ℝ ∞ (fun q : ℝ × (X dim) => q₁ q.1 q.2 i j) :=
    (contDiffOn_univ.mp (hg₁.1 i j)).comp (contDiff_fst.smul contDiff_snd)
  have h₂ (i j : (I dim)) : ContDiff ℝ ∞ (fun q : ℝ × (X dim) => q₂ q.1 q.2 i j) :=
    (contDiffOn_univ.mp (hg₂.1 i j)).comp (contDiff_fst.smul contDiff_snd)
  have hp₁ (lam : ℝ) (y : (X dim)) : (q₁ lam y).PosDef := hg₁.2 _ (mem_univ _)
  have hp₂ (lam : ℝ) (y : (X dim)) : (q₂ lam y).PosDef := hg₂.2 _ (mem_univ _)
  have hpγ (lam : ℝ) (y : (X dim)) : (γ lam y).PosDef :=
    (hp₁ lam y).smul (depthScale_pos 4 y)
  obtain ⟨m, hCoer⟩ := coercivity Y Ω hY hΩ hYc (hYZ.trans hZΩ)
  obtain ⟨K, hK, M, hbackground⟩ := exists_uniform_background (S := S) isCompact_Icc hD hΩD
    hγ h₁ h₂ hpγ hp₁ hp₂ (fun _ _ y _ => ⟨depthScale normal 4 y, depthScale_pos 4 y, rfl⟩) m
  obtain ⟨ρ, E, hρ, hE, hnormal⟩ := exists_uniform_normalCoordinates hγ hpγ hZ hΩ hZΩ
    (S := S) isCompact_Icc
  obtain ⟨F, hF, hf⟩ := eventually_frame_bound hYc hγ hpγ
  let e (lam : ℝ) (y : (X dim)) := smoothMetricFrame (γ lam y)
  obtain ⟨c, c₀, B, T, hc, hc₀, hB, Cj, hprofile⟩ :=
    exists_conformal_shrinkingRadius_profile hYc hg₁ hunit e hF hf
  obtain ⟨floor, ε₀, C, _hfloor, hε₀, hC, hEst⟩ := hCoer K ρ c₀ M Cj hK hρ hc₀
  obtain ⟨p, hp⟩ := exists_nat_gt (max (max (21 + (dim : ℝ)) (pmin : ℝ)) (floor / c))
  have hp24 : 21 + dim ≤ p := by
    exact_mod_cast ((le_max_left (21 + (dim : ℝ)) (pmin : ℝ)).trans (le_max_left _ _)).trans hp.le
  have hpmin : pmin ≤ p := by
    exact_mod_cast ((le_max_right (21 + (dim : ℝ)) (pmin : ℝ)).trans (le_max_left _ _)).trans hp.le
  have hp₂ : 2 ≤ p := by omega
  have hfc : floor ≤ c * p := by
    have h := (le_max_right (max (21 + (dim : ℝ)) (pmin : ℝ)) (floor / c)).trans hp.le
    simpa only [mul_comm] using (div_le_iff₀ hc).mp h
  let ε := min (ε₀ / 2) (εmax p)
  have hε : 0 < ε := lt_min (half_pos hε₀) (hεmax p hpmin)
  have hεcap : ε ≤ εmax p := min_le_right _ _
  have hε' : ε ≤ ε₀ := (min_le_left _ _).trans (half_lt_self hε₀).le
  obtain ⟨U, hU⟩ := hZ.exists_bound_of_continuousOn (contDiff_conformalDepth (normal := normal) 4).continuous.continuousOn
  let L := Real.log (1 + Real.exp U)
  let radiusProfileBound := (p : ℝ)^2 * B^2 * (Real.log (1 + Real.exp T))^(p-2)
  have hL : 0 < L := Real.log_pos (by linarith [Real.exp_pos U])
  have hRadiusProfileBound : 0 < radiusProfileBound := by
    have ht : 0 < Real.log (1 + Real.exp T) := Real.log_pos (by linarith [Real.exp_pos T])
    have hp' : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
    dsimp only [radiusProfileBound]
    positivity
  let R := min (min ((ρ/2) / L^p) (ε / radiusProfileBound)) (Rmax p ε)
  have hR : 0 < R := lt_min (lt_min (div_pos (half_pos hρ) (pow_pos hL _)) (div_pos hε hRadiusProfileBound))
    (hRmax p hpmin ε ⟨hε,hεcap⟩)
  have hRL : R * L^p ≤ ρ/2 := (le_div_iff₀ (pow_pos hL _)).mp
    ((min_le_left _ _).trans (min_le_left _ _))
  have hRZ : R * radiusProfileBound ≤ ε := (le_div_iff₀ hRadiusProfileBound).mp ((min_le_left _ _).trans (min_le_right _ _))
  have hradCap (δ : ℝ) (hδ : δ ∈ Ioc (0 : ℝ) 1) (y : (X dim)) (hy : y ∈ Z) :
      shrinkingRadius R p (conformalDepth normal 4) δ y ≤ ρ/2 := by
    have ht : conformalDepth normal 4 y ≤ U := (le_abs_self _).trans (hU y hy)
    have hs : softplus δ (conformalDepth normal 4 y) ≤ L := by
      have hm := (strictMonoOn_softplus_scale (conformalDepth normal 4 y)).monotoneOn
        hδ.1 zero_lt_one hδ.2
      refine hm.trans ?_
      simp only [softplus, div_one, one_mul, L]
      exact Real.log_le_log (by positivity) (by linarith [Real.exp_le_exp.mpr ht])
    exact ((mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (softplus_pos hδ.1 _).le hs p) hR.le).trans hRL)
  refine ⟨p,R,ε,C,ρ,c₀,K,floor,ε₀,m,M,Cj,E,hp24,hpmin,hR,min_le_right _ _,hε,
    hεcap,hC,hρ,zero_lt_one.trans_le hK,_hfloor,hε',hEst,hE,hnormal,hradCap,?_⟩
  have hS : S ∈ 𝓝 (0 : ℝ) := Icc_mem_nhds (by norm_num) (by norm_num)
  filter_upwards [hS, hprofile] with lam hlam hpr hpos δ hδ A
  let d := conformalSphereData normal g₁ g₂ E p R lam δ A
  obtain ⟨hpr', hβ⟩ := hpr hpos δ hδ hp₂ R hR
  have hβ' (y : (X dim)) (hy : y ∈ Y) : d.radius y * (beta d.γ d.radius y)^2 ≤ ε :=
    (hβ y (subset_closure hy)).trans (by
      have he : R * (p : ℝ)^2 * B^2 * Real.log (1 + Real.exp T)^(p-2) = R * radiusProfileBound := by
        dsimp only [radiusProfileBound]
        ring
      rw [he]
      exact hRZ)
  have hr (y : (X dim)) (hy : y ∈ Y) : d.radius y < ρ :=
    (hradCap δ hδ y (hYZ (subset_closure hy))).trans_lt (half_lt_self hρ)
  have hProfile : Profile Y d.γ d.frame d.radius floor c₀ Cj := hpr'.weaken subset_closure hfc
  have hNor : NormalCoordinates Y Ω d.γ d.expMap (fun _ => ρ) :=
    (hnormal lam hlam).mono_centers (subset_closure.trans hYZ)
  exact ⟨fun y hy => ⟨(hProfile.2 y hy).1,hr y hy,hβ' y hy⟩,hbackground lam hlam,hNor,hProfile⟩

/-- The coercivity parameters can be chosen in the order required by the
manuscript. The remaining premises are the actual Dirichlet solution,
trace adjoint, and small tensor bound. -/
theorem exists_uniform_conformalSphereData_with_limits
    (coercivity : (Coercivity dim)) (pmin : ℕ)
    (εmax : ℕ → ℝ) (Rmax : ℕ → ℝ → ℝ)
    (hεmax : ∀ p ≥ pmin, 0 < εmax p)
    (hRmax : ∀ p ≥ pmin, ∀ ε ∈ Ioc (0 : ℝ) (εmax p), 0 < Rmax p ε)
    {Y Ω D : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    (hYc : IsCompact (closure Y)) (hYΩ : closure Y ⊆ Ω)
    (hD : IsCompact D) (hΩD : Ω ⊆ D)
    {g₁ g₂ : (MetricField dim)} (hg₁ : SmoothMetric univ g₁) (hg₂ : SmoothMetric univ g₂)
    (hunit : g₁ 0 = 1) :
    ∃ (p : ℕ) (R ε C ρ c₀ K floor ε₀ : ℝ) (m : ℕ)
      (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (E : ℝ → (X dim) × (X dim) → (X dim)),
      21 + dim ≤ p ∧ pmin ≤ p ∧ 0 < R ∧ R ≤ Rmax p ε ∧ 0 < ε ∧ ε ≤ εmax p ∧ 0 < C ∧ 0 < ρ ∧ 1 ≤ floor ∧ ε ≤ ε₀ ∧
      UniformEstimate Y Ω K ρ c₀ M Cj floor ε₀ C ∧
      ContDiff ℝ ∞ (fun q : ℝ × ((X dim) × (X dim)) => E q.1 q.2) ∧
      ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam → ∀ δ ∈ Ioc (0 : ℝ) 1, ∀ A : (TraceAdjoint dim),
        let d := conformalSphereData normal g₁ g₂ E p R lam δ A
        (∀ y ∈ Y, 0 < d.radius y ∧ d.radius y < ρ ∧ d.radius y * (beta d.γ d.radius y)^2 ≤ ε) ∧
        Background Ω K M d.γ d.g₁ d.g₂ d.frame ∧
        NormalCoordinates Y Ω d.γ d.expMap (fun _ => ρ) ∧
        Profile Y d.γ d.frame d.radius floor c₀ Cj := by
  obtain ⟨p,R,ε,C,ρ,c₀,K,floor,ε₀,m,M,Cj,E,hp,hpmin,hR,hRmax',hε,hεmax',hC,hρ,_,hfloor,
      hε₀,hEst,hE,_,_,hData⟩ :=
    exists_uniform_conformalSphereData_on_centers coercivity pmin εmax Rmax hεmax hRmax
      hY hΩ hYc (Subset.rfl) hYc hYΩ hD hΩD hg₁ hg₂ hunit
  exact ⟨p,R,ε,C,ρ,c₀,K,floor,ε₀,m,M,Cj,E,hp,hpmin,hR,hRmax',hε,hεmax',hC,hρ,hfloor,
    hε₀,hEst,hE,hData⟩

/-- The coercivity parameters can be chosen in the order required by the
manuscript. The remaining premises are the actual Dirichlet solution,
trace adjoint, and small tensor bound. -/
theorem exists_uniform_conformalSphereData
    (coercivity : (Coercivity dim))
    {Y Ω D : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    (hYc : IsCompact (closure Y)) (hYΩ : closure Y ⊆ Ω)
    (hD : IsCompact D) (hΩD : Ω ⊆ D)
    {g₁ g₂ : (MetricField dim)} (hg₁ : SmoothMetric univ g₁) (hg₂ : SmoothMetric univ g₂)
    (hunit : g₁ 0 = 1) :
    ∃ (p : ℕ) (R ε C ρ c₀ K floor ε₀ : ℝ) (m : ℕ)
      (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (E : ℝ → (X dim) × (X dim) → (X dim)),
      21 + dim ≤ p ∧ 0 < R ∧ 0 < ε ∧ 0 < C ∧ 0 < ρ ∧ 1 ≤ floor ∧ ε ≤ ε₀ ∧
      UniformEstimate Y Ω K ρ c₀ M Cj floor ε₀ C ∧
      ContDiff ℝ ∞ (fun q : ℝ × ((X dim) × (X dim)) => E q.1 q.2) ∧
      ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam → ∀ δ ∈ Ioc (0 : ℝ) 1, ∀ A : (TraceAdjoint dim),
        let d := conformalSphereData normal g₁ g₂ E p R lam δ A
        (∀ y ∈ Y, 0 < d.radius y ∧ d.radius y < ρ ∧ d.radius y * (beta d.γ d.radius y)^2 ≤ ε) ∧
        Background Ω K M d.γ d.g₁ d.g₂ d.frame ∧
        NormalCoordinates Y Ω d.γ d.expMap (fun _ => ρ) ∧
        Profile Y d.γ d.frame d.radius floor c₀ Cj := by
  obtain ⟨p,R,ε,C,ρ,c₀,K,floor,ε₀,m,M,Cj,E,hp,_,hR,_,hε,_,hC,hρ,hfloor,hε₀,hEst,hE,hData⟩ :=
    exists_uniform_conformalSphereData_with_limits coercivity 24 (fun _ => 1) (fun _ _ => 1)
      (fun _ _ => one_pos) (fun _ _ _ _ => one_pos)
      hY hΩ hYc hYΩ hD hΩD hg₁ hg₂ hunit
  exact ⟨p,R,ε,C,ρ,c₀,K,floor,ε₀,m,M,Cj,E,hp,hR,hε,hC,hρ,hfloor,hε₀,hEst,hE,hData⟩

theorem NormalCoordinates.max_radius_of_le {Y Ω : Set (X dim)} {γ : (MetricField dim)} {E : (X dim) × (X dim) → (X dim)}
    {ρ : ℝ} {r : (X dim) → ℝ} (hN : NormalCoordinates Y Ω γ E (fun _ => ρ))
    (hr : ∀ y ∈ Y, r y ≤ ρ) :
    NormalCoordinates Y Ω γ E (fun y => max ρ (r y)) := by
  obtain ⟨⟨V,hV,hS,hSmooth⟩,hLoc⟩ := hN
  refine ⟨⟨V,hV,fun q hq => hS ?_,hSmooth⟩,fun y hy => ?_⟩
  · have h := hq.2
    change q.2 ∈ disk γ q.1 (max ρ (r q.1)) at h
    rw [max_eq_left (hr q.1 hq.1)] at h
    exact ⟨hq.1,h⟩
  · have he : max ρ (r y) = ρ := max_eq_left (hr y hy)
    dsimp only
    rw [he]
    exact hLoc y hy

/-- At the literal normalized sphere data, supplying the two boundary
operators and the small tensor bound gives the protected estimate. -/
theorem exists_uniform_conformalSphereCoercivity
    (coercivity : (Coercivity dim))
    {Y Ω D : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    (hYc : IsCompact (closure Y)) (hYΩ : closure Y ⊆ Ω)
    (hD : IsCompact D) (hΩD : Ω ⊆ D)
    {g₁ g₂ : (MetricField dim)} (hg₁ : SmoothMetric univ g₁) (hg₂ : SmoothMetric univ g₂)
    (hunit : g₁ 0 = 1) :
    ∃ (p : ℕ) (R ε C : ℝ) (E : ℝ → (X dim) × (X dim) → (X dim)),
      21 + dim ≤ p ∧ 0 < R ∧ 0 < ε ∧ 0 < C ∧
      ContDiff ℝ ∞ (fun q : ℝ × ((X dim) × (X dim)) => E q.1 q.2) ∧
      ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam → ∀ δ ∈ Ioc (0 : ℝ) 1, ∀ A : (TraceAdjoint dim),
        let d := conformalSphereData normal g₁ g₂ E p R lam δ A
        (∀ y ∈ Y, d.radius y * (beta d.γ d.radius y)^2 ≤ ε) ∧
        (Dirichlet Y d.γ d.g₁ d.expMap d.radius →
          IsMovingTraceAdjoint Y d.γ d.g₁ d.frame d.expMap d.radius d.adjoint →
          Small Y d.γ d.g₂ d.radius ε →
          ∀ φ, Test Y d.γ d.frame φ → energyNorm Y d φ ≤ C * traceNorm Y d φ) := by
  obtain ⟨p,R,ε,C,ρ,c₀,K,floor,ε₀,m,M,Cj,E,hp,hR,hε,hC,hρ,hfloor,hε₀,hEst,hE,hData⟩ :=
    exists_uniform_conformalSphereData coercivity hY hΩ hYc hYΩ hD hΩD hg₁ hg₂ hunit
  refine ⟨p,R,ε,C,E,hp,hR,hε,hC,hE,?_⟩
  filter_upwards [hData] with lam hlam hlampos δ hδ A
  let d := conformalSphereData normal g₁ g₂ E p R lam δ A
  obtain ⟨hRadius,hBack,hNor,hProfile⟩ := hlam hlampos δ hδ A
  refine ⟨fun y hy => (hRadius y hy).2.2,fun hDir hAdj hSmall => ?_⟩
  have hNor' : NormalCoordinates Y Ω d.γ d.expMap (fun y => max ρ (d.radius y)) :=
    hNor.max_radius_of_le (fun y hy => (hRadius y hy).2.1.le)
  exact hEst d ε hε.le hε₀ ⟨hBack,hNor',hDir,hAdj,hProfile,hSmall⟩

end CalderonN
