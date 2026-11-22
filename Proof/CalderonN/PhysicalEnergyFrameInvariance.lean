module

public import Proof.CalderonN.PhysicalFrameInvariance

import Proof.CalderonN.PhysicalAngularModelData
import Proof.CalderonN.SmoothBesselSections
import Proof.CalderonN.SmoothSphereTrace
import Proof.CalderonN.SmoothBoundaryHilbert
import Proof.CalderonN.MetricConnection
import Mathlib.Tactic

/-! The horizontal covector is contracted in an orthonormal frame, also
after each spectral weight. Hence changing frame preserves the exact
four-term energy for every frozen test. -/

public section

noncomputable section
open Set MeasureTheory
open scoped ContDiff InnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 4700000
set_option maxSynthPendingDepth 24
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet OAI.AnisotropicCalderon SmoothSphereFields SphereHarmonic
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

private theorem smoothTrace_sobolevSq_components (hn : 3 ≤ dim) (g : MetricField dim) (y : X dim) (e : Frame dim)
    (he : ∀ i j, metricPair g y (e y i) (e y j) = if i=j then 1 else 0)
    (u : X dim → ℂ) (R J : SmoothData dim)
    (hR : ∀ z : UnitSphere dim, R.1 z = (u (frameVector e y z)).re)
    (hJ : ∀ z : UnitSphere dim, J.1 z = (u (frameVector e y z)).im)
    (s : ℝ) (hs : s ≤ 2) :
    sobolevSq g e s y u =
      ‖smoothSphereTraceSobolev hn s hs (smoothSphereTrace R)‖^2+
        ‖smoothSphereTraceSobolev hn s hs (smoothSphereTrace J)‖^2 := by
  let BR := ambientBesselField hn s hs (R.1 ∘ Prod.snd) (R.2.comp contDiff_snd) 0
  let BJ := ambientBesselField hn s hs (J.1 ∘ Prod.snd) (J.2.comp contDiff_snd) 0
  have hr := (smoothSphereLift_ae R.1 R.2).trans (Filter.Eventually.of_forall hR)
  have hj := (smoothSphereLift_ae J.1 J.2).trans (Filter.Eventually.of_forall hJ)
  have hBr : ∀ k, harmonicProjection k BR = besselWeight s k • harmonicProjection k (smoothSphereLift R.1 R.2) := by
    intro k
    simp only [BR,ambientBesselField_projection,ambientSphereL2_eq_smoothSphereLift]
    rfl
  have hBj : ∀ k, harmonicProjection k BJ = besselWeight s k • harmonicProjection k (smoothSphereLift J.1 J.2) := by
    intro k
    simp only [BJ,ambientBesselField_projection,ambientSphereL2_eq_smoothSphereLift]
    rfl
  rw [sobolevSq_eq_bessel_components hn g e y he _ _ _ _ _ hr hj s hBr hBj,
    smoothSphereTraceSobolev_apply,smoothSphereTraceSobolev_apply]
  have hEq (U : SmoothData dim) (B : SphereL2 dim)
      (hB : ∀ k, harmonicProjection k B = besselWeight s k • harmonicProjection k (smoothSphereLift U.1 U.2)) :
      smoothBoundarySobolev hn s hs U = sphereHarmonicDecomposition B := by
    apply lp.ext
    funext k
    rw [smoothBoundarySobolev_apply,sphereHarmonicDecomposition_apply,hB]
  rw [hEq R BR hBr,hEq J BJ hBj]
  simp only [LinearIsometryEquiv.norm_map]

private theorem smoothTrace_fiberSq_components (hn : 3 ≤ dim) (e : Frame dim) (y : X dim)
    (u : X dim → ℂ) (R J : SmoothData dim)
    (hR : ∀ z : UnitSphere dim, R.1 z = (u (frameVector e y z)).re)
    (hJ : ∀ z : UnitSphere dim, J.1 z = (u (frameVector e y z)).im) :
    fiberSq e y u =
      ‖smoothSphereTraceL2 hn (smoothSphereTrace R)‖^2+‖smoothSphereTraceL2 hn (smoothSphereTrace J)‖^2 := by
  rw [smoothSphereTraceL2_apply,smoothSphereTraceL2_apply]
  exact fiberSq_eq_component_norms e y u _ _
    ((smoothSphereLift_ae R.1 R.2).trans (Filter.Eventually.of_forall hR))
    ((smoothSphereLift_ae J.1 J.2).trans (Filter.Eventually.of_forall hJ))

private theorem horizontal_frameChange (g : MetricField dim) (p : Field dim) (y w : X dim) (e f : Frame dim)
    (he : ∀ i j, metricPair g y (e y i) (e y j) = if i=j then 1 else 0) (a : I dim) :
    horizontal g p y w (f y a) = ∑ i, frameChange g y e f a i • horizontal g p y w (e y i) := by
  let L := (fderiv ℝ p (y,w)).comp
    ((ContinuousLinearMap.id ℝ (X dim)).prod (-(connectionBilinear g y).flip w))
  have hL (v : X dim) : L v = horizontal g p y w v := by
    simp only [L,ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,ContinuousLinearMap.id_apply,
      ContinuousLinearMap.neg_apply,ContinuousLinearMap.flip_apply,connectionBilinear_apply,horizontal]
  simp_rw [← hL,← map_smul,← map_sum]
  exact congrArg L (frameChange_reconstruct g y e f he a)

private theorem horizontal_frame_contraction (hn : 3 ≤ dim) (g : MetricField dim)
    (p : Field dim) (y : X dim) (e f : Frame dim)
    (he : ∀ i j, metricPair g y (e y i) (e y j) = if i=j then 1 else 0)
    (hf : ∀ i j, metricPair g y (f y i) (f y j) = if i=j then 1 else 0)
    (hSym : (g y).transpose = g y)
    (R J : I dim → SmoothData dim)
    (hR : ∀ i (z : UnitSphere dim),
      (R i).1 z = (horizontal g p y (frameVector e y z) (e y i)).re)
    (hJ : ∀ i (z : UnitSphere dim),
      (J i).1 z = (horizontal g p y (frameVector e y z) (e y i)).im) :
    ((∑ a, fiberSq f y (fun w => horizontal g p y w (f y a))) =
      ∑ i, fiberSq e y (fun w => horizontal g p y w (e y i))) ∧
    ∀ s ≤ 2, (∑ a, sobolevSq g f s y (fun w => horizontal g p y w (f y a))) =
      ∑ i, sobolevSq g e s y (fun w => horizontal g p y w (e y i)) := by
  let c := frameChange g y e f
  let V₀ (U : I dim → SmoothData dim) (a : I dim) : smoothBallDataSubmodule dim :=
    ∑ i, c a i • (⟨(U i).1,(U i).2⟩ : smoothBallDataSubmodule dim)
  let V (U : I dim → SmoothData dim) (a : I dim) : SmoothData dim :=
    ⟨(V₀ U a).1,smoothBallData_contDiff (V₀ U a)⟩
  have hLinear (U : I dim → SmoothData dim) (a : I dim) :
      smoothSphereTrace (V U a) = ∑ i, c a i • smoothSphereTrace (U i) := by
    change smoothSphereTraceL dim (V₀ U a) = _
    simp only [V₀,map_sum,map_smul]
    rfl
  have hV (U : I dim → SmoothData dim) (a : I dim) (z : UnitSphere dim) :
      (V U a).1 z = ∑ i, c a i*(U i).1 z := by
    have h := congrArg (fun u : SmoothSphereTrace dim => u.1 z) (hLinear U a)
    simpa only [smoothSphereTrace_apply,Submodule.coe_sum,Finset.sum_apply,Submodule.coe_smul,Pi.smul_apply,smul_eq_mul] using h
  have hVR (a : I dim) (z : UnitSphere dim) :
      (V R a).1 z = (horizontal g p y (frameVector e y z) (f y a)).re := by
    rw [hV,horizontal_frameChange g p y _ e f he a]
    change (∑ i, c a i*(R i).1 z) = Complex.reCLM (∑ i, c a i • horizontal g p y (frameVector e y z) (e y i))
    rw [map_sum]
    simp only [map_smul,Complex.reCLM_apply,smul_eq_mul,hR]
  have hVJ (a : I dim) (z : UnitSphere dim) :
      (V J a).1 z = (horizontal g p y (frameVector e y z) (f y a)).im := by
    rw [hV,horizontal_frameChange g p y _ e f he a]
    change (∑ i, c a i*(J i).1 z) = Complex.imCLM (∑ i, c a i • horizontal g p y (frameVector e y z) (e y i))
    rw [map_sum]
    simp only [map_smul,Complex.imCLM_apply,smul_eq_mul,hJ]
  have hOrth := frameChange_columns_orthogonal g y e f he hf hSym
  have hNorms {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      (L : SmoothSphereTrace dim →ₗ[ℝ] E) (U : I dim → SmoothData dim) :
      (∑ a, ‖L (smoothSphereTrace (V U a))‖^2) = ∑ i, ‖L (smoothSphereTrace (U i))‖^2 := by
    simp_rw [hLinear,map_sum,map_smul]
    exact sum_norm_sq_of_orthogonal_matrix c hOrth _
  let H (e : Frame dim) (i : I dim) (w : X dim) := horizontal g p y w (e y i)
  change (∑ a, fiberSq f y (H f a)) = (∑ i, fiberSq e y (H e i)) ∧
    ∀ s ≤ 2, (∑ a, sobolevSq g f s y (H f a)) = ∑ i, sobolevSq g e s y (H e i)
  constructor
  · simp_rw [fiberSq_eq_of_orthonormalFrames g y e f he hf,
      fun a => smoothTrace_fiberSq_components hn e y (H f a) (V R a) (V J a) (hVR a) (hVJ a),
      fun i => smoothTrace_fiberSq_components hn e y (H e i) (R i) (J i) (hR i) (hJ i),
      Finset.sum_add_distrib,hNorms]
  · intro s hs
    simp_rw [sobolevSq_eq_of_orthonormalFrames g y e f he hf,
      fun a => smoothTrace_sobolevSq_components hn g y e he (H f a) (V R a) (V J a) (hVR a) (hVJ a) s hs,
      fun i => smoothTrace_sobolevSq_components hn g y e he (H e i) (R i) (J i) (hR i) (hJ i) s hs,
      Finset.sum_add_distrib,hNorms]

theorem energySq_eq_of_orthonormalFrames (hn : 3 ≤ dim) {Y : Set (X dim)} (hY : IsOpen Y)
    {K : ℝ} {g : MetricField dim} (hE : Elliptic Y K g) (hK : 0 < K) {e f : Frame dim}
    (heS : ∀ i, ContDiffOn ℝ ∞ (fun y => e y i) Y)
    (he : ∀ y ∈ Y, ∀ i j, metricPair g y (e y i) (e y j) = if i=j then 1 else 0)
    (hf : ∀ y ∈ Y, ∀ i j, metricPair g y (f y i) (f y j) = if i=j then 1 else 0)
    (r : X dim → ℝ) {φ : Field dim} (hφ : Test Y g e φ) :
    energySq Y g f r φ = energySq Y g e r φ := by
  obtain ⟨E⟩ := hφ.exists_harmonicTestExpansion hn hY e heS he
  choose R hR hr _ using fun i => E.exists_horizontal_component_representative hY hE hK heS he hφ.1 i Complex.reCLM
  choose J hJ hj _ using fun i => E.exists_horizontal_component_representative hY hE hK heS he hφ.1 i Complex.imCLM
  unfold energySq
  apply setIntegral_congr_fun hY.measurableSet
  intro y hy
  let R₀ (i : I dim) : SmoothData dim := ⟨fun z => R i (y,z),(hR i).comp (contDiff_const.prodMk contDiff_id)⟩
  let J₀ (i : I dim) : SmoothData dim := ⟨fun z => J i (y,z),(hJ i).comp (contDiff_const.prodMk contDiff_id)⟩
  obtain ⟨h₀,h₁⟩ := horizontal_frame_contraction hn g φ y e f (he y hy) (hf y hy) (hE.2 y hy).1
    R₀ J₀ (fun i z => hr i y hy z) (fun i z => hj i y hy z)
  dsimp only
  rw [h₀,h₁ (1/2:ℝ) (by norm_num)]
  simp_rw [sobolevSq_eq_of_orthonormalFrames g y e f (he y hy) (hf y hy)]

theorem uniformEstimate_of_canonicalFrames (hn : 3 ≤ dim)
    {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hsub : Y ⊆ Ω)
    {m : ℕ} (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 0 < K)
    (floor ε₀ C : ℝ)
    (hEstimate : ∀ (d : Data dim) (ε : ℝ), 0 ≤ ε → ε ≤ ε₀ →
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      (∀ y i, d.frame y i = smoothMetricFrame (d.γ y) i) →
      ∀ φ, Test Y d.γ d.frame φ → energyNorm Y d φ ≤ C*traceNorm Y d φ) :
    UniformEstimate Y Ω K ρ c₀ M Cj floor ε₀ C := by
  intro d ε hε hε₀ hd φ hφ
  let f (y : X dim) := smoothMetricFrame (d.γ y)
  have hBG := hd.1
  have hSmooth : ∀ i, ContDiffOn ℝ ∞ (fun y => f y i) Ω :=
    contDiffOn_smoothMetricFrame hBG.1.1 (fun _ hy => hBG.1.posDef hK hy)
  have hOrtho (y : X dim) (hy : y ∈ Ω) (i j : I dim) :
      metricPair d.γ y (f y i) (f y j) = if i=j then 1 else 0 :=
    smoothMetricFrame_orthonormal (hBG.1.posDef hK hy) i j
  have he := fun y hy => hBG.2.2.2.2.2.2.2 y (hsub hy)
  have hf := fun y hy => hOrtho y (hsub hy)
  have hD := hd.reframe hsub hSmooth hOrtho
  have hφf := hφ.of_orthonormalFrames he hf
  have h := hEstimate (d.reframe f) ε hε hε₀ hD (fun _ _ => rfl) φ hφf
  have hN : energyNorm Y (d.reframe f) φ = energyNorm Y d φ := by
    unfold energyNorm
    dsimp only [Data.reframe]
    rw [energySq_eq_of_orthonormalFrames hn hY (⟨fun i j => (hBG.1.1 i j).mono hsub,
      fun y hy => hBG.1.2 y (hsub hy)⟩ : Elliptic Y K d.γ) hK (fun i => (hBG.2.2.2.2.2.2.1 i).mono hsub)
      he hf d.radius hφ]
  rwa [hN,traceNorm_reframe hY he hf] at h

end CalderonN
