module

public import Proof.CalderonN.EnlargedTraceDensity

import Proof.CalderonN.MetricPair
import Mathlib.Tactic

/-! Adapted from `TracePairUniqueness` in the checked Theorem 3.1 release. -/

public section

noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

/-- All smooth Dirichlet traces on the same sphere determine a continuous
complex fiber function. The real and imaginary parts supply real tests. -/
theorem complex_eq_zero_on_frame_of_dirichlet_pairings
    {Y : Set (X dim)} {γ g : (MetricField dim)} {E : (X dim) × (X dim) → (X dim)} {r : (X dim) → ℝ} {y : (X dim)}
    (hy : y ∈ Y) (hDir : Dirichlet Y γ g E r)
    (e : (Frame dim)) (hframe : ∀ i j, metricPair γ y (e y i) (e y j) = if i = j then 1 else 0)
    {v : (X dim) → ℂ} (hv : smoothNear v (sphereAt γ y))
    (hAnn : ∀ u : (X dim) → ℝ, HarmonicOnBall g (closedBallImage γ E r y) u →
      sphereAverage e y (fun w => v w * (u (endpoint E r (y,w)) : ℂ)) = 0) :
    ∀ w : ↥(standardSphere dim), v (frameVector e y w) = 0 := by
  let f (w : ↥(standardSphere dim)) := v (frameVector e y w)
  have hw (w : ↥(standardSphere dim)) : frameVector e y w ∈ sphereAt γ y :=
    frameVector_mem_sphere γ e y hframe w
  obtain ⟨U,hU,hSU,hvU⟩ := hv
  have hCont : Continuous f :=
    hvU.continuousOn.comp_continuous ((continuous_frameVector e y).comp continuous_subtype_val)
      (fun w => hSU (hw w))
  have hRe : smoothNear (fun w : (X dim) => (v w).re) (sphereAt γ y) :=
    ⟨U,hU,hSU,Complex.reCLM.contDiff.comp_contDiffOn hvU⟩
  have hIm : smoothNear (fun w : (X dim) => (v w).im) (sphereAt γ y) :=
    ⟨U,hU,hSU,Complex.imCLM.contDiff.comp_contDiffOn hvU⟩
  obtain ⟨u,hu,_⟩ := hDir y hy _ hRe
  obtain ⟨b,hb,_⟩ := hDir y hy _ hIm
  have heRe : ∫ w, f w * ((f w).re : ℂ) ∂(sphereProbability dim) = 0 := by
    have hz := hAnn u hu.1
    change (∫ w : ↥(standardSphere dim), f w * (u (endpoint E r (y,frameVector e y w)) : ℂ) ∂(sphereProbability dim)) = 0 at hz
    rw [← hz]
    apply integral_congr_ae
    filter_upwards with w
    rw [hu.2 _ (hw w)]
  have heIm : ∫ w, f w * ((f w).im : ℂ) ∂(sphereProbability dim) = 0 := by
    have hz := hAnn b hb.1
    change (∫ w : ↥(standardSphere dim), f w * (b (endpoint E r (y,frameVector e y w)) : ℂ) ∂(sphereProbability dim)) = 0 at hz
    rw [← hz]
    apply integral_congr_ae
    filter_upwards with w
    rw [hb.2 _ (hw w)]
  have he := complex_eq_zero_of_enlarged_trace_duality hCont (ε := 1) one_pos
    (fun p => (f p.2).re) (fun p => (f p.2).im)
    ((Complex.continuous_re.comp (hCont.comp continuous_snd)).continuousOn)
    ((Complex.continuous_im.comp (hCont.comp continuous_snd)).continuousOn)
    (fun _ => rfl) (fun _ => rfl) (fun _ _ => heRe) (fun _ _ => heIm)
  exact fun w => congrFun he w

/-- Once two smooth moving trace adjoints have been constructed, their
values on each tested frame sphere agree. -/
theorem movingTraceAdjoint_eq_on_frame
    {Y : Set (X dim)} {γ g : (MetricField dim)} {E : (X dim) × (X dim) → (X dim)} {r : (X dim) → ℝ} {y : (X dim)}
    (hy : y ∈ Y) (hE : Continuous E) (hDir : Dirichlet Y γ g E r)
    (e : (Frame dim)) (hframe : ∀ i j, metricPair γ y (e y i) (e y j) = if i = j then 1 else 0)
    {A B : (TraceAdjoint dim)} (hA : IsMovingTraceAdjoint Y γ g e E r A)
    (hB : IsMovingTraceAdjoint Y γ g e E r B)
    (i : (I dim)) {ψ : (Field dim)} (hψ : smoothNear ψ (bundle Y γ)) :
    ∀ w : ↥(standardSphere dim),
      adjointField A i ψ (y,frameVector e y w) = adjointField B i ψ (y,frameVector e y w) := by
  let vA (w : (X dim)) := adjointField A i ψ (y,w)
  let vB (w : (X dim)) := adjointField B i ψ (y,w)
  have hFiber (v : (Field dim)) (h : smoothNear v (bundle Y γ)) :
      smoothNear (fun w => v (y,w)) (sphereAt γ y) := by
    obtain ⟨S,hS,hS',hsm⟩ := h
    let W := (fun w : (X dim) => (y,w)) ⁻¹' S
    have hW : IsOpen W := hS.preimage (continuous_const.prodMk continuous_id)
    have hSW : sphereAt γ y ⊆ W := fun _ hw => hS' ⟨hy,hw⟩
    exact ⟨W,hW,hSW,hsm.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ h => h)⟩
  obtain ⟨SA,hSA,hSA',hdA⟩ := hFiber _ (hA i ψ hψ).1
  obtain ⟨SB,hSB,hSB',hdB⟩ := hFiber _ (hB i ψ hψ).1
  have hsw (w : ↥(standardSphere dim)) : frameVector e y w ∈ sphereAt γ y :=
    frameVector_mem_sphere γ e y hframe w
  have hF : Continuous (fun w : ↥(standardSphere dim) => frameVector e y w) :=
    (continuous_frameVector e y).comp continuous_subtype_val
  have hC₁ : Continuous (fun w : ↥(standardSphere dim) => vA (frameVector e y w)) :=
    hdA.continuousOn.comp_continuous hF fun w => hSA' (hsw w)
  have hC₂ : Continuous (fun w : ↥(standardSphere dim) => vB (frameVector e y w)) :=
    hdB.continuousOn.comp_continuous hF fun w => hSB' (hsw w)
  have hV : smoothNear (fun w => vA w-vB w) (sphereAt γ y) :=
    ⟨SA ∩ SB,hSA.inter hSB,fun w hw => ⟨hSA' hw,hSB' hw⟩,
      (hdA.mono inter_subset_left).sub (hdB.mono inter_subset_right)⟩
  have hZero := complex_eq_zero_on_frame_of_dirichlet_pairings hy hDir e hframe hV (by
    intro u hu
    let h (w : ↥(standardSphere dim)) := u (endpoint E r (y,frameVector e y w))
    have hBdry (w : ↥(standardSphere dim)) :
        endpoint E r (y,frameVector e y w) ∈ closedBallImage γ E r y := by
      refine ⟨r y • frameVector e y w,?_,rfl⟩
      change metricPair γ y (r y • frameVector e y w) (r y • frameVector e y w) ≤ (r y)^2
      rw [metricPair_smul_same,show metricPair γ y (frameVector e y w) (frameVector e y w) = 1 from hsw w,mul_one]
    obtain ⟨S,hS,hSub,hSm⟩ := hu.1
    have hmap : Continuous (fun w : ↥(standardSphere dim) => (y,r y • frameVector e y w)) :=
      continuous_const.prodMk (hF.const_smul (r y))
    have hep : Continuous (fun w : ↥(standardSphere dim) => endpoint E r (y,frameVector e y w)) :=
      hE.comp hmap
    have hct : Continuous h :=
      hSm.continuousOn.comp_continuous hep (fun w => hSub (hBdry w))
    let : CompactSpace ↥(standardSphere dim) :=
      isCompact_iff_compactSpace.mp (isCompact_sphere (0 : (X dim)) 1)
    have h₁ : Integrable (fun w : ↥(standardSphere dim) => vA (frameVector e y w) * (h w : ℂ)) (sphereProbability dim) :=
      (hC₁.mul (Complex.continuous_ofReal.comp hct)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have h₂ : Integrable (fun w : ↥(standardSphere dim) => vB (frameVector e y w) * (h w : ℂ)) (sphereProbability dim) :=
      (hC₂.mul (Complex.continuous_ofReal.comp hct)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hPair := ((hA i ψ hψ).2 y hy u hu).trans ((hB i ψ hψ).2 y hy u hu).symm
    change (∫ w, vA (frameVector e y w) * (h w : ℂ) ∂(sphereProbability dim)) =
      (∫ w, vB (frameVector e y w) * (h w : ℂ) ∂(sphereProbability dim)) at hPair
    change (∫ w, (vA (frameVector e y w)-vB (frameVector e y w)) * (h w : ℂ) ∂(sphereProbability dim)) = 0
    simp_rw [sub_mul]
    rw [integral_sub h₁ h₂,hPair,sub_self])
  exact fun w => sub_eq_zero.mp (hZero w)

end CalderonN
