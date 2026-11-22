module

public import Proof.CalderonN.AdmittedScaledVelocitySmooth
public import Proof.CalderonN.ActualMovingTraceAdjoint

import Proof.CalderonN.TracePairUniqueness
import Mathlib.Tactic

/-! The adjoint in admissibility agrees with the literal fixed-ball
velocity adjoint on the selected fiber. The normal chart need only be
smooth on its admitted neighborhood. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

@[expose] def framedScaledMovingAdjoint (d : Data dim) (y : X dim) (i : I dim)
    (v : Field dim) (z : X dim) : ℂ :=
  let g (p : ℝ × X dim) := normalizedBallMetric d.g₁ d.expMap d.frame y (d.radius y) p.2
  let V (p : ℝ × X dim) := scaledNormalTraceVelocity d.γ d.expMap d.frame y (d.radius y)
    (fderiv ℝ d.radius y (axis i)) p.2 (axis i)
  let ψ (p : ℝ × X dim) := v (y,frameVector d.frame y p.2)
  ⟨parametricBallVelocityAdjoint g V (fun p => (ψ p).re) (0,z),
   parametricBallVelocityAdjoint g V (fun p => (ψ p).im) (0,z)⟩

private theorem complex_pair_integrals
    {a b : ↥(standardSphere dim) → ℂ} {u v : ↥(standardSphere dim) → ℝ}
    (ha : Continuous a) (hb : Continuous b) (hu : Continuous u) (hv : Continuous v)
    (hRe : (∫ w, (a w).re*u w ∂(sphereProbability dim)) = ∫ w, (b w).re*v w ∂(sphereProbability dim))
    (hIm : (∫ w, (a w).im*u w ∂(sphereProbability dim)) = ∫ w, (b w).im*v w ∂(sphereProbability dim)) :
    (∫ w, a w*(u w : ℂ) ∂(sphereProbability dim)) = ∫ w, b w*(v w : ℂ) ∂(sphereProbability dim) := by
  let : CompactSpace ↥(standardSphere dim) := isCompact_iff_compactSpace.mp (isCompact_sphere (0:X dim) 1)
  have h₁ : Integrable (fun w => a w*(u w : ℂ)) (sphereProbability dim) :=
    (ha.mul (Complex.continuous_ofReal.comp hu)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have h₂ : Integrable (fun w => b w*(v w : ℂ)) (sphereProbability dim) :=
    (hb.mul (Complex.continuous_ofReal.comp hv)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  apply Complex.ext
  · change (RCLike.re : ℂ → ℝ) _ = (RCLike.re : ℂ → ℝ) _
    rw [← integral_re h₁,← integral_re h₂]
    simpa only [RCLike.re_eq_complex_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      mul_zero,sub_zero,Function.comp_apply] using hRe
  · change (RCLike.im : ℂ → ℝ) _ = (RCLike.im : ℂ → ℝ) _
    rw [← integral_im h₁,← integral_im h₂]
    simpa only [RCLike.im_eq_complex_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      mul_zero,zero_add,Function.comp_apply] using hIm

theorem framedScaledMovingAdjoint_eq_actual
    {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data dim}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    {y : X dim} (hy : y ∈ Y) (hrρ : 2*d.radius y < ρ)
    (i : I dim) {v : Field dim} (hv : smoothNear v (bundle Y d.γ)) :
    ∀ z : ↥(standardSphere dim),
      framedScaledMovingAdjoint d y i v z =
        (d.radius y : ℂ)*adjointField d.adjoint i v (y,frameVector d.frame y z) := by
  let r := d.radius y
  let a := axis i
  let β := fderiv ℝ d.radius y a
  let F := normalBallChartMap d.expMap d.frame y r
  let m₀ := normalizedBallMetric d.g₁ d.expMap d.frame y r
  let V₀ (z : X dim) := scaledNormalTraceVelocity d.γ d.expMap d.frame y r β z a
  let ζ (z : X dim) := (y,frameVector d.frame y z)
  let ψ := v ∘ ζ
  let g (p : ℝ × X dim) := m₀ p.2
  let V (p : ℝ × X dim) := V₀ p.2
  let ψR (p : ℝ × X dim) := (ψ p.2).re
  let ψI (p : ℝ × X dim) := (ψ p.2).im
  let A := framedScaledMovingAdjoint d y i v
  let H := frameCoordinatesL d.γ y (d.frame y)
  have he := hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy)
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hrD := ((hd.2.2.2.2.1.1).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)
  have hζ : ContDiff ℝ ∞ ζ := by
    simp only [ζ,← frameVectorLinear_apply]
    exact contDiff_const.prodMk (frameVectorLinear d.frame y).contDiff
  have hζS (z : X dim) (hz : z ∈ standardSphere dim) : ζ z ∈ bundle Y d.γ :=
    ⟨hy,frameVector_mem_sphere d.γ d.frame y he ⟨z,hz⟩⟩
  have hv₀ := hv
  obtain ⟨S,hS,hVS,hvS⟩ := hv
  obtain ⟨W,hW,hCW,hVW,hDet⟩ := exists_admitted_scaledVelocity_smooth hd hy hrρ a β
  have h0 : HarmonicOnBall d.g₁ (closedBallImage d.γ d.expMap d.radius y) (0 : X dim → ℝ) := by
    refine ⟨⟨univ,isOpen_univ,subset_univ _,contDiffOn_const⟩,fun x _ => ?_⟩
    have hZero (k : I dim) : coordDeriv k (0 : X dim → ℝ) = 0 := by
      funext z
      simp [coordDeriv]
    simp [laplace,hZero,coordDeriv]
  obtain ⟨U₀,hU₀,hCU₀,hm₀,_,_⟩ := harmonicOnBall_admitted_normalChart hΩ hd hK hy hrρ h0
  let T := U₀ ∩ W ∩ ((ζ ⁻¹' S) ∩ ({0}ᶜ : Set (X dim)))
  have hT : IsOpen T := (hU₀.inter hW).inter
    ((hS.preimage hζ.continuous).inter isClosed_singleton.isOpen_compl)
  have hST : standardSphere dim ⊆ T := by
    intro z hz
    refine ⟨⟨hCU₀ (sphere_subset_closedBall hz),hCW (sphere_subset_closedBall hz)⟩,hVS (hζS z hz),?_⟩
    intro hz₀
    change z = 0 at hz₀
    simpa [standardSphere,hz₀] using hz
  have hψT : ContDiffOn ℝ ∞ ψ T :=
    hvS.comp hζ.contDiffOn (fun _ hz => hz.2.1)
  let P₀ := (univ : Set ℝ) ×ˢ U₀
  let P₁ := (univ : Set ℝ) ×ˢ T
  have hP₀ : IsOpen P₀ := isOpen_univ.prod hU₀
  have hP₁ : IsOpen P₁ := isOpen_univ.prod hT
  have hCP₀ : {(0:ℝ)} ×ˢ closedBall (0 : X dim) 1 ⊆ P₀ := fun _ hp => ⟨mem_univ _,hCU₀ hp.2⟩
  have hSP₁ : {(0:ℝ)} ×ˢ standardSphere dim ⊆ P₁ := fun _ hp => ⟨mem_univ _,hST hp.2⟩
  have hgm (i j : I dim) : ContDiffOn ℝ ∞ (fun p => g p i j) P₀ :=
    (hm₀.1 i j).comp contDiff_snd.contDiffOn (fun _ hp => hp.2)
  have hgp (p : ℝ × X dim) (hp : p ∈ P₀) : (g p).PosDef := hm₀.2 p.2 hp.2
  have hVP : ContDiffOn ℝ ∞ V P₁ := hVW.comp contDiff_snd.contDiffOn (fun _ hp => hp.2.1.2)
  have hψRP : ContDiffOn ℝ ∞ ψR P₁ :=
    (Complex.reCLM.contDiff.comp_contDiffOn hψT).comp contDiff_snd.contDiffOn (fun _ hp => hp.2)
  have hψIP : ContDiffOn ℝ ∞ ψI P₁ :=
    (Complex.imCLM.contDiff.comp_contDiffOn hψT).comp contDiff_snd.contDiffOn (fun _ hp => hp.2)
  obtain ⟨VR,_,hVR₀,hR⟩ := exists_contDiffOn_parametricBallVelocityAdjoint
    hP₀ hP₁ 0 hCP₀ hSP₁ hgm hgp hVP hψRP
  obtain ⟨VI,_,hVI₀,hI⟩ := exists_contDiffOn_parametricBallVelocityAdjoint
    hP₀ hP₁ 0 hCP₀ hSP₁ hgm hgp hVP hψIP
  let N := ({0} : Set (X dim))ᶜ
  have hN : IsOpen N := isClosed_singleton.isOpen_compl
  have hAR : ContDiffOn ℝ ∞ (fun z => (A z).re) N :=
    hR.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hz => ⟨hVR₀,hz⟩)
  have hAI : ContDiffOn ℝ ∞ (fun z => (A z).im) N :=
    hI.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hz => ⟨hVI₀,hz⟩)
  have hA : ContDiffOn ℝ ∞ A N := by
    have h : ContDiffOn ℝ ∞ (fun z => ((A z).re : ℂ)+Complex.I*((A z).im : ℂ)) N :=
      (Complex.ofRealCLM.contDiff.comp_contDiffOn hAR).add
        ((contDiffOn_const (c:=Complex.I)).mul (Complex.ofRealCLM.contDiff.comp_contDiffOn hAI))
    refine h.congr ?_
    intro z _
    apply Complex.ext <;> simp
  have hH (z : X dim) : H (frameVector d.frame y z) = z := by
    rw [← frameVectorL_apply_frame]
    exact frameCoordinatesL_frameVectorL d.γ y (d.frame y) he z
  have hHN (w : X dim) (hw : w ∈ sphereAt d.γ y) : H w ∈ N := by
    have h := norm_frameCoordinates_sq d.γ y w (d.frame y) he
    have hw' : metricPair d.γ y w w = 1 := hw
    change H w ≠ 0
    intro hZ
    rw [← frameCoordinatesL_apply] at h
    change ‖H w‖^2 = _ at h
    rw [hZ,hw',norm_zero] at h
    norm_num at h
  let vA (z : X dim) := adjointField d.adjoint i v (y,z)
  let D (z : X dim) := (r:ℂ)*vA z-A (H z)
  obtain ⟨J,hJ,hBJ,hAJ⟩ := (hd.2.2.2.1 i v hv₀).1
  let Q := (fun z : X dim => (y,z)) ⁻¹' J ∩ H ⁻¹' N
  have hQ : IsOpen Q := (hJ.preimage (continuous_const.prodMk continuous_id)).inter
    (hN.preimage H.continuous)
  have hQS : sphereAt d.γ y ⊆ Q := fun z hz => ⟨hBJ ⟨hy,hz⟩,hHN z hz⟩
  have hAQ : ContDiffOn ℝ ∞ vA Q :=
    hAJ.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ h => h.1)
  have hDQ : ContDiffOn ℝ ∞ D Q :=
    (contDiffOn_const.mul hAQ).sub (hA.comp H.contDiff.contDiffOn (fun _ h => h.2))
  have hD : smoothNear D (sphereAt d.γ y) := ⟨Q,hQ,hQS,hDQ⟩
  have hZero := complex_eq_zero_on_frame_of_dirichlet_pairings hy hd.2.2.1 d.frame he hD (by
    intro u hu
    obtain ⟨U,hU,hCU,hm,huF,hLap⟩ := harmonicOnBall_admitted_normalChart hΩ hd hK hy hrρ hu
    let FIB := U ∩ T
    have hFIB : IsOpen FIB := hU.inter hT
    have hSFIB : standardSphere dim ⊆ FIB := fun z hz => ⟨hCU (sphere_subset_closedBall hz),hST hz⟩
    have hVIB : ContDiffOn ℝ ∞ V₀ FIB := hVW.mono (fun _ h => h.2.1.2)
    have hψIB : ContDiffOn ℝ ∞ ψ FIB := hψT.mono inter_subset_right
    have hZeroIB : (0 : X dim) ∉ FIB := fun h => h.2.2.2 (mem_singleton _)
    let α (w : ↥(standardSphere dim)) := A w
    let ξ (w : ↥(standardSphere dim)) := ψ w
    let χ (w : ↥(standardSphere dim)) := (u ∘ F) w
    let τ (w : ↥(standardSphere dim)) := fderiv ℝ (u ∘ F) w (V₀ w)
    have hα : Continuous α :=
      hA.continuousOn.comp_continuous continuous_subtype_val (fun w => (hST w.property).2.2)
    have hξ : Continuous ξ :=
      hψT.continuousOn.comp_continuous continuous_subtype_val (fun w => hST w.property)
    have hχ : Continuous χ :=
      huF.continuousOn.comp_continuous continuous_subtype_val (fun w => hCU (sphere_subset_closedBall w.property))
    have hτ : Continuous τ :=
      (((huF.fderiv_of_isOpen (m:=∞) hU (by simp)).mono inter_subset_left).clm_apply hVIB).continuousOn
        |>.comp_continuous continuous_subtype_val (fun w => hSFIB w.property)
    have hPair : (∫ w, α w*(χ w : ℂ) ∂(sphereProbability dim)) =
        ∫ w, ξ w*(τ w : ℂ) ∂(sphereProbability dim) := by
      apply complex_pair_integrals hα hξ hχ hτ
      · exact integral_parametricBallVelocityAdjoint (0:ℝ) hU hFIB hCU hSFIB
          inter_subset_left hZeroIB hm hVIB (Complex.reCLM.contDiff.comp_contDiffOn hψIB) huF hLap
      · exact integral_parametricBallVelocityAdjoint (0:ℝ) hU hFIB hCU hSFIB
          inter_subset_left hZeroIB hm hVIB (Complex.imCLM.contDiff.comp_contDiffOn hψIB) huF hLap
    have hτeq (w : ↥(standardSphere dim)) : τ w =
        r*horizontal d.γ (fun p => u (endpoint d.expMap d.radius p)) y (frameVector d.frame y w) a := by
      have hVel : r • frameVector d.frame y w ∈ disk d.γ y (max ρ r) := by
        have hW := frameVector_mem_sphere d.γ d.frame y he w
        change metricPair d.γ y (r • frameVector d.frame y w) (r • frameVector d.frame y w) ≤ _
        rw [metricPair_smul_same,show metricPair d.γ y (frameVector d.frame y w) (frameVector d.frame y w) = 1 from hW,mul_one]
        have hρ' : r ≤ max ρ r := le_max_right _ _
        exact pow_le_pow_left₀ hr.le hρ' 2
      obtain ⟨E,hE,hET,hEs⟩ := hd.2.1.1
      have hE' : DifferentiableAt ℝ d.expMap (y,r • frameVector d.frame y w) :=
        (hEs.contDiffAt (hE.mem_nhds (hET ⟨hy,hVel⟩))).differentiableAt (by simp)
      obtain ⟨Ju,hJu,hNu,huJu⟩ := hu.1
      have hPoint : F w ∈ closedBallImage d.γ d.expMap d.radius y := by
        change F w ∈ closedBallImage d.γ d.expMap (fun _ => d.radius y) y
        rw [closedBallImage_eq_scaledFrameImage d.γ d.expMap d.frame y he hr]
        exact mem_image_of_mem _ (sphere_subset_closedBall w.property)
      have hU' := (huJu.contDiffAt (hJu.mem_nhds (hNu hPoint))).differentiableAt (by simp)
      exact fderiv_scaledNormalTraceVelocity_of_differentiableAt d.frame hE' hrD hU' a
        (hDet w (hCW (sphere_subset_closedBall w.property)))
    have hPhys := (hd.2.2.2.1 i v hv₀).2 y hy u hu
    let HTrace (w : ↥(standardSphere dim)) := horizontal d.γ
      (fun p => u (endpoint d.expMap d.radius p)) y (frameVector d.frame y w) a
    change (∫ w : ↥(standardSphere dim), vA (frameVector d.frame y w)*(χ w : ℂ) ∂(sphereProbability dim)) =
      ∫ w, ξ w * (HTrace w : ℂ) ∂(sphereProbability dim) at hPhys
    have hScaled : (∫ w : ↥(standardSphere dim), ((r:ℂ)*vA (frameVector d.frame y w))*(χ w : ℂ)
          ∂(sphereProbability dim)) = (∫ w, α w*(χ w : ℂ) ∂(sphereProbability dim)) := by
      simp_rw [mul_assoc]
      rw [integral_const_mul,hPhys,hPair,← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with w
      rw [hτeq,Complex.ofReal_mul]
      ring
    have hζC : Continuous (fun w : ↥(standardSphere dim) => ζ w) :=
      hζ.continuous.comp continuous_subtype_val
    have hVC : Continuous (fun w : ↥(standardSphere dim) => vA (frameVector d.frame y w)) :=
      hAJ.continuousOn.comp_continuous hζC (fun w => hBJ (hζS w w.property))
    let : CompactSpace ↥(standardSphere dim) := isCompact_iff_compactSpace.mp (isCompact_sphere (0:X dim) 1)
    have hL : Integrable (fun w : ↥(standardSphere dim) => ((r:ℂ)*vA (frameVector d.frame y w))*(χ w : ℂ))
        (sphereProbability dim) :=
      ((continuous_const.mul hVC).mul (Complex.continuous_ofReal.comp hχ)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
    have hR : Integrable (fun w => α w*(χ w : ℂ)) (sphereProbability dim) :=
      (hα.mul (Complex.continuous_ofReal.comp hχ)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
    change (∫ w : ↥(standardSphere dim), D (frameVector d.frame y w)*(χ w : ℂ) ∂(sphereProbability dim)) = 0
    simp_rw [D,hH,sub_mul]
    rw [integral_sub hL hR,hScaled,sub_self])
  intro z
  have hz := hZero z
  change (r:ℂ)*vA (frameVector d.frame y z)-A (H (frameVector d.frame y z)) = 0 at hz
  rw [hH] at hz
  exact (sub_eq_zero.mp hz).symm

end CalderonN
