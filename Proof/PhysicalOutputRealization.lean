import Proof.PhysicalTraceRegularity
import Proof.ProductOutputCompletion

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set MeasureTheory Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.SmoothSphereFields

structure PhysicalOutputRealization (Y : Set X) (g : MetricField) (e : Frame) (F : Field) where
  representative : X × UnitSphere → ℂ
  continuous : Continuous representative
  eqOn : ∀ y ∈ Y,∀ v : UnitSphere,representative (y,v) = F (y,frameVector e y v.val)
  memLp : MemLp representative 2 ((outputBaseMeasure Y g).prod sphereProbability)

def PhysicalOutputRealization.output {Y : Set X} {g : MetricField} {e : Frame} {F : Field}
    (P : PhysicalOutputRealization Y g e F) : Lp ℂ 2 ((outputBaseMeasure Y g).prod sphereProbability) :=
  P.memLp.toLp P.representative

lemma PhysicalOutputRealization.normSq {Y : Set X} {g : MetricField} {e : Frame} {F : Field}
    (P : PhysicalOutputRealization Y g e F) (hY : IsOpen Y) (hρ : ContinuousOn (metricDensity g) Y) :
    ‖P.output‖^2 = outputSq Y g e F := by
  rw [PhysicalOutputRealization.output,norm_sq_output_product hY hρ]
  apply setIntegral_congr_fun hY.measurableSet
  intro y hy
  change metricDensity g y*_ = metricDensity g y*fiberSq e y (fun w => F (y,w))
  rw [fiberSq_integral_norm]
  apply congrArg (metricDensity g y * ·)
  apply integral_congr_ae
  exact Eventually.of_forall (fun v => congrArg (fun z : ℂ => ‖z‖^2) (P.eqOn y hy v))

/-- Every smooth field with compact center support has a genuine physical product-L²
    representative, without imposing a mean-zero condition on its output. -/
theorem exists_physicalOutputRealization {Y : Set X} (hY : IsOpen Y) {g : MetricField} (e : Frame)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (hρ : ContinuousOn (metricDensity g) Y) {F : Field} (hF : smoothNear F (bundle Y g))
    (hcpt : ∃ S,IsCompact S ∧ S ⊆ Y ∧ ∀ y ∈ Y \ S,∀ w ∈ sphereAt g y,F (y,w) = 0) :
    Nonempty (PhysicalOutputRealization Y g e F) := by
  obtain ⟨S,hS,hSY,G,hG,hrep,hzero⟩ := exists_smooth_standard_representative_of_support hY e he hframe hF hcpt
  let U := ambientSphereL2 (fun p => (G p).re) (Complex.reCLM.contDiff.comp hG)
  let V := ambientSphereL2 (fun p => (G p).im) (Complex.imCLM.contDiff.comp hG)
  have hU : ContDiff ℝ ∞ U := contDiff_ambientSphereL2 _ _
  have hV : ContDiff ℝ ∞ V := contDiff_ambientSphereL2 _ _
  have hzU (y : X) (hy : y ∉ S) : U y = 0 := ambientSphereL2_eq_zero _ _ y
    (fun v => by simp only [hzero y hy v,Complex.zero_re])
  have hzV (y : X) (hy : y ∉ S) : V y = 0 := ambientSphereL2_eq_zero _ _ y
    (fun v => by simp only [hzero y hy v,Complex.zero_im])
  have hsU : tsupport U ⊆ S := closure_minimal (fun y hy => by_contra fun hn => hy (hzU y hn)) hS.isClosed
  have hsV : tsupport V ⊆ S := closure_minimal (fun y hy => by_contra fun hn => hy (hzV y hn)) hS.isClosed
  have hiU := integrableOn_local_weighted_norm_sq hY _ hρ U hU.continuous (HasCompactSupport.intro hS hzU) (hsU.trans hSY)
  have hiV := integrableOn_local_weighted_norm_sq hY _ hρ V hV.continuous (HasCompactSupport.intro hS hzV) (hsV.trans hSY)
  let R : X × UnitSphere → ℂ := fun p => G (p.1,p.2.val)
  have hR : Continuous R := hG.continuous.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hm : MemLp R 2 ((outputBaseMeasure Y g).prod sphereProbability) := by
    apply memLp_output_product hY hρ R hR
    apply (hiU.add hiV).congr
    filter_upwards [] with y
    have heq := integral_complex_norm_sq_components (fun v => G (y,v.val)) (U y) (V y)
      (ambientSphereL2_ae _ _ y) (ambientSphereL2_ae _ _ y)
    change metricDensity g y*‖U y‖^2+metricDensity g y*‖V y‖^2 = metricDensity g y*(∫ v,‖G (y,v.val)‖^2 ∂sphereProbability)
    rw [heq,mul_add]
  exact ⟨⟨R,hR,hrep,hm⟩⟩

/-- The actual moving trace is a well-defined element of the exact frozen output Hilbert
    space, with norm equal to the physical traceNorm appearing in Proposition 5.3. -/
theorem Admissible.exists_movingTraceOutput {Y Ω : Set X} (hY : IsOpen Y) (hsub : Y ⊆ Ω)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K) {φ : Field} (hφ : Test Y d.γ d.frame φ) :
    ∃ P : PhysicalOutputRealization Y d.γ d.frame (movingTrace d.γ d.g₂ d.radius d.adjoint φ),
      ‖P.output‖ = traceNorm Y d φ := by
  have h : Elliptic Y K d.γ := ⟨fun i j => (hd.1.1.1 i j).mono hsub,fun y hy => hd.1.1.2 y (hsub hy)⟩
  have h₂ : Elliptic Y K d.g₂ := ⟨fun i j => (hd.1.2.2.1.1 i j).mono hsub,fun y hy => hd.1.2.2.1.2 y (hsub hy)⟩
  have he : ∀ i,ContDiffOn ℝ ∞ (fun y => d.frame y i) Y := fun i => (hd.1.2.2.2.2.2.2.1 i).mono hsub
  have hframe : ∀ y ∈ Y,∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j) = if i = j then 1 else 0 :=
    fun y hy => hd.1.2.2.2.2.2.2.2 y (hsub hy)
  have hρ := (h.contDiffOn_density hK).continuousOn
  obtain ⟨S,hS,hSY,hzero⟩ := hφ.2.1
  obtain ⟨P⟩ := exists_physicalOutputRealization hY d.frame he hframe hρ
    (smoothNear_movingTrace hY h h₂ hK hd.2.2.2.2.1.1 hd.2.2.2.1 hφ.1)
    ⟨S,hS,hSY,fun y hy w hw => movingTrace_zero_of_support hY h hK d.frame he hframe hd.2.2.2.1 hd.2.2.1
      hφ.1 S hS.isClosed hzero hy w hw⟩
  refine ⟨P,?_⟩
  change ‖P.output‖ = Real.sqrt (outputSq Y d.γ d.frame _)
  rw [← P.normSq hY hρ,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _)]

end ShrinkingSpheres
