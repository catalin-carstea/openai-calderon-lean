module

public import Proof.Manuscript.RadiusOperatorTaylor
public import Proof.Manuscript.GeometryAmbientSmoothing
public import Proof.Manuscript.MovingSymbolGeometryProfile

import Proof.CalderonN.Moments
import Proof.Manuscript.GeometrySymbolGlobalization
import Mathlib.Tactic

public section

noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set Filter Metric MeasureTheory CalderonN
open scoped ContDiff Topology

namespace CalderonPaper

variable {dim : ℕ} [NeZero dim]
  {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]
  {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

abbrev SphereRadiusAngular (dim : ℕ) := ↥(standardSphere dim)
local notation "S" => SphereRadiusAngular dim
private abbrev AmbientKernelDomain (Q : Type) (dim : ℕ) := (Q × (X dim × X dim)) × ℝ

private theorem continuous_sphereRadius_slice
    {O : Set (AmbientKernelDomain Q dim)} {a : AmbientKernelDomain Q dim → ℂ}
    (ha : ContDiffOn ℝ ∞ a O) (b : Q) (w : S) (r : ℝ)
    (hIn : ∀ z : S, ((b,((w : X dim),(z : X dim))),r) ∈ O) :
    Continuous (fun z : S => a ((b,((w : X dim),(z : X dim))),r)) := by
  refine continuousOn_univ.mp (ha.continuousOn.comp ?_ ?_)
  · exact ((continuous_const.prodMk (continuous_const.prodMk continuous_subtype_val)).prodMk
      continuous_const).continuousOn
  · exact fun z _ => hIn z

private theorem sphereRadius_derivative_of_kernel
    {O : Set (AmbientKernelDomain Q dim)} (hO : IsOpen O)
    {a : AmbientKernelDomain Q dim → ℂ} (ha : ContDiffOn ℝ ∞ a O)
    (b : Q) (w : S) {u : S → ℂ} (hu : Continuous u)
    {W : Set ℝ} (hW : IsOpen W) (hW₀ : 0 ∈ W)
    (hIn : ∀ r ∈ W, ∀ z : S, ((b,((w : X dim),(z : X dim))),r) ∈ O)
    (A : ℝ → ℂ) (χ : ℂ)
    (hA : ∀ r ∈ W, χ * A r = ∫ z : S, a ((b,((w : X dim),(z : X dim))),r) * u z ∂sphereProbability dim) :
    Integrable (fun z : S => radialFirstDerivative a ((b,((w : X dim),(z : X dim))),0) * u z)
      (sphereProbability dim) ∧
    χ * deriv A 0 =
      ∫ z : S, radialFirstDerivative a ((b,((w : X dim),(z : X dim))),0) * u z ∂sphereProbability dim := by
  haveI : CompactSpace S := isCompact_iff_compactSpace.mp (isCompact_sphere (0 : X dim) 1)
  obtain ⟨ε,hε,hεW⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds hW₀)
  let H := closedBall (0 : ℝ) (ε/2)
  have hHW : H ⊆ W := (closedBall_subset_ball (by linarith)).trans hεW
  have hH : IsCompact H := isCompact_closedBall _ _
  have hH₀ : 0 ∈ H := mem_closedBall_self (by positivity)
  have hHN : H ∈ 𝓝 (0:ℝ) := closedBall_mem_nhds _ (by positivity)
  let d := radialFirstDerivative a
  have hd : ContDiffOn ℝ ∞ d O := contDiffOn_radialFirstDerivative hO ha
  let f (v : ℝ × S) := ((b,((w : X dim),(v.2 : X dim))),v.1)
  have hf : Continuous f :=
    (continuous_const.prodMk (continuous_const.prodMk
      (continuous_subtype_val.comp continuous_snd))).prodMk continuous_fst
  have hComp : ContinuousOn (fun v : ℝ × S => d (f v) * u v.2) (H ×ˢ univ) :=
    (hd.continuousOn.comp hf.continuousOn (fun v hv => hIn v.1 (hHW hv.1) v.2)).mul
      (hu.comp continuous_snd).continuousOn
  obtain ⟨C,hC⟩ := (hH.prod isCompact_univ).exists_bound_of_continuousOn hComp
  have hInt0 : Integrable (fun z : S => a ((b,((w : X dim),(z : X dim))),0) * u z) (sphereProbability dim) :=
    ((continuous_sphereRadius_slice ha b w 0 (hIn 0 hW₀)).mul hu).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  refine radiusLocalized_derivative_of_quantization A χ (fun r (z : S) => a ((b,((w : X dim),(z : X dim))),r))
    (fun r (z : S) => d ((b,((w : X dim),(z : X dim))),r)) u hHN (fun r hr => hA r (hHW hr))
    (fun r hr => ((continuous_sphereRadius_slice ha b w r (hIn r (hHW hr))).mul
      hu).aestronglyMeasurable)
    hInt0 (((continuous_sphereRadius_slice hd b w 0 (hIn 0 (hHW hH₀))).mul
      hu).aestronglyMeasurable) (fun _ => C) (integrable_const _) ?_ ?_
  · exact Eventually.of_forall fun z r hr => by
      simpa only [f,norm_mul] using hC (r,z) ⟨hr,mem_univ _⟩
  · exact Eventually.of_forall fun z r hr =>
      hasDerivAt_radialFirstDerivative (ha.contDiffAt (hO.mem_nhds (hIn r (hHW hr) z)))

/-- Geometry parameters whose full straight radius segment stays in the
open signed-radius domain. -/
@[expose] def sphereRadiusSegment (e : (Q × ℝ) ≃ₗᵢ[ℝ] P) (U : Set P) : Set P :=
  e.symm ⁻¹' radiusSegment (e ⁻¹' U)

/-- Smooth disjoint-support kernels for the actual first radius derivative
and the exact quadratic remainder of the normalized spherical operator. -/
theorem exists_ambient_offDiagonal_radiusTaylor_kernel
    (e : (Q × ℝ) ≃ₗᵢ[ℝ] P) {U : Set P} (hU : IsOpen U)
    {A : P → SphereOperator dim} {χ η : X dim → ℂ}
    {F : P × (X dim × X dim) → ℂ} (hF : ContDiffOn ℝ ∞ F (U ×ˢ univ))
    (hEq : ∀ p ∈ U, ∀ u : X dim → ℂ, smoothNear u (standardSphere dim) →
      ∀ w : S, χ w * A p (fun z => η z * u z) w =
        ∫ z : S, F (p,(w,z)) * u z ∂sphereProbability dim) :
    IsOpen (sphereRadiusSegment e U) ∧
      ∃ F₀ E₁ : P × (X dim × X dim) → ℂ,
        ContDiffOn ℝ ∞ F₀ (sphereRadiusSegment e U ×ˢ univ) ∧
        ContDiffOn ℝ ∞ E₁ (sphereRadiusSegment e U ×ˢ univ) ∧
        ∀ p ∈ sphereRadiusSegment e U, ∀ u : X dim → ℂ, smoothNear u (standardSphere dim) →
          ∀ w : S,
            (χ w * radiusFirstSphereOperator e A p (fun z => η z * u z) w =
              ∫ z : S, F₀ (p,(w,z)) * u z ∂sphereProbability dim) ∧
            ((e.symm p).2 ≠ 0 →
              χ w * radiusTaylorSphereOperator e A p (fun z => η z * u z) w =
                ∫ z : S, E₁ (p,(w,z)) * u z ∂sphereProbability dim) := by
  let V : Set P := sphereRadiusSegment e U
  let T (q : AmbientKernelDomain Q dim) : P × (X dim × X dim) := (e (q.1.1,q.2),q.1.2)
  have hT : ContDiff ℝ ∞ T :=
    (e.contDiff.comp (contDiff_fst.fst.prodMk contDiff_snd)).prodMk contDiff_fst.snd
  let O := T ⁻¹' (U ×ˢ univ)
  have hO : IsOpen O := (hU.prod isOpen_univ).preimage hT.continuous
  let a := F ∘ T
  have ha : ContDiffOn ℝ ∞ a O := hF.comp hT.contDiffOn (mapsTo_preimage _ _)
  have hSeg : IsOpen V := by
    have heU : IsOpen (e ⁻¹' U) := hU.preimage e.continuous
    have h := radiusTaylorRemainder_contDiffOn heU
      (a := fun _ : Q × ℝ => (0:ℂ)) contDiffOn_const
    exact h.1.preimage e.symm.continuous
  let E₀ (p : P × (X dim × X dim)) : AmbientKernelDomain Q dim := (((e.symm p.1).1,p.2),0)
  let E (p : P × (X dim × X dim)) : AmbientKernelDomain Q dim := (((e.symm p.1).1,p.2),(e.symm p.1).2)
  let F₀ := radialFirstDerivative a ∘ E₀
  let E₁ := radiusTaylorRemainder a ∘ E
  have hE₀ : ContDiff ℝ ∞ E₀ :=
    (((e.symm.contDiff.comp contDiff_fst).fst).prodMk contDiff_snd).prodMk contDiff_const
  have hE : ContDiff ℝ ∞ E :=
    (((e.symm.contDiff.comp contDiff_fst).fst).prodMk contDiff_snd).prodMk
      (e.symm.contDiff.comp contDiff_fst).snd
  have hAt0 : MapsTo E₀ (V ×ˢ univ) O := by
    intro q hq
    have hz := hq.1 0 (left_mem_Icc.mpr zero_le_one)
    exact ⟨by simpa [E₀,T] using hz,mem_univ _⟩
  have hSegMap : MapsTo E (V ×ˢ univ) (radiusSegment O) := by
    intro q hq s hs
    exact ⟨hq.1 s hs,mem_univ _⟩
  refine ⟨hSeg,F₀,E₁,(contDiffOn_radialFirstDerivative hO ha).comp hE₀.contDiffOn hAt0,
    (radiusTaylorRemainder_contDiffOn hO ha).2.comp hE.contDiffOn hSegMap,?_⟩
  intro p hp u hu w
  let b := (e.symm p).1
  let r := (e.symm p).2
  let W := (fun s : ℝ => e (b,s)) ⁻¹' U
  have hW : IsOpen W := hU.preimage (e.continuous.comp (continuous_const.prodMk continuous_id))
  have hpSeg : ∀ t ∈ Icc (0:ℝ) 1, e (b,t*r) ∈ U := hp
  have hW₀ : 0 ∈ W := by
    simpa [W] using hpSeg 0 (left_mem_Icc.mpr zero_le_one)
  have hWr : r ∈ W := by
    simpa [W] using hpSeg 1 (right_mem_Icc.mpr zero_le_one)
  have hIn (s : ℝ) (hs : s ∈ W) (z : S) : ((b,((w : X dim),(z : X dim))),s) ∈ O := ⟨hs,mem_univ _⟩
  have hContu : Continuous (fun z : S => u z) := by
    obtain ⟨D,_,hSD,huD⟩ := hu
    exact (huD.continuousOn.mono hSD).restrict
  let D (s : ℝ) := A (e (b,s)) (fun z => η z*u z) w
  have hD (s : ℝ) (hs : s ∈ W) :
      χ w * D s = ∫ z : S, a ((b,((w : X dim),(z : X dim))),s)*u z ∂sphereProbability dim :=
    hEq (e (b,s)) hs u hu w
  obtain ⟨hiFirst,hFirst⟩ := sphereRadius_derivative_of_kernel hO ha b w hContu hW hW₀ hIn D (χ w) hD
  refine ⟨hFirst,?_⟩
  intro hr
  haveI : CompactSpace S := isCompact_iff_compactSpace.mp (isCompact_sphere (0 : X dim) 1)
  have hInt (s : ℝ) (hs : s ∈ W) :
      Integrable (fun z : S => a ((b,((w : X dim),(z : X dim))),s)*u z) (sphereProbability dim) :=
    ((continuous_sphereRadius_slice ha b w s (hIn s hs)).mul
      hContu).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hTaylor (z : S) : a ((b,((w : X dim),(z : X dim))),r) = a ((b,((w : X dim),(z : X dim))),0) +
      r • radialFirstDerivative a ((b,((w : X dim),(z : X dim))),0) + r^2 • E₁ (p,(w,z)) :=
    radius_taylor_eq hO ha (hSegMap (show (p,((w : X dim),(z : X dim))) ∈ V ×ˢ univ
      from ⟨hp,mem_univ _⟩))
  have hRem := (radiusLocalized_remainder_of_quantization D (χ w)
    (fun s (z : S) => a ((b,((w : X dim),(z : X dim))),s)) (fun s (z : S) => radialFirstDerivative a ((b,((w : X dim),(z : X dim))),s))
    (fun z : S => E₁ (p,(w,z))) (fun z : S => u z) r hr
    (hD 0 hW₀) (hD r hWr) hFirst (hInt 0 hW₀) (hInt r hWr) hiFirst hTaylor).2
  have hBp : e (b,r) = p := by change e (e.symm p) = p; exact e.apply_symm_apply p
  simpa only [D,hBp,radiusTaylorSphereOperator,radiusFirstSphereOperator,b,r] using hRem

/-- A compact set of physical moving geometries is closed under scaling
the independent radius toward zero. -/
theorem movingSymbolGeometryCompact_subset_sphereRadiusSegment {dim : ℕ}
    {Y : Set (X dim)} {ρ B : ℝ} {U : Set (MovingSymbolGeometry dim)}
    (hJU : movingSymbolGeometryCompact Y ρ B ⊆ U) :
    movingSymbolGeometryCompact Y ρ B ⊆ sphereRadiusSegment (movingSymbolSignedRadiusEquiv dim) U := by
  intro p hp t ht
  rcases p with ⟨⟨lam,y,r⟩,b⟩
  have hr : r ∈ Icc (0:ℝ) ρ := hp.1.2.2
  apply hJU
  exact ⟨⟨hp.1.1,hp.1.2.1,mul_nonneg ht.1 hr.1,
    (mul_le_of_le_one_left hr.1 ht.2).trans hr.2⟩,hp.2⟩

/-- Package both literal radius Taylor kernels with the uniform geometry
jet bounds on an open subdomain and its compact parameter set. -/
theorem exists_uniform_offDiagonal_radiusTaylor_kernel
    (e : (Q × ℝ) ≃ₗᵢ[ℝ] P) {U V J : Set P} (hU : IsOpen U) (hV : IsOpen V)
    (hJ : IsCompact J) (hJV : J ⊆ V) (hVSeg : V ⊆ sphereRadiusSegment e U)
    {A : P → SphereOperator dim} {χ η : X dim → ℂ}
    {F : P × (X dim × X dim) → ℂ} (hF : ContDiffOn ℝ ∞ F (U ×ˢ univ))
    (hEq : ∀ p ∈ U, ∀ u : X dim → ℂ, smoothNear u (standardSphere dim) →
      ∀ w : S, χ w * A p (fun z => η z * u z) w =
        ∫ z : S, F (p,(w,z)) * u z ∂sphereProbability dim) :
    ∃ K₀ K₁ : P × X dim → X dim → ℂ,
      UniformGeometryAngularSmoothing V J K₀ ∧ UniformGeometryAngularSmoothing V J K₁ ∧
      ∀ p ∈ J, ∀ u : X dim → ℂ, smoothNear u (standardSphere dim) →
        ∀ w : S,
          (χ w * radiusFirstSphereOperator e A p (fun z => η z * u z) w =
            ∫ z : S, K₀ (p,w) z * u z ∂sphereProbability dim) ∧
          ((e.symm p).2 ≠ 0 →
            χ w * radiusTaylorSphereOperator e A p (fun z => η z * u z) w =
              ∫ z : S, K₁ (p,w) z * u z ∂sphereProbability dim) := by
  obtain ⟨_,F₀,E₁,hF₀,hE₁,hTerms⟩ := exists_ambient_offDiagonal_radiusTaylor_kernel e hU hF hEq
  have hSub : V ×ˢ (univ : Set (X dim × X dim)) ⊆ sphereRadiusSegment e U ×ˢ univ :=
    fun _ h => ⟨hVSeg h.1,h.2⟩
  exact ⟨fun q z => F₀ (q.1,(q.2,z)), fun q z => E₁ (q.1,(q.2,z)),
    uniformGeometryAngularSmoothing_of_ambient hV hJ hJV (hF₀.mono hSub),
    uniformGeometryAngularSmoothing_of_ambient hV hJ hJV (hE₁.mono hSub),
    fun p hp => hTerms p (hVSeg (hJV hp))⟩

/-- Globalize the smooth Taylor kernels after fixing the compact
geometry set. Their exact quantization on the compact set is preserved. -/
theorem exists_global_offDiagonal_radiusTaylor_kernel
    (e : (Q × ℝ) ≃ₗᵢ[ℝ] P) {U J : Set P} (hU : IsOpen U) (hJ : IsCompact J)
    (hJSeg : J ⊆ sphereRadiusSegment e U)
    {A : P → SphereOperator dim} {χ η : X dim → ℂ}
    {F : P × (X dim × X dim) → ℂ} (hF : ContDiffOn ℝ ∞ F (U ×ˢ univ))
    (hEq : ∀ p ∈ U, ∀ u : X dim → ℂ, smoothNear u (standardSphere dim) →
      ∀ w : S, χ w * A p (fun z => η z * u z) w =
        ∫ z : S, F (p,(w,z)) * u z ∂sphereProbability dim) :
    ∃ K₀ K₁ : P × X dim → X dim → ℂ,
      UniformGeometryAngularSmoothing univ J K₀ ∧ UniformGeometryAngularSmoothing univ J K₁ ∧
      ∀ p ∈ J, ∀ u : X dim → ℂ, smoothNear u (standardSphere dim) →
        ∀ w : S,
          (χ w * radiusFirstSphereOperator e A p (fun z => η z * u z) w =
            ∫ z : S, K₀ (p,w) z * u z ∂sphereProbability dim) ∧
          ((e.symm p).2 ≠ 0 →
            χ w * radiusTaylorSphereOperator e A p (fun z => η z * u z) w =
              ∫ z : S, K₁ (p,w) z * u z ∂sphereProbability dim) := by
  obtain ⟨hV,F₀,E₁,hF₀,hE₁,hTerms⟩ := exists_ambient_offDiagonal_radiusTaylor_kernel e hU hF hEq
  obtain ⟨K₀,hK₀,hK₀Eq⟩ := UniformGeometryAngularSmoothing.globalize hV hJ hJSeg
    (uniformGeometryAngularSmoothing_of_ambient hV hJ hJSeg hF₀)
  obtain ⟨K₁,hK₁,hK₁Eq⟩ := UniformGeometryAngularSmoothing.globalize hV hJ hJSeg
    (uniformGeometryAngularSmoothing_of_ambient hV hJ hJSeg hE₁)
  refine ⟨K₀,K₁,hK₀,hK₁,fun p hp u hu w => ?_⟩
  obtain ⟨hFirst,hTail⟩ := hTerms p (hJSeg hp) u hu w
  exact ⟨by simpa only [hK₀Eq p hp] using hFirst,fun hr => by
    simpa only [hK₁Eq p hp] using hTail hr⟩

end CalderonPaper
