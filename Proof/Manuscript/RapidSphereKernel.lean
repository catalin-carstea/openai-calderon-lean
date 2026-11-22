module

public import Proof.Manuscript.RapidAngularFourier
public import Proof.Manuscript.MovingTrace.AngularChartCutoffs
public import Proof.Manuscript.GeometryAmbientSmoothing
import Proof.Manuscript.StereoAmbientKernelIntegral
import Proof.Manuscript.StereoTraceDensity
import Proof.CalderonN.EllipticCalculus
import Mathlib.Tactic

public section

noncomputable section

set_option maxHeartbeats 2300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set Filter MeasureTheory CalderonN
open scoped ContDiff Topology

namespace CalderonPaper

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {dim : ℕ} [Fact (Module.finrank ℝ (X dim) = dim - 1 + 1)]

local notation "S" => StandardAngularSphere dim
local notation "E" => AngularCoordinates dim

/-- For a first-order classical symbol whose homogeneous terms all
vanish, the local remainder bounds are exactly rapid decay. -/
theorem rapidAngularSymbol_of_zero_classical_expansion {U : Set P} (hU : IsOpen U)
    {a : P × E → E → ℂ} (ha : ContDiffOn ℝ ∞ (Function.uncurry a) ((U ×ˢ univ) ×ˢ univ))
    {c : E → ℝ} (hc₀ : c 0 = 0)
    {b : ℕ → P × E → E → ℂ}
    (hb : ∀ n p, p ∈ U → ∀ x ξ, ξ ≠ 0 → b n (p,x) ξ = 0)
    (hRest : ∀ J : Set P, IsCompact J → J ⊆ U →
      ∀ N k : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ p ∈ J, ∀ x ξ,
        ‖angularMixedJet k 0
          (fun q ξ' => a q ξ' - (c ξ' : ℂ) * ∑ j ∈ Finset.range N, b j q ξ') (p,x) ξ‖ ≤
        C * (1 + ‖ξ‖) ^ (1 - (N : ℝ))) :
    RapidAngularSymbol U a := by
  refine ⟨ha,?_⟩
  intro J hJ hJU k N
  obtain ⟨C,hC,hB⟩ := hRest J hJ hJU (N+1) k
  refine ⟨C,hC,fun p hp x ξ => ?_⟩
  let F (q : P × E) := a q ξ - (c ξ : ℂ) * ∑ j ∈ Finset.range (N+1), b j q ξ
  have hf : F =ᶠ[𝓝 (p,x)] fun q => a q ξ := by
    refine Filter.mem_of_superset ((hU.prod (isOpen_univ : IsOpen (univ : Set E))).mem_nhds
      (show (p,x) ∈ U ×ˢ univ from ⟨hJU hp,mem_univ x⟩)) ?_
    intro q hq
    change F q = a q ξ
    by_cases hξ : ξ = 0
    · simp [F,hξ,hc₀]
    · simp [F,hb _ _ hq.1 _ _ hξ]
  let L := (continuousMultilinearCurryFin0 ℝ E ℂ).symm
  have hNorm : ‖iteratedFDeriv ℝ k (L ∘ F) (p,x)‖ =
      ‖iteratedFDeriv ℝ k (fun q => a q ξ) (p,x)‖ :=
    (L.norm_iteratedFDeriv_comp_left _ _ _).trans
      (congrArg norm (hf.iteratedFDeriv ℝ k).eq_of_nhds)
  rw [← hNorm]
  have he : (1:ℝ) - ((N+1 : ℕ) : ℝ) = -(N:ℝ) := by push_cast; ring
  simpa only [angularMixedJet, iteratedFDeriv_zero_eq_comp, Function.comp_def, he, F, L]
    using hB p hp x ξ

private theorem exists_angular_chart_guard (v : S) {χ : X dim → ℂ}
    (hχS : angularSupport χ ⊆ (stereographic' (dim-1) v).source) :
    ∃ θ : X dim → ℂ, ContDiff ℝ ∞ θ ∧
      angularSupport θ ⊆ (stereographic' (dim-1) v).source ∧
      ∀ w : S, w ∈ angularSupport χ → θ w = 1 := by
  let D : Set (X dim) := {(v : X dim)}ᶜ
  let K : Set (X dim) := (Subtype.val : S → X dim) '' angularSupport χ
  have hD : IsOpen D := isClosed_singleton.isOpen_compl
  haveI : CompactSpace S := isCompact_iff_compactSpace.mp (isCompact_sphere (0 : X dim) 1)
  have hK : IsCompact K := isClosed_closure.isCompact.image continuous_subtype_val
  have hKD : K ⊆ D := by
    rintro _ ⟨w,hw,rfl⟩ hw'
    have hEq : w = v := Subtype.ext (mem_singleton_iff.mp hw')
    simpa only [stereographic'_source,mem_compl_iff,mem_singleton_iff,hEq,not_true_eq_false]
      using hχS hw
  obtain ⟨r,hr,_,hrD,hrK⟩ := Elliptic.exists_plateau_cutoff hD hK hKD
  let θ (w : X dim) : ℂ := (r w : ℂ)
  refine ⟨θ,Complex.ofRealCLM.contDiff.comp hr,?_,fun w hw => ?_⟩
  · rw [stereographic'_source]
    have hSup : angularSupport θ ⊆ (Subtype.val : S → X dim) ⁻¹' tsupport r := by
      apply closure_minimal
      · intro w hw
        exact subset_tsupport r (fun h => hw (by simp [θ,h]))
      · exact isClosed_closure.preimage continuous_subtype_val
    intro w hw hw'
    exact hrD (hSup hw) (mem_singleton_iff.mpr (congrArg Subtype.val (mem_singleton_iff.mp hw')))
  · change (r (w : X dim) : ℂ) = 1
    rw [(hrK (w : X dim) ⟨w,hw,rfl⟩).eq_of_nhds,Complex.ofReal_one]

private theorem smoothNear_continuous_on_sphere {u : X dim → ℂ}
    (hu : smoothNear u (standardSphere dim)) : Continuous (fun w : S => u w) := by
  obtain ⟨V,hV,hSV,hu⟩ := hu
  exact (hu.continuousOn.mono hSV).restrict

/-- A rapid exact chart quantization for disjoint cutoffs gives the
off-diagonal smoothing kernel for the same spherical operator. -/
theorem exists_ambient_offDiagonal_kernel_of_rapid_chart
    (hdim : 2 ≤ dim) {U W : Set P} (hU : IsOpen U) (hWU : W ⊆ U)
    {A : P → SphereOperator dim}
    (hZero : ∀ p ∈ W, ∀ f : X dim → ℂ, smoothNear f (standardSphere dim) →
      (∀ z : S, f z = 0) → ∀ w : S, A p f w = 0)
    (hChart : ∀ v : S, let κ := stereographic' (dim-1) v
      ∀ χ η : X dim → ℂ, smoothNear χ (standardSphere dim) → smoothNear η (standardSphere dim) →
      angularSupport χ ⊆ κ.source → angularSupport η ⊆ κ.source →
      Disjoint (angularSupport χ) (angularSupport η) →
      ∃ a : P × E → E → ℂ, RapidAngularSymbol U a ∧
        (∀ p ∈ W, ∀ x ∉ angularChartSupport v χ, ∀ ξ, a (p,x) ξ = 0) ∧
        ∀ p ∈ W, ∀ u : X dim → ℂ, smoothNear u (standardSphere dim) →
          ∀ x : E, χ (κ.symm x) * A p (fun w => η w*u w) (κ.symm x) =
            ∫ ξ, angularFourierPhase x ξ * a (p,x) ξ *
              angularFourierTransform (fun z : E => η (κ.symm z)*u (κ.symm z)) ξ)
    (χ η : X dim → ℂ) (hχ : smoothNear χ (standardSphere dim))
    (hη : smoothNear η (standardSphere dim))
    (hDis : Disjoint (angularSupport χ) (angularSupport η)) :
    ∃ F : P × (X dim × X dim) → ℂ, ContDiffOn ℝ ∞ F (U ×ˢ univ) ∧
      ∀ q ∈ W, ∀ u : X dim → ℂ, smoothNear u (standardSphere dim) →
        ∀ w : S, χ w * A q (fun z => η z * u z) w =
          ∫ z : S, F (q,(w,z)) * u z ∂sphereProbability dim := by
  by_cases hχN : (angularSupport χ).Nonempty
  swap
  · refine ⟨fun _ => 0,contDiffOn_const,fun p hp u hu w => ?_⟩
    have hw : χ w = 0 := by_contra fun hw => hχN ⟨w,subset_closure hw⟩
    simp [hw]
  by_cases hηN : (angularSupport η).Nonempty
  swap
  · refine ⟨fun _ => 0,contDiffOn_const,fun p hp u hu w => ?_⟩
    have hηu : smoothNear (fun z => η z * u z) (standardSphere dim) := by
      obtain ⟨V,hV,hSV,hηV⟩ := hη
      obtain ⟨W,hW,hSW,huW⟩ := hu
      exact ⟨V ∩ W,hV.inter hW,fun _ hz => ⟨hSV hz,hSW hz⟩,
        (hηV.mono inter_subset_left).mul (huW.mono inter_subset_right)⟩
    have hη0 (z : S) : η z = 0 := by_contra fun hz => hηN ⟨z,subset_closure hz⟩
    simp [hZero p hp _ hηu (fun z => by simp [hη0]) w]
  obtain ⟨v,hχS,hηS⟩ := disjoint_angularSupport_common_chart hdim χ η hχN hηN hDis
  let κ := stereographic' (dim-1) v
  obtain ⟨a,ha,ha0,haEq⟩ := hChart v χ η hχ hη hχS hηS hDis
  obtain ⟨θ,hθ,hθS,hθ1⟩ := exists_angular_chart_guard v hχS
  have hθnear : smoothNear θ (standardSphere dim) :=
    ⟨univ,isOpen_univ,subset_univ _,hθ.contDiffOn⟩
  obtain ⟨d,hd,hd0,hDensity⟩ := exists_stereographic_sphereProbability_density
    (by omega) v
  obtain ⟨F,hF,hFE⟩ := exists_joint_smooth_stereographic_kernel_integral
    v hθnear hη hθS hηS hd hd0 hDensity (contDiffOn_rapidAngularFourierKernel hU ha)
  refine ⟨F,hF,?_⟩
  intro p hp u hu w
  rw [hFE p (hWU hp) w (fun w : S => u w) (smoothNear_continuous_on_sphere hu)]
  by_cases hw : w ∈ angularSupport χ
  · have hx : κ.symm (κ w) = w := κ.left_inv (hχS hw)
    have hEq := haEq p hp u hu (κ w)
    rw [hx] at hEq
    have hf : ContDiff ℝ ∞ (fun x : E => η (κ.symm x) * u (κ.symm x)) ∧
        HasCompactSupport (fun x : E => η (κ.symm x) * u (κ.symm x)) :=
      compactSmooth_angularDatum v hη hu hηS
    rw [hEq,rapidAngularFourierKernel_quantization ha (hWU hp) (κ w) hf.1.continuous
      (hf.1.continuous.integrable_of_hasCompactSupport hf.2)]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change rapidAngularFourierKernel a (p,(κ w,x)) * (η (κ.symm x) * u (κ.symm x)) =
        θ w * η (κ.symm x) * rapidAngularFourierKernel a (p,(κ w,x)) * u (κ.symm x)
      rw [hθ1 w hw,one_mul]
      ring
  · have hχ0 : χ w = 0 := by_contra fun hz => hw (subset_closure hz)
    rw [hχ0,zero_mul]
    by_cases hwS : w ∈ κ.source
    · have hwX : κ w ∉ angularChartSupport v χ := by
        rintro ⟨w',hw',heq⟩
        exact hw (κ.injOn (hχS hw') hwS heq ▸ hw')
      have hk0 (x : E) : rapidAngularFourierKernel a (p,(κ w,x)) = 0 := by
        unfold rapidAngularFourierKernel
        simp [ha0 p hp (κ w) hwX]
      simp [κ,hk0]
    · have hθ0 : θ w = 0 := by_contra fun hz => hwS (hθS (subset_closure hz))
      simp [hθ0]

end CalderonPaper
