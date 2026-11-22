module

public import Proof.Manuscript.MovingTraceSymbols

import Proof.CalderonN.CompactSmoothExtension
import Proof.CalderonN.EllipticCalculus
import Proof.CalderonN.LocalMixedParameterJetCalculus
import Proof.CalderonN.TaylorJetCalculus
import Mathlib.Tactic

public section

noncomputable section

open Set Filter Metric CalderonN
open scoped ContDiff Topology InnerProductSpace

namespace CalderonPaper

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {dim : ℕ} [Fact (Module.finrank ℝ (X dim) = dim - 1 + 1)]

/-- On any compact subset of the source, the stereographic map has an
ambient smooth extension which agrees in an ambient neighborhood. -/
theorem exists_compact_stereographic_ambient_coordinates
    (v : ↥(standardSphere dim)) {S : Set ↥(standardSphere dim)} (hS : IsCompact S)
    (hChart : S ⊆ (stereographic' (dim-1) v).source) :
    ∃ c : X dim → AngularCoordinates dim, ContDiff ℝ ∞ c ∧ HasCompactSupport c ∧
      ∀ z ∈ S, c (z : X dim) = stereographic' (dim-1) v z := by
  let κ := stereographic' (dim-1) v
  let U := {x : X dim | ⟪(v : X dim), x⟫_ℝ ≠ 1}
  let L := (OrthonormalBasis.fromOrthogonalSpanSingleton (dim-1) (𝕜 := ℝ)
    (ne_zero_of_mem_unit_sphere v)).repr
  let f := fun x : X dim => L (stereoToFun (v : X dim) x)
  have hU : IsOpen U := (isClosed_singleton.preimage (innerSL ℝ (v : X dim)).continuous).isOpen_compl
  have hF : ContDiffOn ℝ ∞ f U := L.contDiff.comp_contDiffOn contDiffOn_stereoToFun
  let C := (Subtype.val : ↥(standardSphere dim) → X dim) '' S
  have hC : IsCompact C := hS.image continuous_subtype_val
  have hCU : C ⊆ U := by
    rintro _ ⟨z,hz,rfl⟩
    have hzV : z ≠ v := by
      simpa only [stereographic'_source, mem_compl_iff, mem_singleton_iff] using hChart hz
    exact ne_of_lt ((inner_lt_one_iff_real_of_norm_eq_one (norm_eq_of_mem_sphere v)
      (norm_eq_of_mem_sphere z)).mpr (fun h => hzV (Subtype.ext h.symm)))
  obtain ⟨c,hc,hc₀,W,_,hCW,_,heq⟩ := exists_contDiff_extension_near_compact hU hC hCU hF
  refine ⟨c,hc,hc₀,fun z hz => ?_⟩
  exact heq (hCW ⟨z,hz,rfl⟩)

omit [Fact (Module.finrank ℝ (X dim) = dim - 1 + 1)] in
/-- Replace a locally smooth angular cutoff by a globally smooth ambient
cutoff. Its ambient support stays inside the chosen open neighborhood of
the angular support. -/
private theorem exists_supported_ambient_angular_cutoff
    {χ : X dim → ℂ} (hχ : smoothNear χ (standardSphere dim))
    {U : Set (X dim)} (hU : IsOpen U)
    (hSupp : (Subtype.val : ↥(standardSphere dim) → X dim) '' angularSupport χ ⊆ U) :
    ∃ a : X dim → ℂ, ContDiff ℝ ∞ a ∧ HasCompactSupport a ∧ tsupport a ⊆ U ∧
      ∀ w : ↥(standardSphere dim), a w = χ w := by
  let S : Set (X dim) := standardSphere dim
  have hSc : IsCompact S := isCompact_sphere _ _
  obtain ⟨V,hV,hSV,hχV⟩ := hχ
  obtain ⟨g,hg,_,W,_,hSW,_,hEg⟩ := exists_contDiff_extension_near_compact hV hSc hSV hχV
  have : CompactSpace ↥(standardSphere dim) := isCompact_iff_compactSpace.mp hSc
  have hK : IsCompact ((Subtype.val : ↥(standardSphere dim) → X dim) '' angularSupport χ) :=
    isClosed_closure.isCompact.image continuous_subtype_val
  obtain ⟨r,hr,hrc,hrU,hrOne⟩ := Elliptic.exists_plateau_cutoff hU hK hSupp
  let a (w : X dim) := (r w : ℂ)*g w
  have ha : ContDiff ℝ ∞ a := (Complex.ofRealCLM.contDiff.comp hr).mul hg
  have haR : tsupport a ⊆ tsupport r := by
    apply closure_mono
    intro w hw
    by_contra hn
    have hrw := Function.notMem_support.mp hn
    exact hw (by simp [a,hrw])
  refine ⟨a,ha,hrc.of_isClosed_subset isClosed_closure haR,haR.trans hrU,fun w => ?_⟩
  have hgχ := hEg (hSW w.property)
  by_cases hw : χ w = 0
  · simp [a,hgχ,hw]
  · have hmem : w ∈ angularSupport χ := subset_closure hw
    have hrw : r w = 1 := (hrOne (w : X dim) ⟨w,hmem,rfl⟩).eq_of_nhds
    simp [a,hgχ,hrw]

/-- The ambient cutoff and coordinate factors are independent of the
base parameter and of the coordinate-space kernel. -/
theorem exists_stereographic_cutoff_kernel_factors
    (v : ↥(standardSphere dim)) {χ η : X dim → ℂ}
    (hχ : smoothNear χ (standardSphere dim)) (hη : smoothNear η (standardSphere dim))
    (hχS : angularSupport χ ⊆ (stereographic' (dim-1) v).source)
    (hηS : angularSupport η ⊆ (stereographic' (dim-1) v).source)
    {d : AngularCoordinates dim → ℝ} (hd : ContDiff ℝ ∞ d) (hd₀ : ∀ z, 0 < d z) :
    ∃ (a b : X dim → ℂ) (c : X dim → AngularCoordinates dim),
      ContDiff ℝ ∞ a ∧ ContDiff ℝ ∞ b ∧ ContDiff ℝ ∞ c ∧
      HasCompactSupport a ∧ HasCompactSupport b ∧ HasCompactSupport c ∧
      (∀ w : ↥(standardSphere dim), a w = χ w) ∧
      (∀ z : ↥(standardSphere dim), b z = η z / (d (stereographic' (dim-1) v z) : ℂ)) ∧
      ∀ z ∈ angularSupport χ ∪ angularSupport η,
        c (z : X dim) = stereographic' (dim-1) v z := by
  have : CompactSpace ↥(standardSphere dim) := isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
  have hC : IsCompact (angularSupport χ ∪ angularSupport η) := (isClosed_closure.union isClosed_closure).isCompact
  obtain ⟨c,hc,hcc,hec⟩ := exists_compact_stereographic_ambient_coordinates v hC (union_subset hχS hηS)
  let U : Set (X dim) := {(v : X dim)}ᶜ
  have hU : IsOpen U := isClosed_singleton.isOpen_compl
  have hRoom {f : X dim → ℂ} (hf : angularSupport f ⊆ (stereographic' (dim-1) v).source) :
      (Subtype.val : ↥(standardSphere dim) → X dim) '' angularSupport f ⊆ U := by
    rintro _ ⟨z,hz,rfl⟩ h
    have hNe : z ≠ v := by
      simpa only [stereographic'_source, mem_compl_iff, mem_singleton_iff] using hf hz
    exact hNe (Subtype.ext (mem_singleton_iff.mp h))
  obtain ⟨a,ha,hac,_,heqa⟩ := exists_supported_ambient_angular_cutoff hχ hU (hRoom hχS)
  obtain ⟨b₀,hb₀,hbc₀,_,heqb⟩ := exists_supported_ambient_angular_cutoff hη hU (hRoom hηS)
  let b (x : X dim) := b₀ x / (d (c x) : ℂ)
  have hi : ContDiff ℝ ∞ (fun x => (d (c x))⁻¹) := (hd.comp hc).inv (fun x => (hd₀ (c x)).ne')
  have hb : ContDiff ℝ ∞ b := by
    simpa only [b, Function.comp_apply, Complex.ofRealCLM_apply, Complex.ofReal_inv, div_eq_mul_inv]
      using hb₀.mul (Complex.ofRealCLM.contDiff.comp hi)
  have hbc : HasCompactSupport b := by
    apply hbc₀.of_isClosed_subset isClosed_closure
    apply closure_mono
    intro x hx
    by_contra hn
    have hb₀x := Function.notMem_support.mp hn
    exact hx (by simp [b,hb₀x])
  refine ⟨a,b,c,ha,hb,hc,hac,hbc,hcc,heqa,fun z => ?_,hec⟩
  by_cases hz : η z = 0
  · simp [b,heqb,hz]
  · have hmem : z ∈ angularSupport χ ∪ angularSupport η := Or.inr (subset_closure hz)
    rw [show b z = b₀ z / (d (c z) : ℂ) from rfl,heqb,hec z hmem]

/-- A smooth coordinate kernel divided by the chart density, localized
on both sides, extends smoothly over the entire ambient angular space. -/
theorem exists_joint_smooth_stereographic_cutoff_kernel
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {V : Set P} (v : ↥(standardSphere dim)) {χ η : X dim → ℂ}
    (hχ : smoothNear χ (standardSphere dim)) (hη : smoothNear η (standardSphere dim))
    (hχS : angularSupport χ ⊆ (stereographic' (dim-1) v).source)
    (hηS : angularSupport η ⊆ (stereographic' (dim-1) v).source)
    {d : AngularCoordinates dim → ℝ} (hd : ContDiff ℝ ∞ d) (hd₀ : ∀ z, 0 < d z)
    {K : P × (AngularCoordinates dim × AngularCoordinates dim) → ℂ}
    (hK : ContDiffOn ℝ ∞ K (V ×ˢ univ)) :
    ∃ F : P × (X dim × X dim) → ℂ, ContDiffOn ℝ ∞ F (V ×ˢ univ) ∧
      ∀ p (w z : ↥(standardSphere dim)),
        F (p,(w,z)) = χ w * (η z / (d (stereographic' (dim-1) v z) : ℂ)) *
          K (p,(stereographic' (dim-1) v w, stereographic' (dim-1) v z)) := by
  obtain ⟨a,b,c,ha,hb,hc,_,_,_,hea,heb,hec⟩ :=
    exists_stereographic_cutoff_kernel_factors v hχ hη hχS hηS hd hd₀
  let E (q : P × (X dim × X dim)) := (q.1,(c q.2.1,c q.2.2))
  have hE : ContDiff ℝ ∞ E := contDiff_fst.prodMk
    ((hc.comp contDiff_snd.fst).prodMk (hc.comp contDiff_snd.snd))
  have hKE : ContDiffOn ℝ ∞ (K ∘ E) (V ×ˢ univ) :=
    hK.comp hE.contDiffOn (fun q hq => ⟨hq.1,mem_univ _⟩)
  let F (q : P × (X dim × X dim)) := a q.2.1 * b q.2.2 * K (E q)
  have hF : ContDiffOn ℝ ∞ F (V ×ˢ univ) :=
    (((ha.comp contDiff_snd.fst).mul (hb.comp contDiff_snd.snd)).contDiffOn).mul hKE
  refine ⟨F,hF,fun p w z => ?_⟩
  change a w * b z * K (p,(c w,c z)) = _
  rw [hea,heb]
  by_cases hw : χ w = 0
  · simp [hw]
  by_cases hz : η z = 0
  · simp [hz]
  rw [hec w (Or.inl (subset_closure hw)),hec z (Or.inr (subset_closure hz))]

private theorem contDiffOn_partial_right_iteratedFDeriv
    {A B F : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {U : Set (A × B)}
    (hU : IsOpen U) {f : A × B → F} (hf : ContDiffOn ℝ ∞ f U) (n : ℕ) :
    ContDiffOn ℝ ∞ (fun q => iteratedFDeriv ℝ n (fun b => f (q.1,b)) q.2) U := by
  let L := ContinuousLinearMap.inr ℝ A B
  let R : ContinuousMultilinearMap ℝ (fun _ : Fin n => A × B) F →L[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin n => B) F :=
    ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin n => L)
  have hR : ContDiffOn ℝ ∞ (fun q => R (iteratedFDeriv ℝ n f q)) U :=
    R.contDiff.comp_contDiffOn (contDiffOn_iteratedFDeriv_top hf hU n)
  apply hR.congr
  intro q hq
  obtain ⟨g,hg,he⟩ := exists_global_smooth_germ_of_open f hU hf hq
  have heg := (he.iteratedFDeriv ℝ n).eq_of_nhds
  have hs : (fun b => g (q.1,b)) =ᶠ[𝓝 q.2] (fun b => f (q.1,b)) :=
    he.comp_tendsto ((continuous_const.prodMk continuous_id).continuousAt)
  have hT : ContDiff ℝ ∞ (fun z : A × B => g ((q.1,0)+z)) :=
    hg.comp (contDiff_const.add contDiff_id)
  have hEq : (fun b => g (q.1,b)) = (fun z => g ((q.1,0)+z)) ∘ L := by
    funext b
    simp [L]
  change iteratedFDeriv ℝ n (fun b => f (q.1,b)) q.2 = _
  rw [← (hs.iteratedFDeriv ℝ n).eq_of_nhds, hEq, L.iteratedFDeriv_comp_right hT _ (by simp),
    iteratedFDeriv_comp_add_left]
  simpa [R,L] using congrArg R heg

omit [Fact (Module.finrank ℝ (X dim) = dim - 1 + 1)] in
/-- Every ordered base and angular jet of a joint smooth kernel is bounded
uniformly on a compact parameter set times the two spheres. -/
theorem exists_compact_mixed_ambient_kernel_jet_bound
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {V C : Set P} (hV : IsOpen V) (hC : IsCompact C) (hCV : C ⊆ V)
    {F : P × (X dim × X dim) → ℂ} (hF : ContDiffOn ℝ ∞ F (V ×ˢ univ))
    (j k l : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ p ∈ C, ∀ w z : ↥(standardSphere dim),
      ‖iteratedFDeriv ℝ j (fun b => iteratedFDeriv ℝ k (fun w' =>
        iteratedFDeriv ℝ l (fun z' => F (b,(w',z'))) z.val) w.val) p‖ ≤ B := by
  let U : Set ((P × X dim) × X dim) := (V ×ˢ univ) ×ˢ univ
  have hU : IsOpen U := (hV.prod isOpen_univ).prod isOpen_univ
  let E (q : (P × X dim) × X dim) := (q.1.1,(q.1.2,q.2))
  have hE : ContDiff ℝ ∞ E := contDiff_fst.fst.prodMk (contDiff_fst.snd.prodMk contDiff_snd)
  have hFE : ContDiffOn ℝ ∞ (F ∘ E) U := hF.comp hE.contDiffOn (fun _ hq => ⟨hq.1.1,mem_univ _⟩)
  have hL := contDiffOn_partial_right_iteratedFDeriv hU hFE l
  let σ (q : (P × X dim) × X dim) := ((q.1.1,q.2),q.1.2)
  have hσ : ContDiff ℝ ∞ σ := (contDiff_fst.fst.prodMk contDiff_snd).prodMk contDiff_fst.snd
  have hL' : ContDiffOn ℝ ∞ (fun q : (P × X dim) × X dim =>
      iteratedFDeriv ℝ l (fun z' => F (q.1.1,(q.2,z'))) q.1.2) U :=
    hL.comp hσ.contDiffOn (fun _ hq => ⟨⟨hq.1.1,mem_univ _⟩,mem_univ _⟩)
  have hM := contDiffOn_partial_right_iteratedFDeriv hU hL' k
  let ι (q : (X dim × X dim) × P) := ((q.2,q.1.2),q.1.1)
  have hι : ContDiff ℝ ∞ ι := (contDiff_snd.prodMk contDiff_fst.snd).prodMk contDiff_fst.fst
  have hM' : ContDiffOn ℝ ∞ (fun q : (X dim × X dim) × P =>
      iteratedFDeriv ℝ k (fun w' => iteratedFDeriv ℝ l (fun z' => F (q.2,(w',z'))) q.1.2) q.1.1)
      (univ ×ˢ V) := hM.comp hι.contDiffOn (fun _ hq => ⟨⟨hq.2,mem_univ _⟩,mem_univ _⟩)
  have hJ := contDiffOn_partial_right_iteratedFDeriv (isOpen_univ.prod hV) hM' j
  let S : Set (X dim) := standardSphere dim
  have hS : IsCompact S := isCompact_sphere _ _
  have hSC : (S ×ˢ S) ×ˢ C ⊆ univ ×ˢ V := fun _ hq => ⟨mem_univ _,hCV hq.2⟩
  obtain ⟨B,hB⟩ := ((hS.prod hS).prod hC).exists_bound_of_continuousOn (hJ.continuousOn.mono hSC)
  refine ⟨max 1 B,lt_of_lt_of_le (by norm_num) (le_max_left _ _),fun p hp w z => ?_⟩
  exact (hB ((w.val,z.val),p) ⟨⟨w.property,z.property⟩,hp⟩).trans (le_max_right _ _)

end CalderonPaper
