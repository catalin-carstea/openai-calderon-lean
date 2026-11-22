module

public import Proof.CalderonN.Chart
public import Mathlib.Analysis.Calculus.Implicit
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

import Proof.CalderonN.EllipticCalculus
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic

@[expose] public section

/-! Tangent phase chart and compact chart cutoffs adopted from `MixedKernelPhaseChartsV021` from anisotropic-calderon-lean revision `d6704c49395a38eb07e0249afeb8ea83d67971cc`. -/

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff InnerProductSpace

namespace CalderonN.Elliptic.PhaseCoordinates

variable {dim : ℕ}


section Tangent
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- The transverse coordinate is the actual tangent Hilbert subspace. -/
private def tangentChartData (theta : E → ℝ) (ell : E →L[ℝ] ℝ) (p : E)
    [CompleteSpace ell.ker] (htheta : HasStrictFDerivAt theta ell p)
    (hell : ell ≠ 0) : ImplicitFunctionData ℝ E ℝ ell.ker := by
  let P := ell.ker.orthogonalProjectionOnto
  have hlinear : ell.toLinearMap ≠ 0 := by
    intro h
    apply hell
    ext x
    exact congrArg (fun f : E →ₗ[ℝ] ℝ => f x) h
  refine
    { leftFun := theta
      leftDeriv := ell
      rightFun := fun x => P (x-p)
      rightDeriv := P
      pt := p
      hasStrictFDerivAt_leftFun := htheta
      hasStrictFDerivAt_rightFun := ?_
      range_leftDeriv := ?_
      range_rightDeriv := ?_
      isCompl_ker := ?_ }
  · simpa using P.hasStrictFDerivAt.comp p ((hasStrictFDerivAt_id p).sub_const p)
  · exact Module.Dual.range_eq_top_of_ne_zero hlinear
  · apply LinearMap.range_eq_top.mpr
    intro z
    exact ⟨(z : E), Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (K := ell.ker) z⟩
  · change IsCompl ell.ker ell.ker.orthogonalProjectionOnto.ker
    rw [Submodule.ker_orthogonalProjectionOnto]
    exact ell.ker.isCompl_orthogonal

/-- Native phase is exactly the first coordinate; no PDE coordinate change. -/
theorem exists_tangent_phase_chart (theta : E → ℝ) (ell : E →L[ℝ] ℝ) (p : E)
    [CompleteSpace ell.ker] (htheta : HasStrictFDerivAt theta ell p)
    (hell : ell ≠ 0) :
    ∃ e : OpenPartialHomeomorph E (ℝ × ell.ker), p ∈ e.source ∧
      (∀ x, e x = (theta x, ell.ker.orthogonalProjectionOnto (x-p))) ∧
      (theta p, 0) ∈ e.target := by
  let D := tangentChartData theta ell p htheta hell
  refine ⟨D.toOpenPartialHomeomorph,
    D.pt_mem_toOpenPartialHomeomorph_source, ?_, ?_⟩
  · intro x
    rw [D.toOpenPartialHomeomorph_apply]
    rfl
  · have h := D.map_pt_mem_toOpenPartialHomeomorph_target
    change (theta p, ell.ker.orthogonalProjectionOnto (p - p)) ∈ D.toOpenPartialHomeomorph.target at h
    simpa only [sub_self, map_zero] using h

/-- A tangent chart with the specified forward map has a smooth inverse
as a germ at its centre. -/
theorem contDiffAt_tangent_chart_symm {θ : E → ℝ} (hθ : ContDiff ℝ ∞ θ)
    (p : E) (hzero : θ p = 0) (hell : fderiv ℝ θ p ≠ 0)
    [CompleteSpace (fderiv ℝ θ p).ker]
    (e : OpenPartialHomeomorph E (ℝ × (fderiv ℝ θ p).ker))
    (hpe : p ∈ e.source)
    (he : ∀ x, e x = (θ x, (fderiv ℝ θ p).ker.orthogonalProjectionOnto (x-p))) :
    ContDiffAt ℝ ∞ e.symm (0,0) := by
  let ell := fderiv ℝ θ p
  let D := tangentChartData θ ell p (hθ.contDiffAt.hasStrictFDerivAt (by simp)) hell
  let e' := D.toOpenPartialHomeomorph
  have hmap (x : E) : e' x = e x := by
    rw [he, D.toOpenPartialHomeomorph_apply]
    rfl
  have h₀ : e p = (0,0) := by rw [he, hzero, sub_self, map_zero]
  have hp' : p ∈ e'.source := D.pt_mem_toOpenPartialHomeomorph_source
  have ht' : (0,0) ∈ e'.target := by rw [← h₀, ← hmap]; exact e'.map_source hp'
  have ht : (0,0) ∈ e.target := by rw [← h₀]; exact e.map_source hpe
  have hz : e'.symm (0,0) = p := by rw [← h₀, ← hmap]; exact e'.left_inv hp'
  have hd : ContDiffAt ℝ ∞ e'.symm (0,0) := by
    have hl : ContDiffAt ℝ ∞ D.leftFun D.pt := hθ.contDiffAt
    have hr : ContDiffAt ℝ ∞ D.rightFun D.pt :=
      (ell.ker.orthogonalProjectionOnto.contDiff.comp (contDiff_id.sub contDiff_const)).contDiffAt
    have h := D.contDiffAt_implicitFunction hl hr (by simp)
    have hi : D.implicitFunction.uncurry = e'.symm := funext fun q => D.implicitFunction_apply
    have hp : D.prodFun D.pt = e' p := (congrFun D.toOpenPartialHomeomorph_coe p).symm
    rwa [hi, hp, hmap, h₀] at h
  have hnear : ∀ᶠ z in 𝓝 (0,0), e'.symm z ∈ e.source := by
    have hm : e'.symm (0,0) ∈ e.source := hz.symm ▸ hpe
    exact hd.continuousAt (e.open_source.mem_nhds hm)
  apply hd.congr_of_eventuallyEq
  filter_upwards [hnear, e'.open_target.mem_nhds ht', e.open_target.mem_nhds ht] with z hz hz' hze
  exact (e.injOn hz (e.map_target hze) (by rw [← hmap, e'.right_inv hz', e.right_inv hze])).symm

end Tangent

variable {E : Type*} [TopologicalSpace E]

/-- Compact chart boxes are lifted by the continuous inverse on its target. -/
theorem isCompact_inverse_chart_image {F : Type*} [TopologicalSpace F]
    (e : OpenPartialHomeomorph E F) {B : Set F} (hB : IsCompact B)
    (hBt : B ⊆ e.target) : IsCompact (e.symm '' B) := by
  exact hB.image_of_continuousOn (e.continuousOn_symm.mono hBt)

/-- The lifted box stays inside the native chart source. -/
theorem inverse_chart_image_subset_source {F : Type*} [TopologicalSpace F]
    (e : OpenPartialHomeomorph E F) {B : Set F} (hBt : B ⊆ e.target) :
    e.symm '' B ⊆ e.source := by
  rintro x ⟨y, hy, rfl⟩
  exact e.map_target (hBt hy)

/-- Image description prevents an unjustified global properness inference. -/
theorem inverse_chart_image_eq {F : Type*} [TopologicalSpace F]
    (e : OpenPartialHomeomorph E F) {B : Set F} (hBt : B ⊆ e.target) :
    e.symm '' B = {x ∈ e.source | e x ∈ B} := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨e.map_target (hBt hy), ?_⟩
    simpa only [e.right_inv (hBt hy)] using hy
  · rintro ⟨hxs, hxB⟩
    exact ⟨e x, hxB, e.left_inv hxs⟩


/-- The outer native plateau contributes no extra transition residual. -/
theorem exists_chart_supported_cutoff {F : Type*} [TopologicalSpace F]
    (e : OpenPartialHomeomorph (X dim) F) {B : Set F}
    (hB : IsCompact B) (hBt : B ⊆ e.target) (f : (X dim) → ℝ)
    (hf : ContDiff ℝ ∞ f)
    (hformula : ∀ x ∈ e.source, f x ≠ 0 → e x ∈ B) :
    ∃ chi : (X dim) → ℝ, ContDiff ℝ ∞ chi ∧ HasCompactSupport chi ∧
      tsupport chi ⊆ e.symm '' B ∧
      (∀ x ∈ e.symm '' B, chi =ᶠ[nhds x] f) ∧
      (∀ x ∉ e.symm '' B, chi =ᶠ[nhds x] fun _ => (0 : ℝ)) := by
  let K := e.symm '' B
  have hK : IsCompact K := isCompact_inverse_chart_image e hB hBt
  have hKsource : K ⊆ e.source := inverse_chart_image_subset_source e hBt
  obtain ⟨zeta, hz, _, hzsource, hz1⟩ :=
    CalderonN.Elliptic.exists_plateau_cutoff e.open_source hK hKsource
  let chi : (X dim) → ℝ := fun x => zeta x * f x
  have hsupp : Function.support chi ⊆ K := by
    intro x hx
    have hxmul : zeta x * f x ≠ 0 := hx
    have hz0 : zeta x ≠ 0 := (mul_ne_zero_iff.mp hxmul).1
    have hf0 : f x ≠ 0 := (mul_ne_zero_iff.mp hxmul).2
    have hxs : x ∈ e.source := hzsource (subset_tsupport zeta hz0)
    exact ⟨e x, hformula x hxs hf0, e.left_inv hxs⟩
  have ht : tsupport chi ⊆ K := closure_minimal hsupp hK.isClosed
  refine ⟨chi, hz.mul hf, hK.of_isClosed_subset (isClosed_tsupport chi) ht, ht, ?_, ?_⟩
  · intro x hx
    filter_upwards [hz1 x hx] with y hy
    simp only [chi, hy, one_mul]
  · intro x hx
    exact notMem_tsupport_iff_eventuallyEq.mp (fun h => hx (ht h))

/-! B1–B3: the actual centred tangent box
and the height/lateral formula with the literal Hilbert transverse norm squared. -/

/-- B1: centred boxes of small half-widths lie in an open chart target. -/
theorem exists_box_subset_target {E₀ K : Type*} [TopologicalSpace E₀] [NormedAddCommGroup K]
    (e : OpenPartialHomeomorph E₀ (ℝ × K)) (h0 : ((0 : ℝ), (0 : K)) ∈ e.target) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ a r : ℝ, a ≤ ρ → r ≤ ρ →
      Icc (-a) a ×ˢ Metric.closedBall (0 : K) r ⊆ e.target := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp e.open_target _ h0
  refine ⟨ε / 2, half_pos hε, fun a r ha hr => ?_⟩
  rintro ⟨s, z⟩ ⟨hs, hz⟩
  apply hball
  rw [Metric.mem_ball, Prod.dist_eq]
  have h1 : dist s 0 ≤ a := by
    rw [Real.dist_eq, sub_zero]
    exact abs_le.mpr hs
  have h2 : dist z 0 ≤ r := Metric.mem_closedBall.mp hz
  exact max_lt (by linarith) (by linarith)

/-- B1: the box is compact (finite-dimensional transverse space). -/
theorem isCompact_box {K : Type*} [NormedAddCommGroup K] [ProperSpace K] (a r : ℝ) :
    IsCompact (Icc (-a) a ×ˢ Metric.closedBall (0 : K) r) :=
  isCompact_Icc.prod (isCompact_closedBall 0 r)

/-- B2: scalar support of the height/lateral formula puts the chart value in the box. -/
theorem tangent_formula_mem_box {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (theta : E → ℝ) (ell : E →L[ℝ] ℝ) (p : E) [CompleteSpace ell.ker]
    {α β : ℝ → ℝ} {a r : ℝ} (hr : 0 ≤ r)
    (hα : ∀ s, α s ≠ 0 → |s| ≤ a) (hβ : ∀ t, β t ≠ 0 → t ≤ r ^ 2) (x : E)
    (hx : α (theta x) * β (‖ell.ker.orthogonalProjectionOnto (x - p)‖ ^ 2) ≠ 0) :
    (theta x, ell.ker.orthogonalProjectionOnto (x - p)) ∈
      Icc (-a) a ×ˢ Metric.closedBall (0 : ell.ker) r := by
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp hx
  refine ⟨abs_le.mp (hα _ h1), ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  have h3 := hβ _ h2
  by_contra hlt
  push Not at hlt
  nlinarith [norm_nonneg (ell.ker.orthogonalProjectionOnto (x - p))]

/-- B3: the height/lateral formula is globally smooth. -/
theorem contDiff_tangent_formula {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {theta : E → ℝ} (htheta : ContDiff ℝ ∞ theta) (ell : E →L[ℝ] ℝ) (p : E)
    [CompleteSpace ell.ker] {α β : ℝ → ℝ} (hα : ContDiff ℝ ∞ α) (hβ : ContDiff ℝ ∞ β) :
    ContDiff ℝ ∞ (fun x => α (theta x) * β (‖ell.ker.orthogonalProjectionOnto (x - p)‖ ^ 2)) :=
  (hα.comp htheta).mul (hβ.comp ((contDiff_norm_sq ℝ).comp
    (ell.ker.orthogonalProjectionOnto.contDiff.comp (contDiff_id.sub contDiff_const))))

/-- B1–B3 assembled on the ACTUAL tangent chart of a smooth native phase with
`θ p = 0`, `dθ p ≠ 0`: for every small box and every pair of smooth scalar cutoffs with
the box supports, a globally smooth compactly supported `χ` equal to the literal formula
as germs on `K = e.symm '' B` and with zero germs off `K`. -/
theorem exists_tangent_box_cutoff {theta : (X dim) → ℝ} (htheta : ContDiff ℝ ∞ theta) (p : (X dim))
    (h0 : theta p = 0) (hell : fderiv ℝ theta p ≠ 0) :
    ∃ e : OpenPartialHomeomorph (X dim) (ℝ × (fderiv ℝ theta p).ker), p ∈ e.source ∧
      (∀ x, e x = (theta x, (fderiv ℝ theta p).ker.orthogonalProjectionOnto (x - p))) ∧
      ∃ ρ : ℝ, 0 < ρ ∧ ∀ a r : ℝ, a ≤ ρ → 0 ≤ r → r ≤ ρ →
        Icc (-a) a ×ˢ Metric.closedBall (0 : (fderiv ℝ theta p).ker) r ⊆ e.target ∧
        ∀ α β : ℝ → ℝ, ContDiff ℝ ∞ α → ContDiff ℝ ∞ β →
          (∀ s, α s ≠ 0 → |s| ≤ a) → (∀ t, β t ≠ 0 → t ≤ r ^ 2) →
          ∃ chi : (X dim) → ℝ, ContDiff ℝ ∞ chi ∧ HasCompactSupport chi ∧
            tsupport chi ⊆ e.symm '' (Icc (-a) a ×ˢ Metric.closedBall 0 r) ∧
            (∀ x ∈ e.symm '' (Icc (-a) a ×ˢ Metric.closedBall 0 r),
              chi =ᶠ[nhds x] fun y => α (theta y) *
                β (‖(fderiv ℝ theta p).ker.orthogonalProjectionOnto (y - p)‖ ^ 2)) ∧
            (∀ x ∉ e.symm '' (Icc (-a) a ×ˢ Metric.closedBall 0 r),
              chi =ᶠ[nhds x] fun _ => (0 : ℝ)) := by
  have hstrict : HasStrictFDerivAt theta (fderiv ℝ theta p) p :=
    htheta.contDiffAt.hasStrictFDerivAt (by simp)
  obtain ⟨e, hpe, he, hpt⟩ := exists_tangent_phase_chart theta (fderiv ℝ theta p) p hstrict hell
  rw [h0] at hpt
  obtain ⟨ρ, hρ, hbox⟩ := exists_box_subset_target e hpt
  refine ⟨e, hpe, he, ρ, hρ, fun a r ha hr0 hr => ⟨hbox a r ha hr, ?_⟩⟩
  intro α β hα hβ hαs hβs
  exact exists_chart_supported_cutoff e (isCompact_box a r) (hbox a r ha hr) _
    (contDiff_tangent_formula htheta _ p hα hβ)
    (fun x _ hx => by
      rw [he x]
      exact tangent_formula_mem_box theta _ p hr0 hαs hβs x hx)


/-- W3: the chart centre. -/
theorem chart_symm_zero {K : Type*} [NormedAddCommGroup K]
    (e : OpenPartialHomeomorph (X dim) (ℝ × K)) {θ : (X dim) → ℝ} {P : (X dim) → K} {p : (X dim)}
    (he : ∀ x, e x = (θ x, P (x - p))) (hP0 : P 0 = 0) (h0 : θ p = 0) (hpe : p ∈ e.source) :
    e.symm ((0 : ℝ), (0 : K)) = p ∧ ((0 : ℝ), (0 : K)) ∈ e.target := by
  have h : e p = ((0 : ℝ), (0 : K)) := by rw [he, sub_self, hP0, h0]
  exact ⟨by rw [← h]; exact e.left_inv hpe, by rw [← h]; exact e.map_source hpe⟩

/-- W3: small centred boxes lift into any native ball around the centre. -/
theorem exists_box_image_subset_ball {K : Type*} [NormedAddCommGroup K]
    (e : OpenPartialHomeomorph (X dim) (ℝ × K)) {p : (X dim)} (hp0 : e.symm ((0 : ℝ), (0 : K)) = p)
    (h0t : ((0 : ℝ), (0 : K)) ∈ e.target) {r : ℝ} (hr : 0 < r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ρ' : ℝ, ρ' < δ →
      Set.Icc (-ρ') ρ' ×ˢ Metric.closedBall (0 : K) ρ' ⊆ e.target →
      e.symm '' (Set.Icc (-ρ') ρ' ×ˢ Metric.closedBall (0 : K) ρ') ⊆ Metric.ball p r := by
  obtain ⟨δ, hδ, H⟩ := Metric.continuousWithinAt_iff.mp (e.continuousOn_symm _ h0t) r hr
  refine ⟨δ, hδ, fun ρ' hρ' hbt => ?_⟩
  rintro x ⟨⟨s, z⟩, ⟨hs, hz⟩, rfl⟩
  have hd : dist (s, z) ((0 : ℝ), (0 : K)) < δ := by
    rw [Prod.dist_eq]
    have h1 : dist s 0 ≤ ρ' := by
      rw [Real.dist_eq, sub_zero]
      exact abs_le.mpr hs
    have h2 : dist z 0 ≤ ρ' := Metric.mem_closedBall.mp hz
    exact max_lt (by linarith) (by linarith)
  have h := H (hbt ⟨hs, hz⟩) hd
  rw [hp0] at h
  exact h


end CalderonN.Elliptic.PhaseCoordinates
