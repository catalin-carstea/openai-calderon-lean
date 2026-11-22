module

public import Proof.CalderonPatch.CompactSecondJet
public import Proof.CalderonPatch.ChartTranslation

import Proof.CalderonN.MetricCalculus
import Proof.CalderonN.ChartGeometry
import Proof.CalderonN.TraceFrameCoefficients

public section

noncomputable section
open Filter Matrix Set
open scoped ContDiff Topology

namespace CalderonPatch

open CalderonN (I X Mat MetricField axis axis_sum_chart coordDeriv hessian)

variable {n : ℕ} {U : Set (X n)}

/-- The open-chart smooth scalar functions, with their ordinary linear operations. -/
@[expose] def openChartScalars (U : Set (X n)) : Submodule ℝ (X n → ℝ) where
  carrier := {f | ContDiffOn ℝ ∞ f U}
  zero_mem' := contDiffOn_const
  add_mem' hf hg := hf.add hg
  smul_mem' c {_f} hf := hf.const_smul c

private def openChartPartial (hU : IsOpen U) (i : I n) :
    openChartScalars U →ₗ[ℝ] openChartScalars U where
  toFun f := ⟨U.indicator (coordDeriv i f), (CalderonN.contDiffOn_coordDeriv f.property hU i).congr
    (fun _ hx => indicator_of_mem hx _)⟩
  map_add' f g := by
    apply Subtype.ext
    funext x
    change U.indicator (coordDeriv i ((f : X n → ℝ) + (g : X n → ℝ))) x =
      U.indicator (coordDeriv i (f : X n → ℝ)) x + U.indicator (coordDeriv i (g : X n → ℝ)) x
    by_cases hx : x ∈ U
    · simp only [indicator_of_mem hx, coordDeriv]
      rw [fderiv_add ((f.property.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))
        ((g.property.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))]
      rfl
    · simp [indicator_of_notMem hx]
  map_smul' c f := by
    apply Subtype.ext
    funext x
    change U.indicator (coordDeriv i (c • (f : X n → ℝ))) x = c * U.indicator (coordDeriv i f) x
    by_cases hx : x ∈ U
    · simp only [indicator_of_mem hx, coordDeriv]
      rw [fderiv_const_smul ((f.property.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))]
      rfl
    · simp [indicator_of_notMem hx]

private def openChartEval (x : X n) : openChartScalars U →ₗ[ℝ] ℝ :=
  (LinearMap.proj x).comp (openChartScalars U).subtype

private theorem openChartPartial_eqOn (hU : IsOpen U) (i : I n) (f : openChartScalars U) :
    EqOn ((openChartPartial hU i f : openChartScalars U) : X n → ℝ) (coordDeriv i f) U :=
  fun _ hx => indicator_of_mem hx _

private def openChartHessian (hU : IsOpen U) (x : X n) : openChartScalars U →ₗ[ℝ] Mat n :=
  LinearMap.pi fun i => LinearMap.pi fun j =>
    (openChartEval x).comp ((openChartPartial hU i).comp (openChartPartial hU j))

private theorem openChartHessian_eq (hU : IsOpen U) {x : X n} (hx : x ∈ U) (f : openChartScalars U) :
    openChartHessian hU x f = hessian f x := by
  ext i j
  change (openChartPartial hU i (openChartPartial hU j f) : openChartScalars U).val x = _
  rw [openChartPartial_eqOn hU i _ hx]
  exact CalderonN.eqOn_coordDeriv hU (openChartPartial_eqOn hU j f) i hx

variable [NeZero n]

/-- Actual chart jets depend linearly on the smooth input function. -/
def openChartSecondJet (hU : IsOpen U) {x : X n} (hx : x ∈ U) : openChartScalars U →ₗ[ℝ] ScalarSecondJet n :=
  (openChartEval x).prod ((LinearMap.pi fun i => (openChartEval x).comp (openChartPartial hU i)).prod
    ((openChartHessian hU x).codRestrict (symmetricHessians n) fun f => by
      change (openChartHessian hU x f).transpose = openChartHessian hU x f
      rw [openChartHessian_eq hU hx f]
      exact CalderonN.hessian_transpose hU f.property hx))

@[simp]
theorem openChartSecondJet_apply (hU : IsOpen U) {x : X n} (hx : x ∈ U) (f : openChartScalars U) :
    openChartSecondJet hU hx f = smoothSecondJet hU hx f f.property := by
  refine Prod.ext rfl (Prod.ext (funext fun i => openChartPartial_eqOn hU i f hx)
    (Subtype.ext (openChartHessian_eq hU hx f)))

variable {F : Type*} [AddCommGroup F] [Module ℝ F]

/-- The jet map of any linear source solution family in one chart. -/
def sourceSecondJet (hU : IsOpen U) {x : X n} (hx : x ∈ U) (u : F →ₗ[ℝ] (X n → ℝ))
    (hu : ∀ a, ContDiffOn ℝ ∞ (u a) U) : F →ₗ[ℝ] ScalarSecondJet n :=
  (openChartSecondJet hU hx).comp (u.codRestrict (openChartScalars U) hu)

@[simp]
theorem sourceSecondJet_apply (hU : IsOpen U) {x : X n} (hx : x ∈ U) (u : F →ₗ[ℝ] (X n → ℝ))
    (hu : ∀ a, ContDiffOn ℝ ∞ (u a) U) (a : F) : sourceSecondJet hU hx u hu a = smoothSecondJet hU hx (u a) (hu a) :=
  openChartSecondJet_apply hU hx ⟨u a, hu a⟩

/-- Recenter the base point without changing the ordinary jet in the
translated basis. -/
theorem smoothSecondJet_translate (hU : IsOpen U) {x : X n} (hx : x ∈ U) {f : X n → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) :
    smoothSecondJet (hU.preimage (continuous_const.add continuous_id))
      (show (0 : X n) ∈ (x + ·) ⁻¹' U by simpa using hx)
      (fun y => f (x + y)) (hf.comp (contDiff_const.add contDiff_id).contDiffOn (fun _ hy => hy)) =
        smoothSecondJet hU hx f hf := by
  refine Prod.ext (by change f (x + 0) = f x; rw [add_zero]) (Prod.ext (funext fun i => ?_)
    (Subtype.ext ?_))
  · change fderiv ℝ (fun y => f (x + y)) 0 (axis i) = fderiv ℝ f x (axis i)
    rw [fderiv_comp_add_left, add_zero]
  · change hessian (fun y => f (x + y)) 0 = hessian f x
    rw [hessian_translate, add_zero]

/-- A full harmonic jet range realizes every continuous covector as
the first derivative of a member of the source family. -/
theorem exists_source_fderiv_of_harmonicJetRange (hU : IsOpen U) {x : X n} (hx : x ∈ U)
    {γ : MetricField n} (hγ : (γ x).PosDef) (u : F →ₗ[ℝ] (X n → ℝ))
    (hu : ∀ a, ContDiffOn ℝ ∞ (u a) U)
    (hRange : (sourceSecondJet hU hx u hu).range = (laplaceOnSecondJet γ x).ker)
    (D : X n →L[ℝ] ℝ) : ∃ a, fderiv ℝ (u a) x = D := by
  obtain ⟨v, hv, hH⟩ := exists_harmonicJet_with_first γ x hγ (fun i => D (axis i))
  obtain ⟨a, ha⟩ := LinearMap.mem_range.mp (hRange.symm ▸ LinearMap.mem_ker.mpr hH)
  have hh (i : I n) : fderiv ℝ (u a) x (axis i) = D (axis i) := by
    have h := congrArg (fun w : ScalarSecondJet n => w.2.1 i) ha
    rw [sourceSecondJet_apply] at h
    change fderiv ℝ (u a) x (axis i) = v.2.1 i at h
    exact h.trans (congrFun hv i)
  refine ⟨a, ContinuousLinearMap.ext (fun v => ?_)⟩
  rw [← axis_sum_chart v, map_sum, map_sum]
  simp only [map_smul, hh]

/-- In harmonic coordinates the Hessians of the source family span
exactly the trace-zero symmetric hyperplane. -/
theorem hessianSpan_of_harmonicJetRange (hU : IsOpen U) {x : X n} (hx : x ∈ U)
    {γ : MetricField n} (hchart : CalderonN.HarmonicCoordinates U γ) (u : F →ₗ[ℝ] (X n → ℝ))
    (hu : ∀ a, ContDiffOn ℝ ∞ (u a) U)
    (hRange : (sourceSecondJet hU hx u hu).range = (laplaceOnSecondJet γ x).ker) (A : Mat n) :
    A ∈ Submodule.span ℝ (range fun a => hessian (u a) x) ↔
      A.transpose = A ∧ ((γ x)⁻¹ * A).trace = 0 := by
  let H := secondJetHessian.comp (sourceSecondJet hU hx u hu)
  have hH (a : F) : H a = hessian (u a) x := by
    rw [show H a = secondJetHessian (sourceSecondJet hU hx u hu a) from rfl, sourceSecondJet_apply]
    rfl
  rw [show (fun a => hessian (u a) x) = H from funext fun a => (hH a).symm,
    ← LinearMap.coe_range, Submodule.span_eq]
  constructor
  · rintro ⟨a, rfl⟩
    have hL : laplaceOnSecondJet γ x (sourceSecondJet hU hx u hu a) = 0 :=
      LinearMap.mem_ker.mp (hRange ▸ LinearMap.mem_range_self _ a)
    rw [sourceSecondJet_apply, smoothSecondJet_laplace] at hL
    have hSym := CalderonN.hessian_transpose hU (hu a) hx
    rw [hH a]
    refine ⟨hSym, ?_⟩
    rw [← hSym]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
    exact (CalderonN.laplace_eq_hessian_contraction hchart hx (u a)).symm.trans hL
  · rintro ⟨hSym, hTrace⟩
    let v : ScalarSecondJet n := (0, 0, ⟨A, hSym⟩)
    have hv : laplaceOnSecondJet γ x v = 0 := (laplaceOnSecondJet_zero_first γ x 0 ⟨A, hSym⟩).trans hTrace
    obtain ⟨a, ha⟩ := LinearMap.mem_range.mp (hRange.symm ▸ LinearMap.mem_ker.mpr hv)
    exact LinearMap.mem_range.mpr ⟨a, congrArg secondJetHessian ha⟩

end CalderonPatch
