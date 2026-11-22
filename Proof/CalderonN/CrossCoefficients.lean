module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

import Mathlib.Tactic

/-! The restriction-basis coefficient functional used in Section 3.2.
Adapted from `Calderon/MixedKernelConstruction/C3Coefficients.lean` at
d6704c49395a38eb07e0249afeb8ea83d67971cc. -/

@[expose] public section

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace LocalMetricExtension
attribute [local instance] Classical.propDecidable

section CoefficientOperator
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  (R : E →L[ℝ] F) {ι : Type*} (w : ι → E) (μ : ι → ℝ)

/-- The actual real-valued coefficient functional from cross:coefficient-extension. -/
def singularCoefficient (i : ι) : F →L[ℝ] ℝ :=
  (μ i ^ 2)⁻¹ • innerSL ℝ (R (w i))

@[simp] theorem singularCoefficient_apply (i : ι) (G : F) :
    singularCoefficient R w μ i G = (μ i ^ 2)⁻¹ * inner ℝ (R (w i)) G := by
  rfl

theorem singularCoefficient_norm_le (hμ : ∀ i, 0 < μ i)
    (hgram : ∀ i j, inner ℝ (R (w i)) (R (w j)) = if i = j then μ i ^ 2 else 0)
    (i : ι) : ‖singularCoefficient R w μ i‖ ≤ (μ i)⁻¹ := by
  have hnorm : ‖R (w i)‖ = μ i := by
    apply (sq_eq_sq₀ (norm_nonneg _) (hμ i).le).mp
    calc
      ‖R (w i)‖ ^ 2 = inner ℝ (R (w i)) (R (w i)) :=
        (real_inner_self_eq_norm_sq _).symm
      _ = μ i ^ 2 := by rw [hgram, ite_eq_left rfl]
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr (hμ i).le)
  intro G
  change |(μ i ^ 2)⁻¹ * inner ℝ (R (w i)) G| ≤ _
  calc
    _ = (μ i ^ 2)⁻¹ * |inner ℝ (R (w i)) G| := by
      rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg _))]
    _ ≤ (μ i ^ 2)⁻¹ * (‖R (w i)‖ * ‖G‖) :=
      mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (inv_nonneg.mpr (sq_nonneg _))
    _ = (μ i)⁻¹ * ‖G‖ := by
      rw [hnorm]
      field_simp

/-- Actual measurable L2 coefficient family, constructed using the pointwise Lp action. -/
def singularCoefficientLp {Y : Type*} [MeasurableSpace Y] (ν : Measure Y)
    (Q : Lp F 2 ν) (i : ι) : Lp ℝ 2 ν :=
  (singularCoefficient R w μ i).compLp Q

theorem singularCoefficientLp_ae {Y : Type*} [MeasurableSpace Y] (ν : Measure Y)
    (Q : Lp F 2 ν) (i : ι) :
    (singularCoefficientLp R w μ ν Q i : Y → ℝ) =ᵐ[ν]
      fun y => (μ i ^ 2)⁻¹ * inner ℝ (R (w i)) (Q y) :=
  (singularCoefficient R w μ i).coeFn_compLp Q

theorem singularCoefficientLp_norm_le {Y : Type*} [MeasurableSpace Y] (ν : Measure Y)
    (Q : Lp F 2 ν) (hμ : ∀ i, 0 < μ i)
    (hgram : ∀ i j, inner ℝ (R (w i)) (R (w j)) = if i = j then μ i ^ 2 else 0)
    (i : ι) : ‖singularCoefficientLp R w μ ν Q i‖ ≤ (μ i)⁻¹ * ‖Q‖ := by
  exact ((singularCoefficient R w μ i).norm_compLp_le Q).trans
    (mul_le_mul_of_nonneg_right (singularCoefficient_norm_le R w μ hμ hgram i)
      (norm_nonneg Q))

variable [CompleteSpace E] [CompleteSpace F]

/-- Agreement on the actual restriction range, by the SAME eigen equation. -/
theorem singularCoefficient_restrict (hμ : ∀ i, 0 < μ i)
    (heigen : ∀ i, (ContinuousLinearMap.adjoint R ∘L R) (w i) = μ i ^ 2 • w i)
    (u : E) (i : ι) : singularCoefficient R w μ i (R u) = inner ℝ (w i) u := by
  rw [singularCoefficient_apply, ← R.adjoint_inner_left u (R (w i))]
  change (μ i ^ 2)⁻¹ * inner ℝ ((ContinuousLinearMap.adjoint R ∘L R) (w i)) u = _
  rw [heigen, real_inner_smul_left, ← mul_assoc,
    inv_mul_cancel₀ (pow_ne_zero 2 (hμ i).ne'), one_mul]

/-- Reconstruction is only claimed on the actual range of R. -/
theorem hasSum_singularCoefficient_restrict (b : HilbertBasis ι ℝ E)
    (hwb : ∀ i, w i = b i) (hμ : ∀ i, 0 < μ i)
    (heigen : ∀ i, (ContinuousLinearMap.adjoint R ∘L R) (w i) = μ i ^ 2 • w i)
    (u : E) : HasSum (fun i => singularCoefficient R w μ i (R u) • R (w i)) (R u) := by
  have hs := R.hasSum (b.hasSum_repr u)
  simpa only [map_smul, b.repr_apply_apply, singularCoefficient_restrict R w μ hμ heigen,
    hwb] using hs

omit [CompleteSpace E] in
/-- The same coefficients reconstruct elements of the closed restriction
range. This uses completeness of the normalized restricted basis. -/
theorem hasSum_singularCoefficient_closure (w : HilbertBasis ι ℝ E)
    (hμ : ∀ i, 0 < μ i)
    (hgram : ∀ i j, inner ℝ (R (w i)) (R (w j)) = if i = j then μ i ^ 2 else 0)
    {z : F} (hz : z ∈ closure (Set.range R)) :
    HasSum (fun i => singularCoefficient R w μ i z • R (w i)) z := by
  classical
  let e (i : ι) := (μ i)⁻¹ • R (w i)
  let V := (Submodule.span ℝ (Set.range e)).topologicalClosure
  have hV : IsClosed (V : Set F) := Submodule.isClosed_topologicalClosure _
  let : CompleteSpace V := hV.completeSpace_coe
  let eV (i : ι) : V := ⟨e i, Submodule.le_topologicalClosure _
    (Submodule.subset_span ⟨i, rfl⟩)⟩
  have hnorm : Orthonormal ℝ eV := by
    rw [orthonormal_iff_ite]
    intro i j
    change inner ℝ (e i) (e j) = _
    simp only [e, real_inner_smul_left, real_inner_smul_right, hgram]
    split
    next he =>
      subst j
      field_simp [(hμ i).ne']
    next => ring
  have hBot : (Submodule.span ℝ (Set.range eV))ᗮ = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have horth (i : ι) : inner ℝ (e i) (x : F) = 0 :=
      (Submodule.mem_orthogonal _ x).mp hx (eV i) (Submodule.subset_span ⟨i, rfl⟩)
    let L := innerSL ℝ (x : F)
    have hsub : Submodule.span ℝ (Set.range e) ≤ L.ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact LinearMap.mem_ker.mpr (inner_eq_zero_symm.mp (horth i))
    have hker : V ≤ L.ker := Submodule.topologicalClosure_minimal _ hsub L.isClosed_ker
    have hzero : inner ℝ (x : F) (x : F) = 0 := hker x.property
    have hxz : x = 0 := Subtype.ext (inner_self_eq_zero.mp hzero)
    rw [hxz]
    exact Submodule.zero_mem _
  have hR : Set.range R ⊆ V := by
    rintro _ ⟨u, rfl⟩
    have hh := R.hasSum (w.hasSum_repr u)
    apply hV.mem_of_tendsto hh
    refine Eventually.of_forall fun J => Submodule.sum_mem _ fun i _ => ?_
    rw [map_smul]
    apply Submodule.smul_mem
    have heq : μ i • e i = R (w i) := by
      dsimp only [e]
      rw [smul_smul, mul_inv_cancel₀ (hμ i).ne', one_smul]
    rw [← heq]
    exact Submodule.smul_mem _ _ (eV i).property
  have hzV : z ∈ V := closure_minimal hR hV hz
  let b : HilbertBasis ι ℝ V := HilbertBasis.mkOfOrthogonalEqBot hnorm hBot
  have hb (i : ι) : b i = eV i := congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot hnorm hBot) i
  have h := V.subtypeL.hasSum (b.hasSum_repr ⟨z, hzV⟩)
  change HasSum (fun i => V.subtypeL (b.repr ⟨z, hzV⟩ i • b i)) z at h
  convert h using 1
  funext i
  simp only [map_smul, b.repr_apply_apply, hb, Submodule.subtypeL_apply, singularCoefficient_apply]
  change ((μ i ^ 2)⁻¹ * inner ℝ (R (w i)) z) • R (w i) = inner ℝ (e i) z • e i
  simp only [e, real_inner_smul_left, smul_smul, pow_two]
  congr 1
  ring

end CoefficientOperator

end LocalMetricExtension
