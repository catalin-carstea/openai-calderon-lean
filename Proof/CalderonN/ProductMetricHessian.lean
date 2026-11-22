module

public import Proof.CalderonN.ChartBilinear
public import Proof.CalderonN.ProductPhaseAlgebra
public import Mathlib.LinearAlgebra.Basis.Prod

import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Proof.CalderonN.MetricPair
import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set Matrix
open scoped ContDiff

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

/-- The Hessian of the defining function for the product Levi-Civita
connection of the two actual chart metrics. -/
@[expose] def productMetricHessian (g₁ g₂ : (MetricField dim)) (ρ : (X dim) × (X dim) → ℝ)
    (z v w : (X dim) × (X dim)) : ℝ :=
  fderiv ℝ (fderiv ℝ ρ) z v w -
    fderiv ℝ ρ z (connection g₁ z.1 v.1 w.1, connection g₂ z.2 v.2 w.2)

theorem fderiv_product_split (d : (X dim) × (X dim) →L[ℝ] ℝ) (v : (X dim) × (X dim)) :
    d v = d (v.1,0) + d (0,v.2) :=
  (d.comp_inl_add_comp_inr v).symm

theorem fderiv_product_slices (ρ : (X dim) × (X dim) → ℝ) (z : (X dim) × (X dim))
    (hρ : DifferentiableAt ℝ ρ z) :
    fderiv ℝ (fun x => ρ (x,z.2)) z.1 = (fderiv ℝ ρ z).comp (ContinuousLinearMap.inl ℝ (X dim) (X dim)) ∧
    fderiv ℝ (fun y => ρ (z.1,y)) z.2 = (fderiv ℝ ρ z).comp (ContinuousLinearMap.inr ℝ (X dim) (X dim)) := by
  let L := ContinuousLinearMap.inl ℝ (X dim) (X dim)
  let R := ContinuousLinearMap.inr ℝ (X dim) (X dim)
  have hL : HasFDerivAt (fun x : (X dim) => (x,z.2)) L z.1 := (hasFDerivAt_id z.1).prodMk (hasFDerivAt_const z.2 z.1)
  have hR : HasFDerivAt (fun y : (X dim) => (z.1,y)) R z.2 := (hasFDerivAt_const z.1 z.2).prodMk (hasFDerivAt_id z.2)
  have hl : HasFDerivAt (fun x => ρ (x,z.2)) ((fderiv ℝ ρ z).comp L) z.1 :=
    hρ.hasFDerivAt.comp z.1 hL
  have hr : HasFDerivAt (fun y => ρ (z.1,y)) ((fderiv ℝ ρ z).comp R) z.2 :=
    hρ.hasFDerivAt.comp z.2 hR
  exact ⟨hl.fderiv,hr.fderiv⟩

theorem slice_coordDeriv (ρ : (X dim) × (X dim) → ℝ) (z : (X dim) × (X dim))
    (hρ : DifferentiableAt ℝ ρ z) (i : (I dim)) :
    coordDeriv i (fun x => ρ (x,z.2)) z.1 = fderiv ℝ ρ z (axis i,0) ∧
    coordDeriv i (fun y => ρ (z.1,y)) z.2 = fderiv ℝ ρ z (0,axis i) := by
  obtain ⟨h₁,h₂⟩ := fderiv_product_slices ρ z hρ
  unfold coordDeriv
  rw [h₁,h₂]
  exact ⟨rfl,rfl⟩

theorem productMetricHessian_smul_self (g₁ g₂ : (MetricField dim)) (φ : (X dim) × (X dim) → ℝ)
    (p u : (X dim) × (X dim)) (s : ℝ) :
    productMetricHessian g₁ g₂ φ p (s • u) (s • u) =
      s^2 * productMetricHessian g₁ g₂ φ p u u := by
  have hc (g : (MetricField dim)) (x v : (X dim)) :
      connection g x (s • v) (s • v) = s^2 • connection g x v v := by
    ext i
    simp only [connection, PiLp.toLp_apply, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  have hp : (connection g₁ p.1 (s • u.1) (s • u.1),connection g₂ p.2 (s • u.2) (s • u.2)) =
      s^2 • (connection g₁ p.1 u.1 u.1,connection g₂ p.2 u.2 u.2) := by rw [hc,hc]; rfl
  simp only [productMetricHessian,Prod.smul_fst,Prod.smul_snd,hp,map_smul,
    _root_.smul_apply,smul_eq_mul]
  ring

/-- Source condition at a product point, expressed using the literal
partial gradients and the product covariant Hessian. -/
@[expose] def ProductStrictHessianAt (g₁ g₂ : (MetricField dim)) (ρ : (X dim) × (X dim) → ℝ) (z : (X dim) × (X dim)) : Prop :=
  let f₁ : (X dim) → ℝ := fun x => ρ (x,z.2)
  let f₂ : (X dim) → ℝ := fun y => ρ (z.1,y)
  let a₁ : (X dim) := (covectorSq g₁ f₁ z.1)⁻¹ • chartMetricGradient g₁ f₁ z.1
  let a₂ : (X dim) := (covectorSq g₂ f₂ z.2)⁻¹ • chartMetricGradient g₂ f₂ z.2
  (fun i => coordDeriv i f₁ z.1) ≠ 0 ∧ (fun i => coordDeriv i f₂ z.2) ≠ 0 ∧
    ∀ v w : (X dim),
      metricPair g₁ z.1 (chartMetricGradient g₁ f₁ z.1) v = 0 →
      metricPair g₁ z.1 v v = metricPair g₁ z.1 a₁ a₁ →
      metricPair g₂ z.2 (chartMetricGradient g₂ f₂ z.2) w = 0 →
      metricPair g₂ z.2 w w = metricPair g₂ z.2 a₂ a₂ →
      0 < productMetricHessian g₁ g₂ ρ z (a₁,-a₂) (a₁,-a₂) +
        productMetricHessian g₁ g₂ ρ z (v,w) (v,w)

/-- Separation produces the two strictly admissible Hessians and the
positive definite quadratic gap at the product point. -/
theorem exists_blockHessians_of_productStrictHessian [Nontrivial (Fin dim)]
    {g₁ g₂ : (MetricField dim)} (hg₁ : SmoothMetric univ g₁) (hg₂ : SmoothMetric univ g₂)
    {ρ : (X dim) × (X dim) → ℝ} {z : (X dim) × (X dim)} (hρ : ContDiffAt ℝ 2 ρ z)
    (hstrict : ProductStrictHessianAt g₁ g₂ ρ z) :
    let f₁ : (X dim) → ℝ := fun x => ρ (x,z.2)
    let f₂ : (X dim) → ℝ := fun y => ρ (z.1,y)
    let a₁ : (X dim) := (covectorSq g₁ f₁ z.1)⁻¹ • chartMetricGradient g₁ f₁ z.1
    let a₂ : (X dim) := (covectorSq g₂ f₂ z.2)⁻¹ • chartMetricGradient g₂ f₂ z.2
    ∃ (P₁ P₂ : selfAdjoint (Mat dim)) (K : ℝ), 0 < K ∧
      P₁ ∈ ProductHessianSeparation.strictSphereCone (g₁ z.1)
        (fun i => coordDeriv i f₁ z.1) (fun i => a₁ i) ∧
      P₂ ∈ ProductHessianSeparation.strictSphereCone (g₂ z.2)
        (fun i => coordDeriv i f₂ z.2) (fun i => a₂ i) ∧
      ∀ v : (X dim) × (X dim), v ≠ 0 → 0 <
        productMetricHessian g₁ g₂ ρ z v v + K * (fderiv ℝ ρ z v)^2 -
          chartBilinear (P₁ : (Mat dim)) v.1 v.1 - chartBilinear (P₂ : (Mat dim)) v.2 v.2 := by
  classical
  intro f₁ f₂ a₁ a₂
  change _ ∧ _ ∧ _ at hstrict
  rcases hstrict with ⟨hd₁,hd₂,hstrict⟩
  let d₁ : (X dim) →L[ℝ] ℝ := (fderiv ℝ ρ z).comp (ContinuousLinearMap.inl ℝ (X dim) (X dim))
  let d₂ : (X dim) →L[ℝ] ℝ := (fderiv ℝ ρ z).comp (ContinuousLinearMap.inr ℝ (X dim) (X dim))
  let c₁ (i : (I dim)) := coordDeriv i f₁ z.1
  let c₂ (i : (I dim)) := coordDeriv i f₂ z.2
  have hc₁ (i : (I dim)) : c₁ i = d₁ (axis i) := (slice_coordDeriv ρ z (hρ.differentiableAt (by norm_num)) i).1
  have hc₂ (i : (I dim)) : c₂ i = d₂ (axis i) := (slice_coordDeriv ρ z (hρ.differentiableAt (by norm_num)) i).2
  let C₁ : (X dim) →L[ℝ] (X dim) →L[ℝ] ℝ :=
    chartBilinear (fun i j => ∑ k, d₁ (axis k) * christoffel g₁ z.1 k i j)
  let C₂ : (X dim) →L[ℝ] (X dim) →L[ℝ] ℝ :=
    chartBilinear (fun i j => ∑ k, d₂ (axis k) * christoffel g₂ z.2 k i j)
  let E := (X dim) × (X dim)
  let Q : E →L[ℝ] E →L[ℝ] ℝ := fderiv ℝ (fderiv ℝ ρ) z
  let pr₁ : E →L[ℝ] (X dim) := ContinuousLinearMap.fst ℝ (X dim) (X dim)
  let pr₂ : E →L[ℝ] (X dim) := ContinuousLinearMap.snd ℝ (X dim) (X dim)
  let C₁' : E →L[ℝ] E →L[ℝ] ℝ := ((ContinuousLinearMap.compL ℝ E (X dim) ℝ).flip pr₁).comp (C₁.comp pr₁)
  let C₂' : E →L[ℝ] E →L[ℝ] ℝ := ((ContinuousLinearMap.compL ℝ E (X dim) ℝ).flip pr₂).comp (C₂.comp pr₂)
  let H := Q - C₁' - C₂'
  have hH (v w : E) : H v w = productMetricHessian g₁ g₂ ρ z v w := by
    change Q v w - C₁ v.1 w.1 - C₂ v.2 w.2 =
      Q v w - fderiv ℝ ρ z (connection g₁ z.1 v.1 w.1, connection g₂ z.2 v.2 w.2)
    rw [fderiv_product_split (fderiv ℝ ρ z)]
    have h₁ := covector_connection_eq_bilinear g₁ z.1 v.1 w.1 d₁
    have h₂ := covector_connection_eq_bilinear g₂ z.2 v.2 w.2 d₂
    change fderiv ℝ ρ z (connection g₁ z.1 v.1 w.1,0) = C₁ v.1 w.1 at h₁
    change fderiv ℝ ρ z (0,connection g₂ z.2 v.2 w.2) = C₂ v.2 w.2 at h₂
    rw [h₁,h₂]
    ring
  let L : LinearMap.BilinForm ℝ E :=
    { toFun := fun v => (H v).toLinearMap
      map_add' := fun v w => by
        apply LinearMap.ext
        intro q
        change H (v+w) q = H v q + H w q
        rw [map_add]
        rfl
      map_smul' := fun t v => by
        apply LinearMap.ext
        intro q
        change H (t • v) q = t * H v q
        rw [map_smul]
        rfl }
  have hL (v w : E) : L v w = productMetricHessian g₁ g₂ ρ z v w := hH v w
  let b := (chartCoordBasis dim).prod (chartCoordBasis dim)
  let M := LinearMap.BilinForm.toMatrix b L
  let V (v : E) : (I dim) ⊕ (I dim) → ℝ := Sum.elim (fun i => v.1 i) (fun i => v.2 i)
  have hrepr (v : E) : (fun i => b.repr v i) = V v := by
    funext i
    cases i with
    | inl i => rw [show b = (chartCoordBasis dim).prod (chartCoordBasis dim) from rfl, Module.Basis.prod_repr_inl]; rfl
    | inr i => rw [show b = (chartCoordBasis dim).prod (chartCoordBasis dim) from rfl, Module.Basis.prod_repr_inr]; rfl
  have hM (v w : E) : V v ⬝ᵥ (M *ᵥ V w) = productMetricHessian g₁ g₂ ρ z v w := by
    rw [← hrepr v, ← hrepr w]
    exact (LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec b L v w).symm.trans (hL v w)
  have hMs : M.IsHermitian := by
    ext i j
    simp only [M, Matrix.conjTranspose_apply, star_trivial, LinearMap.BilinForm.toMatrix_apply, hL]
    unfold productMetricHessian
    rw [connection_symm_of_smoothMetric hg₁ z.1 (b j).1 (b i).1,
      connection_symm_of_smoothMetric hg₂ z.2 (b j).2 (b i).2,
      (hρ.isSymmSndFDerivAt (by norm_num)).eq (b j) (b i)]
  have hG₁ := hg₁.2 z.1 (mem_univ z.1)
  have hG₂ := hg₂.2 z.2 (mem_univ z.2)
  have hfinite (v : (I dim) → ℝ) (hv : v ∈ ProductHessianSeparation.metricTangentSphere
        (g₁ z.1) c₁ (fun i => a₁ i))
      (w : (I dim) → ℝ) (hw : w ∈ ProductHessianSeparation.metricTangentSphere
        (g₂ z.2) c₂ (fun i => a₂ i)) :
      0 < (V (a₁,-a₂)) ⬝ᵥ (M *ᵥ V (a₁,-a₂)) +
        Sum.elim v w ⬝ᵥ (M *ᵥ Sum.elim v w) := by
    let x : (X dim) := WithLp.toLp 2 v
    let y : (X dim) := WithLp.toLp 2 w
    change v ∈ ProductHessianSeparation.metricTangentSphere (g₁ z.1) c₁ (fun i => a₁ i) at hv
    change w ∈ ProductHessianSeparation.metricTangentSphere (g₂ z.2) c₂ (fun i => a₂ i) at hw
    obtain ⟨hv₁,hv₂⟩ := hv
    obtain ⟨hw₁,hw₂⟩ := hw
    have hV : V (x,y) = Sum.elim v w := rfl
    rw [hM, ← hV, hM]
    apply hstrict x y
    · rw [metricPair_metricGradient _ _ _ _ hG₁]; exact hv₁
    · simp only [metricPair_eq_dotProduct]; exact hv₂
    · rw [metricPair_metricGradient _ _ _ _ hG₂]; exact hw₁
    · simp only [metricPair_eq_dotProduct]; exact hw₂
  obtain ⟨P₁,P₂,K,hK,hP₁,hP₂,hKP⟩ :=
    ProductHessianSeparation.exists_strict_block_forms_of_tangentSphere_positive
      (g₁ z.1) (g₂ z.2) hG₁ hG₂ c₁ c₂ (fun i => a₁ i) (fun i => a₂ i)
      (normalizedGradient_pair g₁ f₁ z.1 hG₁ hd₁) (normalizedGradient_pair g₂ f₂ z.2 hG₂ hd₂)
      M hMs hfinite
  refine ⟨P₁,P₂,K,hK,hP₁,hP₂,fun v hv => ?_⟩
  have hV : V v ≠ 0 := by
    intro h
    apply hv
    apply Prod.ext
    · ext i
      exact congrFun h (Sum.inl i)
    · ext i
      exact congrFun h (Sum.inr i)
  have hcov : Sum.elim c₁ c₂ ⬝ᵥ V v = fderiv ℝ ρ z v := by
    rw [show V v = Sum.elim (fun i => v.1 i) (fun i => v.2 i) from rfl,
      sumElim_dotProduct_sumElim, fderiv_product_split (fderiv ℝ ρ z)]
    have h₁ := covector_axis_sum d₁ v.1
    have h₂ := covector_axis_sum d₂ v.2
    simp only [← hc₁, ← hc₂] at h₁ h₂
    rw [← h₁, ← h₂]
    rfl
  have hpen : V v ⬝ᵥ ((K • Matrix.vecMulVec (Sum.elim c₁ c₂) (Sum.elim c₁ c₂)) *ᵥ V v) =
      K * (fderiv ℝ ρ z v)^2 := by
    have hrank (a b c : (I dim) ⊕ (I dim) → ℝ) : Matrix.vecMulVec a b *ᵥ c = (b ⬝ᵥ c) • a := by
      ext i
      simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [Matrix.smul_mulVec, hrank, dotProduct_smul, dotProduct_smul,
      dotProduct_comm (V v), hcov]
    simp only [smul_eq_mul]
    ring
  have hblocks : V v ⬝ᵥ ((Matrix.fromBlocks (P₁ : (Mat dim)) 0 0 (P₂ : (Mat dim))) *ᵥ V v) =
      chartBilinear (P₁ : (Mat dim)) v.1 v.1 + chartBilinear (P₂ : (Mat dim)) v.2 v.2 := by
    simp only [V, Matrix.fromBlocks_mulVec, Matrix.zero_mulVec, add_zero, zero_add,
      sumElim_dotProduct_sumElim, chartBilinear_apply]
    rfl
  have h := hKP.dotProduct_mulVec_pos hV
  change 0 < V v ⬝ᵥ ((M + K • Matrix.vecMulVec (Sum.elim c₁ c₂) (Sum.elim c₁ c₂) -
    Matrix.fromBlocks (P₁ : (Mat dim)) 0 0 (P₂ : (Mat dim))) *ᵥ V v) at h
  simp only [Matrix.sub_mulVec, Matrix.add_mulVec, dotProduct_sub, dotProduct_add,
    hM, hpen, hblocks] at h
  linarith

end CalderonN
