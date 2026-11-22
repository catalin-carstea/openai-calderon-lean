module

public import Proof.CalderonPatch.InteriorCurveBound
public import Proof.CalderonPatch.ConnectedInterior

import Mathlib.Topology.EMetricSpace.Basic
import Mathlib.Topology.UniformSpace.CompleteSeparated

@[expose] public section

noncomputable section
open Bundle Filter Manifold Metric Set
open scoped Bundle ContDiff ENNReal Manifold NNReal Topology

namespace CalderonPatch

open CalderonN (X)

variable {n : ℕ} [NeZero n] {M₁ M₂ : Type*}
  [TopologicalSpace M₁] [T2Space M₁] [CompactSpace M₁]
  [ChartedSpace (EuclideanHalfSpace n) M₁] [IsManifold (𝓡∂ n) ∞ M₁]
  [TopologicalSpace M₂] [T2Space M₂]
  [ChartedSpace (EuclideanHalfSpace n) M₂] [IsManifold (𝓡∂ n) ∞ M₂]

local notation "J" => 𝓡∂ n

private theorem exists_continuous_extension_of_interiorIsometry
    {g₁ : SmoothMetric n M₁} {g₂ : SmoothMetric n M₂}
    {e : OpenPartialHomeomorph M₂ M₁} (he : IsLocalMetricIsometry g₁ g₂ e)
    (hs : e.source = (𝓡∂ n).interior M₂) :
    ∃ f : M₂ → M₁, Continuous f ∧ EqOn f e e.source := by
  let _ : RiemannianBundle (fun x : M₁ => TangentSpace J x) := ⟨g₁.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle (X n) (fun x : M₁ => TangentSpace J x) :=
    ⟨⟨g₁.inner, g₁.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let _ : EMetricSpace M₁ := .ofRiemannianMetric J M₁
  have hDense : Dense e.source := hs.symm ▸ dense_manifoldInterior
  let a : e.source → M₁ := fun x => e x
  let f := hDense.extend a
  have hCauchy (p : M₂) : Cauchy (map (e : M₂ → M₁) (𝓝[e.source] p)) := by
    let _ : NeBot (𝓝[e.source] p) := mem_closure_iff_nhdsWithin_neBot.mp (hDense p)
    apply EMetric.cauchy_iff.mpr ⟨NeBot.ne inferInstance, ?_⟩
    intro ε hε
    obtain ⟨C, hC, V, hV, hpV, hCurve⟩ := exists_interior_curve_bound g₂ p
    obtain ⟨δ, hδ, hSmall⟩ :=
      ENNReal.exists_pos_mul_lt (a := (C : ℝ≥0∞)) ENNReal.coe_ne_top (ne_of_gt hε)
    let c := extChartAt J p
    let U := V ∩ c ⁻¹' eball (c p) (δ / 2)
    have hU : U ∈ 𝓝 p := inter_mem (hV.mem_nhds hpV)
      ((continuousAt_extChartAt (I := J) p).preimage_mem_nhds
        (eball_mem_nhds _ (ENNReal.div_pos hδ.ne' (by simp))))
    let A := U ∩ e.source
    have hA : A ∈ 𝓝[e.source] p := inter_mem (mem_nhdsWithin_of_mem_nhds hU) self_mem_nhdsWithin
    refine ⟨e '' A, image_mem_map hA, ?_⟩
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have hxI : x ∈ (𝓡∂ n).interior M₂ := hs ▸ hx.2
    have hyI : y ∈ (𝓡∂ n).interior M₂ := hs ▸ hy.2
    obtain ⟨γ, hγ, hγx, hγy, hγI, hLen⟩ := hCurve x ⟨hx.1.1, hxI⟩ y ⟨hy.1.1, hyI⟩
    have hγS : MapsTo γ (Icc 0 1) e.source := hs.symm ▸ hγI
    have hγe : ContMDiffOn 𝓘(ℝ, ℝ) J 1 (e ∘ γ) (Icc 0 1) :=
      (he.smooth.of_le (by simp)).comp hγ hγS
    have hLen' : edist (e x) (e y) ≤ nativePathLength g₂ γ 0 1 := by
      change riemannianEDist J (e x) (e y) ≤ nativePathLength g₂ γ 0 1
      calc
        _ ≤ pathELength J (e ∘ γ) 0 1 :=
          riemannianEDist_le_pathELength hγe (congrArg e hγx) (congrArg e hγy) zero_le_one
        _ = nativePathLength g₁ (e ∘ γ) 0 1 := pathELength_eq_native g₁ _ _ _
        _ = _ := nativePathLength_comp_isometry he hγ hγS
    have hdist : edist (c x) (c y) ≤ δ := by
      have hxδ : edist (c x) (c p) < δ / 2 := hx.1.2
      have hyδ : edist (c y) (c p) < δ / 2 := hy.1.2
      calc
        _ ≤ edist (c x) (c p) + edist (c p) (c y) := edist_triangle _ _ _
        _ ≤ δ / 2 + δ / 2 := add_le_add hxδ.le (edist_comm (c p) (c y) ▸ hyδ.le)
        _ = δ := ENNReal.add_halves _
    calc
      _ ≤ (C : ℝ≥0∞) * edist (c x) (c y) := hLen'.trans hLen
      _ ≤ (C : ℝ≥0∞) * δ := by gcongr
      _ < ε := by rwa [mul_comm]
  have hf : Continuous f := by
    apply hDense.isDenseInducing_val.continuous_extend_of_cauchy
    intro p
    change Cauchy (map ((e : M₂ → M₁) ∘ (Subtype.val : e.source → M₂)) (comap Subtype.val (𝓝 p)))
    rw [← Filter.map_map, Filter.map_comap_setCoe_val]
    exact hCauchy p
  refine ⟨f, hf, ?_⟩
  intro p hp
  have ha : Continuous a := continuousOn_iff_continuous_domRestrict.mp e.continuousOn
  exact hDense.extend_eq ha ⟨p, hp⟩

/-- The interior isometry and its inverse extend continuously to a
homeomorphism of the compact manifolds with boundary. Small interior
paths prove the needed Cauchy property at boundary points. -/
theorem interiorIsometry_extends_homeomorph [CompactSpace M₂]
    {g₁ : SmoothMetric n M₁} {g₂ : SmoothMetric n M₂}
    {e : OpenPartialHomeomorph M₂ M₁} (he : IsLocalMetricIsometry g₁ g₂ e)
    (hs : e.source = (𝓡∂ n).interior M₂) (ht : e.target = (𝓡∂ n).interior M₁) :
    ∃ f : M₂ ≃ₜ M₁, EqOn f e e.source ∧ EqOn f.symm e.symm e.target := by
  obtain ⟨f, hf, hfE⟩ := exists_continuous_extension_of_interiorIsometry he hs
  obtain ⟨g, hg, hgE⟩ := exists_continuous_extension_of_interiorIsometry he.symm ht
  have hL (p : M₂) : g (f p) = p := by
    have hc : IsClosed {x | g (f x) = x} := isClosed_eq (hg.comp hf) continuous_id
    have hDense : Dense e.source := hs.symm ▸ dense_manifoldInterior
    apply closure_minimal _ hc (hDense p)
    intro x hx
    change g (f x) = x
    rw [hfE hx, hgE (e.map_source hx), e.left_inv hx]
  have hR (q : M₁) : f (g q) = q := by
    have hc : IsClosed {x | f (g x) = x} := isClosed_eq (hf.comp hg) continuous_id
    have hDense : Dense e.target := ht.symm ▸ dense_manifoldInterior
    apply closure_minimal _ hc (hDense q)
    intro x hx
    change f (g x) = x
    rw [hgE hx, hfE (e.map_target hx), e.right_inv hx]
  exact ⟨⟨⟨f, g, hL, hR⟩, hf, hg⟩, hfE, hgE⟩

end CalderonPatch
