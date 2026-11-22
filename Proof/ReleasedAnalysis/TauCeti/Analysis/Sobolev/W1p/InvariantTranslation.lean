module

public import Proof.ReleasedAnalysis.TauCeti.Analysis.Sobolev.W1p.Translation
public import Proof.ReleasedAnalysis.TauCeti.Analysis.Sobolev.W1p.Zero

public section

noncomputable section
open MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions ENNReal

namespace TauCeti

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {U : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

private theorem measurePreserving_translate_invariant {h : E}
    (hMap : MapsTo (· + h) U U) (hRev : ∀ x, x + h ∈ U → x ∈ U) :
    MeasurePreserving (· + h) (μ.restrict U) (μ.restrict U) := by
  have hPre : (· + h) ⁻¹' (U : Set E) = U :=
    Set.Subset.antisymm (fun x hx => hRev x hx) (fun _ hx => hMap hx)
  simpa only [hPre] using
    (measurePreserving_add_right μ h).restrict_preimage_emb (measurableEmbedding_addRight h) (U : Set E)

private theorem W1p.value_translate_eq_comp {h : E}
    (hMap : MapsTo (· + h) U U)
    (hμ : MeasurePreserving (· + h) (μ.restrict U) (μ.restrict U)) (w : W1p μ U p) :
    W1p.value (W1p.translate hMap w) =
      Lp.compMeasurePreservingₗᵢ ℝ (· + h) hμ (W1p.value w) :=
  Lp.ext ((W1p.value_translate_ae hMap w).trans (Lp.coeFn_compMeasurePreserving _ hμ).symm)

private theorem W1p.gradient_translate_eq_comp {h : E}
    (hMap : MapsTo (· + h) U U)
    (hμ : MeasurePreserving (· + h) (μ.restrict U) (μ.restrict U)) (w : W1p μ U p) :
    W1p.gradient (W1p.translate hMap w) =
      Lp.compMeasurePreservingₗᵢ ℝ (· + h) hμ (W1p.gradient w) :=
  Lp.ext ((W1p.gradient_translate_ae hMap w).trans (Lp.coeFn_compMeasurePreserving _ hμ).symm)

private def W1p.translateLinearInvariant {h : E} (hMap : MapsTo (· + h) U U)
    (hμ : MeasurePreserving (· + h) (μ.restrict U) (μ.restrict U)) :
    W1p μ U p →ₗ[ℝ] W1p μ U p where
  toFun := W1p.translate hMap
  map_add' a b := by
    apply W1p.ext_value
    rw [W1p.value_translate_eq_comp hMap hμ]
    simp only [← W1p.valueL_apply (a + b), ← W1p.valueL_apply (W1p.translate hMap a + W1p.translate hMap b),
      map_add, W1p.valueL_apply, W1p.value_translate_eq_comp hMap hμ]
  map_smul' a w := by
    apply W1p.ext_value
    rw [W1p.value_translate_eq_comp hMap hμ]
    simp only [← W1p.valueL_apply (a • w), ← W1p.valueL_apply (a • W1p.translate hMap w),
      map_smul, W1p.valueL_apply, W1p.value_translate_eq_comp hMap hμ, RingHom.id_apply]

private theorem W1p.norm_translateInvariant_le {h : E}
    (hMap : MapsTo (· + h) U U)
    (hμ : MeasurePreserving (· + h) (μ.restrict U) (μ.restrict U)) (w : W1p μ U p) :
    ‖W1p.translate hMap w‖ ≤ 2 * ‖w‖ := by
  refine (W1p.norm_le_norm_value_add_norm_gradient _).trans ?_
  rw [W1p.value_translate_eq_comp hMap hμ, W1p.gradient_translate_eq_comp hMap hμ,
    LinearIsometry.norm_map, LinearIsometry.norm_map, two_mul]
  exact add_le_add (W1p.norm_value_le w) (W1p.norm_gradient_le w)

private theorem W1p.continuous_translateInvariant {h : E} (hMap : MapsTo (· + h) U U)
    (hμ : MeasurePreserving (· + h) (μ.restrict U) (μ.restrict U)) :
    Continuous (W1p.translate (p := p) hMap : W1p μ U p → W1p μ U p) := by
  let T : W1p μ U p →ₗ[ℝ] W1p μ U p := W1p.translateLinearInvariant hMap hμ
  have hT (w : W1p μ U p) : ‖T w‖ ≤ 2 * ‖w‖ :=
    W1p.norm_translateInvariant_le hMap hμ w
  exact (T.mkContinuous 2 hT).continuous.congr (fun _ => rfl)

private theorem W1p.translate_ofTestFunction_mem_w1p0 {h : E} (hMap : MapsTo (· + h) U U)
    (hRev : ∀ x, x + h ∈ U → x ∈ U) (φ : 𝓓(U, ℝ)) :
    W1p.translate hMap (W1p.ofTestFunctionₗ μ U p φ) ∈ w1p0Submodule μ U p := by
  let τ : E ≃ₜ E := Homeomorph.addRight h
  have hPre : τ ⁻¹' (U : Set E) = U := Set.Subset.antisymm (fun x hx => hRev x hx) (fun _ hx => hMap hx)
  have hμ : MeasurePreserving τ (μ.restrict U) (μ.restrict U) :=
    measurePreserving_translate_invariant hMap hRev
  have hTs : tsupport ((φ : E → ℝ) ∘ τ) ⊆ U := by
    have hs : Function.support ((φ : E → ℝ) ∘ τ) = τ ⁻¹' Function.support (φ : E → ℝ) := rfl
    rw [tsupport, hs, ← τ.preimage_closure, ← hPre]
    exact preimage_mono φ.tsupport_subset
  let ψ : 𝓓(U, ℝ) := ⟨(φ : E → ℝ) ∘ τ,
    φ.contDiff.comp (contDiff_id.add contDiff_const), φ.hasCompactSupport.comp_homeomorph τ, hTs⟩
  let w := W1p.ofTestFunctionₗ μ U p φ
  have hv : (W1p.value w : E → ℝ) =ᵐ[μ.restrict U] φ := by
    unfold w
    rw [W1p.value_ofTestFunctionₗ]
    exact testFunctionLp_apply_ae p φ
  have hψ : (W1p.value (W1p.ofTestFunctionₗ μ U p ψ) : E → ℝ) =ᵐ[μ.restrict U] ψ := by
    rw [W1p.value_ofTestFunctionₗ]
    exact testFunctionLp_apply_ae p ψ
  have heq : W1p.translate hMap w = W1p.ofTestFunctionₗ μ U p ψ := by
    apply W1p.ext_value
    apply Lp.ext
    exact (W1p.value_translate_ae hMap w).trans ((hμ.quasiMeasurePreserving.ae_eq_comp hv).trans hψ.symm)
  rw [heq]
  exact W1p.ofTestFunctionₗ_mem_w1p0Submodule ψ

/-- Translation preserving an open domain also preserves the closure of
its smooth compactly supported tests in the Sobolev norm. -/
theorem W1p.translate_mem_w1p0Submodule {h : E} (hMap : MapsTo (· + h) U U)
    (hRev : ∀ x, x + h ∈ U → x ∈ U) {u : W1p μ U p}
    (hu : u ∈ w1p0Submodule μ U p) : W1p.translate hMap u ∈ w1p0Submodule μ U p := by
  have hμ := measurePreserving_translate_invariant (μ := μ) hMap hRev
  let A : Set (W1p μ U p) := range (W1p.ofTestFunctionₗ μ U p)
  let B : Set (W1p μ U p) := ↑(w1p0Submodule μ U p)
  have hu' : u ∈ closure A := (coe_w1p0Submodule (mu := μ) (Omega := U) (p := p)) ▸ hu
  have hTest : W1p.translate hMap '' A ⊆ B := by
    rintro _ ⟨_, ⟨φ, rfl⟩, rfl⟩
    exact W1p.translate_ofTestFunction_mem_w1p0 hMap hRev φ
  have hCont : Continuous (W1p.translate (p := p) hMap) := W1p.continuous_translateInvariant hMap hμ
  have hImg := image_closure_subset_closure_image (s := A) hCont (mem_image_of_mem _ hu')
  exact closure_minimal hTest (w1p0Submodule μ U p).isClosed hImg

end TauCeti
