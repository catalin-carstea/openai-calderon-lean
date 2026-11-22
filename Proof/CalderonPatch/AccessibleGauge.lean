module

public import Proof.CalderonPatch.BoundaryCauchy
public import Proof.CalderonPatch.IsometricCharts
public import Proof.CalderonPatch.ManifoldContinuation
public import Proof.CalderonPatch.MeasuredGauge

import Proof.CalderonN.GreenWeak

public section

noncomputable section
open Filter Set
open scoped ContDiff Manifold Topology

namespace CalderonPatch

open CalderonN (X laplace laplace_congrOn)

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]

local notation "J" => 𝓡∂ n
local notation "R" => 𝓘(ℝ, ℝ)
local notation "K" => 𝓘(ℝ, X n)

omit [IsManifold (𝓡∂ n) ∞ M] in
private theorem diffeomorph_image_manifoldInterior (Φ : M ≃ₘ⟮J, J⟯ M) :
    Φ '' (J).interior M = (J).interior M := by
  have h := Φ.image_boundary (by simp)
  rw [← (J).compl_interior, image_compl_eq (f := (Φ : M → M)) Φ.bijective] at h
  exact compl_injective h

/-- The native Laplacian commutes with pullback by a smooth metric
isometry, for every interior point. -/
theorem nativeLaplace_comp_of_pullbackMetric {g₁ g₂ : SmoothMetric n M}
    (Φ : M ≃ₘ⟮J, J⟯ M) (hΦ : PullbackMetric g₁ g₂ Φ) {u : M → ℝ}
    (hu : ContMDiff J R ∞ u) {x : M} (hx : x ∈ (J).interior M) :
    nativeLaplace g₂ (u ∘ Φ) x = nativeLaplace g₁ u (Φ x) := by
  let e := Φ.toHomeomorph.toOpenPartialHomeomorph
  have hE : IsLocalMetricIsometry g₁ g₂ e := ⟨Φ.contMDiff.contMDiffOn,
    Φ.symm.contMDiff.contMDiffOn, fun p _ => hΦ p⟩
  obtain ⟨b, hxb, _, hbI, hb, hbs⟩ := exists_interiorChart x hx isOpen_univ (mem_univ x)
  obtain ⟨a, hT, hS, hInv, ha, has, hMetric⟩ := exists_transported_chart hE b (subset_univ _) hb hbs
  have haI : a.source ⊆ (J).interior M := by
    rw [hS, ← diffeomorph_image_manifoldInterior Φ]
    exact image_mono hbI
  have hxa : Φ x ∈ a.source := hS.symm ▸ mem_image_of_mem e hxb
  have hCoord : a (Φ x) = b x := by
    have h := congrFun hInv (b x)
    change a.symm (b x) = Φ (b.symm (b x)) at h
    rw [b.left_inv hxb] at h
    rw [← h, a.right_inv (hT.symm ▸ b.map_source hxb)]
  have hFunc : (u ∘ Φ) ∘ b.symm = u ∘ a.symm := by rw [hInv]; rfl
  rw [nativeLaplace_eq_coordinate g₂ b hbI hb hbs (hu.comp Φ.contMDiff).contMDiffOn hxb,
    nativeLaplace_eq_coordinate g₁ a haI ha has hu.contMDiffOn hxa, hCoord, hFunc]
  exact laplace_congrOn b.open_target hMetric.symm (fun _ _ => rfl) (b.map_source hxb)

variable [ConnectedSpace M]

/-- Interior unique continuation and continuity recover equality on the
whole original manifold, including its entire boundary. -/
theorem eq_of_native_harmonic_agreement (g : SmoothMetric n M) {u v : M → ℝ}
    (hu : ContMDiff J R ∞ u) (hv : ContMDiff J R ∞ v)
    (huH : EqOn (nativeLaplace g u) 0 ((J).interior M)) (hvH : EqOn (nativeLaplace g v) 0 ((J).interior M))
    {V : Set M} (hV : IsOpen V) (hVne : V.Nonempty) (hVI : V ⊆ (J).interior M) (hEq : EqOn u v V) : u = v := by
  have hI : IsOpen ((J).interior M) := (J).isOpen_interior (n := ∞) (by simp)
  have h := eqOn_of_locally_harmonic hI isConnected_manifoldInterior hV hVne hVI hEq (fun p hp => by
    obtain ⟨e, hpe, heU, heI, he, hei⟩ := exists_interiorChart p hp hI hp
    refine ⟨e, hpe, heU, coordinateMetric g e, coordinateMetric_smooth g e he hei, ?_, ?_⟩
    · refine ⟨(hu.comp_contMDiffOn hei).contDiffOn, fun y hy => ?_⟩
      have hes := e.map_target hy
      have hh := nativeLaplace_eq_coordinate g e heI he hei hu.contMDiffOn hes
      rw [e.right_inv hy, huH (heI hes)] at hh
      exact hh.symm
    · refine ⟨(hv.comp_contMDiffOn hei).contDiffOn, fun y hy => ?_⟩
      have hes := e.map_target hy
      have hh := nativeLaplace_eq_coordinate g e heI he hei hv.contMDiffOn hes
      rw [e.right_inv hy, hvH (heI hes)] at hh
      exact hh.symm)
  exact hu.continuous.ext_on dense_manifoldInterior hv.continuous h

omit [ConnectedSpace M] in
/-- A smooth native harmonic function with zero Cauchy data in an
extended boundary chart vanishes on the chart's original interior. -/
theorem eqOn_native_harmonic_of_boundary_cauchy (g : SmoothMetric n M) {u : M → ℝ}
    (hu : ContMDiff J R ∞ u) (huH : EqOn (nativeLaplace g u) 0 ((J).interior M))
    (e : OpenPartialHomeomorph M (X n)) (heI : e.source ⊆ (J).interior M)
    (he : ContMDiffOn J K ∞ e e.source) (hes : ContMDiffOn K J ∞ e.symm e.target)
    {U : Set (X n)} {i : CalderonN.I n} (hU : IsOpen U) (hUc : IsConnected U)
    (hFace : (boundaryFace U i).Nonempty) (hTarget : e.target = U ∩ {x | 0 < x i})
    {γ : CalderonN.MetricField n} (hγ : CalderonN.SmoothMetric univ γ)
    (hMetric : EqOn (coordinateMetric g e) γ e.target)
    {v : X n → ℝ} (hv : ContDiff ℝ ∞ v) (hV : EqOn (u ∘ e.symm) v e.target)
    (hValue : EqOn v 0 (boundaryFace U i)) (hNormal : EqOn (CalderonN.coordDeriv i v) 0 (boundaryFace U i)) :
    EqOn u 0 e.source := by
  have hHa : EqOn (laplace γ v) 0 e.target := by
    intro y hy
    have hh := nativeLaplace_eq_coordinate g e heI he hes hu.contMDiffOn (e.map_target hy)
    rw [huH (heI (e.map_target hy)), e.right_inv hy, laplace_congrOn e.open_target hMetric hV hy] at hh
    exact hh.symm
  have hZero := laplace_eq_zero_of_flat_boundary_cauchy hγ hU hUc hFace hv (hTarget ▸ hHa) hValue hNormal
  intro p hp
  have h := hV (e.map_source hp)
  rw [Function.comp_apply, e.left_inv hp, hZero (hTarget ▸ e.map_source hp)] at h
  exact h

variable [T2Space M] [CompactSpace M]

/-- Equality of the pulled-back harmonic solutions near the attached
seam forces the recovered gauge to fix the whole measured patch. -/
theorem fixesPatch_of_harmonic_agreement_at_seam {g₁ g₂ : SmoothMetric n M}
    {Γ : Set ((J).boundary M)} (hΓ : IsOpen Γ) (Φ : M ≃ₘ⟮J, J⟯ M) (hΦ : PullbackMetric g₁ g₂ Φ)
    (hSolutions : ∀ f : M → ℝ, ContMDiff J R ∞ f → tsupport (fun p : (J).boundary M => f p) ⊆ Γ →
      ∃ u₁ u₂ : M → ℝ,
        ContMDiff J R ∞ u₁ ∧ ContMDiff J R ∞ u₂ ∧
        EqOn u₁ f ((J).boundary M) ∧ EqOn u₂ f ((J).boundary M) ∧
        EqOn (nativeLaplace g₁ u₁) 0 ((J).interior M) ∧ EqOn (nativeLaplace g₂ u₂) 0 ((J).interior M) ∧
        ∃ V : Set M, IsOpen V ∧ V.Nonempty ∧ V ⊆ (J).interior M ∧ EqOn u₂ (u₁ ∘ Φ) V) : FixesPatch Γ Φ := by
  apply fixesPatch_of_supported_trace_eq hΓ Φ
  intro f hf hfs p
  obtain ⟨u₁,u₂,h₁,h₂,hT₁,hT₂,hH₁,hH₂,V,hV,hVne,hVI,hEq⟩ := hSolutions f hf hfs
  have hComp : EqOn (nativeLaplace g₂ (u₁ ∘ Φ)) 0 ((J).interior M) := by
    intro x hx
    have hy : Φ x ∈ (J).interior M := by
      rw [← diffeomorph_image_manifoldInterior Φ]
      exact mem_image_of_mem Φ hx
    exact (nativeLaplace_comp_of_pullbackMetric Φ hΦ h₁ hx).trans (hH₁ hy)
  have h := eq_of_native_harmonic_agreement g₂ h₂ (h₁.comp Φ.contMDiff) hH₂ hComp hV hVne hVI hEq
  have hΦp : Φ p ∈ (J).boundary M :=
    (Φ.image_boundary (by simp)).subset (mem_image_of_mem Φ p.property)
  exact (hT₂ p.property).symm.trans ((congrFun h p).trans (hT₁ hΦp))

end CalderonPatch
