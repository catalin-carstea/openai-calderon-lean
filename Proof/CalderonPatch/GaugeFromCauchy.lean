module

public import Proof.CalderonPatch.AccessibleGauge

import Proof.CalderonN.HarmonicL2Space

public section

noncomputable section
open Set
open scoped ContDiff Manifold

namespace CalderonPatch

open CalderonN (I X MetricField coordDeriv laplace_sub)

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]

local notation "J" => 𝓡∂ n
local notation "R" => 𝓘(ℝ, ℝ)
local notation "K" => 𝓘(ℝ, X n)

/-- The native Laplacian is linear on smooth functions. -/
theorem nativeLaplace_sub (g : SmoothMetric n M) {u v : M → ℝ}
    (hu : ContMDiff J R ∞ u) (hv : ContMDiff J R ∞ v)
    {p : M} (hp : p ∈ (J).interior M) :
    nativeLaplace g (fun x => u x - v x) p = nativeLaplace g u p - nativeLaplace g v p := by
  obtain ⟨e, hpe, _, heI, he, hes⟩ := exists_interiorChart p hp isOpen_univ (mem_univ p)
  rw [nativeLaplace_eq_coordinate g e heI he hes (hu.sub hv).contMDiffOn hpe,
    nativeLaplace_eq_coordinate g e heI he hes hu.contMDiffOn hpe,
    nativeLaplace_eq_coordinate g e heI he hes hv.contMDiffOn hpe]
  exact laplace_sub e.open_target _ (hu.comp_contMDiffOn hes).contDiffOn
    (hv.comp_contMDiffOn hes).contDiffOn (e.map_source hpe)

/-- Two smooth harmonic functions with equal value and inward derivatives
in a shared signed chart agree near its boundary face. -/
theorem eqOn_native_harmonic_of_agreeing_cauchy (g : SmoothMetric n M)
    {u v : M → ℝ} (hu : ContMDiff J R ∞ u) (hv : ContMDiff J R ∞ v)
    (huH : EqOn (nativeLaplace g u) 0 ((J).interior M))
    (hvH : EqOn (nativeLaplace g v) 0 ((J).interior M))
    (e : OpenPartialHomeomorph M (X n)) (heI : e.source ⊆ (J).interior M)
    (he : ContMDiffOn J K ∞ e e.source) (hes : ContMDiffOn K J ∞ e.symm e.target)
    {U : Set (X n)} {i : I n} (hU : IsOpen U) (hUc : IsConnected U)
    (hFace : (boundaryFace U i).Nonempty) (hTarget : e.target = U ∩ {x | 0 < x i})
    {γ : MetricField n} (hγ : CalderonN.SmoothMetric univ γ)
    (hMetric : EqOn (coordinateMetric g e) γ e.target)
    {a b : X n → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hReprU : EqOn (u ∘ e.symm) a e.target) (hReprV : EqOn (v ∘ e.symm) b e.target)
    (hValue : EqOn a b (boundaryFace U i))
    (hNormal : EqOn (coordDeriv i a) (coordDeriv i b) (boundaryFace U i)) :
    EqOn u v e.source := by
  have hd : EqOn (nativeLaplace g (fun x => u x - v x)) 0 ((J).interior M) := by
    intro p hp
    rw [nativeLaplace_sub g hu hv hp, huH hp, hvH hp, sub_self]
    rfl
  have hRepr : EqOn ((fun x => u x - v x) ∘ e.symm) (fun y => a y - b y) e.target := by
    intro y hy
    exact congrArg₂ Sub.sub (hReprU hy) (hReprV hy)
  have h0 : EqOn (fun y => a y - b y) 0 (boundaryFace U i) :=
    fun y hy => sub_eq_zero.mpr (hValue hy)
  have h1 : EqOn (coordDeriv i (fun y => a y - b y)) 0 (boundaryFace U i) := by
    intro y hy
    have h := hNormal hy
    change fderiv ℝ a y (CalderonN.axis i) = fderiv ℝ b y (CalderonN.axis i) at h
    change fderiv ℝ (fun y => a y - b y) y (CalderonN.axis i) = 0
    rw [fderiv_fun_sub (ha.differentiable (by simp) y) (hb.differentiable (by simp) y),
      sub_apply, h, sub_self]
  have hz := eqOn_native_harmonic_of_boundary_cauchy g (hu.sub hv) hd e heI he hes hU hUc
    hFace hTarget hγ hMetric (ha.sub hb) hRepr h0 h1
  exact fun p hp => sub_eq_zero.mp (hz hp)

variable [T2Space M] [CompactSpace M] [ConnectedSpace M]

/-- For each measured trace it suffices to know agreement of the Cauchy
data on one common boundary chart. The pulled-back Dirichlet solutions
then force equality of all supported traces under the recovered map. -/
theorem fixesPatch_of_cauchyAgreement_at_seam {g₁ g₂ : SmoothMetric n M}
    {Γ : Set ((J).boundary M)} (hΓ : IsOpen Γ)
    (Φ : M ≃ₘ⟮J, J⟯ M) (hΦ : PullbackMetric g₁ g₂ Φ)
    (e : OpenPartialHomeomorph M (X n)) (heI : e.source ⊆ (J).interior M)
    (he : ContMDiffOn J K ∞ e e.source) (hes : ContMDiffOn K J ∞ e.symm e.target)
    {U : Set (X n)} {i : I n} (hU : IsOpen U) (hUc : IsConnected U)
    (hFace : (boundaryFace U i).Nonempty) (hTarget : e.target = U ∩ {x | 0 < x i})
    {γ : MetricField n} (hγ : CalderonN.SmoothMetric univ γ)
    (hMetric : EqOn (coordinateMetric g₂ e) γ e.target)
    (hSolutions : ∀ f : M → ℝ, ContMDiff J R ∞ f →
      tsupport (fun p : (J).boundary M => f p) ⊆ Γ →
      ∃ (u₁ u₂ : M → ℝ) (a b : X n → ℝ),
        ContMDiff J R ∞ u₁ ∧ ContMDiff J R ∞ u₂ ∧
        EqOn u₁ f ((J).boundary M) ∧ EqOn u₂ f ((J).boundary M) ∧
        EqOn (nativeLaplace g₁ u₁) 0 ((J).interior M) ∧
        EqOn (nativeLaplace g₂ u₂) 0 ((J).interior M) ∧
        ContDiff ℝ ∞ a ∧ ContDiff ℝ ∞ b ∧
        EqOn (u₂ ∘ e.symm) a e.target ∧ EqOn (u₁ ∘ Φ ∘ e.symm) b e.target ∧
        EqOn a b (boundaryFace U i) ∧
        EqOn (coordDeriv i a) (coordDeriv i b) (boundaryFace U i)) : FixesPatch Γ Φ := by
  have hne : e.source.Nonempty := by
    obtain ⟨x, hx⟩ := hFace
    have hxcl : x ∈ closure e.target := hTarget.symm ▸ boundaryFace_subset_closure_positive hU hx
    obtain ⟨y, hy⟩ := (closure_nonempty_iff.mp ⟨x, hxcl⟩)
    exact ⟨e.symm y, e.map_target hy⟩
  apply fixesPatch_of_harmonic_agreement_at_seam hΓ Φ hΦ
  intro f hf hs
  obtain ⟨u₁,u₂,a,b,hu₁,hu₂,hT₁,hT₂,hH₁,hH₂,ha,hb,hRa,hRb,hVal,hNorm⟩ := hSolutions f hf hs
  have hComp : EqOn (nativeLaplace g₂ (u₁ ∘ Φ)) 0 ((J).interior M) := by
    intro x hx
    have hy : Φ x ∈ (J).interior M := by
      rw [← Φ.image_interior (by simp)]
      exact mem_image_of_mem Φ hx
    exact (nativeLaplace_comp_of_pullbackMetric Φ hΦ hu₁ hx).trans (hH₁ hy)
  refine ⟨u₁,u₂,hu₁,hu₂,hT₁,hT₂,hH₁,hH₂,e.source,e.open_source,hne,heI,?_⟩
  exact eqOn_native_harmonic_of_agreeing_cauchy g₂ hu₂ (hu₁.comp Φ.contMDiff) hH₂ hComp
    e heI he hes hU hUc hFace hTarget hγ hMetric ha hb hRa hRb hVal hNorm

end CalderonPatch
