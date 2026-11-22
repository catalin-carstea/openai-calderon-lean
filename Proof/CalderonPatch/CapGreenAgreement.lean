module

public import Proof.CalderonPatch.GreenMatchedDomain

import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Measure.OpenPos
import Proof.CalderonN.GreenRestriction

@[expose] public section

noncomputable section
open Filter MeasureTheory Set
open scoped ContDiff Manifold Topology

namespace CalderonPatch

open CalderonN (X IsDirichletGreenKernel)

variable {n : ℕ}

private theorem integrable_mul_test {U : Set (X n)} (hU : IsOpen U)
    {f φ : X n → ℝ} (hf : ContinuousOn f U) (hφ : Continuous φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U) :
    Integrable (fun x => φ x * f x) volume := by
  apply Continuous.integrable_of_hasCompactSupport _ hc.mul_right
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x ∈ U
  · exact hφ.continuousAt.mul (hf.continuousAt (hU.mem_nhds hx))
  · apply (show ContinuousAt (fun _ : X n => (0 : ℝ)) x from continuousAt_const).congr_of_eventuallyEq
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds (show x ∉ tsupport φ from fun h => hx (hs h))]
      with y hy
    change φ y * f y = 0
    rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]

/-- Testing against the same supported sources determines continuous
kernel sections off their poles when they use the same positive density. -/
theorem eqOn_of_weighted_test_pairings {U V : Set (X n)} (hV : IsOpen V) (hVU : V ⊆ U)
    {ρ a b : X n → ℝ} (hρ : ContinuousOn ρ V) (hρpos : ∀ x ∈ V, 0 < ρ x)
    (ha : ContinuousOn a V) (hb : ContinuousOn b V)
    (hEq : ∀ φ : X n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ V →
      (∫ x in U, φ x * a x * ρ x) = ∫ x in U, φ x * b x * ρ x) :
    EqOn a b V := by
  let d : X n → ℝ := fun x => (a x - b x) * ρ x
  have hd : ContinuousOn d V := (ha.sub hb).mul hρ
  have htests (φ : X n → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
      (hs : tsupport φ ⊆ V) : (∫ x, φ x • d x) = 0 := by
    have h := hEq φ hφ hc hs
    have hzero (x : X n) (hx : x ∉ U) : φ x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hh => hx (hVU (hs hh)))
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by simp [hzero x hx]),
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by simp [hzero x hx])] at h
    have hi₁ : Integrable (fun x => φ x * a x * ρ x) volume := by
      simp only [mul_assoc]
      exact integrable_mul_test hV (ha.mul hρ) hφ.continuous hc hs
    have hi₂ : Integrable (fun x => φ x * b x * ρ x) volume := by
      simp only [mul_assoc]
      exact integrable_mul_test hV (hb.mul hρ) hφ.continuous hc hs
    have hsub : (∫ x, φ x * a x * ρ x - φ x * b x * ρ x) = 0 := by
      rw [integral_sub hi₁ hi₂, h, sub_self]
    simpa only [d, smul_eq_mul, mul_sub, sub_mul, mul_assoc] using hsub
  have hAE : d =ᵐ[(volume : Measure (X n)).restrict V] 0 :=
    (ae_restrict_iff' hV.measurableSet).mpr
      (hV.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hd.locallyIntegrableOn hV.measurableSet) htests)
  have hd0 := Measure.eqOn_open_of_ae_eq hAE hV hd continuousOn_const
  exact fun x hx => sub_eq_zero.mp ((mul_eq_zero.mp (hd0 hx)).resolve_right (hρpos x hx).ne')

variable [NeZero n] {F M₁ M₂ : Type*}
  [TopologicalSpace M₁] [T2Space M₁] [MeasurableSpace M₁] [BorelSpace M₁]
  [ChartedSpace (EuclideanHalfSpace n) M₁] [IsManifold (𝓡∂ n) ∞ M₁]
  [TopologicalSpace M₂] [T2Space M₂] [MeasurableSpace M₂] [BorelSpace M₂]
  [ChartedSpace (EuclideanHalfSpace n) M₂] [IsManifold (𝓡∂ n) ∞ M₂]

/-- The cap source representations of paired evaluations imply pointwise
equality of the actual Green kernels on the whole matching domain. -/
theorem green_eqOn_of_capSourceRepresentations (hn : 2 ≤ n)
    {g₁ : SmoothMetric n M₁} {g₂ : SmoothMetric n M₂}
    (Φ : OpenPartialHomeomorph M₂ M₁) (hΦ : IsLocalMetricIsometry g₁ g₂ Φ)
    (hI₂ : Φ.source ⊆ (𝓡∂ n).interior M₂) (hI₁ : Φ.target ⊆ (𝓡∂ n).interior M₁)
    (hW : IsConnected Φ.source)
    {μ₁ : Measure M₁} {μ₂ : Measure M₂} (hμ₁ : IsMetricVolume g₁ μ₁) (hμ₂ : IsMetricVolume g₂ μ₂)
    {G₁ : M₁ × M₁ → ℝ} {G₂ : M₂ × M₂ → ℝ}
    (hG₁ : IsDirichletGreenKernel (𝓡∂ n) μ₁ (nativeLaplace g₁) G₁)
    (hG₂ : IsDirichletGreenKernel (𝓡∂ n) μ₂ (nativeLaplace g₂) G₂)
    (c₁ : OpenPartialHomeomorph M₁ (X n)) (c₂ : OpenPartialHomeomorph M₂ (X n))
    {V : Set (X n)} (hV : IsOpen V) (hVConn : IsConnected V)
    (hV₁ : V ⊆ c₁.target) (hV₂ : V ⊆ c₂.target)
    (hCap : MapsTo c₂.symm V Φ.source)
    (hId : EqOn c₁.symm (Φ ∘ c₂.symm) V)
    (E₁ : M₁ → F → ℝ) (E₂ : M₂ → F → ℝ)
    (hEval : ∀ q ∈ Φ.source, E₂ q = E₁ (Φ q))
    (ρ : X n → ℝ) (hρ : ContinuousOn ρ V) (hρpos : ∀ x ∈ V, 0 < ρ x)
    (hPair : ∀ φ : X n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ V →
      ∃ a : F,
        (∀ p ∈ (𝓡∂ n).interior M₁, E₁ p a = ∫ x in V, φ x * G₁ (c₁.symm x, p) * ρ x) ∧
        (∀ p ∈ (𝓡∂ n).interior M₂, E₂ p a = ∫ x in V, φ x * G₂ (c₂.symm x, p) * ρ x)) :
    ∀ q ∈ Φ.source, ∀ x ∈ Φ.source, x ≠ q → G₁ (Φ x, Φ q) = G₂ (x, q) := by
  let A := c₂.symm '' V
  have hA : IsOpen A := c₂.isOpen_image_symm_of_subset_target hV hV₂
  have hConn : IsConnected A := hVConn.image c₂.symm (c₂.continuousOn_symm.mono hV₂)
  apply green_eqOn_matchedDomain hn Φ hΦ hI₂ hI₁ hW hμ₁ hμ₂ hG₁ hG₂ hA hConn
    (image_subset_iff.mpr hCap)
  intro q hq x hx hneq
  obtain ⟨z, hz, rfl⟩ := hx
  let V' := V ∩ c₂.symm ⁻¹' ({q} : Set M₂)ᶜ
  have hV' : IsOpen V' := (c₂.continuousOn_symm.mono hV₂).isOpen_inter_preimage hV
    isClosed_singleton.isOpen_compl
  have hV'sub : V' ⊆ V := inter_subset_left
  have hNear₁ : MapsTo c₁.symm V' ({Φ q} : Set M₁)ᶜ := by
    intro y hy
    change c₁.symm y ∉ ({Φ q} : Set M₁)
    intro he
    have he' := (hId hy.1).symm.trans (mem_singleton_iff.mp he)
    exact hy.2 (mem_singleton_iff.mpr (Φ.injOn (hCap hy.1) hq he'))
  have hNear₂ : MapsTo c₂.symm V' ({q} : Set M₂)ᶜ := fun _ hy => hy.2
  have hp₁ := hI₁ (Φ.map_source hq)
  have hp₂ := hI₂ hq
  have h₁ := (hG₁.continuous_off_pole (Φ q) hp₁).comp
    (c₁.continuousOn_symm.mono (hV'sub.trans hV₁)) hNear₁
  have h₂ := (hG₂.continuous_off_pole q hp₂).comp
    (c₂.continuousOn_symm.mono (hV'sub.trans hV₂)) hNear₂
  have hEq := eqOn_of_weighted_test_pairings hV' hV'sub (hρ.mono hV'sub)
    (fun y hy => hρpos y hy.1) h₁ h₂ (by
      intro φ hφ hc hs
      obtain ⟨a, h₁, h₂⟩ := hPair φ hφ hc (hs.trans hV'sub)
      exact (h₁ _ hp₁).symm.trans ((congrFun (hEval q hq) a).symm.trans (h₂ _ hp₂)))
  have hzz : z ∈ V' := ⟨hz, fun h => hneq (mem_singleton_iff.mp h)⟩
  calc
    G₁ (Φ (c₂.symm z), Φ q) = G₁ (c₁.symm z, Φ q) :=
      congrArg (fun y => G₁ (y, Φ q)) (hId hz).symm
    _ = G₂ (c₂.symm z, q) := hEq hzz

end CalderonPatch
