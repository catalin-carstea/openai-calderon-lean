module

public import Proof.CalderonN.NormalGreenCutoff

import Proof.CalderonN.GreenWeak
import Proof.CalderonN.CrossProductWeak
import Proof.CalderonN.ChartUniqueContinuation
import Mathlib.Tactic

public section

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

namespace NormalGreenCutoff

variable {Y Ω : Set (X dim)} {γ g₁ g₂ : (MetricField dim)} {ρ : ℝ} {E V : (X dim) × (X dim) → (X dim)}
  {O : Set ((X dim) × (X dim))} {r u : (X dim) → ℝ} {y : (X dim)}

private theorem pair_mem_of_mem_source
    (hΩ : IsOpen Ω) (hNΩ : normalPairDomain Y γ ρ E ⊆ Ω ×ˢ Y)
    (hExact : ∀ z ∈ normalVelocityDomain Y γ ρ, V (E z,z.1) = z.2)
    (hInv : ∀ q ∈ normalPairDomain Y γ ρ E,
      (q.2,V q) ∈ normalVelocityDomain Y γ ρ ∧ E (q.2,V q) = q.1)
    (hu : Harmonic Ω g₁ u) (hy : y ∈ Y) {η : ℝ} {φ : (X dim) → ℝ}
    (h : NormalGreenCutoff Y γ ρ E V O r u y η φ) {x : (X dim)}
    (hx : x ∈ tsupport (greenCutoffSource g₁ φ)) : (x,y) ∈ O :=
  h.shell x (h.source_subset_shell hΩ hNΩ hExact hInv hy hu hx)

private theorem integrable_pairing (hΩ : IsOpen Ω)
    (hg₁ : SmoothMetric univ g₁) (hNΩ : normalPairDomain Y γ ρ E ⊆ Ω ×ˢ Y)
    (hExact : ∀ z ∈ normalVelocityDomain Y γ ρ, V (E z,z.1) = z.2)
    (hInv : ∀ q ∈ normalPairDomain Y γ ρ E,
      (q.2,V q) ∈ normalVelocityDomain Y γ ρ ∧ E (q.2,V q) = q.1)
    (hu : Harmonic Ω g₁ u) (hy : y ∈ Y)
    {F : (X dim) × (X dim) → ℝ} (hF : ProductSolutionOn g₁ g₂ O F)
    {η : ℝ} {φ : (X dim) → ℝ} (h : NormalGreenCutoff Y γ ρ E V O r u y η φ) :
    Integrable (fun x => F (x,y) * greenCutoffSource g₁ φ x) := by
  let K := tsupport (greenCutoffSource g₁ φ)
  have hK : IsCompact K := h.compact.of_isClosed_subset (isClosed_tsupport _)
    (tsupport_greenCutoffSource_subset g₁ φ)
  exact integrable_greenCutoffPairing_of_compact_source hg₁ hK
    (hF.1.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun _ hx => h.pair_mem_of_mem_source hΩ hNΩ hExact hInv hu hy hx)) h.smooth h.compact Subset.rfl

private theorem pairing_eq_of_width_le
    (hΩ : IsOpen Ω) (hg₁ : SmoothMetric univ g₁)
    (hN : IsOpen (normalPairDomain Y γ ρ E)) (hNΩ : normalPairDomain Y γ ρ E ⊆ Ω ×ˢ Y)
    {F : (X dim) × (X dim) → ℝ} (hF : ProductSolutionOn g₁ g₂ O F)
    (hγ : SmoothMetric univ γ) (hVc : ContinuousOn V (normalPairDomain Y γ ρ E))
    (hExact : ∀ z ∈ normalVelocityDomain Y γ ρ, V (E z,z.1) = z.2)
    (hInv : ∀ q ∈ normalPairDomain Y γ ρ E,
      (q.2,V q) ∈ normalVelocityDomain Y γ ρ ∧ E (q.2,V q) = q.1)
    (hu : Harmonic Ω g₁ u) (hy : y ∈ Y)
    {η₁ η₂ : ℝ} {φ₁ φ₂ : (X dim) → ℝ} (h₁ : NormalGreenCutoff Y γ ρ E V O r u y η₁ φ₁)
    (h₂ : NormalGreenCutoff Y γ ρ E V O r u y η₂ φ₂) (hle : η₁ ≤ η₂) :
    greenCutoffPairing g₁ F φ₁ y = greenCutoffPairing g₁ F φ₂ y := by
  let N := normalPairDomain Y γ ρ E
  let S := normalShellRoom N γ V y (r y-η₂) (r y+η₂)
  have hS : IsOpen S := isOpen_normalShellRoom hN hγ hVc _ _ _
  have hSf : Harmonic S g₁ (fun x => F (x,y)) := by
    have hsub : S ×ˢ ({y} : Set (X dim)) ⊆ O := by
      rintro ⟨x,z⟩ hz
      obtain rfl : z = y := mem_singleton_iff.mp hz.2
      exact h₂.shell x hz.1
    exact (hF.mono hsub).harmonic_left (mem_singleton y)
  have hbound : (r y+η₁)^2 ≤ (r y+η₂)^2 :=
    pow_le_pow_left₀ (by linarith [h₁.inner_pos,h₁.width_pos]) (by linarith) 2
  have hInner : (r y-η₂)^2 ≤ (r y-η₁)^2 :=
    pow_le_pow_left₀ h₂.inner_pos.le (by linarith) 2
  have hCap₁ : r y-η₁ < ρ := by linarith [h₁.outer_lt,h₁.width_pos]
  have hCap₂ : r y-η₂ < ρ := by linarith [h₂.outer_lt,h₂.width_pos]
  have hdiff : tsupport (φ₁-φ₂) ⊆ S := by
    intro x hx
    have hout : x ∈ normalBallRoom N γ V y (r y+η₂) := by
      rcases tsupport_sub φ₁ φ₂ hx with hx₁ | hx₂
      · exact ⟨(h₁.outer hx₁).1,(h₁.outer hx₁).2.trans_le hbound⟩
      · exact h₂.outer hx₂
    refine ⟨hout.1,lt_of_not_ge (fun hi => ?_),hout.2⟩
    have hx₁ := (mem_closedBallImage_iff_normalRadialSq hExact hInv hy h₁.inner_pos.le hCap₁).mpr
      ⟨hout.1,hi.trans hInner⟩
    have hx₂ := (mem_closedBallImage_iff_normalRadialSq hExact hInv hy h₂.inner_pos.le hCap₂).mpr
      ⟨hout.1,hi⟩
    exact (notMem_tsupport_iff_eventuallyEq.mpr
      (((h₁.inner x hx₁).and (h₂.inner x hx₂)).mono fun z hz => by
        change φ₁ z-φ₂ z = 0
        rw [hz.1,hz.2,sub_self])) hx
  exact greenCutoffPairing_eq_of_harmonic_difference hS (smoothMetric_restrict hg₁ (subset_univ _))
    hSf h₁.smooth h₂.smooth h₁.compact h₂.compact
    (h₁.integrable_pairing hΩ hg₁ hNΩ hExact hInv hu hy hF)
    (h₂.integrable_pairing hΩ hg₁ hNΩ hExact hInv hu hy hF) hdiff

theorem pairing_eq
    (hΩ : IsOpen Ω) (hg₁ : SmoothMetric univ g₁)
    (hN : IsOpen (normalPairDomain Y γ ρ E)) (hNΩ : normalPairDomain Y γ ρ E ⊆ Ω ×ˢ Y)
    {F : (X dim) × (X dim) → ℝ} (hF : ProductSolutionOn g₁ g₂ O F)
    (hγ : SmoothMetric univ γ) (hVc : ContinuousOn V (normalPairDomain Y γ ρ E))
    (hExact : ∀ z ∈ normalVelocityDomain Y γ ρ, V (E z,z.1) = z.2)
    (hInv : ∀ q ∈ normalPairDomain Y γ ρ E,
      (q.2,V q) ∈ normalVelocityDomain Y γ ρ ∧ E (q.2,V q) = q.1)
    (hu : Harmonic Ω g₁ u) (hy : y ∈ Y)
    {η₁ η₂ : ℝ} {φ₁ φ₂ : (X dim) → ℝ} (h₁ : NormalGreenCutoff Y γ ρ E V O r u y η₁ φ₁)
    (h₂ : NormalGreenCutoff Y γ ρ E V O r u y η₂ φ₂) :
    greenCutoffPairing g₁ F φ₁ y = greenCutoffPairing g₁ F φ₂ y := by
  rcases le_total η₁ η₂ with h | h
  · exact pairing_eq_of_width_le hΩ hg₁ hN hNΩ hF hγ hVc hExact hInv hu hy h₁ h₂ h
  · exact (pairing_eq_of_width_le hΩ hg₁ hN hNΩ hF hγ hVc hExact hInv hu hy h₂ h₁ h).symm

end NormalGreenCutoff

/-- On a known Green slice the compact pairing is evaluation at the
center. The cutoff source can be tested using the original Green law. -/
theorem NormalGreenCutoff.pairing_eq_value
    {Y Ω : Set (X dim)} (hΩ : IsOpen Ω) {γ g : (MetricField dim)}
    {ρ : ℝ} {E V : (X dim) × (X dim) → (X dim)} (hNΩ : normalPairDomain Y γ ρ E ⊆ Ω ×ˢ Y)
    (hExact : ∀ z ∈ normalVelocityDomain Y γ ρ, V (E z,z.1) = z.2)
    (hInv : ∀ q ∈ normalPairDomain Y γ ρ E,
      (q.2,V q) ∈ normalVelocityDomain Y γ ρ ∧ E (q.2,V q) = q.1)
    {O : Set ((X dim) × (X dim))} {r u φ : (X dim) → ℝ} {y : (X dim)} (hy : y ∈ Y) {η : ℝ}
    (h : NormalGreenCutoff Y γ ρ E V O r u y η φ)
    (hCenter : E (y,0) = y) (hu : Harmonic Ω g u)
    {F G : (X dim) × (X dim) → ℝ} (hG : GreenGerm Ω g G)
    (hEq : ∀ x, (x,y) ∈ normalPairDomain Y γ ρ E → x ≠ y → F (x,y) = G (x,y)) :
    greenCutoffPairing g F φ y = u y := by
  have hyV : (y,(0 : (X dim))) ∈ normalVelocityDomain Y γ ρ := by
    have hρ : 0 < ρ := by linarith [h.inner_pos,h.outer_lt,h.width_pos]
    exact ⟨hy,by simp [metricPair,pow_pos hρ]⟩
  have hyN : (y,y) ∈ normalPairDomain Y γ ρ E := ⟨(y,0),hyV,Prod.ext hCenter rfl⟩
  have hZero : V (y,y) = 0 := by simpa only [hCenter] using hExact (y,0) hyV
  have hyInn : y ∈ closedBallImage γ E (fun _ => r y-η) y :=
    ⟨0,by simp [disk,metricPair,sq_nonneg],hCenter⟩
  have hφy : φ y = u y := (h.inner y hyInn).eq_of_nhds
  rw [← hφy]
  apply greenCutoffPairing_eq_value_of_greenGerm hΩ hG h.smooth h.compact
    (fun x hx => (hNΩ (h.outer hx).1).1) (hNΩ hyN).1
  intro x hx
  have hs := h.source_subset_shell hΩ hNΩ hExact hInv hy hu hx
  refine hEq x hs.1 (fun he => ?_)
  subst x
  have hs' : (r y-η)^2 < normalRadialSq γ V (y,y) := hs.2.1
  simp only [normalRadialSq,hZero,metricPair,PiLp.zero_apply,mul_zero,Finset.sum_const_zero] at hs'
  exact (sq_nonneg _).not_gt hs'

/-- The Green transfer is a well-defined second-side harmonic function on
the center domain. Locally it is computed by one fixed compact source. -/
theorem exists_harmonic_normalGreenTransfer
    {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {γ g₁ g₂ : (MetricField dim)} (hγ : SmoothMetric univ γ) (hg₁ : SmoothMetric univ g₁)
    {ρ : ℝ} {E V : (X dim) × (X dim) → (X dim)} (hE : Continuous E)
    (hN : IsOpen (normalPairDomain Y γ ρ E)) (hNΩ : normalPairDomain Y γ ρ E ⊆ Ω ×ˢ Y)
    (hV : ContinuousOn V (normalPairDomain Y γ ρ E))
    (hExact : ∀ z ∈ normalVelocityDomain Y γ ρ, V (E z,z.1) = z.2)
    (hInv : ∀ q ∈ normalPairDomain Y γ ρ E,
      (q.2,V q) ∈ normalVelocityDomain Y γ ρ ∧ E (q.2,V q) = q.1)
    {O : Set ((X dim) × (X dim))} (hO : IsOpen O)
    {F : (X dim) × (X dim) → ℝ} (hF : ProductSolutionOn g₁ g₂ O F)
    {e : (Frame dim)} (he : ∀ y ∈ Y, ∀ i j, metricPair γ y (e y i) (e y j) = if i = j then 1 else 0)
    (hec : ∀ i, ContinuousOn (fun y => e y i) Y) {r : (X dim) → ℝ}
    (hrc : ContinuousOn r Y) (hr : ∀ y ∈ Y, 0 < r y ∧ r y < ρ)
    (hSphere : ∀ y ∈ Y, ∀ w : ↥(standardSphere dim), (E (y,r y • frameVector e y w),y) ∈ O)
    {u : (X dim) → ℝ} (hu : Harmonic Ω g₁ u) :
    ∃ T : (X dim) → ℝ, Harmonic Y g₂ T ∧
      ∀ y ∈ Y, ∀ η φ, NormalGreenCutoff Y γ ρ E V O r u y η φ →
        T y = greenCutoffPairing g₁ F φ y := by
  classical
  have hLocal (y : (X dim)) (hy : y ∈ Y) :
      ∃ η φ, ∀ᶠ z in 𝓝 y, NormalGreenCutoff Y γ ρ E V O r u z η φ :=
    exists_eventually_normalGreenCutoff hY hΩ hγ hE hN hNΩ hV hExact hInv hO hy he
      (fun i => (hec i).continuousAt (hY.mem_nhds hy)) (hrc.continuousAt (hY.mem_nhds hy))
      (hr y hy).1 (hr y hy).2 (hSphere y hy) hu.1
  let P (z : (X dim)) (φ : (X dim) → ℝ) := ∃ η, NormalGreenCutoff Y γ ρ E V O r u z η φ
  let T (z : (X dim)) := if h : ∃ φ, P z φ then greenCutoffPairing g₁ F h.choose z else 0
  have hT (z : (X dim)) (hz : z ∈ Y) (η : ℝ) (φ : (X dim) → ℝ)
      (hφ : NormalGreenCutoff Y γ ρ E V O r u z η φ) : T z = greenCutoffPairing g₁ F φ z := by
    have h : ∃ φ, P z φ := ⟨φ,η,hφ⟩
    obtain ⟨η₀,h₀⟩ := h.choose_spec
    dsimp only [T]
    rw [dite_eq_left h]
    exact h₀.pairing_eq hΩ hg₁ hN hNΩ hF hγ hV hExact hInv hu hz hφ
  have hH (y : (X dim)) (hy : y ∈ Y) : ∃ V₀ : Set (X dim), IsOpen V₀ ∧ y ∈ V₀ ∧ Harmonic V₀ g₂ T := by
    obtain ⟨η,φ,hφ⟩ := hLocal y hy
    let K := tsupport (greenCutoffSource g₁ φ)
    have hyφ := mem_of_mem_nhds hφ
    have hK : IsCompact K := hyφ.compact.of_isClosed_subset (isClosed_tsupport _)
      (tsupport_greenCutoffSource_subset g₁ φ)
    have hProd : K ×ˢ ({y} : Set (X dim)) ⊆ O := by
      rintro ⟨x,z⟩ hz
      obtain rfl : z = y := mem_singleton_iff.mp hz.2
      exact hyφ.pair_mem_of_mem_source hΩ hNΩ hExact hInv hu hy hz.1
    obtain ⟨A,B,hA,hB,hKA,hyB,hAB⟩ := generalized_tube_lemma hK isCompact_singleton hO hProd
    have hJ := greenCutoffPairing_harmonic_of_compact_source hg₁ hA hB hK hKA (hF.mono hAB)
      hyφ.smooth hyφ.compact (show K ⊆ K from Subset.rfl)
    have hNear : {z | NormalGreenCutoff Y γ ρ E V O r u z η φ} ∩ Y ∩ B ∈ 𝓝 y :=
      inter_mem (inter_mem hφ (hY.mem_nhds hy)) (hB.mem_nhds (hyB (mem_singleton y)))
    obtain ⟨D,hD,hDo,hyD⟩ := _root_.mem_nhds_iff.mp hNear
    have heq : EqOn T (greenCutoffPairing g₁ F φ) D := fun z hz =>
      hT z (hD hz).1.2 η φ (hD hz).1.1
    exact ⟨D,hDo,hyD,(hJ.1.mono (fun z hz => (hD hz).2)).congr heq,fun z hz =>
      (laplace_congrOn hDo (fun _ _ => rfl) heq hz).trans (hJ.2 z (hD hz).2)⟩
  refine ⟨T,⟨?_,?_⟩,hT⟩
  · apply contDiffOn_of_locally_contDiffOn
    intro y hy
    obtain ⟨D,hDo,hyD,hD⟩ := hH y hy
    exact ⟨D,hDo,hyD,hD.1.mono inter_subset_right⟩
  · intro y hy
    obtain ⟨D,_,hyD,hD⟩ := hH y hy
    exact hD.2 y hyD

end CalderonN
