module

public import Proof.CalderonN.MovingCutoffGeometry
public import Proof.CalderonN.GreenCutoffPairing

import Proof.CalderonN.EllipticCalculus
import Proof.CalderonN.GreenWeak
import Mathlib.Tactic

public section

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

/-- A fixed smooth test that equals the first-side harmonic function near
the inner ball. Its transition shell lies where the actual kernel is known. -/
structure NormalGreenCutoff (Y : Set (X dim)) (γ : (MetricField dim)) (ρ : ℝ) (E V : (X dim) × (X dim) → (X dim))
    (O : Set ((X dim) × (X dim))) (r : (X dim) → ℝ) (u : (X dim) → ℝ) (y : (X dim)) (η : ℝ) (φ : (X dim) → ℝ) : Prop where
  width_pos : 0 < η
  inner_pos : 0 < r y - η
  outer_lt : r y + η < ρ
  smooth : ContDiff ℝ ∞ φ
  compact : HasCompactSupport φ
  inner : ∀ x ∈ closedBallImage γ E (fun _ => r y - η) y, φ =ᶠ[𝓝 x] u
  inside : tsupport φ ⊆ normalBallRoom (normalPairDomain Y γ ρ E) γ V y (r y)
  shell : ∀ x ∈ normalShellRoom (normalPairDomain Y γ ρ E) γ V y (r y - η) (r y + η), (x,y) ∈ O

theorem NormalGreenCutoff.outer {Y : Set (X dim)} {γ : (MetricField dim)} {ρ : ℝ} {E V : (X dim) × (X dim) → (X dim)}
    {O : Set ((X dim) × (X dim))} {r u φ : (X dim) → ℝ} {y : (X dim)} {η : ℝ}
    (h : NormalGreenCutoff Y γ ρ E V O r u y η φ) :
    tsupport φ ⊆ normalBallRoom (normalPairDomain Y γ ρ E) γ V y (r y + η) := by
  intro x hx
  exact ⟨(h.inside hx).1,(h.inside hx).2.trans_le
    (pow_le_pow_left₀ (by linarith [h.inner_pos,h.width_pos]) (by linarith [h.width_pos]) 2)⟩

/-- A single cutoff works for all centers in a sufficiently small neighborhood
of each center. Its construction uses the exact normal endpoint map. -/
theorem exists_eventually_normalGreenCutoff
    {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {γ : (MetricField dim)} (hγ : SmoothMetric univ γ) {ρ : ℝ} {E V : (X dim) × (X dim) → (X dim)}
    (hE : Continuous E)
    (hN : IsOpen (normalPairDomain Y γ ρ E)) (hNΩ : normalPairDomain Y γ ρ E ⊆ Ω ×ˢ Y)
    (hV : ContinuousOn V (normalPairDomain Y γ ρ E))
    (hExact : ∀ z ∈ normalVelocityDomain Y γ ρ, V (E z,z.1) = z.2)
    (hInv : ∀ q ∈ normalPairDomain Y γ ρ E,
      (q.2,V q) ∈ normalVelocityDomain Y γ ρ ∧ E (q.2,V q) = q.1)
    {O : Set ((X dim) × (X dim))} (hO : IsOpen O) {y₀ : (X dim)} (hy₀ : y₀ ∈ Y)
    {e : (Frame dim)} (he : ∀ y ∈ Y, ∀ i j, metricPair γ y (e y i) (e y j) = if i = j then 1 else 0)
    (hec : ∀ i, ContinuousAt (fun y => e y i) y₀) {r : (X dim) → ℝ}
    (hrc : ContinuousAt r y₀) (hr : 0 < r y₀) (hρ : r y₀ < ρ)
    (hSphere : ∀ w : ↥(standardSphere dim), (E (y₀,r y₀ • frameVector e y₀ w),y₀) ∈ O)
    {u : (X dim) → ℝ} (hu : ContDiffOn ℝ ∞ u Ω) :
    ∃ η φ, ∀ᶠ y in 𝓝 y₀, NormalGreenCutoff Y γ ρ E V O r u y η φ := by
  obtain ⟨η,hη,hηr,hηρ,hShell⟩ := exists_eventually_normalShellRoom_subset hE hInv hO he hec hrc hr hρ hSphere
  let a := r y₀-η/2
  let b := r y₀-η/4
  let N := normalPairDomain Y γ ρ E
  let D := normalBallRoom N γ V y₀ b
  let K := closedBallImage γ E (fun _ => a) y₀
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have hab : a < b := by dsimp [a,b]; linarith
  have hb : b ≤ ρ := by dsimp [b]; linarith
  have hD : IsOpen D := isOpen_normalBallRoom hN hγ hV _ _
  have hK : IsCompact K := isCompact_closedBallImage γ hE e y₀ (he y₀ hy₀) ha
  have hKD : K ⊆ D := closedBallImage_subset_normalBallRoom hExact hInv hy₀ ha hab hb
  have hDΩ : D ⊆ Ω := fun x hx => (hNΩ hx.1).1
  obtain ⟨χ,hχ,hχc,hχD,hχ1⟩ := Elliptic.exists_plateau_cutoff hD hK hKD
  let U := interior {x : (X dim) | χ x = 1}
  have hKU : K ⊆ U := fun x hx => mem_interior_iff_mem_nhds.mpr (hχ1 x hx)
  have hInner : closedBallImage γ E (fun y => r y-η) y₀ ⊆ U := by
    intro x hx
    obtain ⟨v,hv,rfl⟩ := hx
    apply hKU
    have hrad : (r y₀-η)^2 ≤ a^2 :=
      pow_le_pow_left₀ (sub_nonneg.mpr hηr.le) (show r y₀-η ≤ a by dsimp [a]; linarith) 2
    exact ⟨v,hv.trans hrad,rfl⟩
  have hNearInner := eventually_closedBallImage_subset hE isOpen_interior (hY.mem_nhds hy₀) he hec
    (hrc.sub continuousAt_const) (sub_pos.mpr hηr) hInner
  have hχOuter : tsupport χ ⊆ normalBallRoom N γ V y₀ (r y₀) := by
    intro x hx
    refine ⟨(hχD hx).1,(hχD hx).2.trans_le ?_⟩
    exact pow_le_pow_left₀ (by dsimp [b]; linarith) (by dsimp [b]; linarith) 2
  have hNearOuter := eventually_subset_normalBallRoom hN hγ hV hχc hrc hχOuter
  let φ : (X dim) → ℝ := fun x => χ x * u x
  have hφ : ContDiff ℝ ∞ φ :=
    Elliptic.contDiff_mul_of_tsupport_subset hΩ hχ (hχD.trans hDΩ) hu
  have hφχ : tsupport φ ⊆ tsupport χ := tsupport_mul_subset_left
  have hφc : HasCompactSupport φ := hχc.of_isClosed_subset (isClosed_tsupport φ) hφχ
  refine ⟨η,φ,?_⟩
  filter_upwards [hShell,hNearInner,hNearOuter] with y hShell hI hOut
  refine ⟨hη,hShell.1,hShell.2.1,hφ,hφc,?_,hφχ.trans hOut,hShell.2.2⟩
  intro x hx
  have hnear : ∀ᶠ z in 𝓝 x, z ∈ U := isOpen_interior.mem_nhds (hI hx)
  exact hnear.mono fun z hz => by
    have h1 : z ∈ {x : (X dim) | χ x = 1} := interior_subset hz
    change χ z * u z = u z
    rw [(show χ z = 1 from h1),one_mul]

theorem NormalGreenCutoff.source_subset_shell
    {Y Ω : Set (X dim)} (hΩ : IsOpen Ω)
    {γ g : (MetricField dim)} {ρ : ℝ} {E V : (X dim) × (X dim) → (X dim)}
    (hNΩ : normalPairDomain Y γ ρ E ⊆ Ω ×ˢ Y)
    (hExact : ∀ z ∈ normalVelocityDomain Y γ ρ, V (E z,z.1) = z.2)
    (hInv : ∀ q ∈ normalPairDomain Y γ ρ E,
      (q.2,V q) ∈ normalVelocityDomain Y γ ρ ∧ E (q.2,V q) = q.1)
    {O : Set ((X dim) × (X dim))} {r u φ : (X dim) → ℝ} {y : (X dim)} (hy : y ∈ Y) {η : ℝ}
    (h : NormalGreenCutoff Y γ ρ E V O r u y η φ) (hu : Harmonic Ω g u) :
    tsupport (greenCutoffSource g φ) ⊆
      normalShellRoom (normalPairDomain Y γ ρ E) γ V y (r y - η) (r y + η) := by
  intro x hx
  have hout := h.outer (tsupport_greenCutoffSource_subset g φ hx)
  refine ⟨hout.1,lt_of_not_ge fun hi => ?_,hout.2⟩
  have hin : x ∈ closedBallImage γ E (fun _ => r y-η) y :=
    (mem_closedBallImage_iff_normalRadialSq hExact hInv hy h.inner_pos.le
      (by linarith [h.width_pos,h.outer_lt])).mpr ⟨hout.1,hi⟩
  have hxΩ := (hNΩ hout.1).1
  have he : {z | φ z = u z} ∩ Ω ∈ 𝓝 x := inter_mem (h.inner x hin) (hΩ.mem_nhds hxΩ)
  exact (notMem_tsupport_iff_eventuallyEq.mpr (by
    obtain ⟨U,hU,hUo,hxU⟩ := _root_.mem_nhds_iff.mp he
    have hnear : ∀ᶠ z in 𝓝 x, z ∈ U := hUo.mem_nhds hxU
    exact hnear.mono fun z hz => by
      have hl := laplace_congrOn hUo (g := g) (h := g) (fun _ _ => rfl) (fun w hw => (hU hw).1) hz
      simp [greenCutoffSource,hl,hu.2 z (hU hz).2])) hx

end CalderonN
