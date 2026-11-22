module

public import Proof.CalderonN.OrthogonalFrameContraction
public import Proof.CalderonN.UniformCanonicalFrameJets

import Proof.CalderonN.MetricConnection
import Mathlib.Tactic

/-! Changing the orthonormal trivialization leaves the physical problem,
sphere averaging, and the admitted covariant radius bounds invariant. -/

public section

noncomputable section
open Set
open scoped ContDiff
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

theorem fiberSq_eq_of_orthonormalFrames (g : MetricField dim) (y : X dim) (e f : Frame dim)
    (he : ∀ i j, metricPair g y (e y i) (e y j) = if i=j then 1 else 0)
    (hf : ∀ i j, metricPair g y (f y i) (f y j) = if i=j then 1 else 0)
    (u : X dim → ℂ) :
    fiberSq f y u = fiberSq e y u :=
  congrArg Complex.re (sphereAverage_eq_of_orthonormalFrames g y e f he hf _)

theorem degreePart_eq_of_orthonormalFrames (g : MetricField dim) (y : X dim) (e f : Frame dim)
    (he : ∀ i j, metricPair g y (e y i) (e y j) = if i=j then 1 else 0)
    (hf : ∀ i j, metricPair g y (f y i) (f y j) = if i=j then 1 else 0)
    (k : ℕ) (u : X dim → ℂ) :
    degreePart g f k y u = degreePart g e k y u := by
  funext w
  exact congrArg ((harmonicMultiplicity dim k : ℂ)*·)
    (sphereAverage_eq_of_orthonormalFrames g y e f he hf _)

theorem sobolevSq_eq_of_orthonormalFrames (g : MetricField dim) (y : X dim) (e f : Frame dim)
    (he : ∀ i j, metricPair g y (e y i) (e y j) = if i=j then 1 else 0)
    (hf : ∀ i j, metricPair g y (f y i) (f y j) = if i=j then 1 else 0)
    (s : ℝ) (u : X dim → ℂ) :
    sobolevSq g f s y u = sobolevSq g e s y u := by
  unfold sobolevSq
  simp_rw [degreePart_eq_of_orthonormalFrames g y e f he hf,
    fiberSq_eq_of_orthonormalFrames g y e f he hf]

variable {Y Ω : Set (X dim)} {K ρ c₀ floor ε : ℝ} {m : ℕ}
variable {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {g : MetricField dim} {e f : Frame dim}

theorem Test.of_orthonormalFrames {φ : Field dim} (hφ : Test Y g e φ)
    (he : ∀ y ∈ Y, ∀ i j, metricPair g y (e y i) (e y j) = if i=j then 1 else 0)
    (hf : ∀ y ∈ Y, ∀ i j, metricPair g y (f y i) (f y j) = if i=j then 1 else 0) :
    Test Y g f φ := by
  refine ⟨hφ.1,hφ.2.1,fun y hy => ?_⟩
  rw [sphereAverage_eq_of_orthonormalFrames g y e f (he y hy) (hf y hy)]
  exact hφ.2.2 y hy

theorem Profile.of_orthonormalFrames {r : X dim → ℝ} (hp : Profile Y g e r floor c₀ Cj)
    (he : ∀ y ∈ Y, ∀ i j, metricPair g y (e y i) (e y j) = if i=j then 1 else 0)
    (hf : ∀ y ∈ Y, ∀ i j, metricPair g y (f y i) (f y j) = if i=j then 1 else 0)
    (hSym : ∀ y ∈ Y, (g y).transpose = g y) :
    Profile Y g f r floor c₀ Cj := by
  refine ⟨hp.1,fun y hy => ?_⟩
  obtain ⟨hr,hβ,hH,hJ⟩ := hp.2 y hy
  refine ⟨hr,hβ,hH,fun j hj => ?_⟩
  rw [jetNorm_eq_of_orthonormalFrames g y e f (he y hy) (hf y hy) (hSym y hy)]
  exact hJ j hj

theorem IsMovingTraceAdjoint.of_orthonormalFrames {g₁ : MetricField dim}
    {P : X dim × X dim → X dim} {r : X dim → ℝ} {A : TraceAdjoint dim}
    (h : IsMovingTraceAdjoint Y g g₁ e P r A)
    (he : ∀ y ∈ Y, ∀ i j, metricPair g y (e y i) (e y j) = if i=j then 1 else 0)
    (hf : ∀ y ∈ Y, ∀ i j, metricPair g y (f y i) (f y j) = if i=j then 1 else 0) :
    IsMovingTraceAdjoint Y g g₁ f P r A := by
  intro i v hv
  refine ⟨(h i v hv).1,fun y hy u hu => ?_⟩
  dsimp only
  rw [sphereAverage_eq_of_orthonormalFrames g y e f (he y hy) (hf y hy),
    sphereAverage_eq_of_orthonormalFrames g y e f (he y hy) (hf y hy)]
  exact (h i v hv).2 y hy u hu

@[expose] def Data.reframe (d : Data dim) (f : Frame dim) : Data dim :=
  {d with frame := f}

theorem Admissible.reframe {d : Data dim} (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d)
    (hsub : Y ⊆ Ω) (hfSmooth : ∀ i, ContDiffOn ℝ ∞ (fun y => f y i) Ω)
    (hf : ∀ y ∈ Ω, ∀ i j, metricPair d.γ y (f y i) (f y j) = if i=j then 1 else 0) :
    Admissible Y Ω K ρ c₀ M Cj floor ε (d.reframe f) := by
  obtain ⟨hBG,hN,hD,hA,hP,hS⟩ := hd
  obtain ⟨hE,hE₁,hE₂,hCon,hJets,hDrift,hSmooth,he⟩ := hBG
  have heY := fun y hy => he y (hsub hy)
  have hfY := fun y hy => hf y (hsub hy)
  exact ⟨⟨hE,hE₁,hE₂,hCon,hJets,hDrift,hfSmooth,hf⟩,hN,hD,hA.of_orthonormalFrames heY hfY,
    hP.of_orthonormalFrames heY hfY (fun y hy => (hE.2 y (hsub hy)).1),hS⟩

theorem traceNorm_reframe {d : Data dim} (hY : IsOpen Y)
    (he : ∀ y ∈ Y, ∀ i j, metricPair d.γ y (d.frame y i) (d.frame y j) = if i=j then 1 else 0)
    (hf : ∀ y ∈ Y, ∀ i j, metricPair d.γ y (f y i) (f y j) = if i=j then 1 else 0)
    (φ : Field dim) :
    traceNorm Y (d.reframe f) φ = traceNorm Y d φ := by
  unfold traceNorm outputSq
  congr 1
  apply MeasureTheory.setIntegral_congr_fun hY.measurableSet
  intro y hy
  dsimp only [Data.reframe]
  rw [fiberSq_eq_of_orthonormalFrames d.γ y d.frame f (he y hy) (hf y hy)]

end CalderonN
