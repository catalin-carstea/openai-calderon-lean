module

public import Proof.CalderonPatch.CoordinateEnergy
public import Proof.CalderonPatch.MatchedCoordinates

import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.Geometry.Manifold.Algebra.SMul
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

noncomputable section
open Filter Set
open scoped ContDiff Manifold Topology

namespace CalderonPatch

open CalderonN (I X axis)

variable {n : ℕ} [NeZero n] {F M₁ M₂ M : Type*}
  [TopologicalSpace M₁] [ChartedSpace (EuclideanHalfSpace n) M₁] [IsManifold (𝓡∂ n) ∞ M₁]
  [TopologicalSpace M₂] [ChartedSpace (EuclideanHalfSpace n) M₂] [IsManifold (𝓡∂ n) ∞ M₂]
  [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M]

local notation "J" => 𝓡∂ n
local notation "K" => 𝓘(ℝ, X n)
local notation "R" => 𝓘(ℝ, ℝ)

/-- The coordinate tuple formed from the same ordered source labels. -/
def sourceTuple (E : M → F → ℝ) (a : I n → F) (p : M) : X n :=
  ∑ i, E p (a i) • axis i

theorem sourceTuple_apply (E : M → F → ℝ) (a : I n → F) (p : M) (i : I n) :
    (sourceTuple E a p) i = E p (a i) := by
  simp [sourceTuple, axis, Pi.single_apply, mul_ite]

theorem contMDiff_sourceTuple (E : M → F → ℝ) (a : I n → F)
    (hE : ∀ b, ContMDiff J R ∞ (fun p => E p b)) :
    ContMDiff J K ∞ (sourceTuple E a) := by
  rw [← contMDiffOn_univ]
  apply contMDiffOn_finsetSum
  intro i _
  exact (hE (a i)).contMDiffOn.smul contMDiffOn_const

/-- A matched smooth function has the same dual energy on the two sides.
Taking all linear combinations preserves the entire gradient Gram form. -/
theorem covectorEnergy_eq_on_match
    {g₁ : SmoothMetric n M₁} {g₂ : SmoothMetric n M₂}
    {Φ : OpenPartialHomeomorph M₂ M₁} (hΦ : IsLocalMetricIsometry g₁ g₂ Φ)
    {u₁ : M₁ → ℝ} {u₂ : M₂ → ℝ} (hu₁ : ContMDiff J R ∞ u₁)
    (hEq : EqOn u₂ (u₁ ∘ Φ) Φ.source) {p : M₂} (hp : p ∈ Φ.source) :
    covectorEnergy g₂ p (mfderiv J R u₂ p) = covectorEnergy g₁ (Φ p) (mfderiv J R u₁ (Φ p)) := by
  have hMD : Φ.MDifferentiable J J :=
    ⟨hΦ.smooth.mdifferentiableOn (by simp), hΦ.smooth_inverse.mdifferentiableOn (by simp)⟩
  have hEv : u₂ =ᶠ[𝓝 p] u₁ ∘ Φ :=
    Filter.mem_of_superset (Φ.open_source.mem_nhds hp) (fun _ hx => hEq hx)
  have hC := mfderiv_comp p (hu₁.contMDiffAt.mdifferentiableAt (by simp)) (hMD.mdifferentiableAt hp)
  have hD := hEv.mfderiv_eq.trans hC
  calc
    _ = covectorEnergy g₂ p
        ((mfderiv J R u₁ (Φ p)).comp (hMD.mfderiv hp).toContinuousLinearMap) :=
      congrArg (covectorEnergy g₂ p) hD
    _ = _ := covectorEnergy_pullback g₁ g₂ p (Φ p) (hMD.mfderiv hp) (hΦ.metric_eq p hp) _

/-- The limiting partners of an interior frontier point preserve every
quadratic pairing of the differentials of the same source functions. -/
theorem covectorEnergy_eq_at_partner
    {g₁ : SmoothMetric n M₁} {g₂ : SmoothMetric n M₂}
    {Φ : OpenPartialHomeomorph M₂ M₁} (hΦ : IsLocalMetricIsometry g₁ g₂ Φ)
    {p : M₂} {q : M₁} (hp : p ∈ (𝓡∂ n).interior M₂) (hq : q ∈ (𝓡∂ n).interior M₁)
    (hpcl : p ∈ closure Φ.source) (hlim : Tendsto Φ (𝓝[Φ.source] p) (𝓝 q))
    {u₁ : M₁ → ℝ} {u₂ : M₂ → ℝ} (hu₁ : ContMDiff J R ∞ u₁) (hu₂ : ContMDiff J R ∞ u₂)
    (hEq : EqOn u₂ (u₁ ∘ Φ) Φ.source) :
    covectorEnergy g₂ p (mfderiv J R u₂ p) = covectorEnergy g₁ q (mfderiv J R u₁ q) := by
  let A (x : M₂) := covectorEnergy g₂ x (mfderiv J R u₂ x)
  let B (x : M₁) := covectorEnergy g₁ x (mfderiv J R u₁ x)
  have hOpen₂ := (𝓡∂ n).isOpen_interior (M := M₂) (n := ∞) (by simp)
  have hOpen₁ := (𝓡∂ n).isOpen_interior (M := M₁) (n := ∞) (by simp)
  have hA : ContinuousAt A p :=
    (continuousOn_covectorEnergy_mfderiv g₂ hOpen₂ Subset.rfl hu₂.contMDiffOn).continuousAt
      (hOpen₂.mem_nhds hp)
  have hB : ContinuousAt B q :=
    (continuousOn_covectorEnergy_mfderiv g₁ hOpen₁ Subset.rfl hu₁.contMDiffOn).continuousAt
      (hOpen₁.mem_nhds hq)
  have hAE : A =ᶠ[𝓝[Φ.source] p] B ∘ Φ :=
    Filter.mem_of_superset self_mem_nhdsWithin (fun _ hx => covectorEnergy_eq_on_match hΦ hu₁ hEq hx)
  let _ : NeBot (𝓝[Φ.source] p) := mem_closure_iff_nhdsWithin_neBot.mp hpcl
  exact tendsto_nhds_unique_of_eventuallyEq hA.continuousWithinAt (hB.tendsto.comp hlim) hAE

private theorem invertible_of_covectorEnergy_eq
    (g₁ : SmoothMetric n M₁) (g₂ : SmoothMetric n M₂) (p : M₂) (q : M₁)
    (D₁ D₂ : X n →L[ℝ] X n) (hD₂ : D₂.IsInvertible)
    (hEnergy : ∀ a : X n →L[ℝ] ℝ,
      covectorEnergy g₂ p (a.comp D₂) = covectorEnergy g₁ q (a.comp D₁)) :
    D₁.IsInvertible := by
  obtain ⟨e₂, rfl⟩ := hD₂
  have hSurj : Function.Surjective D₁ := by
    apply LinearMap.dualMap_injective_iff.mp
    apply (injective_iff_map_eq_zero _).mpr
    intro b hb
    let a := LinearMap.toContinuousLinearMap b
    have hz : a.comp D₁ = 0 := by
      ext t
      exact congrArg (fun l : Module.Dual ℝ (X n) => l t) hb
    have hzero : covectorEnergy g₂ p (a.comp e₂.toContinuousLinearMap) = 0 :=
      (hEnergy a).trans ((covectorEnergy_eq_zero_iff g₁ q _).mpr hz)
    have hcomp := (covectorEnergy_eq_zero_iff g₂ p _).mp hzero
    ext t
    obtain ⟨s, rfl⟩ := e₂.surjective t
    exact congrArg (fun d : X n →L[ℝ] ℝ => d s) hcomp
  have hInj : Function.Injective D₁ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mpr hSurj
  exact ⟨ContinuousLinearEquiv.ofBijective D₁ (LinearMap.ker_eq_bot.mpr hInj)
      (LinearMap.range_eq_top.mpr hSurj), rfl⟩

/-- Equality of the gradient Gram forms transfers invertibility of a
source coordinate tuple to its limiting partner. -/
theorem invertible_mfderiv_at_partner
    {g₁ : SmoothMetric n M₁} {g₂ : SmoothMetric n M₂}
    {Φ : OpenPartialHomeomorph M₂ M₁} (hΦ : IsLocalMetricIsometry g₁ g₂ Φ)
    {p : M₂} {q : M₁} (hp : p ∈ (𝓡∂ n).interior M₂) (hq : q ∈ (𝓡∂ n).interior M₁)
    (hpcl : p ∈ closure Φ.source) (hlim : Tendsto Φ (𝓝[Φ.source] p) (𝓝 q))
    {f₁ : M₁ → X n} {f₂ : M₂ → X n} (hf₁ : ContMDiff J K ∞ f₁) (hf₂ : ContMDiff J K ∞ f₂)
    (hEq : EqOn f₂ (f₁ ∘ Φ) Φ.source) (hD₂ : (mfderiv J K f₂ p).IsInvertible) :
    (mfderiv J K f₁ q).IsInvertible := by
  apply invertible_of_covectorEnergy_eq g₁ g₂ p q _ _ hD₂
  intro a
  have hcomp : ∀ x : X n, mfderiv K R (a : X n → ℝ) x = a := by
    intro x
    rw [mfderiv_eq_fderiv, ContinuousLinearMap.fderiv]
    ext t
    rfl
  have ha₂ : ContMDiffAt K R ∞ (a : X n → ℝ) (f₂ p) := a.contMDiffAt
  have ha₁ : ContMDiffAt K R ∞ (a : X n → ℝ) (f₁ q) := a.contMDiffAt
  have h₂ := mfderiv_comp p (ha₂.mdifferentiableAt (by simp))
    (hf₂.contMDiffAt.mdifferentiableAt (by simp))
  have h₁ := mfderiv_comp q (ha₁.mdifferentiableAt (by simp))
    (hf₁.contMDiffAt.mdifferentiableAt (by simp))
  have hmf₂ : mfderiv J R (a ∘ f₂) p = a.comp (mfderiv J K f₂ p) :=
    h₂.trans (congrArg (fun L : X n →L[ℝ] ℝ => L.comp (mfderiv J K f₂ p)) (hcomp (f₂ p)))
  have hmf₁ : mfderiv J R (a ∘ f₁) q = a.comp (mfderiv J K f₁ q) :=
    h₁.trans (congrArg (fun L : X n →L[ℝ] ℝ => L.comp (mfderiv J K f₁ q)) (hcomp (f₁ q)))
  have hE := covectorEnergy_eq_at_partner hΦ hp hq hpcl hlim
    (a.contMDiff.comp hf₁) (a.contMDiff.comp hf₂) (fun x hx => congrArg a (hEq hx))
  exact (congrArg (covectorEnergy g₂ p) hmf₂).symm.trans
    (hE.trans (congrArg (covectorEnergy g₁ q) hmf₁))

end CalderonPatch
