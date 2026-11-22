module

public import Proof.CalderonPatch.FixedSupportTestCompleteness
public import Proof.CalderonPatch.CompactSecondJet
public import Mathlib.Analysis.Matrix.Normed

import Proof.CalderonPatch.NormalJetLine
import Mathlib.Analysis.Calculus.LineDeriv.Basic

public section

noncomputable section
open Filter Function Set TopologicalSpace
open scoped ContDiff Distributions Matrix.Norms.Elementwise Topology

namespace CalderonPatch

set_option autoImplicit false

open CalderonN (I X chartDerivativeWord axis)

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Compacts E}

local notation "T" => 𝓓_{K}(E, ℝ)
local notation "Y" => X (m+1)

variable {U : Set (X (m+1))} (hU : IsOpen U) (A : 𝓓_{K}(E, ℝ) → X (m+1) → ℝ)
variable (hSmooth : ∀ f, ContDiffOn ℝ ∞ (A f) U)
variable (hEval : ∀ x ∈ U, ∃ L : 𝓓_{K}(E, ℝ) →L[ℝ] ℝ, ∀ f, L f = A f x)

include hU hSmooth hEval

/-- Directional differentiation of a pointwise smooth family of continuous
linear evaluations gives continuous linear evaluations of every derivative. -/
theorem exists_chartWordEvaluation (w : List (I (m+1))) {x : Y} (hx : x ∈ U) :
    ∃ L : T →L[ℝ] ℝ, ∀ f, L f = chartDerivativeWord w (A f) x := by
  let : BaireSpace T := fixedSupportTest_baireSpace K
  induction w generalizing x with
  | nil => exact hEval x hx
  | cons i w ih =>
    classical
    choose L hL using (fun (y : Y) (hy : y ∈ U) => ih (x := y) hy)
    let a (t : ℝ) := x + t • axis i
    let B (t : ℝ) : T →L[ℝ] ℝ := if ht : a t ∈ U then t⁻¹ • (L (a t) ht - L x hx) else 0
    have ha : Continuous a := continuous_const.add (continuous_id.smul continuous_const)
    have ha₀ : a 0 = x := by simp [a]
    have hMem : a 0 ∈ U := ha₀.symm ▸ hx
    have hEvent : ∀ᶠ t in 𝓝 (0 : ℝ), a t ∈ U :=
      ha.continuousAt.preimage_mem_nhds (hU.mem_nhds hMem)
    have hNear : ∀ᶠ t in 𝓝[≠] (0 : ℝ), a t ∈ U := hEvent.filter_mono nhdsWithin_le_nhds
    have hT : Tendsto (fun t f => B t f) (𝓝[≠] (0 : ℝ))
        (𝓝 (fun f => chartDerivativeWord (i :: w) (A f) x)) := by
      apply tendsto_pi_nhds.mpr
      intro f
      have hv := BoundaryLayer.contDiffOn_chartDerivativeWord hU w (hSmooth f)
      have hd := ((hv.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hx)).hasFDerivAt
      refine (hd.hasLineDerivAt (axis i)).tendsto_slope_zero.congr' (hNear.mono fun t ht => ?_)
      change t⁻¹ • (chartDerivativeWord w (A f) (a t) - chartDerivativeWord w (A f) x) = B t f
      rw [show B t = t⁻¹ • (L (a t) ht - L x hx) from dite_eq_left ht]
      simp only [smul_apply, sub_apply, hL]
    exact ⟨continuousLinearMapOfTendsto B hT,fun _ => rfl⟩

/-- A pointwise smooth family with continuous evaluation at every nearby
point has continuous second-jet evaluation in the fixed-support topology. -/
theorem exists_secondJetEvaluation {x : Y} (hx : x ∈ U) :
    ∃ L : T →L[ℝ] ScalarSecondJet (m+1), ∀ f, L f = smoothSecondJet hU hx (A f) (hSmooth f) := by
  obtain ⟨V,hV⟩ := hEval x hx
  choose P hP using fun i => exists_chartWordEvaluation hU A hSmooth hEval [i] hx
  choose Q hQ using fun ij : I (m+1) × I (m+1) =>
    exists_chartWordEvaluation hU A hSmooth hEval [ij.1,ij.2] hx
  let H : T →L[ℝ] (I (m+1) → I (m+1) → ℝ) :=
    ContinuousLinearMap.pi (fun i => ContinuousLinearMap.pi (fun j => Q (i,j)))
  let S : T →L[ℝ] symmetricHessians (m+1) := H.codRestrict (symmetricHessians (m+1)) (by
    intro f
    change Matrix.transpose (H f : CalderonN.Mat (m+1)) = H f
    have hH : H f = (smoothSecondJet hU hx (A f) (hSmooth f)).2.2.val := by
      funext i j
      exact hQ (i,j) f
    rw [hH]
    exact (smoothSecondJet hU hx (A f) (hSmooth f)).2.2.property)
  refine ⟨V.prod ((ContinuousLinearMap.pi P).prod S),fun f => ?_⟩
  refine Prod.ext (hV f) (Prod.ext (funext fun i => hP i f)
    (Subtype.ext (Matrix.ext fun i j => hQ (i,j) f)))

/-- Continuity of the jet supplies a bound by finitely many of the existing
seminorms on fixed-support smooth tests. -/
theorem exists_secondJetEvaluation_seminorm_bound {x : Y} (hx : x ∈ U) :
    ∃ (orders : Finset ℕ) (B : ℝ), 0 ≤ B ∧ ∀ f : T,
      ‖smoothSecondJet hU hx (A f) (hSmooth f)‖ ≤ B * (orders.sup fun i => N[ℝ]_{K, i}) f := by
  obtain ⟨L,hL⟩ := exists_secondJetEvaluation hU A hSmooth hEval hx
  let q : Seminorm ℝ T := (normSeminorm ℝ (ScalarSecondJet (m+1))).comp L.toLinearMap
  obtain ⟨orders,B,_,hB⟩ := Seminorm.bound_of_continuous
    (ContDiffMapSupportedIn.withSeminorms ℝ E ℝ ⊤ K) q L.continuous.norm
  refine ⟨orders,B,B.coe_nonneg,fun f => ?_⟩
  rw [← hL f]
  exact hB f

end CalderonPatch
