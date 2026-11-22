module

public import Proof.CalderonPatch.FrontierGram

import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

@[expose] public section

noncomputable section
open Set
open scoped ContDiff Manifold

namespace CalderonPatch

open CalderonN (I X)

variable {n : ℕ} [NeZero n] {F M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]

local notation "J" => 𝓡∂ n
local notation "K" => 𝓘(ℝ, X n)
local notation "R" => 𝓘(ℝ, ℝ)

/-- A source family realizing each first derivative supplies a tuple
whose differential is invertible. -/
theorem exists_invertible_tuple_of_realized_covectors
    (E : M → F → ℝ) (hE : ∀ a, ContMDiff J R ∞ (fun x => E x a))
    (p : M) (hRange : ∀ A : TangentSpace J p →L[ℝ] ℝ,
      ∃ a, mfderiv J R (fun x => E x a) p = A) :
    ∃ a : I n → F, (mfderiv J K (sourceTuple E a) p).IsInvertible := by
  let P (i : I n) : X n →L[ℝ] ℝ := EuclideanSpace.proj i
  choose a ha using (fun i : I n => hRange (P i))
  let f := sourceTuple E a
  have hf : ContMDiff J K ∞ f := contMDiff_sourceTuple E a hE
  let D : X n →L[ℝ] X n := mfderiv J K f p
  have hD : D = ContinuousLinearMap.id ℝ (X n) := by
    ext v i
    have hF : (P i : X n → ℝ) ∘ f = fun x => E x (a i) := by
      funext x
      exact sourceTuple_apply E a x i
    have hPi : ContMDiffAt K R ∞ (P i : X n → ℝ) (f p) := (P i).contMDiffAt
    have hPD : mfderiv K R (P i : X n → ℝ) (f p) = P i := by
      rw [mfderiv_eq_fderiv, ContinuousLinearMap.fderiv]
      ext x
      rfl
    have h := mfderiv_comp p (hPi.mdifferentiableAt (by simp)) (hf.contMDiffAt.mdifferentiableAt (by simp))
    have hFder : (mfderiv J R (fun x => E x (a i)) p : X n →L[ℝ] ℝ) =
        mfderiv J R ((P i : X n → ℝ) ∘ f) p := by rw [hF]
    have hcomp : P i = (P i).comp D := by
      have h' := (ha i).symm.trans hFder
      exact (h'.trans h).trans
        (congrArg (fun A : X n →L[ℝ] ℝ => A.comp D) hPD)
    exact (congrArg (fun A : X n →L[ℝ] ℝ => A v) hcomp).symm
  exact ⟨a, ⟨ContinuousLinearEquiv.refl ℝ (X n), hD.symm⟩⟩

end CalderonPatch
