module

public import Proof.Manuscript.ScalarConductivityDefs

public import Proof.Manuscript.ScalarCoordinates
public import Proof.Manuscript.ScalarConformalEnergy
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
import Mathlib.Tactic

public section

noncomputable section
open Set Filter
open scoped ContDiff Manifold Topology

set_option backward.isDefEq.respectTransparency false

namespace CalderonPaper

open CalderonN (X)
open CalderonPatch

variable {n : ℕ} [NeZero n] {Ω : Set (X n)}
  [ChartedSpace (EuclideanHalfSpace n) ↥(closure Ω)]
  [IsManifold (𝓡∂ n) ∞ ↥(closure Ω)]

local notation "J" => 𝓡∂ n
local notation "K" => 𝓘(ℝ, X n)
local notation "R" => 𝓘(ℝ, ℝ)

private theorem scalarDerivative_transport (D : EuclideanClosure Ω) (hΩ : IsOpen Ω)
    (Φ : ↥(closure Ω) ≃ₘ⟮J, J⟯ ↥(closure Ω)) {x : X n} (hx : x ∈ Ω) :
    let p := D.interiorInverse x
    let ι : ↥(closure Ω) → X n := Subtype.val
    let A := mfderiv J K ι p
    let B := mfderiv J K ι (Φ p)
    let C := mfderiv K J D.interiorInverse x
    let T := mfderiv J J Φ p
    (∀ v : X n, (A (C v) : X n) = v) ∧
      (∀ v : X n, fderiv ℝ (closureSelfMap Φ) x v = (B (T (C v)) : X n)) := by
  let p := D.interiorInverse x
  let ι : ↥(closure Ω) → X n := Subtype.val
  let A := mfderiv J K ι p
  let B := mfderiv J K ι (Φ p)
  let C := mfderiv K J D.interiorInverse x
  let T := mfderiv J J Φ p
  have hc : MDifferentiableAt K J D.interiorInverse x :=
    (D.interiorInverse_smooth.contMDiffAt (hΩ.mem_nhds hx)).mdifferentiableAt (by simp)
  have hi (q : ↥(closure Ω)) : MDifferentiableAt J K ι q :=
    (D.inclusion_smooth q).mdifferentiableAt (by simp)
  have hf (q : ↥(closure Ω)) : MDifferentiableAt J J Φ q :=
    (Φ.contMDiff q).mdifferentiableAt (by simp)
  have hId : (ι ∘ D.interiorInverse) =ᶠ[𝓝 x] id := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    exact D.interiorInverse_apply y hy
  have hF : ((ι ∘ Φ) ∘ D.interiorInverse) =ᶠ[𝓝 x] closureSelfMap Φ := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    change (Φ (D.interiorInverse y) : X n) = closureSelfMap Φ y
    rw [← closureSelfMap_on_closure Φ (D.interiorInverse y), D.interiorInverse_apply y hy]
  constructor
  · intro v
    change (A.comp C) v = v
    rw [show A.comp C = mfderiv K K (ι ∘ D.interiorInverse) x from (mfderiv_comp x (hi p) hc).symm]
    rw [hId.mfderiv_eq, mfderiv_id]
    rfl
  · intro v
    have he : mfderiv K K ((ι ∘ Φ) ∘ D.interiorInverse) x = (B.comp T).comp C := by
      rw [mfderiv_comp x ((hi (Φ p)).comp p (hf p)) hc,
        mfderiv_comp p (hi (Φ p)) (hf p)]
    rw [← hF.fderiv_eq (𝕜 := ℝ)]
    rw [mfderiv_eq_fderiv] at he
    exact DFunLike.congr_fun he (show TangentSpace K x from v)

/-- A pullback between the two conductivity metrics gives exact ambient
conformality on the Euclidean interior with the difference of the two exponents. -/
theorem closureSelfMap_conformal_of_pullback (D : EuclideanClosure Ω) (hΩ : IsOpen Ω)
    (Φ : ↥(closure Ω) ≃ₘ⟮J, J⟯ ↥(closure Ω))
    {ψ₁ ψ₂ : X n → ℝ} (hψ₁ : SmoothThrough (closure Ω) ψ₁) (hψ₂ : SmoothThrough (closure Ω) ψ₂)
    (hPull : PullbackMetric
      (expScaledMetric D.metric (ψ₁ ∘ Subtype.val) (D.contMDiff_restrict hψ₁))
      (expScaledMetric D.metric (ψ₂ ∘ Subtype.val) (D.contMDiff_restrict hψ₂)) Φ) :
    EuclideanConformalOn Ω (closureSelfMap Φ) (fun x => ψ₂ x - ψ₁ (closureSelfMap Φ x)) := by
  intro x hx v w
  let p := D.interiorInverse x
  let ι : ↥(closure Ω) → X n := Subtype.val
  let A := mfderiv J K ι p
  let B := mfderiv J K ι (Φ p)
  let C := mfderiv K J D.interiorInverse x
  let T := mfderiv J J Φ p
  let F := closureSelfMap Φ
  obtain ⟨hA, hB⟩ := scalarDerivative_transport D hΩ Φ hx
  have h₀ : (p : X n) = x := D.interiorInverse_apply x hx
  have h₁ : (Φ p : X n) = F x := by
    rw [← closureSelfMap_on_closure Φ p, h₀]
  have h := hPull p (C v) (C w)
  change Real.exp (2 * ψ₂ p) * D.metric.inner p (C v) (C w) =
    Real.exp (2 * ψ₁ (Φ p)) * D.metric.inner (Φ p) (T (C v)) (T (C w)) at h
  simp only [D.metric_inner] at h
  change Real.exp (2 * ψ₂ p) * inner ℝ (show X n from A (C v)) (show X n from A (C w)) =
    Real.exp (2 * ψ₁ (Φ p)) * inner ℝ (show X n from B (T (C v))) (show X n from B (T (C w))) at h
  rw [hA v, hA w, ← hB v, ← hB w, congrArg ψ₂ h₀, congrArg ψ₁ h₁] at h
  change inner ℝ (fderiv ℝ F x v) (fderiv ℝ F x w) =
    Real.exp (2 * (ψ₂ x - ψ₁ (F x))) * inner ℝ v w
  let c := Real.exp (2 * ψ₁ (F x))
  calc
    _ = c⁻¹ * (c * inner ℝ (fderiv ℝ F x v) (fderiv ℝ F x w)) := by
      rw [← mul_assoc, inv_mul_cancel₀ (Real.exp_pos _).ne', one_mul]
    _ = c⁻¹ * (Real.exp (2 * ψ₂ x) * inner ℝ v w) := by rw [← h]
    _ = _ := by
      dsimp only [c]
      rw [← mul_assoc, ← Real.exp_neg, ← Real.exp_add]
      congr 2
      ring

/-- The inverse of a pullback diffeomorphism has the reversed metric identity. -/
theorem pullbackMetric_inverse {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold J ∞ M]
    {g₁ g₂ : SmoothMetric n M} (Φ : M ≃ₘ⟮J, J⟯ M)
    (hΦ : PullbackMetric g₁ g₂ Φ) : PullbackMetric g₂ g₁ Φ.symm := by
  intro x v w
  have hComp : (fun y : M => Φ (Φ.symm y)) = id := funext Φ.apply_symm_apply
  have hD : (mfderiv J J Φ (Φ.symm x)).comp (mfderiv J J Φ.symm x) =
      ContinuousLinearMap.id ℝ (TangentSpace J x) := by
    rw [← mfderiv_comp x (Φ.contMDiff.mdifferentiable (by simp) _)
      (Φ.symm.contMDiff.mdifferentiable (by simp) _)]
    change mfderiv J J (fun y : M => Φ (Φ.symm y)) x = _
    rw [hComp, mfderiv_id]
  have h := hΦ (Φ.symm x) (mfderiv J J Φ.symm x v) (mfderiv J J Φ.symm x w)
  change g₂.inner (Φ.symm x) (mfderiv J J Φ.symm x v) (mfderiv J J Φ.symm x w) =
    g₁.inner (Φ (Φ.symm x))
      (((mfderiv J J Φ (Φ.symm x)).comp (mfderiv J J Φ.symm x)) v)
      (((mfderiv J J Φ (Φ.symm x)).comp (mfderiv J J Φ.symm x)) w) at h
  rw [hD, Φ.apply_symm_apply] at h
  exact h.symm

end CalderonPaper
