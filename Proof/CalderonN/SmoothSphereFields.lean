module

public import Proof.CalderonN.CompactParameterSmoothness
public import Proof.CalderonN.SphereHarmonicBridge

import Mathlib.Tactic

@[expose] public section

/- Adopted from the selected ZIP, lean/Calderon/SmoothSphereFields.lean.
   Mathematical declarations and proof bodies are preserved; local imports are rewritten. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.SmoothSphereFields
variable {N : ℕ} [NeZero N]
open SphereHarmonic CompactParameterSmoothness

def unitSphereInclusion : C((UnitSphere N),(CalderonN.X N)) := ⟨Subtype.val,continuous_subtype_val⟩

def ambientSphereSection (G : (CalderonN.X N) × (CalderonN.X N) → ℝ) (hG : ContDiff ℝ ∞ G) :
    (CalderonN.X N) → C((UnitSphere N),ℝ) := compactPullback G hG.continuous unitSphereInclusion

def ambientSphereL2 (G : (CalderonN.X N) × (CalderonN.X N) → ℝ) (hG : ContDiff ℝ ∞ G) : (CalderonN.X N) → (SphereL2 N) :=
  fun x => ContinuousMap.toLp 2 (unitSphereProbability N) ℝ (ambientSphereSection G hG x)

lemma contDiff_ambientSphereSection (G : (CalderonN.X N) × (CalderonN.X N) → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (ambientSphereSection G hG) :=
  contDiff_infty_compactPullback G hG unitSphereInclusion

lemma contDiff_ambientSphereL2 (G : (CalderonN.X N) × (CalderonN.X N) → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (ambientSphereL2 G hG) := by
  change ContDiff ℝ ∞
    ((ContinuousMap.toLp 2 (unitSphereProbability N) ℝ : C((UnitSphere N),ℝ) →L[ℝ] (SphereL2 N)) ∘
      ambientSphereSection G hG)
  exact (ContinuousMap.toLp 2 (unitSphereProbability N) ℝ : C((UnitSphere N),ℝ) →L[ℝ] (SphereL2 N)).contDiff.comp
    (contDiff_ambientSphereSection G hG)

lemma ambientSphereL2_ae (G : (CalderonN.X N) × (CalderonN.X N) → ℝ) (hG : ContDiff ℝ ∞ G) (x : (CalderonN.X N)) :
    ambientSphereL2 G hG x =ᵐ[(unitSphereProbability N)] (fun theta : (UnitSphere N) => G (x,theta.val)) :=
  ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (unitSphereProbability N)
    (ambientSphereSection G hG x)

def ambientBasePartialSphere (G : (CalderonN.X N) × (CalderonN.X N) → ℝ) (hG : ContDiff ℝ ∞ G) (x : (CalderonN.X N)) :
    C((UnitSphere N),(CalderonN.X N) →L[ℝ] ℝ) :=
  compactPullback (basePartial G)
    (contDiff_basePartial 0 G (hG.of_le (by simp))).continuous unitSphereInclusion x

lemma hasFDerivAt_ambientSphereSection (G : (CalderonN.X N) × (CalderonN.X N) → ℝ) (hG : ContDiff ℝ ∞ G) (x : (CalderonN.X N)) :
    HasFDerivAt (ambientSphereSection G hG)
      (transposeContinuousFamily (ambientBasePartialSphere G hG x)) x := by
  apply hasFDerivAt_of_uniform_slice_derivative
    (ambientSphereSection G hG) (ambientBasePartialSphere G hG) x
  · exact (continuous_compactPullback (basePartial G)
      (contDiff_basePartial 0 G (hG.of_le (by simp))).continuous unitSphereInclusion).continuousAt
  · intro y theta
    exact hasFDerivAt_base_slice G (hG.differentiable (by simp)) y theta.val

lemma fderiv_ambientSphereL2 (G : (CalderonN.X N) × (CalderonN.X N) → ℝ) (hG : ContDiff ℝ ∞ G) (x : (CalderonN.X N)) :
    fderiv ℝ (ambientSphereL2 G hG) x =
      (ContinuousMap.toLp 2 (unitSphereProbability N) ℝ).comp
        (transposeContinuousFamily (ambientBasePartialSphere G hG x)) := by
  change fderiv ℝ
    ((ContinuousMap.toLp 2 (unitSphereProbability N) ℝ : C((UnitSphere N),ℝ) →L[ℝ] (SphereL2 N)) ∘
      ambientSphereSection G hG) x = _
  exact ((ContinuousMap.toLp 2 (unitSphereProbability N) ℝ : C((UnitSphere N),ℝ) →L[ℝ] (SphereL2 N)).hasFDerivAt.comp x
    (hasFDerivAt_ambientSphereSection G hG x)).fderiv

lemma fderiv_ambientSphereL2_ae (G : (CalderonN.X N) × (CalderonN.X N) → ℝ) (hG : ContDiff ℝ ∞ G) (x a : (CalderonN.X N)) :
    fderiv ℝ (ambientSphereL2 G hG) x a =ᵐ[(unitSphereProbability N)]
      (fun theta : (UnitSphere N) => fderiv ℝ G (x,theta.val) (a,0)) := by
  rw [fderiv_ambientSphereL2,ContinuousLinearMap.comp_apply]
  exact ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (unitSphereProbability N)
    (transposeContinuousFamily (ambientBasePartialSphere G hG x) a)

lemma ambientSphereSection_eq_zero (G : (CalderonN.X N) × (CalderonN.X N) → ℝ) (hG : ContDiff ℝ ∞ G) (x : (CalderonN.X N))
    (hz : ∀ theta : (UnitSphere N), G (x,theta.val)=0) : ambientSphereSection G hG x = 0 := by
  ext theta
  exact hz theta

lemma ambientSphereL2_eq_zero (G : (CalderonN.X N) × (CalderonN.X N) → ℝ) (hG : ContDiff ℝ ∞ G) (x : (CalderonN.X N))
    (hz : ∀ theta : (UnitSphere N), G (x,theta.val)=0) : ambientSphereL2 G hG x = 0 := by
  change ContinuousMap.toLp 2 (unitSphereProbability N) ℝ (ambientSphereSection G hG x)=0
  rw [ambientSphereSection_eq_zero G hG x hz,map_zero]

lemma hasCompactSupport_ambientSphereSection (G : (CalderonN.X N) × (CalderonN.X N) → ℝ) (hG : ContDiff ℝ ∞ G)
    (K : Set (CalderonN.X N)) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ theta : (UnitSphere N), G (x,theta.val)=0) :
    HasCompactSupport (ambientSphereSection G hG) :=
  HasCompactSupport.intro hK (fun x hx => ambientSphereSection_eq_zero G hG x (hz x hx))

lemma hasCompactSupport_ambientSphereL2 (G : (CalderonN.X N) × (CalderonN.X N) → ℝ) (hG : ContDiff ℝ ∞ G)
    (K : Set (CalderonN.X N)) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ theta : (UnitSphere N), G (x,theta.val)=0) :
    HasCompactSupport (ambientSphereL2 G hG) :=
  HasCompactSupport.intro hK (fun x hx => ambientSphereL2_eq_zero G hG x (hz x hx))

lemma hasCompactSupport_fderiv_ambientSphereL2 (G : (CalderonN.X N) × (CalderonN.X N) → ℝ) (hG : ContDiff ℝ ∞ G)
    (K : Set (CalderonN.X N)) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ theta : (UnitSphere N), G (x,theta.val)=0) (a : (CalderonN.X N)) :
    HasCompactSupport (fun x => fderiv ℝ (ambientSphereL2 G hG) x a) :=
  (hasCompactSupport_ambientSphereL2 G hG K hK hz).fderiv_apply ℝ a

end OAI.AnisotropicCalderon.SmoothSphereFields
