module

public import Proof.CalderonN.SmoothAngularCasimir
public import Proof.CalderonN.SmoothSphereFields

import Mathlib.Analysis.Calculus.FDeriv.Prod

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ContDiff Topology ENNReal

namespace CalderonN

variable {N : ℕ} [NeZero N]
open OAI.AnisotropicCalderon SphereHarmonic SmoothSphereFields SmoothSphereRotation

def ambientAngularRotation (i j : Fin N) (G : (X N) × (X N) → ℝ) (q : (X N) × (X N)) : ℝ :=
  fderiv ℝ G q (0,rotationVector i j q.2)

def ambientAngularCasimir (G : (X N) × (X N) → ℝ) (q : (X N) × (X N)) : ℝ :=
  -(1/2 : ℝ) * ∑ i : Fin N, ∑ j : Fin N,
    ambientAngularRotation i j (ambientAngularRotation i j G) q

def ambientShiftedAngularCasimir (G : (X N) × (X N) → ℝ) (q : (X N) × (X N)) : ℝ :=
  G q + ambientAngularCasimir G q

def ambientShiftedAngularCasimirIterate : ℕ → ((X N) × (X N) → ℝ) → (X N) × (X N) → ℝ
  | 0,G => G
  | m+1,G => ambientShiftedAngularCasimir (ambientShiftedAngularCasimirIterate m G)

lemma contDiff_angular_slice (G : (X N) × (X N) → ℝ) (hG : ContDiff ℝ ∞ G) (x : (X N)) :
    ContDiff ℝ ∞ (fun z => G (x,z)) := hG.comp (contDiff_const.prodMk contDiff_id)

lemma fderiv_angular_slice_apply (G : (X N) × (X N) → ℝ) (hG : ContDiff ℝ ∞ G)
    (x z v : (X N)) : fderiv ℝ (fun w => G (x,w)) z v = fderiv ℝ G (x,z) (0,v) := by
  convert! congrArg (fun L : (X N) →L[ℝ] ℝ => L v)
    ((((hG.differentiable (by simp)) (x,z)).hasFDerivAt.comp z
      (hasFDerivAt_prodMk_right x z)).fderiv) using 1 <;> rfl

lemma contDiff_ambientAngularRotation (i j : Fin N) (G : (X N) × (X N) → ℝ)
    (hG : ContDiff ℝ ∞ G) : ContDiff ℝ ∞ (ambientAngularRotation i j G) :=
  (contDiff_infty_iff_fderiv.mp hG).2.clm_apply
    (contDiff_const.prodMk ((contDiff_rotationVector i j).comp contDiff_snd))

lemma ambientAngularRotation_slice (i j : Fin N) (G : (X N) × (X N) → ℝ)
    (hG : ContDiff ℝ ∞ G) (x : (X N)) :
    (fun z => ambientAngularRotation i j G (x,z)) =
      sphereRotationDerivative i j (fun z => G (x,z)) := by
  funext z
  exact (fderiv_angular_slice_apply G hG x z (rotationVector i j z)).symm

lemma contDiff_ambientAngularCasimir (G : (X N) × (X N) → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (ambientAngularCasimir G) := by
  have hs : ContDiff ℝ ∞ (fun q => ∑ i : Fin N, ∑ j : Fin N,
      ambientAngularRotation i j (ambientAngularRotation i j G) q) :=
    ContDiff.sum fun i _ => ContDiff.sum fun j _ => contDiff_ambientAngularRotation i j _
      (contDiff_ambientAngularRotation i j G hG)
  exact contDiff_const.mul hs

lemma ambientAngularCasimir_slice (G : (X N) × (X N) → ℝ) (hG : ContDiff ℝ ∞ G) (x : (X N)) :
    (fun z => ambientAngularCasimir G (x,z)) = angularCasimir (fun z => G (x,z)) := by
  funext z
  unfold ambientAngularCasimir angularCasimir
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have he := ambientAngularRotation_slice i j (ambientAngularRotation i j G)
    (contDiff_ambientAngularRotation i j G hG) x
  rw [ambientAngularRotation_slice i j G hG x] at he
  exact congrFun he z

lemma contDiff_ambientShiftedAngularCasimir (G : (X N) × (X N) → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (ambientShiftedAngularCasimir G) := hG.add (contDiff_ambientAngularCasimir G hG)

lemma ambientShiftedAngularCasimir_slice (G : (X N) × (X N) → ℝ) (hG : ContDiff ℝ ∞ G) (x : (X N)) :
    (fun z => ambientShiftedAngularCasimir G (x,z)) = shiftedAngularCasimir (fun z => G (x,z)) := by
  funext z
  exact congrArg (fun a : ℝ => G (x,z)+a) (congrFun (ambientAngularCasimir_slice G hG x) z)

lemma contDiff_ambientShiftedAngularCasimirIterate (m : ℕ) (G : (X N) × (X N) → ℝ)
    (hG : ContDiff ℝ ∞ G) : ContDiff ℝ ∞ (ambientShiftedAngularCasimirIterate m G) := by
  induction m with
  | zero => exact hG
  | succ m hm => exact contDiff_ambientShiftedAngularCasimir _ hm

lemma ambientShiftedAngularCasimirIterate_slice (m : ℕ) (G : (X N) × (X N) → ℝ)
    (hG : ContDiff ℝ ∞ G) (x : (X N)) :
    (fun z => ambientShiftedAngularCasimirIterate m G (x,z)) =
      shiftedAngularCasimirIterate m (fun z => G (x,z)) := by
  induction m with
  | zero => rfl
  | succ m hm =>
      rw [ambientShiftedAngularCasimirIterate,ambientShiftedAngularCasimir_slice
        _ (contDiff_ambientShiftedAngularCasimirIterate m G hG) x,hm]
      rfl

lemma ambientAngularRotation_sphere_zero (i j : Fin N) (G : (X N) × (X N) → ℝ)
    (hG : ContDiff ℝ ∞ G) (K : Set (X N))
    (hz : ∀ x ∉ K, ∀ u : (UnitSphere N), G (x,u.val)=0) :
    ∀ x ∉ K, ∀ u : (UnitSphere N), ambientAngularRotation i j G (x,u.val)=0 := by
  intro x hx u
  have he := congrFun (ambientAngularRotation_slice i j G hG x) u.val
  rw [he]
  exact sphereRotationDerivative_eq_zero_of_sphere_zero i j _
    (contDiff_angular_slice G hG x) (hz x hx) u

lemma ambientShiftedAngularCasimir_sphere_zero (G : (X N) × (X N) → ℝ)
    (hG : ContDiff ℝ ∞ G) (K : Set (X N))
    (hz : ∀ x ∉ K, ∀ u : (UnitSphere N), G (x,u.val)=0) :
    ∀ x ∉ K, ∀ u : (UnitSphere N), ambientShiftedAngularCasimir G (x,u.val)=0 := by
  intro x hx u
  have ho (i j : Fin N) : ambientAngularRotation i j (ambientAngularRotation i j G) (x,u.val)=0 :=
    ambientAngularRotation_sphere_zero i j _ (contDiff_ambientAngularRotation i j G hG) K
      (ambientAngularRotation_sphere_zero i j G hG K hz) x hx u
  simp [ambientShiftedAngularCasimir,ambientAngularCasimir,hz x hx u,ho]

lemma ambientShiftedAngularCasimirIterate_sphere_zero (m : ℕ) (G : (X N) × (X N) → ℝ)
    (hG : ContDiff ℝ ∞ G) (K : Set (X N))
    (hz : ∀ x ∉ K, ∀ u : (UnitSphere N), G (x,u.val)=0) :
    ∀ x ∉ K, ∀ u : (UnitSphere N), ambientShiftedAngularCasimirIterate m G (x,u.val)=0 := by
  induction m with
  | zero => exact hz
  | succ m hm =>
      exact ambientShiftedAngularCasimir_sphere_zero _
        (contDiff_ambientShiftedAngularCasimirIterate m G hG) K hm

lemma ambientSphereL2_eq_smoothSphereLift (G : (X N) × (X N) → ℝ) (hG : ContDiff ℝ ∞ G) (x : (X N)) :
    ambientSphereL2 G hG x = smoothSphereLift (fun z => G (x,z)) (contDiff_angular_slice G hG x) := by
  change (ContinuousMap.toLp 2 (unitSphereProbability N) ℝ) _ =
    (ContinuousMap.toLp 2 (unitSphereProbability N) ℝ) _
  congr 1

lemma hasCompactSupport_angularCasimirLift (m : ℕ) (G : (X N) × (X N) → ℝ)
    (hG : ContDiff ℝ ∞ G) (K : Set (X N)) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ u : (UnitSphere N), G (x,u.val)=0) :
    HasCompactSupport (ambientSphereL2 (ambientShiftedAngularCasimirIterate m G)
      (contDiff_ambientShiftedAngularCasimirIterate m G hG)) :=
  hasCompactSupport_ambientSphereL2 _ (contDiff_ambientShiftedAngularCasimirIterate m G hG) K hK
    (ambientShiftedAngularCasimirIterate_sphere_zero m G hG K hz)

 
lemma contDiff_angularCasimirLift (m : ℕ) (G : (X N) × (X N) → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (ambientSphereL2 (ambientShiftedAngularCasimirIterate m G)
      (contDiff_ambientShiftedAngularCasimirIterate m G hG)) :=
  contDiff_ambientSphereL2 _ (contDiff_ambientShiftedAngularCasimirIterate m G hG)

end CalderonN
