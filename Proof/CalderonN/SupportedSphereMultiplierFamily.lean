module

public import Proof.CalderonN.SmoothSupportedTraceFiberAction

import Proof.CalderonN.ParametricBallConormal
import Proof.CalderonN.SmoothTraceMultiplierOrder
import Proof.CalderonN.SmoothSupportedTraceAdjointCalculus
import Mathlib.Tactic

/-! A jointly smooth angular multiplier and its self-adjoint action
on the common supported trace space. -/

public section

noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Elementwise InnerProductSpace Classical
set_option autoImplicit false
set_option maxHeartbeats 2300000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE OAI.AnisotropicCalderon SphereHarmonic
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)}

@[expose] def supportedSphereMultiplierFamily (m : ∀ x ∈ Y,SmoothData dim) (x : X dim) :
    Module.End ℝ (SmoothSphereTrace dim) :=
  if hx : x ∈ Y then smoothSphereTraceMul (m x hx) else 0

theorem supportedSphereMultiplierFamily_regular (hY : IsOpen Y)
    (m : ∀ x ∈ Y,SmoothData dim)
    (hLoc : ∀ x ∈ Y, ∃ (V : Set (X dim)) (a : X dim × X dim → ℝ),
      IsOpen V ∧ x ∈ V ∧ V ⊆ Y ∧ ContDiffOn ℝ ∞ a (V ×ˢ ({0}ᶜ : Set (X dim))) ∧
      ∀ y ∈ V,∀ hy : y ∈ Y,∀ z ∈ standardSphere dim,a (y,z) = (m y hy).1 z) :
    SmoothSupportedTraceFiberRegular Y (supportedSphereMultiplierFamily m) := by
  intro u
  obtain ⟨G,hG,hRep⟩ := smoothSupportedTraceSection_repr u
  let Z : Set (X dim) := {0}ᶜ
  let F (p : X dim × X dim) := if h : p.1 ∈ Y then (m p.1 h).1 (sphereNormalize p.2) else 0
  have hZ : IsOpen Z := isClosed_singleton.isOpen_compl
  have hZS : standardSphere dim ⊆ Z := by
    intro z hz
    change z ≠ 0
    intro h
    simp [standardSphere,h] at hz
  have hF : ContDiffOn ℝ ∞ F (Y ×ˢ Z) := by
    apply contDiffOn_of_locally_contDiffOn
    intro p hp
    obtain ⟨V,a,hV,hpV,hVY,ha,hA⟩ := hLoc p.1 hp.1
    let Q (q : X dim × X dim) := (q.1,sphereNormalize q.2)
    have hQ : ContDiffOn ℝ ∞ Q (V ×ˢ Z) :=
      contDiff_fst.contDiffOn.prodMk
        (contDiffOn_sphereNormalize.comp contDiff_snd.contDiffOn (fun _ h => h.2))
    have hMQ : MapsTo Q (V ×ˢ Z) (V ×ˢ Z) := fun _ h =>
      ⟨h.1,hZS (sphereNormalize_mem_sphere h.2)⟩
    refine ⟨V ×ˢ Z,hV.prod hZ,⟨hpV,hp.2⟩,((ha.comp hQ hMQ).mono inter_subset_right).congr ?_⟩
    intro q hq
    exact (dite_eq_left hq.1.1).trans (hA q.1 hq.2.1 hq.1.1 _ (sphereNormalize_mem_sphere hq.2.2)).symm
  refine ⟨Y ×ˢ Z,fun p => F p*G p,hY.prod hZ,prod_mono_right hZS,hF.mul hG.contDiffOn,?_⟩
  intro x hx z
  simp only [F,dite_eq_left hx,sphereNormalize_eq_of_sphere z.property,supportedSphereMultiplierFamily]
  rw [smoothSphereTraceMul_apply,smoothSupportedTraceFiberL_apply,hRep x z]

theorem supportedSphereMultiplierFamily_selfAdjoint (hn : 3 ≤ dim)
    (m : ∀ x ∈ Y,SmoothData dim) (x : X dim) (hx : x ∈ Y) :
    SmoothTraceAdjoint hn (supportedSphereMultiplierFamily m x) (supportedSphereMultiplierFamily m x) := by
  rw [supportedSphereMultiplierFamily,dite_eq_left hx]
  exact smoothSphereTraceMul_symmetric hn (m x hx)

end CalderonN
