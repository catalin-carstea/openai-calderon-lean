module

public import Proof.CalderonN.MetricCalculus

import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Tactic

@[expose] public section

/- Coordinate calculus from the 3D Theorem 3.1 release. The derivative used
   by the divergence operator is the protected coordinate derivative. -/
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace CalderonN.Elliptic

variable {d : ℕ}

abbrev pd (i : Fin d) (f : X d → ℝ) : X d → ℝ := coordDeriv i f

section
variable {f g : (X d) → ℝ} {i j : Fin d}

@[fun_prop]
theorem contDiff_pd (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (pd i f) := by
  unfold pd coordDeriv axis
  have h := hf.fderiv_right (m := ∞) (by simp)
  exact h.clm_apply contDiff_const

@[fun_prop]
theorem contDiff_pd_apply (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (fun x => pd i f x) :=
  contDiff_pd hf

theorem diffAt (hf : ContDiff ℝ ∞ f) (x : (X d)) : DifferentiableAt ℝ f x :=
  (hf.differentiable (by simp)) x

theorem pd_add (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : (X d)) :
    pd i (fun y => f y + g y) x = pd i f x + pd i g x := by
  simp [pd, coordDeriv, axis, fderiv_fun_add (diffAt hf x) (diffAt hg x)]

theorem pd_sub (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : (X d)) :
    pd i (fun y => f y - g y) x = pd i f x - pd i g x := by
  simp [pd, coordDeriv, axis, fderiv_fun_sub (diffAt hf x) (diffAt hg x)]

theorem pd_neg (x : (X d)) : pd i (fun y => -f y) x = -pd i f x := by
  simp [pd, coordDeriv, axis, fderiv_fun_neg]

theorem pd_mul (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : (X d)) :
    pd i (fun y => f y * g y) x = pd i f x * g x + f x * pd i g x := by
  simp [pd, coordDeriv, axis, fderiv_fun_mul (diffAt hf x) (diffAt hg x)]
  ring

theorem pd_const (c : ℝ) (x : (X d)) : pd i (fun _ => c) x = 0 := by
  simp [pd, coordDeriv, axis]

theorem pd_const_mul (c : ℝ) (hf : ContDiff ℝ ∞ f) (x : (X d)) :
    pd i (fun y => c * f y) x = c * pd i f x := by
  rw [pd_mul contDiff_const hf, pd_const]; ring

theorem pd_sum {F : Fin d → (X d) → ℝ} (hF : ∀ k, ContDiff ℝ ∞ (F k)) (x : (X d)) :
    pd i (fun y => ∑ k, F k y) x = ∑ k, pd i (F k) x := by
  unfold pd coordDeriv axis
  rw [fderiv_fun_sum (fun k _ => diffAt (hF k) x)]
  simp

theorem pd_comm (hf : ContDiff ℝ ∞ f) :
    pd i (pd j f) = pd j (pd i f) := by
  funext x
  have hs := (hf.contDiffAt (x := x)).isSymmSndFDerivAt (by simp)
  have key : ∀ a b : Fin d, pd a (pd b f) x =
      fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single a 1) (EuclideanSpace.single b 1) := by
    intro a b
    unfold pd coordDeriv axis
    have h2 : DifferentiableAt ℝ (fderiv ℝ f) x :=
      ((hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp)) x
    rw [fderiv_clm_apply h2 (differentiableAt_const _)]
    simp
  rw [key, key, hs]

theorem pd_congr_of_eventuallyEq {x : X d} (h : f =ᶠ[𝓝 x] g) (i : Fin d) :
    pd i f x = pd i g x :=
  congrArg (fun D : X d →L[ℝ] ℝ => D (axis i)) (h.fderiv_eq (𝕜 := ℝ))

theorem hasCompactSupport_pd (hf : HasCompactSupport f) : HasCompactSupport (pd i f) :=
  hf.fderiv_apply (𝕜 := ℝ) _

theorem integrable_of_contDiff_hasCompactSupport (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) : Integrable f :=
  hf.continuous.integrable_of_hasCompactSupport hc

theorem integral_pd_eq_zero (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    ∫ x, pd i f x = 0 := by
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := fun _ : (X d) => (1 : ℝ)) (g := f) (v := EuclideanSpace.single i 1)
    (by simp) (by simp only [one_mul]; exact (integrable_of_contDiff_hasCompactSupport
      (contDiff_pd hf) (hasCompactSupport_pd (i := i) hc)))
    (by simpa using integrable_of_contDiff_hasCompactSupport hf hc)
    (fun x _ => differentiableAt_const _) (fun x _ => diffAt hf x)
  change (∫ x, fderiv ℝ f x (EuclideanSpace.single i 1)) = 0
  simpa using h

end

/-- `div(a ∇f)` in coordinates. -/
def Lop (a : Fin d → Fin d → (X d) → ℝ) (f : (X d) → ℝ) (x : (X d)) : ℝ :=
  ∑ i, pd i (fun z => ∑ k, a i k z * pd k f z) x

/-- Divergence of a vector field. -/
def divV (F : Fin d → X d → ℝ) (x : X d) : ℝ := ∑ j, pd j (F j) x

theorem contDiff_mul_of_tsupport_subset {D : Set (X d)} (hD : IsOpen D) {chi w : (X d) → ℝ}
    (hc : ContDiff ℝ ∞ chi) (hsub : tsupport chi ⊆ D) (hw : ContDiffOn ℝ ∞ w D) :
    ContDiff ℝ ∞ (fun y => chi y * w y) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ D
  · exact (hc.contDiffOn.mul hw).contDiffAt (hD.mem_nhds hx)
  · have hx' : x ∉ tsupport chi := fun h => hx (hsub h)
    have hmem : (tsupport chi)ᶜ ∈ nhds x := (isClosed_tsupport chi).isOpen_compl.mem_nhds hx'
    have heq : (fun y => chi y * w y) =ᶠ[nhds x] fun _ => (0 : ℝ) :=
      Filter.mem_of_superset hmem fun y hy => by
        have h0 : chi y = 0 := by
          by_contra h
          exact hy (subset_tsupport chi h)
        show chi y * w y = 0
        rw [h0, zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq heq

theorem exists_plateau_cutoff {D K : Set (X d)} (hD : IsOpen D) (hK : IsCompact K)
    (hKD : K ⊆ D) :
    ∃ zeta : (X d) → ℝ, ContDiff ℝ ∞ zeta ∧ HasCompactSupport zeta ∧ tsupport zeta ⊆ D ∧
      ∀ x ∈ K, zeta =ᶠ[nhds x] fun _ => (1 : ℝ) := by
  obtain ⟨U, hUo, hKU, hUD, hUc⟩ := exists_open_between_and_isCompact_closure hK hD hKD
  obtain ⟨V, hVo, hKV, hVU, -⟩ := exists_open_between_and_isCompact_closure hK hUo hKU
  obtain ⟨f, hf, -, hsupp, h1⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hUo isClosed_closure hVU
  refine ⟨f, hf, ?_, ?_, ?_⟩
  · show IsCompact (closure (Function.support f))
    rw [hsupp]
    exact hUc
  · show closure (Function.support f) ⊆ D
    rw [hsupp]
    exact hUD
  · intro x hx
    exact Filter.mem_of_superset (hVo.mem_nhds (hKV hx)) fun y hy =>
      (h1 y).1 (subset_closure hy)

end CalderonN.Elliptic
