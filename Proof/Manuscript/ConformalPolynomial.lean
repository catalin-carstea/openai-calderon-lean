module

public import Proof.Manuscript.Lemma81Defs

import Proof.Manuscript.ConformalDifferentiation
import Proof.Manuscript.ConformalAlgebra
import Proof.Manuscript.LocalExtensions
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

public section

noncomputable section
open Set Filter
open scoped ContDiff Topology BigOperators

namespace CalderonPaper

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "axis" => EuclideanSpace.basisFun (Fin n) ℝ

private def radialQuadratic (x : E) : ℝ := (1 / 2 : ℝ) * ‖x‖ ^ 2

private theorem radialQuadratic_contDiff : ContDiff ℝ ∞ (radialQuadratic (n := n)) := by
  unfold radialQuadratic
  exact contDiff_const.mul (contDiff_norm_sq ℝ)

private theorem radialQuadratic_directional (j : Fin n) :
    directional (axis j) (radialQuadratic (n := n)) = EuclideanSpace.proj j := by
  funext x
  unfold directional radialQuadratic
  rw [fderiv_const_mul ((contDiff_norm_sq ℝ (n := ∞)).differentiable (by simp) x), fderiv_norm_sq_apply]
  simp
  ring_nf
  simpa only [EuclideanSpace.basisFun_apply] using
    (EuclideanSpace.inner_basisFun_real (Fin n) x j)


private theorem radialQuadratic_hessian (x : E) (i j : Fin n) :
    directional (axis i) (directional (axis j) radialQuadratic) x =
      if i = j then 1 else 0 := by
  rw [radialQuadratic_directional]
  unfold directional
  rw [(EuclideanSpace.proj (𝕜 := ℝ) j).fderiv]
  simp [EuclideanSpace.basisFun_apply, eq_comm]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

private theorem directional_smul_fun {g : E → ℝ} {f : E → V} {x v : E}
    (hg : DifferentiableAt ℝ g x) (hf : DifferentiableAt ℝ f x) :
    directional v (fun y => g y • f y) x =
      g x • directional v f x + directional v g x • f x := by
  simp [directional, fderiv_fun_smul hg hf]

private theorem polynomial_of_constant_diagonal_hessian {Ω : Set E} {f : E → V}
    (hΩ : IsOpen Ω) (hconn : IsConnected Ω) (hf : ContDiffOn ℝ ∞ f Ω) (c : V)
    (hess : ∀ x ∈ Ω, ∀ i j : Fin n,
      directional (axis i) (directional (axis j) f) x = if i = j then c else 0) :
    ∃ g : E → V, ContDiff ℝ ∞ g ∧ EqOn g f Ω := by
  let Q (x : E) := radialQuadratic x • c
  have hQ : ContDiff ℝ ∞ Q := radialQuadratic_contDiff.smul contDiff_const
  let u (x : E) := f x - Q x
  have hu : ContDiffOn ℝ ∞ u Ω := hf.sub hQ.contDiffOn
  have hQu (j : Fin n) : directional (axis j) Q = fun x => (EuclideanSpace.proj j x) • c := by
    funext x
    rw [directional_smul_fun (radialQuadratic_contDiff.differentiable (by simp) x) (differentiableAt_const c)]
    have hr := congrFun (radialQuadratic_directional (n := n) j) x
    rw [hr]
    have hz : directional (axis j) (fun _ : E => c) x = 0 := by simp [directional]
    rw [hz, smul_zero, zero_add]
  have hQh (x : E) (i j : Fin n) :
      directional (axis i) (directional (axis j) Q) x = if i = j then c else 0 := by
    rw [hQu, directional_smul_fun (EuclideanSpace.proj j).differentiableAt (differentiableAt_const c)]
    have h := radialQuadratic_hessian x i j
    rw [radialQuadratic_directional] at h
    rw [h]
    by_cases e : i = j <;> simp [directional, e]
  have hu1 (j : Fin n) :
      EqOn (directional (axis j) u)
        (fun x => directional (axis j) f x - directional (axis j) Q x) Ω := by
    intro x hx
    simp [u, directional, fderiv_fun_sub
      ((hf.contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp)) (hQ.differentiable (by simp) x)]
  have huh (x : E) (hx : x ∈ Ω) (i j : Fin n) :
      directional (axis i) (directional (axis j) u) x = 0 := by
    have he := ((hu1 j).eventuallyEq_of_mem (hΩ.mem_nhds hx)).fderiv_eq (𝕜 := ℝ)
    change (fderiv ℝ (directional (axis j) u) x) (axis i) = 0
    rw [he, fderiv_fun_sub
      ((directional_contDiffAt (v := axis j) (hf.contDiffAt (hΩ.mem_nhds hx))).differentiableAt (by simp))
      ((directional_contDiffAt (v := axis j) hQ.contDiffAt).differentiableAt (by simp))]
    change directional (axis i) (directional (axis j) f) x -
      directional (axis i) (directional (axis j) Q) x = 0
    rw [hess x hx i j, hQh x i j, sub_self]
  obtain ⟨p, hp⟩ := hconn.nonempty
  let L := fderiv ℝ u p
  have hLu (j : Fin n) : EqOn (directional (axis j) u) (fun _ => L (axis j)) Ω := by
    have hdu : DifferentiableOn ℝ (directional (axis j) u) Ω := by
      intro x hx
      exact ((directional_contDiffAt (v := axis j) (hu.contDiffAt (hΩ.mem_nhds hx))).differentiableAt
        (by simp)).differentiableWithinAt
    obtain ⟨a, ha⟩ := exists_const_of_directional_eq_zero_on hΩ hconn.isPreconnected hdu
      fun x hx i => huh x hx i j
    exact fun x hx => (ha hx).trans (ha hp).symm
  let w (x : E) := u x - L x
  have hw : DifferentiableOn ℝ w Ω :=
    (hu.differentiableOn (by simp)).sub L.differentiable.differentiableOn
  have hw0 (x : E) (hx : x ∈ Ω) (i : Fin n) : directional (axis i) w x = 0 := by
    have h := hLu i hx
    change fderiv ℝ u x (axis i) = L (axis i) at h
    change fderiv ℝ (fun y => u y - L y) x (axis i) = 0
    rw [fderiv_fun_sub ((hu.contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp)) L.differentiableAt,
      L.fderiv, sub_apply, h, sub_self]
  obtain ⟨a, ha⟩ := exists_const_of_directional_eq_zero_on hΩ hconn.isPreconnected hw hw0
  refine ⟨fun x => a + L x + Q x, (contDiff_const.add L.contDiff).add hQ, ?_⟩
  intro x hx
  have hh : u x - L x = a := ha hx
  dsimp only [u] at hh
  abel_nf at hh ⊢
  rw [← hh]
  abel

/-- Smooth conformal maps between Euclidean domains extend smoothly through
each point of the closure where the given map and scale extend continuously.
The weighted map and the inverse conformal scale are quadratic on the interior. -/
theorem smoothThrough_of_conformal_on_connected_domain (hn : 3 ≤ n)
    {Ω : Set E} (hΩ : IsOpen Ω) (hconn : IsConnected Ω) {F : E → E} {b : E → ℝ}
    (hF : ContDiffOn ℝ ∞ F Ω) (hb : ContDiffOn ℝ ∞ b Ω)
    (hFc : ContinuousOn F (closure Ω)) (hbc : ContinuousOn b (closure Ω))
    (hconf : EuclideanConformalOn Ω F b) :
    SmoothThrough (closure Ω) F ∧ SmoothThrough (closure Ω) b := by
  let u (x : E) := Real.exp (-b x)
  let G (x : E) := u x • F x
  have hu : ContDiffOn ℝ ∞ u Ω := hb.neg.exp
  have hG : ContDiffOn ℝ ∞ G Ω := hu.smul hF
  have huc : ContinuousOn u (closure Ω) := Real.continuous_exp.continuousOn.comp hbc.neg (mapsTo_univ _ _)
  have hGc : ContinuousOn G (closure Ω) := huc.smul hFc
  obtain ⟨c, _, hess⟩ := exists_const_exp_neg_hessian_of_conformal hn hΩ hconn.isPreconnected hF hb hconf
  obtain ⟨U, hU, hUeq⟩ := polynomial_of_constant_diagonal_hessian hΩ hconn hu c hess
  have hUcl : EqOn U u (closure Ω) :=
    eqOn_closure_of_continuousOn hU.continuous.continuousOn huc hUeq
  let k (x : E) := c • F x -
    u x • ∑ j : Fin n, directional (axis j) b x • directional (axis j) F x
  have hessG (x : E) (hx : x ∈ Ω) (i j : Fin n) :
      directional (axis i) (directional (axis j) G) x = if i = j then k x else 0 := by
    have dF := (hF.contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp)
    have db := (hb.contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp)
    have du := (hu.contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp)
    have ddF := (directional_contDiffAt (v := axis j)
      (hF.contDiffAt (hΩ.mem_nhds hx))).differentiableAt (by simp)
    have ddu := (directional_contDiffAt (v := axis j)
      (hu.contDiffAt (hΩ.mem_nhds hx))).differentiableAt (by simp)
    have hFirst : directional (axis j) G =ᶠ[𝓝 x]
        (fun y => u y • directional (axis j) F y + directional (axis j) u y • F y) := by
      filter_upwards [hΩ.mem_nhds hx] with y hy
      exact directional_smul_fun ((hu.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp))
        ((hF.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp))
    have he (l : Fin n) :
        directional (axis l) u x = u x * (-directional (axis l) b x) := by
      have h := congrArg (fun L : E →L[ℝ] ℝ => L (axis l)) db.hasFDerivAt.neg.exp.fderiv
      simpa only [u, directional, Pi.neg_apply, smul_apply, smul_eq_mul, neg_apply] using h
    calc
      _ = directional (axis i)
          (fun y => u y • directional (axis j) F y + directional (axis j) u y • F y) x :=
        congrArg (fun L : E →L[ℝ] E => L (axis i)) (hFirst.fderiv_eq (𝕜 := ℝ))
      _ = (u x • directional (axis i) (directional (axis j) F) x +
            directional (axis i) u x • directional (axis j) F x) +
          (directional (axis j) u x • directional (axis i) F x +
            directional (axis i) (directional (axis j) u) x • F x) := by
        have hAdd := fderiv_fun_add (du.smul ddF) (ddu.smul dF)
        change (fderiv ℝ (fun y => u y • directional (axis j) F y +
          directional (axis j) u y • F y) x) (axis i) = _
        change (fderiv ℝ (fun y => (u • directional (axis j) F) y +
          (directional (axis j) u • F) y) x) (axis i) = _
        rw [hAdd, add_apply]
        exact congrArg₂ (· + ·) (directional_smul_fun du ddF) (directional_smul_fun ddu dF)
      _ = _ := by
        rw [he i, he j, hess x hx i j,
          directional_directional_of_conformal hΩ hx (hF.contDiffAt (hΩ.mem_nhds hx))
            (hb.contDiffAt (hΩ.mem_nhds hx)) hconf]
        simp only [conformalConnection, add_smul, sub_smul, Finset.sum_add_distrib,
          Finset.sum_sub_distrib, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
          mul_smul, neg_smul, smul_add, smul_sub]
        by_cases h : i = j
        · subst j
          simp [k, smul_neg]
          abel
        · simp [h, smul_neg]
  have hkcont (x : E) (hx : x ∈ Ω) : ContDiffAt ℝ ∞ k x := by
    have hFx := hF.contDiffAt (hΩ.mem_nhds hx)
    have hbx := hb.contDiffAt (hΩ.mem_nhds hx)
    exact ((contDiffAt_const (c := c)).smul hFx).sub ((hu.contDiffAt (hΩ.mem_nhds hx)).smul
      (ContDiffAt.sum (s := (Finset.univ : Finset (Fin n)))
        (f := fun i y => directional (axis i) b y • directional (axis i) F y)
        fun i _ => (directional_contDiffAt hbx).smul (directional_contDiffAt hFx)))
  have hk0 (x : E) (hx : x ∈ Ω) (i : Fin n) : directional (axis i) k x = 0 := by
    have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
    obtain ⟨j, hj⟩ := exists_ne i
    have haa : directional (axis j) (directional (axis j) G) =ᶠ[𝓝 x] k := by
      filter_upwards [hΩ.mem_nhds hx] with y hy using by simpa using hessG y hy j j
    have hbb : directional (axis i) (directional (axis j) G) =ᶠ[𝓝 x] fun _ => (0 : E) := by
      filter_upwards [hΩ.mem_nhds hx] with y hy using by simpa [hj.symm] using hessG y hy i j
    have hcomm := directional_comm (directional_contDiffAt (v := axis j)
      (hG.contDiffAt (hΩ.mem_nhds hx))) (axis i) (axis j)
    have ha := congrArg (fun L : E →L[ℝ] E => L (axis i)) (haa.fderiv_eq (𝕜 := ℝ))
    have hb := congrArg (fun L : E →L[ℝ] E => L (axis j)) (hbb.fderiv_eq (𝕜 := ℝ))
    have hb₀ : directional (axis j) (directional (axis i) (directional (axis j) G)) x = 0 := by
      change (fderiv ℝ (directional (axis i) (directional (axis j) G)) x) (axis j) = 0
      have hz : (fderiv ℝ (fun _ : E => (0 : E)) x) (axis j) = 0 := by simp
      exact hb.trans hz
    exact ha.symm.trans (hcomm.trans hb₀)
  obtain ⟨z, hz⟩ := exists_const_of_directional_eq_zero_on hΩ hconn.isPreconnected
    (fun x hx => ((hkcont x hx).differentiableAt (by simp)).differentiableWithinAt) hk0
  obtain ⟨R, hR, hReq⟩ := polynomial_of_constant_diagonal_hessian hΩ hconn hG z
    (fun x hx i j => by rw [hessG x hx i j, hz hx])
  have hRcl : EqOn R G (closure Ω) :=
    eqOn_closure_of_continuousOn hR.continuous.continuousOn hGc hReq
  let V := {x | 0 < U x}
  have hV : IsOpen V := hU.continuous.isOpen_preimage _ isOpen_Ioi
  have hcl : closure Ω ⊆ V := by
    intro x hx
    change 0 < U x
    rw [hUcl hx]
    exact Real.exp_pos _
  constructor
  · intro x hx
    refine ⟨V, hV, hcl hx, fun y => (U y)⁻¹ • R y, ?_, ?_⟩
    · exact (hU.contDiffOn.inv (fun y hy => (show 0 < U y from hy).ne')).smul hR.contDiffOn
    · intro y hy
      change (U y)⁻¹ • R y = F y
      rw [hUcl hy.2, hRcl hy.2]
      change (u y)⁻¹ • (u y • F y) = F y
      rw [smul_smul, inv_mul_cancel₀ (Real.exp_pos _).ne', one_smul]
  · intro x hx
    refine ⟨V, hV, hcl hx, fun y => -Real.log (U y), ?_, ?_⟩
    · exact (hU.contDiffOn.log (fun y hy => (show 0 < U y from hy).ne')).neg
    · intro y hy
      change -Real.log (U y) = b y
      rw [hUcl hy.2]
      simp [u]

end CalderonPaper
