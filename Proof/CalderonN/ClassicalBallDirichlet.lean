module

public import Proof.CalderonN.ClassicalBallRepresentative
public import Proof.CalderonN.ClassicalBallEquation
public import Proof.CalderonN.ParametricBallStrongSolution

import Proof.CalderonN.EllipticCalculus
import Mathlib.Tactic

public section

noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise

namespace CalderonN

variable {dim : ℕ} [NeZero dim]


open CalderonN.BallDirichlet

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

omit [FiniteDimensional ℝ P] in
theorem section_coordDeriv_eq_product_fderiv
    {b : P × (X dim) → ℝ} (hb : ContDiff ℝ ∞ b) (p : P) (x : (X dim)) (i : (I dim)) :
    coordDeriv i (fun z => b (p,z)) x = fderiv ℝ b (p,x) (0,axis i) := by
  have h := ((hb.differentiable (by simp) (p,x)).hasFDerivAt.comp x
    (hasFDerivAt_prodMk_right p x)).fderiv
  change fderiv ℝ (b ∘ Prod.mk p) x (axis i) = _
  rw [h]
  simp

/-- The same divergence expression is smooth with the ball parameters. -/
theorem contDiff_negativeBallDivergence_family
    {a : P × (X dim) → (Mat dim)} (ha : ContDiff ℝ ∞ a) {u : P × (X dim) → ℝ} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (fun q : P × (X dim) =>
      negativeBallDivergence (fun z => a (q.1,z)) (fun z => u (q.1,z)) q.2) := by
  let w (i : (I dim)) (q : P × (X dim)) := ∑ j : (I dim), a q i j * fderiv ℝ u q (0,axis j)
  have hw (i : (I dim)) : ContDiff ℝ ∞ (w i) := by
    apply ContDiff.sum
    intro j _
    let L : (Mat dim) →L[ℝ] ℝ := (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap
    exact (L.contDiff.comp ha).mul ((hu.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const)
  have he (q : P × (X dim)) : negativeBallDivergence (fun z => a (q.1,z)) (fun z => u (q.1,z)) q.2 =
      -(∑ i : (I dim), fderiv ℝ (w i) q (0,axis i)) := by
    unfold negativeBallDivergence Elliptic.Lop Elliptic.pd
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    simp_rw [section_coordDeriv_eq_product_fderiv hu]
    exact section_coordDeriv_eq_product_fderiv (hw i) q.1 q.2 i
  simp_rw [he]
  exact (ContDiff.sum fun i _ => ((hw i).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).neg

set_option maxHeartbeats 1600000 in
/-- At every elliptic parameter the fixed inverse produces a classical
zero-Dirichlet solution, with no loss of derivatives at the sphere. -/
theorem exists_classical_zeroDirichlet_of_parametricStrongSolution [Nontrivial (Fin dim)]
    (V : Set P)
    (a : P × (X dim) → (Mat dim)) (ha : ContDiff ℝ ∞ a)
    (Ka : Set (X dim)) (hKa : IsCompact Ka) (hSa : ∀ p z, z ∉ Ka → a (p,z) = 0)
    (f : P × (X dim) → ℝ) (hf : ContDiff ℝ ∞ f)
    (Kf : Set (X dim)) (hKf : IsCompact Kf) (hSf : ∀ p z, z ∉ Kf → f (p,z) = 0)
    (lo hi : P → ℝ)
    (hEll : ∀ p ∈ V, TauCeti.PDE.UniformlyEllipticOn ((fixedBallOpens dim) : Set (X dim))
      (fun z => a (p,z)) (lo p) (hi p)) :
    ∀ p ∈ V, ∃ b : (X dim) → ℝ, ContDiff ℝ ∞ b ∧ EqOn b 0 (standardSphere dim) ∧
      EqOn (negativeBallDivergence (fun z => a (p,z)) b) (fun z => f (p,z)) (ball (0 : (X dim)) 1) := by
  obtain ⟨U,_,hU⟩ := exists_parametric_ballStrongSolution V a ha Ka hKa hSa f hf Kf hKf hSf lo hi hEll
  intro p hp
  obtain ⟨b,hb,hbv⟩ := exists_smooth_strongBallRepresentative
    (U := fun s => U s p) (fun s => (hU p hp s).1)
  let v := (strongDirichletProjectionL dim) 0 (U 0 p)
  have hA : ContDiff ℝ ∞ (fun z => a (p,z)) := ha.comp (contDiff_const.prodMk contDiff_id)
  have hF : ContDiff ℝ ∞ (fun z => f (p,z)) := hf.comp (contDiff_const.prodMk contDiff_id)
  refine ⟨b,hb,eqOn_zero_sphere_of_ballH1Zero hb v hbv,?_⟩
  exact negativeBallDivergence_eq_of_ballWeakSolution hA hF hb v hbv _
    (ballForcingFamily_value 0 f hf Kf hKf hSf p) (hU p hp 0).2.1

/-- The fixed differential expression is linear in its solution. -/
theorem negativeBallDivergence_add {A : (X dim) → (Mat dim)} (hA : ContDiff ℝ ∞ A)
    {u v : (X dim) → ℝ} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (z : (X dim)) :
    negativeBallDivergence A (u+v) z =
      negativeBallDivergence A u z + negativeBallDivergence A v z := by
  let b (x : (X dim)) := u x + v x
  change negativeBallDivergence A b z = _
  have hLinear (i : (I dim)) (x : (X dim)) : coordDeriv i b x = coordDeriv i u x + coordDeriv i v x := by
    unfold coordDeriv b
    rw [fderiv_fun_add (hu.differentiable (by simp) x) (hv.differentiable (by simp) x),add_apply]
  have hFlux (i : (I dim)) (g : (X dim) → ℝ) (hg : ContDiff ℝ ∞ g) :
      ContDiff ℝ ∞ (fun x => ∑ j : (I dim), A x i j * coordDeriv j g x) := by
    apply ContDiff.sum
    intro j _
    let L : (Mat dim) →L[ℝ] ℝ := (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap
    exact (L.contDiff.comp hA).mul ((hg.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const)
  have hDeriv (i : (I dim)) :
      coordDeriv i (fun x => ∑ j : (I dim), A x i j * coordDeriv j b x) z =
        coordDeriv i (fun x => ∑ j : (I dim), A x i j * coordDeriv j u x) z +
        coordDeriv i (fun x => ∑ j : (I dim), A x i j * coordDeriv j v x) z := by
    simp_rw [hLinear,mul_add,Finset.sum_add_distrib]
    unfold coordDeriv
    exact congrFun (congrArg DFunLike.coe (fderiv_fun_add
      ((hFlux i u hu).differentiable (by simp) z)
      ((hFlux i v hv).differentiable (by simp) z))) (axis i)
  simp only [negativeBallDivergence,Elliptic.Lop,Elliptic.pd,hDeriv,Finset.sum_add_distrib,neg_add]

set_option maxHeartbeats 1200000 in
theorem exists_classical_ballDirichlet_of_parametricStrongSolution [Nontrivial (Fin dim)]
    (V : Set P)
    (a : P × (X dim) → (Mat dim)) (ha : ContDiff ℝ ∞ a)
    (Ka : Set (X dim)) (hKa : IsCompact Ka) (hSa : ∀ p z, z ∉ Ka → a (p,z) = 0)
    (d : P × (X dim) → ℝ) (hd : ContDiff ℝ ∞ d)
    (lo hi : P → ℝ)
    (hEll : ∀ p ∈ V, TauCeti.PDE.UniformlyEllipticOn ((fixedBallOpens dim) : Set (X dim))
      (fun z => a (p,z)) (lo p) (hi p)) :
    ∀ p ∈ V, ∃ b : (X dim) → ℝ, ContDiff ℝ ∞ b ∧ EqOn b (fun z => d (p,z)) (standardSphere dim) ∧
      EqOn (negativeBallDivergence (fun z => a (p,z)) b) 0 (ball (0 : (X dim)) 1) := by
  let f (q : P × (X dim)) := -negativeBallDivergence (fun z => a (q.1,z))
    (fun z => d (q.1,z)) q.2
  have hf : ContDiff ℝ ∞ f := (contDiff_negativeBallDivergence_family ha hd).neg
  have hSupp (p : P) (z : (X dim)) (hz : z ∉ Ka) : f (p,z) = 0 := by
    have he (i : (I dim)) : (fun x => ∑ j : (I dim), a (p,x) i j * coordDeriv j (fun v => d (p,v)) x)
        =ᶠ[𝓝 z] fun _ => (0:ℝ) := by
      filter_upwards [hKa.isClosed.isOpen_compl.mem_nhds hz] with x hx
      simp [hSa p x hx]
    have hD (i : (I dim)) : coordDeriv i (fun x => ∑ j : (I dim),
        a (p,x) i j * coordDeriv j (fun v => d (p,v)) x) z = 0 := by
      rw [coordDeriv,(he i).fderiv_eq]
      simp
    simp only [f,negativeBallDivergence,Elliptic.Lop,Elliptic.pd,hD,Finset.sum_const_zero,neg_zero]
  intro p hp
  obtain ⟨u,hu,hU,hEq⟩ :=
    exists_classical_zeroDirichlet_of_parametricStrongSolution V a ha Ka hKa hSa f hf Ka hKa hSupp lo hi hEll p hp
  let b (z : (X dim)) := u z + d (p,z)
  have hDatum : ContDiff ℝ ∞ (fun z => d (p,z)) := hd.comp (contDiff_const.prodMk contDiff_id)
  refine ⟨b,hu.add hDatum,fun z hz => ?_,?_⟩
  · change u z + d (p,z) = _
    rw [show u z = 0 from hU hz,zero_add]
  · intro z hz
    let c := fun x : (X dim) => d (p,x)
    let A := fun x : (X dim) => a (p,x)
    have hA : ContDiff ℝ ∞ A := ha.comp (contDiff_const.prodMk contDiff_id)
    change negativeBallDivergence A b z = 0
    rw [show b = u+c from rfl,negativeBallDivergence_add hA hu hDatum,hEq hz]
    change -negativeBallDivergence A c z + negativeBallDivergence A c z = 0
    exact neg_add_cancel _

end CalderonN
