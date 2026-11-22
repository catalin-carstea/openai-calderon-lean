module

public import Proof.CalderonN.ActualGaussConormalCore

import Proof.CalderonN.ParametricBallConormal
import Proof.CalderonN.CompactSmoothExtension
import Proof.CalderonN.SmoothTraceLinearAdjunction
import Mathlib.Tactic

/-! The classical conormal response as a regular, symmetric fiber
operator on compactly base-supported smooth traces. -/

public section

noncomputable section
open Set Filter Metric
open scoped ContDiff Topology Matrix.Norms.Elementwise InnerProductSpace Classical
set_option autoImplicit false
set_option maxHeartbeats 4200000
set_option maxSynthPendingDepth 29
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE OAI.AnisotropicCalderon SphereHarmonic
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)} {d : Data dim}

@[expose] def ActualGaussFiberData.conormal {x : X dim} (D : ActualGaussFiberData d x) :
    Module.End ℝ (SmoothSphereTrace dim) :=
  smoothSphereTraceMul D.weight *
    ((LinearMap.fst ℝ _ _).comp (smoothSphereTaylorResponses D.smoothCoefficient D.ellipticCoefficient D.solve))

theorem ActualGaussFiberData.conormal_apply {x : X dim} (D : ActualGaussFiberData d x) (f : SmoothData dim) :
    D.conormal (smoothSphereTrace f) =
      smoothSphereTrace ⟨smoothBallConormal D.coefficient (D.solve f).actual.1,
        contDiff_smoothBallConormal D.smoothCoefficient (D.solve f).actual⟩ := by
  apply Subtype.ext
  funext z
  rw [ActualGaussFiberData.conormal,Module.End.mul_apply,LinearMap.comp_apply,
    smoothSphereTaylorResponses_apply,LinearMap.fst_apply,smoothSphereTraceMul_apply,
    smoothSphereTrace_apply,smoothSphereTrace_apply]
  exact (D.weightConormal (D.solve f).actual z.property).symm

theorem ActualGaussFiberData.conormal_symmetric (hn : 3 ≤ dim) {x : X dim}
    (D : ActualGaussFiberData d x) (hSym : ∀ z ∈ ball (0:X dim) 1,(D.coefficient z).IsSymm) :
    SmoothTraceAdjoint hn D.conormal D.conormal := by
  intro u v
  obtain ⟨f,rfl⟩ := smoothSphereTraceL_surjective u
  obtain ⟨g,rfl⟩ := smoothSphereTraceL_surjective v
  let u : SmoothData dim := ⟨f.1,smoothBallData_contDiff f⟩
  let v : SmoothData dim := ⟨g.1,smoothBallData_contDiff g⟩
  change ⟪smoothSphereTraceL2 hn (D.conormal (smoothSphereTrace u)),
    smoothSphereTraceL2 hn (smoothSphereTrace v)⟫_ℝ =
      ⟪smoothSphereTraceL2 hn (smoothSphereTrace u),
        smoothSphereTraceL2 hn (D.conormal (smoothSphereTrace v))⟫_ℝ
  rw [D.conormal_apply,D.conormal_apply]
  simp only [smoothSphereTraceL2_apply,smoothSphereLift_inner]
  exact integral_smoothBallConormal_symm D.smoothCoefficient
    hSym
    u v (D.solve u).actual (D.solve v).actual (D.solve u).actualEquation (D.solve v).actualEquation
    (D.solve u).actualTrace (D.solve v).actualTrace

@[expose] def actualGaussConormalFamily (D : ∀ x ∈ Y, ActualGaussFiberData d x) (x : X dim) :
    Module.End ℝ (SmoothSphereTrace dim) :=
  if hx : x ∈ Y then (D x hx).conormal else 0

theorem actualGaussConormalFamily_regular (hY : IsOpen Y)
    (D : ∀ x ∈ Y,ActualGaussFiberData d x)
    (hLoc : ∀ y ∈ Y, ∃ (V : Set (X dim)) (a : X dim × X dim → Mat dim) (J : Set (X dim)),
      IsOpen V ∧ y ∈ V ∧ V ⊆ Y ∧ ContDiff ℝ ∞ a ∧ IsCompact J ∧
      (∀ x z,z ∉ J → a (x,z) = 0) ∧
      ∀ x ∈ V, ∀ hx : x ∈ Y, EqOn (fun z => a (x,z)) (D x hx).coefficient (ball (0:X dim) 1)) :
    SmoothSupportedTraceFiberRegular Y (actualGaussConormalFamily D) := by
  classical
  intro u
  obtain ⟨G,hG,hRep⟩ := smoothSupportedTraceSection_repr u
  let Z : Set (X dim) := {0}ᶜ
  let H (p : X dim × X dim) : ℝ :=
    if hz : p.2 ∈ Z then
      (actualGaussConormalFamily D p.1 (smoothSupportedTraceFiberL p.1 u)).1
        ⟨sphereNormalize p.2,sphereNormalize_mem_sphere hz⟩
    else 0
  have hZ : IsOpen Z := isClosed_singleton.isOpen_compl
  refine ⟨Y ×ˢ Z,H,hY.prod hZ,prod_mono_right (fun z hz => ?_),?_,?_⟩
  · change z ≠ 0
    intro h
    simp [h,standardSphere] at hz
  · apply contDiffOn_of_locally_contDiffOn
    intro q hq
    obtain ⟨V,a,J,hV,hqV,hVY,ha,hJ,hSupp,hEq⟩ := hLoc q.1 hq.1
    let lo (x : X dim) := if hx : x ∈ Y then (D x hx).lo else 1
    let hi (x : X dim) := if hx : x ∈ Y then (D x hx).hi else 1
    have hEll (x : X dim) (hx : x ∈ V) :
        UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) (fun z => a (x,z)) (lo x) (hi x) := by
      have hYx := hVY hx
      simp only [lo,hi,dite_eq_left hYx]
      let E := D x hYx
      refine ⟨E.ellipticCoefficient.1,E.ellipticCoefficient.2.1,fun z hz => ?_⟩
      rw [hEq x hx hYx hz]
      exact E.ellipticCoefficient.2.2 hz
    obtain ⟨b,hb,hB,_,hbD⟩ := exists_parametric_classical_ballDirichlet hV a ha J hJ hSupp G hG lo hi hEll
    let W := V ×ˢ Z
    let S := V ×ˢ closedBall (0:X dim) 1
    let N (p : X dim × X dim) := (p.1,sphereNormalize p.2)
    let T (p : X dim × X dim) := smoothBallConormal (fun z => a (p.1,z)) (b p.1) p.2
    have hN : ContDiffOn ℝ ∞ N W :=
      contDiff_fst.contDiffOn.prodMk (contDiffOn_sphereNormalize.comp contDiff_snd.contDiffOn fun _ h => h.2)
    have hNS : MapsTo N W S := fun p hp => ⟨hp.1,sphere_subset_closedBall (sphereNormalize_mem_sphere hp.2)⟩
    have hT : ContDiffOn ℝ ∞ T S := by
      have hD (i : I dim) : ContDiffOn ℝ ∞ (fun p : X dim × X dim => coordDeriv i (b p.1) p.2) S :=
        hbD.clm_apply contDiffOn_const
      have hE (p : X dim × X dim) :
          T p = ∑ i : I dim,p.2 i*(∑ j : I dim,a p i j*coordDeriv j (b p.1) p.2) := by
        simp only [T,smoothBallConormal,EuclideanSpace.inner_eq_star_dotProduct,dotProduct,star_trivial,
          smoothBallFlux_apply]
        exact Finset.sum_congr rfl fun i _ => mul_comm _ _
      have hL : ContDiffOn ℝ ∞ (fun p : X dim × X dim =>
          ∑ i : I dim,p.2 i*(∑ j : I dim,a p i j*coordDeriv j (b p.1) p.2)) S := by
        apply ContDiffOn.sum
        intro i _
        apply ((EuclideanSpace.proj (𝕜:=ℝ) i).contDiff.comp contDiff_snd).contDiffOn.mul
        exact ContDiffOn.sum fun j _ =>
          ((contDiff_pi.mp (contDiff_pi.mp ha i) j).contDiffOn).mul (hD j)
      exact hL.congr (fun p _ => hE p)
    have hComp := hT.comp hN hNS
    refine ⟨W,hV.prod hZ,⟨hqV,hq.2⟩,?_⟩
    apply (hComp.mono inter_subset_right).congr
    intro p hp
    have hx := hp.2.1
    have hYx := hVY hx
    let E := D p.1 hYx
    let f : SmoothData dim := ⟨fun z => G (p.1,z),hG.comp (contDiff_const.prodMk contDiff_id)⟩
    let P := E.solve f
    let z := sphereNormalize p.2
    have hz : z ∈ standardSphere dim := sphereNormalize_mem_sphere hp.2.2
    have hF : smoothSupportedTraceFiberL p.1 u = smoothSphereTrace f := Subtype.ext (funext (hRep p.1))
    have hAC := hEq p.1 hx hYx
    have ha' : ContDiff ℝ ∞ (fun z => a (p.1,z)) := ha.comp (contDiff_const.prodMk contDiff_id)
    have hClosed : EqOn (fun z => a (p.1,z)) E.coefficient (closedBall (0:X dim) 1) := by
      rw [← closure_ball _ (by norm_num : (1:ℝ) ≠ 0)]
      exact hAC.closure ha'.continuous E.smoothCoefficient.continuous
    have hbP : EqOn (negativeBallDivergence E.coefficient (b p.1)) 0 (ball (0:X dim) 1) := by
      intro w hw
      have hEv : (fun z => a (p.1,z)) =ᶠ[𝓝 w] E.coefficient := by
        filter_upwards [isOpen_ball.mem_nhds hw] with z hz using hAC hz
      rw [← negativeBallDivergence_congr_germ hEv EventuallyEq.rfl]
      exact (hB p.1 hx).2 hw
    have hSol := eqOn_closedUnitBall_of_equal_ball_forcing E.smoothCoefficient E.ellipticCoefficient
      (fun _ _ => rfl) ⟨b p.1,hb p.1⟩ P.actual
      (fun w hw => (hbP hw).trans (P.actualEquation hw).symm)
      ((hB p.1 hx).1.trans P.actualTrace.symm)
    have hDer := eqOn_fderiv_closedUnitBall (hb p.1) P.actual.2 hSol (sphere_subset_closedBall hz)
    have hFlux : smoothBallFlux (fun z => a (p.1,z)) (b p.1) z =
        smoothBallFlux E.coefficient P.actual.1 z := by
      ext i
      simp only [smoothBallFlux_apply,hClosed (sphere_subset_closedBall hz),coordDeriv,hDer]
    unfold H
    rw [dite_eq_left hp.2.2,actualGaussConormalFamily,dite_eq_left hYx,hF,E.conormal_apply,
      smoothSphereTrace_apply]
    change smoothBallConormal E.coefficient P.actual.1 z = smoothBallConormal (fun z => a (p.1,z)) (b p.1) z
    simp only [smoothBallConormal,hFlux]
  · intro x hx z
    have h0 : (z : X dim) ∈ Z := by
      change (z : X dim) ≠ 0
      intro h
      have hz := mem_sphere_zero_iff_norm.mp z.property
      rw [h,norm_zero] at hz
      exact zero_ne_one hz
    simp only [H,dite_eq_left h0]
    have hEq : (⟨sphereNormalize z,sphereNormalize_mem_sphere h0⟩ : ↥(standardSphere dim)) = z :=
      Subtype.ext (sphereNormalize_eq_of_sphere z.property)
    rw [hEq]

end CalderonN
