module

public import Proof.CalderonN.ParametricBallConormal
public import Proof.CalderonN.BallBoundaryAdjoint

import Mathlib.Tactic

/-! Adapted from `ParametricBallVelocityAdjoint` in the checked Theorem 3.1 release. -/

public section

set_option maxHeartbeats 1600000

noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]
open OAI.AnisotropicCalderon.SmoothSphereRotation

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

@[expose] def velocityBoundaryDatum
    (g : P × (X dim) → (Mat dim)) (V : P × (X dim) → (X dim)) (ψ : P × (X dim) → ℝ) (q : P × (X dim)) : ℝ :=
  ψ q * conormalComponent (fun w => g (q.1,w)) q.2 (V q)

@[expose] def velocityRotationDatum
    (g : P × (X dim) → (Mat dim)) (V : P × (X dim) → (X dim)) (ψ : P × (X dim) → ℝ)
    (i j : (I dim)) (q : P × (X dim)) : ℝ :=
  ψ q * (q.2 i * tangentialComponent (fun w => g (q.1,w)) q.2 (V q) j)

/-- The angular adjoint of a velocity, with its harmonic normal
contribution and its tangential integration-by-parts terms. -/
@[expose] def parametricBallVelocityAdjoint
    (g : P × (X dim) → (Mat dim)) (V : P × (X dim) → (X dim)) (ψ : P × (X dim) → ℝ) (q : P × (X dim)) : ℝ :=
  parametricBallConormal g (velocityBoundaryDatum g V ψ) q -
    ∑ i, ∑ j, sphereRotationDerivative i j
      (fun z => velocityRotationDatum g V ψ i j (q.1,z)) (sphereNormalize q.2)

omit [FiniteDimensional ℝ P] in
theorem ballVelocityAdjointData_smooth
    {S : Set (P × (X dim))} {g : P × (X dim) → (Mat dim)} {V : P × (X dim) → (X dim)} {ψ : P × (X dim) → ℝ}
    (hg : ∀ i j, ContDiffOn ℝ ∞ (fun q => g q i j) S)
    (hPos : ∀ q ∈ S, (g q).PosDef) (hS : ∀ q ∈ S, q.2 ≠ 0)
    (hV : ContDiffOn ℝ ∞ V S) (hψ : ContDiffOn ℝ ∞ ψ S) :
    ContDiffOn ℝ ∞ (velocityBoundaryDatum g V ψ) S ∧
      ∀ i j, ContDiffOn ℝ ∞ (velocityRotationDatum g V ψ i j) S := by
  let C (q : P × (X dim)) := ballConormalVector (fun z => g (q.1,z)) q.2
  have hC : ContDiffOn ℝ ∞ C S := contDiffOn_product_ballConormalVector hg hPos
  let c (q : P × (X dim)) := conormalComponent (fun z => g (q.1,z)) q.2 (V q)
  have hc : ContDiffOn ℝ ∞ c S :=
    (contDiff_snd.contDiffOn.inner ℝ hV).div (contDiff_snd.contDiffOn.inner ℝ hC)
      (fun q hq => (ballConormalVector_inner_pos (hPos q hq) (hS q hq)).ne')
  have hT : ContDiffOn ℝ ∞ (fun q : P × (X dim) =>
      tangentialComponent (fun z => g (q.1,z)) q.2 (V q)) S :=
    hV.sub (hc.smul hC)
  refine ⟨hψ.mul hc,fun i j => ?_⟩
  exact hψ.mul ((((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp contDiff_snd).contDiffOn).mul
      ((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp_contDiffOn hT))

omit [FiniteDimensional ℝ P] in
private theorem contDiffOn_fiberRotation
    {T : Set (P × (X dim))} (hT : IsOpen T) {d : P × (X dim) → ℝ} (hd : ContDiffOn ℝ ∞ d T)
    (i j : (I dim)) : ContDiffOn ℝ ∞ (fun q : P × (X dim) =>
      sphereRotationDerivative i j (fun z => d (q.1,z)) q.2) T := by
  have hC : ContDiffOn ℝ ∞ (fun q : P × (X dim) =>
      fderiv ℝ d q (0,rotationVector i j q.2)) T :=
    (hd.fderiv_of_isOpen (m := ∞) hT (by simp)).clm_apply
      ((contDiff_const (c := (0:P))).prodMk ((contDiff_rotationVector i j).comp contDiff_snd)).contDiffOn
  apply hC.congr
  intro q hq
  have hD : DifferentiableAt ℝ d (q.1,q.2) :=
    (hd.contDiffAt (hT.mem_nhds hq)).differentiableAt (by simp)
  have hSlice : HasFDerivAt (Prod.mk q.1) (ContinuousLinearMap.inr ℝ P (X dim)) q.2 :=
    hasFDerivAt_prodMk_right q.1 q.2
  have h := (hD.hasFDerivAt.comp q.2 hSlice).fderiv
  change (fderiv ℝ (d ∘ Prod.mk q.1) q.2) (rotationVector i j q.2) = _
  rw [h]
  simp

set_option maxHeartbeats 1600000 in
/-- The literal velocity adjoint varies smoothly with the metric, the
velocity and the input field around the sphere. -/
theorem exists_contDiffOn_parametricBallVelocityAdjoint
    {U T : Set (P × (X dim))} (hU : IsOpen U) (hT : IsOpen T) (p₀ : P)
    (hCU : {p₀} ×ˢ closedBall (0 : (X dim)) 1 ⊆ U)
    (hST : {p₀} ×ˢ (standardSphere dim) ⊆ T)
    {g : P × (X dim) → (Mat dim)} (hg : ∀ i j, ContDiffOn ℝ ∞ (fun q => g q i j) U)
    (hPos : ∀ q ∈ U, (g q).PosDef) {V : P × (X dim) → (X dim)} {ψ : P × (X dim) → ℝ}
    (hV : ContDiffOn ℝ ∞ V T) (hψ : ContDiffOn ℝ ∞ ψ T) :
    ∃ W : Set P, IsOpen W ∧ p₀ ∈ W ∧ ContDiffOn ℝ ∞ (parametricBallVelocityAdjoint g V ψ)
      (W ×ˢ ({0}ᶜ : Set (X dim))) := by
  let N : Set (X dim) := ({0}ᶜ : Set (X dim))
  let Q := (U ∩ T) ∩ ((univ : Set P) ×ˢ N)
  have hN : IsOpen N := isClosed_singleton.isOpen_compl
  have hQ : IsOpen Q := (hU.inter hT).inter (isOpen_univ.prod hN)
  have hSQ : {p₀} ×ˢ (standardSphere dim) ⊆ Q := by
    intro q hq
    have hn := mem_sphere_zero_iff_norm.mp hq.2
    exact ⟨⟨hCU ⟨hq.1,sphere_subset_closedBall hq.2⟩,hST hq⟩,
      mem_univ _,fun h => by have he : q.2 = 0 := h; simp [he] at hn⟩
  have hQU : Q ⊆ U := inter_subset_left.trans inter_subset_left
  have hQT : Q ⊆ T := inter_subset_left.trans inter_subset_right
  obtain ⟨hd,hRot⟩ := ballVelocityAdjointData_smooth (fun i j => (hg i j).mono hQU)
    (fun q hq => hPos q (hQU hq)) (fun _ hq => hq.2.2) (hV.mono hQT) (hψ.mono hQT)
  obtain ⟨V₁,hV₁,hp₁,hCor⟩ :=
    exists_contDiffOn_parametricBallConormal hU hQ p₀ hCU hSQ hg hPos hd
  obtain ⟨V₂,Z,hV₂,_,hp₂,hZ,hVZ⟩ := generalized_tube_lemma
    (isCompact_singleton (x := p₀)) (isCompact_sphere (0 : (X dim)) 1) hQ hSQ
  let W := V₁ ∩ V₂
  have hW : IsOpen W := hV₁.inter hV₂
  have hWZ : W ×ˢ Z ⊆ Q := fun q hq => hVZ ⟨hq.1.2,hq.2⟩
  have hNorm : ContDiffOn ℝ ∞ (fun q : P × (X dim) => (q.1,sphereNormalize q.2)) (W ×ˢ N) :=
    contDiff_fst.contDiffOn.prodMk (contDiffOn_sphereNormalize.comp contDiff_snd.contDiffOn
      (fun q hq => hq.2))
  have hMap : MapsTo (fun q : P × (X dim) => (q.1,sphereNormalize q.2)) (W ×ˢ N) Q :=
    fun q hq => hWZ ⟨hq.1,hZ (sphereNormalize_mem_sphere hq.2)⟩
  refine ⟨W,hW,⟨hp₁,hp₂ (mem_singleton _)⟩,?_⟩
  exact (hCor.mono (fun q hq => ⟨hq.1.1,hq.2⟩)).sub
    (ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ =>
      (contDiffOn_fiberRotation hQ (hRot i j) i j).comp hNorm hMap)

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
theorem parametricBallVelocityAdjoint_on_sphere
    (g : P × (X dim) → (Mat dim)) (V : P × (X dim) → (X dim)) (ψ : P × (X dim) → ℝ) (p : P)
    {w : (X dim)} (hw : w ∈ (standardSphere dim)) :
    parametricBallVelocityAdjoint g V ψ (p,w) =
      ballVelocityAdjoint (fun z => g (p,z)) (fun z => V (p,z)) (fun z => ψ (p,z))
        (fixedBallPoisson (fun z => g (p,z)) (fun z => velocityBoundaryDatum g V ψ (p,z))) w := by
  simp only [parametricBallVelocityAdjoint,parametricBallConormal,ballVelocityAdjoint,
    sphereNormalize_eq_of_sphere hw,velocityRotationDatum]

omit [FiniteDimensional ℝ P] in
/-- The parametric choice of Poisson solution implements the exact real
adjoint on each fixed sphere. -/
theorem integral_parametricBallVelocityAdjoint
    (p : P) {g : P × (X dim) → (Mat dim)} {V : P × (X dim) → (X dim)} {ψ : P × (X dim) → ℝ}
    {U S : Set (X dim)} (hU : IsOpen U) (hS : IsOpen S)
    (hBU : closedBall (0 : (X dim)) 1 ⊆ U) (hSS : (standardSphere dim) ⊆ S) (hSU : S ⊆ U)
    (hS₀ : (0 : (X dim)) ∉ S) (hg : SmoothMetric U (fun z => g (p,z)))
    (hV : ContDiffOn ℝ ∞ (fun z => V (p,z)) S) (hψ : ContDiffOn ℝ ∞ (fun z => ψ (p,z)) S)
    {u : (X dim) → ℝ} (hu : ContDiffOn ℝ ∞ u U)
    (hLap : ∀ x ∈ ball (0 : (X dim)) 1, laplace (fun z => g (p,z)) u x = 0) :
    (∫ w : ↥(standardSphere dim), parametricBallVelocityAdjoint g V ψ (p,w) * u w ∂(sphereProbability dim)) =
      ∫ w : ↥(standardSphere dim), ψ (p,w) * fderiv ℝ u w (V (p,w)) ∂(sphereProbability dim) := by
  let a := fun z : (X dim) => g (p,z)
  let d := fun z : (X dim) => velocityBoundaryDatum g V ψ (p,z)
  let b := fixedBallPoisson a d
  have hN : ContDiffOn ℝ ∞ (fun z => conormalComponent a z (V (p,z))) S :=
    (contDiffOn_id.inner ℝ hV).div
      (contDiffOn_id.inner ℝ ((contDiffOn_ballConormalVector hg).mono hSU))
      (fun z hz => (ballConormalVector_inner_pos (hg.2 z (hSU hz)) (fun h => hS₀ (h ▸ hz))).ne')
  have hd : smoothNear d (standardSphere dim) := ⟨S,hS,hSS,hψ.mul hN⟩
  have hP : FixedBallSolution a d b := fixedBallPoisson_solution hU hBU hg hd
  have h := integral_ballVelocityAdjoint hU hS hBU hSS hSU hS₀ hg hu hP.1.contDiffOn
    hLap hP.2.2 hψ hV hP.2.1
  refine (integral_congr_ae (Eventually.of_forall (fun w : ↥(standardSphere dim) => ?_))).trans h
  rw [parametricBallVelocityAdjoint_on_sphere g V ψ p w.property]


end CalderonN
