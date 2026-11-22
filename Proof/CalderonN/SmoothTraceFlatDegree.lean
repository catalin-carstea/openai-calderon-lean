module

public import Proof.CalderonN.SmoothTraceSobolevCompletion
public import Proof.CalderonN.DoubleAngularPoissonEquation

import Proof.CalderonN.SmoothConormalTaylorSymmetry
import Mathlib.Tactic

/-! The flat radial trace realizes the harmonic degree and commutes with
every rotation on the actual smooth trace core. -/

public section

noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 4600000
set_option maxSynthPendingDepth 26
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE OAI.AnisotropicCalderon.SmoothSphereRotation
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

@[expose] def smoothTraceFlatDegree
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
    {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim, ConormalTaylorSolutions A ell f) :
    Module.End ℝ (SmoothSphereTrace dim) :=
  (LinearMap.fst ℝ _ _).comp ((LinearMap.snd ℝ _ _).comp (smoothSphereTaylorResponses hA hEll S))

theorem smoothTraceFlatDegree_apply
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
    {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim, ConormalTaylorSolutions A ell f) (p : SmoothData dim) :
    smoothTraceFlatDegree hA hEll S (smoothSphereTrace p) = smoothSphereTrace (S p).degree := by
  simp only [smoothTraceFlatDegree,LinearMap.comp_apply,smoothSphereTaylorResponses_apply,
    LinearMap.fst_apply,LinearMap.snd_apply]

theorem smoothTraceFlatDegree_symmetric (hn : 3 ≤ dim)
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
    {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim, ConormalTaylorSolutions A ell f) :
    SmoothTraceAdjoint hn (smoothTraceFlatDegree hA hEll S) (smoothTraceFlatDegree hA hEll S) := by
  intro x y
  obtain ⟨u,rfl⟩ := smoothSphereTraceL_surjective x
  obtain ⟨v,rfl⟩ := smoothSphereTraceL_surjective y
  let U : SmoothData dim := ⟨u.1,smoothBallData_contDiff u⟩
  let V : SmoothData dim := ⟨v.1,smoothBallData_contDiff v⟩
  let B := smoothTraceFlatDegree hA hEll S
  change ⟪smoothSphereTraceL2 hn (B (smoothSphereTrace U)),smoothSphereTraceL2 hn (smoothSphereTrace V)⟫_ℝ =
    ⟪smoothSphereTraceL2 hn (smoothSphereTrace U),smoothSphereTraceL2 hn (B (smoothSphereTrace V))⟫_ℝ
  simp only [B,smoothTraceFlatDegree_apply,smoothSphereTraceL2_apply]
  exact conormalTaylorSolutions_degree_symmetric (S U) (S V)

theorem smoothTraceFlatDegree_finite
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
    {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim, ConormalTaylorSolutions A ell f)
    (f : HarmonicFiniteCoefficients dim) :
    smoothTraceFlatDegree hA hEll S (finiteHarmonicSmoothTraceL f) =
      finiteHarmonicSmoothTraceL (finiteHarmonicDegreeL f) := by
  rw [finiteHarmonicSmoothTraceL_apply,finiteHarmonicSmoothTraceL_apply,smoothTraceFlatDegree_apply]
  let g := harmonicFiniteSmooth f
  let U := S g
  have hEq := eqOn_closedUnitBall_of_equal_ball_forcing (a:=fun _ => (1 : Mat dim)) contDiff_const
    (uniformlyEllipticOn_const_one_one (n:=Fin dim) (fixedBallOpens dim : Set (X dim)))
    (fun _ _ => rfl) U.flat g
    (fun z hz => (U.flatEquation hz).trans (negativeBallDivergence_flat_harmonicFiniteSmooth f z).symm)
    U.flatTrace
  apply (smoothSphereTrace_eq_iff _ _).mpr
  intro z hz
  exact (eqOn_radialDerivative_of_eqOn_closedUnitBall hEq hz).trans
    (congrFun (harmonicFiniteSmooth_degree_eq_radial f).symm z)

private theorem negativeBallDivergence_flat_rotation (i j : Fin dim)
    (u : SmoothData dim)
    (hu : EqOn (negativeBallDivergence (fun _ => (1 : Mat dim)) u.1) 0 (ball (0 : X dim) 1)) :
    EqOn (negativeBallDivergence (fun _ => (1 : Mat dim)) (sphereRotationDerivative i j u.1))
      0 (ball (0 : X dim) 1) := by
  intro z hz
  have hG : negativeBallDivergence (fun _ => (1 : Mat dim)) u.1 =ᶠ[𝓝 z] 0 := by
    filter_upwards [isOpen_ball.mem_nhds hz] with x hx using hu hx
  have hDer : sphereRotationDerivative i j (negativeBallDivergence (fun _ => (1 : Mat dim)) u.1) z = 0 := by
    rw [sphereRotationDerivative,hG.fderiv_eq]
    simp
  have hRot := sphereRotationDerivative_negativeBallDivergence i j (a:=fun _ => (1 : Mat dim)) contDiff_const u z
  have hA : ballRotationCoefficient i j (fun _ => (1 : Mat dim)) = 0 := by
    funext x
    simp [ballRotationCoefficient,fderiv_fun_const]
  rw [hDer,hA] at hRot
  have hZ : negativeBallDivergence (0 : X dim → Mat dim) u.1 z = 0 := by
    unfold negativeBallDivergence Elliptic.Lop
    simp [coordDeriv,Pi.zero_apply,fderiv_fun_const]
  rw [hZ,add_zero] at hRot
  exact hRot.symm

theorem smoothTraceFlatDegree_commutes_rotation
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
    {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim, ConormalTaylorSolutions A ell f)
    (i j : Fin dim) :
    let B := smoothTraceFlatDegree hA hEll S
    let K := smoothSphereTraceRotation i j
    B*K = K*B := by
  dsimp only
  ext x : 1
  obtain ⟨v,rfl⟩ := smoothSphereTraceL_surjective x
  let f : SmoothData dim := ⟨v.1,smoothBallData_contDiff v⟩
  let g : SmoothData dim := ⟨sphereRotationDerivative i j f.1,contDiff_sphereRotationDerivative i j f.1 f.2⟩
  let U := (S f).flat
  let V := (S g).flat
  let U' : SmoothData dim := ⟨sphereRotationDerivative i j U.1,contDiff_sphereRotationDerivative i j U.1 U.2⟩
  change smoothTraceFlatDegree hA hEll S (smoothSphereTraceRotation i j (smoothSphereTrace f)) =
    smoothSphereTraceRotation i j (smoothTraceFlatDegree hA hEll S (smoothSphereTrace f))
  rw [smoothSphereTraceRotation_apply,smoothTraceFlatDegree_apply,smoothTraceFlatDegree_apply,
    smoothSphereTraceRotation_apply]
  have hEq := eqOn_closedUnitBall_of_equal_ball_forcing (a:=fun _ => (1 : Mat dim)) contDiff_const
    (uniformlyEllipticOn_const_one_one (n:=Fin dim) (fixedBallOpens dim : Set (X dim)))
    (fun _ _ => rfl) V U'
    (fun z hz => ((S g).flatEquation hz).trans
      ((negativeBallDivergence_flat_rotation i j U (S f).flatEquation) hz).symm)
    (fun z hz => ((S g).flatTrace hz).trans
      ((EqOn.sphereRotationDerivative (S f).flatTrace U.2 f.2 i j) hz).symm)
  apply (smoothSphereTrace_eq_iff _ _).mpr
  intro z hz
  have hRad := eqOn_radialDerivative_of_eqOn_closedUnitBall hEq hz
  change fderiv ℝ V.1 z z = sphereRotationDerivative i j (fun x => fderiv ℝ U.1 x x) z
  exact hRad.trans (sphereRotationDerivative_comm_radial i j U.2 z).symm

end CalderonN
