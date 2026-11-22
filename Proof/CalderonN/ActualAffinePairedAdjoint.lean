module

public import Proof.CalderonN.ActualSupportedAffineRegular
public import Proof.CalderonN.SupportedSphereMultiplierFamily
public import Proof.CalderonN.SmoothSupportedTraceAdjointCalculus

import Mathlib.Tactic

/-! Adjunction for the affine density correction through its exact
flat-degree commutator formula. -/

public section

noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Elementwise InnerProductSpace Classical
set_option autoImplicit false
set_option maxHeartbeats 4200000
set_option maxSynthPendingDepth 27
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)} {d : Data dim}

private theorem pairedAdjoint_smul {V : Type*} [AddCommGroup V] [Module ℝ V]
    {B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {S T : Module.End ℝ V} (h : PairedAdjoint B S T) (c : ℝ) :
    PairedAdjoint B (c • S) (c • T) := by
  intro u v
  simp only [LinearMap.smul_apply,map_smul,h u v]

theorem exists_pairedAdjoint_actualSupportedAffine
    (hn : 3 ≤ dim) (hY : IsOpen Y) {K : ℝ} (hg : Elliptic Y K d.γ)
    (he : ∀ a,ContDiffOn ℝ ∞ (fun x => d.frame x a) Y) (hr : ContDiffOn ℝ ∞ d.radius Y)
    (hDensity : ContDiffOn ℝ ∞ (firstDensityCenterLinear d) Y)
    (μ : X dim → ℝ) (hμ : ContDiffOn ℝ ∞ μ Y)
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
    {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim, ConormalTaylorSolutions A ell f)
    (D : ∀ x ∈ Y,ActualGaussFiberData d x)
    (hF : ∀ i,SmoothSupportedTraceFiberRegular Y (actualGaussAffineFamily D i)) (i : I dim) :
    ∃ F',PairedAdjoint (smoothSupportedTracePairingL hn hY μ hμ)
      (actualSupportedAffine hY D hF i) F' := by
  let Pair := smoothSupportedTracePairingL hn hY μ hμ
  let L₀ (x : X dim) (_ : x ∈ Y) : SmoothData dim :=
    ⟨firstDensityCenterLinear d x,(firstDensityCenterLinear d x).contDiff⟩
  let M₀ (x : X dim) (_ : x ∈ Y) : SmoothData dim :=
    smoothVelocityNormal (smoothConstantVelocity (frameCoordinatesL d.γ x (d.frame x) (axis i)))
  have hL₀ : SmoothSupportedTraceFiberRegular Y (supportedSphereMultiplierFamily L₀) := by
    apply supportedSphereMultiplierFamily_regular hY
    intro x hx
    refine ⟨Y,fun p => firstDensityCenterLinear d p.1 p.2,hY,hx,Subset.rfl,?_,fun _ _ _ _ _ => rfl⟩
    exact (hDensity.comp contDiff_fst.contDiffOn (fun _ h => h.1)).clm_apply contDiff_snd.contDiffOn
  have hM₀ : SmoothSupportedTraceFiberRegular Y (supportedSphereMultiplierFamily M₀) := by
    apply supportedSphereMultiplierFamily_regular hY
    intro x hx
    refine ⟨Y,fun p => ∑ k : I dim,p.2 k*traceFrameCoordinate d.γ d.frame k i p.1,hY,hx,Subset.rfl,?_,?_⟩
    · exact ContDiffOn.sum fun k _ => ((EuclideanSpace.proj (𝕜:=ℝ) k).contDiff.comp contDiff_snd).contDiffOn.mul
        ((contDiffOn_traceFrameCoordinate hg he k i).comp contDiff_fst.contDiffOn (fun _ h => h.1))
    intro y _ hy z _
    change _ = ⟪z,frameCoordinatesL d.γ y (d.frame y) (axis i)⟫_ℝ
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [dotProduct,star_trivial,traceFrameCoordinate]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  let L := smoothSupportedTraceFiberAction hY _ hL₀
  let M := smoothSupportedTraceFiberAction hY _ hM₀
  let B := supportedFlatDegree hA hEll S hY
  let Q := (-(1/2:ℝ)) • (L+(B*L-L*B))
  let Q' := (-(1/2:ℝ)) • (L+(L*B-B*L))
  let b (x : X dim) := fderiv ℝ d.radius x (axis i)
  have hb : ContDiffOn ℝ ∞ b Y :=
    (hr.fderiv_of_isOpen (m:=∞) hY (by simp)).clm_apply contDiffOn_const
  let D₀ := smoothSupportedTraceBaseMul hY b hb
  have hL : PairedAdjoint Pair L L := pairedAdjoint_supportedFiber hn hY μ hμ _ _ hL₀ hL₀
    (fun x hx => supportedSphereMultiplierFamily_selfAdjoint hn _ x hx)
  have hM : PairedAdjoint Pair M M := pairedAdjoint_supportedFiber hn hY μ hμ _ _ hM₀ hM₀
    (fun x hx => supportedSphereMultiplierFamily_selfAdjoint hn _ x hx)
  have hB : PairedAdjoint Pair B B := pairedAdjoint_supportedFlatDegree hn hY μ hμ hA hEll S
  have hQ : PairedAdjoint Pair Q Q' :=
    pairedAdjoint_smul (hL.add ((hB.mul hL).sub (hL.mul hB))) _
  have hD : PairedAdjoint Pair D₀ D₀ := pairedAdjoint_supportedBaseMul hn hY μ hμ _ _
  have hEq : actualSupportedAffine hY D hF i = Q*M+D₀*Q := by
    ext u : 1
    apply smoothSupportedTraceSection_ext_by_fibers
    intro x hx
    simp only [Q,L,M,D₀,B,actualSupportedAffine,Module.End.mul_apply,LinearMap.add_apply,
      LinearMap.sub_apply,LinearMap.smul_apply, map_add,map_sub,map_smul,
      smoothSupportedTraceBaseMul_fiber,smoothSupportedTraceFiberAction_fiber,
      supportedSphereMultiplierFamily,dite_eq_left hx,actualGaussAffineFamily]
    rw [ActualGaussFiberData.affineCorrection_eq hn _ hA hEll S]
    simp only [ActualGaussFiberData.affineDensityMul,ActualGaussFiberData.translationMultiplier,L₀,M₀,b,
      LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,Module.End.mul_apply,
      ← smul_sub,← smul_add,smul_comm (fderiv ℝ d.radius x (axis i)) (-(1/2:ℝ))]
  rw [hEq]
  exact ⟨M*Q'+Q'*D₀,(hQ.mul hM).add (hD.mul hQ)⟩

end CalderonN
