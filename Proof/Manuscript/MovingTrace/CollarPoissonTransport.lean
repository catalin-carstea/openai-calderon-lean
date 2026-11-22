module

public import Proof.Manuscript.MovingTrace.CollarTrialSupport
public import Proof.Manuscript.MovingTrace.ComplexPoissonCorrection
public import Proof.Manuscript.MovingTrace.LiftedPhysicalResidualBound
public import Proof.Manuscript.MovingTrace.RadializedCollar
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

noncomputable section
set_option maxHeartbeats 5300000
set_option backward.isDefEq.respectTransparency false

open CalderonN CalderonPatch CalderonPatch.BoundaryLayer Set Metric Matrix
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Elementwise

namespace CalderonPaper

variable {n : ℕ} [Nontrivial (Fin (n+1))]
local notation "Z" => X (n+1)
local notation "S" => sphere (0 : Z) 1
local notation "E" => X n
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
local notation "Q" => P × E

local instance : Fact (Module.finrank ℝ Z = (n + 1) - 1 + 1) :=
  ⟨by rw [finrank_euclideanSpace_fin]; omega⟩

/-- A fixed signed normal collar for one stereographic chart of the
normalized ball. The upper depth bound keeps the angular chart regular. -/
structure SignedPoissonCollar (G : BallPoissonTube P (n+1)) where
  pole : ↥S
  δ : ℝ
  pos : 0 < δ
  small : δ ≤ 1/16
  contains : G.V ×ˢ closedBall (0 : Z) (1+δ) ⊆ G.U
  mixed : ∀ p ∈ G.V, ∀ x (t : ℝ), t ∈ Ioo (-δ) (3*δ) → ∀ j : I n,
    pullbackMetric (fun z => G.g (p,z)) (signedSphericalCollar pole)
      (signedLayerCoordinates (x,t)) 0 j.succ = 0

namespace SignedPoissonCollar

variable {G : BallPoissonTube P (n+1)} (C : SignedPoissonCollar G)

def baseDomain (G : BallPoissonTube P (n+1)) : Set (Q × E) :=
  (G.V ×ˢ ({0}ᶜ : Set E)) ×ˢ univ

def collarDomain : Set ((Q × E) × ℝ) :=
  ((G.V ×ˢ (univ : Set E)) ×ˢ (univ : Set E)) ×ˢ Ioo (-C.δ) (3*C.δ)

theorem baseDomain_open : IsOpen (baseDomain G) :=
  (G.openV.prod isOpen_compl_singleton).prod isOpen_univ

theorem collarDomain_open : IsOpen C.collarDomain :=
  ((G.openV.prod isOpen_univ).prod isOpen_univ).prod isOpen_Ioo

theorem baseFace : MapsTo (fun p : Q × E => (p,(0:ℝ))) (baseDomain G) C.collarDomain := by
  intro q hq
  exact ⟨⟨⟨hq.1.1,mem_univ _⟩,mem_univ _⟩,⟨by linarith [C.pos],by linarith [C.pos]⟩⟩

def metric (G : BallPoissonTube P (n+1)) (v : ↥S) (p : Q) : MetricField (n+1) :=
  pullbackMetric (fun z => G.g (p.1,z)) (signedSphericalCollar v)

theorem physical_mem {q : (Q × E) × ℝ} (hq : q ∈ C.collarDomain) :
    (q.1.1.1,polarCollar (angularPoint C.pole) (q.1.2,q.2)) ∈ G.U := by
  have hq₁ : q.2 < 1 := hq.2.2.trans (by linarith [C.small])
  apply C.contains
  refine ⟨hq.1.1.1,?_⟩
  rw [Metric.mem_closedBall,dist_zero_right,polarCollar_norm C.pole q.1.2 hq₁.le]
  linarith [hq.2.1]

theorem metric_posDef {q : (Q × E) × ℝ} (hq : q ∈ C.collarDomain) :
    (metric G C.pole q.1.1 (signedLayerCoordinates (q.1.2,q.2))).PosDef := by
  let r := signedLayerCoordinates (q.1.2,q.2)
  have hq₁ : q.2 < 1 := hq.2.2.trans (by linarith [C.small])
  have hB := signedSphericalCollar_derivative_bijective C.pole r
    (by simpa only [r,signedLayerCoordinates.symm_apply_apply] using hq₁)
  have hDet := coordinateJacobian_det_ne_zero hB
  change ((coordinateJacobian (signedSphericalCollar C.pole) r)ᵀ *
    G.g (q.1.1.1,signedSphericalCollar C.pole r) *
    coordinateJacobian (signedSphericalCollar C.pole) r).PosDef
  rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
  have hg := G.posG _ (C.physical_mem hq)
  exact hg.conjTranspose_mul_mul_same
    (Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hDet)))

def tangential (G : BallPoissonTube P (n+1)) (v : ↥S) (q : (Q × E) × ℝ) : Mat n :=
  collarTangential (metric G v q.1.1) (q.1.2,q.2)

def normalDrift (G : BallPoissonTube P (n+1)) (v : ↥S) (q : (Q × E) × ℝ) : ℝ :=
  collarNormalDrift (metric G v q.1.1) (q.1.2,q.2)

def tangentialDrift (G : BallPoissonTube P (n+1)) (v : ↥S) (q : (Q × E) × ℝ) (i : I n) : ℝ :=
  collarTangentDrift (metric G v q.1.1) (q.1.2,q.2) i

theorem split_smooth :
    (∀ i j, ContDiffOn ℝ ∞ (fun q => tangential G C.pole q i j) C.collarDomain) ∧
    ContDiffOn ℝ ∞ (normalDrift G C.pole) C.collarDomain ∧
    ∀ i, ContDiffOn ℝ ∞ (fun q => tangentialDrift G C.pole q i) C.collarDomain := by
  let F (q : Q × Z) := (q.1.1,signedSphericalCollar C.pole q.2)
  let W := F ⁻¹' G.U ∩ {q : Q × Z | ((signedLayerCoordinates.symm q.2).2) < 1}
  have hF : ContDiff ℝ ∞ F := contDiff_fst.fst.prodMk
    ((signedSphericalCollar_contDiff C.pole).comp contDiff_snd)
  have hW : IsOpen W := (G.openU.preimage hF.continuous).inter
    (isOpen_lt (continuous_snd.comp (signedLayerCoordinates.symm.continuous.comp continuous_snd))
      continuous_const)
  let m (q : Q × Z) := metric G C.pole q.1 q.2
  have hm (i j : I (n+1)) : ContDiffOn ℝ ∞ (fun q => m q i j) W := by
    have hg (k l : I (n+1)) : ContDiffOn ℝ ∞ (fun q => G.g (F q) k l) W :=
      (G.smoothG k l).comp hF.contDiffOn (fun q hq => hq.1)
    have hd (k l : I (n+1)) : ContDiffOn ℝ ∞
        (fun q : Q × Z => coordinateJacobian (signedSphericalCollar C.pole) q.2 k l) W :=
      ((contDiff_coordinateJacobian_entry _ (signedSphericalCollar_contDiff C.pole) k l).comp
        contDiff_snd).contDiffOn
    simp only [m,metric,pullbackMetric,Matrix.mul_apply,Matrix.transpose_apply]
    exact ContDiffOn.sum fun l _ => (ContDiffOn.sum fun k _ => (hd k i).mul (hg k l)).mul (hd l j)
  have hPos (q : Q × Z) (hq : q ∈ W) : (m q).PosDef := by
    have hB := signedSphericalCollar_derivative_bijective C.pole q.2 hq.2
    have hDet := coordinateJacobian_det_ne_zero hB
    change ((coordinateJacobian (signedSphericalCollar C.pole) q.2)ᵀ * G.g (F q) *
      coordinateJacobian (signedSphericalCollar C.pole) q.2).PosDef
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
    exact (G.posG _ hq.1).conjTranspose_mul_mul_same
      (Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hDet)))
  obtain ⟨hA,hτ,hb⟩ := collarNormalizedSplit_contDiffOn hW hm hPos
  have hsub : ∀ q ∈ C.collarDomain, (q.1.1,signedLayerCoordinates (q.1.2,q.2)) ∈ W := by
    intro q hq
    refine ⟨C.physical_mem hq,?_⟩
    have ht : q.2 < 1 := hq.2.2.trans (by linarith [C.small])
    change (signedLayerCoordinates.symm (signedLayerCoordinates (q.1.2,q.2))).2 < 1
    simpa only [signedLayerCoordinates.symm_apply_apply] using ht
  exact ⟨fun i j => (hA i j).mono hsub,(hτ.mono hsub),fun i => (hb i).mono hsub⟩

def covector (p : Q) : E := (2*Real.pi) • p.2

theorem covector_contDiff : ContDiff ℝ ∞ (covector : Q → E) :=
  contDiff_const (c := 2*Real.pi) |>.smul contDiff_snd

theorem covector_ne_zero {q : Q × E} (hq : q ∈ baseDomain G) : covector q.1 ≠ 0 :=
  smul_ne_zero (by positivity : 2 * Real.pi ≠ 0) hq.1.2

def coefficients : ParametricLayerCoefficients (n := n) (baseDomain G) :=
  splitOperatorLayerCoefficients C.collarDomain_open C.baseFace
    (tangential G C.pole) C.split_smooth.1
    (fun q hq => collarTangential_symm (C.metric_posDef hq))
    (fun q hq => collarTangential_posDef (C.metric_posDef (C.baseFace hq)))
    (normalDrift G C.pole) C.split_smooth.2.1
    (tangentialDrift G C.pole) C.split_smooth.2.2 covector covector_contDiff
    (fun q hq => covector_ne_zero hq)

theorem planePhase_covector_eq (p : Q) (x : E) :
    ParametricLayerCoefficients.planePhase covector (p,x) = 2 * Real.pi * ⟪x,p.2⟫_ℝ := by
  unfold ParametricLayerCoefficients.planePhase covector
  rw [PiLp.inner_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [PiLp.smul_apply,smul_eq_mul,RCLike.inner_apply,starRingEnd_apply,star_trivial]
  ring

end SignedPoissonCollar
end CalderonPaper
