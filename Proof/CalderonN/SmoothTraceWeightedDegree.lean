module

public import Proof.CalderonN.SmoothTraceWeightedCasimir
public import Proof.CalderonN.WeightedDegreeSylvester

import Proof.CalderonN.SmoothTraceDualOrder
import Proof.CalderonN.FiniteHarmonicPackets
import Mathlib.Tactic

/-! A weighted finite harmonic estimate for the genuine degree
commutator, extended using the smooth-core adjunction. -/

public section

noncomputable section
open scoped InnerProductSpace Classical
set_option autoImplicit false
set_option maxHeartbeats 4500000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet OAI.AnisotropicCalderon SphereHarmonic SpectralSylvester
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem smoothSphereTraceL2_finiteHarmonic (hn : 3 ≤ dim) (f : HarmonicFiniteCoefficients dim) :
    smoothSphereTraceL2 hn (finiteHarmonicSmoothTraceL f) = finiteHarmonicSphereL hn f := by
  rw [finiteHarmonicSmoothTraceL_apply,smoothSphereTraceL2_apply,finiteHarmonicSphereL_apply]

private theorem finiteHarmonicPacket_union_support_left (f g : HarmonicFiniteCoefficients dim) :
    finiteHarmonicPacket (f.support ∪ g.support) f = f := by
  conv_rhs => rw [← finiteHarmonicPacket_support f]
  unfold finiteHarmonicPacket
  symm
  apply Finset.sum_subset Finset.subset_union_left
  intro k _ hk
  rw [DFinsupp.notMem_support_iff.mp hk,map_zero]

private theorem smoothTrace_spectralComm_pair_packet (hn : 3 ≤ dim)
    (A T : Module.End ℝ (SmoothSphereTrace dim)) (hA : SmoothTraceAdjoint hn A A)
    (eigen : ℕ → ℝ) (J : Finset ℕ)
    (hEig : ∀ x : ∀ k, harmonicSphereSubspace dim k,
      A (finiteHarmonicSmoothTraceL (finiteHarmonicPacket J x)) =
        finiteHarmonicSmoothTraceL (finiteHarmonicPacket J (fun k => eigen k • x k)))
    (u v : ∀ k, harmonicSphereSubspace dim k) :
    let T₀ := (smoothSphereTraceL2 hn).comp (T.comp finiteHarmonicSmoothTraceL)
    let X := finiteHarmonicSmoothTraceL (dim:=dim)
    let L := smoothSphereTraceL2 (dim:=dim) hn
    ⟪L ((A*T-T*A) (X (finiteHarmonicPacket J u))),L (X (finiteHarmonicPacket J v))⟫_ℝ =
      ∑ m ∈ J,∑ n ∈ J,(eigen m-eigen n)*⟪physicalHarmonicBlock T₀ m n (u n),v m⟫_ℝ := by
  dsimp only
  let X := finiteHarmonicSmoothTraceL (dim:=dim)
  let L := smoothSphereTraceL2 (dim:=dim) hn
  let T₀ := L.comp (T.comp X)
  let P := finiteHarmonicPacket (dim:=dim) J
  change ⟪L (A (T (X (P u)))-T (A (X (P u)))),L (X (P v))⟫_ℝ = _
  rw [map_sub,inner_sub_left,hA (T (X (P u))) (X (P v)),hEig u,hEig v]
  have hL (x : ∀ k, harmonicSphereSubspace dim k) :
      L (X (P x)) = ∑ k ∈ J,(x k : SphereL2 dim) := by
    dsimp only [L,X,P]
    rw [smoothSphereTraceL2_finiteHarmonic,finiteHarmonicSphereL_eq_sobolev,sphereSobolevZeroEquiv_symm_packet]
  rw [hL v,hL (fun k => eigen k • v k)]
  change ⟪T₀ (P u),∑ k ∈ J,((eigen k • v k : harmonicSphereSubspace dim k) : SphereL2 dim)⟫_ℝ-
    ⟪T₀ (P (fun k => eigen k • u k)),∑ k ∈ J,(v k : SphereL2 dim)⟫_ℝ = _
  rw [← physicalHarmonicBlock_pairing,← physicalHarmonicBlock_pairing,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [map_smul]
  let b := physicalHarmonicBlock T₀ m n (u n)
  change ⟪b,eigen m • v m⟫_ℝ-⟪eigen n • b,v m⟫_ℝ = (eigen m-eigen n)*⟪b,v m⟫_ℝ
  rw [real_inner_smul_right b (v m) (eigen m),real_inner_smul_left b (v m) (eigen n)]
  ring

private theorem norm_harmonicBoundaryFiniteL_packet_weight
    (s : ℝ) (J : Finset ℕ) (u : ∀ k, harmonicSphereSubspace dim k) :
    ‖harmonicBoundaryFiniteL s (finiteHarmonicPacket J u)‖ =
      Real.sqrt (∑ k ∈ J,(1+(k:ℝ))^(2*s)*‖u k‖^2) := by
  rw [norm_finiteHarmonicPacket]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  unfold besselWeight
  have h : (((1:ℝ)+k)^s)^2 = ((1:ℝ)+k)^(2*s) := by
    rw [← Real.rpow_two,← Real.rpow_mul (by positivity : 0 ≤ (1:ℝ)+k),mul_comm s 2]
  rw [h]

/-- If the same smooth angular operator and its adjoint are symmetric,
its degree commutator has order zero on every indicated level as soon
as its rotation commutators do at the two intervening levels. -/
theorem norm_smoothTraceDegree_comm_le_of_rotation (hn : 3 ≤ dim)
    (B T : Module.End ℝ (SmoothSphereTrace dim))
    (hB : SmoothTraceAdjoint hn B B)
    (hFin : ∀ f, B (finiteHarmonicSmoothTraceL f) = finiteHarmonicSmoothTraceL (finiteHarmonicDegreeL f))
    (hT : SmoothTraceAdjoint hn T T) (s C : ℝ) (hC : 0 ≤ C)
    (hs : s+1/2 ≤ 2) (hns : -s+1/2 ≤ 2)
    (hRot₁ : ∀ i j u, ‖smoothSphereTraceSobolev hn (s+1/2) hs (smoothTraceAngularComm i j T u)‖ ≤
      C*‖smoothSphereTraceSobolev hn (s+1/2) hs u‖)
    (hRot₂ : ∀ i j u, ‖smoothSphereTraceSobolev hn (-s+1/2) hns (smoothTraceAngularComm i j T u)‖ ≤
      C*‖smoothSphereTraceSobolev hn (-s+1/2) hns u‖)
    (u : SmoothSphereTrace dim) :
    ‖smoothSphereTraceSobolev hn s (by linarith) ((B*T-T*B) u)‖ ≤
      (2*(dim:ℝ)^4*C)*‖smoothSphereTraceSobolev hn s (by linarith) u‖ := by
  let shift := ((dim:ℝ)-2)/2
  let X := finiteHarmonicSmoothTraceL (dim:=dim)
  let L := smoothSphereTraceL2 (dim:=dim) hn
  let T₀ := L.comp (T.comp X)
  let A := B*B+((dim:ℝ)-2) • B
  let C₀ := 2*(dim:ℝ)^3*C
  let C₁ := 2*(dim:ℝ)^4*C
  have hd : (3:ℝ) ≤ dim := by exact_mod_cast hn
  have hShift : (1/2:ℝ) ≤ shift := by dsimp only [shift]; linarith
  have hC₀ : 0 ≤ C₀ := by dsimp only [C₀]; positivity
  have hC₁ : 0 ≤ C₁ := by dsimp only [C₁]; positivity
  have hA : SmoothTraceAdjoint hn A A := (hB.mul hB).add (hB.const_smul _)
  have hBx (J : Finset ℕ) (x : ∀ k, harmonicSphereSubspace dim k) :
      B (X (finiteHarmonicPacket J x)) = X (finiteHarmonicPacket J (fun k => (k:ℝ) • x k)) := by
    simp only [X,hFin,finiteHarmonicDegreeL_packet]
  have hAx (J : Finset ℕ) (x : ∀ k, harmonicSphereSubspace dim k) :
      A (X (finiteHarmonicPacket J x)) =
        X (finiteHarmonicPacket J (fun k => ((k:ℝ)*((k:ℝ)+dim-2)) • x k)) := by
    simp only [A,LinearMap.add_apply,Module.End.mul_apply,LinearMap.smul_apply,hBx,smul_smul]
    simp only [finiteHarmonicPacket,map_sum,map_smul,Finset.smul_sum,← Finset.sum_add_distrib,smul_smul,
      ← add_smul]
    apply Finset.sum_congr rfl
    intro k _
    congr 1
    ring
  have hCas (J : Finset ℕ) (x y : ∀ k, harmonicSphereSubspace dim k) :
      |∑ m ∈ J,∑ n ∈ J,((((m:ℝ)+shift)^2-((n:ℝ)+shift)^2)*
        ⟪physicalHarmonicBlock T₀ m n (x n),y m⟫_ℝ)| ≤
      C₀*Real.sqrt (∑ k ∈ J,(1+(k:ℝ))^(2*(s+1/2))*‖x k‖^2)*
        Real.sqrt (∑ k ∈ J,(1+(k:ℝ))^(2*(-s+1/2))*‖y k‖^2) := by
    have h := abs_smoothTraceCasimir_comm_pair_le hn B T hB hFin hT s C hC hs hns hRot₁ hRot₂
      (X (finiteHarmonicPacket J x)) (X (finiteHarmonicPacket J y))
    dsimp only at h
    change |⟪L ((A*T-T*A) (X (finiteHarmonicPacket J x))),L (X (finiteHarmonicPacket J y))⟫_ℝ| ≤ _ at h
    rw [smoothTrace_spectralComm_pair_packet hn A T hA _ J (hAx J)] at h
    have hPoly (m n : ℕ) : ((m:ℝ)+shift)^2-((n:ℝ)+shift)^2 =
        (m:ℝ)*((m:ℝ)+dim-2)-(n:ℝ)*((n:ℝ)+dim-2) := by dsimp only [shift]; ring
    simp_rw [hPoly]
    simpa only [X,C₀,finiteHarmonicSmoothTraceL_apply,smoothSphereTraceSobolev_apply,
      smoothBoundarySobolev_harmonicFiniteSmooth,norm_harmonicBoundaryFiniteL_packet_weight] using h
  let D := B*T-T*B
  have hAdj : SmoothTraceAdjoint hn D (-D) := by
    have h := (hB.mul hT).sub (hT.mul hB)
    have e : T*B-B*T = -D := by dsimp only [D]; abel
    rwa [e] at h
  apply norm_smoothTraceOperator_le_of_finite hn s s (by linarith) (by linarith) (by linarith)
    D (-D) hAdj C₁ hC₁ _ u
  intro f
  apply norm_smoothTraceSobolev_le_of_finite_tests hn s (by linarith) (by linarith)
    (D (X f)) (C₁*‖harmonicBoundaryFiniteL s f‖) (by positivity)
  intro g
  let J := f.support ∪ g.support
  have hf : finiteHarmonicPacket J f = f := finiteHarmonicPacket_union_support_left f g
  have hg : finiteHarmonicPacket J g = g := by
    simpa only [J,Finset.union_comm] using finiteHarmonicPacket_union_support_left g f
  rw [← hf,← hg]
  rw [show ⟪L (D (X (finiteHarmonicPacket J f))),L (X (finiteHarmonicPacket J g))⟫_ℝ = _ from
    smoothTrace_spectralComm_pair_packet hn B T hB _ J (hBx J) f g]
  have hh := finite_hilbert_degree_weighted_form_bound J (physicalHarmonicBlock T₀)
    shift C₀ s hShift hC₀ (hCas J) f g
  rw [norm_harmonicBoundaryFiniteL_packet_weight,norm_harmonicBoundaryFiniteL_packet_weight]
  have hCoef : 2*C₀*(1+shift) = C₁ := by dsimp only [C₀,C₁,shift]; ring
  rwa [hCoef] at hh

end CalderonN
