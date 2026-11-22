module

public import Proof.CalderonN.SmoothTraceDegreeSpectral
public import Proof.CalderonN.FiniteDoubleConormalTrace

import Proof.CalderonN.SmoothTraceRotationGraph
import Mathlib.Tactic

/-! The commutator with the spectral Casimir can be bounded using one
rotation on either test and the same genuine rotation commutators. -/

public section

noncomputable section
open scoped InnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 850000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet OAI.AnisotropicCalderon SphereHarmonic
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

private theorem comm_square_split {R : Type*} [Ring R] (k t : R) :
    k*k*t-t*(k*k) = k*(k*t-t*k)+(k*t-t*k)*k := by noncomm_ring

private theorem comm_skew_symm {R : Type*} [Ring R] (k t : R) :
    t*(-k)-(-k)*t = k*t-t*k := by simp only [mul_neg,neg_mul,sub_neg_eq_add]; abel

theorem abs_smoothTraceCasimir_comm_pair_le (hn : 3 ≤ dim)
    (B T : Module.End ℝ (SmoothSphereTrace dim))
    (hB : SmoothTraceAdjoint hn B B)
    (hFin : ∀ f, B (finiteHarmonicSmoothTraceL f) = finiteHarmonicSmoothTraceL (finiteHarmonicDegreeL f))
    (hT : SmoothTraceAdjoint hn T T) (s C : ℝ) (hC : 0 ≤ C)
    (hs : s+1/2 ≤ 2) (hns : -s+1/2 ≤ 2)
    (hRot₁ : ∀ i j u, ‖smoothSphereTraceSobolev hn (s+1/2) hs (smoothTraceAngularComm i j T u)‖ ≤
      C*‖smoothSphereTraceSobolev hn (s+1/2) hs u‖)
    (hRot₂ : ∀ i j u, ‖smoothSphereTraceSobolev hn (-s+1/2) hns (smoothTraceAngularComm i j T u)‖ ≤
      C*‖smoothSphereTraceSobolev hn (-s+1/2) hns u‖)
    (u v : SmoothSphereTrace dim) :
    let A := B*B+((dim:ℝ)-2) • B
    |⟪smoothSphereTraceL2 hn ((A*T-T*A) u),smoothSphereTraceL2 hn v⟫_ℝ| ≤
      2*(dim:ℝ)^3*C*‖smoothSphereTraceSobolev hn (s+1/2) hs u‖*
        ‖smoothSphereTraceSobolev hn (-s+1/2) hns v‖ := by
  dsimp only
  let L := smoothSphereTraceL2 (dim:=dim) hn
  let K := fun ij : Fin dim × Fin dim => smoothSphereTraceRotation ij.1 ij.2
  let P := fun ij : Fin dim × Fin dim => smoothTraceAngularComm ij.1 ij.2 T
  let U := ‖smoothSphereTraceSobolev hn (s+1/2) hs u‖
  let V := ‖smoothSphereTraceSobolev hn (-s+1/2) hns v‖
  have hAdj (ij : Fin dim × Fin dim) : SmoothTraceAdjoint hn (P ij) (P ij) := by
    have hK : SmoothTraceAdjoint hn (K ij) (-K ij) := smoothTraceRotation_skew hn _ _
    have h : SmoothTraceAdjoint hn (K ij*T-T*K ij) (T*(-K ij)-(-K ij)*T) :=
      (hK.mul hT).sub (hT.mul hK)
    change SmoothTraceAdjoint hn (K ij*T-T*K ij) (K ij*T-T*K ij)
    exact (congrArg (SmoothTraceAdjoint hn (K ij*T-T*K ij)) (comm_skew_symm (K ij) T)).mp h
  have hCasimir := smoothTraceDegree_casimir hB hFin
  have hPair (ij : Fin dim × Fin dim) :
      |⟪L ((K ij*P ij+P ij*K ij) u),L v⟫_ℝ| ≤ (4*(dim:ℝ))*C*U*V := by
    have h1 := abs_smoothTrace_inner_le_sobolev hn (s+1/2) hs (by linarith) (K ij v) (P ij u)
    have h2 := abs_smoothTrace_inner_le_sobolev hn (-s+1/2) hns (by linarith) (K ij u) (P ij v)
    have hKu : ‖smoothSphereTraceSobolev hn (-(-s+1/2)) (by linarith) (K ij u)‖ ≤
        (2*(dim:ℝ))*U := by
      have he : -(-s+1/2)+1 = s+1/2 := by ring
      have hb : -(-s+1/2)+1 ≤ 2 := he.symm ▸ hs
      have h := norm_smoothSphereTraceRotation_le hn (-(-s+1/2)) hb ij.1 ij.2 u
      rw [smoothSphereTraceSobolev_order_eq hn he hb hs] at h
      exact h
    have hKv : ‖smoothSphereTraceSobolev hn (-(s+1/2)) (by linarith) (K ij v)‖ ≤
        (2*(dim:ℝ))*V := by
      have he : -(s+1/2)+1 = -s+1/2 := by ring
      have hb : -(s+1/2)+1 ≤ 2 := he.symm ▸ hns
      have h := norm_smoothSphereTraceRotation_le hn (-(s+1/2)) hb ij.1 ij.2 v
      rw [smoothSphereTraceSobolev_order_eq hn he hb hns] at h
      exact h
    have hK : SmoothTraceAdjoint hn (K ij) (-K ij) := smoothTraceRotation_skew hn _ _
    have hSwap : ⟪L (K ij (P ij u)),L v⟫_ℝ = -⟪L (K ij v),L (P ij u)⟫_ℝ := by
      rw [hK (P ij u) v,LinearMap.neg_apply,map_neg,inner_neg_right,real_inner_comm]
    change |⟪L (K ij (P ij u)+P ij (K ij u)),L v⟫_ℝ| ≤ _
    rw [map_add,inner_add_left,hSwap,hAdj ij (K ij u) v]
    calc
      _ ≤ |⟪L (K ij v),L (P ij u)⟫_ℝ|+|⟪L (K ij u),L (P ij v)⟫_ℝ| := by
        simpa only [abs_neg] using abs_add_le (-⟪L (K ij v),L (P ij u)⟫_ℝ) ⟪L (K ij u),L (P ij v)⟫_ℝ
      _ ≤ ((2*(dim:ℝ))*V)*(C*U)+((2*(dim:ℝ))*U)*(C*V) :=
        add_le_add (h1.trans (mul_le_mul hKv (hRot₁ ij.1 ij.2 u) (norm_nonneg _) (by positivity)))
          (h2.trans (mul_le_mul hKu (hRot₂ ij.1 ij.2 v) (norm_nonneg _) (by positivity)))
      _ = _ := by ring
  have hReindex : (∑ i : Fin dim, ∑ j : Fin dim, smoothSphereTraceRotation i j*smoothSphereTraceRotation i j) =
      ∑ ij : Fin dim × Fin dim,K ij*K ij := by
    exact (Fintype.sum_prod_type (fun ij : Fin dim × Fin dim => K ij*K ij)).symm
  rw [hReindex] at hCasimir
  have hRing (ij : Fin dim × Fin dim) :
      (K ij*K ij)*T-T*(K ij*K ij) = K ij*P ij+P ij*K ij := by
    exact comm_square_split (K ij) T
  have hSum : (B*B+((dim:ℝ)-2) • B)*T-T*(B*B+((dim:ℝ)-2) • B) =
      (-1/2:ℝ) • ∑ ij : Fin dim × Fin dim,(K ij*P ij+P ij*K ij) := by
    rw [hCasimir,smul_mul_assoc,mul_smul_comm]
    let A := ∑ ij : Fin dim × Fin dim,K ij*K ij
    have hSub : (-1/2:ℝ) • (A*T)-(-1/2:ℝ) • (T*A) = (-1/2:ℝ) • (A*T-T*A) :=
      (smul_sub (-1/2:ℝ) (A*T) (T*A)).symm
    rw [hSub]
    apply congrArg ((-1/2:ℝ) • ·)
    dsimp only [A]
    rw [Finset.sum_mul,Finset.mul_sum]
    have hDiff : (∑ ij : Fin dim × Fin dim,((K ij*K ij)*T-T*(K ij*K ij))) =
        (∑ ij : Fin dim × Fin dim,(K ij*K ij)*T)-∑ ij : Fin dim × Fin dim,T*(K ij*K ij) :=
      Finset.sum_sub_distrib (s:=Finset.univ) (fun ij : Fin dim × Fin dim => (K ij*K ij)*T)
        (fun ij => T*(K ij*K ij))
    exact hDiff.symm.trans (Finset.sum_congr rfl fun ij _ => hRing ij)
  change |⟪L (((B*B+((dim:ℝ)-2) • B)*T-T*(B*B+((dim:ℝ)-2) • B)) u),L v⟫_ℝ| ≤
    2*(dim:ℝ)^3*C*U*V
  rw [hSum]
  simp only [LinearMap.smul_apply,LinearMap.sum_apply,map_smul,map_sum,
    real_inner_smul_left,sum_inner,abs_mul,show |(-1/2:ℝ)| = 1/2 by norm_num]
  calc
    _ ≤ (1/2:ℝ)*∑ ij : Fin dim × Fin dim,|⟪L ((K ij*P ij+P ij*K ij) u),L v⟫_ℝ| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by norm_num)
    _ ≤ (1/2:ℝ)*∑ _ : Fin dim × Fin dim,(4*(dim:ℝ))*C*U*V :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun ij _ => hPair ij) (by norm_num)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul]
      ring

end CalderonN
