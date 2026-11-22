module

public import Proof.CalderonN.FiniteHilbertDegreeSylvester
public import Proof.CalderonN.FiniteHarmonicPackets
public import Proof.CalderonN.HarmonicBlockCasimirForm

import Mathlib.Tactic

/-! Finite spectral comparison of an operator and the commutators of
the same physical operator with all sphere rotations. -/

public section

set_option autoImplicit false
set_option maxHeartbeats 3200000
noncomputable section
open scoped InnerProductSpace DirectSum Classical
namespace CalderonN

open OAI.AnisotropicCalderon SphereHarmonic SpectralSylvester

variable {dim : ℕ} [NeZero dim]

@[expose] def physicalHarmonicBlock (T : HarmonicFiniteCoefficients dim →ₗ[ℝ] SphereL2 dim) (m n : ℕ) :
    harmonicSphereSubspace dim n →ₗ[ℝ] harmonicSphereSubspace dim m :=
  (harmonicProjection m).toLinearMap.comp
    (T.comp (DirectSum.lof ℝ ℕ (fun k => ↥(harmonicSphereSubspace dim k)) n))

theorem physicalHarmonicBlock_pairing
    (T : HarmonicFiniteCoefficients dim →ₗ[ℝ] SphereL2 dim)
    (s t : Finset ℕ) (u v : ∀ k, harmonicSphereSubspace dim k) :
    (∑ m ∈ t,∑ n ∈ s, ⟪physicalHarmonicBlock T m n (u n),v m⟫_ℝ) =
      ⟪T (finiteHarmonicPacket s u), ∑ m ∈ t, (v m : SphereL2 dim)⟫_ℝ := by
  symm
  rw [inner_sum]
  apply Finset.sum_congr rfl
  intro m _
  simp only [finiteHarmonicPacket,map_sum,sum_inner,physicalHarmonicBlock,LinearMap.comp_apply,
    ContinuousLinearMap.coe_coe,harmonicProjection_inner]

private theorem abs_finite_physical_casimir_le (hn : 3 ≤ dim)
    (T : HarmonicFiniteCoefficients dim →ₗ[ℝ] SphereL2 dim)
    (P Q : Fin dim × Fin dim → HarmonicFiniteCoefficients dim →ₗ[ℝ] SphereL2 dim)
    (MP MQ : ℝ) (hMP : 0 ≤ MP) (hMQ : 0 ≤ MQ)
    (hP : ∀ ij f, ‖P ij f‖ ≤ MP*‖harmonicBoundaryFiniteL 1 f‖)
    (hQ : ∀ ij f, ‖Q ij f‖ ≤ MQ*‖harmonicBoundaryFiniteL 1 f‖)
    (hDual : ∀ ij, ∀ f g : HarmonicFiniteCoefficients dim,
      ⟪P ij f,(sphereSobolevZeroEquiv (dim:=dim)).symm (harmonicBoundaryFiniteL 0 g)⟫_ℝ =
      ⟪(sphereSobolevZeroEquiv (dim:=dim)).symm (harmonicBoundaryFiniteL 0 f),Q ij g⟫_ℝ)
    (hGraph : ∀ ij m n z,
      physicalHarmonicBlock (P ij) m n z =
        harmonicSphereRotation m ij.1 ij.2 (physicalHarmonicBlock T m n z)-
        physicalHarmonicBlock T m n (harmonicSphereRotation n ij.1 ij.2 z))
    (s : Finset ℕ) (u v : ∀ k, harmonicSphereSubspace dim k) :
    |∑ m ∈ s,∑ n ∈ s,
      (((m:ℝ)*((m:ℝ)+dim-2)-(n:ℝ)*((n:ℝ)+dim-2))*⟪physicalHarmonicBlock T m n (u n),v m⟫_ℝ)| ≤
      (dim:ℝ)^3*(MP+MQ)*‖harmonicBoundaryFiniteL 1 (finiteHarmonicPacket s u)‖*
        ‖harmonicBoundaryFiniteL 1 (finiteHarmonicPacket s v)‖ := by
  let F := fun m n (ij : Fin dim × Fin dim) =>
    ⟪physicalHarmonicBlock (P ij) m n (u n), harmonicSphereRotation m ij.1 ij.2 (v m)⟫_ℝ -
    ⟪physicalHarmonicBlock (P ij) m n (harmonicSphereRotation n ij.1 ij.2 (u n)),v m⟫_ℝ
  let H (w : ∀ k, harmonicSphereSubspace dim k) := ‖harmonicBoundaryFiniteL 1 (finiteHarmonicPacket s w)‖
  have hReorder : (∑ m ∈ s,∑ n ∈ s,∑ ij : Fin dim × Fin dim,F m n ij) =
      ∑ ij : Fin dim × Fin dim,∑ m ∈ s,∑ n ∈ s,F m n ij := by
    calc
      _ = ∑ m ∈ s,∑ ij : Fin dim × Fin dim,∑ n ∈ s,F m n ij :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  have hEq :
      (∑ m ∈ s,∑ n ∈ s,
        (((m:ℝ)*((m:ℝ)+dim-2)-(n:ℝ)*((n:ℝ)+dim-2))*⟪physicalHarmonicBlock T m n (u n),v m⟫_ℝ)) =
        (1/2:ℝ)*(∑ ij : Fin dim × Fin dim,∑ m ∈ s,∑ n ∈ s,F m n ij) := by
    rw [← hReorder]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    apply Finset.sum_congr rfl
    intro n _
    simpa only [Finset.mul_sum,F] using harmonic_block_rotation_casimir_form
      (physicalHarmonicBlock T m n) (fun ij => physicalHarmonicBlock (P ij) m n)
      (fun ij z => hGraph ij m n z) (u n) (v m)
  have hb (ij : Fin dim × Fin dim) : |∑ m ∈ s,∑ n ∈ s,F m n ij| ≤
      (2*(dim:ℝ))*(MP+MQ)*H u*H v := by
    let rot (w : ∀ k, harmonicSphereSubspace dim k) k := harmonicSphereRotation k ij.1 ij.2 (w k)
    have hAdj : ⟪P ij (finiteHarmonicPacket s (rot u)),∑ k ∈ s, (v k : SphereL2 dim)⟫_ℝ =
      ⟪∑ k ∈ s, (rot u k : SphereL2 dim),Q ij (finiteHarmonicPacket s v)⟫_ℝ := by
      rw [← sphereSobolevZeroEquiv_symm_packet,← sphereSobolevZeroEquiv_symm_packet,hDual]
    dsimp only [F]
    simp only [Finset.sum_sub_distrib]
    rw [physicalHarmonicBlock_pairing,physicalHarmonicBlock_pairing]
    change |⟪P ij (finiteHarmonicPacket s u),∑ k ∈ s, (rot v k : SphereL2 dim)⟫_ℝ-
      ⟪P ij (finiteHarmonicPacket s (rot u)),∑ k ∈ s, (v k : SphereL2 dim)⟫_ℝ| ≤ _
    rw [hAdj]
    have hu := norm_finiteRotation_L2_le hn ij.1 ij.2 s u
    have hv := norm_finiteRotation_L2_le hn ij.1 ij.2 s v
    calc
      _ ≤ _ := abs_sub _ _
      _ ≤ ‖P ij (finiteHarmonicPacket s u)‖*‖∑ k ∈ s,(rot v k : SphereL2 dim)‖+
          ‖∑ k ∈ s,(rot u k : SphereL2 dim)‖*‖Q ij (finiteHarmonicPacket s v)‖ :=
        add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
      _ ≤ (MP*H u)*((2*(dim:ℝ))*H v)+((2*(dim:ℝ))*H u)*(MQ*H v) :=
        add_le_add (mul_le_mul (hP _ _) hv (norm_nonneg _) (by dsimp [H]; positivity))
          (mul_le_mul hu (hQ _ _) (norm_nonneg _) (by dsimp [H]; positivity))
      _ = _ := by ring
  rw [hEq,abs_mul,abs_of_pos (by norm_num : 0 < (1/2 : ℝ))]
  calc
    _ ≤ (1/2:ℝ)*∑ ij : Fin dim × Fin dim,|∑ m ∈ s,∑ n ∈ s,F m n ij| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by norm_num)
    _ ≤ (1/2:ℝ)*∑ _ : Fin dim × Fin dim,(2*(dim:ℝ))*(MP+MQ)*H u*H v :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun ij _ => hb ij) (by norm_num)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,
        nsmul_eq_mul,Nat.cast_mul]; ring

/-- A midpoint rotation bound and its genuine dual bound yield a
balanced half-order bound for the degree commutator. -/
theorem abs_finite_physical_degree_form_le (hn : 3 ≤ dim)
    (T : HarmonicFiniteCoefficients dim →ₗ[ℝ] SphereL2 dim)
    (P Q : Fin dim × Fin dim → HarmonicFiniteCoefficients dim →ₗ[ℝ] SphereL2 dim)
    (MP MQ : ℝ) (hMP : 0 ≤ MP) (hMQ : 0 ≤ MQ)
    (hP : ∀ ij f, ‖P ij f‖ ≤ MP*‖harmonicBoundaryFiniteL 1 f‖)
    (hQ : ∀ ij f, ‖Q ij f‖ ≤ MQ*‖harmonicBoundaryFiniteL 1 f‖)
    (hDual : ∀ ij, ∀ f g : HarmonicFiniteCoefficients dim,
      ⟪P ij f,(sphereSobolevZeroEquiv (dim:=dim)).symm (harmonicBoundaryFiniteL 0 g)⟫_ℝ =
      ⟪(sphereSobolevZeroEquiv (dim:=dim)).symm (harmonicBoundaryFiniteL 0 f),Q ij g⟫_ℝ)
    (hGraph : ∀ ij m n z,
      physicalHarmonicBlock (P ij) m n z =
        harmonicSphereRotation m ij.1 ij.2 (physicalHarmonicBlock T m n z)-
        physicalHarmonicBlock T m n (harmonicSphereRotation n ij.1 ij.2 z))
    (s : Finset ℕ) (u v : ∀ k, harmonicSphereSubspace dim k) :
    |∑ m ∈ s,∑ n ∈ s, ((m:ℝ)-(n:ℝ))*⟪physicalHarmonicBlock T m n (u n),v m⟫_ℝ| ≤
      (dim:ℝ)^4*(MP+MQ)*‖harmonicBoundaryFiniteL (1/2:ℝ) (finiteHarmonicPacket s u)‖*
        ‖harmonicBoundaryFiniteL (1/2:ℝ) (finiteHarmonicPacket s v)‖ := by
  let shift := ((dim:ℝ)-2)/2
  let C := (dim:ℝ)^3*(MP+MQ)
  have hd : (3 : ℝ) ≤ dim := by exact_mod_cast hn
  have hs : (1/2:ℝ) ≤ shift := by dsimp [shift]; linarith
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hForm (x y : ∀ k, harmonicSphereSubspace dim k) :
      |∑ m ∈ s,∑ n ∈ s, (((m:ℝ)+shift)^2-((n:ℝ)+shift)^2)*
        ⟪physicalHarmonicBlock T m n (x n),y m⟫_ℝ| ≤
        C*Real.sqrt (∑ k ∈ s, (1+(k:ℝ))^2*‖x k‖^2)*
          Real.sqrt (∑ k ∈ s, (1+(k:ℝ))^2*‖y k‖^2) := by
    have hh := abs_finite_physical_casimir_le hn T P Q MP MQ hMP hMQ hP hQ hDual hGraph s x y
    simp only [norm_finiteHarmonicPacket,besselWeight,Real.rpow_one] at hh
    convert hh using 2
    apply Finset.sum_congr rfl
    intro m _
    apply Finset.sum_congr rfl
    intro n _
    congr 1
    dsimp [shift]
    ring
  have hh := finite_hilbert_degree_half_form_bound s (physicalHarmonicBlock T) shift C hs hC hForm u v
  rw [norm_finiteHarmonicPacket,norm_finiteHarmonicPacket]
  simp_rw [besselWeight_one_half_sq]
  convert hh using 1
  dsimp [shift,C]
  ring

end CalderonN
