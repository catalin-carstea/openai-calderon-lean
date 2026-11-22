module

public import Proof.CalderonN.HarmonicRotationCasimir

import Mathlib.Tactic

/-! The block Casimir calculation from Proposition 5.3 release f308cb9d
for the arbitrary-dimensional rotation family. -/

public section

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open scoped InnerProductSpace
namespace CalderonN

open OAI.AnisotropicCalderon SphereHarmonic
variable {dim : ℕ} [NeZero dim]

/-- The finite harmonic Casimir identity for an arbitrary common operator
    block and its SAME rotation commutator blocks. -/
theorem harmonic_block_rotation_casimir_identity {m n : ℕ}
    (K : harmonicSphereSubspace dim n →ₗ[ℝ] harmonicSphereSubspace dim m)
    (D : Fin dim × Fin dim → harmonicSphereSubspace dim n →ₗ[ℝ] harmonicSphereSubspace dim m)
    (hD : ∀ ij : Fin dim × Fin dim,∀ z,D ij z =
      harmonicSphereRotation m ij.1 ij.2 (K z)-K (harmonicSphereRotation n ij.1 ij.2 z))
    (z : harmonicSphereSubspace dim n) :
    (((m:ℝ)*((m:ℝ)+dim-2)-(n:ℝ)*((n:ℝ)+dim-2))) • K z =
      (-(1/2:ℝ)) • ∑ ij : Fin dim × Fin dim,(harmonicSphereRotation m ij.1 ij.2 (D ij z)+
        D ij (harmonicSphereRotation n ij.1 ij.2 z)) := by
  have hSum : (∑ ij : Fin dim × Fin dim,(harmonicSphereRotation m ij.1 ij.2 (D ij z)+
      D ij (harmonicSphereRotation n ij.1 ij.2 z))) =
      (-(2:ℝ)*((m:ℝ)*((m:ℝ)+dim-2)-(n:ℝ)*((n:ℝ)+dim-2))) • K z := by
    calc
      _ = ∑ i : Fin dim,∑ j : Fin dim,(harmonicSphereRotation m i j (harmonicSphereRotation m i j (K z))-
          K (harmonicSphereRotation n i j (harmonicSphereRotation n i j z))) := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [hD,hD,map_sub]
        abel
      _ = (∑ i : Fin dim,∑ j : Fin dim,harmonicSphereRotation m i j (harmonicSphereRotation m i j (K z)))-
          K (∑ i : Fin dim,∑ j : Fin dim,harmonicSphereRotation n i j (harmonicSphereRotation n i j z)) := by
        simp only [map_sum,Finset.sum_sub_distrib]
      _ = (-(2*(m:ℝ)*((m:ℝ)+dim-2))) • K z-K ((-(2*(n:ℝ)*((n:ℝ)+dim-2))) • z) := by
        rw [sum_harmonicSphereRotation_twice,sum_harmonicSphereRotation_twice]
      _ = _ := by rw [map_smul];module
  rw [hSum,smul_smul]
  congr 1
  ring

/-- Pairing the common block identity gives the exact finite Casimir form
    used by the supplied Sylvester half-endpoint estimate. -/
theorem harmonic_block_rotation_casimir_form {m n : ℕ}
    (K : harmonicSphereSubspace dim n →ₗ[ℝ] harmonicSphereSubspace dim m)
    (D : Fin dim × Fin dim → harmonicSphereSubspace dim n →ₗ[ℝ] harmonicSphereSubspace dim m)
    (hD : ∀ ij : Fin dim × Fin dim,∀ z,D ij z =
      harmonicSphereRotation m ij.1 ij.2 (K z)-K (harmonicSphereRotation n ij.1 ij.2 z))
    (u : harmonicSphereSubspace dim n) (v : harmonicSphereSubspace dim m) :
    (((m:ℝ)*((m:ℝ)+dim-2)-(n:ℝ)*((n:ℝ)+dim-2)))*⟪K u,v⟫_ℝ =
      (1/2:ℝ)*(∑ ij : Fin dim × Fin dim,(⟪D ij u,harmonicSphereRotation m ij.1 ij.2 v⟫_ℝ-
        ⟪D ij (harmonicSphereRotation n ij.1 ij.2 u),v⟫_ℝ)) := by
  have hh := congrArg (fun z : harmonicSphereSubspace dim m => ⟪z,v⟫_ℝ)
    (harmonic_block_rotation_casimir_identity K D hD u)
  change ⟪(((m:ℝ)*((m:ℝ)+dim-2)-(n:ℝ)*((n:ℝ)+dim-2))) • K u,v⟫_ℝ =
    ⟪(-(1/2:ℝ)) • (∑ ij : Fin dim × Fin dim,(harmonicSphereRotation m ij.1 ij.2 (D ij u)+
        D ij (harmonicSphereRotation n ij.1 ij.2 u))),v⟫_ℝ at hh
  rw [real_inner_smul_left (K u) v _,real_inner_smul_left _ v (-(1/2:ℝ))] at hh
  simp only [sum_inner,inner_add_left,inner_harmonicSphereRotation_skew] at hh
  have hSum : (∑ ij : Fin dim × Fin dim,(-⟪D ij u,harmonicSphereRotation m ij.1 ij.2 v⟫_ℝ+
      ⟪D ij (harmonicSphereRotation n ij.1 ij.2 u),v⟫_ℝ)) =
      -(∑ ij : Fin dim × Fin dim,(⟪D ij u,harmonicSphereRotation m ij.1 ij.2 v⟫_ℝ-
        ⟪D ij (harmonicSphereRotation n ij.1 ij.2 u),v⟫_ℝ)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro ij _
    ring
  rw [hSum] at hh
  exact hh.trans (by ring)

end CalderonN
