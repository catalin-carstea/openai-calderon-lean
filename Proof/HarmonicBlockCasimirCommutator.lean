import Proof.Archive.HarmonicSphereRotationCasimirVector
import Proof.Geometry

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.SmoothSphereRotationProjection
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

/-- The finite harmonic Casimir identity for an arbitrary common operator
    block and its SAME rotation commutator blocks. -/
theorem harmonic_block_rotation_casimir_identity {m n : ℕ}
    (K : harmonicSphereSubspace n →L[ℝ] harmonicSphereSubspace m)
    (D : I × I → harmonicSphereSubspace n →L[ℝ] harmonicSphereSubspace m)
    (hD : ∀ ij : I × I,∀ z,D ij z =
      harmonicSphereRotation m ij.1 ij.2 (K z)-K (harmonicSphereRotation n ij.1 ij.2 z))
    (z : harmonicSphereSubspace n) :
    (((m:ℝ)*((m:ℝ)+1)-(n:ℝ)*((n:ℝ)+1))) • K z =
      (-(1/2:ℝ)) • ∑ ij : I × I,(harmonicSphereRotation m ij.1 ij.2 (D ij z)+
        D ij (harmonicSphereRotation n ij.1 ij.2 z)) := by
  have hSum : (∑ ij : I × I,(harmonicSphereRotation m ij.1 ij.2 (D ij z)+
      D ij (harmonicSphereRotation n ij.1 ij.2 z))) =
      (-(2:ℝ)*((m:ℝ)*((m:ℝ)+1)-(n:ℝ)*((n:ℝ)+1))) • K z := by
    calc
      _ = ∑ i : I,∑ j : I,(harmonicSphereRotation m i j (harmonicSphereRotation m i j (K z))-
          K (harmonicSphereRotation n i j (harmonicSphereRotation n i j z))) := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [hD,hD,map_sub]
        abel
      _ = (∑ i : I,∑ j : I,harmonicSphereRotation m i j (harmonicSphereRotation m i j (K z)))-
          K (∑ i : I,∑ j : I,harmonicSphereRotation n i j (harmonicSphereRotation n i j z)) := by
        simp only [map_sum,Finset.sum_sub_distrib]
      _ = (-(2*(m:ℝ)*((m:ℝ)+1))) • K z-K ((-(2*(n:ℝ)*((n:ℝ)+1))) • z) := by
        rw [sum_harmonicSphereRotation_twice,sum_harmonicSphereRotation_twice]
      _ = _ := by rw [map_smul];module
  rw [hSum,smul_smul]
  congr 1
  ring

/-- Pairing the common block identity gives the exact finite Casimir form
    used by the supplied Sylvester half-endpoint estimate. -/
theorem harmonic_block_rotation_casimir_form {m n : ℕ}
    (K : harmonicSphereSubspace n →L[ℝ] harmonicSphereSubspace m)
    (D : I × I → harmonicSphereSubspace n →L[ℝ] harmonicSphereSubspace m)
    (hD : ∀ ij : I × I,∀ z,D ij z =
      harmonicSphereRotation m ij.1 ij.2 (K z)-K (harmonicSphereRotation n ij.1 ij.2 z))
    (u : harmonicSphereSubspace n) (v : harmonicSphereSubspace m) :
    (((m:ℝ)*((m:ℝ)+1)-(n:ℝ)*((n:ℝ)+1)))*⟪K u,v⟫_ℝ =
      (1/2:ℝ)*(∑ ij : I × I,(⟪D ij u,harmonicSphereRotation m ij.1 ij.2 v⟫_ℝ-
        ⟪D ij (harmonicSphereRotation n ij.1 ij.2 u),v⟫_ℝ)) := by
  have hh := congrArg (fun z : harmonicSphereSubspace m => ⟪z,v⟫_ℝ)
    (harmonic_block_rotation_casimir_identity K D hD u)
  simp only [real_inner_smul_left,sum_inner,inner_add_left,inner_harmonicSphereRotation_skew] at hh
  have hSum : (∑ ij : I × I,(-⟪D ij u,harmonicSphereRotation m ij.1 ij.2 v⟫_ℝ+
      ⟪D ij (harmonicSphereRotation n ij.1 ij.2 u),v⟫_ℝ)) =
      -(∑ ij : I × I,(⟪D ij u,harmonicSphereRotation m ij.1 ij.2 v⟫_ℝ-
        ⟪D ij (harmonicSphereRotation n ij.1 ij.2 u),v⟫_ℝ)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro ij _
    ring
  rw [hSum] at hh
  exact hh.trans (by ring)

end ShrinkingSpheres
