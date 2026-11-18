import Proof.CoarseDegreeFamilyJets
import Proof.FintypeFamilyHigherJetBound
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 30
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

lemma norm_iteratedFDeriv_coarseDegreeAssembly_le
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (F : P → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (G H : I × I → P → SphereSobolev 1 →L[ℝ] SphereSobolev 0) (p : P)
    (hF : ContDiffAt ℝ ∞ F p) (hG : ∀ ij,ContDiffAt ℝ ∞ (G ij) p)
    (hH : ∀ ij,ContDiffAt ℝ ∞ (H ij) p) (n : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hFJet : ‖iteratedFDeriv ℝ n F p‖ ≤ B)
    (hGJet : ∀ ij,‖iteratedFDeriv ℝ n (G ij) p‖ ≤ B)
    (hHJet : ∀ ij,‖iteratedFDeriv ℝ n (H ij) p‖ ≤ B) :
    ‖iteratedFDeriv ℝ n (fun x => (F x,((fun ij => G ij x),(fun ij => H ij x))) :
      P → CoarseDegreeCompatibility.CoarseDegreeData) p‖ ≤ B := by
  have hGP := contDiffAt_pi.mpr hG
  have hHP := contDiffAt_pi.mpr hH
  exact norm_iteratedFDeriv_product_family_le F _ p hF (hGP.prodMk hHP) n B hFJet
    (norm_iteratedFDeriv_product_family_le _ _ p hGP hHP n B
      (norm_iteratedFDeriv_fintype_family_le _ p hGP n B hB hGJet)
      (norm_iteratedFDeriv_fintype_family_le _ p hHP n B hB hHJet))

namespace CoarseDegreeCompatibility
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma halfFamily_physical_block (f : E → CoarseDegreeData) (V : Set E)
    (hOriginal : ∀ x ∈ V,∀ z,constraintL z (f x) = 0)
    (p : E) (hp : p ∈ V) (m n : ℕ) (z : harmonicSphereSubspace n) :
    sphereSobolevCoefficientL (-(1/2:ℝ)) m
      (halfFamily f V hOriginal p (sphereSobolevSingleL (1/2:ℝ) n z)) =
        ((m:ℝ)-(n:ℝ)) • coarsePhysicalHarmonicBlock (f p).1 m n z := by
  let x := restriction f V hOriginal p
  have hCoe : (x : CoarseDegreeData) = f p := coarseDegreeRestriction_coe_of_mem f V hOriginal p hp
  have hRad : x.1.1 = (f p).1 := congrArg (fun w : CoarseDegreeData => w.1) hCoe
  have hValue := congrArg (fun R : SphereSobolev 1 →L[ℝ] SphereSobolev 0 =>
    ((m:ℝ)-(n:ℝ)) • coarsePhysicalHarmonicBlock R m n z) hRad
  exact (halfExtractorL_physical_block x m n z).trans hValue
end CoarseDegreeCompatibility
end ShrinkingSpheres
