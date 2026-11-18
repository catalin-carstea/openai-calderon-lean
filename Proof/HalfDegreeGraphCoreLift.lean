import Proof.HalfDegreeHigherLift
import Proof.ShiftedDegreeInclusion
noncomputable section
set_option autoImplicit false
namespace OAI.AnisotropicCalderon.SphereHarmonic.DegreeGraphLifting
open SpectralWeightedGraph SpectralCoreRegularity SphereHilbertDecomposition
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "JH" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
attribute [local irreducible] sphereSobolevInclusionL sphereSobolevBesselOrderL sphereSobolevShiftedDegreeL
lemma sphereSobolevShiftedDegreeL_add_inclusion_half :
    (sphereSobolevShiftedDegreeL (1/2 : ℝ) : Half →L[ℝ] Neg) + JH =
      sphereSobolevBesselOrderL (1/2 : ℝ) (-(1/2 : ℝ)) := by
  apply ContinuousLinearMap.ext
  intro v
  apply sphereSobolev_ext (-(1/2 : ℝ))
  intro k
  have hIndex : sphereSobolevCoefficientL (-(1/2 : ℝ)) k
      (sphereSobolevShiftedDegreeL (1/2 : ℝ) v) =
      sphereSobolevCoefficientL ((1/2 : ℝ)-1) k
        (sphereSobolevShiftedDegreeL (1/2 : ℝ) v) :=
    congrArg (fun s : ℝ => sphereSobolevCoefficientL s k
      (sphereSobolevShiftedDegreeL (1/2 : ℝ) v))
        (show (-(1/2 : ℝ)) = (1/2 : ℝ)-1 by norm_num)
  have hDegree := hIndex.trans (sphereSobolevCoefficientL_shiftedDegree (1/2 : ℝ) k v)
  have hJ := sphereSobolevCoefficientL_inclusion (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) v k
  have hBessel := sphereSobolevCoefficientL_besselOrder (1/2 : ℝ) (-(1/2 : ℝ)) v k
  have hWeight : besselWeight ((1/2 : ℝ)-(-(1/2 : ℝ))) k = 1 + (k : ℝ) := by
    rw [show (1/2 : ℝ)-(-(1/2 : ℝ)) = 1 by norm_num]
    simp only [besselWeight, Real.rpow_one]
  calc
    sphereSobolevCoefficientL (-(1/2 : ℝ)) k
        (((sphereSobolevShiftedDegreeL (1/2 : ℝ) : Half →L[ℝ] Neg) + JH) v) =
        sphereSobolevCoefficientL (-(1/2 : ℝ)) k (sphereSobolevShiftedDegreeL (1/2 : ℝ) v) +
          sphereSobolevCoefficientL (-(1/2 : ℝ)) k (JH v) :=
      (sphereSobolevCoefficientL (-(1/2 : ℝ)) k).map_add _ _
    _ = (k : ℝ) • sphereSobolevCoefficientL (1/2 : ℝ) k v +
          sphereSobolevCoefficientL (1/2 : ℝ) k v :=
      congrArg₂ (fun a b : harmonicSphereSubspace k => a+b) hDegree hJ
    _ = (1 + (k : ℝ)) • sphereSobolevCoefficientL (1/2 : ℝ) k v := by
      rw [add_smul, one_smul]
      exact add_comm _ _
    _ = sphereSobolevCoefficientL (-(1/2 : ℝ)) k
        (sphereSobolevBesselOrderL (1/2 : ℝ) (-(1/2 : ℝ)) v) :=
      (hBessel.trans (congrArg
        (fun a : ℝ => a • sphereSobolevCoefficientL (1/2 : ℝ) k v) hWeight)).symm

 
lemma inclusion_besselOrder_eq_of_half_degree_graph (v z0 : Half)
    (hDegree : (sphereSobolevShiftedDegreeL (1/2 : ℝ) v : Neg) = JH z0) :
    IH (sphereSobolevBesselOrderL (1/2 : ℝ) (3/2 : ℝ) (z0+v)) = v := by
  let Lplus : Half →L[ℝ] Neg := sphereSobolevBesselOrderL (1/2 : ℝ) (-(1/2 : ℝ))
  let Lminus : Half →L[ℝ] Hi := sphereSobolevBesselOrderL (1/2 : ℝ) (3/2 : ℝ)
  let Linverse : Neg →L[ℝ] Half := sphereSobolevBesselOrderL (-(1/2 : ℝ)) (1/2 : ℝ)
  have hAt : (sphereSobolevShiftedDegreeL (1/2 : ℝ) v : Neg) + JH v = Lplus v :=
    congrArg (fun A : Half →L[ℝ] Neg => A v)
      sphereSobolevShiftedDegreeL_add_inclusion_half
  have hSum : (sphereSobolevShiftedDegreeL (1/2 : ℝ) v : Neg) + JH v = JH (z0+v) :=
    (congrArg (fun z : Neg => z + JH v) hDegree).trans (((JH).map_add z0 v).symm)
  have hPlus : Lplus v = JH (z0+v) := hAt.symm.trans hSum
  have hTransport : (IH).comp Lminus = Linverse.comp JH :=
    sphereSobolevBesselOrderL_inclusion_comp (1/2 : ℝ) (-(1/2 : ℝ)) (3/2 : ℝ) (1/2 : ℝ)
      (by norm_num) (by norm_num) (by norm_num)
  have hTransportAt : IH (Lminus (z0+v)) = Linverse (JH (z0+v)) :=
    congrArg (fun A : Half →L[ℝ] Half => A (z0+v)) hTransport
  have hInverseAt : Linverse (Lplus v) = v :=
    congrArg (fun A : Half →L[ℝ] Half => A v)
      (sphereSobolevBesselOrderL_inverse (1/2 : ℝ) (-(1/2 : ℝ)))
  exact hTransportAt.trans ((congrArg Linverse hPlus.symm).trans hInverseAt)

 

end OAI.AnisotropicCalderon.SphereHarmonic.DegreeGraphLifting
