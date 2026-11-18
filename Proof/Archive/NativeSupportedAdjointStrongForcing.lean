import Proof.Archive.NativeH2RotationTrace
import Proof.Archive.InheritedNormedStructureData

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge

def nativeH2FirstOrderL : BallSobolev 2 →L[ℝ] BallH1 := by
  let L : BallSobolev 2 →ₗ[ℝ] BallH1 :=
    { toFun := TauCeti.Wkp.firstOrder (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) 1
      map_add' := fun U V =>
        (TauCeti.Wkp.firstOrderL (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) 1).map_add U V
      map_smul' := fun c U => by
        have hm := (TauCeti.Wkp.firstOrderL (mu := (volume : Measure R3))
          (Omega := ballOpens) (p := 2) 1).map_smul c U
        simpa only [RingHom.id_apply, TauCeti.Wkp.firstOrder,
          real_nontriviallyNormedField_normedField_eq,
          submodule_normedSpace_module_eq] using hm }
  exact L.mkContinuous 1 (fun U => by
    have hLU : L U = TauCeti.Wkp.firstOrder (mu := (volume : Measure R3))
        (Omega := ballOpens) (p := 2) 1 U := rfl
    rw [hLU, one_mul]
    exact norm_unitBall_firstOrder_le 1 U)

lemma nativeH2FirstOrderL_apply (U : BallSobolev 2) :
    nativeH2FirstOrderL U = TauCeti.Wkp.firstOrder 1 U := rfl


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
