import Proof.Archive.FixedDirichletRegularity

set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ENNReal ContDiff Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge

 
def fixedDirichletRegularityConstant (hreg : FixedDirichletRegularity) :=
  fun s a lam Lam hsmooth hell hcoeff =>
    Classical.choose (hreg s a lam Lam hsmooth hell hcoeff)

 
def fixedDirichletRegularityLift (hreg : FixedDirichletRegularity) :=
  fun s a lam Lam hsmooth hell hcoeff f u hu =>
    Classical.choose ((Classical.choose_spec (hreg s a lam Lam hsmooth hell hcoeff)).2 f u hu)

 
def fixedDirichletRegularityLift_spec (hreg : FixedDirichletRegularity) :=
  fun s a lam Lam hsmooth hell hcoeff f u hu =>
    Classical.choose_spec
      ((Classical.choose_spec (hreg s a lam Lam hsmooth hell hcoeff)).2 f u hu)

 
def fixedDirichletRegularityLift_mem (hreg : FixedDirichletRegularity) :=
  fun s a lam Lam hsmooth hell hcoeff f u hu =>
    (mem_strongDirichletSubmodule s
      (fixedDirichletRegularityLift hreg s a lam Lam hsmooth hell hcoeff f u hu)).mpr
      ((fixedDirichletRegularityLift_spec hreg s a lam Lam hsmooth hell hcoeff f u hu).1.symm
        ▸ u.2)

 
def fixedStrongDirichletRegularityLift (hreg : FixedDirichletRegularity) :=
  fun s a lam Lam hsmooth hell hcoeff f u hu =>
    (⟨fixedDirichletRegularityLift hreg s a lam Lam hsmooth hell hcoeff f u hu,
      fixedDirichletRegularityLift_mem hreg s a lam Lam hsmooth hell hcoeff f u hu⟩ :
      StrongDirichletSpace s)

end OAI.AnisotropicCalderon.DirichletFamily
