import Proof.ClassicalWeakDirichlet
import Proof.Archive.NativeSmoothBoundaryZeroClosure

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set MeasureTheory
open scoped ContDiff ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

lemma smoothSobolev_sub_mem_zero_of_boundary_eq (U V : SmoothData)
    (hBoundary : ∀ x : X,‖x‖ = 1 → U.1 x = V.1 x) :
    smoothSobolev U-smoothSobolev V ∈ TauCeti.w1p0Submodule (volume : Measure X) ballOpens 2 := by
  have hZero : ∀ x : X,‖x‖ = 1 → (U.1-V.1) x = 0 := by
    intro x hx
    simp only [Pi.sub_apply,hBoundary x hx,sub_self]
  have hh := smoothBoundaryZeroClosure_constructive ⟨U.1-V.1,U.2.sub V.2⟩ hZero
  rwa [smoothSobolev_sub] at hh

/-- The exact weak forcing of the correction to a chosen boundary extension. -/
def affineDirichletForcing {a : X → Mat}
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0)
      ⊤ ((volume : Measure X).restrict ballOpens)) (V : BallH1) : StrongDual ℝ BallH1Zero :=
  -((TauCeti.PDE.energyFormH1L (a:=a) (b:=fun _ => (0:X)) (c:=fun _ => (0:ℝ)) hcoeff V).comp
    (TauCeti.w1p0Submodule (volume : Measure X) ballOpens 2).toSubmodule.subtypeL)

lemma affineDirichletForcing_apply {a : X → Mat}
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0)
      ⊤ ((volume : Measure X).restrict ballOpens)) (V : BallH1) (v : BallH1Zero) :
    affineDirichletForcing hcoeff V v = -TauCeti.PDE.energyFormH1 a (fun _ => (0:X)) (fun _ => (0:ℝ)) V (v : BallH1) := by
  simp only [affineDirichletForcing,_root_.neg_apply,ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply,TauCeti.PDE.energyFormH1L_apply]

/-- The zero-boundary Sobolev difference selected by matching smooth traces. -/
def smoothBoundaryDifference (U V : SmoothData)
    (hBoundary : ∀ x : X,‖x‖ = 1 → U.1 x = V.1 x) : BallH1Zero :=
  ⟨smoothSobolev U-smoothSobolev V,smoothSobolev_sub_mem_zero_of_boundary_eq U V hBoundary⟩

/-- The actual weak forcing equation for the difference from a boundary extension. -/
theorem smooth_boundary_difference_equation {a : X → Mat}
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0)
      ⊤ ((volume : Measure X).restrict ballOpens))
    (U V : SmoothData) (hBoundary : ∀ x : X,‖x‖ = 1 → U.1 x = V.1 x)
    (hWeak : ∀ v : BallH1Zero,TauCeti.PDE.energyFormH1 a
      (fun _ => (0:X)) (fun _ => (0:ℝ)) (smoothSobolev U) (v : BallH1) = 0)
    (v : BallH1Zero) :
    TauCeti.PDE.energyFormH1L0 (a:=a) (b:=fun _ => (0:X)) (c:=fun _ => (0:ℝ)) hcoeff
      (smoothBoundaryDifference U V hBoundary) v = affineDirichletForcing hcoeff (smoothSobolev V) v := by
  have hWU : TauCeti.PDE.energyFormH1L (a:=a) (b:=fun _ => (0:X)) (c:=fun _ => (0:ℝ))
      hcoeff (smoothSobolev U) (v : BallH1) = 0 := by
    rw [TauCeti.PDE.energyFormH1L_apply]
    exact hWeak v
  change TauCeti.PDE.energyFormH1L (a:=a) (b:=fun _ => (0:X)) (c:=fun _ => (0:ℝ)) hcoeff
    (smoothSobolev U-smoothSobolev V) (v : BallH1) =
    -(TauCeti.PDE.energyFormH1L (a:=a) (b:=fun _ => (0:X)) (c:=fun _ => (0:ℝ)) hcoeff
      (smoothSobolev V) (v : BallH1))
  rw [map_sub,_root_.sub_apply,hWU,zero_sub]

end ShrinkingSpheres
