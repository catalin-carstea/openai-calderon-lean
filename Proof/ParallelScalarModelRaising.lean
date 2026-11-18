import Proof.ParallelNormAssemblyReservedRaisingJets
import Proof.ParallelScalarFirstSymmetricJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

def scalarModelRaisingAdjointHigher
    (A : I → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (d : Data) (b : I) (y : X) : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  ∑ j : I,frameCoordinateLinear d.γ d.frame y j (axis b) • A j

lemma scalarModelRaisingAdjointHigher_balanced
    (A : I → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (d : Data) (b : I) (y : X)
    (hA : ∀ j : I,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (A j)=
      (flatHalfRaisingL j).adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (scalarModelRaisingAdjointHigher A d b y)=
    (framedRaisingHalfL d y (axis b)).adjoint.comp
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro u
  have hAu (j : I) := DFunLike.congr_fun (hA j) u
  simp only [ContinuousLinearMap.comp_apply] at hAu
  simp only [scalarModelRaisingAdjointHigher,framedRaisingHalfL,map_sum,map_smul,
    ContinuousLinearMap.comp_apply,_root_.sum_apply,_root_.smul_apply,hAu]

lemma scalarModelRaisingAdjoint_smooth
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (b : I) :
    ContDiffOn ℝ ∞ (fun x => (framedRaisingHalfL d x (axis b)).adjoint) Y := by
  let Adj := (ContinuousLinearMap.adjoint :
    (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) ≃ₗᵢ[ℝ]
      (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))))
  exact Adj.contDiff.comp_contDiffOn (hd.framedRaisingHalf_smooth (axis b)).1

def scalarModelSymmetricCoefficient (d : Data) (w : X → ℝ) (b : I) (y : X) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  w y • (framedRaisingHalfL d y (axis b)+(framedRaisingHalfL d y (axis b)).adjoint)

def scalarModelSymmetricHigher
    (A : I → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (d : Data) (w : X → ℝ) (b : I) (y : X) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  w y • (framedRaisingHigherL d y (axis b)+scalarModelRaisingAdjointHigher A d b y)

lemma scalarModelSymmetricCoefficient_smooth
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (w : X → ℝ)
    (hw : ContDiffOn ℝ ∞ w Y) (b : I) :
    ContDiffOn ℝ ∞ (scalarModelSymmetricCoefficient d w b) Y :=
  hw.smul (((hd.framedRaisingHalf_smooth (axis b)).1).add (scalarModelRaisingAdjoint_smooth hd b))

lemma scalarModelSymmetricHigher_balanced
    (A : I → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (d : Data) (w : X → ℝ) (b : I) (y : X)
    (hA : ∀ j : I,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (A j)=
      (flatHalfRaisingL j).adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (scalarModelSymmetricHigher A d w b y)=
      (scalarModelSymmetricCoefficient d w b y).comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) :=
  balanced_symmetric_scalar_graph _ _ _ _ _ (w y) (framedRaisingHalf_balanced d y (axis b))
    (scalarModelRaisingAdjointHigher_balanced A d b y hA)

/-- Sharp first strong-half jets of the actual scalar-weighted symmetric
background raising map. The frame derivative cancels by the imported
physical raising graph and true adjoint transfer. -/
theorem scalarModelSymmetricCoefficient_strong_jet
    {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} {K ρ c₀ floor ε A0 A1 QR QD β : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (A : I → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (w : X → ℝ) (b i : I) {y : X} (hy : y ∈ Y)
    (hA : ∀ j : I,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (A j)=
      (flatHalfRaisingL j).adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (hw : ContDiffAt ℝ ∞ w y)
    (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1) (hQR : 0 ≤ QR) (hQD : 0 ≤ QD)
    (hε : 0 ≤ ε) (hβ : 1 ≤ β)
    (hR : ‖framedRaisingHalfL d y (axis b)‖ ≤ QR)
    (hD : ‖framedRaisingFirstHalfJet d i b y‖ ≤ QD)
    (hw0 : |w y| ≤ A0*ε/β^2) (hw1 : |fderiv ℝ w y (axis i)| ≤ A1*ε/β) :
    ‖scalarModelSymmetricCoefficient d w b y‖ ≤ (2*A0*QR)*ε/β ∧
    ∃ L : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
      halfOperatorCovariantDerivativeL d (scalarModelSymmetricCoefficient d w b)
        (scalarModelSymmetricHigher A d w b) y (axis i)=
        L.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) ∧
      ‖L‖ ≤ (2*A1*QR+2*A0*QD)*ε/β := by
  let R := fun x => framedRaisingHalfL d x (axis b)
  let RH := fun x => framedRaisingHigherL d x (axis b)
  let AH := scalarModelRaisingAdjointHigher A d b
  let D := framedRaisingFirstHalfJet d i b y
  have hRS := ((hd.framedRaisingHalf_smooth (axis b)).1).contDiffAt (hY.mem_nhds hy)
  have hRAS := (scalarModelRaisingAdjoint_smooth hd b).contDiffAt (hY.mem_nhds hy)
  have hDR := framed_raising_strong_half_graph hY hΩ hd hK hy i b
  have hDA := half_covariant_adjoint_strong_extension d R RH AH hRS (axis i)
    (framedRaisingHalf_balanced d y (axis b)) (scalarModelRaisingAdjointHigher_balanced A d b y hA) D hDR
  let L := fderiv ℝ w y (axis i) • (R y+(R y).adjoint)+w y • (D+D.adjoint)
  have hN := symmetric_background_weighted_jet_norm (R y) D (w y) (fderiv ℝ w y (axis i))
    A0 A1 QR QD ε β hA0 hA1 hQR hQD hε hβ hR hD hw0 hw1
  refine ⟨hN.1,L,symmetric_weighted_half_covariant_derivative d R RH AH w y (axis i)
    hRS hRAS hw D hDR hDA,hN.2⟩

end ShrinkingSpheres.ParallelEnergy
