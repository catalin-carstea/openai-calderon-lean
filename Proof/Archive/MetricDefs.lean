import Mathlib
import Proof.Archive.PrincipalDirectional

namespace OAI

noncomputable section
open MeasureTheory
open scoped ContDiff

namespace AnisotropicCalderon

 
















 
/- R3 is the identical alias already imported by the angular development. -/

 
/- MatrixField is the identical alias already imported by PrincipalDirectional. -/

 
def B : Set R3 := Metric.ball 0 1

 
def d (u : R3 → ℝ) (x : R3) : Fin 3 → ℝ :=
  fun i => fderiv ℝ u x (EuclideanSpace.single i 1)

 
def D (Φ : R3 → R3) : MatrixField :=
  fun x => Matrix.of fun i j => fderiv ℝ Φ x (EuclideanSpace.single j 1) i

 
def vol (g : MatrixField) (x : R3) : ℝ :=
  Real.sqrt (g x).det

 
def energy (g : MatrixField) (u : R3 → ℝ) : ℝ :=
  ∫ x in B, (∑ i, ∑ j, (g x)⁻¹ i j * d u x i * d u x j) * vol g x

 
def minimalEnergy (g : MatrixField) (f : R3 → ℝ) : ℝ :=
  sInf (energy g '' { u | ContDiff ℝ ∞ u ∧ ∀ x : R3, 1 ≤ ‖x‖ → u x = f x })

 

structure IsAdmissibleMetric (g : MatrixField) : Prop where
  smooth : ∀ i j, ContDiff ℝ ∞ fun x => g x i j
  posDef : ∀ x, (g x).PosDef
  euclidean_exterior : ∀ x : R3, 1 ≤ ‖x‖ → g x = 1

 

structure IsIsometryFixingExterior (Φ : R3 ≃ R3) (g₁ g₂ : MatrixField) : Prop where
  smooth : ContDiff ℝ ∞ Φ
  smooth_inv : ContDiff ℝ ∞ Φ.symm
  fixes_exterior : ∀ x : R3, 1 ≤ ‖x‖ → Φ x = x
  isometry : ∀ x : R3, g₂ x = (D Φ x).transpose * g₁ (Φ x) * D Φ x

end AnisotropicCalderon
end

end OAI
