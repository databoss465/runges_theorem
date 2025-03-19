import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.ConnectedComponents
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Topology.Basic

-- open TopologicalSpace
open Set

#check Complex
variable {U V : Set ℂ}
variable {z : ℂ}(h : z ∈ U)
#check IsOpen U
#check connectedComponentIn U z ∩ V ≠ ∅

lemma open_subset_eq_of_boundary_disjoint_and_intersects_components {U V : Set ℂ} (h₁ : IsOpen U ∧ IsOpen V) (h₂ : V ⊆ U)
    (h₃: frontier V ∩ U = ∅) (h₄: ∀ z ∈ U, connectedComponentIn U z ∩ V ≠ ∅) : U = V := by sorry

#check Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable
#check Ioo

theorem integral_boundary_rect_sub_inv_smul_of_differentiable_on_off_countable {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (f : ℂ → E) (z w a : ℂ) (s : Set ℂ) (hs : s.Countable)
    (ha: a ∈ (Ioo (min z.re w.re) (max z.re w.re) ×ℂ Ioo (min z.im w.im) (max z.im w.im)))
    (Hc : ContinuousOn f (Icc z.re w.re ×ℂ Icc z.im w.im))
    (Hd : ∀ x ∈ Ioo (min z.re w.re) (max z.re w.re) ×ℂ Ioo (min z.im w.im) (max z.im w.im) \ s,
      DifferentiableAt ℂ f x) :
      (∫ x : ℝ in z.re..w.re, ((x + z.im * I - a)⁻¹ • f (x + z.im * I)) -
      ∫ x : ℝ in z.re..w.re, ((x + w.im * I - a)⁻¹ • f (x + w.im * I))) +
      I • ∫ y : ℝ in z.im..w.im, ((w.re + y * I - a)⁻¹ • f (w.re + y * I)) -
      I • ∫ y : ℝ in z.im..w.im, ((z.re + y * I - a)⁻¹ • f (z.re + y * I)) = (2 * π * I) • f a := by sorry
