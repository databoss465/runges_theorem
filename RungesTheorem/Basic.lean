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

/-
TODO:
1. CIF_Rect : f is diff on all of Rect, value at center
2. CIF_Rect : f is diff on all of Rect, value anywhere in Rect
3. CIF_Rect : f is not diff on S, value at points not in S
Tentatively we need these. Confirm what all we actually need after proof sketch.
-/

/-- **Cauchy integral formula (Rectangle)** : if `f : ℂ → E` is continuous on a closed rectangle with its edges parallel to
coordinate axes, and diagonally opposite points at `z` and `w`, and `f` is complex differentiable at all but countably many
points of its interior, then for any `w` in this interior we have $∮_{R}(y-c)^{-1}f(y) = 2πif(c)
-/
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

-- TODO: Define grid_contour as an Inductive Type
/-
The grid_contour is the boundary of the countable union of adjacent rectangles.
Each rectangle is defined by two opposite corners, z and w.
-/
