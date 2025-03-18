import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Basic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.ConnectedComponents

-- open TopologicalSpace

#check Complex
variable {U V : Set ℂ}
variable {z : ℂ}(h : z ∈ U)
#check IsOpen U
#check connectedComponentIn U z ∩ V ≠ ∅

lemma open_subset_intersesecting_comp_eq {U V : Set ℂ} (h₁ : IsOpen U ∧ IsOpen V) (h₂ : V ⊆ U) (h₃: frontier V ∩ U = ∅)
(h₄: ∀ z ∈ U, connectedComponentIn U z ∩ V ≠ ∅) : U = V := by
  sorry
