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
#check IsOpen (closure U)
#check connectedComponentIn U z ∩ V ≠ ∅

/-- **Unnamed Lemma** This gives us some specific conditions under which we can assert that two open sets in ℂ
are equal. We will need this later when we have to prove the membership of (z-a)^{-1} in B(E)
 -/
lemma open_subset_eq_of_boundary_disjoint_and_intersects_components {U V : Set ℂ} (h₁ : IsOpen U ∧ IsOpen V) (h₂ : V ⊆ U)
    (h₃: frontier V ∩ U = ∅) (h₄: ∀ z ∈ U, connectedComponentIn U z ∩ V ≠ ∅) : U = V := by
    apply subset_antisymm
    · intros z hzU
      let W := connectedComponentIn U z

      -- Gives me a dichotomy of membership of W
      have h_subset : W ⊆ (W ∩ V) ∨ W ⊆ (W ∩ Vᶜ) := by

        have hWU : W ⊆ U := connectedComponentIn_subset U z

        have hW_open : IsOpen W := IsOpen.connectedComponentIn h₁.1

        have hW_conn : IsConnected W := by
            rw [isConnected_connectedComponentIn_iff]
            exact hzU

        have hW_preconn : IsPreconnected W := IsConnected.isPreconnected hW_conn

        have hW_eq : W = (W ∩ V) ∪ (W ∩ Vᶜ) := by rw [inter_union_compl W V]

        have hW_subset : W ⊆ (W ∩ V) ∪ (W ∩ Vᶜ) := (Subset.antisymm_iff.mp hW_eq).1

        have hWV_open : IsOpen (W ∩ V) := IsOpen.inter hW_open h₁.2

        have hWVc_open : IsOpen (W ∩ Vᶜ) := by

            let V' := (closure V)ᶜ
            have hWV'_open : IsOpen (W ∩ V') := by
              apply IsOpen.inter
              · exact hW_open
              · apply isOpen_compl_iff.mpr
                apply isClosed_closure

            have hWV'_eq : W ∩ Vᶜ = W ∩ V' := by
                have hV'_eq : Vᶜ = V' ∪ frontier V := by
                    simp [V']
                    rw [frontier_eq_closure_inter_closure, union_inter_distrib_left, compl_union_self]
                    rw [inter_comm, union_inter_distrib_right, inter_univ, inter_univ]
                    have hVcc_eq: closure Vᶜ = Vᶜ := by
                        apply IsClosed.closure_eq
                        apply isClosed_compl_iff.mpr
                        exact h₁.2
                    rw [hVcc_eq, union_comm]
                    have hVcc_sub : (closure V)ᶜ ⊆ Vᶜ := by
                        apply compl_subset_compl.mpr
                        exact subset_closure
                    symm
                    rw [union_eq_left]
                    exact hVcc_sub

                rw [hV'_eq, inter_comm, union_inter_distrib_right, inter_comm (frontier V)]

                have hW_frontier_empty : W ∩ frontier V = ∅ := by
                    have hW_frontier_subset : W ∩ frontier V ⊆ U ∩ frontier V:= by
                        rw [inter_comm, inter_comm U]
                        apply inter_subset_inter_right
                        exact hWU
                    rw [←subset_empty_iff, ←h₃, inter_comm (frontier V) U]
                    exact hW_frontier_subset

                rw [hW_frontier_empty, union_empty, inter_comm]

            rw [hWV'_eq]
            exact hWV'_open

        have h_disjoint : Disjoint (W ∩ V) (W ∩ Vᶜ) := by
            rw [disjoint_iff_inter_eq_empty]
            rw [inter_comm, inter_assoc, inter_comm Vᶜ, inter_assoc, inter_compl_self, inter_empty, inter_empty]

        exact IsPreconnected.subset_or_subset hWV_open hWVc_open h_disjoint (Subset.antisymm_iff.mp hW_eq).1 hW_preconn

      -- If W ⊆ W ∩ Vᶜ → W ⊆ Vᶜ → W ∩ V = ∅ (Contradiction with h₄)
      have hWV_subset : W ⊆ (W ∩ V) := by
        cases h_subset with
        | inl hl => exact hl
        | inr hr =>
            by_contra h_contra

            have h_nonempty : (W ∩ V).Nonempty := by
                apply nonempty_iff_ne_empty.mpr
                exact h₄ z hzU

            have h_empty : W ∩ V = ∅ := by
                apply subset_empty_iff.mp
                have hx : W ∩ V ⊆ W ∩ Vᶜ ∩ V := (inter_subset_inter hr (subset_refl V))
                rw [inter_assoc, compl_inter_self, inter_empty] at hx
                exact hx

            exact (nonempty_iff_ne_empty.1 h_nonempty) h_empty

      have hWV_subset' : W ⊆ V := (subset_inter_iff.mp hWV_subset).2

      have hz_in_Wz : z ∈ W := mem_connectedComponentIn hzU
      exact hWV_subset' hz_in_Wz


    · exact h₂

#check Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable

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
