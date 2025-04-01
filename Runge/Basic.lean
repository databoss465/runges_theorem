import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.ConnectedComponents
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Topology.Basic
import Mathlib

open Set TopologicalSpace RatFunc ContinuousMap Metric Complex Polynomial

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
-- In my hypothesis for Runge's Theorem, f is Differentiable over all of Ω, and thus over all of K. Since Γ would be within Ω \ K,
-- we shall only take the hypothesis that f is diffentaible on the closed square.
-- consider making all rectangles squares... We anyway need unions of squares

noncomputable def integral_boundary_rect {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (f : ℂ → E) (z w : ℂ) := (∫ x : ℝ in z.re..w.re, f (x + z.im * I) - ∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
  I • (∫ y : ℝ in z.im..w.im, f (w.re + y * I) - ∫ y : ℝ in z.im..w.im, f (z.re + y * I))

-- TODO: Fix this statement
lemma integral_boundary_rect_eq_circleIntegral {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (f : ℂ → E) (z w : ℂ) (s : Set ℂ) (hs : s.Countable)
    (Hc : ContinuousOn f (closedBall ((z + w) / 2) (‖z-w‖ / √2) \ {((z + w) / 2)}))
    (Hd : ∀ x ∈ (ball ((z + w) / 2) (‖z-w‖ / √2)) \ s, DifferentiableAt ℂ f x) :
      (∫ x : ℝ in z.re..w.re, ((x + z.im * I)⁻¹ • f (x + z.im * I)) -
      ∫ x : ℝ in z.re..w.re, ((x + w.im * I)⁻¹ • f (x + w.im * I))) +
      I • ∫ y : ℝ in z.im..w.im, ((w.re + y * I)⁻¹ • f (w.re + y * I)) -
      I • ∫ y : ℝ in z.im..w.im, ((z.re + y * I)⁻¹ • f (z.re + y * I)) = ∮ z in C((z + w) / 2, ‖z-w‖ / √2), f z := by sorry

variable {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (f : ℂ → E) (z : ℂ)(R : ℝ) (hR : 0 < R)
#check ∮ ζ in C(z, R), f ζ

lemma CircleIntegral_eq_integral_boundary_rect {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (f : ℂ → E) (z : ℂ)(R : ℝ) (hR : 0 < R) (Hd : DifferentiableOn ℂ f (closedBall z R)) :
    (∮ ζ in C(z, R), f ζ) = (integral_boundary_rect f (z - (R / (Real.sqrt 2)) *  (1 + I)) (z + (R / (Real.sqrt 2)) * (1 + I))) := by sorry


/--**Cauchhy's Integral Formula** for a square(?). If `f : ℂ → E` is complex differentiable on a closed square(?) with diagonal points `z` and `w`,
then for any point `a` in the interior, the integral of `(c - a)⁻¹ • f c` along the boundary evaluates to `2πI • f(a)`-/
theorem DifferentiableOn.integral_boundary_rect_sub_inv_mul {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (f : ℂ → E) (z w a : ℂ)
    (ha: a ∈ (Ioo (min z.re w.re) (max z.re w.re) ×ℂ Ioo (min z.im w.im) (max z.im w.im)))
    (Hd: DifferentiableOn ℂ f ((Icc (min z.re w.re) (max z.re w.re) ×ℂ Icc (min z.im w.im) (max z.im w.im)))) :
    integral_boundary_rect (fun c ↦ ((c - a)⁻¹ • f c)) z w = (2 * π * I) • f a := by sorry

variable (F : RatFunc ℂ)

#check F.num
#check F.denom

/-- Definitions for some Props about Rational functions, with respect to poles-/
def pole_at (z : ℂ) (F : RatFunc ℂ) : Prop := F.denom.eval z = 0 ∧ F.num.eval z ≠ 0
-- TODO: A version without the eval

def poles_in (E : Set ℂ) (F : RatFunc ℂ) : Prop := ∃ z ∈ E, pole_at z F

def no_poles_in (E : Set ℂ) (F : RatFunc ℂ) : Prop := ¬ poles_in E F

def only_poles_in (E : Set ℂ) (F : RatFunc ℂ) : Prop := poles_in E F ∧ no_poles_in (Eᶜ) F

-- If z ≠ ∞, pole_at' z F = pole_at (↑z) F
-- If z = ∞, pole_at' z F = deg F.num > deg F.denom
def pole_at' (z: (OnePoint ℂ)) (F : RatFunc ℂ) : Prop :=
    match z with
    | some z => pole_at z F
    | none => degree F.num > degree F.denom

def pole_in' (E : Set (OnePoint ℂ)) (F : RatFunc ℂ) : Prop := ∃ z ∈ E, pole_at' z F

def no_pole_in' (E : Set (OnePoint ℂ)) (F : RatFunc ℂ) : Prop := ¬ pole_in' E F

def only_poles_in' (E : Set (OnePoint ℂ)) (F : RatFunc ℂ) : Prop := pole_in' E F ∧ no_pole_in' (Eᶜ) F

-- theorem only_pole_at_infty_pol {F : RatFunc ℂ} (h : pole_at ∞ F) :



/-- Defined coercion from Set ℂ to Set (OnePoint ℂ) and backwards -/
def coe_set : Set ℂ → Set (OnePoint ℂ) := fun E ↦ {↑z | z ∈ E}
instance coe : Coe (Set ℂ) (Set (OnePoint ℂ)) := ⟨coe_set⟩

def rev_coe_set : Set (OnePoint ℂ) → Set ℂ := fun E ↦ {z | ↑z ∈ E}
instance rev_coe : Coe (Set (OnePoint ℂ)) (Set ℂ) := ⟨rev_coe_set⟩

/-
theorem separation_lemma {Ω K : Set ℂ} {f : ℂ → ℂ} (hΩ : IsOpen Ω) (hK : IsCompact K)
    (hf : ∀ x ∈ Ω, DifferentiableAt ℂ f x) : ∃ γ : Grid_Contour, (as_set γ ⊆ Ω \ K) ∧ (∀ z ∈ K,
    integral γ ((z - a)⁻¹ • f z) = 2 * π * I * f a) := by sorry

theorem approximation_lemma {K : Set ℂ} {γ : Grid_Contour} {f : ℂ → ℂ} (hK : IsCompact K)
    (hγ'₁ : bdry γ ∩ K = ∅) (hγ'₂ : ∀ z ∈ K, integral γ ((z - a)⁻¹ • f z) = 2 * π * I * f a)
    (hf' : ContinuousOn f (bdry γ)) : ∀ ε > 0, ∃ R : RatFunc ℂ, (only_poles_in' (bdry γ)) ∧
    (∀ x ∈ K, ‖f x - R.eval (RingHom.id ℂ) x‖ < ε) := by sorry
-/
