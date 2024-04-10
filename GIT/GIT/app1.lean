import Mathlib.Tactic

/-!
# Appendix 1: Axioms and basic results of hereditarily finite set theory

In this file, Appendix 1 of S. Swierczkowski: 'Finite Sets and Gödel’s Incompleteness Theorems' is formalised.
It presents the axioms and basic results of hereditarily finite set theory.

## Main results

- `exten_prop`: Extensionality property.
- `exists_union`: Existence of the union of two sets.
- `exists_union_set`: Existence of the union of a set of sets.
- `comp_scheme`: Comprehension scheme.
- `repl_scheme`: Replacement scheme.
- `exists_power`: Existence of the power set.
- `found_prop`: Foundation property.

## Notation

- `◁` : enlarging, see `HF.enlarge`.

## References

S. Swierczkowski. Finite Sets and Gödel’s Incompleteness Theorems. Dissertationes
mathematicae. IM PAN, 2003. URL https://books.google.co.uk/books?id=5BQZAQAAIAAJ.
-/

universe u

/-- Define the non-logical symbols of HF which are: -/

class HFprior (s : Type u) where
  /-- empty set: constant symbol -/
  emptyset : s
  /-- membership: 2-ary relation symbol -/
  mem : s → s → Prop
  /-- enlarging: 2-ary operation symbol -/
  enlarging : s → s → s

/-- Write ∅ instead of empty -/
instance (s) [HFprior s] : EmptyCollection s := ⟨HFprior.emptyset⟩

/-- Write ∈ instead of mem -/
instance (s) [HFprior s] : Membership s s := ⟨HFprior.mem⟩

/-- Write ◁ instead of enlarge -/
infixl:90 " ◁ " => HFprior.enlarging

/-- Define the axioms -/
class HF (s : Type u) extends HFprior s where
  empty (z : s) : z = ∅ ↔ ∀ x, x ∉ z
  enlarge (x y z : s) : z = x ◁ y ↔ ∀ u, u ∈ z ↔ u ∈ x ∨ u = y
  induction (P : s → Prop) (base : P ∅) (step : ∀ x y, P x → P y → P (x ◁ y)) (z : s) : P z

attribute [elab_as_elim] HF.induction

variable {S : Type u} [HF S]       -- Now x : S means x is a HF set

namespace HF

-- Theorem 1.1

theorem set_notin_empty (x : S) : x ∉ (∅ : S) := by
  have h := HF.empty (∅ : S)  -- substitute ∅ for z in HF1
  simp at h  -- simplify as ∅ = ∅
  specialize h x -- substitute x in h
  exact h

@[simp] theorem enlarge_iff (u x y : S) : u ∈ x ◁ y ↔ u ∈ x ∨ u = y := by
  have h := HF.enlarge x y (x ◁ y)  -- substitute x ◁ y for z in HF2
  simp at h  -- simplify as x ◁ y = x ◁ y
  specialize h u  -- substitute u in h
  exact h

theorem enlarge_empty (z y : S) : z ∈ ∅ ◁ y ↔ z = y := by
  have h1b := enlarge_iff z (∅ : S) y  -- substitute ∅ for x in Theorem 1.1 (b)
  have h1a := set_notin_empty z  -- substitute z for x in Theorem 1.1 (a)
  rw [h1b]  -- substitute h1b
  constructor  -- split the iff
  · intro h
    cases' h with h1 h2  -- both hypotheses h1 and h2 imply the goal
    · apply h1a at h1  -- h1a and h1 contradict
      exfalso; exact h1
    · exact h2
  · intro h  -- this case is trivial
    right; exact h


-- Theorem 1.2 (Extensionality Property)

theorem exten_prop (z : S) : ∀ x, x = z ↔ ∀ u, u ∈ x ↔ u ∈ z := by
  apply HF.induction  -- use HF3, i.e. start a proof by induction on the 'size' of the set x
  -- base case: x = ∅
  · constructor  -- split iff
    · intro h
      rw [h]  -- to obtain u ∈ z ↔ u ∈ z in goal
      simp
    · intro h
      have hHF1 : ∀ u, u ∉ z := by  -- have the RHS of HF1 which is equivalent to z = ∅
        intro u  -- pick u arbitrarily
        specialize h u  -- substitute u in h
        intro huz  -- u ∉ z is equivalent to u ∈ z → False
        rw [← h] at huz  -- change hu to u ∈ ∅
        have h1a := set_notin_empty u  -- substitute u for x in Theorem 1.1 (a) which leads to contradiction
        apply h1a; exact huz
      rw [← HF.empty z] at hHF1  -- change the RHS of HF1 to the LHS
      rw [hHF1]
  -- inductive step: if exten_prop(x) and exten_prop(y), then exten_prop(x ◁ y)
  · intros x y _ _  -- pick x and y arbitrarily
    constructor  -- split iff
    · intro h
      rw [h]  -- to obtain u ∈ z ↔ u ∈ z in goal
      simp
    · intro h
      have hHF2 : ∀ u, u ∈ z ↔ u ∈ x ∨ u = y := by  -- have the RHS of HF2 which is equivalent to z = x ◁ y
        intro u  -- pick u arbitrarily
        specialize h u  -- substitute u in h
        rw [← h]  -- substitute h; goal now equals Theorem 1.1 (b)
        exact enlarge_iff u x y
      rw [← HF.enlarge x y z] at hHF2  -- change the RHS of HF2 to the LHS
      rw [hHF2]


-- Definition 1.3

/-- {x} = ∅ ◁ x -/
def single (x : S) : S := ∅ ◁ x
/-- {x,y} = {x} ◁ y -/
def pair (x y : S) : S := (single x) ◁ y
/-- {x,y,z} = {x,y} ◁ z -/
def triple (x y z : S) : S := (pair x y) ◁ z
/-- ⟨x,y⟩ = {{x},{x,y}} -/
def ord_pair (x y : S) : S := pair (single x) (pair x y)


-- Theorem 1.4

theorem single_iff (u x : S) : u ∈ single x ↔ u = x := by
  rw [single]  -- use definition of {x}
  exact enlarge_empty u x  -- Theorem 1.1 (c)

theorem pair_iff (u x y : S) : u ∈ pair x y ↔ u = x ∨ u = y := by
  rw [pair]  -- use definition of {x,y}
  rw [enlarge_iff u (single x) y]  -- use Theorem 1.1 (b)
  rw [single_iff u x]  -- use Theorem 1.4 (a)

theorem double_pair (x : S) : pair x x = single x := by
  rw [exten_prop (single x)]  -- use Theorem 1.2
  intro u  -- pick u arbitrarily
  rw [pair_iff u x x]; simp  -- use Theorem 1.4 (b) and simplify
  rw [single_iff u x]  -- use Theorem 1.4 (a)


lemma single_equal (x y : S) : single x = single y ↔ x = y := by  -- we will use this lemma in the proof of Theorem 1.4 (d)
  rw [exten_prop (single y)]  -- use Theorem 1.2
  constructor  -- split the iff
  · intro h
    have h14a : ∀ (u : S), u = x ↔ u = y := by  -- this holds by rewriting h using Theorem 1.4 (a)
      intro u  -- pick u arbitrarily
      specialize h u  -- substitute u in h
      rw [← single_iff u x]; rw [← single_iff u y]  -- use Theorem 1.4 (a) twice
      exact h
    specialize h14a x; simp at h14a  -- substitute x in h14a and simplify
    exact h14a
  · intros h u  -- this case is trivial
    rw [h]

lemma pair_single (x y z : S) : (pair y z = single x) ↔ (x = y ∧ x = z) := by  -- we will use this lemma in the proof of Theorem 1.4 (d)
  rw [exten_prop (single x)]  -- use Theorem 1.2
  constructor  -- split the iff
  · intro h
    have h14: ∀ u, u = y ∨ u = z ↔ u = x  := by  -- this holds by rewriting h using Theorem 1.4 (a) and (b)
      intro u  -- pick u arbitrarily
      specialize h u  -- substitute u in h
      rw [← pair_iff u y z]; rw [← single_iff u x]  -- use Theorem 1.4 (a) and (b)
      exact h
    have h14' := h14  -- copy h14 for later use
    specialize h14 y; simp at h14  -- substitute y in h14 and simplify
    specialize h14' z; simp at h14'  -- substitute z in h14' and simplify
    rw [h14]; rw [h14']; simp
  · intro h
    cases' h with h1 h2  -- split the ∧ in the hypothesis
    intro u  -- pick u arbitrarily
    rw [← h1]; rw[← h2]  -- subtitute x = y =z
    rw [double_pair x]  -- use Theorem 1.4 (c)

lemma pair_equal (x y u v : S) : (pair x y = pair u v) → (x ∈ pair u v ∧ y ∈ pair u v) := by  -- we will use this lemma in the proof of Theorem 1.4 (d)
  rw [exten_prop (pair u v)]  -- use Theorem 1.2
  intro h
  have h14b : ∀ (w : S), (w = x ∨ w = y) ↔ (w = u ∨ w = v) := by  -- this holds by rewriting h using Theorem 1.4 (b)
    intro w  -- pick w arbitrarily
    specialize h w  -- substitute w in h
    rw [← pair_iff w x y]; rw [← pair_iff w u v]  -- use Theorem 1.4 (b) twice
    exact h
  constructor  -- split the ∧ in the goal
  · rw [pair_iff x u v]  -- use Theorem 1.4 (b)
    specialize h14b x; simp at h14b  -- substitute x in h14b and simplify
    exact h14b
  · rw [pair_iff y u v]  -- use Theorem 1.4 (b)
    specialize h14b y; simp at h14b  -- substitute y in h14b and simplify
    exact h14b

theorem ord_pair_equal (x y u v : S) : ord_pair x y = ord_pair u v ↔ x = u ∧ y = v := by
  constructor  -- split the iff
  -- this is the interesting direction
  · intro h
    rw [ord_pair] at h; rw [ord_pair] at h  -- use definition of ⟨x,y⟩
    have h' : pair (single u) (pair u v) = pair (single x) (pair x y) := by rw [h]  -- have h' which is h interchanged
    apply pair_equal (single x) (pair x y) (single u) (pair u v) at h  -- use the third lemma to rewrite h
    apply pair_equal (single u) (pair u v) (single x) (pair x y) at h'  -- use the third lemma to rewrite h'
    cases' h with hx hxy  -- split the ∧ in the hypothesis
    cases' h' with hu huv  -- split the ∧ in the hypothesis
    rw [pair_iff (single u) (single x) (pair x y)] at hu  -- use Theorem 1.4 (b) to rewrite hu
    rw [pair_iff (pair u v) (single x) (pair x y)] at huv  -- use Theorem 1.4 (b) to rewrite huv
    rw [pair_iff (single x) (single u) (pair u v)] at hx  -- use Theorem 1.4 (b) to rewrite hx
    rw [pair_iff (pair x y) (single u) (pair u v)] at hxy  -- use Theorem 1.4 (b) to rewrite hy
    -- have hu' :=  hu; have huv' := huv  -- copy hu and huv for later use
    cases' hu with ha hb  -- split hu into two cases
    · rw [single_equal u x] at ha  -- use the lemma: {u} = {x} ↔ u = x
      constructor  -- split the ∧ in the goal
      · rw [ha]  -- u = x
      · cases' huv with hc hd  -- split huv into two cases
        · rw [pair_single x u v] at hc  -- use the lemma: {u,v} = {x} ↔ u = v = x
          cases' hc with hcu hcv  -- split the ∧ in the hypothesis
          rw [← hcv] at hxy; rw [← hcu] at hxy   -- substitute v = x  and u = x in hxy
          rw [double_pair x] at hxy; simp at hxy  -- use Theorem 1.4 (c) to rewrite hxy and simplify
          rw [pair_single x x y] at hxy; simp at hxy  -- use the lemma: {x,y} = {x} ↔ x = y
          rw [← hxy]; exact hcv  -- conclude u = v = x = y
        · apply pair_equal u v x y at hd  -- use the third lemma to rewrite hd
          cases' hd with hd1 hd2  -- split the ∧ at the hypothesis
          rw [pair_iff u x y] at hd1  -- use Theorem 1.4 (b) to rewrite hd1
          rw [pair_iff v x y] at hd2  -- use Theorem 1.4 (b) to rewrite hd2
          cases' hd2 with hdx hdy -- split hd2 into two cases
          · rw [hdx] at hxy; rw [ha] at hxy   -- substitute v = x  and u = x in hxy
            rw [double_pair x] at hxy; simp at hxy  -- use Theorem 1.4 (c) to rewrite hxy and simplify
            rw [pair_single x x y] at hxy; simp at hxy  -- use the lemma: {x,y} = {x} ↔ x = y
            rw [← hxy]; rw [hdx]  -- conclude u = v = x = y
          · rw [hdy]  -- this case is trivial
    · have hb' : pair x y = single u := by rw [hb]  -- have hb' which is hb interchanged to apply the second lemma
      rw [pair_single u x y] at hb'  -- use the lemma: {x,y} = {u} ↔ u = x = y
      cases' hb' with hbx hby  -- split the ∧ in the hypothesis
      constructor  -- split the ∧ in the goal
      · rw [hbx]
      · rw [← hbx] at huv; rw [← hby] at huv  -- substitute x = u  and y = u in huv
        rw [double_pair u] at huv; simp at huv  -- use Theorem 1.4 (c) to rewrite hxy and simplify
        rw [pair_single u u v] at huv; simp at huv  -- use the lemma: {u,v} = {u} ↔ u = v
        rw [← huv]; rw [hby]  -- conclude u = v = x = y
  -- this is the trivial direction
  · intro h; rw [ord_pair]; rw [ord_pair] -- use definition of ⟨x,y⟩
    cases' h with h1 h2  -- split the ∧ in the hypothesis
    rw [h1]; rw [h2]


-- Theorem 1.5 (Existence of the union of two sets)

theorem exists_union (x y : S) : ∃(z : S), ∀(u : S), (u ∈ z ↔ (u ∈ x ∨ u ∈ y))  := by
  induction' x using HF.induction with x w hx _
  -- base case
  · use y  -- take z = y
    simp [set_notin_empty]
  -- inductive step
  · simp_rw [enlarge_iff]
    cases' hx with xUy hxUy  -- xUy is x ∪ y, which exists by hypothesis
    use xUy ◁ w  -- take z = (x ∪ y) ◁ w
    simp_rw [enlarge_iff, hxUy]; tauto

/-- x ∪ y -/
noncomputable def union (x y : S) : S := (exists_union x y).choose

lemma union_iff (x y : S) : ∀ (u : S), u ∈ union x y ↔ u ∈ x ∨ u ∈ y :=
  (exists_union x y).choose_spec


-- Theorem 1.6 (Existence of the union of a set of sets)

theorem exists_union_set (x : S) : ∃(z : S), ∀(u : S), (u ∈ z ↔ (∃ y ∈ x, u ∈ y))  := by
  revert x  -- to prove ∀x α(x) using HF3/induction
  apply HF.induction
  -- base case
  · use ∅  -- take z = ∅
    simp [set_notin_empty]
  -- inductive step
  · intros x w hx _
    simp_rw [enlarge_iff, or_and_right, exists_or, exists_eq_left]
    cases' hx with Ux hUx  -- Ux is ⋃ x, which exists by hypothesis
    use union Ux w  -- take z = (⋃ x) ∪ w
    simp_rw [union_iff]; simp_all

/-- ⋃ x -/
noncomputable def union_set (x : S) : S := (exists_union_set x).choose

lemma union_set_iff (x : S) : ∀(u : S), (u ∈ union_set x ↔ (∃ y ∈ x, u ∈ y)) :=
  (exists_union_set x).choose_spec


-- Theorem 1.7 (Comprehension Scheme)

theorem comp_scheme (x : S) (φ : S → Prop) : ∃ (z : S), ∀ (u : S), (u ∈ z ↔ u ∈ x ∧ φ u) := by
  revert x -- to prove ∀x α(x) using HF3/induction
  apply HF.induction
  -- base case
  · use ∅  -- take z = ∅
    simp [set_notin_empty]
  -- inductive step
  · intros x y hx _
    simp_rw [enlarge_iff]
    cases' hx with xφ hxφ  -- xφ is {u ∈ x : φ(u)} , which exists by hypothesis
    by_cases hφy : φ y
    · use xφ ◁ y  -- take z = {u ∈ x : φ(u)} ◁ y
      simp_rw [enlarge_iff]; aesop
    · use xφ; aesop  -- take z = {u ∈ x : φ(u)}

/-- {u ∈ x : φ(u)} -/
noncomputable def pred_set (x : S) (φ : S → Prop) : S := (comp_scheme x φ).choose

lemma pred_set_iff (x : S) (φ : S → Prop) : ∀ (u : S), (u ∈ pred_set x φ ↔ u ∈ x ∧ φ u) :=
  (comp_scheme x φ).choose_spec


-- Definition 1.8 (Intersection)

/-- x ∩ y = {u ∈ x : u ∈ y} -/
noncomputable def inter (x : S) (y : S) : S := pred_set x (fun u ↦ u ∈ y)

lemma inter_iff (x y : S) : ∀ (u : S), (u ∈ inter x y ↔ u ∈ x ∧ u ∈ y) := by
  exact pred_set_iff _ _

/-- ⋂ x = {u ∈ ⋃ x : ∀ v ∈ x, u ∈ v} -/
noncomputable def inter_set (x : S) : S := pred_set (union_set x) (fun u ↦ ∀ v ∈ x, u ∈ v)

lemma inter_set_iff (x : S) :
    ∀ (u : S), (u ∈ inter_set x ↔ u ∈ union_set x ∧ ∀ v ∈ x, u ∈ v) := by
  exact pred_set_iff _ _

lemma inter_enlarge (x y : S) : inter (x ◁ y) x = x := by
  simp_rw [exten_prop, inter_iff, enlarge_iff]; aesop


-- Theorem 1.9 (Replacement Scheme)

theorem repl_scheme (x : S) (ψ : S → S → Prop) :
    (∀ u ∈ x, ∃! v, ψ u v) → (∃ (z : S), ∀ v, (v ∈ z ↔ ∃ u ∈ x, ψ u v)) := by
  revert x -- to prove ∀x α(x) using HF3/induction
  apply HF.induction
  -- base case
  · intro _; use ∅  -- take z = ∅
    simp [set_notin_empty]
  -- inductive step
  · intros x y hx _ h
    simp_rw [enlarge_iff] at h; have h2 := h
    specialize h y; simp only [or_true, forall_true_left] at h
    cases' h with vy hvy
    have hx1 : (∀ u ∈ x, ∃! v, ψ u v) := by simp_all
    specialize hx hx1
    cases' hx with xψ hxψ  -- xψ is {v : ∃ u ∈ x, ψ(u,v)}, which exists by hypothesis
    use xψ ◁ vy  -- take z = {v : ∃ u ∈ x, ψ(u,v)} ◁ vy
    simp_rw [enlarge_iff]; aesop

/-- {v : ∃ u ∈ x, ψ(u,v)} -/
noncomputable def repl (x : S) (ψ : S → S → Prop) (h : (∀ u ∈ x, ∃! v, ψ u v)) : S
    := (repl_scheme x ψ h).choose

lemma repl_iff (x : S) (ψ : S → S → Prop) (h : (∀ u ∈ x, ∃! v, ψ u v)) :
    ∀ (v : S), (v ∈ repl x ψ h ↔ ∃ u ∈ x, ψ u v) := (repl_scheme x ψ h).choose_spec


-- Definition 1.10 (Subset relation)

/-- y ⊆ x -/
def subset_eq (y x : S) : Prop := ∀ (v : S), v ∈ y → v ∈ x

/-- y ⊂ x -/
def subset (y x : S) : Prop := subset_eq y x ∧ y ≠ x


-- Theorem 1.11 (Existence of the power set)

lemma subset_enlarge (u x y Px : S) (hPx : ∀ (u : S), u ∈ Px ↔ subset_eq u x) :
    subset_eq u (x ◁ y) ↔ (u ∈ Px) ∨ (∃ v ∈ Px, u = v ◁ y) := by
  constructor
  · intro hu
    simp_rw [subset_eq, enlarge_iff] at hu
    by_cases hy : y ∈ u
    · right
      use inter u x; constructor  -- the required v is u ∩ x
      · simp_rw [hPx, subset_eq, inter_iff]; simp_all
      · simp_rw [HF.enlarge, inter_iff]; aesop
    · left; rw [hPx, subset_eq]
      intros v hv; specialize hu v hv; aesop
  · intro hu; cases' hu with hul hur
    · rw [hPx, subset_eq] at hul
      simp_rw [subset_eq, enlarge_iff]; simp_all
    · cases' hur with v hv
      cases' hv with hv1 hv2; rw [HF.enlarge] at hv2
      simp_rw [subset_eq, enlarge_iff, hv2]; aesop

theorem exists_power (x : S) : ∃ (z : S), ∀ (u : S), u ∈ z ↔ subset_eq u x := by
  revert x -- to prove ∀x α(x) using HF3/induction
  apply HF.induction
  -- base case
  · use single ∅  -- take z = {∅}
    simp_rw [single_iff, subset_eq, exten_prop]
    simp [set_notin_empty]
  -- inductive step
  · intros x y hx _
    cases' hx with Px hPx  -- Px is the power set P(x), which exists by hypothesis
    have h : (∀ v ∈ Px, ∃! u, u = v ◁ y) := by  -- condition for usage replacement scheme
      intros v _; use v ◁ y; simp_all
    -- take z = P(x) ∪ {u : ∃ v ∈ P(x), u = v ◁ y}
    use union (Px) (repl (Px) (fun v u ↦ u = v ◁ y) (h))
    intro u; have hsub := subset_enlarge u x y Px  -- use the lemma
    specialize hsub hPx; rw [hsub, union_iff, repl_iff]

  /-- Power set: P(x) -/
noncomputable def power (x : S) : S := (exists_power x).choose

lemma power_iff (x : S) : ∀ (u : S), u ∈ power x ↔ subset_eq u x :=
  (exists_power x).choose_spec


-- Definition 1.12 (∈-minimal element)

/-- w an ∈-minimal element of z: w ∈ z ∧ w ∩ z = ∅ -/
def mem_min (w z : S) : Prop := w ∈ z ∧ inter w z = ∅


-- Theorem 1.13 (Foundation Property)

lemma found_prop_lemma (z : S) : (∀ w ∈ z, inter w z ≠ ∅) → ∀ x, x ∉ z ∧ inter x z = ∅ := by
  intro h; apply HF.induction
  -- base case
  · constructor
    · by_contra hn
      specialize h ∅ hn; simp only [ne_eq] at h
      simp_rw [exten_prop, inter_iff] at h; simp_all [set_notin_empty]
    · simp_rw [exten_prop, inter_iff]; simp_all [set_notin_empty]
  -- inductive step
  · intros x y hx hy
    by_contra hn; rw [not_and_or] at hn
    simp only [not_not] at hn
    have hxyz : (¬inter (x ◁ y) z = ∅) → False := by  -- covers both Case 1 and Case 2
      intro hne; have hstep : inter x z ≠ ∅ → False := by simp_all
      apply hstep
      simp_rw [exten_prop, inter_iff, enlarge_iff] at hne; simp only [not_forall] at hne
      cases' hne with w hw; simp [set_notin_empty] at hw
      cases' hw with hw1 hw2; cases' hw1 with hwl hwr
      · simp_rw [exten_prop, inter_iff] at hx; simp_all [set_notin_empty]
      · simp_rw [exten_prop, inter_iff] at hy; simp_all
    cases' hn with hnl hnr  -- Case 1 and Case 2
    · specialize h (x ◁ y) hnl; simp only [ne_eq] at h ; simp_all
    · simp_all

theorem found_prop (z : S) : z ≠ ∅ → ∃ w, mem_min w z := by
  have h := found_prop_lemma z
  rw [not_imp_comm, not_exists]; intro h2
  simp_rw [mem_min] at h2; simp only [not_and] at h2
  simp only [ne_eq] at h
  specialize h h2; rw [exten_prop]
  simp_all [set_notin_empty]


-- Corollary 1.14

theorem set_notin_set (x : S) : x ∉ x := by
  have h := found_prop (single x)
  have hx : single x ≠ ∅ := by
    simp only [ne_eq]; simp_rw [single, exten_prop, enlarge_iff]
    simp_all [set_notin_empty]
  specialize h hx
  cases' h with w hw; rw [mem_min] at hw
  simp_rw [single, exten_prop, inter_iff, enlarge_iff] at hw
  simp only [set_notin_empty] at hw; aesop

end HF
