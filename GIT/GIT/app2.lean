import Mathlib.Tactic
import GIT.app1

/-!
# Appendix 2: Ordinals of hereditarily finite set theory

In this file, Appendix 2 of S. Swierczkowski: 'Finite Sets and Gödel’s Incompleteness Theorems' is formalised.
It presents the theory on hereditarily finite ordinals.

This work contains a stronger version of the original Theorem 2.7 on the ordering of ordinals. See section 'On the ordering of ordinals'.

By 'set' we mean an 'HF set'; by 'collection' we mean a 'Lean set' (i.e. a set which need not be HF).

## Main results

- `HF.compar_of_ord_ord`: Comparability of ordinals.
- `HF.exists_max_of_set_of_ord`: Existence of a largest element of a set of ordinals.
- `HF.exists_min_of_set_of_ord`: Existence of a smallest element of a set of ordinals.
- `HF.ordinal.lt_wf`: The binary relation < is well-founded on every collection of ordinals.
- `HF.ordinal.exists_min_set`: Existence of a smallest element of a collection of ordinals.
- `HF.ordinal.cond_comp_lin_ord_bot`: The ordinals, ordered by <, form a conditionally complete linear order with a bottom element.

## Notation

- `◁` : enlarging, see `HF.enlarge`.
- `<` : membership for ordinals. See section 'On the ordering of ordinals'.
- `≤` : membership or equality for ordinals. See section 'On the ordering of ordinals'.

## References

S. Swierczkowski. Finite Sets and Gödel’s Incompleteness Theorems. Dissertationes
mathematicae. IM PAN, 2003. URL https://books.google.co.uk/books?id=5BQZAQAAIAAJ.
-/

open Classical

suppress_compilation

set_option maxHeartbeats 500000

variable {S : Type u} [HF S]

namespace HF

--- Definition 2.1 ---

/-- The set x is transitive -/
def tran (x : S) : Prop := ∀ y ∈ x, subset_eq y x

/-- The set x is an ordinal -/
def ord (x : S) : Prop := tran x ∧ ∀ y ∈ x, tran y

--- Definition 2.2 ---

/-- The successor of a set x -/
def succ (x : S) : S := x ◁ x

--- Theorem 2.3 ---

lemma ord_iff_ord_succ (x : S) : ord x ↔ ord (succ x) := by
  simp_rw [ord, tran, succ, subset_eq, enlarge_iff]; aesop

theorem succ_of_ord_is_ord (x : S) (ord_x : ord x) : ord (succ x) := by
  rwa [← ord_iff_ord_succ]

theorem element_of_ord_is_ord (x y : S) (ord_x : ord x) (y_in_x : y ∈ x) : ord y := by
  simp_rw[ord] at *; aesop

theorem empty_is_ord : ord (∅ : S) := by
  rw [ord, tran]; simp [set_notin_empty]

theorem mem_min_of_ord_eq_empty (x : S) (ord_x : ord x) (neq_emp : x ≠ ∅) :
    (∀ w, mem_min w x → w = ∅) ∧ ∅ ∈ x := by
  have mem_min_imp_emp (w : S) (w_mem_min : mem_min w x) : w = ∅ := by
    simp_rw [mem_min, exten_prop, inter_iff, set_notin_empty, iff_false, not_and] at w_mem_min
    cases' w_mem_min with w_in_x hwx
    cases' ord_x with tran_x _; simp_rw [tran, subset_eq] at tran_x
    specialize tran_x w w_in_x
    rw [HF.empty]; simp_all
  obtain ⟨w, w_mem_min⟩ := found_prop x neq_emp; have w_eq_emp := w_mem_min
  apply mem_min_imp_emp at w_eq_emp
  cases' w_mem_min with w_in_x hwx; rw [w_eq_emp] at w_in_x
  aesop

lemma empty_in_ord (x : S) (ord_x : ord x) (neq_emp : x ≠ ∅) : ∅ ∈ x := by have := mem_min_of_ord_eq_empty x; simp_all

--- Theorem 2.4 ---

lemma compar_of_ord_ord_aux1 (h : ∃ (k l : S), ord k ∧ ord l ∧ k ∉ l ∧ k ≠ l ∧ l ∉ k) :
    ∃ (k0 : S), ord k0 ∧ (∀ m ∈ k0, ∀ l, ord l → (m ∈ l ∨ m = l ∨ l ∈ m))
    ∧ (∃ l, ord l ∧ (k0 ∉ l ∧ k0 ≠ l ∧ l ∉ k0)) := by
  rcases h with ⟨k, ⟨l, ⟨ord_k, ⟨ord_l, hkl⟩⟩⟩⟩
  let K := pred_set (power k) (fun k0 ↦ (ord k0 ∧ ∃ l, ord l ∧ (k0 ∉ l ∧ k0 ≠ l ∧ l ∉ k0)))
  have K_neq_emp : K ≠ ∅ := by
    intro hK; rw [HF.empty] at hK; specialize hK k; apply hK; rw [pred_set_iff, power_iff, subset_eq]; aesop
  obtain ⟨k0, ⟨k0_in_K, inter_k0_K⟩⟩ := found_prop K K_neq_emp
  rw [pred_set_iff] at k0_in_K
  rcases k0_in_K with ⟨k0_power_k, ⟨ord_k0, hk0⟩⟩
  refine ⟨k0, by exact ord_k0, ⟨?_, by exact hk0⟩⟩
  by_contra! hn
  rcases hn with ⟨r0, ⟨r0_in_k0, ⟨l0, ⟨ord_l0, hr0l0⟩⟩⟩⟩
  simp_rw [HF.empty, inter_iff] at inter_k0_K
  refine inter_k0_K r0 ⟨r0_in_k0, ?_⟩
  rw [pred_set_iff, power_iff]
  rw [power_iff] at k0_power_k
  have r0_in_k : r0 ∈ k := by aesop
  rw [ord, tran] at ord_k; cases' ord_k with tran_k _
  specialize tran_k r0 r0_in_k; simp only [tran_k, ne_eq, true_and]
  refine ⟨element_of_ord_is_ord k0 r0 ?_ ?_, ⟨l0, ?_⟩⟩ <;> simp_all

lemma compar_of_ord_ord_aux2 (k0 : S) (h : ∃ (l : S), ord l ∧ k0 ∉ l ∧ k0 ≠ l ∧ l ∉ k0) :
    ∃ (l0 : S), ord l0 ∧ (∀ p ∈ l0, k0 ∈ p ∨ k0 = p ∨ p ∈ k0)
    ∧ (k0 ∉ l0 ∧ k0 ≠ l0 ∧ l0 ∉ k0) := by
  rcases h with ⟨l, ⟨ord_l, hk0l⟩⟩
  let L := pred_set (power l) (fun l0 ↦ (ord l0 ∧ (k0 ∉ l0 ∧ k0 ≠ l0 ∧ l0 ∉ k0)))
  have L_neq_emp : L ≠ ∅ := by
    intro hL; rw [HF.empty] at hL; specialize hL l; apply hL; rw [pred_set_iff, power_iff, subset_eq]; aesop
  obtain ⟨l0, ⟨l0_in_L, inter_l0_L⟩⟩ := found_prop L L_neq_emp
  rw [pred_set_iff] at l0_in_L
  rcases l0_in_L with ⟨l0_power_l, ⟨ord_l0, hk0l0⟩⟩
  refine ⟨l0, by exact ord_l0, ⟨?_, by exact hk0l0⟩⟩
  by_contra! hn
  rcases hn with ⟨q0, ⟨q0_in_l0, hk0q0⟩⟩
  simp_rw [HF.empty, inter_iff] at inter_l0_L
  refine inter_l0_L q0 ⟨q0_in_l0, ?_⟩
  rw [pred_set_iff, power_iff]
  rw [power_iff] at l0_power_l
  have q0_in_l : q0 ∈ l := by aesop
  rw [ord, tran] at ord_l; cases' ord_l with tran_l _
  specialize tran_l q0 q0_in_l; simp only [tran_l, ne_eq, true_and]
  refine ⟨element_of_ord_is_ord l0 q0 ?_ ?_, ?_⟩ <;> simp_all

lemma subset_imp_diff_has_element (x y : S) (h : subset x y) : ∃ z, z ∈ y ∧ z ∉ x := by
  rw [subset, subset_eq] at h
  cases' h with h1 h2
  by_contra! hn
  have hf : ∀ u, u ∈ x ↔ u ∈ y := by aesop
  simp_all [exten_prop]

theorem compar_of_ord_ord (k l : S) (ord_k : ord k) (ord_l : ord l) :
    k ∈ l ∨ k = l ∨ l ∈ k := by
  revert k l
  by_contra! hn
  have hk := compar_of_ord_ord_aux1 hn
  rcases hk with ⟨k0, ⟨ord_k0, ⟨forall_in_k0, hk0⟩⟩⟩
  have hl := compar_of_ord_ord_aux2 k0 hk0
  rcases hl with ⟨l0, ⟨ord_l0, ⟨forall_in_l0, hl0⟩⟩⟩
  have subset_l0k0 : subset l0 k0 := by
    rw [subset, subset_eq]
    refine ⟨?_, by aesop⟩
    intros p p_in_l0
    specialize forall_in_l0 p p_in_l0
    simp_rw [ord, tran, subset_eq] at ord_l0; cases' ord_l0 with tran_l0 _
    specialize tran_l0 p p_in_l0
    rcases forall_in_l0 with k0_in_p | k0_eq_p | p_in_k0 <;> simp_all
  obtain ⟨m, ⟨m_in_k0 , m_notin_l0⟩⟩ := subset_imp_diff_has_element l0 k0 subset_l0k0
  specialize forall_in_k0 m m_in_k0 l0 ord_l0
  simp only [m_notin_l0, false_or] at forall_in_k0
  cases' forall_in_k0 with m_eq_l0 l0_in_m
  · simp_all
  · simp_rw [ord, tran, subset_eq] at ord_k0; cases' ord_k0 with tran_k0 _
    specialize tran_k0 m m_in_k0 l0 l0_in_m
    simp_all

--- Theorem 2.5 ---

lemma mem_antisymm_of_ord (k l : S) (ord_k : ord k) (k_in_l : k ∈ l) (l_in_k : l ∈ k) : False := by
  cases' ord_k with tran_k _
  simp_rw [tran, subset_eq] at tran_k
  specialize tran_k l l_in_k k k_in_l
  simp_all [set_notin_set]

theorem exclusive_compar_of_ord_ord (k l : S) (ord_k : ord k) (ord_l : ord l) :
  (k ∈ l ∧ (k ≠ l ∧ l ∉ k)) ∨ (k = l ∧ (k ∉ l ∧ l ∉ k)) ∨ (l ∈ k ∧ (k ∉ l ∧ k ≠ l)) := by
  have h := compar_of_ord_ord k l; specialize h ord_k ord_l
  have k_notin_k := set_notin_set k
  by_cases k_in_l : k ∈ l
  · left; simp only [k_in_l, true_and]
    refine ⟨by aesop, ?_⟩
    by_contra l_in_k
    apply mem_antisymm_of_ord k l <;> simp_all
  · by_cases k = l
    · right; left; aesop
    · right; right; aesop

theorem mem_iff_subset_of_ord_ord (k l : S) (ord_k : ord k) (ord_l : ord l) :
    k ∈ l ↔ subset k l := by
  have h := compar_of_ord_ord k l; specialize h ord_k ord_l
  cases' ord_k with tran_k _; cases' ord_l with tran_l _
  simp_rw [tran, subset_eq] at *
  have set_notin_set (m : S) := set_notin_set m
  constructor
  · intro k_in_l
    rw [subset, subset_eq]
    specialize tran_l k k_in_l
    refine ⟨by exact tran_l, by aesop⟩
  · intro k_subset_l; rw [subset, subset_eq] at k_subset_l
    cases' k_subset_l with k_subseteq_l k_neq_l
    simp only [k_neq_l, false_or] at h
    cases' h with k_in_l l_in_k
    · exact k_in_l
    · specialize k_subseteq_l l l_in_k; simp_all

theorem mem_imp_succ_eq_or_succ_mem_of_ord_ord (k l : S) (ord_k : ord k) (ord_l : ord l)  :
    l ∈ k → succ l = k ∨ succ l ∈ k := by
  have ord_succ_l : ord (succ l) := by exact succ_of_ord_is_ord l ord_l
  have h := compar_of_ord_ord k (succ l); simp only [and_imp] at h
  specialize h ord_k ord_succ_l
  intro l_in_k
  have k_notin_succ_l : k ∉ succ l := by
    intro k_in_succ_l
    rw [succ, enlarge_iff] at k_in_succ_l
    have set_notin_set (m : S) := set_notin_set m
    refine k_in_succ_l.elim ?_ (by aesop)
    apply mem_antisymm_of_ord l k <;> simp_all
  aesop

theorem eq_succ_of_ord (k l : S) (ord_k : ord k) :
    succ k = succ l → k = l := by
  intro h ; simp_rw [succ, exten_prop, enlarge_iff] at h
  have h2 := h
  specialize h k; specialize h2 l
  simp only [set_notin_set, or_true, true_iff, iff_true] at *
  by_contra! k_neq_l
  simp only [k_neq_l, or_false] at h
  rw [ne_comm] at k_neq_l; simp only [k_neq_l, or_false] at h2
  apply mem_antisymm_of_ord k l <;> simp_all

--- Theorem 2.6 (originally part of Theorem 2.7 in Swierczkowski (2003)) ---

lemma exists_max_of_enlarged_set_of_ord (x y : S) (set_of_ord : ∀ k ∈ x ◁ y, ord k)
    (x_has_max : ∃ l ∈ x, ∀ k ∈ x, (k ∈ l ∨ k = l)) :
    ∃ l ∈ x ◁ y, ∀ k ∈ x ◁ y, (k ∈ l ∨ k = l) := by
  rcases x_has_max with ⟨max_x, ⟨max_x_in_x, h_max_x⟩⟩
  use if max_x ∈ y then y else max_x
  split_ifs with max_x_in_y
  · simp_rw [enlarge_iff, or_true, true_and]
    intros k hkxy
    refine hkxy.elim ?_ (by simp_all); intro k_in_x
    specialize h_max_x k k_in_x
    refine h_max_x.elim ?_ (by simp_all); intro k_in_max_x
    have ord_y : ord y := by aesop
    cases' ord_y with tran_y _
    simp_rw [tran, subset_eq] at tran_y
    specialize tran_y max_x max_x_in_y k k_in_max_x
    left; exact tran_y
  · simp_rw [enlarge_iff, max_x_in_x, true_or, true_and]
    intros k hkxy
    refine hkxy.elim (by aesop) ?_; intro k_eq_y
    have compar_ord := compar_of_ord_ord k max_x
    simp_all

theorem exists_max_of_set_of_ord (x : S) (set_of_ord : ∀ k ∈ x, ord k) (neq_emp : x ≠ ∅) :
    ∃ l ∈ x, ∀ k ∈ x, (k ∈ l ∨ k = l) := by
  induction' x using HF.induction with x y hx _
  · simp_all
  · have x_set_of_ord : ∀ k ∈ x, ord k := by simp_rw [enlarge_iff] at set_of_ord; aesop
    specialize hx x_set_of_ord
    by_cases x_eq_emp : x = ∅
    · simp_rw [x_eq_emp, enlarge_iff, set_notin_empty, false_or]
      use y; simp_all
    · apply exists_max_of_enlarged_set_of_ord x y <;> simp_all

lemma exists_min_of_enlarged_set_of_ord (x y : S) (set_of_ord : ∀ k ∈ x ◁ y, ord k)
    (x_has_min : ∃ l ∈ x, ∀ k ∈ x, (l ∈ k ∨ l = k)) :
    ∃ l ∈ x ◁ y, ∀ k ∈ x ◁ y, (l ∈ k ∨ l = k) := by
  rcases x_has_min with ⟨min_x, ⟨min_x_in_x, h_min_x⟩⟩
  use if y ∈ min_x then y else min_x
  split_ifs with y_in_min_x
  · simp_rw [enlarge_iff, or_true, true_and]
    intros k hkxy
    refine hkxy.elim ?_ (by simp_all); intro k_in_x
    specialize h_min_x k k_in_x
    refine h_min_x.elim ?_ (by aesop); intro min_x_in_k
    have ord_k : ord k := by aesop
    cases' ord_k with tran_k _; simp_rw [tran, subset_eq] at tran_k
    specialize tran_k min_x min_x_in_k y y_in_min_x
    left; exact tran_k
  · simp_rw [enlarge_iff, min_x_in_x, true_or, true_and]
    intros k hkxy
    refine hkxy.elim (by aesop) ?_; intro k_eq_y
    have compar_ord := compar_of_ord_ord min_x k
    simp_all

theorem exists_min_of_set_of_ord (x : S) (set_of_ord : ∀ k ∈ x, ord k) (neq_emp : x ≠ ∅) :
    ∃ l ∈ x, ∀ k ∈ x, (l ∈ k ∨ l = k) := by
  induction' x using HF.induction with x y hx _
  · simp_all
  · have x_set_of_ord : ∀ k ∈ x, ord k := by simp_rw [enlarge_iff] at set_of_ord; aesop
    specialize hx x_set_of_ord
    by_cases x_eq_emp : x = ∅
    · simp_rw [x_eq_emp, enlarge_iff, set_notin_empty, false_or]
      use y; simp_all
    · apply exists_min_of_enlarged_set_of_ord x y <;> simp_all

--- Theorem 2.7 (originally Theorem 2.8 in Swierczkowski (2003)) ---

lemma succ_of_ord_notin_ord (k : S) (ord_k : ord k) : succ k ∉ k := by
  cases' ord_k with tran_k _
  simp_rw [tran, subset_eq] at tran_k
  intro succ_k_in_k
  specialize tran_k (succ k) succ_k_in_k
  simp_rw [succ, enlarge_iff] at tran_k
  specialize tran_k k
  simp_all [set_notin_set]

theorem exists_predec_of_ord (k : S) (ord_k : ord k) (neq_emp : k ≠ ∅) :
    ∃! l, succ l = k := by
  have k_set_of_ord : ∀ m ∈ k, ord m := by intro m; apply element_of_ord_is_ord k m ord_k
  obtain ⟨max_k, ⟨max_k_in_k, h_max_k⟩⟩ := exists_max_of_set_of_ord k k_set_of_ord neq_emp
  have ord_max_k : ord max_k := by aesop
  have succ_max_k_k := mem_imp_succ_eq_or_succ_mem_of_ord_ord k max_k ord_k ord_max_k max_k_in_k
  cases' succ_max_k_k with succ_max_k_eq_k succ_max_k_in_k
  · use max_k
    simp_rw [← succ_max_k_eq_k, true_and]
    intros y h_succ; have h_succ2 := h_succ
    rw [succ_max_k_eq_k] at h_succ; rw [← h_succ, ← ord_iff_ord_succ] at ord_k
    exact eq_succ_of_ord y max_k ord_k h_succ2
  · specialize h_max_k (succ max_k) succ_max_k_in_k
    simp only [succ_of_ord_notin_ord max_k ord_max_k, false_or] at h_max_k
    simp_rw [exten_prop, succ, enlarge_iff] at h_max_k
    specialize h_max_k max_k
    simp_all [set_notin_set]

--- Definition 2.8 (originally Definition 2.9 in Swierczkowski (2003)) ---

/-- The predecessor of a non-empty set x, which is an ordinal -/
def predec (k : S) (ord_k : ord k) (neq_emp : k ≠ ∅) : S := (exists_predec_of_ord k ord_k neq_emp).choose

lemma succ_predec_of_ord_eq_ord (k : S) (ord_k : ord k) (neq_emp : k ≠ ∅) :
    succ (predec k ord_k neq_emp) = k := by
  have := (exists_predec_of_ord k ord_k neq_emp).choose_spec; simp only at this
  cases' this with this _
  rw [predec]; exact this

----------------------------------------------------------------------------------------------------------------------------------------------
--- On the ordering of ordinals ---
----------------------------------------------------------------------------------------------------------------------------------------------

variable (S) in
/-- The ordinal type, which is a subtype of the type for HF set (S)-/
def ordinal : Type u := {k : S // ord k}

namespace ordinal

instance : Membership (ordinal S) (ordinal S) := ⟨fun k l ↦ k.1 ∈ l.1⟩

instance : EmptyCollection (ordinal S) := ⟨⟨(∅ : S), empty_is_ord⟩⟩

@[simp] lemma eq (k l : ordinal S) : k = l ↔ k.1 = l.1 := Subtype.ext_iff

lemma neq (k l : ordinal S) : k ≠ l ↔ k.1 ≠ l.1 := by simp

@[simp] lemma mem (k l : ordinal S) : k ∈ l ↔ k.1 ∈ l.1 := Iff.rfl

lemma set_in_empty_false (k : ordinal S) (k_in_emp : k ∈ (∅ : ordinal S)) : False := by
  cases' k with k ord_k; simp only [mem] at k_in_emp
  apply set_notin_empty k
  exact k_in_emp

lemma set_in_set_false (k : ordinal S) (k_in_k : k ∈ k) : False := by
  cases' k with k ord_k; simp only [mem] at k_in_k
  simp_all [set_notin_set]

/-- The successor of an ordinal k -/
def succ (k : ordinal S) : ordinal S := ⟨_, succ_of_ord_is_ord _ k.2⟩

lemma contains_empty (k : ordinal S) (neq_emp : k ≠ ∅) : ∅ ∈ k := by
cases' k with k ord_k; simp only [mem]
apply empty_in_ord <;> aesop

lemma compar (k l : ordinal S) : k ∈ l ∨ k = l ∨ l ∈ k := by
  cases' k with k ord_k; cases' l with l ord_l
  simp only [eq, mem]
  apply compar_of_ord_ord k l ord_k ord_l

lemma mem_antisymm (k l : ordinal S) (k_in_l : k ∈ l) (l_in_k : l ∈ k) : False := by
  cases' k with k ord_k; cases' l with l ord_l
  simp only [mem] at *
  apply mem_antisymm_of_ord k l ord_k k_in_l l_in_k

lemma exclusive_compar (k l : ordinal S) :
    (k ∈ l ∧ (k ≠ l ∧ l ∉ k)) ∨ (k = l ∧ (k ∉ l ∧ l ∉ k)) ∨ (l ∈ k ∧ (k ∉ l ∧ k ≠ l)) := by
  cases' k with k ord_k; cases' l with l ord_l
  simp only [eq, neq, mem]
  apply exclusive_compar_of_ord_ord k l ord_k ord_l

/-- k ⊆ l -/
def sbst_eq (k l : ordinal S) : Prop := ∀ (v : ordinal S), v ∈ k → v ∈ l

@[simp] lemma sbst_eq_lemma (k l : ordinal S) : sbst_eq k l ↔ subset_eq k.1 l.1 := by
  cases' k with k ord_k; cases' l with l ord_l
  rw [sbst_eq, subset_eq]
  simp only [mem]
  refine ⟨?_, by simp_all⟩
  intros h v v_in_k
  have ord_v : ord v := by exact element_of_ord_is_ord k v ord_k v_in_k
  let v' : ordinal S := ⟨v, ord_v⟩
  specialize h v'
  aesop

/-- k ⊂ l -/
def sbst (k l : ordinal S) : Prop := sbst_eq k l ∧ k ≠ l

@[simp] lemma sbst_lemma (k l : ordinal S) : sbst k l ↔ subset k.1 l.1 := by
  cases' k with k ord_k; cases' l with l ord_l
  rw [sbst, subset]
  simp_all

lemma mem_iff_subset (k l : ordinal S) : k ∈ l ↔ sbst k l := by
  cases' k with k ord_k; cases' l with l ord_l
  simp only [mem, sbst_lemma]
  apply mem_iff_subset_of_ord_ord k l ord_k ord_l

lemma mem_imp_succ_eq_or_succ_mem (k l : ordinal S) (l_in_k : l ∈ k) : succ l = k ∨ succ l ∈ k := by
  cases' k with k ord_k; cases' l with l ord_l
  simp only [eq, mem] at *
  apply mem_imp_succ_eq_or_succ_mem_of_ord_ord k l ord_k ord_l l_in_k

lemma eq_succ (k l : ordinal S) : succ k = succ l → k = l := by
  cases' k with k ord_k; cases' l with l ord_l
  simp only [eq]
  apply eq_succ_of_ord k l ord_k

instance : LT (ordinal S) := ⟨fun k l => (k ∈ l)⟩

lemma lt_iff (k l : ordinal S) : k < l ↔ k ∈ l  := by rfl

instance : LE (ordinal S) := ⟨fun k l => (k ∈ l) ∨ k = l⟩

lemma le_iff (k l : ordinal S) : k ≤ l ↔ k < l ∨ k = l := by rfl

lemma exists_max (k : ordinal S) (neq_emp : k ≠ ∅) : ∃ l ∈ k, ∀ m ∈ k, (m ≤ l) := by
  simp_rw [le_iff, lt_iff]
  cases' k with k ord_k; simp only [eq, neq, mem] at *
  have k_set_of_ord (l : S) (l_in_k : l ∈ k) := element_of_ord_is_ord k l ord_k l_in_k
  obtain ⟨max_k, ⟨max_k_in_k, h_max_k⟩⟩ := exists_max_of_set_of_ord k k_set_of_ord neq_emp
  have ord_max_k : ord max_k := by aesop
  let max_k' : ordinal S := ⟨max_k, ord_max_k⟩
  use max_k'
  simp_all

/-- The largest element of an ordinal k -/
def max (k : ordinal S) (neq_emp : k ≠ ∅) : ordinal S := (exists_max k neq_emp).choose

lemma le_max (k : ordinal S) (neq_emp : k ≠ ∅) : ∀ l ∈ k, l ≤ max k neq_emp := by
  have := (exists_max k neq_emp).choose_spec; aesop

/-- The predecessor of a non-empty ordinal k, i.e. it's largest element -/
def predec (k : ordinal S) (neq_emp : k ≠ ∅) : ordinal S := max k neq_emp

lemma succ_le_false (k : ordinal S) : ¬succ k ≤ k := by
   rw [le_iff, lt_iff, succ]
   cases' k with k ord_k; simp only [eq, neq, mem]
   simp only [succ_of_ord_notin_ord k ord_k, false_or]
   simp_rw [exten_prop, HF.succ, enlarge_iff, or_iff_left_iff_imp, forall_eq]
   simp_all [set_notin_set]

lemma succ_of_predec (k : ordinal S) (neq_emp : k ≠ ∅) : succ (predec k neq_emp) = k := by
  rw [predec]
  have max_in_k : max k neq_emp ∈ k := by have := (exists_max k neq_emp).choose_spec; aesop
  apply mem_imp_succ_eq_or_succ_mem k (max k neq_emp) at max_in_k
  refine max_in_k.elim (by simp_all) ?_; intro succ_max_in_k
  exfalso
  have succ_le := le_max k neq_emp (succ (max k neq_emp)) succ_max_in_k
  apply succ_le_false (max k neq_emp) succ_le

lemma le_refl' (k : ordinal S) : k ≤ k := by simp_rw [le_iff, lt_iff]; simp

lemma le_trans' (k l m : ordinal S) : k ≤ l → l ≤ m → k ≤ m := by
  simp_rw [le_iff, lt_iff]
  intros hk hl
  cases' k with k ord_k; cases' l with l ord_l; cases' m with m ord_m
  simp only [mem, eq] at *
  simp_rw [ord, tran, subset_eq] at *
  aesop

lemma lt_iff_le_not_le' (k l : ordinal S) : k < l ↔ k ≤ l ∧ ¬l ≤ k := by
  simp_rw [le_iff, lt_iff]
  refine ⟨?_, by aesop⟩
  intro k_in_l
  refine ⟨by simp_all, ?_⟩; push_neg
  constructor
  · intro l_in_k
    apply mem_antisymm k l <;> simp_all
  · intro l_eq_k
    apply set_in_set_false k; simp_all

lemma le_antisymm' (k l : ordinal S) : k ≤ l → l ≤ k → k = l := by
  simp_rw [le_iff, lt_iff]
  intros hk hl
  by_contra k_neq_l
  apply mem_antisymm k l <;> aesop

lemma le_total' (k l : ordinal S) : k ≤ l ∨ l ≤ k := by
  simp_rw [le_iff, lt_iff]
  have := compar k l
  aesop

lemma emp_le (k : ordinal S) : ∅ ≤ k := by
  simp_rw [le_iff, lt_iff]
  have := contains_empty k
  tauto

instance : PartialOrder (ordinal S) where
  le_refl := le_refl'
  le_trans := le_trans'
  lt_iff_le_not_le := lt_iff_le_not_le'
  le_antisymm := le_antisymm'

instance : Sup (ordinal S) where
  sup := fun k l => if k ≤ l then l else k

lemma sup_def (k l : ordinal S) : k ⊔ l = if k ≤ l then l else k := rfl

lemma le_sup_left' (k l : ordinal S) : k ≤ k ⊔ l := by rw [sup_def]; aesop

lemma le_sup_right' (k l : ordinal S) : l ≤ k ⊔ l := by
  rw [sup_def]
  have h2 := le_total' k l
  aesop

lemma sup_le' (k l m : ordinal S) :k ≤ m → l ≤ m → k ⊔ l ≤ m := by rw [sup_def]; aesop

instance : Inf (ordinal S) where
  inf := fun k l => if k ≤ l then k else l

lemma inf_def (k l : ordinal S) : k ⊓ l = if k ≤ l then k else l := rfl

lemma inf_le_left' (k l : ordinal S) : k ⊓ l ≤ k := by
  rw [inf_def]
  have := le_total' k l
  aesop

lemma inf_le_right' (k l : ordinal S) : k ⊓ l ≤ l := by rw [inf_def]; aesop

lemma le_inf' (k l m : ordinal S) : k ≤ l → k ≤ m → k ≤ l ⊓ m := by rw [inf_def]; aesop

instance : Lattice (ordinal S) where
  le_sup_left := le_sup_left'
  le_sup_right := le_sup_right'
  sup_le := sup_le'
  inf_le_left := inf_le_left'
  inf_le_right := inf_le_right'
  le_inf := le_inf'

lemma trans' : ∀ (k l m : ordinal S), k < l → l < m → k < m := by
  intros k l m
  rcases k with ⟨k, ⟨tran_k, _⟩⟩; rcases l with ⟨l, ⟨tran_l, _⟩⟩; rcases m with ⟨m, ⟨tran_m, _⟩⟩
  simp_rw [lt_iff, mem, tran, subset_eq] at *
  aesop

/-- To turn a set into a collection, i.e. turn an HF set into  a 'Lean' set -/
def toSetS (x : S) : Set S := {s : S | s ∈ x}

lemma toSetS_finite (x : S) : Set.Finite {s : S | s ∈ x} := by
  induction' x using HF.induction with x y hx _
  · simp_all only [set_notin_empty ,Set.setOf_false, Set.finite_empty]
  · simp_rw [enlarge_iff]
    rw [show {s | s ∈ x ∨ s = y} = {s | s ∈ x} ∪ {y} by aesop]
    aesop

instance (x : S): Fintype (toSetS x) := Set.Finite.fintype (toSetS_finite x)

/-- The cardinality of a set x -/
def card (x : S) : ℕ := Fintype.card (toSetS x)

lemma mem_subset_lemma (k l : ordinal S) (k_in_l : k ∈ l) : toSetS k.1 ⊂ toSetS l.1 := by
  simp_rw [toSetS]
  rw [mem_iff_subset, sbst_lemma] at k_in_l
  have k_sbst_l := k_in_l
  rw [subset] at k_in_l
  simp_rw [Set.ssubset_def, Set.subset_def]
  refine ⟨by aesop, ?_⟩
  simp only [Set.mem_setOf_eq, not_forall, exists_prop]
  apply subset_imp_diff_has_element k.1 l.1 at k_sbst_l
  cases' k_sbst_l with m hm
  use m

lemma wf_lemma (X : (fun x y : ℕ => x > y) ↪r fun x y : ordinal S => x < y) : False := by
  have card_lemma (m n : ℕ) (h : m < n) : card (X n).1 < card (X m).1 := by
    apply Set.card_lt_card
    apply mem_subset_lemma
    change X m > X n
    rwa [gt_iff_lt, X.map_rel_iff]
  have h : IsWellFounded (ℕ) (· < ·) := instWellFoundedLTNatInstLTNat
  have h2 : WellFounded fun (x : ℕ) x_1 => x < x_1 := h.1
  rw [RelEmbedding.wellFounded_iff_no_descending_seq] at h2
  have inj : Function.Injective fun (n : ℕ) => card (X n).1 := by
    intros n m h_card; simp only at h_card
    by_contra! n_neq_m; rw [Nat.lt_or_gt] at n_neq_m
    cases' n_neq_m with n_lt_m m_lt_n
    · specialize card_lemma n m n_lt_m; simp_all
    · specialize card_lemma m n m_lt_n; simp_all
  have map_rel_iff : ∀ {n m : ℕ}, card (X n).1 < card (X m).1 ↔ m < n := by
    intros n m
    refine ⟨?_, by simp_all⟩
    intro h_card
    by_contra m_le_n; rw [not_lt_iff_eq_or_lt] at m_le_n
    refine m_le_n.elim (by aesop) ?_; intro n_lt_m
    specialize card_lemma n m n_lt_m
    rw [lt_iff_le_not_le] at *
    simp_all
  let f : (fun x y : ℕ  => x > y) ↪r fun x y : ℕ  => x < y := {
    toFun := fun (n : ℕ) => card (X n).1
    inj' := inj
    map_rel_iff' := map_rel_iff
  }
  contrapose! h2
  simp only [gt_iff_lt, not_isEmpty_iff]
  exact ⟨f⟩

instance lt_wf : IsWellFounded (ordinal S) (· < ·) where
  wf := by
    letI i : IsStrictOrder (ordinal S) (· < · ) := {
      irrefl := by have _ (k : (ordinal S)) := set_in_set_false k; aesop
      trans := trans'
    }
    rw [RelEmbedding.wellFounded_iff_no_descending_seq]
    by_contra! H
    simp only [gt_iff_lt, not_isEmpty_iff] at H
    cases' H with F
    exact wf_lemma (S := S) F

instance : LinearOrder (ordinal S) where
  le_total := le_total'
  decidableLE := inferInstance

theorem exists_min_set (x : Set (ordinal S)) (neq_emp : x ≠ ∅) :
    ∃ l ∈ x, (∀ k ∈ x, l ≤ k) := by
  let l :=  @WellFounded.min (ordinal S) (· < ·) lt_wf.1 x (by
    contrapose! neq_emp
    exact neq_emp)
  use l
  constructor
  · apply WellFounded.min_mem
  · intro k k_in_x
    have := @WellFounded.not_lt_min (ordinal S) (· < ·) lt_wf.1 x (by
    contrapose! neq_emp
    exact neq_emp) k k_in_x
    change ¬ k < l at this
    rw [not_lt] at this
    exact this

/-- The smallest element of a non-empty collection of ordinals -/
def min_set (x : Set (ordinal S)) (neq_emp : x ≠ ∅) : ordinal S := (exists_min_set x neq_emp).choose

lemma min_set_le (x : Set (ordinal S)) (neq_emp : x ≠ ∅) : ∀ l ∈ x, min_set x neq_emp ≤ l := by
  have h := (exists_min_set x neq_emp).choose_spec; aesop

lemma min_set_in_set (x : Set (ordinal S)) (neq_emp : x ≠ ∅) : min_set x neq_emp ∈ x := by
  have h := (exists_min_set x neq_emp).choose_spec; aesop

lemma min_set_unique (x : Set (ordinal S)) (neq_emp : x ≠ ∅)
    (m : ordinal S) (h1 : ∀ l ∈ x, m ≤ l) (h2 : m ∈ x) : m = min_set x neq_emp := by
  have min_set_le := min_set_le x neq_emp
  have min_set_in_set := min_set_in_set x neq_emp
  specialize h1 (min_set x neq_emp) min_set_in_set
  specialize min_set_le m h2
  apply le_antisymm' m (min_set x neq_emp) <;> simp_all

instance : InfSet (ordinal S) where
  sInf := fun x => if neq_emp : x ≠ ∅ then min_set x neq_emp else ∅

lemma sInf_def (x : Set (ordinal S)) : sInf x = if neq_emp : x ≠ ∅ then min_set x neq_emp else ∅ := rfl

lemma csInf_le' (x : Set (ordinal S)) (k : ordinal S) : BddBelow x → k ∈ x → sInf x ≤ k := by
  simp [sInf_def]
  have h := min_set_le x
  aesop

lemma le_csInf' (x : Set (ordinal S)) (k : ordinal S) : Set.Nonempty x → k ∈ lowerBounds x → k ≤ sInf x := by
  simp [sInf_def]
  have h := min_set_in_set x
  aesop

instance : SupSet (ordinal S) where
  sSup := fun x => if BddAbove x then sInf (upperBounds x) else ∅

lemma sSup_def (x : Set (ordinal S)) : sSup x = if BddAbove x then sInf (upperBounds x) else ∅ := rfl

lemma le_csSup' (x : Set (ordinal S)) (k : ordinal S) : BddAbove x → k ∈ x → k ≤ sSup x := by
  intros bdd_x k_in_x
  simp [sSup_def]
  split_ifs
  rw [sInf_def]
  rw [BddAbove] at bdd_x
  split_ifs with up_bd
  · have min_up_bd : min_set (upperBounds x) up_bd ∈ upperBounds x := min_set_in_set (upperBounds x) up_bd
    aesop
  · aesop

lemma csSup_le' (x : Set (ordinal S)) (k : ordinal S) : k ∈ upperBounds x → sSup x ≤ k := by
  intro k_up_bd
  simp [sSup_def]
  have bdd_ab_x : BddAbove x := by rw [BddAbove, Set.Nonempty]; aesop
  have emp_le (l : ordinal S) := emp_le l
  have bdd_bel_up_bds : BddBelow (upperBounds x) := by rw [BddBelow, Set.Nonempty, lowerBounds]; use (∅ : ordinal S); aesop
  split_ifs
  · apply csInf_le' <;> simp_all
  · simp_all

instance : ConditionallyCompleteLattice (ordinal S) where
  le_csSup := le_csSup'
  csSup_le := by have (x : Set (ordinal S)) (k : ordinal S) := csSup_le' x k; simp_all
  csInf_le := csInf_le'
  le_csInf := le_csInf'

lemma emp_min_up_bds_emp (h : upperBounds (∅ : Set (ordinal S)) ≠ ∅) : ∅ = min_set (upperBounds ∅) h := by
  apply min_set_unique
  · intros l _
    exact emp_le l
  · aesop

lemma csSup_of_not_bddAbove' (x : Set (ordinal S)) : ¬BddAbove x → sSup x = sSup ∅ := by
  intro n_bdd_x
  simp_rw [sSup_def, sInf_def]
  have up_bds_emp : upperBounds (∅ : Set (ordinal S)) ≠ ∅ := by aesop
  have emp_min_up_bds_emp := emp_min_up_bds_emp up_bds_emp
  split_ifs <;> aesop

lemma csInf_of_not_bddBelow' (x : Set (ordinal S)) : ¬BddBelow x → sInf x = sInf ∅ := by
  intro not_bdd
  exfalso; apply not_bdd
  use ∅
  have emp_le (k : ordinal S) := emp_le k
  rw [lowerBounds]
  aesop

instance : ConditionallyCompleteLinearOrder (ordinal S) where
  le_total := le_total'
  decidableLE := inferInstance
  decidableEq := inferInstance
  decidableLT := inferInstance
  csSup_of_not_bddAbove := csSup_of_not_bddAbove'
  csInf_of_not_bddBelow := csInf_of_not_bddBelow'

instance cond_comp_lin_ord_bot : ConditionallyCompleteLinearOrderBot (ordinal S) where
  bot := (∅ : ordinal S)
  bot_le := emp_le
  csSup_empty := by simp_rw [sSup_def, sInf_def, ← emp_min_up_bds_emp]; aesop

end ordinal

end HF
