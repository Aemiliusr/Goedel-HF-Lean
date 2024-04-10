import Mathlib.Tactic
import GIT.app1
import GIT.app2


open Classical

suppress_compilation

variable {S : Type u} [HF S]

namespace HF

def function (x : S) : Prop := (∀ y ∈ x, ∃ z z', y = ord_pair z z')
    ∧ (∀ u v v', ((ord_pair u v) ∈ x) → ((ord_pair u v') ∈ x) → v = v')

def dom (x : S) : S := pred_set (union_set (union_set x)) (fun u ↦ ∃ v, (ord_pair u v) ∈ x)

def seq (s : S) (k : ordinal S) : Prop := function s ∧ k ≠ ∅ ∧ dom s = k.1

end HF
