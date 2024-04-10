import Mathlib.ModelTheory.Syntax

open FirstOrder

def HFLang : Language.{0, 0} where
  Functions :=
  fun
  | 0 => PUnit -- We have one 0-ary function, i.e. a constant term, the empty set
  | 1 => Empty -- We have no 1-ary functions
  | 2 => PUnit -- We have one 2-ary function, i.e. a binary function, the enlargement
  | .succ _ => Empty
  Relations :=
  fun
  | 0 => Empty -- We have no 0-ary relations
  | 1 => Empty -- We have no unary relations
  | 2 => PUnit -- We have one binary relation, the membership relation
  | .succ _ => Empty -- We have no n-ary relations for n > 2

abbrev HFLang.emptySetSymbol : HFLang.Functions 0 := PUnit.unit

local notation "∅'" => HFLang.emptySetSymbol

abbrev HFLang.enlargementSymbol : HFLang.Functions 2 := PUnit.unit

local notation "◁'" => HFLang.enlargementSymbol

abbrev HFLang.membershipSymbol : HFLang.Relations 2 := PUnit.unit

local notation "∈'" => HFLang.membershipSymbol

/--
HF1: ∀ z, z = ∅ ↔ ∀ x, ¬(x ∈ z)
-/
def HFAxiom1 : HFLang.Sentence :=
∀' (&0 =' (.func ∅' Fin.elim0)) ⇔ ∀' ∼(.rel ∈' ![&1, &0])

/--
∀ z, ∀ x, ∀ y, z = enlarge x y ↔ ∀ u, u ∈ z ↔ u ∈ x ∨ u = y
-/
def HFAxiom2 : HFLang.Sentence :=
∀' ∀' ∀'
  (&0 =' (.func ◁' ![&1, &2])) ⇔
  ∀' (.rel ∈' ![&3, &0] ⇔ (.rel ∈' ![&3, &1] ⊔ .rel ∈' ![&3, &2]))

/--
`α` is a formula with one free variable.

HF3: α(∅) ∧ ∀ x y, α(x) → α(y) → α(enlarge x y)
-/
def HFAxiom3 (α : HFLang.Formula (Fin 1)) : HFLang.Sentence :=
α.subst ![.func ∅' Fin.elim0] ⊓
∀' ∀'
((α.subst ![.var 0] |>.relabel ![.inr 0]) ⊓ (α.subst ![.var 1] |>.relabel ![.inr 1]) ⟹
  (α.subst ![ .func ◁' ![.var 0, .var 1] ] |>.relabel .inr))

def HFSetTheory : HFLang.Theory :=
{HFAxiom1, HFAxiom2} ∪ ⋃ (α : HFLang.Formula (Fin 1)), {HFAxiom3 α}
