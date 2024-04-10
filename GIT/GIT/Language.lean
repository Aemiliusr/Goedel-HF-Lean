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

abbrev HFLang.enlargementSymbol : HFLang.Functions 2 := PUnit.unit

abbrev HFLang.membershipSymbol : HFLang.Relations 2 := PUnit.unit

def HFLang.emptySetTerm : HFLang.Term Empty :=
.func HFLang.emptySetSymbol (fun x => x.elim0)

/--
HF1: ∀ z, z = ∅ ↔ ∀ x, ¬(x ∈ z)
-/
def HFAxiom1 : HFLang.Sentence :=
.all <| .iff
  (.equal
    (.var (.inr 0)) -- z
    (.func HFLang.emptySetSymbol (fun x => x.elim0))) -- ∅
  (.all <| .not <|
    .rel HFLang.membershipSymbol ![.var (.inr 1), .var (.inr 0)]) -- x ∈ z

/--
∀ z, ∀ x, ∀ y, z = enlarge x y ↔ ∀ u, u ∈ z ↔ u ∈ x ∨ u = y
-/
def HFAxiom2 : HFLang.Sentence :=
.all <| -- for all z
.all <| -- for all x
.all <| -- for all y
.iff
  (.equal
    (.var <| .inr 0) -- z
    (.func HFLang.enlargementSymbol ![.var (.inr 1), .var (.inr 2)])) -- enlarge x y
  (.all <| -- for all u
    .iff
      (.rel HFLang.membershipSymbol ![.var (.inr 3), .var (.inr 0)]) -- u ∈ z
      (.rel HFLang.membershipSymbol ![.var (.inr 3), .var (.inr 1)] ⊔
       .rel HFLang.membershipSymbol ![.var (.inr 3), .var (.inr 1)])) -- u ∈ x ∨ u = y

/--
`α` is a formula with one free variable.

HF3: α(∅) ∧ ∀ x y, α(x) → α(y) → α(enlarge x y)

-/
def HFAxiom3 (α : HFLang.Formula (Fin 1)) : HFLang.Sentence :=
α.subst ![.func HFLang.emptySetSymbol Fin.elim0] ⊓ -- α(∅)
(.all <| -- for all x
.all <| -- for all y
.imp
  (α.subst ![.var (0 : Fin 1)] |>.relabel ![.inr 0]) -- α(x)
  (.imp
    (α.subst ![.var (0 : Fin 1)] |>.relabel ![.inr 1]) -- α(y)
    (α.subst ![ .func HFLang.enlargementSymbol
      ![.var (0 : Fin 2), .var (1 : Fin 2)] ] |>.relabel .inr))) -- α(enlarge x y)

def HFSetTheory : HFLang.Theory :=
{HFAxiom1, HFAxiom2} ∪ ⋃ (α : HFLang.Formula (Fin 1)), {HFAxiom3 α}
