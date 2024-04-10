import Mathlib.Tactic
import GIT.app1
import GIT.app2

open Classical

suppress_compilation

variable {S : Type u} [HF S]

namespace HF

def R : ordinal S → ordinal S
| (∅ : ordinal S) => ∅
| succ x => power (R x)

end HF
